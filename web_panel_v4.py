#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import re
import sys
import json
import time
import uuid
import signal
import random
import socket
import hashlib
import inspect
import threading
from collections import deque
from contextlib import asynccontextmanager
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from typing import Optional

# Embedded environment configuration (no external env vars required)
os.environ["PANEL_TOKEN"] = "KENG"
os.environ["DATA_DIR"] = "/data" if os.path.isdir("/data") else "./data"
os.environ["SOCKET_POOL"] = "1"
os.environ["WS_WORKER_RECYCLE_SEC"] = "3600"
os.environ["UVICORN_BACKLOG"] = "2048"
os.environ["UVICORN_LIMIT_CONCURRENCY"] = "256"

import psutil
import requests
import uvicorn
from fastapi import FastAPI, Header, HTTPException, Request
from fastapi.responses import HTMLResponse, JSONResponse
from instagrapi import Client
from instagrapi.exceptions import BadPassword, ClientNeedsUpgradeError, TwoFactorRequired
from pydantic import BaseModel

try:
    from igrapiweb import make_ig_web_socket
    IGRAPIWEB_AVAILABLE = True
except Exception:
    make_ig_web_socket = None
    IGRAPIWEB_AVAILABLE = False

# ======================== CONFIG ========================

PORT = 8080
PANEL_TOKEN = "KENG"

IG_APP_VERSION = "355.0.0.47.96"
IG_VERSION_CODE = "656018442"
IG_USER_AGENT = (
    f"Instagram {IG_APP_VERSION} Android (34/14; 480dpi; 1080x2400; samsung; SM-S918B; dm3q; qcom; en_US; {IG_VERSION_CODE})"
)

DATA_DIR = os.environ["DATA_DIR"]
os.makedirs(DATA_DIR, exist_ok=True)
ACCOUNTS_FILE = os.path.join(DATA_DIR, "accounts.json")
TEMPLATE_FILE = os.path.join(DATA_DIR, "template.json")
WS_SESSIONS_FILE = os.path.join(DATA_DIR, "ws_sessions.json")

DEFAULT_SINGLE_LINE_TEMPLATE = "<{TARGET}> Kɪ Mᴀᴀ Mᴏᴛɪ !< Gᴀɴᴅ Wᴀʟɪ> Rᴀɴᴅ!> <😎>"
DEFAULT_GROUP_TITLE_TEMPLATE = "{TARGET} <⚡️>"
LINE_GAPS_AFTER = [6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 1]

EMOJI_POOL = [
    "😎", "🦊", "🐉", "🦅", "🦂", "🦈", "🐺", "🦁",
    "☄️", "💥", "🗡️", "🛡️", "👑", "💎", "🎯", "🧨",
]

SUBTLE_LINK_SLUGS = [
    "r", "x", "q", "v", "k", "m", "n", "t",
]

WS_EMOJI_POOL = [
    "😎", "🦁", "🐯", "🐺", "🦊", "🐉", "🦅", "🦉", "🦇", "🦈", "🐊", "🦂",
    "🕷️", "🐍", "🦖", "☄️", "💥", "🔥", "🌪️", "🌊", "❄️", "💎", "👑", "🗡️",
    "🛡️", "🎯", "🧨", "🚀",
]
WS_GC_EMOJI = "⚡️"
WS_FOOTER = "\n\n\n\nScript by - ρ 𝕣 ꪜ 𝕣 अब्बू ☽"

WS_UA_POOL = [
    "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1",
    "Mozilla/5.0 (iPhone; CPU iPhone OS 16_6 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/16.6 Mobile/15E148 Safari/604.1",
    "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 13; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 12; V2148A) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 13; CPH2451) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.3 Safari/605.1.15",
]

socket.setdefaulttimeout(8)

WS_ROTATE_MIN = 1800
WS_ROTATE_MAX = 5400
WS_HEALTH_CHECK_MIN = 300
WS_HEALTH_CHECK_MAX = 600
WS_WORKER_RECYCLE_SEC = 3600

MIN_SAFE_ADD_COOLDOWN = 20.0
RENAME_PER_THREAD_GAP_SEC = 4.0

WS_SOCKET_POOL = 1

_MWS_PARAMS = set()
if IGRAPIWEB_AVAILABLE and make_ig_web_socket is not None:
    try:
        _MWS_PARAMS = set(inspect.signature(make_ig_web_socket).parameters.keys())
    except Exception:
        _MWS_PARAMS = set()

MAX_RETRIES = 5

active_tasks: dict = {}
multi_gc_jobs: dict = {}
group_creator_jobs: dict = {}
ws_sessions: dict = {}
client_cache: dict = {}
pending_2fa: dict = {}
tasks_lock = threading.Lock()
ws_lock = threading.Lock()
store_lock = threading.Lock()
logs_lock = threading.Lock()
PANEL_LOGS = deque(maxlen=400)
GLOBAL_MESSAGES_SENT = 0
BOT_START_TIME = datetime.now()

_accounts_cache: Optional[dict] = None
_template_cache: Optional[dict] = None


def append_panel_log(source: str, message: str):
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    entry = f"[{ts}] [{source}] {message}"
    with logs_lock:
        PANEL_LOGS.append(entry)
    print(entry, flush=True)


def _handle_exit_signal(signum, frame):
    append_panel_log("SYS", f"Received signal {signum}, exiting immediately...")
    os._exit(0)


signal.signal(signal.SIGTERM, _handle_exit_signal)
signal.signal(signal.SIGINT, _handle_exit_signal)


# ======================== AUTH HELPER ========================

def verify_auth(x_panel_token: Optional[str] = None, token_query: Optional[str] = None):
    if not PANEL_TOKEN:
        return
    provided = (x_panel_token or token_query or "").strip()
    if provided != PANEL_TOKEN:
        raise HTTPException(status_code=401, detail="Unauthorized: invalid or missing panel token")


# ======================== PERSISTENCE ========================

def load_saved_accounts() -> dict:
    global _accounts_cache
    if _accounts_cache is not None:
        return dict(_accounts_cache)
    with store_lock:
        if _accounts_cache is not None:
            return dict(_accounts_cache)
        if not os.path.exists(ACCOUNTS_FILE):
            _accounts_cache = {}
            return {}
        try:
            with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            _accounts_cache = data if isinstance(data, dict) else {}
        except Exception:
            _accounts_cache = {}
        return dict(_accounts_cache)


def register_saved_account(username: str, ig_user_id=None, auth_method: str = "password"):
    global _accounts_cache
    with store_lock:
        accounts = {}
        if os.path.exists(ACCOUNTS_FILE):
            try:
                with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                    loaded = json.load(f)
                    if isinstance(loaded, dict):
                        accounts = loaded
            except Exception:
                accounts = {}

        prev = accounts.get(username, {})
        accounts[username] = {
            "username": username,
            "ig_user_id": str(ig_user_id) if ig_user_id is not None else prev.get("ig_user_id"),
            "auth_method": auth_method,
            "updated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        }
        with open(ACCOUNTS_FILE, "w", encoding="utf-8") as f:
            json.dump(accounts, f, indent=2)
        _accounts_cache = dict(accounts)


def delete_saved_account(username: str):
    global _accounts_cache
    with store_lock:
        if os.path.exists(ACCOUNTS_FILE):
            try:
                with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                    accounts = json.load(f)
                if isinstance(accounts, dict) and username in accounts:
                    del accounts[username]
                    with open(ACCOUNTS_FILE, "w", encoding="utf-8") as f:
                        json.dump(accounts, f, indent=2)
                    _accounts_cache = dict(accounts)
            except Exception:
                pass
        session_path = os.path.join(DATA_DIR, f"ig_{username}.json")
        if os.path.exists(session_path):
            try:
                os.remove(session_path)
            except Exception:
                pass
    client_cache.pop(username, None)


def _read_template_payload() -> dict:
    global _template_cache
    if _template_cache is not None:
        return dict(_template_cache)
    if os.path.exists(TEMPLATE_FILE):
        try:
            with open(TEMPLATE_FILE, "r", encoding="utf-8") as f:
                payload = json.load(f)
            if isinstance(payload, dict):
                _template_cache = dict(payload)
                return payload
        except Exception:
            pass
    _template_cache = {}
    return {}


def get_active_single_line_template() -> str:
    payload = _read_template_payload()
    tpl = payload.get("template")
    if isinstance(tpl, str) and tpl.strip():
        lines = [ln.strip() for ln in tpl.splitlines() if ln.strip()]
        if lines:
            return lines[0]
    return DEFAULT_SINGLE_LINE_TEMPLATE


def get_active_group_title_template() -> str:
    payload = _read_template_payload()
    gt = payload.get("group_title_template")
    if isinstance(gt, str) and gt.strip():
        return gt.strip()
    return DEFAULT_GROUP_TITLE_TEMPLATE


def set_active_template(tpl: str, group_title_template: Optional[str] = None):
    global _template_cache
    lines = [ln.strip() for ln in tpl.splitlines() if ln.strip()]
    if not lines:
        raise ValueError("Template cannot be empty.")
    single_line = lines[0]
    with store_lock:
        existing = _read_template_payload()
        gt = (
            group_title_template.strip()
            if isinstance(group_title_template, str) and group_title_template.strip()
            else existing.get("group_title_template") or DEFAULT_GROUP_TITLE_TEMPLATE
        )
        new_payload = {
            "template": single_line,
            "group_title_template": gt,
            "updated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        }
        with open(TEMPLATE_FILE, "w", encoding="utf-8") as f:
            json.dump(new_payload, f, indent=2)
        _template_cache = dict(new_payload)


def reset_active_template():
    global _template_cache
    with store_lock:
        if os.path.exists(TEMPLATE_FILE):
            try:
                os.remove(TEMPLATE_FILE)
            except Exception:
                pass
        _template_cache = {}


def save_ws_sessions_disk():
    with ws_lock:
        payload = {uid: dict(w.data) for uid, w in ws_sessions.items()}
    with store_lock:
        try:
            with open(WS_SESSIONS_FILE, "w", encoding="utf-8") as f:
                json.dump(payload, f, indent=2)
        except Exception as exc:
            append_panel_log("WS", f"Disk save error: {exc}")


def load_ws_sessions_disk() -> dict:
    with store_lock:
        if not os.path.exists(WS_SESSIONS_FILE):
            return {}
        try:
            with open(WS_SESSIONS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, dict) else {}
        except Exception:
            return {}


def render_single_line_with_random_emoji(base_line: str, target_name: str) -> str:
    chosen_emoji = random.choice(EMOJI_POOL)
    rendered = base_line.replace("{TARGET}", target_name).replace("{EMOJI}", chosen_emoji)
    if "<😎>" in rendered:
        return rendered.replace("<😎>", f"<{chosen_emoji}>")
    if "-🌒-" in rendered:
        return rendered.replace("-🌒-", f"<{chosen_emoji}>")
    if re.search(r"![^!\s]+!\s*$", rendered):
        return re.sub(r"![^!\s]+!(\s*)$", f"<{chosen_emoji}>\\1", rendered)
    if re.search(r"<[^<>\s]+>\s*$", rendered):
        return re.sub(r"<[^<>\s]+>(\s*)$", f"<{chosen_emoji}>\\1", rendered)
    if re.search(r"-[^\s-]+-\s*$", rendered):
        return re.sub(r"-[^\s-]+-(\s*)$", f"<{chosen_emoji}>\\1", rendered)
    return f"{rendered} <{chosen_emoji}>"


def format_nc_title(base_title: str) -> str:
    cleaned = re.sub(r"\s*(?:!+\s*[^\s!<>]+\s*!+|<\s*[^\s<>]+\s*>)\s*$", "", base_title.strip()).strip()
    if not cleaned:
        cleaned = base_title.strip() or "GC"
    return f"{cleaned} <{WS_GC_EMOJI}>"[:75]


def build_expanded_message(single_line_template: str, target_name: str) -> str:
    parts = []
    for idx, newlines_after in enumerate(LINE_GAPS_AFTER):
        parts.append(render_single_line_with_random_emoji(single_line_template, target_name))
        if idx < len(LINE_GAPS_AFTER) - 1:
            parts.append("\n" * newlines_after)
    return "".join(parts)


def make_subtle_z_link() -> str:
    slug = random.choice(SUBTLE_LINK_SLUGS)
    suffix = uuid.uuid4().hex[:3]
    return f"https://z.in/{slug}{suffix}"


# ======================== IG HELPERS ========================

def make_ig_client() -> Client:
    cl = Client()
    cl.delay_range = [0, 0]
    try:
        if IG_APP_VERSION:
            cl.set_app_version(IG_APP_VERSION)
    except Exception:
        pass
    try:
        if IG_USER_AGENT:
            cl.set_user_agent(IG_USER_AGENT)
    except Exception:
        pass
    if IG_VERSION_CODE:
        try:
            cl.version_code = IG_VERSION_CODE
        except Exception:
            pass
    return cl


def clean_session_id(raw: str) -> str:
    val = raw.strip().strip('"').strip("'")
    if "sessionid=" in val:
        val = val.split("sessionid=", 1)[1].split(";", 1)[0].strip()
    return val


def resolve_username(client: Client, fallback: str = "") -> str:
    if fallback:
        return fallback.strip().lstrip("@")
    u = getattr(client, "username", None)
    if isinstance(u, str) and u.strip():
        return u.strip().lstrip("@")
    try:
        info = client.account_info()
        if getattr(info, "username", None):
            return str(info.username).strip().lstrip("@")
    except Exception:
        pass
    return f"user_{getattr(client, 'user_id', 'session')}"


def save_session(client: Client, username: str, auth_method: str):
    session_path = os.path.join(DATA_DIR, f"ig_{username}.json")
    client.dump_settings(session_path)
    register_saved_account(username, getattr(client, "user_id", None), auth_method=auth_method)
    client_cache[username] = client


def get_or_resume_client(username: str) -> Client:
    if username in client_cache:
        return client_cache[username]
    session_path = os.path.join(DATA_DIR, f"ig_{username}.json")
    if not os.path.exists(session_path):
        raise RuntimeError(f"Saved session for @{username} not found.")
    cl = make_ig_client()
    cl.load_settings(session_path)
    cl.account_info()
    cl.dump_settings(session_path)
    client_cache[username] = cl
    return cl


def list_threads(client: Client):
    threads = client.direct_threads(amount=30)
    out = []
    for t in threads:
        tid_str = str(t.id).strip()
        if getattr(t, "thread_title", None):
            title = str(t.thread_title)
        elif getattr(t, "users", None):
            names = [u.username for u in t.users if getattr(u, "username", None)]
            title = ", ".join(names) if names else "Direct Chat"
        else:
            title = "Thread"
        is_group = bool(getattr(t, "is_group", False))
        tag = "GC" if is_group else "DM"
        out.append({
            "id": tid_str,
            "is_group": is_group,
            "title": title,
            "label": f"[{tag}] {title[:32]}",
        })
    return out


def _extract_threads_from_web_json(obj, acc: list, seen: set):
    if isinstance(obj, dict):
        tid = obj.get("thread_id") or obj.get("id")
        if tid and str(tid).strip().isdigit():
            s_tid = str(tid).strip()
            has_thread_shape = any(
                k in obj for k in ("thread_title", "users", "items", "last_permanent_item", "is_group")
            )
            if has_thread_shape and s_tid not in seen:
                seen.add(s_tid)
                is_group = bool(obj.get("is_group", False))
                title = str(obj.get("thread_title") or "").strip()
                if not title and isinstance(obj.get("users"), list):
                    names = [
                        str(u.get("username") or u.get("full_name") or "").strip()
                        for u in obj["users"]
                        if isinstance(u, dict) and (u.get("username") or u.get("full_name"))
                    ]
                    title = ", ".join(names) if names else ("Group Chat" if is_group else "Direct Chat")
                if not title:
                    title = "Group Chat" if is_group else "Direct Chat"
                tag = "GC" if is_group else "DM"
                acc.append({
                    "id": s_tid,
                    "is_group": is_group,
                    "title": title,
                    "label": f"[{tag}] {title[:32]}",
                })
        for v in obj.values():
            _extract_threads_from_web_json(v, acc, seen)
    elif isinstance(obj, list):
        for item in obj:
            _extract_threads_from_web_json(item, acc, seen)


def fetch_threads_via_sessionid(session_id: str, ua: Optional[str] = None) -> list[dict]:
    sid = clean_session_id(session_id)
    if not sid:
        raise RuntimeError("Missing session ID.")

    headers = {
        "User-Agent": ua or random.choice(WS_UA_POOL),
        "X-IG-App-ID": "936619743392459",
        "Accept": "application/json, text/plain, */*",
        "Referer": "https://www.instagram.com/direct/inbox/",
    }
    cookies = {"sessionid": sid}

    if IGRAPIWEB_AVAILABLE and make_ig_web_socket is not None:
        sock = None
        try:
            sock = make_ig_web_socket(sessionid=sid, user_agent=headers["User-Agent"])
            for method_name in ("get_inbox", "direct_threads", "fetch_threads", "list_threads"):
                fn = getattr(sock, method_name, None)
                if callable(fn):
                    res = fn()
                    found = []
                    _extract_threads_from_web_json(res, found, set())
                    if found:
                        return found[:30]
        except Exception:
            pass
        finally:
            if sock is not None:
                try:
                    sock.disconnect()
                except Exception:
                    pass

    last_err = None
    for url in (
        "https://www.instagram.com/api/v1/direct_v2/inbox/?persistentBadging=true&folder=&limit=30",
        "https://i.instagram.com/api/v1/direct_v2/inbox/?persistentBadging=true&folder=&limit=30",
    ):
        try:
            resp = requests.get(url, headers=headers, cookies=cookies, timeout=10)
            if resp.status_code == 200:
                data = resp.json()
                found = []
                _extract_threads_from_web_json(data, found, set())
                if found:
                    return found[:30]
            last_err = f"HTTP {resp.status_code}"
        except Exception as exc:
            last_err = str(exc)[:100]

    raise RuntimeError(f"Could not fetch chats from session ID ({last_err or 'empty inbox'}).")


def parse_thread_ids(raw_ids) -> list[str]:
    if not raw_ids:
        return []
    result = []
    for item in raw_ids:
        s = str(item).strip()
        if s.isdigit() and s not in result:
            result.append(s)
    return result


def parse_usernames(raw_usernames: Optional[list]) -> list[str]:
    if not raw_usernames:
        return []
    out = []
    for item in raw_usernames:
        clean = str(item).strip().lstrip("@").lower()
        if clean and clean not in out:
            out.append(clean)
    return out


def resolve_usernames_to_ids(cl: Client, usernames: list[str]) -> tuple[list[int], list[str]]:
    resolved_ids: list[int] = []
    failed: list[str] = []
    my_uid = int(getattr(cl, "user_id", 0) or 0)

    for idx, uname in enumerate(usernames):
        try:
            uid_str = cl.user_id_from_username(uname)
            uid_int = int(str(uid_str).strip())
            if uid_int > 0 and uid_int != my_uid and uid_int not in resolved_ids:
                resolved_ids.append(uid_int)
        except Exception as exc:
            failed.append(f"@{uname} ({str(exc)[:30]})")
        if idx < len(usernames) - 1:
            time.sleep(random.uniform(1.2, 2.5))

    return resolved_ids, failed


def resolve_single_member_id(cl: Client, raw_member: str) -> tuple[int, str]:
    cleaned = str(raw_member or "").strip()
    if not cleaned:
        raise ValueError("Target user ID or @username is required.")

    my_uid = int(getattr(cl, "user_id", 0) or 0)
    if cleaned.isdigit():
        uid_int = int(cleaned)
        if uid_int <= 0:
            raise ValueError("User ID must be a positive number.")
        if uid_int == my_uid:
            raise ValueError("Cannot add your own account ID to the group.")
        return uid_int, str(uid_int)

    uname = cleaned.lstrip("@").strip().lower()
    if not uname:
        raise ValueError("Invalid @username.")
    uid_str = cl.user_id_from_username(uname)
    uid_int = int(str(uid_str).strip())
    if uid_int <= 0:
        raise RuntimeError(f"Could not resolve numeric ID for @{uname}.")
    if uid_int == my_uid:
        raise ValueError("Cannot add your own account to the group.")
    return uid_int, f"@{uname} ({uid_int})"


def add_user_to_group_thread(cl: Client, tid_str: str, user_id: int) -> None:
    tid_int = int(tid_str)
    if hasattr(cl, "direct_thread_add_users"):
        cl.direct_thread_add_users(tid_int, [user_id])
        return
    if hasattr(cl, "private_request"):
        cl.private_request(
            f"direct_v2/threads/{tid_int}/add_user/",
            data={"user_ids": json.dumps([str(user_id)])},
        )
        return
    raise RuntimeError("Client does not support adding users to a group thread.")


def _find_invite_url_in_obj(obj) -> Optional[str]:
    if obj is None:
        return None
    if isinstance(obj, str):
        m = re.search(r"https?://(?:www\.)?ig\.me/j/[A-Za-z0-9_-]+/?", obj)
        if m:
            return m.group(0)
        m2 = re.search(r"https?://(?:www\.)?instagram\.com/j/[A-Za-z0-9_-]+/?", obj)
        if m2:
            return m2.group(0)
        return None
    if isinstance(obj, dict):
        for k, v in obj.items():
            kl = str(k).lower()
            if ("invite" in kl or "join" in kl or "url" in kl or "link" in kl) and isinstance(v, str):
                found = _find_invite_url_in_obj(v)
                if found:
                    return found
            found = _find_invite_url_in_obj(v)
            if found:
                return found
    elif isinstance(obj, (list, tuple)):
        for item in obj:
            found = _find_invite_url_in_obj(item)
            if found:
                return found
    else:
        d = getattr(obj, "__dict__", None)
        if isinstance(d, dict):
            return _find_invite_url_in_obj(d)
    return None


def extract_group_invite_link(cl: Client, tid_str: str) -> dict:
    tid_int = int(tid_str)
    title = f"Thread {tid_str}"
    is_group = True

    try:
        th = cl.direct_thread(tid_int, amount=1)
        if getattr(th, "thread_title", None):
            title = str(th.thread_title)
        is_group = bool(getattr(th, "is_group", True))
        link = _find_invite_url_in_obj(th)
        if link:
            return {"thread_id": tid_str, "title": title, "is_group": is_group, "invite_link": link, "status": "ok"}
    except Exception:
        pass

    for endpoint, method in [
        (f"direct_v2/threads/{tid_int}/get_invite_link/", "GET"),
        (f"direct_v2/threads/{tid_int}/create_invite_link/", "POST"),
        (f"direct_v2/threads/{tid_int}/invite_link/", "GET"),
    ]:
        try:
            if hasattr(cl, "private_request"):
                data = (
                    cl.private_request(endpoint, data={})
                    if method == "POST"
                    else cl.private_request(endpoint)
                )
                link = _find_invite_url_in_obj(data)
                if link:
                    return {
                        "thread_id": tid_str,
                        "title": title,
                        "is_group": is_group,
                        "invite_link": link,
                        "status": "ok",
                    }
        except Exception:
            continue

    return {
        "thread_id": tid_str,
        "title": title,
        "is_group": is_group,
        "invite_link": None,
        "status": "unavailable (enable invite link on mobile or verify group admin rights)",
    }


def _create_single_group(cl: Client, title: str, member_user_ids: list[int], send_ping: bool) -> str:
    my_uid = int(getattr(cl, "user_id", 0) or 0)
    participants = [uid for uid in member_user_ids if uid and uid != my_uid]
    if len(participants) < 2:
        raise RuntimeError("Instagram requires at least 2 valid other usernames to create a group thread.")
    if my_uid and my_uid not in participants:
        participants.insert(0, my_uid)

    created = cl.direct_thread_create(participants, title=title[:75])
    if hasattr(created, "id"):
        tid_str = str(created.id).strip()
    elif isinstance(created, dict) and created.get("thread_id"):
        tid_str = str(created["thread_id"]).strip()
    else:
        tid_str = str(created).strip()

    if send_ping and tid_str.isdigit():
        try:
            cl.direct_send(title[:75] or "✨", thread_ids=[int(tid_str)])
        except Exception:
            pass
    return tid_str


# ======================== WEBSOCKET MULTI-SENDER (igrapiweb) ========================

def clamp_socket_pool(n: int) -> int:
    return max(1, min(10, int(n)))


def _apply_sock_timeout(ws_obj, sec: float = 8.0):
    try:
        for attr in ("sock", "_sock", "ws", "_ws", "socket", "_socket", "conn", "_conn"):
            inner = getattr(ws_obj, attr, None)
            if inner is not None:
                if hasattr(inner, "settimeout"):
                    inner.settimeout(sec)
                sub = getattr(inner, "sock", None)
                if sub is not None and hasattr(sub, "settimeout"):
                    sub.settimeout(sec)
    except Exception:
        pass


def _find_key(res, key: str) -> Optional[str]:
    if isinstance(res, dict):
        val = res.get(key)
        if val:
            return str(val)
        for v in res.values():
            if isinstance(v, (dict, list)):
                found = _find_key(v, key)
                if found:
                    return found
    elif isinstance(res, list):
        for v in res:
            found = _find_key(v, key)
            if found:
                return found
    return None


def _extract_ids(res) -> tuple:
    """Return (message_id, item_id) from a send response; either may be None."""
    return _find_key(res, "message_id"), _find_key(res, "item_id")


class WsSessionWorker:
    def __init__(self, data: dict):
        self.data = data
        self.stop_event = threading.Event()
        self.msg_thread = None
        self.rename_thread = None
        self.rotate_thread = None
        self.health_thread = None
        self.recycle_thread = None
        self.self_reply_thread = None
        self._own_msg_ids = deque(maxlen=50)
        self._own_lock = threading.Lock()
        self.listen_threads = []
        self._listen_lock = threading.Lock()
        self._recycle_lock = threading.Lock()
        self._executor = None
        self.pool_size = clamp_socket_pool(self.data.get("socket_pool", WS_SOCKET_POOL))
        self.data["socket_pool"] = self.pool_size
        self.sockets = []
        self.socket_locks = []
        self._pool_lock = threading.Lock()
        self._rr_idx = 0
        self._rr_lock = threading.Lock()
        self._inflight = 0
        self._inflight_lock = threading.Lock()

        if "ua" not in self.data or not self.data["ua"]:
            self.data["ua"] = random.choice(WS_UA_POOL)

        if "device_id" not in self.data or not self.data["device_id"]:
            seed = self.data.get("session_name", self.data["session_id"][:16])
            self.data["device_id"] = hashlib.md5(seed.encode(), usedforsecurity=False).hexdigest()
        self._device_id = self.data["device_id"]

        self.stats = {
            "sent": 0,
            "failed": 0,
            "renames": 0,
            "recycles": 0,
            "start_time": None,
            "status": "stopped",
            "last_error": None,
            "session_status": None,
            "session_error": None,
            "self_replies": 0,
        }
        self._stats_lock = threading.Lock()

    def build_message(self) -> str:
        subtle_link = make_subtle_z_link()
        emoji = random.choice(WS_EMOJI_POOL)
        line = f"{self.data['msg_text']} <{emoji}>"
        body = ("\n" * 5).join([line] * random.randint(12, 18))
        return f"{subtle_link}\n\n{body}{WS_FOOTER}"

    def build_gc_name(self) -> str:
        return format_nc_title(self.data["gc_name_text"])

    def _make_factory_kwargs(self) -> dict:
        base = {"sessionid": self.data["session_id"], "user_agent": self.data["ua"]}
        if "device_id" in _MWS_PARAMS:
            base["device_id"] = self._device_id
        elif "device" in _MWS_PARAMS:
            base["device"] = self._device_id
        elif "device_dict" in _MWS_PARAMS:
            base["device_dict"] = self._device_id
        return base

    def _connect(self, label: str, max_retries: int = 2, retry_delay: float = 1.5):
        if not IGRAPIWEB_AVAILABLE or make_ig_web_socket is None:
            raise RuntimeError("igrapiweb is not installed in this environment.")
        err = None
        base_kwargs = self._make_factory_kwargs()
        for attempt in range(max_retries):
            if self.stop_event.is_set():
                raise RuntimeError("stopped")
            for mode in ("dgw", "iris"):
                try:
                    try:
                        s = make_ig_web_socket(**base_kwargs)
                    except TypeError:
                        s = make_ig_web_socket(
                            sessionid=self.data["session_id"],
                            user_agent=self.data["ua"],
                        )
                    s.connect(dm_receive=mode)
                    _apply_sock_timeout(s, 8.0)
                    lt = threading.Thread(target=self._listen_loop, args=(s,), daemon=True)
                    lt.start()
                    with self._listen_lock:
                        self.listen_threads = [t for t in self.listen_threads if t.is_alive()]
                        self.listen_threads.append(lt)
                    return s
                except Exception as exc:
                    err = exc
                    if "connack" in str(exc).lower():
                        append_panel_log(f"WS:{self.data.get('session_name', '?')}", f"connack on {mode} ({label})")
                        time.sleep(retry_delay)
                        continue
            if attempt < max_retries - 1:
                time.sleep(retry_delay)
        raise RuntimeError(f"{label}: {err}")

    def _listen_loop(self, sock):
        try:
            sock.listen()
        except Exception as exc:
            append_panel_log(f"WS:{self.data.get('session_name', '?')}", f"listen error: {str(exc)[:100]}")

    def _seed_pool(self) -> int:
        n = clamp_socket_pool(self.data.get("socket_pool", self.pool_size))
        with self._pool_lock:
            self.pool_size = n
            self.data["socket_pool"] = n
            self.sockets = [None] * n
            self.socket_locks = [threading.Lock() for _ in range(n)]
        ok = 0
        last_err = None
        for i in range(n):
            try:
                s = self._connect(f"pool{i}", max_retries=2, retry_delay=1.5)
                with self._pool_lock:
                    if i < len(self.sockets):
                        with self.socket_locks[i]:
                            self.sockets[i] = s
                        ok += 1
                    else:
                        s.disconnect()
            except Exception as exc:
                last_err = str(exc)[:100]
            if i < n - 1:
                time.sleep(0.8)
        if ok == 0:
            raise RuntimeError(last_err or "no sockets connected")
        return ok

    def set_socket_pool_size(self, new_count: int) -> int:
        target = clamp_socket_pool(new_count)
        extra_socks = []
        with self._pool_lock:
            self.data["socket_pool"] = target
            self.pool_size = target
            if not self.sockets:
                return target

            current = len(self.sockets)
            if target == current:
                return target

            if target < current:
                extra_socks = self.sockets[target:]
                self.sockets = self.sockets[:target]
                self.socket_locks = self.socket_locks[:target]
            else:
                add_n = target - current
                self.sockets.extend([None] * add_n)
                self.socket_locks.extend(threading.Lock() for _ in range(add_n))
                if not self.stop_event.is_set() and self.stats.get("status") == "live":
                    threading.Thread(
                        target=self._grow_pool_slots,
                        args=(current, target),
                        daemon=True,
                    ).start()
        for s in extra_socks:
            if s:
                try:
                    s.disconnect()
                except Exception:
                    pass
        return target

    def _grow_pool_slots(self, start_idx: int, end_idx: int):
        for i in range(start_idx, end_idx):
            if self.stop_event.is_set():
                break
            try:
                s = self._connect(f"grow{i}", max_retries=2, retry_delay=1.5)
                with self._pool_lock:
                    if i < len(self.sockets):
                        with self.socket_locks[i]:
                            old = self.sockets[i]
                            self.sockets[i] = s
                        if old:
                            try:
                                old.disconnect()
                            except Exception:
                                pass
                    else:
                        s.disconnect()
            except Exception as exc:
                with self._stats_lock:
                    self.stats["last_error"] = f"grow@{i}: {str(exc)[:80]}"
            if i < end_idx - 1:
                time.sleep(0.8)

    def start(self):
        with self._stats_lock:
            if self.stats["status"] in ("live", "starting", "stopping"):
                return False, "Already running or stopping"
            self.stats["status"] = "starting"
            self.stats["last_error"] = None

        for old_t in (self.msg_thread, self.rename_thread, self.rotate_thread, self.health_thread, self.recycle_thread, self.self_reply_thread):
            if old_t and old_t.is_alive():
                old_t.join(timeout=2)

        with self._listen_lock:
            self.listen_threads = [t for t in self.listen_threads if t.is_alive()]

        self.stop_event = threading.Event()
        self._rr_idx = 0

        try:
            ok = self._seed_pool()
        except Exception as exc:
            err_msg = str(exc)[:100]
            with self._stats_lock:
                self.stats["status"] = "error"
                self.stats["last_error"] = err_msg
            append_panel_log(f"WS:{self.data.get('session_name', '?')}", f"Start failed: {err_msg}")
            return False, err_msg

        with self._stats_lock:
            self.stats.update({
                "status": "live",
                "start_time": time.time(),
                "sent": 0,
                "failed": 0,
                "renames": 0,
                "recycles": 0,
                "self_replies": 0,
                "last_error": None if ok == self.pool_size else f"only {ok}/{self.pool_size} sockets",
                "session_status": None,
                "session_error": None,
            })

        append_panel_log(f"WS:{self.data.get('session_name', '?')}", f"Live ({ok}/{self.pool_size} sockets)")
        self.msg_thread = threading.Thread(target=self._msg_loop, daemon=True)
        self.rename_thread = threading.Thread(target=self._rename_loop, daemon=True)
        self.rotate_thread = threading.Thread(target=self._ws_rotate_loop, daemon=True)
        self.health_thread = threading.Thread(target=self._health_check_loop, daemon=True)
        self.recycle_thread = threading.Thread(target=self._ws_recycle_loop, daemon=True)
        self.msg_thread.start()
        self.rename_thread.start()
        self.rotate_thread.start()
        self.health_thread.start()
        self.recycle_thread.start()
        if self.data.get("self_reply_enabled"):
            self.self_reply_thread = threading.Thread(target=self._self_reply_loop, daemon=True)
            self.self_reply_thread.start()
        return True, None

    def _msg_loop(self):
        self._executor = ThreadPoolExecutor(max_workers=8)
        next_fire = time.monotonic()

        try:
            while not self.stop_event.is_set():
                d_min = max(0.01, float(self.data.get("delay_min", 0.1)))
                d_max = max(d_min, float(self.data.get("delay_max", 0.2)))
                interval = random.uniform(d_min, d_max)

                with self._pool_lock:
                    live = sum(1 for s in self.sockets if s is not None)
                max_inflight = max(4, min(8, live * 2)) if live > 0 else 1

                now = time.monotonic()
                max_debt = max(1.5, interval * 20)
                if next_fire < now - max_debt:
                    next_fire = now

                wait = next_fire - now
                if wait > 0 and self.stop_event.wait(wait):
                    break

                with self._inflight_lock:
                    if self._inflight >= max_inflight:
                        next_fire += interval
                        if self.stop_event.wait(min(0.05, interval)):
                            break
                        continue
                    self._inflight += 1

                try:
                    self._executor.submit(self._fire_message_rr)
                except RuntimeError:
                    with self._inflight_lock:
                        self._inflight -= 1
                    break

                next_fire += interval
        finally:
            try:
                self._executor.shutdown(wait=False, cancel_futures=True)
            except Exception:
                pass
            self._executor = None

    def _is_ok(self, res) -> bool:
        if isinstance(res, dict):
            if res.get("ok") is True:
                return True
            if "response" in res and isinstance(res["response"], dict):
                d = res["response"].get("data", {})
                if d and any("message_id" in str(v) for v in d.values()):
                    return True
        return False

    def _fire_message_rr(self):
        global GLOBAL_MESSAGES_SENT
        try:
            if self.stop_event.is_set():
                return
            ok, ids = self._send_pool(self.build_message())
            if ok and ids and any(ids) and self.data.get("self_reply_enabled"):
                with self._own_lock:
                    self._own_msg_ids.append(ids)
        finally:
            with self._inflight_lock:
                self._inflight -= 1

    def _send_pool(self, text: str, reply_to: Optional[tuple] = None) -> tuple[bool, Optional[tuple]]:
        """Send text round-robin across the socket pool.

        reply_to is (message_id, item_id) of the target; returns (ok, (message_id, item_id)).
        """
        global GLOBAL_MESSAGES_SENT
        with self._pool_lock:
            n = len(self.sockets)
            if n == 0 or len(self.socket_locks) < n:
                return False, None
            with self._rr_lock:
                idx = self._rr_idx % n
                self._rr_idx = (self._rr_idx + 1) % n
            has_any = any(self.sockets[i] is not None for i in range(n))

        if not has_any:
            with self._stats_lock:
                self.stats["failed"] += 1
            return False, None

        for offset in range(n):
            with self._pool_lock:
                if offset >= len(self.sockets):
                    break
                i = (idx + offset) % len(self.sockets)
                sock_lock = self.socket_locks[i]
            if not sock_lock.acquire(timeout=2.0):
                continue
            try:
                with self._pool_lock:
                    sock = self.sockets[i] if i < len(self.sockets) else None
                if sock is None:
                    continue

                if reply_to:
                    r_mid, r_item = reply_to
                    quoted = {"key": {}, "message": {}}
                    if r_item:
                        quoted["key"]["id"] = str(r_item)
                    if r_mid:
                        quoted["message"]["message_id"] = str(r_mid)
                    res = sock.send_message(
                        self.data["thread_id"], {"text": text}, options={"quoted": quoted}
                    )
                    if not self._is_ok(res):
                        # Web (graphql) reply was rejected; retry once over the WebSocket transport.
                        first_err = str(res)[:80]
                        res = sock.send_message(
                            self.data["thread_id"], {"text": text},
                            options={"quoted": quoted, "transport": "ws"},
                        )
                        if not self._is_ok(res) and isinstance(res, dict) and res.get("transport") == "ws":
                            res = {"ok": True, "transport": "ws", **res}
                        elif not self._is_ok(res):
                            res = {"ok": False, "error": f"graphql: {first_err} | ws: {str(res)[:60]}"}
                else:
                    res = sock.send_message(self.data["thread_id"], {"text": text})

                if self._is_ok(res):
                    with self._stats_lock:
                        self.stats["sent"] += 1
                    with tasks_lock:
                        GLOBAL_MESSAGES_SENT += 1
                    return True, _extract_ids(res)
                with self._stats_lock:
                    self.stats["failed"] += 1
                    tag = f"reply->{reply_to}: " if reply_to else ""
                    self.stats["last_error"] = (tag + str(res))[:140]
                return False, None
            except Exception as exc:
                err_str = str(exc).lower()
                with self._stats_lock:
                    self.stats["last_error"] = f"send@{i}: {err_str[:80]}"
                if "timeout" in err_str or "timed out" in err_str:
                    with self._stats_lock:
                        self.stats["failed"] += 1
                    return False, None
                continue
            finally:
                sock_lock.release()

        with self._stats_lock:
            self.stats["failed"] += 1
        return False, None

    def _self_reply_loop(self):
        """Periodically reply to one of this worker's own sent messages, chaining replies."""
        while not self.stop_event.is_set():
            lo = max(5.0, float(self.data.get("self_reply_min", 30.0)))
            hi = max(lo, float(self.data.get("self_reply_max", 90.0)))
            if self.stop_event.wait(random.uniform(lo, hi)):
                break
            if self.stats.get("status") != "live":
                continue
            with self._own_lock:
                if not self._own_msg_ids:
                    continue
                target = random.choice(list(self._own_msg_ids))
            ok, new_ids = self._send_pool(self.build_message(), reply_to=target)
            if ok:
                with self._stats_lock:
                    self.stats["self_replies"] = int(self.stats.get("self_replies", 0)) + 1
                if new_ids and any(new_ids):
                    with self._own_lock:
                        self._own_msg_ids.append(new_ids)

    def _rotate_socket_at(self, idx: int):
        old = None
        with self._pool_lock:
            if idx >= len(self.sockets):
                return
            sock_lock = self.socket_locks[idx]
            if sock_lock.acquire(timeout=2.0):
                try:
                    old = self.sockets[idx]
                    self.sockets[idx] = None
                finally:
                    sock_lock.release()
            else:
                old = self.sockets[idx]
                self.sockets[idx] = None
        if old:
            try:
                old.disconnect()
            except Exception:
                pass
        backoff = 5
        while not self.stop_event.is_set():
            try:
                new = self._connect(f"rot{idx}", max_retries=2, retry_delay=1.5)
                with self._pool_lock:
                    if idx < len(self.sockets):
                        self.sockets[idx] = new
                        return
                try:
                    new.disconnect()
                except Exception:
                    pass
                return
            except Exception as exc:
                with self._stats_lock:
                    self.stats["last_error"] = f"rot{idx}: {str(exc)[:80]}"
                if self.stop_event.wait(backoff):
                    return
                backoff = min(backoff * 2, 60)

    def _ws_rotate_loop(self):
        with self._pool_lock:
            n = len(self.sockets)
        if n == 0:
            return
        base = time.monotonic() + random.uniform(WS_ROTATE_MIN, WS_ROTATE_MAX)
        next_rotate = [
            base + i * random.uniform(300, 900) + random.uniform(0, 120)
            for i in range(n)
        ]
        while not self.stop_event.is_set():
            now = time.monotonic()
            with self._pool_lock:
                curr_n = len(self.sockets)
            for i in range(curr_n):
                if self.stop_event.is_set():
                    break
                if i >= len(next_rotate):
                    next_rotate.append(time.monotonic() + random.uniform(WS_ROTATE_MIN, WS_ROTATE_MAX))
                if now >= next_rotate[i]:
                    self._rotate_socket_at(i)
                    next_rotate[i] = time.monotonic() + random.uniform(WS_ROTATE_MIN, WS_ROTATE_MAX)
            if self.stop_event.wait(5):
                break

    def _health_check_loop(self):
        while not self.stop_event.is_set():
            wait = random.uniform(WS_HEALTH_CHECK_MIN, WS_HEALTH_CHECK_MAX)
            if self.stop_event.wait(wait):
                break

            with self._pool_lock:
                sock = next((s for s in self.sockets if s is not None), None)
            if sock is None:
                with self._stats_lock:
                    self.stats["session_status"] = "error"
                    self.stats["session_error"] = "no live socket"
                continue

            try:
                health = sock.session_health()
                web = health.get("web") if isinstance(health, dict) else None
                logged_out = bool(health.get("logged_out", False)) if isinstance(health, dict) else False

                with self._stats_lock:
                    if logged_out:
                        self.stats["session_status"] = "logged_out"
                        self.stats["session_error"] = "logged_out=True"
                    elif web == "walled":
                        self.stats["session_status"] = "walled"
                        self.stats["session_error"] = "web=walled"
                    elif web == "ok":
                        self.stats["session_status"] = "ok"
                        self.stats["session_error"] = None
                    else:
                        self.stats["session_status"] = "error"
                        self.stats["session_error"] = f"unknown health: {health}"
            except Exception as exc:
                with self._stats_lock:
                    self.stats["session_status"] = "error"
                    self.stats["session_error"] = str(exc)[:100]

    def _rename_loop(self):
        """One-by-one group rename loop with spacing between threads and no instant multi-thread burst."""
        while not self.stop_event.is_set():
            r_min = max(1.0, float(self.data.get("rename_min", 5)))
            r_max = max(r_min, float(self.data.get("rename_max", 15)))
            if self.stop_event.wait(random.uniform(r_min, r_max)):
                break

            raw_tids = self.data.get("thread_ids")
            tids = parse_thread_ids(raw_tids) if isinstance(raw_tids, list) else []
            if not tids:
                single = str(self.data.get("thread_id", "")).strip()
                if single.isdigit():
                    tids = [single]

            new_name = self.build_gc_name()
            for idx, tid_str in enumerate(tids):
                if self.stop_event.is_set():
                    break
                with self._pool_lock:
                    sock = next((s for s in self.sockets if s is not None), None)
                if sock is None:
                    continue
                try:
                    sock.rename_group(tid_str, new_name)
                    with self._stats_lock:
                        self.stats["renames"] += 1
                except Exception as exc:
                    with self._stats_lock:
                        self.stats["last_error"] = f"rename@{tid_str}: {str(exc)[:80]}"
                if idx < len(tids) - 1 and self.stop_event.wait(RENAME_PER_THREAD_GAP_SEC):
                    break

    def recycle(self) -> tuple[bool, Optional[str]]:
        if not self._recycle_lock.acquire(blocking=False):
            return False, "Recycle already in progress"
        try:
            if self.stop_event.is_set() or self.stats.get("status") != "live":
                return False, "WS session is not live"

            with self._pool_lock:
                old_socks = list(self.sockets)
                n = len(old_socks)
                for i in range(n):
                    self.sockets[i] = None

            for s in old_socks:
                if s:
                    try:
                        s.disconnect()
                    except Exception:
                        pass

            with self._listen_lock:
                self.listen_threads = [t for t in self.listen_threads if t.is_alive()]

            ok = 0
            last_err = None
            for i in range(n):
                if self.stop_event.is_set():
                    break
                try:
                    new_s = self._connect(f"recycle{i}", max_retries=2, retry_delay=1.5)
                    with self._pool_lock:
                        if i < len(self.sockets):
                            old_slot = self.sockets[i]
                            self.sockets[i] = new_s
                            if old_slot:
                                try:
                                    old_slot.disconnect()
                                except Exception:
                                    pass
                            ok += 1
                        else:
                            new_s.disconnect()
                except Exception as exc:
                    last_err = str(exc)[:90]
                if i < n - 1 and self.stop_event.wait(0.6):
                    break

            with self._stats_lock:
                self.stats["recycles"] = int(self.stats.get("recycles", 0)) + 1
                if ok == 0 and n > 0:
                    self.stats["last_error"] = f"recycle failed: {last_err or 'no sockets'}"
                elif ok < n:
                    self.stats["last_error"] = f"recycle {ok}/{n} sockets ({last_err or ''})".strip()

            if ok == 0 and n > 0:
                return False, last_err or "No sockets reconnected during recycle"
            append_panel_log(f"WS:{self.data.get('session_name', '?')}", f"WS recycle complete ({ok}/{n} sockets)")
            return True, None
        finally:
            self._recycle_lock.release()

    def _ws_recycle_loop(self):
        if WS_WORKER_RECYCLE_SEC <= 0:
            return
        while not self.stop_event.is_set():
            if self.stop_event.wait(WS_WORKER_RECYCLE_SEC):
                break
            if self.stop_event.is_set() or self.stats.get("status") != "live":
                continue
            self.recycle()

    def stop(self):
        if self.stats.get("status") == "stopped":
            return
        self.stop_event.set()
        with self._stats_lock:
            self.stats["status"] = "stopping"
        self._cleanup()
        append_panel_log(f"WS:{self.data.get('session_name', '?')}", "Stopped")

    def _cleanup(self):
        with self._pool_lock:
            socks = list(self.sockets)
            self.sockets = [None] * len(self.sockets)
        for s in socks:
            if s:
                try:
                    s.disconnect()
                except Exception:
                    pass

        for t in (self.msg_thread, self.rename_thread, self.rotate_thread, self.health_thread, self.recycle_thread):
            if t and t.is_alive():
                t.join(timeout=1.5)
        with self._listen_lock:
            self.listen_threads = [t for t in self.listen_threads if t.is_alive()]

        with self._stats_lock:
            self.stats["status"] = "stopped"

    def get_stats(self) -> dict:
        if self._stats_lock.acquire(timeout=0.05):
            try:
                s = dict(self.stats)
            finally:
                self._stats_lock.release()
        else:
            s = dict(self.stats)

        if self._pool_lock.acquire(timeout=0.05):
            try:
                live = sum(1 for x in self.sockets if x is not None) if self.sockets else 0
                total = len(self.sockets) if self.sockets else self.pool_size
            finally:
                self._pool_lock.release()
        else:
            live = 0
            total = self.pool_size

        s["uptime"] = int(time.time() - s["start_time"]) if (s.get("start_time") and s.get("status") == "live") else 0
        s["sockets_live"] = live
        s["sockets_total"] = total
        s["socket_pool"] = self.pool_size
        return s


# ======================== GROUP CREATOR LOOP ========================

def is_creator_running(job_id: str) -> bool:
    with tasks_lock:
        return bool(group_creator_jobs.get(job_id, {}).get("running", False))


def set_creator_running(job_id: str, running: bool):
    with tasks_lock:
        if job_id in group_creator_jobs:
            group_creator_jobs[job_id]["running"] = running


def log_creator(job_id: str, msg: str, created_id: Optional[str] = None, err: Optional[str] = None):
    with tasks_lock:
        job = group_creator_jobs.get(job_id)
        if not job:
            return
        job["last_event"] = msg
        job["last_update"] = datetime.now().strftime("%H:%M:%S")
        if created_id:
            job["created_ids"].append(created_id)
            job["created_count"] = len(job["created_ids"])
        if err:
            job["errors"].append(err)
    append_panel_log(f"GC_JOB {job_id}", msg)


def group_creator_loop(job_id: str):
    with tasks_lock:
        job = group_creator_jobs.get(job_id)
        if not job:
            return
        cl: Client = job["client"]
        count = int(job["count"])
        title_tpl = str(job["title_template"])
        target_name = str(job["target_name"])
        usernames = list(job["usernames"])
        send_ping = bool(job["send_ping"])
        min_cd = float(job["min_cooldown"])
        max_cd = float(job["max_cooldown"])

    log_creator(job_id, f"Resolving {len(usernames)} username(s)...")
    resolved_ids, failed_users = resolve_usernames_to_ids(cl, usernames)
    if failed_users:
        log_creator(job_id, f"Unresolved: {', '.join(failed_users)}", err="; ".join(failed_users))

    if len(resolved_ids) < 2:
        set_creator_running(job_id, False)
        log_creator(
            job_id,
            f"Need >=2 valid usernames (resolved {len(resolved_ids)})",
            err=f"Only resolved {len(resolved_ids)} user IDs from {usernames}",
        )
        return

    log_creator(job_id, f"Resolved {len(resolved_ids)} users; creating {count} group(s)")

    for idx in range(1, count + 1):
        if not is_creator_running(job_id):
            log_creator(job_id, "Stopped by user")
            return

        rendered_title = title_tpl.replace("{TARGET}", target_name).replace("{N}", str(idx)).strip()
        if not rendered_title:
            rendered_title = f"Group {idx}"

        made = False
        for attempt in range(1, MAX_RETRIES + 1):
            if not is_creator_running(job_id):
                return
            try:
                tid_str = _create_single_group(cl, rendered_title, resolved_ids, send_ping)
                log_creator(job_id, f"Created {idx}/{count} -> {tid_str}", created_id=tid_str)
                made = True
                break
            except Exception as exc:
                err_short = f"#{idx} attempt {attempt}: {str(exc)[:55]}"
                backoff = min(300, 35 * attempt + random.uniform(5, 15))
                log_creator(job_id, f"Rate/API backoff {backoff:.0f}s ({str(exc)[:30]})", err=err_short)
                slept = 0.0
                while slept < backoff and is_creator_running(job_id):
                    step = min(1.0, backoff - slept)
                    time.sleep(step)
                    slept += step

        if not made and is_creator_running(job_id):
            log_creator(job_id, f"Skipped group {idx}/{count} after retries")

        if idx < count and is_creator_running(job_id):
            delay = random.uniform(min_cd, max_cd)
            log_creator(job_id, f"Cooldown {delay:.1f}s before group {idx + 1}/{count}")
            slept = 0.0
            while slept < delay and is_creator_running(job_id):
                step = min(1.0, delay - slept)
                time.sleep(step)
                slept += step

    set_creator_running(job_id, False)
    with tasks_lock:
        done_n = group_creator_jobs.get(job_id, {}).get("created_count", 0)
    log_creator(job_id, f"Completed ({done_n}/{count} created)")


# ======================== WORKER LOOP & MULTI-GC SENDER ========================

def is_task_running(task_id: str) -> bool:
    with tasks_lock:
        return bool(active_tasks.get(task_id, {}).get("running", False))


def set_task_running(task_id: str, running: bool):
    with tasks_lock:
        if task_id in active_tasks:
            active_tasks[task_id]["running"] = running


def log_task(task_id: str, msg: str):
    with tasks_lock:
        task = active_tasks.get(task_id)
        if not task:
            return
        task["last_event"] = msg
        task["last_update"] = datetime.now().strftime("%H:%M:%S")
    append_panel_log(f"TASK {task_id}", msg)


def next_delay(speed_mode: str) -> float:
    """Fast mode: 8-10 seconds. Slow mode: 50-60 seconds."""
    if speed_mode == "fast":
        return random.uniform(8.0, 10.0)
    return random.uniform(50.0, 60.0)


def _rename_thread_by_session(session_id: str, ua: str, tid_str: str, nc_title: str) -> tuple[bool, str]:
    """Renames a single thread using WS socket (with REST fallback)."""
    if not nc_title:
        return True, ""
    err_msg = ""

    if IGRAPIWEB_AVAILABLE and make_ig_web_socket is not None:
        sock = None
        try:
            sock = make_ig_web_socket(sessionid=session_id, user_agent=ua)
            for mode in ("dgw", "iris"):
                try:
                    sock.connect(dm_receive=mode)
                    break
                except Exception:
                    continue
            _apply_sock_timeout(sock, 8.0)
            sock.rename_group(str(tid_str), nc_title[:75])
            return True, ""
        except Exception as exc:
            err_msg = str(exc)[:60]
        finally:
            if sock is not None:
                try:
                    sock.disconnect()
                except Exception:
                    pass

    try:
        resp = requests.post(
            f"https://www.instagram.com/api/v1/direct_v2/threads/{tid_str}/update_title/",
            headers={
                "User-Agent": ua,
                "X-IG-App-ID": "936619743392459",
                "Referer": f"https://www.instagram.com/direct/t/{tid_str}/",
            },
            cookies={"sessionid": session_id},
            data={"title": nc_title[:75]},
            timeout=10,
        )
        if resp.status_code in (200, 201):
            return True, ""
        err_msg = f"{err_msg}; HTTP {resp.status_code}".strip("; ")
    except Exception as exc:
        err_msg = f"{err_msg}; {str(exc)[:50]}".strip("; ")

    return False, err_msg


def _do_nc_after_send(
    task_id: str,
    cl: Optional[Client],
    session_id: Optional[str],
    ua: str,
    tid_str: str,
    nc_title: str,
):
    if not nc_title or not is_task_running(task_id):
        return
    if cl is not None:
        try:
            cl.direct_thread_update_title(int(tid_str), nc_title)
            log_task(task_id, f"NC updated {tid_str} -> {nc_title[:28]}")
        except Exception as exc:
            log_task(task_id, f"NC err {tid_str}: {str(exc)[:40]}")
    elif session_id:
        ok, err = _rename_thread_by_session(session_id, ua, tid_str, nc_title)
        if ok:
            log_task(task_id, f"NC updated {tid_str} -> {nc_title[:28]}")
        else:
            log_task(task_id, f"NC err {tid_str}: {err[:40]}")


def worker_loop(task_id: str):
    global GLOBAL_MESSAGES_SENT
    with tasks_lock:
        task = active_tasks.get(task_id)
        if not task:
            return
        cl: Optional[Client] = task.get("client")
        session_id: Optional[str] = task.get("session_id")
        ua: str = task.get("ua") or random.choice(WS_UA_POOL)
        thread_ids = list(task["thread_ids"])
        target_name = task["target_name"]
        speed_mode = task.get("speed_mode", "slow")
        use_nc = bool(task.get("use_nc", True))

    single_line_tpl = get_active_single_line_template()
    title_tpl = get_active_group_title_template()
    raw_nc = title_tpl.replace("{TARGET}", target_name).strip() or target_name.strip()
    nc_title = format_nc_title(raw_nc) if (use_nc and raw_nc) else ""
    round_num = 0

    while is_task_running(task_id):
        try:
            round_num += 1
            nc_label = "NC:ON" if use_nc else "NC:OFF"
            log_task(task_id, f"Round {round_num} started ({speed_mode}, {nc_label})")
            for tid_str in thread_ids:
                if not is_task_running(task_id):
                    break

                expanded_msg = build_expanded_message(single_line_tpl, target_name)
                subtle_link = make_subtle_z_link()
                payload = (
                    f"{subtle_link}\n\n{expanded_msg}"
                    if random.choice([True, False])
                    else f"{expanded_msg}\n\n{subtle_link}"
                )

                sent = False
                for attempt in range(1, MAX_RETRIES + 1):
                    if not is_task_running(task_id):
                        break
                    try:
                        if cl is not None:
                            cl.direct_send(payload, thread_ids=[int(tid_str)])
                            sent = True
                        elif session_id:
                            s_ok, _, s_err = _send_and_rename_ws_gc(
                                session_id=session_id,
                                ua=ua,
                                tid_str=tid_str,
                                text_body=payload,
                                nc_title=None,
                            )
                            if not s_ok:
                                raise RuntimeError(s_err or "send failed")
                            sent = True
                        else:
                            raise RuntimeError("No sender client or session")

                        with tasks_lock:
                            GLOBAL_MESSAGES_SENT += 1
                            if task_id in active_tasks:
                                active_tasks[task_id]["msg_count"] += 1
                        log_task(task_id, f"Sent to {tid_str}")
                        break
                    except Exception as exc:
                        wait = 30 * attempt
                        log_task(task_id, f"Retry {attempt}/{MAX_RETRIES} ({str(exc)[:35]}) in {wait}s")
                        time.sleep(wait)

                if sent and use_nc and nc_title and is_task_running(task_id):
                    _do_nc_after_send(task_id, cl, session_id, ua, tid_str, nc_title)
                elif not sent and is_task_running(task_id):
                    log_task(task_id, f"Skipped thread {tid_str} after retries")

                delay = next_delay(speed_mode)
                log_task(task_id, f"Cooldown {delay:.1f}s ({speed_mode})")
                slept = 0.0
                while slept < delay and is_task_running(task_id):
                    step = min(1.0, delay - slept)
                    time.sleep(step)
                    slept += step
        except Exception as exc:
            log_task(task_id, f"Loop error: {str(exc)[:40]} (resting 60s)")
            time.sleep(60)

    log_task(task_id, "Stopped")


def is_multi_gc_running(job_id: str) -> bool:
    with tasks_lock:
        return bool(multi_gc_jobs.get(job_id, {}).get("running", False))


def set_multi_gc_running(job_id: str, running: bool):
    with tasks_lock:
        if job_id in multi_gc_jobs:
            multi_gc_jobs[job_id]["running"] = running


def log_multi_gc(job_id: str, msg: str, sent_inc: int = 0, rename_inc: int = 0):
    global GLOBAL_MESSAGES_SENT
    with tasks_lock:
        job = multi_gc_jobs.get(job_id)
        if not job:
            return
        if sent_inc > 0:
            job["msg_count"] += sent_inc
            GLOBAL_MESSAGES_SENT += sent_inc
        if rename_inc > 0:
            job["rename_count"] += rename_inc
        job["last_event"] = msg
        job["last_update"] = datetime.now().strftime("%H:%M:%S")
    append_panel_log(f"MGC {job_id}", msg)


def _send_and_rename_ws_gc(session_id: str, ua: str, tid_str: str, text_body: str, nc_title: Optional[str]) -> tuple[bool, bool, str]:
    """Sends text and optionally renames GC using WS socket (with REST fallback for send & rename)."""
    sent_ok = False
    renamed_ok = False
    err_msg = ""

    if IGRAPIWEB_AVAILABLE and make_ig_web_socket is not None:
        sock = None
        try:
            sock = make_ig_web_socket(sessionid=session_id, user_agent=ua)
            for mode in ("dgw", "iris"):
                try:
                    sock.connect(dm_receive=mode)
                    break
                except Exception:
                    continue
            _apply_sock_timeout(sock, 8.0)
            res = sock.send_message(str(tid_str), {"text": text_body})
            if isinstance(res, dict) and (res.get("ok") is True or "message_id" in str(res)):
                sent_ok = True
            else:
                sent_ok = True
        except Exception as exc:
            err_msg = str(exc)[:80]
        finally:
            if nc_title and sock is not None:
                try:
                    sock.rename_group(str(tid_str), nc_title[:75])
                    renamed_ok = True
                except Exception as exc:
                    err_msg = f"{err_msg}; nc:{str(exc)[:50]}".strip("; ")
            if sock is not None:
                try:
                    sock.disconnect()
                except Exception:
                    pass

    if not sent_ok:
        try:
            resp = requests.post(
                "https://www.instagram.com/api/v1/direct_v2/threads/broadcast/text/",
                headers={
                    "User-Agent": ua,
                    "X-IG-App-ID": "936619743392459",
                    "Referer": f"https://www.instagram.com/direct/t/{tid_str}/",
                },
                cookies={"sessionid": session_id},
                data={"thread_ids": f"[{tid_str}]", "text": text_body},
                timeout=10,
            )
            if resp.status_code in (200, 201):
                sent_ok = True
                err_msg = ""
            else:
                err_msg = f"HTTP {resp.status_code}"
        except Exception as exc:
            err_msg = str(exc)[:80]

    if nc_title and not renamed_ok:
        r_ok, r_err = _rename_thread_by_session(session_id, ua, tid_str, nc_title)
        if r_ok:
            renamed_ok = True
            err_msg = ""
        elif r_err:
            err_msg = f"{err_msg}; nc:{r_err}".strip("; ")

    return sent_ok, renamed_ok, err_msg


def multi_gc_loop(job_id: str):
    """Sends text to each GC, optionally changes that GC's name right after sending, then waits 8-10s (fast) or 50-60s (slow)."""
    with tasks_lock:
        job = multi_gc_jobs.get(job_id)
        if not job:
            return
        cl: Optional[Client] = job.get("client")
        session_id: Optional[str] = job.get("session_id")
        ua: str = job.get("ua") or random.choice(WS_UA_POOL)
        thread_ids = list(job["thread_ids"])
        target_name = job["target_name"]
        custom_text = (job.get("custom_text") or "").strip()
        nc_text = (job.get("nc_text") or "").strip()
        speed_mode = job.get("speed_mode", "slow")
        use_nc = bool(job.get("use_nc", True))

    single_line_tpl = get_active_single_line_template()
    title_tpl = get_active_group_title_template()
    round_num = 0

    while is_multi_gc_running(job_id):
        round_num += 1
        log_multi_gc(job_id, f"Round {round_num} ({speed_mode}, {'with NC' if use_nc else 'without NC'})")

        for tid_str in thread_ids:
            if not is_multi_gc_running(job_id):
                break

            if custom_text:
                link = make_subtle_z_link()
                emoji = random.choice(WS_EMOJI_POOL)
                payload = f"{link}\n\n{custom_text} <{emoji}>{WS_FOOTER}"
            else:
                expanded = build_expanded_message(single_line_tpl, target_name)
                link = make_subtle_z_link()
                payload = f"{link}\n\n{expanded}"

            nc_title = None
            if use_nc:
                base_nc = nc_text if nc_text else title_tpl
                raw_nc = base_nc.replace("{TARGET}", target_name).strip() or target_name.strip() or "GC"
                nc_title = format_nc_title(raw_nc)

            sent_ok = False
            renamed_ok = False
            last_err = ""

            if cl is not None:
                try:
                    cl.direct_send(payload, thread_ids=[int(tid_str)])
                    sent_ok = True
                except Exception as exc:
                    last_err = str(exc)[:60]

                if use_nc and nc_title:
                    try:
                        cl.direct_thread_update_title(int(tid_str), nc_title)
                        renamed_ok = True
                    except Exception as exc:
                        last_err = f"{last_err}; nc:{str(exc)[:40]}".strip("; ")
            elif session_id:
                sent_ok, renamed_ok, last_err = _send_and_rename_ws_gc(
                    session_id=session_id,
                    ua=ua,
                    tid_str=tid_str,
                    text_body=payload,
                    nc_title=nc_title if use_nc else None,
                )

            if sent_ok:
                status_str = f"Sent -> {tid_str}"
                if use_nc:
                    status_str += (" + NC" if renamed_ok else " (NC err)")
                log_multi_gc(job_id, status_str, sent_inc=1, rename_inc=1 if renamed_ok else 0)
            else:
                log_multi_gc(job_id, f"Err {tid_str}: {last_err[:45]}")

            if not is_multi_gc_running(job_id):
                break

            delay = next_delay(speed_mode)
            log_multi_gc(job_id, f"Next in {delay:.1f}s ({speed_mode})")
            slept = 0.0
            while slept < delay and is_multi_gc_running(job_id):
                step = min(0.5, delay - slept)
                time.sleep(step)
                slept += step

    log_multi_gc(job_id, "Stopped")


# ======================== REQUEST SCHEMAS ========================

class SessionLoginReq(BaseModel):
    session_id: str


class PasswordLoginReq(BaseModel):
    username: str
    password: str
    two_factor_code: Optional[str] = None


class StartTaskReq(BaseModel):
    username: Optional[str] = None
    ws_uid: Optional[str] = None
    session_id: Optional[str] = None
    thread_ids: list[str]
    target_name: str
    speed_mode: Optional[str] = "slow"
    use_nc: Optional[bool] = True


class StartMultiGcReq(BaseModel):
    username: Optional[str] = None
    ws_uid: Optional[str] = None
    session_id: Optional[str] = None
    thread_ids: list[str]
    target_name: Optional[str] = ""
    custom_text: Optional[str] = ""
    nc_text: Optional[str] = ""
    speed_mode: Optional[str] = "slow"
    use_nc: Optional[bool] = True


class TemplateReq(BaseModel):
    template: str
    group_title_template: Optional[str] = None


class CreateGroupsReq(BaseModel):
    username: str
    count: int = 1
    title_template: Optional[str] = None
    target_name: Optional[str] = ""
    usernames: list[str] = []
    send_ping: Optional[bool] = True
    min_cooldown: Optional[float] = 25.0
    max_cooldown: Optional[float] = 45.0


class AddUserToGroupReq(BaseModel):
    username: str
    thread_ids: list[str]
    member_input: str
    cooldown_sec: Optional[float] = 25.0


class InviteLinksReq(BaseModel):
    username: str
    thread_ids: list[str]


class WsAddReq(BaseModel):
    session_name: str
    session_id: str
    gc_name_text: str
    msg_text: str
    thread_id: str
    thread_ids: Optional[list[str]] = None
    socket_pool: Optional[int] = None
    delay_min: float = 0.1
    delay_max: float = 0.2
    rename_min: float = 5.0
    rename_max: float = 15.0
    auto_start: Optional[bool] = True
    self_reply_enabled: bool = False
    self_reply_min: float = 30.0
    self_reply_max: float = 90.0


class WsAdjustReq(BaseModel):
    msg_delta: Optional[float] = None
    rename_delta: Optional[float] = None


class WsSocketsReq(BaseModel):
    socket_pool: int


# ======================== AUTH / SESSION RESOLUTION ========================

def _resolve_sender_auth(username: Optional[str], ws_uid: Optional[str], session_id: Optional[str]):
    """Returns (client_or_none, session_id_or_none, ua_or_none, label)."""
    raw_sid = clean_session_id(session_id or "")
    if raw_sid:
        return None, raw_sid, random.choice(WS_UA_POOL), "sessionid"

    uid_clean = (ws_uid or "").strip()
    if uid_clean:
        with ws_lock:
            w = ws_sessions.get(uid_clean)
        if not w:
            raise RuntimeError(f"WS session '{uid_clean}' not found.")
        return None, clean_session_id(w.data.get("session_id", "")), w.data.get("ua"), f"WS:{w.data.get('session_name', uid_clean)}"

    uname = (username or "").strip().lstrip("@")
    if uname:
        cl = get_or_resume_client(uname)
        return cl, None, None, f"@{uname}"

    with ws_lock:
        first_w = next(iter(ws_sessions.values()), None)
    if first_w and first_w.data.get("session_id"):
        return None, clean_session_id(first_w.data["session_id"]), first_w.data.get("ua"), f"WS:{first_w.data.get('session_name', 'ws')}"

    raise RuntimeError("Select a WS login session, saved account, or enter a Session ID.")


# ======================== LIFESPAN & APP ========================

@asynccontextmanager
async def lifespan(app: FastAPI):
    saved_ws = load_ws_sessions_disk()
    with ws_lock:
        for uid, rec in saved_ws.items():
            if isinstance(rec, dict) and rec.get("session_id") and rec.get("thread_id"):
                rec["_uid"] = uid
                ws_sessions[uid] = WsSessionWorker(rec)
        to_start = [(uid, w) for uid, w in ws_sessions.items() if w.data.get("auto_start", False)]
    for uid, w in to_start:
        threading.Thread(target=w.start, daemon=True).start()
    append_panel_log("SYS", "Panel server initialized")
    yield


app = FastAPI(title="IG Web Controller", lifespan=lifespan)


# ======================== API ROUTES ========================

@app.get("/api/state")
async def api_state(x_panel_token: Optional[str] = Header(default=None), token: Optional[str] = None):
    verify_auth(x_panel_token, token)
    cpu = psutil.cpu_percent(interval=None)
    ram = psutil.virtual_memory()
    proc_mb = psutil.Process(os.getpid()).memory_info().rss / (1024 * 1024)

    tasks_view = []
    multi_gc_view = []
    creator_view = []
    running_count = 0

    if tasks_lock.acquire(timeout=0.05):
        try:
            tasks_view = [
                {
                    "task_id": tid,
                    "username": info.get("username"),
                    "target_name": info.get("target_name"),
                    "thread_ids": [str(x) for x in info.get("thread_ids", [])],
                    "speed_mode": info.get("speed_mode", "slow"),
                    "use_nc": bool(info.get("use_nc", True)),
                    "running": info.get("running"),
                    "msg_count": info.get("msg_count", 0),
                    "last_event": info.get("last_event", ""),
                    "last_update": info.get("last_update", ""),
                }
                for tid, info in active_tasks.items()
            ]
            multi_gc_view = [
                {
                    "job_id": jid,
                    "label": j.get("label", ""),
                    "target_name": j.get("target_name", ""),
                    "thread_ids": [str(x) for x in j.get("thread_ids", [])],
                    "speed_mode": j.get("speed_mode", "slow"),
                    "use_nc": bool(j.get("use_nc", True)),
                    "running": bool(j.get("running", False)),
                    "msg_count": j.get("msg_count", 0),
                    "rename_count": j.get("rename_count", 0),
                    "last_event": j.get("last_event", ""),
                    "last_update": j.get("last_update", ""),
                }
                for jid, j in multi_gc_jobs.items()
            ]
            creator_view = [
                {
                    "job_id": jid,
                    "username": j.get("username"),
                    "count": j.get("count", 0),
                    "created_count": j.get("created_count", 0),
                    "created_ids": list(j.get("created_ids", [])),
                    "running": bool(j.get("running", False)),
                    "last_event": j.get("last_event", ""),
                    "last_update": j.get("last_update", ""),
                    "errors": list(j.get("errors", []))[-5:],
                }
                for jid, j in group_creator_jobs.items()
            ]
            running_count = (
                sum(1 for t in active_tasks.values() if t.get("running"))
                + sum(1 for j in multi_gc_jobs.values() if j.get("running"))
            )
        finally:
            tasks_lock.release()

    ws_view = []
    ws_live_count = 0
    if ws_lock.acquire(timeout=0.05):
        try:
            ws_items = list(ws_sessions.items())
        finally:
            ws_lock.release()
    else:
        ws_items = list(ws_sessions.items())

    for uid, w in ws_items:
        st = w.get_stats()
        if st.get("status") == "live":
            ws_live_count += 1
        ws_view.append({
            "uid": uid,
            "session_name": w.data.get("session_name", "Unnamed"),
            "thread_id": w.data.get("thread_id", ""),
            "thread_ids": w.data.get("thread_ids", [w.data.get("thread_id", "")]),
            "gc_name_text": w.data.get("gc_name_text", ""),
            "msg_text": w.data.get("msg_text", ""),
            "socket_pool": w.pool_size,
            "delay_min": w.data.get("delay_min", 0.1),
            "delay_max": w.data.get("delay_max", 0.2),
            "rename_min": w.data.get("rename_min", 5.0),
            "rename_max": w.data.get("rename_max", 15.0),
            "auto_start": bool(w.data.get("auto_start", False)),
            "device_id": str(w.data.get("device_id", ""))[:12],
            "stats": st,
        })

    with logs_lock:
        logs_snapshot = list(PANEL_LOGS)

    return {
        "accounts": load_saved_accounts(),
        "template": get_active_single_line_template(),
        "group_title_template": get_active_group_title_template(),
        "is_custom_template": os.path.exists(TEMPLATE_FILE),
        "tasks": tasks_view,
        "multi_gc_jobs": multi_gc_view,
        "group_creator_jobs": creator_view,
        "ws_sessions": ws_view,
        "logs": logs_snapshot,
        "igrapiweb_available": IGRAPIWEB_AVAILABLE,
        "ws_socket_pool": WS_SOCKET_POOL,
        "min_safe_add_cooldown": MIN_SAFE_ADD_COOLDOWN,
        "global_messages_sent": GLOBAL_MESSAGES_SENT,
        "uptime": str(datetime.now() - BOT_START_TIME).split(".")[0],
        "stats": {
            "cpu_percent": round(cpu, 1),
            "ram_percent": round(ram.percent, 1),
            "ram_used_gb": round(ram.used / (1024**3), 2),
            "ram_total_gb": round(ram.total / (1024**3), 2),
            "rss_mb": round(proc_mb, 1),
            "running_tasks": running_count + ws_live_count,
        },
    }


@app.delete("/api/logs")
def api_clear_logs(x_panel_token: Optional[str] = Header(default=None), token: Optional[str] = None):
    verify_auth(x_panel_token, token)
    with logs_lock:
        PANEL_LOGS.clear()
    return {"ok": True}


# ---------- WS Multi-Sender API Endpoints ----------

@app.get("/api/ws/sessions")
def api_ws_list(x_panel_token: Optional[str] = Header(default=None), token: Optional[str] = None):
    verify_auth(x_panel_token, token)
    with ws_lock:
        items = [
            {
                "uid": uid,
                "session_name": w.data.get("session_name"),
                "thread_id": w.data.get("thread_id"),
                "thread_ids": w.data.get("thread_ids", [w.data.get("thread_id", "")]),
                "gc_name_text": w.data.get("gc_name_text"),
                "msg_text": w.data.get("msg_text"),
                "socket_pool": w.pool_size,
                "delay_min": w.data.get("delay_min"),
                "delay_max": w.data.get("delay_max"),
                "rename_min": w.data.get("rename_min"),
                "rename_max": w.data.get("rename_max"),
                "auto_start": bool(w.data.get("auto_start", False)),
                "stats": w.get_stats(),
            }
            for uid, w in ws_sessions.items()
        ]
    return {"ok": True, "igrapiweb_available": IGRAPIWEB_AVAILABLE, "socket_pool": WS_SOCKET_POOL, "sessions": items}


@app.post("/api/ws/sessions")
def api_ws_add(
    body: WsAddReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    sname = body.session_name.strip()
    sid = clean_session_id(body.session_id)
    tids = parse_thread_ids(body.thread_ids or [])
    tid = body.thread_id.strip()
    if tid.isdigit() and tid not in tids:
        tids.insert(0, tid)
    gc_text = body.gc_name_text.strip()
    msg_text = body.msg_text.strip()

    if not sname or not sid or not tids or not gc_text or not msg_text:
        raise HTTPException(status_code=400, detail="Session name, session ID, GC name text, message text, and at least 1 numeric thread ID are required.")
    if body.delay_min < 0.01 or body.delay_max < body.delay_min:
        raise HTTPException(status_code=400, detail="Invalid message delays (min >= 0.01, max >= min).")
    if body.rename_min < 1.0 or body.rename_max < body.rename_min:
        raise HTTPException(status_code=400, detail="Invalid rename delays (min >= 1.0, max >= min).")

    primary_tid = tids[0]
    pool_size = clamp_socket_pool(body.socket_pool if body.socket_pool is not None else WS_SOCKET_POOL)

    with ws_lock:
        dup = next(
            (w for w in ws_sessions.values() if w.data.get("session_id") == sid and w.data.get("thread_id") == primary_tid),
            None,
        )
        if dup:
            raise HTTPException(status_code=400, detail="Duplicate session_id + thread_id already exists in WS sessions.")
        existing = next((w for w in ws_sessions.values() if w.data.get("session_id") == sid), None)

    ua = existing.data.get("ua") if existing and existing.data.get("ua") else random.choice(WS_UA_POOL)
    dev_id = existing.data.get("device_id") if existing and existing.data.get("device_id") else uuid.uuid4().hex
    uid = uuid.uuid4().hex[:12]

    should_start = bool(True if body.auto_start is None else body.auto_start)
    rec = {
        "_uid": uid,
        "session_name": sname,
        "session_id": sid,
        "gc_name_text": gc_text,
        "msg_text": msg_text,
        "thread_id": primary_tid,
        "thread_ids": tids,
        "socket_pool": pool_size,
        "delay_min": float(body.delay_min),
        "delay_max": float(body.delay_max),
        "rename_min": float(body.rename_min),
        "rename_max": float(body.rename_max),
        "ua": ua,
        "device_id": dev_id,
        "auto_start": should_start,
        "self_reply_enabled": bool(body.self_reply_enabled),
        "self_reply_min": float(body.self_reply_min),
        "self_reply_max": float(body.self_reply_max),
    }

    worker = WsSessionWorker(rec)
    with ws_lock:
        ws_sessions[uid] = worker

    if should_start:
        threading.Thread(target=worker.start, daemon=True).start()

    save_ws_sessions_disk()
    append_panel_log("WS", f"Added session '{sname}' ({uid})")
    return {
        "ok": True,
        "uid": uid,
        "started": should_start,
        "error": None,
        "stats": worker.get_stats(),
    }


@app.post("/api/ws/sessions/{uid}/start")
def api_ws_start(
    uid: str,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    with ws_lock:
        w = ws_sessions.get(uid)
    if not w:
        raise HTTPException(status_code=404, detail="WS session not found.")
    w.data["auto_start"] = True
    threading.Thread(target=w.start, daemon=True).start()
    save_ws_sessions_disk()
    return {"ok": True, "uid": uid, "stats": w.get_stats()}


@app.post("/api/ws/sessions/{uid}/stop")
def api_ws_stop(
    uid: str,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    with ws_lock:
        w = ws_sessions.get(uid)
    if not w:
        raise HTTPException(status_code=404, detail="WS session not found.")
    w.data["auto_start"] = False
    threading.Thread(target=w.stop, daemon=True).start()
    save_ws_sessions_disk()
    return {"ok": True, "uid": uid, "stats": w.get_stats()}


@app.post("/api/ws/sessions/{uid}/recycle")
def api_ws_recycle(
    uid: str,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    with ws_lock:
        w = ws_sessions.get(uid)
    if not w:
        raise HTTPException(status_code=404, detail="WS session not found.")
    if w.stats.get("status") != "live":
        raise HTTPException(status_code=400, detail="WS session is not live.")
    threading.Thread(target=w.recycle, daemon=True).start()
    return {"ok": True, "uid": uid, "stats": w.get_stats()}


@app.post("/api/ws/sessions/{uid}/sockets")
def api_ws_sockets(
    uid: str,
    body: WsSocketsReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    with ws_lock:
        w = ws_sessions.get(uid)
    if not w:
        raise HTTPException(status_code=404, detail="WS session not found.")
    applied = w.set_socket_pool_size(body.socket_pool)
    save_ws_sessions_disk()
    return {"ok": True, "uid": uid, "socket_pool": applied, "stats": w.get_stats()}


@app.post("/api/ws/sessions/{uid}/adjust")
def api_ws_adjust(
    uid: str,
    body: WsAdjustReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    with ws_lock:
        w = ws_sessions.get(uid)
    if not w:
        raise HTTPException(status_code=404, detail="WS session not found.")

    if body.msg_delta is not None:
        nm = max(0.01, float(w.data.get("delay_min", 0.1)) + float(body.msg_delta))
        nx = max(nm, float(w.data.get("delay_max", 0.2)) + float(body.msg_delta))
        w.data["delay_min"] = round(nm, 2)
        w.data["delay_max"] = round(nx, 2)

    if body.rename_delta is not None:
        nm = max(1.0, float(w.data.get("rename_min", 5.0)) + float(body.rename_delta))
        nx = max(nm, float(w.data.get("rename_max", 15.0)) + float(body.rename_delta))
        w.data["rename_min"] = round(nm, 1)
        w.data["rename_max"] = round(nx, 1)

    save_ws_sessions_disk()
    return {
        "ok": True,
        "uid": uid,
        "delay_min": w.data["delay_min"],
        "delay_max": w.data["delay_max"],
        "rename_min": w.data["rename_min"],
        "rename_max": w.data["rename_max"],
    }


@app.delete("/api/ws/sessions/{uid}")
def api_ws_delete(
    uid: str,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    with ws_lock:
        w = ws_sessions.pop(uid, None)
    if not w:
        raise HTTPException(status_code=404, detail="WS session not found.")
    threading.Thread(target=w.stop, daemon=True).start()
    save_ws_sessions_disk()
    append_panel_log("WS", f"Deleted session {uid}")
    return {"ok": True, "deleted": uid}


# ---------- Existing Instagrapi, Thread Fetcher & Group Endpoints ----------

@app.post("/api/login/session")
def api_login_session(
    body: SessionLoginReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    cleaned = clean_session_id(body.session_id)
    if not cleaned:
        raise HTTPException(status_code=400, detail="Session ID is empty.")
    try:
        cl = make_ig_client()
        cl.login_by_sessionid(cleaned)
        if not getattr(cl, "user_id", None):
            info = cl.account_info()
            if getattr(info, "pk", None):
                cl.user_id = int(info.pk)
        if not getattr(cl, "user_id", None):
            raise RuntimeError("Could not verify Instagram user ID.")
        uname = resolve_username(cl)
        save_session(cl, uname, "sessionid")
        append_panel_log("AUTH", f"Session login success for @{uname}")
        return {"ok": True, "username": uname, "user_id": str(cl.user_id)}
    except Exception as exc:
        raise HTTPException(status_code=400, detail=f"{type(exc).__name__}: {str(exc)[:180]}")


@app.post("/api/login/password")
def api_login_password(
    body: PasswordLoginReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    uname = body.username.strip().lstrip("@")
    if not uname or not body.password:
        raise HTTPException(status_code=400, detail="Username and password are required.")

    cl = None
    try:
        if body.two_factor_code and uname in pending_2fa:
            cl = pending_2fa[uname]["client"]
            cl.login(uname, body.password, verification_code=body.two_factor_code.strip())
            pending_2fa.pop(uname, None)
            save_session(cl, uname, "password+2fa")
            append_panel_log("AUTH", f"Password+2FA login success for @{uname}")
            return {"ok": True, "username": uname, "user_id": str(cl.user_id)}

        cl = make_ig_client()
        cl.login(uname, body.password)
        save_session(cl, uname, "password")
        append_panel_log("AUTH", f"Password login success for @{uname}")
        return {"ok": True, "username": uname, "user_id": str(cl.user_id)}
    except TwoFactorRequired:
        if cl is not None:
            pending_2fa[uname] = {"client": cl, "password": body.password}
        return JSONResponse(
            status_code=202,
            content={"two_factor_required": True, "username": uname, "detail": "Enter 6-digit 2FA code."},
        )
    except BadPassword:
        raise HTTPException(status_code=401, detail="Incorrect Instagram password.")
    except ClientNeedsUpgradeError:
        raise HTTPException(
            status_code=400,
            detail="Instagram rejected app version (ClientNeedsUpgradeError). Upgrade instagrapi, set IG_APP_VERSION / IG_VERSION_CODE, or use Session ID fallback.",
        )
    except Exception as exc:
        msg = str(exc)
        if "out of date" in msg.lower() or "upgrade your app" in msg.lower():
            msg = f"{msg} — Upgrade instagrapi or set IG_APP_VERSION / IG_VERSION_CODE, or use Session ID fallback."
        raise HTTPException(status_code=400, detail=f"{type(exc).__name__}: {msg[:200]}")


@app.delete("/api/accounts/{username}")
def api_delete_account(
    username: str,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    delete_saved_account(username)
    append_panel_log("AUTH", f"Deleted saved account @{username}")
    return {"ok": True, "removed": username}


@app.get("/api/threads")
def api_threads_query(
    username: Optional[str] = None,
    ws_uid: Optional[str] = None,
    session_id: Optional[str] = None,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    try:
        cl, sid, ua, _ = _resolve_sender_auth(username, ws_uid, session_id)
        if cl is not None:
            return {"ok": True, "threads": list_threads(cl)}
        return {"ok": True, "threads": fetch_threads_via_sessionid(sid or "", ua=ua)}
    except Exception as exc:
        raise HTTPException(status_code=400, detail=f"{type(exc).__name__}: {str(exc)[:180]}")


@app.get("/api/threads/{username}")
def api_threads(
    username: str,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    try:
        cl = get_or_resume_client(username)
        return {"ok": True, "threads": list_threads(cl)}
    except Exception as exc:
        raise HTTPException(status_code=400, detail=f"{type(exc).__name__}: {str(exc)[:180]}")


@app.post("/api/groups/create")
def api_create_groups(
    body: CreateGroupsReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    uname = body.username.strip().lstrip("@")
    count = int(body.count or 1)
    unames = parse_usernames(body.usernames)
    if not uname:
        raise HTTPException(status_code=400, detail="Account username is required.")
    if count < 1 or count > 50:
        raise HTTPException(status_code=400, detail="Group count must be between 1 and 50.")
    if len(unames) < 2:
        raise HTTPException(status_code=400, detail="Enter at least 2 usernames (comma-separated) to create a group.")

    min_cd = max(10.0, float(body.min_cooldown if body.min_cooldown is not None else 25.0))
    max_cd = max(min_cd, float(body.max_cooldown if body.max_cooldown is not None else 45.0))
    title_tpl = (body.title_template or "").strip() or get_active_group_title_template()
    target_name = (body.target_name or "").strip()
    send_ping = bool(True if body.send_ping is None else body.send_ping)

    try:
        cl = get_or_resume_client(uname)
    except Exception as exc:
        raise HTTPException(status_code=400, detail=str(exc))

    job_id = f"G{uuid.uuid4().hex[:6].upper()}"
    with tasks_lock:
        group_creator_jobs[job_id] = {
            "job_id": job_id,
            "client": cl,
            "username": uname,
            "count": count,
            "title_template": title_tpl,
            "target_name": target_name,
            "usernames": unames,
            "send_ping": send_ping,
            "min_cooldown": min_cd,
            "max_cooldown": max_cd,
            "running": True,
            "created_count": 0,
            "created_ids": [],
            "errors": [],
            "last_event": f"Queued ({count} groups, {len(unames)} users, {min_cd:.0f}-{max_cd:.0f}s cd)",
            "last_update": datetime.now().strftime("%H:%M:%S"),
        }

    threading.Thread(target=group_creator_loop, args=(job_id,), daemon=True).start()
    return {"ok": True, "job_id": job_id, "count": count, "usernames": unames}


@app.post("/api/groups/create/{job_id}/stop")
def api_stop_group_creator(
    job_id: str,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    set_creator_running(job_id, False)
    return {"ok": True, "job_id": job_id}


@app.post("/api/groups/add-user")
def api_add_user_to_group(
    body: AddUserToGroupReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    uname = body.username.strip().lstrip("@")
    tids = parse_thread_ids(body.thread_ids)
    raw_member = (body.member_input or "").strip()
    if not uname or not tids or not raw_member:
        raise HTTPException(
            status_code=400,
            detail="Account username, at least 1 numeric group thread ID, and a target user ID or @username are required.",
        )

    requested_cd = float(body.cooldown_sec if body.cooldown_sec is not None else 25.0)
    safe_cd = max(MIN_SAFE_ADD_COOLDOWN, requested_cd)

    try:
        cl = get_or_resume_client(uname)
        target_uid, resolved_label = resolve_single_member_id(cl, raw_member)
    except Exception as exc:
        raise HTTPException(status_code=400, detail=f"{type(exc).__name__}: {str(exc)[:180]}")

    results = []
    for idx, tid_str in enumerate(tids):
        added = False
        last_err = ""
        for attempt in range(1, 3):
            try:
                add_user_to_group_thread(cl, tid_str, target_uid)
                added = True
                results.append({
                    "thread_id": tid_str,
                    "target_user_id": str(target_uid),
                    "target_label": resolved_label,
                    "status": "added",
                })
                append_panel_log("ADD_USER", f"Added {resolved_label} to thread {tid_str}")
                break
            except Exception as exc:
                last_err = str(exc)[:140]
                if attempt < 2:
                    time.sleep(random.uniform(10.0, 18.0))
        if not added:
            results.append({
                "thread_id": tid_str,
                "target_user_id": str(target_uid),
                "target_label": resolved_label,
                "status": f"failed: {last_err}",
            })
            append_panel_log("ADD_USER", f"Failed adding {resolved_label} to {tid_str}: {last_err[:50]}")

        if idx < len(tids) - 1:
            jitter = random.uniform(0.0, 5.0)
            time.sleep(safe_cd + jitter)

    ok_count = sum(1 for r in results if r.get("status") == "added")
    return {
        "ok": True,
        "target_user_id": str(target_uid),
        "target_label": resolved_label,
        "safety_cooldown_sec": safe_cd,
        "added_count": ok_count,
        "total_threads": len(tids),
        "results": results,
    }


@app.post("/api/groups/invite-links")
def api_group_invite_links(
    body: InviteLinksReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    uname = body.username.strip().lstrip("@")
    tids = parse_thread_ids(body.thread_ids)
    if not uname or not tids:
        raise HTTPException(status_code=400, detail="Select or enter at least 1 valid numeric GC thread ID.")

    try:
        cl = get_or_resume_client(uname)
    except Exception as exc:
        raise HTTPException(status_code=400, detail=str(exc))

    results = []
    for idx, tid_str in enumerate(tids):
        results.append(extract_group_invite_link(cl, tid_str))
        if idx < len(tids) - 1:
            time.sleep(random.uniform(1.5, 3.0))

    return {"ok": True, "results": results}


@app.post("/api/tasks/start")
def api_start_task(
    body: StartTaskReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    target = body.target_name.strip()
    tids = parse_thread_ids(body.thread_ids)
    speed = (body.speed_mode or "slow").strip().lower()
    use_nc = bool(True if body.use_nc is None else body.use_nc)
    if speed not in ("slow", "fast"):
        raise HTTPException(status_code=400, detail="speed_mode must be 'slow' or 'fast'.")
    if not target or not tids:
        raise HTTPException(status_code=400, detail="Target name and at least 1 valid numeric thread ID required.")

    try:
        cl, sid, ua, label = _resolve_sender_auth(body.username, body.ws_uid, body.session_id)
    except Exception as exc:
        raise HTTPException(status_code=400, detail=str(exc))

    task_id = f"T{uuid.uuid4().hex[:6].upper()}"
    with tasks_lock:
        active_tasks[task_id] = {
            "client": cl,
            "session_id": sid,
            "ua": ua,
            "username": label,
            "thread_ids": tids,
            "target_name": target,
            "speed_mode": speed,
            "use_nc": use_nc,
            "running": True,
            "msg_count": 0,
            "last_event": f"Queued ({speed}, {'with NC' if use_nc else 'no NC'})",
            "last_update": datetime.now().strftime("%H:%M:%S"),
        }

    threading.Thread(target=worker_loop, args=(task_id,), daemon=True).start()
    return {"ok": True, "task_id": task_id, "speed_mode": speed, "use_nc": use_nc, "thread_ids": tids}


@app.post("/api/tasks/{task_id}/stop")
def api_stop_task(
    task_id: str,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    set_task_running(task_id, False)
    return {"ok": True, "task_id": task_id}


@app.delete("/api/tasks/{task_id}")
def api_delete_task(
    task_id: str,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    with tasks_lock:
        task = active_tasks.get(task_id)
        if not task:
            raise HTTPException(status_code=404, detail="Task not found.")
        if task.get("running"):
            raise HTTPException(status_code=400, detail="Stop the task before removing it.")
        del active_tasks[task_id]
    append_panel_log("TASK", f"Removed stopped task {task_id}")
    return {"ok": True, "removed": task_id}


@app.post("/api/multi-gc/start")
def api_start_multi_gc(
    body: StartMultiGcReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    tids = parse_thread_ids(body.thread_ids)
    target = (body.target_name or "").strip()
    custom_text = (body.custom_text or "").strip()
    nc_text = (body.nc_text or "").strip()
    speed = (body.speed_mode or "slow").strip().lower()
    use_nc = bool(True if body.use_nc is None else body.use_nc)

    if speed not in ("slow", "fast"):
        raise HTTPException(status_code=400, detail="speed_mode must be 'slow' or 'fast'.")
    if len(tids) < 1:
        raise HTTPException(status_code=400, detail="Select or enter at least 1 valid numeric GC thread ID.")
    if not target and not custom_text:
        raise HTTPException(status_code=400, detail="Enter a target name or custom text to send.")

    try:
        cl, sid, ua, label = _resolve_sender_auth(body.username, body.ws_uid, body.session_id)
    except Exception as exc:
        raise HTTPException(status_code=400, detail=str(exc))

    job_id = f"M{uuid.uuid4().hex[:6].upper()}"
    with tasks_lock:
        multi_gc_jobs[job_id] = {
            "job_id": job_id,
            "client": cl,
            "session_id": sid,
            "ua": ua,
            "label": label,
            "thread_ids": tids,
            "target_name": target or custom_text[:30],
            "custom_text": custom_text,
            "nc_text": nc_text,
            "speed_mode": speed,
            "use_nc": use_nc,
            "running": True,
            "msg_count": 0,
            "rename_count": 0,
            "last_event": f"Queued ({len(tids)} GCs, {speed}, {'with NC' if use_nc else 'no NC'})",
            "last_update": datetime.now().strftime("%H:%M:%S"),
        }

    threading.Thread(target=multi_gc_loop, args=(job_id,), daemon=True).start()
    return {"ok": True, "job_id": job_id, "thread_ids": tids, "speed_mode": speed, "use_nc": use_nc}


@app.post("/api/multi-gc/{job_id}/stop")
def api_stop_multi_gc(
    job_id: str,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    set_multi_gc_running(job_id, False)
    return {"ok": True, "job_id": job_id}


@app.post("/api/tasks/stop-all")
def api_stop_all(x_panel_token: Optional[str] = Header(default=None), token: Optional[str] = None):
    verify_auth(x_panel_token, token)
    with tasks_lock:
        for info in active_tasks.values():
            info["running"] = False
        for job in multi_gc_jobs.values():
            job["running"] = False
        for job in group_creator_jobs.values():
            job["running"] = False
    with ws_lock:
        ws_workers = list(ws_sessions.values())
    for w in ws_workers:
        w.data["auto_start"] = False
        threading.Thread(target=w.stop, daemon=True).start()
    save_ws_sessions_disk()
    append_panel_log("SYS", "Stop-all executed")
    return {"ok": True}


@app.post("/api/template")
def api_set_template(
    body: TemplateReq,
    x_panel_token: Optional[str] = Header(default=None),
    token: Optional[str] = None,
):
    verify_auth(x_panel_token, token)
    try:
        set_active_template(body.template, body.group_title_template)
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc))
    append_panel_log("TPL", "Updated message / group title templates")
    return {
        "ok": True,
        "template": get_active_single_line_template(),
        "group_title_template": get_active_group_title_template(),
    }


@app.post("/api/template/reset")
def api_reset_template(x_panel_token: Optional[str] = Header(default=None), token: Optional[str] = None):
    verify_auth(x_panel_token, token)
    reset_active_template()
    append_panel_log("TPL", "Reset templates to defaults")
    return {
        "ok": True,
        "template": get_active_single_line_template(),
        "group_title_template": get_active_group_title_template(),
    }


# ======================== WEB UI ========================

HTML_PAGE = """<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>ρ 𝕣 ꪜ 𝕣 अब्बू ☽ · IG Web Controller</title>
  <style>
    :root {
      --bg: #0b0d14;
      --card: #151923;
      --border: #272e3f;
      --text: #eef2ff;
      --muted: #94a3b8;
      --accent: #3b82f6;
      --green: #22c55e;
      --red: #ef4444;
      --amber: #f59e0b;
    }
    * { box-sizing: border-box; font-family: system-ui, -apple-system, sans-serif; }
    body { margin: 0; background: var(--bg); color: var(--text); padding: 20px; }
    .wrap { max-width: 1120px; margin: 0 auto; display: grid; gap: 16px; }

    @keyframes rgbShift {
      0% { background-position: 0% 50%; }
      50% { background-position: 100% 50%; }
      100% { background-position: 0% 50%; }
    }
    @keyframes pulseGlow {
      0%, 100% {
        box-shadow: 0 0 22px rgba(236, 72, 153, 0.35), 0 0 42px rgba(59, 130, 246, 0.25);
        transform: translateY(0px);
      }
      50% {
        box-shadow: 0 0 30px rgba(34, 211, 238, 0.45), 0 0 54px rgba(168, 85, 247, 0.35);
        transform: translateY(-1px);
      }
    }

    .hero-banner {
      position: relative;
      border-radius: 16px;
      padding: 2px;
      background: linear-gradient(120deg, #ff2a85, #ff8a00, #ffd600, #00f5a0, #00d9f5, #8b5cf6, #ff2a85);
      background-size: 300% 300%;
      animation: rgbShift 6s ease infinite, pulseGlow 3.2s ease-in-out infinite;
    }
    .hero-banner-inner {
      background: radial-gradient(circle at 20% 20%, rgba(236, 72, 153, 0.22), transparent 45%),
                  radial-gradient(circle at 80% 30%, rgba(34, 211, 238, 0.22), transparent 45%),
                  radial-gradient(circle at 50% 90%, rgba(168, 85, 247, 0.24), transparent 55%),
                  #0e111b;
      border-radius: 14px;
      padding: 24px 20px;
      text-align: center;
    }
    .hero-banner-text {
      font-size: clamp(2rem, 5vw, 3.25rem);
      font-weight: 900;
      letter-spacing: 0.05em;
      line-height: 1.2;
      background: linear-gradient(90deg, #ff4ecd, #ffbe0b, #00f5d4, #4cc9f0, #c77dff, #ff4ecd);
      background-size: 250% 250%;
      -webkit-background-clip: text;
      background-clip: text;
      color: transparent;
      animation: rgbShift 5s linear infinite;
      filter: drop-shadow(0 0 14px rgba(236, 72, 153, 0.35));
      word-break: break-word;
    }

    .top { display: flex; flex-wrap: wrap; justify-content: space-between; align-items: center; gap: 12px; }
    .grid-2 { display: grid; grid-template-columns: repeat(auto-fit, minmax(340px, 1fr)); gap: 16px; }
    .card { background: var(--card); border: 1px solid var(--border); border-radius: 12px; padding: 16px; }
    h1, h2, h3 { margin: 0 0 10px; }
    h1 { font-size: 1.35rem; }
    h2 { font-size: 1.05rem; }
    label { display: block; font-size: 0.85rem; color: var(--muted); margin: 10px 0 4px; }
    input, select, textarea {
      width: 100%; background: #0d1017; color: var(--text); border: 1px solid var(--border);
      border-radius: 8px; padding: 9px 11px; font-size: 0.92rem;
    }
    button {
      background: linear-gradient(135deg, #3b82f6, #8b5cf6); color: #fff; border: 0; border-radius: 8px;
      padding: 8px 12px; font-weight: 600; cursor: pointer; font-size: 0.85rem;
    }
    button:hover { opacity: 0.92; }
    button.secondary { background: #242b3d; color: var(--text); }
    button.picked { background: linear-gradient(135deg, #ec4899, #8b5cf6); border: 1px solid #f472b6; color: #fff; }
    button.danger { background: var(--red); }
    button.warn { background: var(--amber); color: #111; }
    .row { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 10px; align-items: center; }
    .two-col-inline { display: grid; grid-template-columns: 1fr 1fr; gap: 8px; }
    .picker-box { display: flex; flex-direction: column; gap: 6px; max-height: 200px; overflow-y: auto; margin-top: 8px; }
    .pick-btn { width: 100%; text-align: left; display: flex; justify-content: space-between; align-items: center; gap: 8px; }
    .tid-mono { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 0.76rem; opacity: 0.85; word-break: break-all; }
    .logs-box {
      background: #090c12;
      border: 1px solid var(--border);
      border-radius: 8px;
      padding: 10px 12px;
      height: 260px;
      overflow-y: auto;
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      font-size: 0.78rem;
      line-height: 1.45;
      color: #cbd5e1;
      white-space: pre-wrap;
      word-break: break-word;
      margin-top: 10px;
    }
    .log-line { padding: 2px 0; border-bottom: 1px solid rgba(39, 46, 63, 0.45); }
    .log-line:last-child { border-bottom: 0; }
    .badge { display: inline-block; padding: 2px 8px; border-radius: 999px; font-size: 0.78rem; font-weight: 600; }
    .on { background: rgba(34,197,94,0.16); color: var(--green); }
    .off { background: rgba(239,68,68,0.16); color: var(--red); }
    .speed-badge { background: rgba(59,130,246,0.16); color: #93c5fd; }
    .nc-badge { background: rgba(245,158,11,0.16); color: #fcd34d; }
    .muted { color: var(--muted); font-size: 0.85rem; }
    .list-item { border-top: 1px solid var(--border); padding: 10px 0; display: flex; justify-content: space-between; align-items: flex-start; gap: 10px; }
    .list-item:first-child { border-top: 0; }
    .link-box { margin-top: 10px; display: flex; flex-direction: column; gap: 6px; max-height: 200px; overflow-y: auto; }
    .link-row { background: #0d1017; border: 1px solid var(--border); border-radius: 8px; padding: 8px 10px; font-size: 0.82rem; }
    details { margin-top: 14px; border-top: 1px solid var(--border); padding-top: 10px; }
    summary { cursor: pointer; color: var(--muted); font-size: 0.85rem; }
    .toast { position: fixed; bottom: 18px; right: 18px; background: #1f2937; border: 1px solid var(--border); padding: 10px 14px; border-radius: 8px; display: none; z-index: 50; max-width: 420px; }
  </style>
</head>
<body>
  <div class="wrap">
    <div class="hero-banner">
      <div class="hero-banner-inner">
        <div class="hero-banner-text">ρ 𝕣 ꪜ 𝕣 अब्बू ☽</div>
      </div>
    </div>

    <div class="top">
      <div>
        <h1>Instagram Automation Web Panel</h1>
        <div class="muted" id="statsBar">Loading stats...</div>
      </div>
      <div class="row" style="margin:0;">
        <input id="tokenInput" type="password" placeholder="Panel Token (if set)" style="width:190px;" />
        <button class="secondary" onclick="saveToken()">Save Token</button>
        <button class="danger" onclick="stopAll()">Stop All</button>
      </div>
    </div>

    <div class="card">
      <h2>All Running Tasks</h2>
      <div class="muted" id="allRunningSummary">Unified live view of all currently running tasks across all modules.</div>
      <div id="allRunningTasksList" class="muted" style="margin-top:8px;">No running tasks right now.</div>
    </div>

    <div class="grid-2">
      <div class="card">
        <h2>1. Login (Username & Password)</h2>
        <label>Instagram Username</label>
        <input id="igUser" placeholder="Instagram username" />
        <label>Instagram Password</label>
        <input id="igPass" type="password" placeholder="Instagram password" />
        <div id="tfaBox" style="display:none;">
          <label>6-Digit 2FA Code</label>
          <input id="ig2fa" placeholder="6-digit 2FA code" />
        </div>
        <div class="row"><button onclick="loginPassword()">Login with Password</button></div>

        <details>
          <summary>Fallback: Login via Session ID</summary>
          <label>Session ID Cookie</label>
          <input id="sidInput" type="password" placeholder="Paste sessionid cookie value" />
          <div class="row"><button class="secondary" onclick="loginSession()">Login with Session ID</button></div>
        </details>

        <h3 style="margin-top:16px; font-size:0.95rem;">Saved Accounts</h3>
        <div id="accountsList" class="muted">None yet.</div>
      </div>

      <div class="card">
        <h2>2. Start Task & GC / Chat Fetcher</h2>
        <label>Login Source (WS Session or Saved Account)</label>
        <select id="taskAccount" onchange="syncAccountSelectors(this.value)"></select>

        <div class="row">
          <button class="secondary" onclick="fetchThreads(true)">Fetch GC List</button>
          <button class="secondary" onclick="fetchThreads(false)">Fetch All Chats</button>
          <button class="secondary" onclick="selectAllLoaded(true)">Select All</button>
          <button class="secondary" onclick="selectAllLoaded(false)">Clear</button>
          <span class="muted" id="threadStatus"></span>
        </div>

        <div id="threadPicker" class="picker-box"></div>

        <label>Thread IDs (pick from GC list above or paste comma-separated IDs)</label>
        <input id="threadIdsInput" type="text" placeholder="Fetched GCs appear above, or paste numeric Thread IDs" />

        <label>Target Name ({TARGET})</label>
        <input id="targetInput" placeholder="Enter target name" />

        <div class="two-col-inline">
          <div>
            <label>Message Speed</label>
            <select id="speedMode">
              <option value="slow" selected>Slow (50–60s)</option>
              <option value="fast">Fast (8–10s)</option>
            </select>
          </div>
          <div>
            <label>Name Change (NC) Mode</label>
            <select id="ncMode">
              <option value="true" selected>With NC</option>
              <option value="false">Without NC</option>
            </select>
          </div>
        </div>

        <div class="row"><button onclick="startTask()">Start Task</button></div>
      </div>
    </div>

    <div class="card">
      <h2>3. Multi-GC Text + NC Sender (Separate Feature)</h2>
      <div class="muted">Sends text to each selected/entered GC, then optionally changes that GC's name (With NC / Without NC) before moving to the next GC. Uses the same WS login session.</div>

      <div class="grid-2" style="margin-top:8px;">
        <div>
          <label>WS Session / Login</label>
          <select id="mgcLoginSelect"></select>

          <label>Target Name ({TARGET}) or Custom Text</label>
          <input id="mgcTargetInput" placeholder="Target name for template (or leave blank if using custom text)" />

          <label>Custom Message Text (optional — uses template if blank)</label>
          <input id="mgcCustomText" placeholder="Optional custom message text" />
        </div>
        <div>
          <label>GC Thread IDs (uses Selected Thread IDs above if left blank)</label>
          <input id="mgcThreadIdsInput" placeholder="Leave blank to use Selected Thread IDs, or paste comma-separated GC IDs" />

          <div class="two-col-inline">
            <div>
              <label>Speed Mode</label>
              <select id="mgcSpeedMode">
                <option value="fast" selected>Fast (8–10s)</option>
                <option value="slow">Slow (50–60s)</option>
              </select>
            </div>
            <div>
              <label>NC Option</label>
              <select id="mgcNcMode">
                <option value="true" selected>With NC (send text then rename GC)</option>
                <option value="false">Without NC (send text only)</option>
              </select>
            </div>
          </div>

          <label>New GC Name Text (optional — defaults to Group Name Template / Target)</label>
          <input id="mgcNcText" placeholder="Optional GC name after sending text" />
        </div>
      </div>

      <div class="row">
        <button onclick="startMultiGc()">Start Multi-GC Sender</button>
        <button class="secondary" onclick="fillMultiGcFromSelected()">Copy Selected GCs</button>
      </div>

      <div id="multiGcJobsList" class="muted" style="margin-top:10px;">No Multi-GC sender jobs yet.</div>
    </div>

    <div class="grid-2">
      <div class="card">
        <h2>4. Group Chat Creator (With Cooldowns)</h2>
        <div class="muted">Enter at least <strong>2 usernames</strong>. Resolves usernames to IDs and creates groups with cooldowns.</div>
        <label>Account</label>
        <select id="gcCreatorAccount"></select>

        <label>Usernames to Add (comma-separated, at least 2)</label>
        <input id="gcCreateUsernames" type="text" placeholder="e.g. @user_one, @user_two, user_three" />

        <div class="two-col-inline">
          <div>
            <label>Number of Groups to Create</label>
            <input id="gcCreateCount" type="number" min="1" max="50" value="3" />
          </div>
          <div>
            <label>Target Name ({TARGET})</label>
            <input id="gcCreateTarget" placeholder="Optional target name" />
          </div>
        </div>

        <label>Group Title Template</label>
        <input id="gcCreateTitle" type="text" placeholder="{TARGET} #{N}" />

        <div class="two-col-inline">
          <div>
            <label>Min Cooldown (sec)</label>
            <input id="gcMinCd" type="number" min="10" value="25" />
          </div>
          <div>
            <label>Max Cooldown (sec)</label>
            <input id="gcMaxCd" type="number" min="10" value="45" />
          </div>
        </div>

        <label>Initial Message After Creation</label>
        <select id="gcSendPing">
          <option value="true" selected>Send welcome ping so GC appears in inbox</option>
          <option value="false">Do not send initial message</option>
        </select>

        <div class="row">
          <button onclick="startGroupCreator()">Start Creating Groups</button>
          <button class="secondary" onclick="useCreatedIdsForTask()">Use Created IDs in Task</button>
        </div>

        <div id="creatorJobsList" class="muted" style="margin-top:10px;">No group creation jobs yet.</div>
      </div>

      <div class="card">
        <h2>5. Mobile Group Invite Link Extractor</h2>
        <div class="muted">Extracts mobile invite links for the selected/entered group IDs above.</div>
        <label>Account</label>
        <select id="inviteAccount"></select>

        <label>Group Thread IDs to Extract (uses Selected Thread IDs if left blank)</label>
        <input id="inviteThreadIds" type="text" placeholder="Leave blank to use Selected Thread IDs" />

        <div class="row">
          <button onclick="extractInviteLinks()">Extract Invite Links</button>
          <button class="secondary" onclick="copyExtractedLinks()">Copy Links</button>
        </div>

        <div id="inviteLinksResult" class="link-box">
          <div class="muted">No invite links extracted yet.</div>
        </div>
      </div>
    </div>

    <div class="card">
      <h2>6. WebSocket Multi-Sender (igrapiweb)</h2>
      <div class="muted" id="wsMetaBar">Separate WebSocket worker engine (socket pool, live socket scaling, dgw/iris fallback, rotation, auto-recycle & health checks).</div>

      <div class="grid-2" style="margin-top:10px;">
        <div>
          <label>Session Name</label>
          <input id="wsSessionName" placeholder="e.g. ws_acc_1" />
          <label>Instagram Session ID</label>
          <input id="wsSessionId" type="password" placeholder="sessionid value" />
          <label>GC Name Text</label>
          <input id="wsGcName" placeholder="Group rename text" />
          <label>Message Text</label>
          <input id="wsMsgText" placeholder="Message body text" />
        </div>
        <div>
          <div class="two-col-inline">
            <div>
              <label>Thread ID (numeric)</label>
              <input id="wsThreadId" placeholder="Primary numeric thread ID" />
            </div>
            <div>
              <label>Sockets (1–10, live changeable)</label>
              <input id="wsSocketPool" type="number" min="1" max="10" value="1" />
            </div>
          </div>
          <label>Extra Thread IDs (optional comma-separated, processed one-by-one)</label>
          <input id="wsThreadIds" placeholder="Leave blank to use Thread ID above" />
          <div class="two-col-inline">
            <div>
              <label>Msg Min Delay (s)</label>
              <input id="wsDelayMin" type="number" step="0.01" min="0.01" value="0.1" />
            </div>
            <div>
              <label>Msg Max Delay (s)</label>
              <input id="wsDelayMax" type="number" step="0.01" min="0.01" value="0.2" />
            </div>
          </div>
          <div class="two-col-inline">
            <div>
              <label>Rename Min Delay (s)</label>
              <input id="wsRenameMin" type="number" step="0.5" min="1" value="5" />
            </div>
            <div>
              <label>Rename Max Delay (s)</label>
              <input id="wsRenameMax" type="number" step="0.5" min="1" value="15" />
            </div>
          </div>
          <div class="row">
            <button onclick="addWsSession()">Add & Start WS Session</button>
          </div>
        </div>
      </div>

      <div id="wsSessionsList" class="muted" style="margin-top:12px;">No WebSocket sessions yet.</div>
    </div>

    <div class="grid-2">
      <div class="card">
        <h2>7. Active Tasks</h2>
        <div id="tasksList" class="muted">No tasks yet.</div>
      </div>

      <div class="card">
        <h2>8. Message & Group Rename Templates</h2>
        <div class="muted">Enter <strong>one line</strong> using <code>{TARGET}</code>. Picks a random emoji formatted as <code>&lt;😎&gt;</code> on each of the 11 lines.</div>
        <label>Single Line Message Template</label>
        <input id="templateLineInput" type="text" placeholder="<{TARGET}> Kɪ Mᴀᴀ Mᴏᴛɪ !< Gᴀɴᴅ Wᴀʟɪ> Rᴀɴᴅ!> <😎>" />

        <label>Group Name Template (when NC is ON, uses <code>{TARGET}</code> + <code>&lt;⚡️&gt;</code>)</label>
        <input id="groupTitleInput" type="text" placeholder="{TARGET} <⚡️>" />

        <div class="row">
          <button onclick="saveTemplate()">Save Templates</button>
          <button class="warn" onclick="resetTemplate()">Reset Defaults</button>
        </div>
      </div>
    </div>

    <div class="card">
      <h2>9. Add User to Selected Group (With Safety Cooldown)</h2>
      <div class="muted">Adds a specific user (numeric IG ID or <code>@username</code>) to selected group threads with a minimum <strong>20s safety cooldown</strong> between groups.</div>
      <div class="grid-2" style="margin-top:8px;">
        <div>
          <label>Account</label>
          <select id="addMemberAccount"></select>

          <label>User ID or @Username to Add</label>
          <input id="addMemberInput" type="text" placeholder="e.g. 1234567890 or @username" />
        </div>
        <div>
          <label>Target Group Thread IDs (uses Selected Thread IDs if left blank)</label>
          <input id="addMemberThreadIds" type="text" placeholder="Leave blank to use Selected Thread IDs" />

          <label>Safety Cooldown Between Groups (sec, min 20s)</label>
          <input id="addMemberCooldown" type="number" min="20" step="1" value="25" />
        </div>
      </div>
      <div class="row">
        <button onclick="addUserToSelectedGroups()">Add to Selected Group(s)</button>
      </div>
      <div id="addMemberResult" class="link-box">
        <div class="muted">No member-add actions run yet.</div>
      </div>
    </div>

    <div class="card">
      <div class="top" style="margin-bottom:4px;">
        <div>
          <h2 style="margin:0;">10. System & Activity Logs</h2>
          <div class="muted" id="logsCountBar">Showing latest panel events and errors.</div>
        </div>
        <div class="row" style="margin:0;">
          <button class="secondary" onclick="refreshState()">Refresh Logs</button>
          <button class="danger" onclick="clearLogs()">Delete Logs</button>
        </div>
      </div>
      <div id="panelLogsBox" class="logs-box">No logs recorded yet.</div>
    </div>
  </div>

  <div class="toast" id="toast"></div>

  <script>
    const TOKEN_KEY = "ig_panel_token";
    document.getElementById("tokenInput").value = localStorage.getItem(TOKEN_KEY) || "";
    let loadedThreads = [];
    let latestCreatedIds = [];
    let latestExtractedLinks = [];

    function showToast(msg, err = false) {
      const el = document.getElementById("toast");
      el.textContent = msg;
      el.style.borderColor = err ? "#ef4444" : "#22c55e";
      el.style.display = "block";
      clearTimeout(window._t);
      window._t = setTimeout(() => { el.style.display = "none"; }, 4500);
    }

    function saveToken() {
      localStorage.setItem(TOKEN_KEY, document.getElementById("tokenInput").value.trim());
      showToast("Token saved");
      refreshState();
    }

    async function api(path, method = "GET", body = null, timeoutMs = 15000) {
      const tok = localStorage.getItem(TOKEN_KEY) || "";
      const headers = { "Content-Type": "application/json" };
      if (tok) headers["X-Panel-Token"] = tok;
      const ctrl = new AbortController();
      const timer = setTimeout(() => ctrl.abort(), timeoutMs);
      let res;
      try {
        res = await fetch(path, {
          method,
          headers,
          body: body ? JSON.stringify(body) : null,
          signal: ctrl.signal,
        });
      } finally {
        clearTimeout(timer);
      }
      const data = await res.json().catch(() => ({}));
      if (!res.ok && res.status !== 202) {
        throw new Error(data.detail || `Request failed (${res.status})`);
      }
      return { status: res.status, data };
    }

    function parseSelectedLogin(rawVal) {
      const v = String(rawVal || "").trim();
      if (v.startsWith("ws:")) return { ws_uid: v.slice(3), username: null };
      if (v.startsWith("ig:")) return { ws_uid: null, username: v.slice(3) };
      return { ws_uid: null, username: v || null };
    }

    function syncAccountSelectors(val) {
      if (!val) return;
      const parsed = parseSelectedLogin(val);
      if (parsed.username) {
        for (const id of ["gcCreatorAccount", "inviteAccount", "addMemberAccount"]) {
          const el = document.getElementById(id);
          if (el && Array.from(el.options).some(o => o.value === parsed.username)) {
            el.value = parsed.username;
          }
        }
      }
      const mgcSel = document.getElementById("mgcLoginSelect");
      if (mgcSel && Array.from(mgcSel.options).some(o => o.value === val)) {
        mgcSel.value = val;
      }
    }

    function parseThreadStringList(rawStr) {
      return String(rawStr || "")
        .split(",")
        .map(s => s.trim())
        .filter(s => /^\\d+$/.test(s));
    }

    function getSelectedThreadStrings() {
      return parseThreadStringList(document.getElementById("threadIdsInput").value);
    }

    function renderThreadPicker() {
      const selected = new Set(getSelectedThreadStrings());
      const picker = document.getElementById("threadPicker");
      if (!loadedThreads.length) {
        picker.innerHTML = "";
        return;
      }
      picker.innerHTML = loadedThreads.map(t => {
        const idStr = String(t.id);
        const isPicked = selected.has(idStr);
        return `<button type="button" class="pick-btn ${isPicked ? "picked" : "secondary"}" onclick="toggleThreadId('${idStr}')">
          <span>${isPicked ? "✅" : "⬜"} ${escapeHtml(t.label)}</span>
          <span class="tid-mono">${escapeHtml(idStr)}</span>
        </button>`;
      }).join("");
    }

    function escapeHtml(s) {
      return String(s || "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#39;");
    }

    function toggleThreadId(idStr) {
      const cleanId = String(idStr).trim();
      const input = document.getElementById("threadIdsInput");
      const list = getSelectedThreadStrings();
      const idx = list.indexOf(cleanId);
      if (idx >= 0) list.splice(idx, 1);
      else list.push(cleanId);
      input.value = list.join(", ");
      renderThreadPicker();
    }

    function selectAllLoaded(selectAll) {
      if (!loadedThreads.length) return showToast("Fetch GCs/chats first", true);
      document.getElementById("threadIdsInput").value = selectAll
        ? loadedThreads.map(t => String(t.id).trim()).filter(s => /^\\d+$/.test(s)).join(", ")
        : "";
      renderThreadPicker();
    }

    let isRefreshing = false;
    async function refreshState() {
      if (isRefreshing) return;
      isRefreshing = true;
      try {
        const { data } = await api("/api/state");
        const s = data.stats;
        document.getElementById("statsBar").textContent =
          `CPU ${s.cpu_percent}% · RAM ${s.ram_percent}% (${s.ram_used_gb}/${s.ram_total_gb} GB) · RSS ${s.rss_mb} MB · Sent ${data.global_messages_sent} · Uptime ${data.uptime}`;

        document.getElementById("wsMetaBar").textContent =
          `igrapiweb: ${data.igrapiweb_available ? "Available" : "Not Installed"} · Default Pool Size: ${data.ws_socket_pool} · WS-only recycle active`;

        const accs = Object.keys(data.accounts || {});
        const wsList = data.ws_sessions || [];
        const mgcJobs = data.multi_gc_jobs || [];
        const cJobs = data.group_creator_jobs || [];
        const stdTasks = data.tasks || [];

        const runningItems = [];
        for (const t of stdTasks) {
          if (t.running) {
            runningItems.push({
              kind: "Task",
              id: t.task_id,
              title: `${escapeHtml(t.username || "")} → <strong>${escapeHtml(t.target_name || "")}</strong>`,
              meta: `Threads: ${(t.thread_ids || []).length} · Sent: ${t.msg_count || 0} · ${escapeHtml(t.last_event || "")} (${escapeHtml(t.last_update || "")})`,
              stopHtml: `<button class="danger" onclick="stopTask('${escapeHtml(t.task_id)}')">Stop</button>`,
            });
          }
        }
        for (const j of mgcJobs) {
          if (j.running) {
            runningItems.push({
              kind: "Multi-GC",
              id: j.job_id,
              title: `${escapeHtml(j.label || "")} · <strong>${escapeHtml(j.target_name || "")}</strong>`,
              meta: `GCs: ${(j.thread_ids || []).length} · Sent: ${j.msg_count || 0} · NC: ${j.rename_count || 0} · ${escapeHtml(j.last_event || "")} (${escapeHtml(j.last_update || "")})`,
              stopHtml: `<button class="danger" onclick="stopMultiGc('${escapeHtml(j.job_id)}')">Stop</button>`,
            });
          }
        }
        for (const j of cJobs) {
          if (j.running) {
            runningItems.push({
              kind: "Creator",
              id: j.job_id,
              title: `@${escapeHtml(j.username || "")} · <strong>${j.created_count || 0}/${j.count || 0}</strong> created`,
              meta: `${escapeHtml(j.last_event || "")} (${escapeHtml(j.last_update || "")})`,
              stopHtml: `<button class="danger" onclick="stopGroupCreator('${escapeHtml(j.job_id)}')">Stop</button>`,
            });
          }
        }
        for (const w of wsList) {
          const wst = w.stats || {};
          if (wst.status === "live") {
            runningItems.push({
              kind: "WS",
              id: w.session_name || w.uid,
              title: `<strong>${escapeHtml(w.session_name || "")}</strong> · Thread <span class="tid-mono">${escapeHtml(w.thread_id || "")}</span>`,
              meta: `Sockets: ${wst.sockets_live || 0}/${wst.sockets_total || 0} · Sent: ${wst.sent || 0} · Renames: ${wst.renames || 0}`,
              stopHtml: `<button class="danger" onclick="wsAction('${escapeHtml(w.uid)}', 'stop')">Stop</button>`,
            });
          }
        }

        const runBox = document.getElementById("allRunningTasksList");
        const runSummary = document.getElementById("allRunningSummary");
        runSummary.textContent = `Currently running: ${runningItems.length} active item(s) across all sections.`;
        if (!runningItems.length) {
          runBox.innerHTML = `<div class="muted">No running tasks right now.</div>`;
        } else {
          runBox.innerHTML = runningItems.map(item => `
            <div class="list-item">
              <div>
                <div><span class="badge on">RUNNING</span> <span class="badge speed-badge">${escapeHtml(item.kind)}</span> <strong>${escapeHtml(item.id)}</strong> · ${item.title}</div>
                <div class="muted">${item.meta}</div>
              </div>
              ${item.stopHtml}
            </div>
          `).join("");
        }

        const loginOptions = [];
        for (const w of wsList) {
          loginOptions.push({ val: `ws:${w.uid}`, text: `WS: ${w.session_name}` });
        }
        for (const u of accs) {
          loginOptions.push({ val: `ig:${u}`, text: `@${u} (saved)` });
        }

        for (const id of ["taskAccount", "mgcLoginSelect"]) {
          const sel = document.getElementById(id);
          const prev = sel.value;
          sel.innerHTML = loginOptions.map(o => `<option value="${escapeHtml(o.val)}">${escapeHtml(o.text)}</option>`).join("");
          if (loginOptions.some(o => o.val === prev)) sel.value = prev;
        }

        for (const id of ["gcCreatorAccount", "inviteAccount", "addMemberAccount"]) {
          const sel = document.getElementById(id);
          const prev = sel.value;
          sel.innerHTML = accs.map(u => `<option value="${escapeHtml(u)}">@${escapeHtml(u)}</option>`).join("");
          if (accs.includes(prev)) sel.value = prev;
        }

        const accBox = document.getElementById("accountsList");
        if (!accs.length) {
          accBox.innerHTML = `<div class="muted">No saved accounts yet.</div>`;
        } else {
          accBox.innerHTML = accs.map(u => {
            const m = data.accounts[u];
            return `<div class="list-item">
              <div><strong>@${escapeHtml(u)}</strong> <span class="muted">(${escapeHtml(m.auth_method || "saved")})</span></div>
              <button class="secondary" onclick="deleteAccount('${escapeHtml(u)}')">Remove</button>
            </div>`;
          }).join("");
        }

        const mgcBox = document.getElementById("multiGcJobsList");
        if (!mgcJobs.length) {
          mgcBox.innerHTML = `<div class="muted">No Multi-GC sender jobs yet.</div>`;
        } else {
          mgcBox.innerHTML = mgcJobs.map(j => `
            <div class="list-item">
              <div>
                <div><strong>${escapeHtml(j.job_id)}</strong> · ${escapeHtml(j.label)} · <strong>${escapeHtml(j.target_name)}</strong>
                  <span class="badge ${j.running ? "on" : "off"}">${j.running ? "RUNNING" : "STOPPED"}</span>
                  <span class="badge speed-badge">${escapeHtml((j.speed_mode || "slow").toUpperCase())}</span>
                  <span class="badge nc-badge">${j.use_nc ? "WITH NC" : "NO NC"}</span>
                </div>
                <div class="muted">GCs: ${(j.thread_ids || []).length} · Sent: ${j.msg_count} · NC: ${j.rename_count} · ${escapeHtml(j.last_event || "")} (${escapeHtml(j.last_update || "")})</div>
              </div>
              ${j.running ? `<button class="danger" onclick="stopMultiGc('${escapeHtml(j.job_id)}')">Stop</button>` : ""}
            </div>
          `).join("");
        }

        const tBox = document.getElementById("tasksList");
        if (!stdTasks.length) {
          tBox.innerHTML = `<div class="muted">No tasks created yet.</div>`;
        } else {
          tBox.innerHTML = stdTasks.map(t => `
            <div class="list-item">
              <div>
                <div><strong>${escapeHtml(t.task_id)}</strong> · ${escapeHtml(t.username || "")} → <strong>${escapeHtml(t.target_name)}</strong>
                  <span class="badge ${t.running ? "on" : "off"}">${t.running ? "RUNNING" : "STOPPED"}</span>
                  <span class="badge speed-badge">${escapeHtml((t.speed_mode || "slow").toUpperCase())}</span>
                  <span class="badge nc-badge">${t.use_nc !== false ? "WITH NC" : "NO NC"}</span>
                </div>
                <div class="muted">Sent: ${t.msg_count} · ${escapeHtml(t.last_event || "Idle")} (${escapeHtml(t.last_update || "")})</div>
              </div>
              <div class="row" style="margin:0;">
                ${t.running
                  ? `<button class="danger" onclick="stopTask('${escapeHtml(t.task_id)}')">Stop</button>`
                  : `<button class="secondary" onclick="removeTask('${escapeHtml(t.task_id)}')">Remove</button>`}
              </div>
            </div>
          `).join("");
        }

        const cBox = document.getElementById("creatorJobsList");
        if (!cJobs.length) {
          cBox.innerHTML = `<div class="muted">No group creation jobs yet.</div>`;
        } else {
          const allIds = [];
          for (const j of cJobs) {
            for (const cid of (j.created_ids || [])) {
              if (!allIds.includes(String(cid))) allIds.push(String(cid));
            }
          }
          latestCreatedIds = allIds;

          cBox.innerHTML = cJobs.map(j => `
            <div class="list-item">
              <div>
                <div><strong>${escapeHtml(j.job_id)}</strong> · @${escapeHtml(j.username)} · <strong>${j.created_count}/${j.count}</strong> created
                  <span class="badge ${j.running ? "on" : "off"}">${j.running ? "CREATING" : "DONE"}</span>
                </div>
                <div class="muted">${escapeHtml(j.last_event || "")} (${escapeHtml(j.last_update || "")})</div>
                ${(j.created_ids && j.created_ids.length)
                  ? `<div class="tid-mono" style="margin-top:4px;">IDs: ${escapeHtml(j.created_ids.join(", "))}</div>`
                  : ""}
              </div>
              ${j.running ? `<button class="danger" onclick="stopGroupCreator('${escapeHtml(j.job_id)}')">Stop</button>` : ""}
            </div>
          `).join("");
        }

        const wsBox = document.getElementById("wsSessionsList");
        if (!wsList.length) {
          wsBox.innerHTML = `<div class="muted">No WebSocket sessions added yet.</div>`;
        } else {
          wsBox.innerHTML = wsList.map(w => {
            const st = w.stats || {};
            const live = st.status === "live";
            const sockInpId = `wsLiveSock_${w.uid}`;
            const activeSockEl = document.getElementById(sockInpId);
            const curSockVal = (activeSockEl && document.activeElement === activeSockEl)
              ? activeSockEl.value
              : (w.socket_pool || 1);
            return `<div class="list-item">
              <div>
                <div><strong>${escapeHtml(w.session_name)}</strong> <span class="tid-mono">(${escapeHtml(w.uid)})</span> · Thread <span class="tid-mono">${escapeHtml(w.thread_id)}</span>
                  <span class="badge ${live ? "on" : "off"}">${escapeHtml((st.status || "stopped").toUpperCase())}</span>
                  <span class="badge speed-badge">🔌 ${st.sockets_live || 0}/${st.sockets_total || 0} (pool:${w.socket_pool || 1})</span>
                  ${st.session_status ? `<span class="badge nc-badge">🩺 ${escapeHtml(st.session_status)}</span>` : ""}
                </div>
                <div class="muted">Sent: ${st.sent || 0} · Fail: ${st.failed || 0} · Renames: ${st.renames || 0} · Recycles: ${st.recycles || 0} · Delay: ${w.delay_min}-${w.delay_max}s · Ren: ${w.rename_min}-${w.rename_max}s</div>
                ${st.last_error ? `<div class="tid-mono" style="color:#fca5a5; margin-top:2px;">Err: ${escapeHtml(st.last_error)}</div>` : ""}
                <div class="row" style="margin-top:6px;">
                  <span class="muted">Live Sockets (1–10):</span>
                  <input id="${escapeHtml(sockInpId)}" type="number" min="1" max="10" value="${curSockVal}" style="width:74px; padding:5px 8px;" />
                  <button class="secondary" onclick="wsSetSockets('${escapeHtml(w.uid)}')">Set Sockets</button>
                </div>
              </div>
              <div class="row" style="margin:0;">
                ${live
                  ? `<button class="danger" onclick="wsAction('${escapeHtml(w.uid)}', 'stop')">Stop</button>`
                  : `<button onclick="wsAction('${escapeHtml(w.uid)}', 'start')">Start</button>`}
                <button class="secondary" onclick="wsAdjust('${escapeHtml(w.uid)}', -0.1, 0)">Msg -0.1</button>
                <button class="secondary" onclick="wsAdjust('${escapeHtml(w.uid)}', 0.1, 0)">Msg +0.1</button>
                <button class="secondary" onclick="wsAdjust('${escapeHtml(w.uid)}', 0, -1)">Ren -1</button>
                <button class="secondary" onclick="wsAdjust('${escapeHtml(w.uid)}', 0, 1)">Ren +1</button>
                <button class="secondary" onclick="wsAction('${escapeHtml(w.uid)}', 'recycle')">Recycle</button>
                <button class="secondary" onclick="wsDelete('${escapeHtml(w.uid)}')">Delete</button>
              </div>
            </div>`;
          }).join("");
        }

        const logsBox = document.getElementById("panelLogsBox");
        const logsCountBar = document.getElementById("logsCountBar");
        const logEntries = Array.isArray(data.logs) ? data.logs : [];
        logsCountBar.textContent = `Showing ${logEntries.length} log entries.`;
        if (!logEntries.length) {
          logsBox.innerHTML = `<div class="muted">No logs recorded yet.</div>`;
        } else {
          const wasNearBottom = (logsBox.scrollHeight - logsBox.scrollTop - logsBox.clientHeight) < 36;
          logsBox.innerHTML = logEntries.map(line => `<div class="log-line">${escapeHtml(line)}</div>`).join("");
          if (wasNearBottom) {
            logsBox.scrollTop = logsBox.scrollHeight;
          }
        }

        const tplEl = document.getElementById("templateLineInput");
        if (document.activeElement !== tplEl) {
          tplEl.value = data.template || "";
        }
        const gtEl = document.getElementById("groupTitleInput");
        if (document.activeElement !== gtEl) {
          gtEl.value = data.group_title_template || "{TARGET} <⚡️>";
        }
      } catch (e) {
        document.getElementById("statsBar").textContent = e && e.name === "AbortError" ? "State request timed out" : e.message;
      } finally {
        isRefreshing = false;
      }
    }

    async function clearLogs() {
      try {
        await api("/api/logs", "DELETE");
        document.getElementById("panelLogsBox").innerHTML = `<div class="muted">No logs recorded yet.</div>`;
        document.getElementById("logsCountBar").textContent = "Showing 0 log entries.";
        showToast("Logs deleted");
      } catch (e) {
        showToast(e.message, true);
      }
    }

    async function fetchThreads(onlyGroups = true) {
      const rawSel = document.getElementById("taskAccount").value;
      const parsed = parseSelectedLogin(rawSel);
      document.getElementById("threadStatus").textContent = "Loading...";
      try {
        const params = new URLSearchParams();
        if (parsed.ws_uid) params.set("ws_uid", parsed.ws_uid);
        if (parsed.username) params.set("username", parsed.username);
        const { data } = await api(`/api/threads?${params.toString()}`);
        const allItems = Array.isArray(data.threads) ? data.threads : [];
        loadedThreads = onlyGroups ? allItems.filter(t => Boolean(t.is_group)) : allItems;
        if (!loadedThreads.length && onlyGroups && allItems.length) {
          loadedThreads = allItems;
        }
        renderThreadPicker();
        document.getElementById("threadStatus").textContent = `${loadedThreads.length} ${onlyGroups ? "GCs" : "chats"} loaded`;
      } catch (e) {
        document.getElementById("threadStatus").textContent = "";
        showToast(e.message, true);
      }
    }

    function fillMultiGcFromSelected() {
      const tids = getSelectedThreadStrings();
      if (!tids.length) return showToast("Select or enter GC thread IDs first", true);
      document.getElementById("mgcThreadIdsInput").value = tids.join(", ");
      showToast(`Copied ${tids.length} GC ID(s)`);
    }

    async function startMultiGc() {
      try {
        const parsed = parseSelectedLogin(document.getElementById("mgcLoginSelect").value);
        const customRaw = document.getElementById("mgcThreadIdsInput").value.trim();
        const thread_ids = customRaw ? parseThreadStringList(customRaw) : getSelectedThreadStrings();
        const target_name = document.getElementById("mgcTargetInput").value.trim() || document.getElementById("targetInput").value.trim();
        const custom_text = document.getElementById("mgcCustomText").value.trim();
        const nc_text = document.getElementById("mgcNcText").value.trim();
        const speed_mode = document.getElementById("mgcSpeedMode").value;
        const use_nc = document.getElementById("mgcNcMode").value === "true";

        const { data } = await api("/api/multi-gc/start", "POST", {
          username: parsed.username,
          ws_uid: parsed.ws_uid,
          thread_ids,
          target_name,
          custom_text,
          nc_text,
          speed_mode,
          use_nc,
        });
        showToast(`Started Multi-GC ${data.job_id} (${data.speed_mode}, ${data.use_nc ? "with NC" : "without NC"})`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function stopMultiGc(jobId) {
      try {
        await api(`/api/multi-gc/${encodeURIComponent(jobId)}/stop`, "POST");
        showToast(`Stopped Multi-GC ${jobId}`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function addUserToSelectedGroups() {
      try {
        const username = document.getElementById("addMemberAccount").value;
        const member_input = document.getElementById("addMemberInput").value.trim();
        const customRaw = document.getElementById("addMemberThreadIds").value.trim();
        const thread_ids = customRaw ? parseThreadStringList(customRaw) : getSelectedThreadStrings();
        const rawCd = parseFloat(document.getElementById("addMemberCooldown").value);
        const cooldown_sec = Number.isFinite(rawCd) ? Math.max(20, rawCd) : 25;
        document.getElementById("addMemberCooldown").value = cooldown_sec;

        if (!member_input) return showToast("Enter a user ID or @username to add", true);
        if (!thread_ids.length) return showToast("Select or enter at least 1 valid group ID first", true);

        const outBox = document.getElementById("addMemberResult");
        outBox.innerHTML = `<div class="muted">Adding ${escapeHtml(member_input)} to ${thread_ids.length} group(s) with >=${cooldown_sec}s safety cooldown...</div>`;

        const { data } = await api("/api/groups/add-user", "POST", {
          username,
          thread_ids,
          member_input,
          cooldown_sec,
        });

        const rows = Array.isArray(data.results) ? data.results : [];
        outBox.innerHTML = rows.map(r => {
          const ok = r.status === "added";
          return `<div class="link-row">
            <div><strong>${escapeHtml(r.target_label || member_input)}</strong> → Thread <span class="tid-mono">${escapeHtml(r.thread_id)}</span>
              <span class="badge ${ok ? "on" : "off"}">${escapeHtml((r.status || "").toUpperCase())}</span>
            </div>
          </div>`;
        }).join("");

        showToast(`Added to ${data.added_count}/${data.total_threads} group(s) (cooldown ${data.safety_cooldown_sec}s)`);
      } catch (e) { showToast(e.message, true); }
    }

    async function addWsSession() {
      try {
        const extraTids = parseThreadStringList(document.getElementById("wsThreadIds").value);
        const payload = {
          session_name: document.getElementById("wsSessionName").value.trim(),
          session_id: document.getElementById("wsSessionId").value.trim(),
          gc_name_text: document.getElementById("wsGcName").value.trim(),
          msg_text: document.getElementById("wsMsgText").value.trim(),
          thread_id: document.getElementById("wsThreadId").value.trim(),
          thread_ids: extraTids.length ? extraTids : null,
          socket_pool: parseInt(document.getElementById("wsSocketPool").value, 10) || 1,
          delay_min: parseFloat(document.getElementById("wsDelayMin").value) || 0.1,
          delay_max: parseFloat(document.getElementById("wsDelayMax").value) || 0.2,
          rename_min: parseFloat(document.getElementById("wsRenameMin").value) || 5.0,
          rename_max: parseFloat(document.getElementById("wsRenameMax").value) || 15.0,
          auto_start: true,
        };
        const { data } = await api("/api/ws/sessions", "POST", payload);
        document.getElementById("wsSessionId").value = "";
        if (data.started) {
          showToast(`WS session "${payload.session_name}" starting`);
        } else {
          showToast(`Saved as stopped: ${data.error || "check socket/session"}`, true);
        }
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function wsSetSockets(uid) {
      try {
        const el = document.getElementById(`wsLiveSock_${uid}`);
        const rawVal = parseInt(el ? el.value : "1", 10) || 1;
        const socket_pool = Math.max(1, Math.min(10, rawVal));
        const { data } = await api(`/api/ws/sessions/${encodeURIComponent(uid)}/sockets`, "POST", { socket_pool });
        showToast(`${uid}: sockets set to ${data.socket_pool}`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function wsAction(uid, action) {
      try {
        await api(`/api/ws/sessions/${encodeURIComponent(uid)}/${action}`, "POST");
        showToast(`WS ${action} -> ${uid}`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function wsAdjust(uid, msgDelta, renameDelta) {
      try {
        await api(`/api/ws/sessions/${encodeURIComponent(uid)}/adjust`, "POST", {
          msg_delta: msgDelta || null,
          rename_delta: renameDelta || null,
        });
        showToast("WS delays updated");
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function wsDelete(uid) {
      try {
        await api(`/api/ws/sessions/${encodeURIComponent(uid)}`, "DELETE");
        showToast(`Deleted WS session ${uid}`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function loginSession() {
      try {
        const sid = document.getElementById("sidInput").value.trim();
        const { data } = await api("/api/login/session", "POST", { session_id: sid });
        document.getElementById("sidInput").value = "";
        showToast(`Logged in as @${data.username}`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function loginPassword() {
      try {
        const username = document.getElementById("igUser").value.trim();
        const password = document.getElementById("igPass").value;
        const two_factor_code = document.getElementById("ig2fa").value.trim() || null;
        const { status, data } = await api("/api/login/password", "POST", { username, password, two_factor_code });
        if (status === 202 && data.two_factor_required) {
          document.getElementById("tfaBox").style.display = "block";
          showToast("2FA code required—enter it and click again", true);
          return;
        }
        document.getElementById("igPass").value = "";
        document.getElementById("ig2fa").value = "";
        document.getElementById("tfaBox").style.display = "none";
        showToast(`Logged in as @${data.username}`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function deleteAccount(u) {
      try {
        await api(`/api/accounts/${encodeURIComponent(u)}`, "DELETE");
        showToast(`Removed @${u}`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function startTask() {
      try {
        const parsed = parseSelectedLogin(document.getElementById("taskAccount").value);
        const target_name = document.getElementById("targetInput").value.trim();
        const speed_mode = document.getElementById("speedMode").value;
        const use_nc = document.getElementById("ncMode").value === "true";
        const thread_ids = getSelectedThreadStrings();
        const { data } = await api("/api/tasks/start", "POST", {
          username: parsed.username,
          ws_uid: parsed.ws_uid,
          thread_ids,
          target_name,
          speed_mode,
          use_nc,
        });
        showToast(`Started task ${data.task_id} (${data.speed_mode}, ${data.use_nc ? "with NC" : "no NC"})`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function startGroupCreator() {
      try {
        const username = document.getElementById("gcCreatorAccount").value;
        const count = parseInt(document.getElementById("gcCreateCount").value, 10) || 1;
        const target_name = document.getElementById("gcCreateTarget").value.trim() || document.getElementById("targetInput").value.trim();
        const title_template = document.getElementById("gcCreateTitle").value.trim() || null;
        const usernames = document.getElementById("gcCreateUsernames").value
          .split(",").map(s => s.trim().replace(/^@+/, "")).filter(Boolean);
        const min_cooldown = parseFloat(document.getElementById("gcMinCd").value) || 25;
        const max_cooldown = parseFloat(document.getElementById("gcMaxCd").value) || 45;
        const send_ping = document.getElementById("gcSendPing").value === "true";

        const { data } = await api("/api/groups/create", "POST", {
          username, count, title_template, target_name, usernames, min_cooldown, max_cooldown, send_ping
        });
        showToast(`Started group creator ${data.job_id} (${data.count} groups)`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function stopGroupCreator(jobId) {
      try {
        await api(`/api/groups/create/${encodeURIComponent(jobId)}/stop`, "POST");
        showToast(`Stopped creator ${jobId}`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    function useCreatedIdsForTask() {
      if (!latestCreatedIds.length) return showToast("No created group IDs yet", true);
      document.getElementById("threadIdsInput").value = latestCreatedIds.join(", ");
      renderThreadPicker();
      showToast(`Loaded ${latestCreatedIds.length} created group IDs`);
    }

    async function extractInviteLinks() {
      try {
        const username = document.getElementById("inviteAccount").value;
        const customRaw = document.getElementById("inviteThreadIds").value.trim();
        const thread_ids = customRaw ? parseThreadStringList(customRaw) : getSelectedThreadStrings();
        if (!thread_ids.length) {
          return showToast("Select or enter at least 1 valid group ID first", true);
        }

        const resBox = document.getElementById("inviteLinksResult");
        resBox.innerHTML = `<div class="muted">Extracting links for ${thread_ids.length} thread(s)...</div>`;

        const { data } = await api("/api/groups/invite-links", "POST", { username, thread_ids });
        latestExtractedLinks = Array.isArray(data.results) ? data.results : [];

        resBox.innerHTML = latestExtractedLinks.map(r => {
          if (r.invite_link) {
            return `<div class="link-row">
              <div><strong>${escapeHtml(r.title)}</strong> <span class="tid-mono">(${escapeHtml(r.thread_id)})</span></div>
              <div class="tid-mono" style="margin-top:4px; color:#6ee7b7;">${escapeHtml(r.invite_link)}</div>
            </div>`;
          }
          return `<div class="link-row">
            <div><strong>${escapeHtml(r.title)}</strong> <span class="tid-mono">(${escapeHtml(r.thread_id)})</span></div>
            <div class="muted" style="margin-top:3px;">${escapeHtml(r.status || "No link returned")}</div>
          </div>`;
        }).join("");

        const okCount = latestExtractedLinks.filter(x => x.invite_link).length;
        showToast(`Extracted ${okCount}/${latestExtractedLinks.length} invite links`);
      } catch (e) { showToast(e.message, true); }
    }

    async function copyExtractedLinks() {
      const links = latestExtractedLinks.map(x => x.invite_link).filter(Boolean);
      if (!links.length) return showToast("No extracted invite links to copy", true);
      try {
        await navigator.clipboard.writeText(links.join("\\n"));
        showToast(`Copied ${links.length} invite link(s)`);
      } catch (_) {
        showToast("Clipboard blocked—copy directly from the list above", true);
      }
    }

    async function stopTask(id) {
      try {
        await api(`/api/tasks/${encodeURIComponent(id)}/stop`, "POST");
        showToast(`Stopped ${id}`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function removeTask(id) {
      try {
        await api(`/api/tasks/${encodeURIComponent(id)}`, "DELETE");
        showToast(`Removed ${id}`);
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function stopAll() {
      try {
        await api("/api/tasks/stop-all", "POST");
        showToast("Stopped all tasks, Multi-GC jobs, creators & WS sessions");
        refreshState();
      } catch (e) { showToast(e.message, true); }
    }

    async function saveTemplate() {
      try {
        const template = document.getElementById("templateLineInput").value;
        const group_title_template = document.getElementById("groupTitleInput").value;
        const { data } = await api("/api/template", "POST", { template, group_title_template });
        document.getElementById("templateLineInput").value = data.template || template;
        document.getElementById("groupTitleInput").value = data.group_title_template || "{TARGET} <⚡️>";
        showToast("Templates saved");
      } catch (e) { showToast(e.message, true); }
    }

    async function resetTemplate() {
      try {
        const { data } = await api("/api/template/reset", "POST");
        document.getElementById("templateLineInput").value = data.template || "";
        document.getElementById("groupTitleInput").value = data.group_title_template || "{TARGET} <⚡️>";
        showToast("Templates reset to defaults");
      } catch (e) { showToast(e.message, true); }
    }

    document.getElementById("threadIdsInput").addEventListener("input", renderThreadPicker);
    refreshState();
    setInterval(refreshState, 4000);
  </script>
</body>
</html>
"""


@app.get("/", response_class=HTMLResponse)
def index(request: Request):
    return HTMLResponse(content=HTML_PAGE)


@app.get("/health")
async def health_check():
    return {"ok": True, "status": "live", "uptime": str(datetime.now() - BOT_START_TIME).split(".")[0]}


if __name__ == "__main__":
    backlog = 2048
    limit_concurrency = 256
    append_panel_log("SYS", f"Web panel listening on 0.0.0.0:{PORT} (DATA_DIR={DATA_DIR}, SOCKET_POOL={WS_SOCKET_POOL}, WS_RECYCLE={WS_WORKER_RECYCLE_SEC}s)")
    uvicorn.run(
        app,
        host="0.0.0.0",
        port=PORT,
        log_level="warning",
        backlog=backlog,
        limit_concurrency=limit_concurrency,
        timeout_keep_alive=15,
    )
