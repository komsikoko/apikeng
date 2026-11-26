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
EMOJI_POOL = ["😎", "🦊", "🐉", "🦅", "🦂", "🦈", "🐺", "🦁", "☄️", "💥", "🗡️", "🛡️", "👑", "💎", "🎯", "🧨"]
SUBTLE_LINK_SLUGS = ["r", "x", "q", "v", "k", "m", "n", "t"]
WS_EMOJI_POOL = ["😎", "🦁", "🐯", "🐺", "🦊", "🐉", "🦅", "🦉", "🦇", "🦈", "🐊", "🦂", "🕷️", "🐍", "🦖", "☄️", "💥", "🔥", "🌪️", "🌊", "❄️", "💎", "👑", "🗡️", "🛡️", "🎯", "🧨", "🚀"]
WS_GC_EMOJI = "⚡️"
WS_FOOTER = "\n\n\n\nScript by - ρ 𝕣 ꪜ 𝕣 अब्बू ☽"
WS_UA_POOL = [
    "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1",
    "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 13; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36",
]

socket.setdefaulttimeout(8)
MIN_SAFE_ADD_COOLDOWN = 20.0
MAX_RETRIES = 5
WS_SOCKET_POOL = 1
WS_WORKER_RECYCLE_SEC = 3600

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

def verify_auth(x_panel_token: Optional[str] = None, token_query: Optional[str] = None):
    if not PANEL_TOKEN:
        return
    provided = (x_panel_token or token_query or "").strip()
    if provided != PANEL_TOKEN:
        raise HTTPException(status_code=401, detail="Unauthorized: invalid or missing panel token")

def make_ig_client() -> Client:
    cl = Client()
    cl.delay_range = [0, 0]
    try:
        cl.set_app_version(IG_APP_VERSION)
        cl.set_user_agent(IG_USER_AGENT)
        cl.version_code = IG_VERSION_CODE
    except Exception:
        pass
    return cl

def clean_session_id(raw: str) -> str:
    val = raw.strip().strip('"').strip("'")
    if "sessionid=" in val:
        val = val.split("sessionid=", 1)[1].split(";", 1)[0].strip()
    return val

def igrapi_send_or_reply(cl: Client, tid_str: str, text: str, reply_target: Optional[dict] = None) -> tuple[bool, Optional[dict], str]:
    """
    Sends a message via instagrapi (Client), optionally replying to a previous message.
    reply_target should be {"id": str, "client_context": Optional[str]} from the previous message.
    Returns (ok, next_reply_target_dict, error_str).
    """
    tid_int = int(tid_str)
    try:
        if reply_target and reply_target.get("id"):
            token = cl.generate_mutation_token()
            payload = {
                "action": "send_item",
                "is_shh_mode": "0",
                "send_attribution": "direct_thread",
                "client_context": token,
                "mutation_token": token,
                "offline_threading_id": token,
                "thread_ids": f"[{tid_int}]",
                "text": text,
                "replied_to_item_id": str(reply_target["id"]),
                "replied_to_action_source": "swipe",
            }
            if reply_target.get("client_context"):
                payload["replied_to_client_context"] = str(reply_target["client_context"])
            resp = cl.private_request("direct_v2/threads/broadcast/text/", data=payload, with_signature=False)
        else:
            resp = cl.direct_send(text, thread_ids=[tid_int])

        # Capture newly sent message id + client_context for continuous self-reply chaining
        new_id = None
        new_ctx = None
        if hasattr(resp, "id") and getattr(resp, "id"):
            new_id = str(getattr(resp, "id")).strip()
            new_ctx = str(getattr(resp, "client_context", "") or "").strip() or None
        elif isinstance(resp, dict):
            # Common broadcast/text response shapes
            for key in ("item_id", "message_id", "id"):
                if resp.get(key):
                    new_id = str(resp[key]).strip()
                    break
            new_ctx = str(resp.get("client_context") or resp.get("offline_threading_id") or "").strip() or None
            if not new_id and isinstance(resp.get("payload"), dict):
                p = resp["payload"]
                new_id = str(p.get("item_id") or p.get("id") or "").strip() or None
                new_ctx = new_ctx or (str(p.get("client_context") or "").strip() or None)

        if not new_id:
            try:
                recent = cl.direct_messages(tid_int, amount=5)
                my_uid = str(getattr(cl, "user_id", "") or "")
                for m in recent:
                    if not my_uid or str(getattr(m, "user_id", "")) == my_uid:
                        new_id = str(getattr(m, "id")).strip()
                        new_ctx = str(getattr(m, "client_context", "") or "").strip() or None
                        break
                if not new_id and recent:
                    new_id = str(getattr(recent[0], "id")).strip()
                    new_ctx = str(getattr(recent[0], "client_context", "") or "").strip() or None
            except Exception:
                pass

        next_target = {"id": new_id, "client_context": new_ctx} if new_id else None
        return True, next_target, ""
    except Exception as exc:
        return False, None, str(exc)


# ======================== INSTAGRAPI SINGLE-LINE SELF-REPLY ENGINE ========================

def _build_single_line_reply_text(template_or_text: str, target_name: str = "") -> str:
    """
    Renders a clean single-line reply with no 7-line spacing gaps and no footer.
    Strips any accidental newlines and ensures single-line formatting.
    """
    chosen_emoji = random.choice(EMOJI_POOL)
    rendered = str(template_or_text or DEFAULT_SINGLE_LINE_TEMPLATE)
    if target_name:
        rendered = rendered.replace("{TARGET}", target_name)
    rendered = rendered.replace("{EMOJI}", chosen_emoji)
    if "<😎>" in rendered:
        rendered = rendered.replace("<😎>", f"<{chosen_emoji}>")
    # Collapse all newlines/whitespace runs into a single clean line without footer
    single_line = re.sub(r"\s+", " ", rendered).strip()
    return single_line


def _get_or_seed_own_reply_target(cl: Client, tid_str: str, state: dict, refresh: bool = False) -> Optional[dict]:
    """
    Gets cached own message target for tid_str, seeding once from cl.direct_messages(...)
    only when missing or explicitly requested via refresh=True (no per-loop polling).
    """
    if not refresh and tid_str in state and state[tid_str] and state[tid_str].get("id"):
        return state[tid_str]

    tid_int = int(tid_str)
    my_uid = str(getattr(cl, "user_id", "") or "").strip()
    if not my_uid:
        try:
            my_uid = str(getattr(cl.account_info(), "pk", "") or "").strip()
        except Exception:
            my_uid = ""

    msgs = cl.direct_messages(tid_int, amount=15)
    for m in msgs:
        mid = getattr(m, "id", None)
        if not mid:
            continue
        m_uid = str(getattr(m, "user_id", "") or "").strip()
        if my_uid and m_uid == my_uid:
            target = {
                "id": str(mid).strip(),
                "client_context": str(getattr(m, "client_context", "") or "").strip() or None,
            }
            state[tid_str] = target
            return target
    return None


def send_single_line_self_reply(
    cl: Client,
    tid_str: str,
    reply_text: str,
    reply_state: dict,
    chain: bool = False,
) -> tuple[bool, str]:
    """
    Sends a single-line reply via instagrapi targeting the user's own message.
    - If chain=False (default): replies to a single fixed own anchor message (zero polling overhead).
    - If chain=True: chains onto the user's newly sent message ID/client_context when returned,
      without polling direct_messages() on every send.
    """
    tid_int = int(tid_str)
    single_line_body = _build_single_line_reply_text(reply_text)
    if not single_line_body:
        return False, "Empty single-line reply text"

    target = _get_or_seed_own_reply_target(cl, tid_str, reply_state, refresh=False)

    # First time in thread with no prior own message: send a single-line message and capture its ID
    if not target or not target.get("id"):
        sent_obj = cl.direct_send(single_line_body, thread_ids=[tid_int])
        new_id = str(getattr(sent_obj, "id", "") or "").strip() or None
        new_ctx = str(getattr(sent_obj, "client_context", "") or "").strip() or None
        if new_id:
            reply_state[tid_str] = {"id": new_id, "client_context": new_ctx}
        return True, ""

    token = cl.generate_mutation_token()
    payload = {
        "action": "send_item",
        "is_shh_mode": "0",
        "send_attribution": "direct_thread",
        "client_context": token,
        "mutation_token": token,
        "offline_threading_id": token,
        "thread_ids": f"[{tid_int}]",
        "text": single_line_body,
        "replied_to_item_id": str(target["id"]),
        "replied_to_action_source": "swipe",
    }
    if target.get("client_context"):
        payload["replied_to_client_context"] = str(target["client_context"])

    resp = cl.private_request(
        "direct_v2/threads/broadcast/text/",
        data=payload,
        with_signature=False,
    )

    if chain and isinstance(resp, dict):
        new_id = None
        for key in ("item_id", "message_id", "id"):
            if resp.get(key):
                new_id = str(resp[key]).strip()
                break
        if not new_id and isinstance(resp.get("payload"), dict):
            p = resp["payload"]
            new_id = str(p.get("item_id") or p.get("id") or "").strip() or None
        if new_id:
            new_ctx = str(resp.get("client_context") or resp.get("offline_threading_id") or token).strip() or None
            reply_state[tid_str] = {"id": new_id, "client_context": new_ctx}

    return True, ""
