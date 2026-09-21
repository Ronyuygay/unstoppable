#!/usr/bin/env python3
"""
RADIATE PROXY MONITOR v6.2
================================================================================
Autonomous proxy validation & monitoring system, controlled entirely from Telegram.

WHAT CHANGED SINCE v6.1  (every item below was a finding in the verification report)
--------------------------------------------------------------------------------
 1. MULTI-STAGE PREFLIGHT ....... TCP connect (stage 1) + real protocol handshake
                                  (stage 2). A port being open is no longer enough
                                  to reach Chromium.
 2. PROTOCOL AUTO-DETECTION ..... scheme-less "ip:port" lines are probed as
                                  http / socks5 / socks4 and the working protocol is
                                  remembered.  This is the usual cause of
                                  "I have 400 proxies but only 200 work".
 3. PREFLIGHT IS PROXY-LEVEL .... it used to run once per (proxy, target) pair.
                                  Now it runs once per proxy, with periodic recheck.
 4. RULE B IS OPT-IN ............ per-target `redirect_means_success`.  Off by
                                  default because a redirect to a captcha / block
                                  page would otherwise be scored as a success.
 5. TWO WORKER POOLS ............ `worker_count` fresh-test workers + a genuinely
                                  separate `retry_worker_count` pool for retrying
                                  failed / re-verifying working pairs.
 6. HARDWARE AUTO-TUNING ........ pool sizes derived from real CPU count + RAM.
 7. FD LIMIT RAISED ............. RLIMIT_NOFILE is lifted before 500+ sockets open.
 8. TRUE SILENT TERMINAL ........ fatal errors go to logs + Telegram, not stdout.
 9. RESTARTABLE STOP ............ Restart (exit 75) and Shutdown (exit 0) are
                                  separate buttons, both behind a confirm step.
10. TIMED PAUSE ................. pause 15m / 1h / 6h / forever, auto-resume,
                                  survives a restart.
11. FULL SETTINGS MENU .......... browse & edit config from Telegram, typed and
                                  range-validated, persisted to config.json.
12. UA CONTROL .................. rotation, remote pool, custom UA list from the bot.
13. SOURCE MANAGEMENT ........... add / remove / list proxy source URLs from the bot.
14. TELEMETRY ................... queue depth, worker stats, circuit breakers,
                                  failure-class breakdown, recent errors, per-target.
15. PROXY MANAGEMENT ............ export validated list as .txt, purge dead, reset.
16. VIP CHECK ................... test a single proxy on demand in its own browser
                                  context and get a full diagnostic back.
17. CODESPACE CONTROL ........... stop / rename / status via gh CLI or GitHub API.
18. PUBLIC URL .................. forwarded-port URL + visibility switch for
                                  UptimeRobot inbound monitors (token protected).
19. MONGODB MIRROR .............. optional, non-fatal, off by default.
20. ANTI-SPAM ................... one live-status message, local diff before every
                                  edit, adaptive interval, deduplicated alerts.
21. DEAD-PROXY PURGE ............ the 40k proxifly list no longer grows forever.
22. BUG FIXES ................... None-safe callbacks, FSM handlers no longer eat
                                  uploads, shared aiohttp session, psutil warning,
                                  pause persistence, keepalive is real work.

ARCHITECTURE (single asyncio event loop, single process)
--------------------------------------------------------------------------------
    fetchers ──► SQLite (WAL) ──► preflight pool (N=512 light sockets)
                                        │  stage1 TCP + stage2 handshake
                                        ▼
                             ALIVE proxies + detected protocol
                                        │
                     ┌──────────────────┴──────────────────┐
              fresh scheduler                        retry scheduler
                     │                                      │
              main worker pool                        retry worker pool
                     └──────────────► browser pool ◄────────┘
                                   (persistent Chromium)
                                        │
                                  validation rules
                                        ▼
                            SQLite  ──►  output / metrics / Telegram

USAGE
    python3 main.py init          # create config.json, targets.json, requirements.txt
    python3 main.py tmux start    # run supervised in the background (survives updates)
    python3 main.py run           # run in the foreground (still silent)
    python3 main.py status        # read the DB without touching the daemon

Requires Python 3.10+.  Only `playwright` is hard-required; aiogram, aiohttp,
psutil and pymongo are optional and the daemon degrades gracefully without them.

NOTE ON RESPONSIBLE USE
    targets.json ships disabled.  Point this at sites you own or are authorised to
    test.  The validation rules exist to tell a working proxy from a broken one,
    not to defeat anyone's access controls.
"""

from __future__ import annotations

import argparse
import asyncio
import contextlib
import dataclasses
import gzip
import hashlib
import html
import ipaddress
import json
import logging
import math
import os
import random
import re
import shlex
import shutil
import signal
import socket
import sqlite3
import struct
import subprocess
import sys
import threading
import time
import traceback
import urllib.error
import urllib.request
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, field
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Optional
from urllib.parse import unquote, urlparse

# ── Optional / platform dependencies ─────────────────────────────────────────
try:
    import fcntl                                   # POSIX only; used for the instance lock
except ImportError:
    fcntl = None

try:
    import resource                                # POSIX only; used to raise the FD limit
except ImportError:
    resource = None

try:
    import psutil                                  # optional; enables RAM-aware autoscaling
except ImportError:
    psutil = None

# ── Aiogram 3.x ──────────────────────────────────────────────────────────────
# Handlers are registered at module level, so when aiogram is absent we install
# no-op stubs.  That keeps `python3 main.py status` working on a machine that
# never installed the bot dependencies.
try:
    from aiogram import BaseMiddleware, Bot, Dispatcher, F, Router
    from aiogram.client.default import DefaultBotProperties
    from aiogram.exceptions import (TelegramBadRequest, TelegramForbiddenError,
                                    TelegramRetryAfter, TelegramUnauthorizedError)
    from aiogram.filters import Command
    from aiogram.fsm.context import FSMContext
    from aiogram.fsm.state import State, StatesGroup
    from aiogram.types import (BufferedInputFile, CallbackQuery, InlineKeyboardButton,
                               InlineKeyboardMarkup, Message)
    AIOGRAM_OK = True
except ImportError:                                # pragma: no cover - import-time shim
    AIOGRAM_OK = False

    class _Chain:                                  # stands in for the magic filter `F`
        def __getattr__(self, _name): return self
        def __call__(self, *a, **k): return self
        def __eq__(self, _other): return self
        def __hash__(self): return 0

    class _Registrar:
        def __call__(self, *a, **k): return lambda fn: fn
        def outer_middleware(self, *a, **k): return None

    class Router:
        def __init__(self, *a, **k):
            self.message = _Registrar()
            self.callback_query = _Registrar()

    class BaseMiddleware: ...
    class StatesGroup: ...
    class State:
        def __init__(self, *a, **k): ...
    def Command(*a, **k): return None

    class TelegramBadRequest(Exception): ...
    class TelegramForbiddenError(Exception): ...
    class TelegramUnauthorizedError(Exception): ...
    class TelegramRetryAfter(Exception):
        retry_after = 1

    F = _Chain()
    Bot = Dispatcher = DefaultBotProperties = None
    BufferedInputFile = CallbackQuery = FSMContext = None
    InlineKeyboardButton = InlineKeyboardMarkup = Message = None

# ── Playwright ───────────────────────────────────────────────────────────────
try:
    from playwright.async_api import Error as PlaywrightError
    from playwright.async_api import TimeoutError as PlaywrightTimeout
    from playwright.async_api import async_playwright
    PLAYWRIGHT_OK = True
except ImportError:                                # pragma: no cover
    PLAYWRIGHT_OK = False
    async_playwright = None

    class PlaywrightError(Exception): ...
    class PlaywrightTimeout(PlaywrightError): ...


VERSION = "6.2"
RESTART_EXIT_CODE = 75                  # tmux wrapper relaunches on this code
ROOT = Path(__file__).resolve().parent
CONFIG_FILE = ROOT / "config.json"
TARGETS_FILE = ROOT / "targets.json"
TMUX_SESSION = "proxy-monitor"

MAX_MAIN_WORKERS = 16                   # hard ceiling for the fresh-test pool
MAX_RETRY_WORKERS = 16                  # hard ceiling for the retry pool
MAX_PREFLIGHT_WORKERS = 2000            # hard ceiling for the socket pool


# ══════════════════════════════════════════════════════════════════════════════
#  CONFIG
#  Every field below is editable from Telegram (⚙️ Settings) unless marked
#  "restart required".  Types are enforced on load so a hand-edited config.json
#  with "12" instead of 12 can never crash the daemon.
# ══════════════════════════════════════════════════════════════════════════════
@dataclass
class Config:
    # ---- hardware / concurrency --------------------------------------------
    auto_tune: bool = False                 # derive pool sizes from real CPU+RAM
    worker_count: int = 3                   # FRESH-test Playwright workers
    retry_worker_count: int = 2             # RETRY / re-verify Playwright workers
    preflight_worker_count: int = 10        # lightweight TCP+handshake sockets
    browser_count: int = 2                 # persistent Chromium processes
    contexts_per_browser: int = 5           # concurrent isolated contexts per browser
    browser_recycle_after: int = 150        # replace a Chromium after N contexts
    fd_limit_target: int = 16384            # RLIMIT_NOFILE we try to reach at boot
    headless: bool = True
    chromium_no_sandbox: bool = True
    ignore_https_errors: bool = True

    # ---- user agent / fingerprint -------------------------------------------
    ua_rotation: bool = True                # vary UA/viewport/locale/tz per session
    custom_ua_profiles: list = field(default_factory=list)   
    ua_pool_remote: bool = False            # DO NOT fetch remote UA list during testing
    ua_pool_refresh_seconds: float = 3600.0
    enable_stealth_script: bool = True
    session_cache_enabled: bool = True      # reuse cookies per (proxy, target)

    # ---- verification window -------------------------------------------------
    post_load_wait_seconds: float = 25.0
    navigation_timeout_ms: int = 45_000
    network_idle_timeout_ms: int = 12_000
    connect_jitter_min: float = 2.0         # Increased to prevent connection bursts
    connect_jitter_max: float = 10.0        # Increased to prevent connection bursts
    stability_poll_seconds: float = 5.0
    hard_timeout_extra_seconds: float = 90.0

    # ---- preflight (stage 1 + stage 2) --------------------------------------
    tcp_preflight_timeout: float = 1.5      # stage 1: raw TCP connect
    handshake_probe_enabled: bool = True    # stage 2: real proxy handshake
    handshake_timeout: float = 3.0
    probe_protocols: bool = True            # auto-detect http / socks5 / socks4
    probe_connect_host: str = "1.1.1.1"     # CONNECT/SOCKS probe destination (IP: no DNS)
    probe_connect_port: int = 443
    preflight_recheck_seconds: float = 21_600.0   # recheck a live proxy every 6h
    preflight_dead_base_cooldown: float = 900.0   # first dead retry after 15m, then x2
    preflight_dead_max_cooldown: float = 86_400.0
    purge_dead_after_days: float = 3.0      # delete proxies dead this long (0 = never)
    purge_dead_min_fails: int = 4

    # ---- scheduler ----------------------------------------------------------
    scheduler_tick_seconds: float = 5.0
    claim_timeout_seconds: float = 600.0    # stale in-flight claims become eligible again
    batch_size_per_tick: int = 30
    queue_extra: int = 4                    # queue depth = workers + queue_extra
    min_retest_gap_seconds: float = 900.0
    cross_target_parallel: bool = False

    # ---- cooldown / quarantine ladder ---------------------------------------
    working_cooldown: float = 1_800.0
    retryable_cooldown: float = 900.0
    retryable_attempts: int = 1
    quarantined_cooldown_1: float = 3_600.0
    quarantined_cooldown_2: float = 21_600.0
    failed_cooldown: float = 86_400.0
    recovered_probe_cooldown: float = 600.0
    soft_retry_cooldown: float = 120.0
    soft_max_streak: int = 5
    cooldown_jitter: float = 0.10
    failure_policy: dict = field(default_factory=lambda: {
        "TCP_FAILURE":              {"cooldown_mult": 1.0},
        "CONNECTION_TIMEOUT":       {"cooldown_mult": 1.0},
        "NAVIGATION_TIMEOUT":       {"cooldown_mult": 0.75},
        "HTTP_ERROR":               {"cooldown_mult": 0.75},
        "EMPTY_RESPONSE":           {"cooldown_mult": 0.75},
        "TARGET_VALIDATION_FAILED": {"cooldown_mult": 0.5},
        "BROWSER_ERROR":            {"soft": True},
        "RETRYABLE_ERROR":          {"soft": True},
    })

    # ---- health score (per proxy+target, 0..1) ------------------------------
    score_weights: dict = field(default_factory=lambda: {
        "overall": 0.25, "recent": 0.30, "latency": 0.15, "streak": 0.30})
    score_latency_ref_seconds: float = 8.0
    score_recent_alpha: float = 0.30

    # ---- circuit breaker / environment guards -------------------------------
    circuit_window: int = 20
    circuit_block_ratio: float = 0.70
    circuit_cooldown: float = 300.0
    circuit_max_cooldown: float = 3_600.0
    circuit_probe_count: int = 3
    circuit_classes: list = field(default_factory=lambda: [
        "TARGET_VALIDATION_FAILED", "BROWSER_ERROR", "RETRYABLE_ERROR"])
    circuit_ignore_classes: list = field(default_factory=lambda: ["TCP_FAILURE"])
    net_probe_hosts: list = field(default_factory=lambda: ["1.1.1.1:443", "8.8.8.8:53", "9.9.9.9:443"])
    net_probe_timeout: float = 3.0
    net_fail_ratio: float = 0.90
    memory_high_percent: float = 90.0

    # ---- output / logging / maintenance -------------------------------------
    silent_terminal: bool = True            # fatal errors -> logs + Telegram, not stdout
    output_flush_interval: float = 15.0
    output_mode: str = "any"                # "any" = works for >=1 target, "all" = every target
    output_include_preflight: bool = False  # publish proxies that only passed preflight
    output_max_age_seconds: float = 0.0
    history_retention_days: float = 7.0
    log_level: str = "INFO"
    log_max_bytes: int = 5_000_000
    log_backup_count: int = 3
    maintenance_interval_seconds: float = 3_600.0
    backup_interval_hours: float = 6.0
    backup_keep: int = 8
    shutdown_grace_seconds: float = 20.0
    metrics_interval_seconds: float = 30.0
    metrics_file: str = "metrics.json"

    # ---- HTTP endpoint / keep-alive / public URL -----------------------------
    http_api_enabled: bool = True
    http_api_host: str = "127.0.0.1"        # set 0.0.0.0 to expose via a forwarded port
    http_api_port: int = 8080
    http_api_token: str = ""                # required when host is not loopback
    keepalive_enabled: bool = True
    keepalive_interval_seconds: float = 90.0
    uptimerobot_url: str = ""               # outbound heartbeat ping (every 5 min)
    uptimerobot_interval_seconds: float = 300.0

    # ---- Telegram -------------------------------------------------------------
    telegram_bot_token: str = ""
    telegram_chat_id: str = ""              # alert destination; a private chat id also grants control
    telegram_admin_ids: list = field(default_factory=list)   # user ids allowed to control the bot
    live_status_interval: float = 5.0       # seconds between live-status edits
    live_status_idle_interval: float = 30.0 # slower interval once nothing changes
    notify_dedupe_seconds: float = 900.0    # suppress an identical alert within this window

    # ---- GitHub Codespace control --------------------------------------------
    github_token: str = ""                  # PAT with `codespace` scope (or use the gh CLI)
    codespace_name: str = ""                # blank = read $CODESPACE_NAME

    # ---- MongoDB mirror (optional, off by default) ---------------------------
    mongo_enabled: bool = False
    mongo_uri: str = ""
    mongo_db: str = "radiate"
    mongo_sync_interval_seconds: float = 300.0

    # ---- runtime state persisted across restarts -----------------------------
    system_paused: bool = False
    pause_until: float = 0.0                # epoch seconds; 0 = paused indefinitely
    default_referer: str = ""

    # ---- files / sources -------------------------------------------------------
    proxy_files: list = field(default_factory=lambda: ["proxy_worked.txt"])
    proxy_file_watch: bool = True
    data_dir: str = "data"
    log_dir: str = "logs"
    output_dir: str = "output"
    state_dir: str = "state"
    output_file: str = "validated_proxies.txt"

    # Removed default massive proxy list to prevent GitHub account suspension
    fallback_urls: list = field(default_factory=list)
    fallback_min_working: int = 50
    fallback_cooldown_seconds: float = 1_800.0
    fetch_on_start: bool = False            # DO NOT fetch automatically at boot

    # ---- git auto-update -------------------------------------------------------
    git_enabled: bool = False
    git_remote: str = "origin"
    git_branch: str = "main"
    git_check_interval_seconds: float = 900.0
    git_auto_restart: bool = True
    git_push_state: bool = False
    git_push_interval_seconds: float = 3_600.0


# ── type coercion + persistence ───────────────────────────────────────────────
def _coerce(default, value):
    """Best-effort coercion so a hand-edited config.json cannot crash the daemon."""
    if isinstance(default, bool):
        if isinstance(value, str):
            return value.strip().lower() in ("1", "true", "yes", "on")
        return bool(value)
    if isinstance(default, int) and not isinstance(default, bool):
        return int(float(value))
    if isinstance(default, float):
        return float(value)
    if isinstance(default, list) and not isinstance(value, list):
        return list(default)
    if isinstance(default, dict) and not isinstance(value, dict):
        return dict(default)
    return value


def _atomic_write(path: Path, text: str) -> None:
    """Write via a temp file + os.replace so a crash never leaves a half file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
        f.flush()
        with contextlib.suppress(OSError):
            os.fsync(f.fileno())
    os.replace(tmp, path)


def _detect_hardware() -> tuple[int, float]:
    """(cpu_cores, total_ram_gb).  Falls back to /proc/meminfo when psutil is absent."""
    cpu = os.cpu_count() or 2
    ram_gb = 0.0
    if psutil is not None:
        with contextlib.suppress(Exception):
            ram_gb = psutil.virtual_memory().total / (1024 ** 3)
    if ram_gb <= 0:
        with contextlib.suppress(Exception):
            for line in Path("/proc/meminfo").read_text().splitlines():
                if line.startswith("MemTotal:"):
                    ram_gb = int(line.split()[1]) / (1024 ** 2)
                    break
    return cpu, (ram_gb or 4.0)


def apply_auto_tune(cfg: "Config") -> dict:
    """Size the pools from the machine we are actually on (4 cores / 16 GB -> 3x5, 6+6, 512)."""
    cpu, ram = _detect_hardware()
    cfg.browser_count = max(1, min(4, cpu - 1 if cpu > 1 else 1))
    cfg.contexts_per_browser = max(2, min(6, int(ram // 3) or 2))
    slots = cfg.browser_count * cfg.contexts_per_browser
    cfg.worker_count = max(1, min(MAX_MAIN_WORKERS, slots // 2))
    cfg.retry_worker_count = max(1, min(MAX_RETRY_WORKERS, slots - cfg.worker_count))
    cfg.preflight_worker_count = max(64, min(MAX_PREFLIGHT_WORKERS, 128 * cpu))
    return {"cpu": cpu, "ram_gb": round(ram, 1), "browsers": cfg.browser_count,
            "contexts": cfg.contexts_per_browser, "fresh": cfg.worker_count,
            "retry": cfg.retry_worker_count, "preflight": cfg.preflight_worker_count}


def _write_config(cfg: Config) -> None:
    _atomic_write(CONFIG_FILE, json.dumps(asdict(cfg), indent=2))
    with contextlib.suppress(OSError):
        os.chmod(CONFIG_FILE, 0o600)        # config.json holds the bot token and the PAT


def _clamp_config(cfg: Config) -> None:
    """Single place where every invariant is enforced, after load and after any edit."""
    cfg.worker_count = min(MAX_MAIN_WORKERS, max(1, cfg.worker_count))
    cfg.retry_worker_count = min(MAX_RETRY_WORKERS, max(0, cfg.retry_worker_count))
    cfg.preflight_worker_count = min(MAX_PREFLIGHT_WORKERS, max(8, cfg.preflight_worker_count))
    cfg.browser_count = max(1, min(8, cfg.browser_count))
    cfg.contexts_per_browser = max(1, min(12, cfg.contexts_per_browser))
    cfg.circuit_window = max(5, cfg.circuit_window)
    cfg.circuit_probe_count = max(1, cfg.circuit_probe_count)
    cfg.batch_size_per_tick = max(1, min(500, cfg.batch_size_per_tick))
    cfg.live_status_interval = max(3.0, min(60.0, cfg.live_status_interval))
    cfg.live_status_idle_interval = max(cfg.live_status_interval, min(300.0, cfg.live_status_idle_interval))
    cfg.tcp_preflight_timeout = max(0.2, min(10.0, cfg.tcp_preflight_timeout))
    cfg.handshake_timeout = max(0.5, min(15.0, cfg.handshake_timeout))
    cfg.telegram_chat_id = str(cfg.telegram_chat_id).strip()
    cfg.telegram_admin_ids = [str(x).strip() for x in (cfg.telegram_admin_ids or []) if str(x).strip()]
    cfg.output_mode = cfg.output_mode if cfg.output_mode in ("any", "all") else "any"
    if sum(float(v) for v in cfg.score_weights.values()) <= 0:
        cfg.score_weights = {"overall": 0.25, "recent": 0.30, "latency": 0.15, "streak": 0.30}
    known = {"TCP_FAILURE", "CONNECTION_TIMEOUT", "NAVIGATION_TIMEOUT", "HTTP_ERROR",
             "EMPTY_RESPONSE", "TARGET_VALIDATION_FAILED", "BROWSER_ERROR", "RETRYABLE_ERROR"}
    cfg.failure_policy = {k: v for k, v in cfg.failure_policy.items() if k in known}


_BOOT_NOTES: list[str] = []                 # startup messages; flushed to the log once it exists


def load_config() -> Config:
    cfg = Config()
    if CONFIG_FILE.exists():
        try:
            data = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
            for k, v in data.items():
                if hasattr(cfg, k):
                    with contextlib.suppress(Exception):
                        setattr(cfg, k, _coerce(getattr(Config(), k), v))
            if any(k not in data for k in asdict(cfg)):      # new keys appeared after an update
                with contextlib.suppress(Exception):
                    _write_config(cfg)
        except Exception as exc:
            _BOOT_NOTES.append(f"config.json unreadable ({exc}) - defaults in use")
    else:
        with contextlib.suppress(Exception):
            _write_config(cfg)

    if cfg.auto_tune:
        info = apply_auto_tune(cfg)
        _BOOT_NOTES.append(
            f"auto-tune: {info['cpu']} cores / {info['ram_gb']} GB -> "
            f"{info['browsers']}x{info['contexts']} contexts, {info['fresh']} fresh + "
            f"{info['retry']} retry workers, {info['preflight']} preflight sockets")
    _clamp_config(cfg)
    return cfg


def save_config(cfg: Config) -> None:
    _clamp_config(cfg)
    _write_config(cfg)


CFG = load_config()


# ══════════════════════════════════════════════════════════════════════════════
#  PATHS
# ══════════════════════════════════════════════════════════════════════════════
def _rp(p: str) -> Path:
    q = Path(p)
    return q if q.is_absolute() else ROOT / q


DATA_DIR = _rp(CFG.data_dir)
LOG_DIR = _rp(CFG.log_dir)
OUT_DIR = _rp(CFG.output_dir)
STATE_DIR = _rp(CFG.state_dir)
BACKUP_DIR = DATA_DIR / "backups"
SESSIONS_DIR = DATA_DIR / "sessions"
UPLOAD_DIR = DATA_DIR / "uploads"
DB_FILE = DATA_DIR / "proxy_state.db"
LOCK_FILE = DATA_DIR / "monitor.lock"
HEARTBEAT_FILE = DATA_DIR / "heartbeat"
DEPS_STAMP = DATA_DIR / "requirements.sha1"
OUTPUT_FILE = OUT_DIR / CFG.output_file
for _d in (DATA_DIR, LOG_DIR, OUT_DIR, STATE_DIR, BACKUP_DIR, SESSIONS_DIR, UPLOAD_DIR):
    _d.mkdir(parents=True, exist_ok=True)


# ══════════════════════════════════════════════════════════════════════════════
#  SILENT LOGGING
#  Nothing ever reaches stdout while the daemon runs.  Five rotating files split
#  by concern; noisy third-party loggers are pinned to WARNING.
# ══════════════════════════════════════════════════════════════════════════════
def _setup_logging() -> dict:
    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s")
    level = getattr(logging, str(CFG.log_level).upper(), logging.INFO)

    def handler(filename: str) -> RotatingFileHandler:
        fh = RotatingFileHandler(LOG_DIR / filename, maxBytes=CFG.log_max_bytes,
                                 backupCount=CFG.log_backup_count, encoding="utf-8")
        fh.setFormatter(fmt)
        return fh

    def mk(name: str, filename: str, lvl: int) -> logging.Logger:
        lg = logging.getLogger(name)
        lg.setLevel(lvl)
        lg.propagate = False
        lg.handlers = [handler(filename)]
        return lg

    root = logging.getLogger()
    root.handlers = [handler("errors.log")]
    root.setLevel(logging.WARNING)
    for noisy in ("aiogram", "aiogram.event", "asyncio", "aiohttp", "pymongo", "websockets"):
        logging.getLogger(noisy).setLevel(logging.WARNING)

    return {
        "daemon":     mk("radiate.daemon",     "daemon.log",     level),
        "validation": mk("radiate.validation", "validation.log", level),
        "errors":     mk("radiate.errors",     "errors.log",     logging.WARNING),
        "recovery":   mk("radiate.recovery",   "recovery.log",   level),
        "git":        mk("radiate.git",        "git.log",        level),
    }


LOGS = _setup_logging()
log = LOGS["daemon"]
vlog = LOGS["validation"]
elog = LOGS["errors"]
rlog = LOGS["recovery"]
glog = LOGS["git"]

for _n in _BOOT_NOTES:
    log.info("%s", _n)


def _say(text: str, err: bool = False) -> None:
    """Terminal output for user-invoked CLI commands only - never used by the daemon."""
    print(text, file=sys.stderr if err else sys.stdout)


def fatal(msg: str, exc: BaseException | None = None) -> None:
    """A failure the operator must know about.

    Silent terminal means the Codespace stays clean, so the message is written to
    errors.log and pushed to Telegram instead of being printed.  If silent_terminal
    is turned off it also goes to stderr.
    """
    elog.critical("%s", msg, exc_info=exc)
    with contextlib.suppress(Exception):
        send_sync_alert(f"\u26d4 RADIATE v{VERSION} FATAL\n{msg}")
    if not CFG.silent_terminal:
        print(f"FATAL: {msg}", file=sys.stderr)


def raise_fd_limit() -> Optional[int]:
    """The preflight pool opens hundreds of sockets; the default 1024 soft limit is not enough."""
    if resource is None:
        return None
    try:
        soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
        want = min(max(soft, CFG.fd_limit_target), hard)
        if want > soft:
            resource.setrlimit(resource.RLIMIT_NOFILE, (want, hard))
        return want
    except Exception as exc:
        elog.warning("could not raise RLIMIT_NOFILE: %s", exc)
        return None


def fd_budget_for_preflight(limit: Optional[int]) -> int:
    """Keep ~40% of the descriptors free for Chromium, SQLite and the bot."""
    if not limit:
        return CFG.preflight_worker_count
    return max(16, min(CFG.preflight_worker_count, int(limit * 0.6) - 256))


def cleanup_sessions(max_age_days: float) -> None:
    now = time.time()
    for f in SESSIONS_DIR.glob("*.json"):
        with contextlib.suppress(OSError):
            if now - f.stat().st_mtime > max_age_days * 86_400:
                f.unlink()


def cleanup_uploads() -> None:
    for f in UPLOAD_DIR.glob("*.txt"):
        with contextlib.suppress(OSError):
            if time.time() - f.stat().st_mtime > 3600:
                f.unlink()


def human_seconds(s: float) -> str:
    s = int(max(0, s))
    if s < 60:
        return f"{s}s"
    if s < 3600:
        return f"{s // 60}m {s % 60}s"
    if s < 86_400:
        return f"{s // 3600}h {(s % 3600) // 60}m"
    return f"{s // 86_400}d {(s % 86_400) // 3600}h"


# ══════════════════════════════════════════════════════════════════════════════
#  TARGETS
# ══════════════════════════════════════════════════════════════════════════════
# Markers that mean "the page we got is not the page we asked for".  The one you
# actually hit in the wild - "anonymous proxy detected" - is included, and Rule A
# below adds a separate case-insensitive catch for "proxy detection".
DEFAULT_FORBIDDEN = [
    "checking your browser",
    "just a moment",
    "verify you are human",
    "attention required",
    "anonymous proxy detected",
    "proxy detected",
    "proxy detection",
    "ddos protection",
    "please wait while we check",
    "enable javascript and cookies",
    "html:cf-chl-",
    "html:challenge-platform",
]
_LEGACY_DROP = {"cloudflare"}
_LEGACY_HTML = {"cf-chl-", "challenge-platform"}


@dataclass
class Target:
    target_id: str
    url: str
    enabled: bool = True
    post_load_wait_seconds: float = 20.0
    navigation_timeout_ms: int = 45_000
    interaction_steps: list = field(default_factory=list)
    reload_after_load: bool = False
    success_markers: list = field(default_factory=list)
    forbidden_markers: list = field(default_factory=lambda: list(DEFAULT_FORBIDDEN))
    success_selectors: list = field(default_factory=list)
    success_selectors_mode: str = "any"
    forbidden_selectors: list = field(default_factory=list)
    title_contains: list = field(default_factory=list)
    min_body_length: int = 40
    require_status_200: bool = True
    cooldowns: dict = field(default_factory=dict)
    referer: str = ""
    # --- redirect handling ---------------------------------------------------
    # allow_offsite_redirect : accept a final page on a different host at all.
    # redirect_means_success : "Rule B" - a redirect away from target.url is itself
    #                          the success signal, so marker/status/body checks are
    #                          skipped.  OFF by default: a proxy bounced to a
    #                          captcha or ISP block page also redirects, and would
    #                          otherwise be published as WORKING.
    allow_offsite_redirect: bool = False
    redirect_means_success: bool = False
    notes: str = ""


_TARGET_FIELDS = {f.name for f in dataclasses.fields(Target)}


def _slug(url: str) -> str:
    p = urlparse(url)
    base = re.sub(r"[^a-zA-Z0-9_-]", "", (p.netloc + p.path).replace("/", "_").replace(".", "_"))[:40]
    h = hashlib.sha1(url.encode()).hexdigest()[:6]
    return f"{base}_{h}" if base else h


def _clean_markers(markers: list) -> list:
    out = []
    for m in markers or []:
        ml = str(m).strip().lower()
        if not ml or ml in _LEGACY_DROP:
            continue
        if ml in _LEGACY_HTML:
            ml = "html:" + ml
        out.append(ml)
    return out


def _target_from_dict(item: dict) -> Target:
    url = str(item["url"]).strip()
    pu = urlparse(url)
    if pu.scheme not in ("http", "https") or not pu.netloc:
        raise ValueError(f"invalid target url: {url!r}")
    kw = {k: v for k, v in item.items() if k in _TARGET_FIELDS}
    kw["url"] = url
    kw["target_id"] = re.sub(r"[^A-Za-z0-9_.-]", "_", str(item.get("target_id") or _slug(url)))
    kw.setdefault("post_load_wait_seconds", CFG.post_load_wait_seconds)
    kw.setdefault("navigation_timeout_ms", CFG.navigation_timeout_ms)
    t = Target(**kw)
    t.forbidden_markers = _clean_markers(t.forbidden_markers)
    t.success_markers = [str(m).lower() for m in t.success_markers]
    t.post_load_wait_seconds = float(t.post_load_wait_seconds)
    t.navigation_timeout_ms = int(t.navigation_timeout_ms)
    t.min_body_length = int(t.min_body_length)
    return t


def template_targets() -> list[dict]:
    return [{
        "target_id": "example",
        "url": "https://example.com/",
        "enabled": False,
        "post_load_wait_seconds": 40,
        "navigation_timeout_ms": 45000,
        "interaction_steps": [
            {"action": "wait", "ms": 2000},
            {"action": "scroll", "count": 2, "dy": 400},
        ],
        "success_markers": [],
        "referer": "",
        "allow_offsite_redirect": False,
        "redirect_means_success": False,
        "notes": "Replace with a site you own or are authorised to test, then set enabled=true.",
    }]


def save_targets(targets: list[Target]) -> None:
    _atomic_write(TARGETS_FILE, json.dumps([asdict(t) for t in targets], indent=2))


def load_targets() -> list[Target]:
    if not TARGETS_FILE.exists():
        _atomic_write(TARGETS_FILE, json.dumps(template_targets(), indent=2))
    try:
        raw = json.loads(TARGETS_FILE.read_text(encoding="utf-8"))
    except Exception as exc:
        raise ValueError(f"targets.json unreadable: {exc}") from exc
    if not isinstance(raw, list):
        raise ValueError("targets.json must be a JSON list")
    out, seen = [], set()
    for item in raw:
        try:
            t = _target_from_dict(item)
        except Exception as exc:
            elog.error("targets.json: skipping invalid entry (%s)", exc)
            continue
        if t.target_id in seen:
            continue
        seen.add(t.target_id)
        out.append(t)
    return out


def cooldown_for(overrides: dict, key: str) -> float:
    return float(overrides.get(key, getattr(CFG, key)))


class TargetRegistry:
    """Hot-reloads targets.json whenever its mtime/size changes."""

    def __init__(self) -> None:
        self.targets: dict[str, Target] = {}
        self._sig: Optional[tuple] = None

    @staticmethod
    def _stat() -> Optional[tuple]:
        try:
            st = TARGETS_FILE.stat()
            return (st.st_mtime_ns, st.st_size)
        except OSError:
            return None

    def reload(self) -> bool:
        try:
            lst = load_targets()
        except ValueError as exc:
            elog.error("target reload failed, keeping previous set: %s", exc)
            self._sig = self._stat()
            return False
        self.targets = {t.target_id: t for t in lst}
        self._sig = self._stat()
        return True

    def changed(self) -> bool:
        return self._stat() != self._sig

    def get(self, tid: str) -> Optional[Target]:
        return self.targets.get(tid)

    def enabled(self) -> list[Target]:
        return [t for t in self.targets.values() if t.enabled]


# ══════════════════════════════════════════════════════════════════════════════
#  PROXY UTILITIES
# ══════════════════════════════════════════════════════════════════════════════
_HOST_RE = re.compile(r"^[A-Za-z0-9._-]+$")
SCHEMES = ("http", "https", "socks5", "socks4")


def normalize_proxy(raw: str) -> Optional[str]:
    """Canonicalise one line into scheme://[user:pass@]host:port, or None if unusable.

    A line with no scheme (your "IP:Port only" files) becomes http:// here; the
    preflight stage later probes http/socks5/socks4 and remembers what really works,
    so a scheme-less SOCKS proxy is no longer mis-tested as HTTP.
    """
    if not raw or not isinstance(raw, str):
        return None
    p = raw.strip()
    if not p or p.startswith("#"):
        return None
    p = re.split(r"\s+#", p, maxsplit=1)[0].strip().rstrip("/")
    scheme = "http"
    if "://" in p:
        scheme, p = p.split("://", 1)
        scheme = scheme.lower()
    if scheme == "socks5h":
        scheme = "socks5"
    if scheme not in SCHEMES:
        return None

    user = pwd = None
    if "@" in p:
        cred, hostport = p.rsplit("@", 1)
        user, _, pwd = cred.partition(":")
        pwd = pwd or None
    else:
        hostport = p
    if hostport.startswith("["):                       # [v6]:port
        m = re.match(r"^\[([0-9A-Fa-f:.]+)\]:(\d+)$", hostport)
        if not m:
            return None
        host, port_s = m.group(1), m.group(2)
    else:
        parts = hostport.split(":")
        if len(parts) == 2:
            host, port_s = parts
        elif len(parts) == 4 and user is None:         # host:port:user:pass
            host, port_s, user, pwd = parts
        else:
            return None
    if not host or not _HOST_RE.match(host.replace(":", "a")):
        return None
    try:
        port = int(port_s)
    except ValueError:
        return None
    if not (0 < port <= 65535):
        return None
    # Chromium cannot do SOCKS authentication, so an authenticated SOCKS proxy is
    # unusable here.  Dropping it early keeps it out of every queue and report.
    if scheme.startswith("socks") and user:
        return None
    host = host.lower()
    hostpart = f"[{host}]" if ":" in host else host
    auth = ""
    if user:
        auth = f"{user}:{pwd}@" if pwd is not None else f"{user}@"
    return f"{scheme}://{auth}{hostpart}:{port}"


def mask_proxy(proxy: str) -> str:
    """Never let a proxy password reach a log file, an export or a Telegram message."""
    return re.sub(r"(://[^:/@]+):[^@]*@", r"\1:***@", proxy)


def apply_scheme(proxy: str, scheme: Optional[str]) -> str:
    """Rewrite the scheme of a stored proxy to the protocol preflight actually proved."""
    if not scheme or "://" not in proxy:
        return proxy
    return scheme + "://" + proxy.split("://", 1)[1]


def build_proxy_config(proxy: str) -> dict:
    """Playwright context proxy dict."""
    u = urlparse(proxy)
    host = u.hostname or ""
    if ":" in host:
        host = f"[{host}]"
    cfg = {"server": f"{u.scheme}://{host}:{u.port}"}
    if u.username:
        cfg["username"] = unquote(u.username)
    if u.password:
        cfg["password"] = unquote(u.password)
    return cfg


def split_hostport(proxy: str) -> tuple[Optional[str], Optional[int]]:
    try:
        u = urlparse(proxy)
        return u.hostname, u.port
    except ValueError:
        return None, None


# ── stage 1: raw TCP reachability ─────────────────────────────────────────────
async def _tcp_ok(host: str, port: int, timeout: float) -> bool:
    try:
        _, writer = await asyncio.wait_for(asyncio.open_connection(host, port), timeout=timeout)
    except Exception:
        return False
    writer.close()
    with contextlib.suppress(Exception):
        await writer.wait_closed()
    return True


async def tcp_preflight(proxy: str, timeout: float) -> bool:
    host, port = split_hostport(proxy)
    if not host or not port:
        return False
    return await _tcp_ok(host, port, timeout)


# ── stage 2: prove it is actually a proxy, and of which protocol ──────────────
# Each probe opens one short-lived socket and speaks the first bytes of the
# protocol.  This is dramatically cheaper than launching Chromium and removes the
# large class of "port 8080 is open but it is a router, not a proxy" hosts.
async def _probe_http_connect(host: str, port: int, timeout: float,
                              user: Optional[str] = None, pwd: Optional[str] = None) -> bool:
    dst = f"{CFG.probe_connect_host}:{CFG.probe_connect_port}"
    req = f"CONNECT {dst} HTTP/1.1\r\nHost: {dst}\r\nProxy-Connection: keep-alive\r\n"
    if user:
        import base64
        token = base64.b64encode(f"{user}:{pwd or ''}".encode()).decode()
        req += f"Proxy-Authorization: Basic {token}\r\n"
    req += "\r\n"
    writer = None
    try:
        reader, writer = await asyncio.wait_for(asyncio.open_connection(host, port), timeout=timeout)
        writer.write(req.encode())
        await asyncio.wait_for(writer.drain(), timeout=timeout)
        line = await asyncio.wait_for(reader.readline(), timeout=timeout)
        if not line.startswith(b"HTTP/"):
            return False
        parts = line.split()
        code = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 0
        # 2xx  = tunnel established.  403/405 = it IS an HTTP proxy but forbids
        # CONNECT to our probe host; still a proxy, so we accept it and let the
        # browser stage make the final call.  407 = needs credentials we do not have.
        return 200 <= code < 300 or code in (403, 405)
    except Exception:
        return False
    finally:
        if writer is not None:
            writer.close()
            with contextlib.suppress(Exception):
                await writer.wait_closed()


async def _probe_socks5(host: str, port: int, timeout: float) -> bool:
    writer = None
    try:
        reader, writer = await asyncio.wait_for(asyncio.open_connection(host, port), timeout=timeout)
        writer.write(b"\x05\x01\x00")                       # VER=5, 1 method, NO-AUTH
        await asyncio.wait_for(writer.drain(), timeout=timeout)
        data = await asyncio.wait_for(reader.readexactly(2), timeout=timeout)
        # 0x05 0x00 = no auth required.  0x05 0xFF = it is SOCKS5 but wants auth,
        # which Chromium cannot supply, so that one is rejected.
        return data[0] == 0x05 and data[1] == 0x00
    except Exception:
        return False
    finally:
        if writer is not None:
            writer.close()
            with contextlib.suppress(Exception):
                await writer.wait_closed()


async def _probe_socks4(host: str, port: int, timeout: float) -> bool:
    writer = None
    try:
        try:
            dst_ip = ipaddress.IPv4Address(CFG.probe_connect_host).packed
        except Exception:
            dst_ip = socket.inet_aton("1.1.1.1")
        reader, writer = await asyncio.wait_for(asyncio.open_connection(host, port), timeout=timeout)
        writer.write(b"\x04\x01" + struct.pack(">H", CFG.probe_connect_port) + dst_ip + b"\x00")
        await asyncio.wait_for(writer.drain(), timeout=timeout)
        data = await asyncio.wait_for(reader.readexactly(8), timeout=timeout)
        # Reply VN must be 0; CD 0x5A = granted.  A rejection (0x5B-0x5D) still
        # proves the endpoint speaks SOCKS4, but not that it is usable, so only
        # a granted request counts.
        return data[0] == 0x00 and data[1] == 0x5A
    except Exception:
        return False
    finally:
        if writer is not None:
            writer.close()
            with contextlib.suppress(Exception):
                await writer.wait_closed()


async def detect_protocol(proxy: str, declared: str, timeout: float) -> Optional[str]:
    """Return the protocol that answered, or None if nothing did.

    The declared scheme is tried first so an explicit socks5:// line costs one probe.
    Scheme-less lines fall through http -> socks5 -> socks4, which is the order that
    matches how free proxy lists are usually distributed.
    """
    host, port = split_hostport(proxy)
    if not host or not port:
        return None
    u = urlparse(proxy)
    user, pwd = u.username, u.password

    async def try_one(scheme: str) -> bool:
        if scheme in ("http", "https"):
            return await _probe_http_connect(host, port, timeout, user, pwd)
        if scheme == "socks5":
            return await _probe_socks5(host, port, timeout)
        if scheme == "socks4":
            return await _probe_socks4(host, port, timeout)
        return False

    order = [declared] + [s for s in ("http", "socks5", "socks4") if s != declared]
    if not CFG.probe_protocols:
        order = [declared]
    if user:                                        # only HTTP proxies can carry credentials here
        order = ["http"]
    for scheme in order:
        try:
            if await try_one(scheme):
                return "http" if scheme == "https" else scheme
        except asyncio.CancelledError:
            raise
        except Exception:
            continue
    return None


# ── proxy file / list loading ─────────────────────────────────────────────────
def load_proxy_file(path: Path) -> tuple[list[str], int]:
    out, seen, bad = [], set(), 0
    with path.open("r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            if not line.strip() or line.strip().startswith("#"):
                continue
            p = normalize_proxy(line)
            if p is None:
                # A messy line ("1.2.3.4:8080 US elite") still yields a proxy token.
                m = _PROXY_TOKEN_RE.search(line)
                p = normalize_proxy(m.group(0)) if m else None
            if p is None:
                bad += 1
            elif p not in seen:
                seen.add(p)
                out.append(p)
    return out, bad


def proxy_files_paths() -> list[Path]:
    return [_rp(f) for f in CFG.proxy_files]


def load_all_proxy_files() -> list[str]:
    seen, out = set(), []
    for fp in proxy_files_paths():
        if not fp.exists():
            continue
        lst, _ = load_proxy_file(fp)
        for p in lst:
            if p not in seen:
                seen.add(p)
                out.append(p)
    return out


def proxy_files_signature() -> tuple:
    sig = []
    for fp in proxy_files_paths():
        with contextlib.suppress(OSError):
            st = fp.stat()
            sig.append((str(fp), st.st_mtime_ns, st.st_size))
    return tuple(sig)


# ══════════════════════════════════════════════════════════════════════════════
#  HEALTH SCORE  (per proxy+target, 0..1)
#  Blends lifetime success rate, an EMA of recent results, latency and streaks,
#  then penalises proxies that flap between working and broken.
# ══════════════════════════════════════════════════════════════════════════════
def compute_score(succ: int, fail: int, recent: float, avg_latency: Optional[float],
                  cs: int, cf: int, recoveries: int) -> float:
    total = succ + fail
    if total == 0:
        return 0.0
    overall = (succ + 1) / (total + 2)                     # Laplace-smoothed
    ref = max(CFG.score_latency_ref_seconds, 0.1)
    lat = 0.5 if avg_latency is None else math.exp(-max(avg_latency, 0.0) / ref)
    streak = min(1.0, max(0.0, 0.5 + 0.10 * min(cs, 5) - 0.15 * min(cf, 5)))
    parts = {"overall": overall, "recent": recent, "latency": lat, "streak": streak}
    w = CFG.score_weights
    wsum = sum(max(float(w.get(k, 0.0)), 0.0) for k in parts) or 1.0
    base = sum(max(float(w.get(k, 0.0)), 0.0) * v for k, v in parts.items()) / wsum
    flap = 1.0 / (1.0 + 0.05 * min(recoveries, 10))
    return round(max(0.0, min(1.0, base * flap)), 6)


def _jit(x: float) -> float:
    """Spread cooldowns so thousands of proxies never become due in the same second."""
    j = CFG.cooldown_jitter
    return x * (1.0 + random.uniform(-j, j)) if j > 0 else x


def failure_ladder(cf: int, overrides: dict) -> tuple[str, float]:
    """RETRYABLE -> QUARANTINED -> QUARANTINED(longer) -> FAILED."""
    r = max(0, CFG.retryable_attempts)
    if cf <= r:
        return "RETRYABLE", cooldown_for(overrides, "retryable_cooldown")
    if cf == r + 1:
        return "QUARANTINED", cooldown_for(overrides, "quarantined_cooldown_1")
    if cf == r + 2:
        return "QUARANTINED", cooldown_for(overrides, "quarantined_cooldown_2")
    return "FAILED", cooldown_for(overrides, "failed_cooldown")


# Matches a proxy anywhere in a messy line, with or without scheme/credentials.
_PROXY_TOKEN_RE = re.compile(
    r"(?:(?:https?|socks[45]h?)://)?(?:[^\s:@/]+:[^\s@/]*@)?(?:\d{1,3}\.){3}\d{1,3}:\d{1,5}\b")


# ══════════════════════════════════════════════════════════════════════════════
#  DATABASE
#  SQLite in WAL mode, driven from a single dedicated thread so the event loop
#  never blocks.  Schema v4 moves preflight from (proxy, target) to the proxy
#  itself - the old layout re-pinged the same host once per target.
# ══════════════════════════════════════════════════════════════════════════════
SCHEMA_VERSION = 4

SCHEMA = """
CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT);

CREATE TABLE IF NOT EXISTS proxies (
    proxy_id         INTEGER PRIMARY KEY AUTOINCREMENT,
    proxy            TEXT UNIQUE NOT NULL,
    first_seen       REAL NOT NULL,
    last_seen        REAL NOT NULL,
    global_status    TEXT NOT NULL DEFAULT 'UNTESTED',
    global_score     REAL NOT NULL DEFAULT 0.0,
    notes            TEXT,
    scheme_detected  TEXT,
    preflight_status TEXT NOT NULL DEFAULT 'UNKNOWN',
    preflight_until  REAL NOT NULL DEFAULT 0,
    preflight_fails  INTEGER NOT NULL DEFAULT 0,
    preflight_last   REAL,
    preflight_latency REAL,
    pf_claimed       REAL
);
CREATE INDEX IF NOT EXISTS idx_proxies_status ON proxies(global_status);
CREATE INDEX IF NOT EXISTS idx_proxies_pf     ON proxies(preflight_status, preflight_until);

CREATE TABLE IF NOT EXISTS targets (
    target_id   TEXT PRIMARY KEY,
    url         TEXT NOT NULL,
    enabled     INTEGER NOT NULL DEFAULT 1,
    added_at    REAL NOT NULL,
    config_json TEXT
);

CREATE TABLE IF NOT EXISTS proxy_target (
    proxy_id              INTEGER NOT NULL,
    target_id             TEXT NOT NULL,
    status                TEXT NOT NULL DEFAULT 'UNTESTED',
    failure_class         TEXT,
    last_tested           REAL,
    last_success          REAL,
    last_failure          REAL,
    last_claimed          REAL,
    success_count         INTEGER NOT NULL DEFAULT 0,
    failure_count         INTEGER NOT NULL DEFAULT 0,
    consecutive_successes INTEGER NOT NULL DEFAULT 0,
    consecutive_failures  INTEGER NOT NULL DEFAULT 0,
    cooldown_until        REAL NOT NULL DEFAULT 0,
    last_http_status      INTEGER,
    last_elapsed          REAL,
    avg_elapsed           REAL,
    score                 REAL NOT NULL DEFAULT 0.0,
    quarantined_at        REAL,
    last_recovery         REAL,
    last_error            TEXT,
    avg_latency           REAL,
    recent_rate           REAL NOT NULL DEFAULT 0.5,
    recoveries            INTEGER NOT NULL DEFAULT 0,
    soft_streak           INTEGER NOT NULL DEFAULT 0,
    PRIMARY KEY (proxy_id, target_id),
    FOREIGN KEY (proxy_id) REFERENCES proxies(proxy_id) ON DELETE CASCADE
);
CREATE INDEX IF NOT EXISTS idx_pt_target_status ON proxy_target(target_id, status, cooldown_until);
CREATE INDEX IF NOT EXISTS idx_pt_eligible      ON proxy_target(target_id, cooldown_until, last_claimed);
CREATE INDEX IF NOT EXISTS idx_pt_score         ON proxy_target(target_id, score DESC);
CREATE INDEX IF NOT EXISTS idx_pt_proxy_claim   ON proxy_target(proxy_id, last_claimed);

CREATE TABLE IF NOT EXISTS test_history (
    id            INTEGER PRIMARY KEY AUTOINCREMENT,
    proxy_id      INTEGER NOT NULL,
    target_id     TEXT NOT NULL,
    ts            REAL NOT NULL,
    status        TEXT NOT NULL,
    failure_class TEXT,
    http_status   INTEGER,
    elapsed       REAL,
    error         TEXT,
    worker_id     INTEGER,
    browser_id    INTEGER,
    latency       REAL
);
CREATE INDEX IF NOT EXISTS idx_hist_proxy_target ON test_history(proxy_id, target_id, ts DESC);
CREATE INDEX IF NOT EXISTS idx_hist_ts           ON test_history(ts DESC);
"""

# Columns added by later versions; applied with ALTER TABLE on an existing DB.
_MIGRATIONS = [
    ("proxy_target", "avg_latency",       "REAL"),
    ("proxy_target", "recent_rate",       "REAL NOT NULL DEFAULT 0.5"),
    ("proxy_target", "recoveries",        "INTEGER NOT NULL DEFAULT 0"),
    ("proxy_target", "soft_streak",       "INTEGER NOT NULL DEFAULT 0"),
    ("test_history", "latency",           "REAL"),
    ("proxies",      "scheme_detected",   "TEXT"),
    ("proxies",      "preflight_status",  "TEXT NOT NULL DEFAULT 'UNKNOWN'"),
    ("proxies",      "preflight_until",   "REAL NOT NULL DEFAULT 0"),
    ("proxies",      "preflight_fails",   "INTEGER NOT NULL DEFAULT 0"),
    ("proxies",      "preflight_last",    "REAL"),
    ("proxies",      "preflight_latency", "REAL"),
    ("proxies",      "pf_claimed",        "REAL"),
]

# One derived status per proxy for reporting.  WORKING wins over everything; a
# proxy whose port is dead is reported as DEAD even if it has stale FAILED rows.
_GLOBAL_STATUS_SQL = """
UPDATE proxies SET
  global_status = CASE
    WHEN (SELECT COUNT(*) FROM proxy_target pt JOIN targets t ON t.target_id=pt.target_id AND t.enabled=1
          WHERE pt.proxy_id=proxies.proxy_id AND pt.status IN ('WORKING','RECOVERED')) > 0 THEN 'WORKING'
    WHEN proxies.preflight_status = 'DEAD' THEN 'DEAD'
    WHEN (SELECT COUNT(*) FROM proxy_target pt JOIN targets t ON t.target_id=pt.target_id AND t.enabled=1
          WHERE pt.proxy_id=proxies.proxy_id AND pt.status='RETRYABLE') > 0 THEN 'RETRYABLE'
    WHEN (SELECT COUNT(*) FROM proxy_target pt JOIN targets t ON t.target_id=pt.target_id AND t.enabled=1
          WHERE pt.proxy_id=proxies.proxy_id AND pt.status='QUARANTINED') > 0 THEN 'QUARANTINED'
    WHEN (SELECT COUNT(*) FROM proxy_target pt JOIN targets t ON t.target_id=pt.target_id AND t.enabled=1
          WHERE pt.proxy_id=proxies.proxy_id AND pt.status='FAILED') > 0 THEN 'FAILED'
    WHEN proxies.preflight_status = 'ALIVE' THEN 'PREFLIGHT_PASS'
    ELSE 'UNTESTED' END,
  global_score = COALESCE((
     SELECT AVG(pt.score) FROM proxy_target pt JOIN targets t ON t.target_id=pt.target_id AND t.enabled=1
     WHERE pt.proxy_id=proxies.proxy_id AND pt.status != 'UNTESTED'), 0.0)
"""


class Store:
    """All SQLite access. Every public method is async and hops to the DB thread."""

    def __init__(self, path: Path, readonly: bool = False) -> None:
        self.path = path
        self.readonly = readonly
        self._ex = ThreadPoolExecutor(max_workers=1, thread_name_prefix="db")
        if readonly:
            self._conn = sqlite3.connect(f"file:{path}?mode=ro", uri=True, check_same_thread=False,
                                         timeout=30.0, isolation_level=None)
            self._conn.row_factory = sqlite3.Row
            return
        self._conn = sqlite3.connect(str(path), check_same_thread=False, timeout=30.0,
                                     isolation_level=None)
        self._conn.row_factory = sqlite3.Row
        try:
            for pragma in ("journal_mode=WAL", "synchronous=NORMAL", "temp_store=MEMORY",
                           "foreign_keys=ON", "busy_timeout=30000", "wal_autocheckpoint=1000",
                           "cache_size=-32000"):
                self._conn.execute(f"PRAGMA {pragma}")
            qc = self._conn.execute("PRAGMA quick_check").fetchone()[0]
            if qc != "ok":
                raise sqlite3.DatabaseError(f"quick_check failed: {qc}")
            self._conn.executescript(SCHEMA)
            self._migrate()
        except Exception:
            with contextlib.suppress(Exception):
                self._conn.close()
            self._ex.shutdown(wait=False)
            raise

    # ---------------------------------------------------------------- lifecycle
    @classmethod
    def open_safely(cls, path: Path, readonly: bool = False) -> "Store":
        """Open the DB; on corruption, quarantine it and restore the newest good backup."""
        try:
            return cls(path, readonly=readonly)
        except sqlite3.DatabaseError as exc:
            if readonly:
                raise
            elog.error("database unusable (%s) - starting recovery", exc)
            ts = time.strftime("%Y%m%d_%H%M%S")
            for suffix in ("", "-wal", "-shm"):
                p = Path(str(path) + suffix)
                if p.exists():
                    p.rename(Path(str(path) + f".corrupt-{ts}{suffix}"))
            for b in sorted(BACKUP_DIR.glob("proxy_state_*.db"), reverse=True):
                try:
                    shutil.copy2(b, path)
                    st = cls(path)
                    rlog.warning("database restored from backup %s", b.name)
                    return st
                except Exception as exc2:
                    elog.error("backup %s unusable: %s", b.name, exc2)
                    for suffix in ("", "-wal", "-shm"):
                        with contextlib.suppress(OSError):
                            Path(str(path) + suffix).unlink()
            rlog.error("no usable backup; created a fresh database (proxy files are re-ingested)")
            return cls(path)

    def _migrate(self) -> None:
        c = self._conn
        ver = c.execute("PRAGMA user_version").fetchone()[0]
        added = []
        for table, col, ddl in _MIGRATIONS:
            cols = {r[1] for r in c.execute(f"PRAGMA table_info({table})")}
            if col not in cols:
                c.execute(f"ALTER TABLE {table} ADD COLUMN {col} {ddl}")
                added.append(f"{table}.{col}")
        if ver >= SCHEMA_VERSION:
            return
        with self._tx() as t:
            if added:
                t.execute("UPDATE proxy_target SET recent_rate = CASE WHEN success_count+failure_count>0 "
                          "THEN 1.0*success_count/(success_count+failure_count) ELSE 0.5 END "
                          "WHERE recent_rate IS NULL")
                t.execute("UPDATE proxy_target SET last_claimed = NULL")
            if ver < 4:
                # v3 kept preflight verdicts in proxy_target; lift them onto the proxy.
                t.execute("UPDATE proxies SET preflight_status='ALIVE', preflight_until=0 "
                          "WHERE proxy_id IN (SELECT proxy_id FROM proxy_target "
                          "WHERE status IN ('WORKING','RECOVERED','PREFLIGHT_PASS'))")
                t.execute("UPDATE proxies SET preflight_status='DEAD', preflight_fails=1, "
                          "preflight_until=0 WHERE preflight_status='UNKNOWN' AND proxy_id IN "
                          "(SELECT proxy_id FROM proxy_target WHERE failure_class='TCP_PREFLIGHT')")
                # PREFLIGHT_PASS is no longer a proxy_target status.
                t.execute("UPDATE proxy_target SET status='UNTESTED', failure_class=NULL, "
                          "cooldown_until=0 WHERE status='PREFLIGHT_PASS'")
                t.execute("UPDATE proxy_target SET status='UNTESTED', failure_class=NULL, "
                          "cooldown_until=0, consecutive_failures=0 "
                          "WHERE status='FAILED' AND failure_class='TCP_PREFLIGHT'")
            rows = t.execute("SELECT proxy_id, target_id, success_count, failure_count, recent_rate, "
                             "avg_latency, consecutive_successes, consecutive_failures, recoveries "
                             "FROM proxy_target WHERE success_count+failure_count>0").fetchall()
            for r in rows:
                t.execute("UPDATE proxy_target SET score=? WHERE proxy_id=? AND target_id=?",
                          (compute_score(r["success_count"], r["failure_count"], r["recent_rate"],
                                         r["avg_latency"], r["consecutive_successes"],
                                         r["consecutive_failures"], r["recoveries"]),
                           r["proxy_id"], r["target_id"]))
            t.execute(_GLOBAL_STATUS_SQL)
        c.execute(f"PRAGMA user_version = {SCHEMA_VERSION}")
        log.info("database migrated to schema v%d", SCHEMA_VERSION)

    @contextlib.contextmanager
    def _tx(self):
        self._conn.execute("BEGIN IMMEDIATE")
        try:
            yield self._conn
        except BaseException:
            with contextlib.suppress(Exception):
                self._conn.execute("ROLLBACK")
            raise
        else:
            self._conn.execute("COMMIT")

    async def _run(self, fn, *a):
        loop = asyncio.get_running_loop()
        return await loop.run_in_executor(self._ex, lambda: fn(*a))

    # ---------------------------------------------------------------- targets
    def _sync_targets(self, targets: list[Target]) -> dict:
        now = time.time()
        with self._tx() as c:
            for t in targets:
                c.execute(
                    "INSERT INTO targets (target_id, url, enabled, added_at, config_json) VALUES (?,?,?,?,?) "
                    "ON CONFLICT(target_id) DO UPDATE SET url=excluded.url, enabled=excluded.enabled, "
                    "config_json=excluded.config_json",
                    (t.target_id, t.url, 1 if t.enabled else 0, now, json.dumps(asdict(t))))
            ids = [t.target_id for t in targets]
            if ids:
                q = ",".join("?" * len(ids))
                gone = c.execute(f"UPDATE targets SET enabled=0 WHERE enabled=1 AND target_id NOT IN ({q})",
                                 ids).rowcount
            else:
                gone = c.execute("UPDATE targets SET enabled=0 WHERE enabled=1").rowcount
            rows = self._backfill(c)
            c.execute(_GLOBAL_STATUS_SQL)
        return {"disabled_missing": gone, "rows_created": rows}

    @staticmethod
    def _backfill(c) -> int:
        """Create a proxy_target row for every (proxy, enabled target) combination."""
        return c.execute(
            "INSERT OR IGNORE INTO proxy_target (proxy_id, target_id, status, cooldown_until) "
            "SELECT p.proxy_id, t.target_id, 'UNTESTED', 0 FROM proxies p CROSS JOIN targets t "
            "WHERE t.enabled = 1").rowcount

    async def sync_targets(self, targets):
        return await self._run(self._sync_targets, targets)

    # ---------------------------------------------------------------- ingestion
    def _ingest(self, proxies: list[str]) -> dict:
        now = time.time()
        with self._tx() as c:
            before = c.execute("SELECT COUNT(*) FROM proxies").fetchone()[0]
            c.executemany("INSERT OR IGNORE INTO proxies (proxy, first_seen, last_seen) VALUES (?,?,?)",
                          [(p, now, now) for p in proxies])
            after = c.execute("SELECT COUNT(*) FROM proxies").fetchone()[0]
            c.executemany("UPDATE proxies SET last_seen=? WHERE proxy=?", [(now, p) for p in proxies])
            rows = self._backfill(c)
        inserted = after - before
        return {"inserted": inserted, "existing": len(proxies) - inserted, "rows_created": rows}

    async def ingest_proxies(self, proxies):
        if not proxies:
            return {"inserted": 0, "existing": 0, "rows_created": 0}
        return await self._run(self._ingest, proxies)

    # ---------------------------------------------------------------- claims
    def _reset_claims(self) -> int:
        with self._tx() as c:
            n = c.execute("UPDATE proxy_target SET last_claimed=NULL WHERE last_claimed IS NOT NULL").rowcount
            c.execute("UPDATE proxies SET pf_claimed=NULL WHERE pf_claimed IS NOT NULL")
            return n

    async def reset_claims(self):
        return await self._run(self._reset_claims)

    def _release_claims(self, pairs: list[tuple[int, str]]) -> None:
        if not pairs:
            return
        with self._tx() as c:
            c.executemany("UPDATE proxy_target SET last_claimed=NULL WHERE proxy_id=? AND target_id=?", pairs)

    async def release_claims(self, pairs):
        return await self._run(self._release_claims, pairs)

    # ---------------------------------------------------------------- preflight
    def _claim_preflight_batch(self, limit: int) -> list[tuple[int, str, str]]:
        """Proxy-level, not per target: one host is probed once, then rechecked on a timer."""
        now = time.time()
        sql = """
            SELECT proxy_id, proxy, COALESCE(scheme_detected, '') FROM proxies
            WHERE preflight_until <= :now
              AND (pf_claimed IS NULL OR :now - pf_claimed > :ct)
            ORDER BY CASE preflight_status WHEN 'UNKNOWN' THEN 0 WHEN 'ALIVE' THEN 1 ELSE 2 END,
                     preflight_until ASC, proxy_id ASC
            LIMIT :lim"""
        with self._tx() as c:
            rows = c.execute(sql, {"now": now, "ct": CFG.claim_timeout_seconds, "lim": limit}).fetchall()
            if rows:
                c.executemany("UPDATE proxies SET pf_claimed=? WHERE proxy_id=?",
                              [(now, r[0]) for r in rows])
        return [(r[0], r[1], r[2]) for r in rows]

    async def claim_preflight_batch(self, limit: int):
        return await self._run(self._claim_preflight_batch, limit)

    def _mark_preflight(self, pid: int, alive: bool, scheme: Optional[str], latency: Optional[float]):
        now = time.time()
        with self._tx() as c:
            if alive:
                c.execute("UPDATE proxies SET preflight_status='ALIVE', preflight_fails=0, "
                          "preflight_last=?, preflight_latency=?, preflight_until=?, pf_claimed=NULL, "
                          "scheme_detected=COALESCE(?, scheme_detected) WHERE proxy_id=?",
                          (now, latency, now + _jit(CFG.preflight_recheck_seconds), scheme, pid))
            else:
                row = c.execute("SELECT preflight_fails FROM proxies WHERE proxy_id=?", (pid,)).fetchone()
                fails = (row[0] if row else 0) + 1
                # Exponential back-off: a dead host is never re-probed aggressively and
                # never reaches Chromium at all.
                cool = min(CFG.preflight_dead_max_cooldown,
                           CFG.preflight_dead_base_cooldown * (2 ** min(fails - 1, 10)))
                c.execute("UPDATE proxies SET preflight_status='DEAD', preflight_fails=?, "
                          "preflight_last=?, preflight_until=?, pf_claimed=NULL WHERE proxy_id=?",
                          (fails, now, now + _jit(cool), pid))
            c.execute(_GLOBAL_STATUS_SQL + " WHERE proxy_id = ?", (pid,))

    async def mark_preflight(self, pid: int, alive: bool, scheme: Optional[str] = None,
                             latency: Optional[float] = None):
        return await self._run(self._mark_preflight, pid, alive, scheme, latency)

    # ---------------------------------------------------------------- browser claims
    def _claim_batch(self, target_id: str, limit: int, kind: str) -> list[tuple[int, str, str]]:
        """kind='fresh'  -> pairs never tested against this target (main pool)
           kind='retry'  -> pairs with a prior verdict whose cooldown expired (retry pool)

        Both require the proxy to be ALIVE, so a host that failed preflight can never
        consume a browser context.
        """
        if limit <= 0:
            return []
        now = time.time()
        if kind == "fresh":
            status_sql = "pt.status = 'UNTESTED'"
        else:
            status_sql = "pt.status IN ('RECOVERED','RETRYABLE','WORKING','QUARANTINED','FAILED')"
        cross = "" if CFG.cross_target_parallel else (
            " AND NOT EXISTS (SELECT 1 FROM proxy_target x WHERE x.proxy_id = pt.proxy_id "
            "AND x.target_id <> pt.target_id AND x.last_claimed IS NOT NULL "
            "AND :now - x.last_claimed < :ct)")
        sql = f"""
            SELECT p.proxy_id, p.proxy, COALESCE(p.scheme_detected, '')
            FROM proxy_target pt
            JOIN proxies p ON p.proxy_id = pt.proxy_id
            WHERE pt.target_id = :tid
              AND p.preflight_status = 'ALIVE'
              AND {status_sql}
              AND pt.cooldown_until <= :now
              AND (pt.last_claimed IS NULL OR :now - pt.last_claimed > :ct)
              AND (pt.last_tested IS NULL OR :now - pt.last_tested >= :gap)
              {cross}
            ORDER BY
              CASE pt.status WHEN 'UNTESTED' THEN 0 WHEN 'RECOVERED' THEN 1 WHEN 'RETRYABLE' THEN 2
                             WHEN 'WORKING' THEN 3 WHEN 'QUARANTINED' THEN 4 ELSE 5 END,
              pt.cooldown_until ASC,
              pt.score DESC,
              p.preflight_latency ASC,
              RANDOM()
            LIMIT :lim"""
        params = {"tid": target_id, "now": now, "ct": CFG.claim_timeout_seconds,
                  "gap": 0 if kind == "fresh" else CFG.min_retest_gap_seconds, "lim": limit}
        with self._tx() as c:
            rows = [(r[0], r[1], r[2]) for r in c.execute(sql, params).fetchall()]
            if rows:
                c.executemany("UPDATE proxy_target SET last_claimed=? WHERE proxy_id=? AND target_id=?",
                              [(now, pid, target_id) for pid, _, _ in rows])
        return rows

    async def claim_batch(self, target_id: str, limit: int, kind: str = "fresh"):
        return await self._run(self._claim_batch, target_id, limit, kind)

    # ---------------------------------------------------------------- record a result
    def _record(self, proxy_id: int, target_id: str, res, worker_id: int, browser_id: int,
                overrides: dict) -> tuple[str, bool]:
        now = time.time()
        with self._tx() as c:
            c.execute("INSERT OR IGNORE INTO proxy_target (proxy_id, target_id) VALUES (?,?)",
                      (proxy_id, target_id))
            row = c.execute("SELECT * FROM proxy_target WHERE proxy_id=? AND target_id=?",
                            (proxy_id, target_id)).fetchone()
            old = row["status"]
            s, f = row["success_count"], row["failure_count"]
            cs, cf = row["consecutive_successes"], row["consecutive_failures"]
            recent, rec_n, soft = row["recent_rate"], row["recoveries"], row["soft_streak"]
            avg_lat, avg_el = row["avg_latency"], row["avg_elapsed"]
            prior_success = s > 0                      # needed by the circuit breaker
            alpha = CFG.score_recent_alpha
            el = res.elapsed_seconds or 0.0
            err = (res.error or "")[:500]

            if res.status == "WORKING":
                s += 1; cs += 1; cf = 0; soft = 0
                recent = (1 - alpha) * recent + alpha
                if res.latency_seconds is not None:
                    avg_lat = res.latency_seconds if avg_lat is None else avg_lat * 0.7 + res.latency_seconds * 0.3
                avg_el = el if avg_el is None else avg_el * 0.7 + el * 0.3
                came_back = old in ("QUARANTINED", "FAILED")
                new_status = "RECOVERED" if came_back else "WORKING"
                cool = (cooldown_for(overrides, "recovered_probe_cooldown") if came_back
                        else cooldown_for(overrides, "working_cooldown"))
                if came_back:
                    rec_n += 1
                c.execute(
                    """UPDATE proxy_target SET status=?, failure_class='WORKING', last_tested=?, last_success=?,
                       success_count=?, consecutive_successes=?, consecutive_failures=0, cooldown_until=?,
                       last_http_status=?, last_elapsed=?, avg_elapsed=?, avg_latency=?, recent_rate=?,
                       recoveries=?, soft_streak=0, last_error=NULL, score=?, last_claimed=NULL,
                       last_recovery=CASE WHEN ? THEN ? ELSE last_recovery END
                       WHERE proxy_id=? AND target_id=?""",
                    (new_status, now, now, s, cs, now + _jit(cool), res.http_status, el, avg_el, avg_lat,
                     recent, rec_n, compute_score(s, f, recent, avg_lat, cs, cf, rec_n),
                     1 if came_back else 0, now, proxy_id, target_id))
            else:
                pol = CFG.failure_policy.get(res.status, {})
                # "soft" classes (browser crash, transient) do not advance the ladder
                # until they repeat - a Chromium hiccup must not condemn a good proxy.
                is_soft = bool(pol.get("soft")) and (soft + 1) < CFG.soft_max_streak
                if is_soft:
                    soft += 1
                    new_status = old
                    cool = max(cooldown_for(overrides, "soft_retry_cooldown"), CFG.min_retest_gap_seconds)
                    c.execute(
                        """UPDATE proxy_target SET failure_class=?, last_tested=?, cooldown_until=?,
                           last_http_status=?, last_elapsed=?, last_error=?, soft_streak=?, last_claimed=NULL
                           WHERE proxy_id=? AND target_id=?""",
                        (res.status, now, now + _jit(cool), res.http_status, el, err, soft,
                         proxy_id, target_id))
                else:
                    f += 1; cf += 1; cs = 0; soft = 0
                    recent = (1 - alpha) * recent
                    new_status, base = failure_ladder(cf, overrides)
                    cool = max(base * float(pol.get("cooldown_mult", 1.0)),
                               cooldown_for(overrides, "soft_retry_cooldown"))
                    q_at = now if (new_status == "QUARANTINED" and old != "QUARANTINED") else None
                    c.execute(
                        """UPDATE proxy_target SET status=?, failure_class=?, last_tested=?, last_failure=?,
                           failure_count=?, consecutive_failures=?, consecutive_successes=0, cooldown_until=?,
                           last_http_status=?, last_elapsed=?, last_error=?, recent_rate=?, soft_streak=0,
                           score=?, last_claimed=NULL, quarantined_at=COALESCE(?, quarantined_at)
                           WHERE proxy_id=? AND target_id=?""",
                        (new_status, res.status, now, now, f, cf, now + _jit(cool), res.http_status, el, err,
                         recent, compute_score(s, f, recent, avg_lat, cs, cf, rec_n), q_at,
                         proxy_id, target_id))

            c.execute(
                "INSERT INTO test_history (proxy_id, target_id, ts, status, failure_class, http_status, "
                "elapsed, error, worker_id, browser_id, latency) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                (proxy_id, target_id, now, res.status, res.status, res.http_status, res.elapsed_seconds,
                 err, worker_id, browser_id, res.latency_seconds))
            # A hard transport failure in the browser also invalidates the preflight verdict.
            if res.status in ("TCP_FAILURE",):
                c.execute("UPDATE proxies SET preflight_status='UNKNOWN', preflight_until=? "
                          "WHERE proxy_id=? AND preflight_status='ALIVE'",
                          (now + _jit(CFG.preflight_dead_base_cooldown), proxy_id))
            c.execute(_GLOBAL_STATUS_SQL + " WHERE proxy_id = ?", (proxy_id,))
        return new_status, prior_success

    async def record(self, proxy_id, target_id, res, worker_id, browser_id, overrides):
        return await self._run(self._record, proxy_id, target_id, res, worker_id, browser_id, overrides)

    # ---------------------------------------------------------------- forgiveness
    def _forgive(self, pairs: list[tuple[int, str]], cooldown: float) -> int:
        """Undo one failure per pair - used when the TARGET or our own network was at fault."""
        now = time.time()
        n = 0
        with self._tx() as c:
            for pid, tid in set(pairs):
                r = c.execute("SELECT status, consecutive_failures, failure_count, last_success, "
                              "success_count, avg_latency, recent_rate, recoveries, consecutive_successes "
                              "FROM proxy_target WHERE proxy_id=? AND target_id=?", (pid, tid)).fetchone()
                if not r or r["consecutive_failures"] <= 0 or \
                        r["status"] not in ("RETRYABLE", "QUARANTINED", "FAILED"):
                    continue
                cf = r["consecutive_failures"] - 1
                fc = max(0, r["failure_count"] - 1)
                if cf == 0:
                    status = "WORKING" if r["last_success"] else "UNTESTED"
                else:
                    status, _ = failure_ladder(cf, {})
                new_score = compute_score(r["success_count"], fc, r["recent_rate"], r["avg_latency"],
                                          r["consecutive_successes"], cf, r["recoveries"])
                c.execute(
                    "UPDATE proxy_target SET status=?, consecutive_failures=?, failure_count=?, "
                    "cooldown_until=?, last_error='forgiven: environment/target outage', "
                    "quarantined_at=CASE WHEN ?='QUARANTINED' THEN quarantined_at ELSE NULL END, score=? "
                    "WHERE proxy_id=? AND target_id=?",
                    (status, cf, fc, now + _jit(cooldown), status, new_score, pid, tid))
                n += 1
            if n:
                c.execute(_GLOBAL_STATUS_SQL)
        return n

    async def forgive(self, pairs, cooldown):
        return await self._run(self._forgive, pairs, cooldown)

    # ---------------------------------------------------------------- reporting
    def _stats(self) -> dict:
        c = self._conn
        now = time.time()
        out: dict = {"proxies_total": 0, "global": {}, "targets": {}, "in_flight": 0, "due": 0,
                     "preflight": {}, "pf_pending": 0, "schemes": {}}
        for r in c.execute("SELECT global_status, COUNT(*) FROM proxies GROUP BY global_status"):
            out["global"][r[0]] = r[1]
        out["proxies_total"] = sum(out["global"].values())
        for r in c.execute("SELECT preflight_status, COUNT(*) FROM proxies GROUP BY preflight_status"):
            out["preflight"][r[0]] = r[1]
        for r in c.execute("SELECT COALESCE(scheme_detected,'?'), COUNT(*) FROM proxies "
                           "WHERE preflight_status='ALIVE' GROUP BY 1"):
            out["schemes"][r[0]] = r[1]
        out["pf_pending"] = c.execute(
            "SELECT COUNT(*) FROM proxies WHERE preflight_until <= ? "
            "AND (pf_claimed IS NULL OR ? - pf_claimed > ?)",
            (now, now, CFG.claim_timeout_seconds)).fetchone()[0]
        for r in c.execute(
                "SELECT t.target_id, pt.status, COUNT(*) FROM proxy_target pt JOIN targets t "
                "ON t.target_id = pt.target_id WHERE t.enabled = 1 GROUP BY t.target_id, pt.status"):
            out["targets"].setdefault(r[0], {})[r[1]] = r[2]
        out["in_flight"] = c.execute(
            "SELECT COUNT(*) FROM proxy_target pt JOIN targets t ON t.target_id=pt.target_id "
            "WHERE t.enabled=1 AND pt.last_claimed IS NOT NULL AND ? - pt.last_claimed < ?",
            (now, CFG.claim_timeout_seconds)).fetchone()[0]
        out["due"] = c.execute(
            "SELECT COUNT(*) FROM proxy_target pt JOIN targets t ON t.target_id=pt.target_id "
            "JOIN proxies p ON p.proxy_id=pt.proxy_id "
            "WHERE t.enabled=1 AND p.preflight_status='ALIVE' AND pt.cooldown_until <= ? "
            "AND (pt.last_claimed IS NULL OR ? - pt.last_claimed >= ?)",
            (now, now, CFG.claim_timeout_seconds)).fetchone()[0]
        return out

    async def stats(self):
        return await self._run(self._stats)

    def _failure_breakdown(self, hours: float) -> list[tuple[str, int]]:
        since = time.time() - hours * 3600
        return [(r[0] or "?", r[1]) for r in self._conn.execute(
            "SELECT status, COUNT(*) FROM test_history WHERE ts >= ? GROUP BY status "
            "ORDER BY 2 DESC", (since,))]

    async def failure_breakdown(self, hours: float = 24.0):
        return await self._run(self._failure_breakdown, hours)

    def _recent_errors(self, limit: int) -> list[dict]:
        rows = self._conn.execute(
            "SELECT h.ts, h.status, h.error, h.target_id, p.proxy FROM test_history h "
            "JOIN proxies p ON p.proxy_id = h.proxy_id WHERE h.status != 'WORKING' "
            "ORDER BY h.ts DESC LIMIT ?", (limit,)).fetchall()
        return [{"ts": r[0], "status": r[1], "error": (r[2] or "")[:160],
                 "target": r[3], "proxy": mask_proxy(r[4])} for r in rows]

    async def recent_errors(self, limit: int = 8):
        return await self._run(self._recent_errors, limit)

    def _top_proxies(self, limit: int) -> list[dict]:
        rows = self._conn.execute(
            "SELECT p.proxy, COALESCE(p.scheme_detected,'?'), p.global_score, "
            "       MAX(pt.last_success), SUM(pt.success_count), SUM(pt.failure_count), AVG(pt.avg_latency) "
            "FROM proxies p JOIN proxy_target pt ON pt.proxy_id = p.proxy_id "
            "WHERE p.global_status='WORKING' GROUP BY p.proxy_id "
            "ORDER BY p.global_score DESC LIMIT ?", (limit,)).fetchall()
        return [{"proxy": mask_proxy(r[0]), "scheme": r[1], "score": round(r[2] or 0, 3),
                 "last_success": r[3], "ok": r[4] or 0, "bad": r[5] or 0,
                 "latency": round(r[6], 2) if r[6] else None} for r in rows]

    async def top_proxies(self, limit: int = 10):
        return await self._run(self._top_proxies, limit)

    def _resume_summary(self) -> dict:
        now = time.time()
        out = {"by_status": {}, "due_now": 0, "cooling": 0}
        for r in self._conn.execute(
                "SELECT pt.status, COUNT(*), SUM(CASE WHEN pt.cooldown_until <= ? THEN 1 ELSE 0 END) "
                "FROM proxy_target pt JOIN targets t ON t.target_id = pt.target_id WHERE t.enabled=1 "
                "GROUP BY pt.status", (now,)):
            out["by_status"][r[0]] = r[1]
            out["due_now"] += r[2] or 0
            out["cooling"] += r[1] - (r[2] or 0)
        return out

    async def resume_summary(self):
        return await self._run(self._resume_summary)

    # ---------------------------------------------------------------- output lists
    def _working_lists(self, mode: str, max_age: float) -> tuple[dict, list]:
        """Validated proxies, written back with the protocol preflight actually proved."""
        c = self._conn
        age_sql, params = "", []
        if max_age and max_age > 0:
            age_sql = " AND pt.last_success >= ?"
            params.append(time.time() - max_age)
        statuses = "'WORKING','RECOVERED'"
        per: dict[str, list[str]] = defaultdict(list)
        for r in c.execute(
                "SELECT t.target_id, p.proxy, COALESCE(p.scheme_detected,'') "
                "FROM proxy_target pt JOIN proxies p ON p.proxy_id=pt.proxy_id "
                "JOIN targets t ON t.target_id=pt.target_id WHERE t.enabled=1 "
                f"AND pt.status IN ({statuses}){age_sql} "
                "ORDER BY t.target_id, pt.score DESC, p.proxy", params):
            per[r[0]].append(apply_scheme(r[1], r[2] or None))
        n_targets = c.execute("SELECT COUNT(*) FROM targets WHERE enabled=1").fetchone()[0]
        need = max(n_targets, 1) if mode == "all" else 1
        flat = [apply_scheme(r[0], r[1] or None) for r in c.execute(
            "SELECT p.proxy, COALESCE(p.scheme_detected,'') FROM proxies p "
            "JOIN proxy_target pt ON pt.proxy_id=p.proxy_id "
            "JOIN targets t ON t.target_id=pt.target_id WHERE t.enabled=1 "
            f"AND pt.status IN ({statuses}){age_sql} "
            "GROUP BY p.proxy_id HAVING COUNT(*) >= ? ORDER BY AVG(pt.score) DESC, p.proxy",
            params + [need])]
        if CFG.output_include_preflight:
            # Port-open-only proxies are clearly separated, never mixed into the main list.
            pf = [apply_scheme(r[0], r[1] or None) for r in c.execute(
                "SELECT proxy, COALESCE(scheme_detected,'') FROM proxies "
                "WHERE preflight_status='ALIVE' AND global_status='PREFLIGHT_PASS' "
                "ORDER BY preflight_latency ASC LIMIT 5000")]
            per["_preflight_only"] = pf
        return dict(per), flat

    async def working_lists(self, mode: str, max_age: float):
        return await self._run(self._working_lists, mode, max_age)

    def _export_working_text(self, limit: int) -> str:
        rows = self._conn.execute(
            "SELECT p.proxy, COALESCE(p.scheme_detected,'') FROM proxies p "
            "WHERE p.global_status='WORKING' ORDER BY p.global_score DESC LIMIT ?", (limit,)).fetchall()
        return "\n".join(apply_scheme(r[0], r[1] or None) for r in rows)

    async def export_working_text(self, limit: int = 20000):
        return await self._run(self._export_working_text, limit)

    # ---------------------------------------------------------------- maintenance
    def _prune_history(self, days: float) -> int:
        with self._tx() as c:
            return c.execute("DELETE FROM test_history WHERE ts < ?",
                             (time.time() - days * 86_400,)).rowcount

    async def prune_history(self, days):
        return await self._run(self._prune_history, days)

    def _purge_dead(self, days: float, min_fails: int) -> int:
        """Drop hosts that have been dead for a while.  Without this the 40k proxifly
        list accumulates forever and every maintenance pass gets slower."""
        if days <= 0:
            return 0
        cutoff = time.time() - days * 86_400
        with self._tx() as c:
            n = c.execute(
                "DELETE FROM proxies WHERE preflight_status='DEAD' AND preflight_fails >= ? "
                "AND COALESCE(preflight_last, 0) < ? AND proxy_id NOT IN "
                "(SELECT proxy_id FROM proxy_target WHERE success_count > 0)",
                (min_fails, cutoff)).rowcount
            if n:
                c.execute("DELETE FROM proxy_target WHERE proxy_id NOT IN (SELECT proxy_id FROM proxies)")
                c.execute("DELETE FROM test_history WHERE proxy_id NOT IN (SELECT proxy_id FROM proxies)")
            return n

    async def purge_dead(self, days: float, min_fails: int):
        return await self._run(self._purge_dead, days, min_fails)

    def _reset_states(self, scope: str) -> int:
        """scope: 'failed' | 'quarantined' | 'preflight' | 'all'."""
        now = time.time()
        with self._tx() as c:
            if scope == "preflight":
                n = c.execute("UPDATE proxies SET preflight_status='UNKNOWN', preflight_fails=0, "
                              "preflight_until=0, pf_claimed=NULL").rowcount
            elif scope == "all":
                n = c.execute("UPDATE proxy_target SET status='UNTESTED', failure_class=NULL, "
                              "cooldown_until=0, consecutive_failures=0, soft_streak=0, "
                              "last_claimed=NULL").rowcount
            else:
                want = "FAILED" if scope == "failed" else "QUARANTINED"
                n = c.execute("UPDATE proxy_target SET status='UNTESTED', failure_class=NULL, "
                              "cooldown_until=0, consecutive_failures=0, soft_streak=0, last_claimed=NULL "
                              "WHERE status=?", (want,)).rowcount
            c.execute(_GLOBAL_STATUS_SQL)
            c.execute("INSERT OR REPLACE INTO meta (key, value) VALUES ('last_reset', ?)", (str(now),))
            return n

    async def reset_states(self, scope: str):
        return await self._run(self._reset_states, scope)

    def _checkpoint(self) -> None:
        self._conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")

    async def checkpoint(self):
        return await self._run(self._checkpoint)

    def _integrity(self) -> str:
        return self._conn.execute("PRAGMA quick_check").fetchone()[0]

    async def integrity(self):
        return await self._run(self._integrity)

    def _backup(self, dest_dir: Path, keep: int) -> Path:
        dest_dir.mkdir(parents=True, exist_ok=True)
        name = f"proxy_state_{time.strftime('%Y%m%d_%H%M%S')}.db"
        tmp, final = dest_dir / (name + ".tmp"), dest_dir / name
        dst = sqlite3.connect(str(tmp))
        try:
            self._conn.backup(dst)
        finally:
            dst.close()
        os.replace(tmp, final)
        for old in sorted(dest_dir.glob("proxy_state_*.db"))[:-max(1, keep)]:
            with contextlib.suppress(OSError):
                old.unlink()
        return final

    async def backup(self, dest_dir: Path, keep: int):
        return await self._run(self._backup, dest_dir, keep)

    def _export_state(self, mask: bool = False) -> dict:
        c = self._conn
        m = mask_proxy if mask else (lambda x: x)
        proxies = [m(r[0]) for r in c.execute("SELECT proxy FROM proxies ORDER BY proxy_id")]
        rows = []
        for r in c.execute("SELECT p.proxy AS proxy, pt.* FROM proxy_target pt "
                           "JOIN proxies p ON p.proxy_id = pt.proxy_id ORDER BY p.proxy_id, pt.target_id"):
            d = dict(r)
            d["proxy"] = m(d["proxy"])
            rows.append(d)
        targets = [dict(r) for r in c.execute("SELECT target_id, url, enabled FROM targets")]
        return {"exported_at": time.time(), "version": VERSION, "targets": targets,
                "proxies": proxies, "proxy_target": rows}

    async def export_state(self, mask: bool = False):
        return await self._run(self._export_state, mask)

    def _mongo_snapshot(self, limit: int) -> dict:
        stats = self._stats()
        working = [{"proxy": mask_proxy(r[0]), "scheme": r[1] or None, "score": r[2]}
                   for r in self._conn.execute(
                       "SELECT proxy, scheme_detected, global_score FROM proxies "
                       "WHERE global_status='WORKING' ORDER BY global_score DESC LIMIT ?", (limit,))]
        return {"ts": time.time(), "version": VERSION, "stats": stats, "working": working}

    async def mongo_snapshot(self, limit: int = 5000):
        return await self._run(self._mongo_snapshot, limit)

    def _close(self) -> None:
        if not self.readonly:
            with contextlib.suppress(Exception):
                self._conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        with contextlib.suppress(Exception):
            self._conn.close()

    def close(self) -> None:
        try:
            self._ex.submit(self._close).result(timeout=15)
        except Exception:
            self._close()
        self._ex.shutdown(wait=True)


# ══════════════════════════════════════════════════════════════════════════════
#  CIRCUIT BREAKER
#  Per target.  If the TARGET (not the proxies) goes down, a whole batch of good
#  proxies would otherwise be demoted.  The breaker trips, pauses that target,
#  probes it cautiously, and hands back "forgiveness" for the wrongly-failed pairs.
# ══════════════════════════════════════════════════════════════════════════════
@dataclass
class _CB:
    state: str = "closed"                       # closed | open | half
    window: deque = field(default_factory=lambda: deque(maxlen=CFG.circuit_window))
    open_until: float = 0.0
    level: int = 0
    probes_issued: int = 0
    probe_results: list = field(default_factory=list)


class TargetCircuit:
    def __init__(self) -> None:
        self._cb: dict[str, _CB] = {}

    def _get(self, tid: str) -> _CB:
        if tid not in self._cb:
            self._cb[tid] = _CB()
        return self._cb[tid]

    @staticmethod
    def is_systemic(status: str, prior_success: bool) -> bool:
        """A failure that says more about the target/environment than about the proxy."""
        if status == "WORKING" or status in CFG.circuit_ignore_classes:
            return False
        if status in CFG.circuit_classes:
            return True
        return prior_success                     # a proxy that used to work now fails

    def blocked(self, tid: str) -> bool:
        cb = self._get(tid)
        return cb.state == "open" and time.time() < cb.open_until

    def reserve(self, tid: str, want: int) -> int:
        """How many tests the scheduler may issue for this target right now."""
        cb = self._get(tid)
        if cb.state == "open":
            if time.time() < cb.open_until:
                return 0
            cb.state, cb.probes_issued, cb.probe_results = "half", 0, []
        if cb.state == "half":
            n = max(0, min(want, CFG.circuit_probe_count - cb.probes_issued))
            cb.probes_issued += n
            return n
        return want

    def _open(self, cb: _CB) -> float:
        cooldown = min(CFG.circuit_cooldown * (2 ** cb.level), CFG.circuit_max_cooldown)
        cb.level += 1
        cb.state = "open"
        cb.open_until = time.time() + cooldown
        cb.window.clear()
        return cooldown

    def record(self, tid: str, pid: int, status: str, prior_success: bool) -> tuple[list, Optional[str]]:
        cb = self._get(tid)
        systemic = self.is_systemic(status, prior_success)
        if cb.state == "open":
            return ([(pid, tid)] if systemic else []), None
        if cb.state == "half":
            if status == "WORKING":
                cb.state, cb.level = "closed", 0
                cb.window.clear()
                return [], "closed"
            cb.probe_results.append("bad" if systemic else "neutral")
            forgive = [(pid, tid)] if systemic else []
            if len(cb.probe_results) >= CFG.circuit_probe_count:
                if "bad" in cb.probe_results:
                    self._open(cb)
                    return forgive, "reopened"
                cb.probes_issued, cb.probe_results = 0, []
            return forgive, None
        cb.window.append((pid, systemic))
        if len(cb.window) >= CFG.circuit_window:
            bad = [p for p, s in cb.window if s]
            if len(bad) / len(cb.window) >= CFG.circuit_block_ratio:
                forgive = [(p, tid) for p in bad]
                self._open(cb)
                rlog.warning("circuit breaker tripped for %s (%d/%d systemic failures)",
                             tid, len(bad), CFG.circuit_window)
                return forgive, "tripped"
        return [], None

    def state_dict(self) -> dict[str, str]:
        now = time.time()
        out = {}
        for tid, cb in self._cb.items():
            if cb.state == "open" and cb.open_until > now:
                out[tid] = f"OPEN {int(cb.open_until - now)}s"
            elif cb.state in ("open", "half"):
                out[tid] = "half-open"
            else:
                out[tid] = "closed"
        return out


async def probe_local_network() -> bool:
    """Is OUR connection alive?  Three well-known anycast endpoints, any one is enough."""
    async def one(hp: str) -> bool:
        host, _, port = hp.rpartition(":")
        return await _tcp_ok(host, int(port), CFG.net_probe_timeout)
    results = await asyncio.gather(*(one(h) for h in CFG.net_probe_hosts), return_exceptions=True)
    return any(r is True for r in results)


class NetGuard:
    """Detects a local outage and pauses testing, so a dropped Codespace network does
    not mass-condemn thousands of perfectly good proxies."""

    def __init__(self) -> None:
        self.window: deque = deque(maxlen=max(CFG.circuit_window, 20))
        self.down = False
        self.suspect = False
        self.was_down = False
        self._last_probe = 0.0

    def record(self, tid: str, pid: int, status: str) -> None:
        self.window.append((pid, tid, status in ("TCP_FAILURE", "CONNECTION_TIMEOUT")))
        ml = self.window.maxlen or 20
        if (not self.down and len(self.window) == ml
                and sum(1 for *_, f in self.window if f) / ml >= CFG.net_fail_ratio):
            self.suspect = True

    async def check(self) -> list:
        if not (self.suspect or self.down) or time.time() - self._last_probe < 5.0:
            return []
        self._last_probe = time.time()
        if await probe_local_network():
            if self.down:
                rlog.info("local network restored - testing resumes")
            self.down = self.suspect = False
            self.window.clear()
            return []
        newly = not self.down
        self.down, self.suspect = True, False
        if newly:
            self.was_down = True
            rlog.error("LOCAL NETWORK DOWN (all probe hosts unreachable) - testing paused")
            return [(p, t) for p, t, f in self.window if f]
        return []


# ══════════════════════════════════════════════════════════════════════════════
#  BROWSER FINGERPRINT PROFILES
#  UA, viewport, locale and timezone are generated together so they never
#  contradict each other (a macOS UA with a Linux screen size is a giveaway).
#  The UA always matches the real host OS and the real Chromium major version.
# ══════════════════════════════════════════════════════════════════════════════
_UA_TEMPLATES = {
    "Windows": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{v}.0.0.0 Safari/537.36",
    "macOS":   "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{v}.0.0.0 Safari/537.36",
    "Linux":   "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{v}.0.0.0 Safari/537.36",
}
_VIEWPORTS = {
    "Windows": [(1280, 720), (1366, 768), (1536, 864), (1920, 1080)],
    "macOS":   [(1440, 900), (1512, 982), (1728, 1117)],
    "Linux":   [(1280, 720), (1366, 768), (1600, 900), (1920, 1080)],
}
_LOCALES = [("en-US", "America/New_York"), ("en-US", "America/Chicago"),
            ("en-US", "America/Los_Angeles"), ("en-GB", "Europe/London")]

_REMOTE_UA_LIST: list[str] = []


def _host_os() -> str:
    if sys.platform.startswith("win"):
        return "Windows"
    return "macOS" if sys.platform == "darwin" else "Linux"


def make_profile(browser_version: str) -> dict:
    if CFG.custom_ua_profiles:
        p = random.choice(CFG.custom_ua_profiles)
        return {"ua": p["ua"],
                "viewport": {"width": int(p.get("width", 1366)), "height": int(p.get("height", 768))},
                "locale": p.get("locale", "en-US"), "tz": p.get("tz", "America/New_York")}
    if not CFG.ua_rotation:
        return {}
    m = re.match(r"(\d+)", browser_version or "")
    major = m.group(1) if m else "128"
    os_name = _host_os()
    if CFG.ua_pool_remote and _REMOTE_UA_LIST:
        ua_str = re.sub(r"Chrome/\d+", f"Chrome/{major}", random.choice(_REMOTE_UA_LIST))
    else:
        ua_str = _UA_TEMPLATES[os_name].format(v=major)
    w, h = random.choice(_VIEWPORTS[os_name])
    loc, tz = random.choice(_LOCALES)
    return {"ua": ua_str, "viewport": {"width": w, "height": h}, "locale": loc, "tz": tz}


# ══════════════════════════════════════════════════════════════════════════════
#  BROWSER POOL
#  A few long-lived Chromium processes, each lending out N isolated contexts.
#  Launching a browser per test would dominate the runtime; leaking them would
#  eat the 16 GB, so every browser is recycled after `browser_recycle_after` uses.
# ══════════════════════════════════════════════════════════════════════════════
@dataclass
class BrowserRec:
    bid: int
    browser: object
    active: int = 0
    uses: int = 0
    retiring: bool = False


class BrowserPool:
    def __init__(self, launcher) -> None:
        self._launcher = launcher
        self.slots: asyncio.Queue = asyncio.Queue()
        self.recs: dict[int, BrowserRec] = {}
        self._next = 0
        self._lock = asyncio.Lock()
        self._stopping = False
        self.restarts = 0

    async def _launch(self) -> Optional[BrowserRec]:
        try:
            b = await asyncio.wait_for(self._launcher(), timeout=90)
        except Exception as exc:
            elog.error("Chromium launch failed: %s", exc)
            return None
        self._next += 1
        rec = BrowserRec(self._next, b)
        self.recs[rec.bid] = rec
        for _ in range(CFG.contexts_per_browser):
            self.slots.put_nowait(rec.bid)
        return rec

    async def start(self) -> None:
        for _ in range(CFG.browser_count):
            await self._launch()

    async def ensure_capacity(self) -> None:
        async with self._lock:
            while not self._stopping and len(self.recs) < CFG.browser_count:
                if await self._launch() is None:
                    break

    async def _replace(self, bid: int) -> None:
        async with self._lock:
            rec = self.recs.pop(bid, None)
            if rec is None:
                return
            self.restarts += 1
            with contextlib.suppress(Exception):
                await asyncio.wait_for(rec.browser.close(), timeout=15)
            if not self._stopping:
                await self._launch()

    async def acquire(self, timeout: float = 30.0):
        end = time.monotonic() + timeout
        while not self._stopping:
            remaining = end - time.monotonic()
            if remaining <= 0:
                return None
            try:
                bid = await asyncio.wait_for(self.slots.get(), timeout=remaining)
            except asyncio.TimeoutError:
                return None
            rec = self.recs.get(bid)
            if rec is None or rec.retiring:
                continue
            if not rec.browser.is_connected():
                await self._replace(bid)
                continue
            rec.active += 1
            rec.uses += 1
            return bid, rec.browser
        return None

    async def release(self, bid: int, crashed: bool = False) -> None:
        rec = self.recs.get(bid)
        if rec is None:
            return
        rec.active = max(0, rec.active - 1)
        if crashed or not rec.browser.is_connected():
            await self._replace(bid)
            return
        if not rec.retiring and rec.uses >= CFG.browser_recycle_after:
            rec.retiring = True
        if rec.retiring:
            if rec.active == 0:
                await self._replace(bid)
            return
        self.slots.put_nowait(bid)

    def capacity(self) -> int:
        return len(self.recs) * CFG.contexts_per_browser

    async def close(self) -> None:
        self._stopping = True
        for rec in list(self.recs.values()):
            with contextlib.suppress(Exception):
                await asyncio.wait_for(rec.browser.close(), timeout=15)
        self.recs.clear()


# ══════════════════════════════════════════════════════════════════════════════
#  VALIDATION ENGINE
# ══════════════════════════════════════════════════════════════════════════════
@dataclass
class ValidationResult:
    status: str
    http_status: Optional[int] = None
    elapsed_seconds: Optional[float] = None
    latency_seconds: Optional[float] = None
    error: Optional[str] = None
    title: str = ""
    browser_crashed: bool = False
    final_url: str = ""
    redirected: bool = False


class StepError(Exception): ...
class BrowserCrashed(Exception): ...
class ConnectionLost(Exception): ...


async def run_interaction_steps(page, steps: list) -> None:
    """Scripted per-target interactions (wait / scroll / click / fill / ...).
    Steps are optional by default; mark one {"required": true} to fail the test."""
    for step in steps:
        action = step.get("action")
        required = bool(step.get("required", not step.get("optional", True)))
        try:
            if action == "wait":
                await page.wait_for_timeout(int(step.get("ms", 1000)))
            elif action == "scroll":
                for _ in range(int(step.get("count", 1))):
                    await page.mouse.wheel(0, int(step.get("dy", 400)))
                    await page.wait_for_timeout(int(step.get("pause_ms", 500)))
            elif action == "move_mouse":
                if "x" in step and "y" in step:
                    await page.mouse.move(int(step["x"]), int(step["y"]), steps=int(step.get("steps", 10)))
            elif action == "hover":
                await page.hover(step["selector"], timeout=step.get("timeout_ms", 5000))
            elif action == "click":
                await page.click(step["selector"], timeout=step.get("timeout_ms", 5000))
            elif action == "fill":
                await page.fill(step["selector"], step.get("value", ""), timeout=step.get("timeout_ms", 5000))
            elif action == "select":
                await page.select_option(step["selector"], step.get("value"), timeout=step.get("timeout_ms", 5000))
            elif action == "press":
                await page.keyboard.press(step["key"])
            elif action == "reload":
                await page.reload(wait_until="domcontentloaded", timeout=step.get("timeout_ms", 30_000))
            elif action == "wait_for":
                await page.wait_for_selector(step["selector"], timeout=step.get("timeout_ms", 10_000))
            elif action == "goto":
                await page.goto(step["url"], wait_until="domcontentloaded", timeout=step.get("timeout_ms", 30_000))
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            if required:
                raise StepError(f"required step {action} failed: {str(exc)[:200]}") from exc


async def human_behavior(page) -> None:
    """A small amount of pointer/scroll activity so the page's lazy content loads
    the way it would for a real visitor.  Best-effort; failures are ignored."""
    for _ in range(random.randint(1, 3)):
        try:
            x, y = random.randint(100, 800), random.randint(100, 800)
            await page.mouse.move(x, y, steps=random.randint(10, 30))
            await asyncio.sleep(random.uniform(0.1, 0.4))
            await page.mouse.wheel(0, random.randint(100, 500) * random.choice([1, -1]))
            await asyncio.sleep(random.uniform(0.2, 0.6))
        except Exception:
            return


# Chromium network errors -> our failure classes.  The class decides the cooldown
# and whether the circuit breaker treats the failure as systemic.
_NET_ERRORS = [
    (("ERR_PROXY_CONNECTION_FAILED", "ERR_CONNECTION_REFUSED", "ERR_SOCKS_CONNECTION_FAILED",
      "ERR_ADDRESS_UNREACHABLE", "ERR_SOCKS_CONNECTION_HOST_UNREACHABLE"), "TCP_FAILURE"),
    (("ERR_CONNECTION_TIMED_OUT", "ERR_TIMED_OUT", "ERR_CONNECTION_RESET", "ERR_CONNECTION_CLOSED"),
     "CONNECTION_TIMEOUT"),
    (("ERR_EMPTY_RESPONSE",), "EMPTY_RESPONSE"),
    (("ERR_TUNNEL_CONNECTION_FAILED", "ERR_PROXY_AUTH", "ERR_INVALID_AUTH", "ERR_NO_SUPPORTED_PROXIES",
      "ERR_HTTP_RESPONSE_CODE_FAILURE", "ERR_SSL", "ERR_CERT", "ERR_UNEXPECTED_PROXY_AUTH",
      "ERR_CERT_DATE_INVALID", "ERR_CERT_AUTHORITY_INVALID", "ERR_SSL_PROTOCOL_ERROR",
      "ERR_SSL_VERSION_OR_CIPHER_MISMATCH"), "HTTP_ERROR"),
    (("ERR_NAME_NOT_RESOLVED", "ERR_INTERNET_DISCONNECTED", "ERR_NETWORK_CHANGED", "ERR_ABORTED",
      "ERR_NETWORK_ACCESS_DENIED"), "RETRYABLE_ERROR"),
]
_CRASH_WORDS = ("target closed", "has been closed", "browser closed", "crashed", "connection closed",
                "browser has disconnected", "target page, context or browser")


def classify_playwright_error(exc: Exception) -> str:
    msg = str(exc)
    for needles, cat in _NET_ERRORS:
        if any(n in msg for n in needles):
            return cat
    low = msg.lower()
    if isinstance(exc, PlaywrightTimeout) or "timeout" in low:
        return "NAVIGATION_TIMEOUT" if ("goto" in low or "navigat" in low) else "RETRYABLE_ERROR"
    return "BROWSER_ERROR"


_STRIP_BLOCKS = re.compile(r"(?is)<(script|style|noscript)[^>]*>.*?</\1>")
_STRIP_TAGS = re.compile(r"(?s)<[^>]+>")

_STEALTH_JS = """
Object.defineProperty(navigator, 'webdriver', {get: () => undefined});
window.chrome = window.chrome || { runtime: {} };
Object.defineProperty(navigator, 'languages', {get: () => ['en-US', 'en']});
Object.defineProperty(navigator, 'plugins', {get: () => [1, 2, 3]});
"""


def _host_of(url: str) -> str:
    return (urlparse(url).hostname or "").lower().removeprefix("www.")


async def _inner_validate(browser, proxy: str, target: Target, profile: dict,
                          state_file: Optional[Path]) -> ValidationResult:
    t0 = time.monotonic()
    flags = {"crashed": False, "req_failed": 0}
    ctx = None
    latency: Optional[float] = None
    http_status: Optional[int] = None
    title = ""
    final_url = ""

    def elapsed() -> float:
        return round(time.monotonic() - t0, 2)

    try:
        kw: dict = {"proxy": build_proxy_config(proxy),
                    "ignore_https_errors": CFG.ignore_https_errors}
        referer = (target.referer or CFG.default_referer or "").strip()
        if referer:
            kw["extra_http_headers"] = {"Referer": referer}
        if profile:
            kw.update(user_agent=profile["ua"], viewport=profile["viewport"],
                      screen=profile["viewport"], locale=profile["locale"],
                      timezone_id=profile["tz"])
        if CFG.session_cache_enabled and state_file and state_file.exists():
            kw["storage_state"] = str(state_file)

        ctx = await browser.new_context(**kw)
        ctx.set_default_timeout(target.navigation_timeout_ms + random.randint(-2000, 5000))
        if CFG.enable_stealth_script:
            await ctx.add_init_script(_STEALTH_JS)

        page = await ctx.new_page()
        page.on("crash", lambda *_: flags.__setitem__("crashed", True))
        page.on("requestfailed", lambda *_: flags.__setitem__("req_failed", flags["req_failed"] + 1))

        t_nav = time.monotonic()
        response = await page.goto(target.url, wait_until="domcontentloaded")
        latency = round(time.monotonic() - t_nav, 2)
        http_status = response.status if response else None

        # ── RULE B (opt-in) ───────────────────────────────────────────────────
        # Some targets answer a valid request with a redirect to a per-session URL.
        # When `redirect_means_success` is set we accept that as the success signal
        # immediately, before any content rule runs.  It is OFF by default because a
        # proxy bounced to a captive portal, an ISP block page or a captcha also
        # redirects, and would otherwise be published as a working proxy.
        if target.redirect_means_success:
            settle = min(4.0, max(1.0, target.post_load_wait_seconds / 5.0))
            await page.wait_for_timeout(int(settle * 1000))
            final_url = page.url
            if final_url and final_url.rstrip("/") != target.url.rstrip("/") \
                    and not final_url.startswith("chrome-error://"):
                with contextlib.suppress(Exception):
                    title = await page.title()
                # Rule A still wins over Rule B: a redirect to a "proxy detected"
                # notice is a failure, not a success.
                probe = ""
                with contextlib.suppress(Exception):
                    probe = (await page.evaluate("() => document.body ? document.body.innerText : ''"))[:4000]
                if "proxy detect" in (title + " " + probe).lower():
                    return ValidationResult("TARGET_VALIDATION_FAILED", http_status, elapsed(), latency,
                                            "proxy detection triggered after redirect", title,
                                            final_url=final_url, redirected=True)
                
                # 30 second wait working  function
                await page.wait_for_timeout(30000) 
                
                return ValidationResult("WORKING", http_status, elapsed(), latency, None, title,
                                        final_url=final_url, redirected=True)

        if target.interaction_steps:
            await run_interaction_steps(page, target.interaction_steps)
        else:
            await human_behavior(page)

        if target.reload_after_load:
            await page.reload(wait_until="domcontentloaded")

        # Verification window: the page must still be alive when it ends.
        deadline = time.monotonic() + target.post_load_wait_seconds
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            await page.wait_for_timeout(int(min(remaining, CFG.stability_poll_seconds) * 1000))
            if flags["crashed"] or page.is_closed():
                raise BrowserCrashed("page crashed/closed during verification window")
            if page.url.startswith("chrome-error://"):
                raise ConnectionLost("connection lost during verification window")

        with contextlib.suppress(Exception):
            await page.wait_for_load_state("networkidle", timeout=CFG.network_idle_timeout_ms)
        with contextlib.suppress(Exception):
            title = await page.title()
        final_url = page.url

        visible = ""
        with contextlib.suppress(Exception):
            visible = await page.evaluate("() => document.body ? document.body.innerText : ''")
        html_src = ""
        need_html = (not visible.strip()) or any(m.startswith("html:") for m in target.forbidden_markers)
        if need_html:
            with contextlib.suppress(Exception):
                html_src = await page.content()
        if not visible.strip() and html_src:
            visible = _STRIP_TAGS.sub(" ", _STRIP_BLOCKS.sub(" ", html_src))
        visible = re.sub(r"\s+", " ", visible).strip()
        text = (title + " " + visible).lower()
        html_l = html_src.lower()
        el = elapsed()
        redirected = bool(final_url) and final_url.rstrip("/") != target.url.rstrip("/")

        def fail(cls: str, why: str) -> ValidationResult:
            return ValidationResult(cls, http_status, el, latency, why, title,
                                    final_url=final_url, redirected=redirected)

        # ── RULE A: hard proxy-detection catch, case-insensitive ──────────────
        # Matches "proxy detection", "proxy detected" and "anonymous proxy detected".
        if "proxy detect" in text:
            return fail("TARGET_VALIDATION_FAILED", "proxy detection triggered")

        final_host, target_host = _host_of(final_url), _host_of(target.url)
        if final_host and target_host and final_host != target_host and not target.allow_offsite_redirect:
            return fail("TARGET_VALIDATION_FAILED", f"redirected off-site to {final_host}")

        for marker in target.forbidden_markers:
            hit = (marker[5:] in html_l) if marker.startswith("html:") else (marker in text)
            if hit:
                return fail("TARGET_VALIDATION_FAILED", f"forbidden marker: {marker}")
        for sel in target.forbidden_selectors:
            with contextlib.suppress(Exception):
                if await page.locator(sel).count() > 0:
                    return fail("TARGET_VALIDATION_FAILED", f"forbidden selector: {sel}")
        if target.require_status_200 and http_status != 200:
            return fail("HTTP_ERROR", f"status {http_status}")
        if http_status is not None and http_status >= 400:
            return fail("HTTP_ERROR", f"status {http_status}")
        if len(visible) < target.min_body_length:
            return fail("EMPTY_RESPONSE", f"body {len(visible)} chars")
        if target.success_markers and not any(m in text for m in target.success_markers):
            return fail("TARGET_VALIDATION_FAILED", "no success marker")
        if target.title_contains and not any(m.lower() in title.lower() for m in target.title_contains):
            return fail("TARGET_VALIDATION_FAILED", "title mismatch")
        if target.success_selectors:
            found = []
            for sel in target.success_selectors:
                ok = False
                with contextlib.suppress(Exception):
                    ok = await page.locator(sel).count() > 0
                found.append(ok)
            good = all(found) if target.success_selectors_mode == "all" else any(found)
            if not good:
                return fail("TARGET_VALIDATION_FAILED", "expected element missing")

        if CFG.session_cache_enabled and state_file:
            with contextlib.suppress(Exception):
                await ctx.storage_state(path=str(state_file))

        return ValidationResult("WORKING", http_status, el, latency, None, title,
                                final_url=final_url, redirected=redirected)

    except asyncio.CancelledError:
        raise
    except StepError as exc:
        return ValidationResult("TARGET_VALIDATION_FAILED", http_status, elapsed(), latency,
                                str(exc)[:400], title, final_url=final_url)
    except BrowserCrashed as exc:
        return ValidationResult("BROWSER_ERROR", http_status, elapsed(), latency, str(exc), title,
                                True, final_url=final_url)
    except ConnectionLost as exc:
        return ValidationResult("CONNECTION_TIMEOUT", http_status, elapsed(), latency, str(exc), title,
                                final_url=final_url)
    except PlaywrightError as exc:
        cat = classify_playwright_error(exc)
        crashed = flags["crashed"] or (cat == "BROWSER_ERROR"
                                       and any(w in str(exc).lower() for w in _CRASH_WORDS))
        return ValidationResult(cat, http_status, elapsed(), latency,
                                str(exc).replace("\n", " ")[:400], title, crashed, final_url=final_url)
    except Exception as exc:
        return ValidationResult("RETRYABLE_ERROR", http_status, elapsed(), latency,
                                f"{type(exc).__name__}: {exc}"[:400], title, final_url=final_url)
    finally:
        if ctx is not None:
            with contextlib.suppress(Exception):
                await asyncio.wait_for(ctx.close(), timeout=10)


async def validate_proxy(browser, proxy: str, target: Target, profile: dict) -> ValidationResult:
    """Outer guard: no single test may ever hang a worker forever."""
    hard = (target.navigation_timeout_ms / 1000.0 * 2 + target.post_load_wait_seconds
            + CFG.hard_timeout_extra_seconds)
    t0 = time.monotonic()
    state_file = None
    if CFG.session_cache_enabled:
        h = hashlib.sha256(f"{proxy}|{target.target_id}".encode()).hexdigest()[:20]
        state_file = SESSIONS_DIR / f"{h}.json"
    try:
        return await asyncio.wait_for(_inner_validate(browser, proxy, target, profile, state_file),
                                      timeout=hard)
    except asyncio.TimeoutError:
        return ValidationResult("NAVIGATION_TIMEOUT", None, round(time.monotonic() - t0, 2), None,
                                f"hard timeout {int(hard)}s")


# ══════════════════════════════════════════════════════════════════════════════
#  HTTP HELPERS
#  One shared aiohttp session for every outbound call (fetching, uptime pings, UA
#  refresh).  Creating a session per request was wasteful and defeated keep-alive.
#  If aiohttp is missing we fall back to urllib in a thread, so nothing breaks.
# ══════════════════════════════════════════════════════════════════════════════
try:
    import aiohttp
    AIOHTTP_OK = True
except ImportError:
    aiohttp = None
    AIOHTTP_OK = False


class HttpClient:
    def __init__(self) -> None:
        self._session = None
        self._lock = asyncio.Lock()

    async def session(self):
        if not AIOHTTP_OK:
            return None
        async with self._lock:
            if self._session is None or self._session.closed:
                self._session = aiohttp.ClientSession(
                    timeout=aiohttp.ClientTimeout(total=60),
                    connector=aiohttp.TCPConnector(limit=32, ttl_dns_cache=300))
            return self._session

    async def get_text(self, url: str, timeout: float = 30.0) -> Optional[str]:
        sess = await self.session()
        if sess is not None:
            try:
                async with sess.get(url, timeout=aiohttp.ClientTimeout(total=timeout)) as r:
                    if r.status != 200:
                        return None
                    return await r.text(errors="ignore")
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                elog.warning("GET %s failed: %s", url.split("?")[0], type(exc).__name__)
                return None
        return await asyncio.to_thread(self._urllib_text, url, timeout)

    async def get_bytes(self, url: str, timeout: float = 45.0) -> Optional[bytes]:
        sess = await self.session()
        if sess is not None:
            try:
                async with sess.get(url, timeout=aiohttp.ClientTimeout(total=timeout)) as r:
                    if r.status != 200:
                        return None
                    return await r.read()
            except asyncio.CancelledError:
                raise
            except Exception:
                return None
        return await asyncio.to_thread(self._urllib_bytes, url, timeout)

    async def ping(self, url: str, timeout: float = 15.0) -> bool:
        sess = await self.session()
        if sess is not None:
            try:
                async with sess.get(url, timeout=aiohttp.ClientTimeout(total=timeout)) as r:
                    await r.read()
                    return r.status < 500
            except asyncio.CancelledError:
                raise
            except Exception:
                return False
        return await asyncio.to_thread(lambda: self._urllib_bytes(url, timeout) is not None)

    @staticmethod
    def _urllib_bytes(url: str, timeout: float) -> Optional[bytes]:
        try:
            req = urllib.request.Request(url, headers={"User-Agent": f"radiate/{VERSION}"})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read()
        except Exception:
            return None

    @classmethod
    def _urllib_text(cls, url: str, timeout: float) -> Optional[str]:
        data = cls._urllib_bytes(url, timeout)
        return data.decode("utf-8", errors="ignore") if data is not None else None

    async def close(self) -> None:
        if self._session is not None and not self._session.closed:
            with contextlib.suppress(Exception):
                await self._session.close()


HTTP = HttpClient()


# ══════════════════════════════════════════════════════════════════════════════
#  EXTERNAL PROXY FETCHING
# ══════════════════════════════════════════════════════════════════════════════
def parse_fallback_text(text: str) -> list[str]:
    """Parse any list format: bare ip:port, scheme://ip:port, or a table row."""
    out, seen = [], set()
    for raw in re.split(r"[\r\n]+", text):
        raw = raw.strip()
        if not raw or raw.startswith("#"):
            continue
        # Whole line first, so an explicit scheme and credentials survive; only if
        # that fails do we pull the proxy token out of a multi-column row.
        p = normalize_proxy(raw)
        if p is None:
            m = _PROXY_TOKEN_RE.search(raw)
            if m:
                p = normalize_proxy(m.group(0))
        if p and p not in seen:
            seen.add(p)
            out.append(p)
    return out


async def fetch_fallback_proxies(urls: list[str], timeout: float = 30.0) -> list[str]:
    out, seen = [], set()
    for url in urls:
        text = await HTTP.get_text(url, timeout=timeout)
        if not text:
            continue
        for p in parse_fallback_text(text):
            if p not in seen:
                seen.add(p)
                out.append(p)
    return out


# ══════════════════════════════════════════════════════════════════════════════
#  OPTIONAL MONGODB MIRROR
#  Purely additive: SQLite stays the source of truth.  Never fatal - if pymongo
#  is absent or the server is unreachable the daemon logs once and carries on.
# ══════════════════════════════════════════════════════════════════════════════
class MongoMirror:
    def __init__(self) -> None:
        self._client = None
        self._warned = False
        self.last_sync = 0.0
        self.last_error = ""

    def _connect(self):
        if self._client is not None:
            return self._client
        try:
            from pymongo import MongoClient
        except ImportError:
            if not self._warned:
                elog.warning("mongo_enabled but pymongo is not installed - mirror disabled")
                self._warned = True
            return None
        try:
            self._client = MongoClient(CFG.mongo_uri, serverSelectionTimeoutMS=5000)
            self._client.admin.command("ping")
            return self._client
        except Exception as exc:
            self.last_error = f"{type(exc).__name__}: {exc}"[:200]
            self._client = None
            return None

    def _push(self, snapshot: dict) -> bool:
        client = self._connect()
        if client is None:
            return False
        try:
            db = client[CFG.mongo_db]
            db.snapshots.insert_one({k: v for k, v in snapshot.items() if k != "working"})
            if snapshot.get("working"):
                db.working.delete_many({})
                db.working.insert_many(snapshot["working"])
            self.last_sync = time.time()
            self.last_error = ""
            return True
        except Exception as exc:
            self.last_error = f"{type(exc).__name__}: {exc}"[:200]
            self._client = None                       # force a reconnect next round
            return False

    async def sync(self, store: "Store") -> bool:
        if not (CFG.mongo_enabled and CFG.mongo_uri):
            return False
        snapshot = await store.mongo_snapshot()
        return await asyncio.to_thread(self._push, snapshot)

    def close(self) -> None:
        with contextlib.suppress(Exception):
            if self._client is not None:
                self._client.close()


MONGO = MongoMirror()


# ══════════════════════════════════════════════════════════════════════════════
#  RUNTIME  - everything the loops and the bot share
# ══════════════════════════════════════════════════════════════════════════════
class Runtime:
    def __init__(self, store: Store, pool: BrowserPool, registry: TargetRegistry,
                 circuit: TargetCircuit, netguard: NetGuard, stop_event: asyncio.Event) -> None:
        self.store = store
        self.pool = pool
        self.registry = registry
        self.circuit = circuit
        self.netguard = netguard
        self.stop_event = stop_event

        # queues: fresh tests, retries, and the cheap socket preflight
        self.queue: asyncio.Queue = asyncio.Queue(maxsize=max(CFG.worker_count + CFG.queue_extra, 8))
        self.retry_queue: asyncio.Queue = asyncio.Queue(
            maxsize=max(CFG.retry_worker_count + CFG.queue_extra, 8))
        self.preflight_queue: asyncio.Queue = asyncio.Queue(maxsize=CFG.preflight_worker_count * 2)

        # live counters (surfaced in Telegram, /stats and metrics.json)
        self.workers_alive = 0          # tasks spawned (a pool of MAX_*, throttled by *_limit)
        self.retry_workers_alive = 0
        self.workers_busy = 0           # tasks actually running a test right now
        self.retry_workers_busy = 0
        self.preflight_workers_alive = 0
        self.browser_version = ""
        self.restart_requested = False
        self.circuit_trips = 0
        self.worker_restarts = 0
        self.tests_done = 0
        self.tests_ok = 0
        self.preflight_done = 0
        self.preflight_alive = 0
        self.daemon_started = time.time()
        self._target_cursor = 0
        self._retry_cursor = 0
        self.fd_limit: Optional[int] = None

        # Telegram
        self.bot: Optional[Any] = None
        self.live_status_msg_id: Optional[int] = None
        self.live_status_chat_id: Optional[int] = None
        self._live_hash = ""
        self._live_unchanged = 0
        self._notify_seen: dict[str, float] = {}
        self.tasks: set = set()                       # keeps fire-and-forget tasks referenced

        # pause state (restored from config so it survives a restart)
        self.user_paused = bool(CFG.system_paused)
        self.pause_until = float(CFG.pause_until or 0.0)
        self.worker_limit = CFG.worker_count          # what the RAM autoscaler currently allows
        self.retry_limit = CFG.retry_worker_count

    # ---- pause helpers ------------------------------------------------------
    @property
    def paused(self) -> bool:
        """Paused by the operator, by a timer that has not expired, or by a network outage."""
        if self.netguard.down:
            return True
        if not self.user_paused:
            return False
        if self.pause_until and time.time() >= self.pause_until:
            self.user_paused = False
            self.pause_until = 0.0
            self.persist_pause()
            log.info("timed pause expired - resuming")
            return False
        return True

    def set_pause(self, paused: bool, seconds: float = 0.0) -> None:
        self.user_paused = paused
        self.pause_until = (time.time() + seconds) if (paused and seconds > 0) else 0.0
        self.persist_pause()

    def persist_pause(self) -> None:
        CFG.system_paused = self.user_paused
        CFG.pause_until = self.pause_until
        with contextlib.suppress(Exception):
            save_config(CFG)

    def pause_text(self) -> str:
        if self.netguard.down:
            return "network outage"
        if not self.user_paused:
            return "running"
        if self.pause_until:
            return f"paused ({human_seconds(self.pause_until - time.time())} left)"
        return "paused"

    def track(self, coro) -> asyncio.Task:
        """Fire-and-forget with a strong reference, so the task is never GC'd mid-flight."""
        task = asyncio.create_task(coro)
        self.tasks.add(task)
        task.add_done_callback(self.tasks.discard)
        return task


async def _sleep_or_stop(rt: Runtime, seconds: float) -> None:
    """Sleep, but wake immediately when the daemon is asked to stop."""
    with contextlib.suppress(asyncio.TimeoutError):
        await asyncio.wait_for(rt.stop_event.wait(), timeout=seconds)


# ══════════════════════════════════════════════════════════════════════════════
#  TELEGRAM CONTROL PANEL (Aiogram 3.x)
#  Design rules:
#    * HTML parse mode, and EVERY dynamic value goes through _h() - a proxy string
#      or an error message with a stray '<' must never break a message.
#    * One long-lived "Live Status" message that is edited, never re-sent, and only
#      when the rendered text actually changed.
#    * Fail-closed authorisation: an unknown user gets nothing, not even an error.
#    * Destructive actions (stop, restart, purge, reset) go through a confirm step.
# ══════════════════════════════════════════════════════════════════════════════
router = Router()

MAX_UPLOAD_BYTES = 8 * 1024 * 1024
TG_LIMIT = 3900                                   # leave headroom under Telegram's 4096


def _h(x: Any) -> str:
    """Escape a dynamic value for HTML parse mode."""
    return html.escape(str(x), quote=False)


def _clip(text: str, limit: int = TG_LIMIT) -> str:
    return text if len(text) <= limit else text[:limit - 20] + "\n… (truncated)"


def _valid_http_url(u: str) -> bool:
    try:
        p = urlparse(u)
    except ValueError:
        return False
    return p.scheme in ("http", "https") and bool(p.netloc)


def _allowed_user_ids() -> set:
    """Telegram user ids allowed to drive the bot.

    telegram_chat_id counts only when it is a private chat (a positive id equals the
    user id).  A group id (negative) still receives alerts but cannot control anything:
    list the operators in telegram_admin_ids instead.
    """
    ids = {str(x).strip() for x in (CFG.telegram_admin_ids or []) if str(x).strip()}
    cid = str(CFG.telegram_chat_id).strip()
    if cid and not cid.startswith("-"):
        ids.add(cid)
    return ids


class AuthMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data):
        user = getattr(event, "from_user", None)
        if user is not None and str(user.id) in _allowed_user_ids():
            return await handler(event, data)
        elog.warning("telegram: blocked unauthorised access from user id=%s", getattr(user, "id", None))
        if AIOGRAM_OK and CallbackQuery is not None and isinstance(event, CallbackQuery):
            with contextlib.suppress(Exception):
                await event.answer("Not authorised.", show_alert=True)
        return None


router.message.outer_middleware(AuthMiddleware())
router.callback_query.outer_middleware(AuthMiddleware())


class BotStates(StatesGroup):
    waiting_for_target = State()
    waiting_for_uptime = State()
    waiting_for_source = State()
    waiting_for_setting = State()
    waiting_for_vip = State()
    waiting_for_rename = State()
    waiting_for_ua = State()


# ── settings that are safe to edit live from the phone ────────────────────────
# (key, label, kind, min, max).  kind: int | float | bool | str
SETTINGS_SCHEMA: dict[str, list[tuple]] = {
    "speed": [
        ("worker_count", "Fresh workers", "int", 1, MAX_MAIN_WORKERS),
        ("retry_worker_count", "Retry workers", "int", 0, MAX_RETRY_WORKERS),
        ("preflight_worker_count", "Preflight sockets", "int", 8, MAX_PREFLIGHT_WORKERS),
        ("batch_size_per_tick", "Batch per tick", "int", 1, 500),
        ("browser_count", "Chromium processes", "int", 1, 8),
        ("contexts_per_browser", "Contexts per browser", "int", 1, 12),
        ("auto_tune", "Auto-tune to hardware", "bool", 0, 1),
    ],
    "timing": [
        ("tcp_preflight_timeout", "TCP timeout (s)", "float", 0.2, 10),
        ("handshake_timeout", "Handshake timeout (s)", "float", 0.5, 15),
        ("post_load_wait_seconds", "Post-load wait (s)", "float", 0, 300),
        ("navigation_timeout_ms", "Navigation timeout (ms)", "int", 5000, 180000),
        ("min_retest_gap_seconds", "Min retest gap (s)", "float", 0, 86400),
        ("scheduler_tick_seconds", "Scheduler tick (s)", "float", 1, 120),
    ],
    "preflight": [
        ("handshake_probe_enabled", "Stage-2 handshake", "bool", 0, 1),
        ("probe_protocols", "Protocol auto-detect", "bool", 0, 1),
        ("probe_connect_host", "Probe host (IP)", "str", 0, 0),
        ("probe_connect_port", "Probe port", "int", 1, 65535),
        ("preflight_recheck_seconds", "Recheck alive (s)", "float", 300, 604800),
        ("purge_dead_after_days", "Purge dead after (days)", "float", 0, 365),
    ],
    "cooldowns": [
        ("working_cooldown", "Working recheck (s)", "float", 60, 604800),
        ("retryable_cooldown", "Retryable (s)", "float", 30, 604800),
        ("failed_cooldown", "Failed (s)", "float", 60, 604800),
        ("retryable_attempts", "Retries before quarantine", "int", 0, 10),
        ("cooldown_jitter", "Cooldown jitter", "float", 0, 0.5),
    ],
    "output": [
        ("output_mode", "Mode (any/all)", "str", 0, 0),
        ("output_include_preflight", "Include preflight-only", "bool", 0, 1),
        ("output_flush_interval", "Flush interval (s)", "float", 5, 3600),
        ("history_retention_days", "History retention (days)", "float", 1, 365),
    ],
    "telegram": [
        ("live_status_interval", "Live refresh (s)", "float", 3, 60),
        ("live_status_idle_interval", "Idle refresh (s)", "float", 5, 300),
        ("notify_dedupe_seconds", "Alert dedupe (s)", "float", 0, 86400),
        ("uptimerobot_interval_seconds", "Uptime ping (s)", "float", 60, 3600),
    ],
    "network": [
        ("fallback_min_working", "Auto-fetch below N working", "int", 0, 100000),
        ("fallback_cooldown_seconds", "Auto-fetch cooldown (s)", "float", 60, 86400),
        ("fetch_on_start", "Fetch at boot", "bool", 0, 1),
        ("http_api_enabled", "HTTP endpoint", "bool", 0, 1),
        ("http_api_host", "HTTP bind host", "str", 0, 0),
        ("http_api_port", "HTTP port", "int", 1, 65535),
    ],
    "mongo": [
        ("mongo_enabled", "Mongo mirror", "bool", 0, 1),
        ("mongo_uri", "Mongo URI", "str", 0, 0),
        ("mongo_db", "Mongo database", "str", 0, 0),
        ("mongo_sync_interval_seconds", "Sync interval (s)", "float", 30, 86400),
    ],
}
_SETTING_INDEX = {k: (cat, label, kind, lo, hi)
                  for cat, items in SETTINGS_SCHEMA.items()
                  for (k, label, kind, lo, hi) in items}
# Changing these needs a restart to take effect; the bot says so after saving.
_RESTART_KEYS = {"browser_count", "contexts_per_browser", "preflight_worker_count",
                 "http_api_enabled", "http_api_host", "http_api_port"}


# ── keyboards ─────────────────────────────────────────────────────────────────
def _kb(rows: list[list[tuple[str, str]]]):
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=t, callback_data=d) for t, d in row] for row in rows])


def main_kb():
    return _kb([
        [("📊 Live Status", "btn_status"), ("🔗 Targets", "btn_targets")],
        [("🔄 Force Fetch", "btn_fetch"), ("➕ Add Proxies", "btn_add_proxies")],
        [("⚙️ System", "btn_manage"), ("🧪 VIP Check", "btn_vip")],
        [("📈 Telemetry", "btn_telemetry"), ("🗂 Proxies", "btn_proxies")],
        [("💻 Codespace", "btn_codespace"), ("🛠 Settings", "btn_settings")],
    ])


def manage_kb(rt: "Runtime"):
    pause_lbl = "▶️ Resume" if rt.user_paused else "⏸️ Pause"
    return _kb([
        [(pause_lbl, "sys_resume" if rt.user_paused else "btn_pause"), ("⏱️ Uptime URL", "sys_uptime")],
        [("🔼 Speed Up", "sys_speed_up"), ("🔽 Speed Down", "sys_speed_down")],
        [("⚡ Speed Presets", "btn_speed"), ("🧬 User-Agent", "btn_ua")],
        [("📡 Sources", "btn_sources"), ("🌐 Public URL", "sys_public")],
        [("🔁 Restart Daemon", "ask_restart"), ("🛑 Force Stop", "ask_stop")],
        [("⬅️ Back", "btn_back")],
    ])


def pause_kb():
    return _kb([
        [("15 min", "pause_900"), ("1 hour", "pause_3600")],
        [("6 hours", "pause_21600"), ("Until I resume", "pause_0")],
        [("⬅️ Back", "btn_manage")],
    ])


def speed_kb():
    return _kb([
        [("🐢 Eco", "speed_eco"), ("⚖️ Normal", "speed_normal")],
        [("🚀 Turbo", "speed_turbo"), ("🤖 Auto-tune", "speed_auto")],
        [("⬅️ Back", "btn_manage")],
    ])


def ua_kb():
    return _kb([
        [(f"Rotation: {'ON' if CFG.ua_rotation else 'OFF'}", "ua_toggle_rot")],
        [(f"Remote pool: {'ON' if CFG.ua_pool_remote else 'OFF'}", "ua_toggle_remote")],
        [(f"Stealth script: {'ON' if CFG.enable_stealth_script else 'OFF'}", "ua_toggle_stealth")],
        [("➕ Add custom UA", "ua_add"), ("🗑 Clear custom", "ua_clear")],
        [("🔄 Refresh remote list", "ua_refresh"), ("⬅️ Back", "btn_manage")],
    ])


def proxies_kb():
    return _kb([
        [("📤 Export working .txt", "px_export"), ("🏆 Top proxies", "px_top")],
        [("🧹 Purge dead", "ask_purge"), ("♻️ Reset failed", "ask_reset_failed")],
        [("🔁 Re-run preflight", "ask_reset_pf"), ("📊 Counts", "px_counts")],
        [("⬅️ Back", "btn_back")],
    ])


def codespace_kb():
    return _kb([
        [("ℹ️ Status", "cs_info"), ("🌐 Public URL", "sys_public")],
        [("✏️ Rename", "cs_rename"), ("🔌 Stop Codespace", "ask_cs_stop")],
        [("⬅️ Back", "btn_back")],
    ])


def settings_kb():
    rows, row = [], []
    for cat in SETTINGS_SCHEMA:
        row.append((cat.capitalize(), f"cat:{cat}"))
        if len(row) == 2:
            rows.append(row); row = []
    if row:
        rows.append(row)
    rows.append([("⬅️ Back", "btn_back")])
    return _kb(rows)


def settings_cat_kb(cat: str):
    rows, row = [], []
    for key, label, *_ in SETTINGS_SCHEMA.get(cat, []):
        row.append((label, f"set:{key}"))
        if len(row) == 2:
            rows.append(row); row = []
    if row:
        rows.append(row)
    rows.append([("⬅️ Settings", "btn_settings")])
    return _kb(rows)


def confirm_kb(action: str):
    return _kb([[("✅ Yes, do it", f"do:{action}"), ("❌ Cancel", "btn_back")]])


def back_kb(to: str = "btn_back"):
    return _kb([[("⬅️ Back", to)]])


# ── message helpers ───────────────────────────────────────────────────────────
def _notify_chat_id(rt: Runtime) -> Optional[int]:
    if rt.live_status_chat_id:
        return rt.live_status_chat_id
    cid = str(CFG.telegram_chat_id).strip()
    try:
        return int(cid) if cid else None
    except ValueError:
        return None


async def _notify(rt: Runtime, text: str, key: Optional[str] = None) -> None:
    """Send an alert, suppressing an identical one inside notify_dedupe_seconds.
    This is the anti-spam valve for repeated fetch/circuit/network messages."""
    chat = _notify_chat_id(rt)
    if not (rt.bot and chat):
        return
    k = key or hashlib.sha1(text.encode()).hexdigest()
    now = time.time()
    if CFG.notify_dedupe_seconds > 0:
        last = rt._notify_seen.get(k, 0.0)
        if now - last < CFG.notify_dedupe_seconds:
            return
        rt._notify_seen[k] = now
        if len(rt._notify_seen) > 200:                 # keep the dedupe table bounded
            for dead in [kk for kk, tt in rt._notify_seen.items() if now - tt > 86_400]:
                rt._notify_seen.pop(dead, None)
    with contextlib.suppress(Exception):
        await rt.bot.send_message(chat, _clip(text))


async def _edit(cq, text: str, kb=None) -> None:
    """Edit the message behind a button press; fall back to a new message if the
    original is gone (old chat, deleted message, inaccessible)."""
    text = _clip(text)
    msg = getattr(cq, "message", None)
    if msg is not None:
        try:
            await msg.edit_text(text, reply_markup=kb)
            with contextlib.suppress(Exception):
                await cq.answer()
            return
        except TelegramBadRequest:
            pass                                       # "message is not modified" / not editable
        except Exception:
            pass
        with contextlib.suppress(Exception):
            await msg.answer(text, reply_markup=kb)
    with contextlib.suppress(Exception):
        await cq.answer()


async def _ask(cq, text: str, state, next_state) -> None:
    """Prompt for free text and park the user in an FSM state."""
    msg = getattr(cq, "message", None)
    if msg is not None:
        with contextlib.suppress(Exception):
            await msg.answer(_clip(text), reply_markup=back_kb())
    if state is not None:
        await state.set_state(next_state)
    with contextlib.suppress(Exception):
        await cq.answer()


def send_sync_alert(text: str) -> None:
    """Blocking, stdlib-only Telegram alert for code paths that have no event loop
    (crash handler, shutdown, pre-start failures).  Never raises."""
    token = CFG.telegram_bot_token
    chat = str(CFG.telegram_chat_id).strip()
    if not token or not chat:
        return
    try:
        req = urllib.request.Request(
            f"https://api.telegram.org/bot{token}/sendMessage",
            data=json.dumps({"chat_id": chat, "text": text[:3900]}).encode("utf-8"),
            headers={"Content-Type": "application/json"}, method="POST")
        with urllib.request.urlopen(req, timeout=5) as resp:
            resp.read()
    except Exception as exc:
        elog.warning("telegram alert failed: %s", type(exc).__name__)   # type only: never log the token


# ── rendered views ────────────────────────────────────────────────────────────
async def render_status(rt: Runtime) -> str:
    st = await rt.store.stats()
    g = st["global"]
    pf = st["preflight"]
    mem = psutil.virtual_memory().percent if psutil else None
    cpu = psutil.cpu_percent(interval=None) if psutil else None
    schemes = ", ".join(f"{k}:{v:,}" for k, v in sorted(st["schemes"].items())) or "-"
    ok_rate = (100.0 * rt.tests_ok / rt.tests_done) if rt.tests_done else 0.0
    lines = [
        f"📊 <b>Radiate v{VERSION}</b> — {_h(rt.pause_text())}",
        f"⏱ up {human_seconds(time.time() - rt.daemon_started)}"
        + (f" | RAM {mem:.0f}%" if mem is not None else "")
        + (f" | CPU {cpu:.0f}%" if cpu is not None else ""),
        "",
        f"🔹 <b>Proxies</b> {st['proxies_total']:,}",
        f"✅ Validated {g.get('WORKING', 0):,}   🟡 Preflight-only {g.get('PREFLIGHT_PASS', 0):,}",
        f"🔄 Retry {g.get('RETRYABLE', 0):,}   🚫 Quarantined {g.get('QUARANTINED', 0):,}",
        f"❌ Failed {g.get('FAILED', 0):,}   💀 Dead {g.get('DEAD', 0):,}   ⏳ Untested {g.get('UNTESTED', 0):,}",
        "",
        f"🧪 <b>Preflight</b> alive {pf.get('ALIVE', 0):,} / dead {pf.get('DEAD', 0):,} / "
        f"unknown {pf.get('UNKNOWN', 0):,}",
        f"🔌 Protocols: {_h(schemes)}",
        f"📥 Pending probes {st['pf_pending']:,}   queue {rt.preflight_queue.qsize()}",
        "",
        f"👷 <b>Workers busy</b> fresh {rt.workers_busy}/{rt.worker_limit} "
        f"(cap {CFG.worker_count}) | retry {rt.retry_workers_busy}/{rt.retry_limit} "
        f"(cap {CFG.retry_worker_count})",
        f"🧵 Sockets {rt.preflight_workers_alive} | 🖥 browsers {len(rt.pool.recs)}"
        f"×{CFG.contexts_per_browser}",
        f"📦 Queues fresh {rt.queue.qsize()}/{rt.queue.maxsize} · "
        f"retry {rt.retry_queue.qsize()}/{rt.retry_queue.maxsize}",
        f"⚙️ In-flight {st['in_flight']:,} | due {st['due']:,}",
        f"📈 Tests {rt.tests_done:,} ({ok_rate:.1f}% ok) | probes {rt.preflight_done:,} "
        f"({rt.preflight_alive:,} alive)",
    ]
    if st["targets"]:
        lines.append("")
        lines.append("🎯 <b>Targets</b>")
        for tid, counts in list(st["targets"].items())[:6]:
            w = counts.get("WORKING", 0) + counts.get("RECOVERED", 0)
            tot = sum(counts.values())
            lines.append(f"  • {_h(tid)}: {w:,}/{tot:,} working")
    cir = rt.circuit.state_dict()
    tripped = {k: v for k, v in cir.items() if v != "closed"}
    if tripped:
        lines.append("")
        lines.append("🔌 <b>Circuit</b> " + _h(", ".join(f"{k}={v}" for k, v in tripped.items())))
    return "\n".join(lines)


async def render_telemetry(rt: Runtime) -> str:
    fb = await rt.store.failure_breakdown(24.0)
    errs = await rt.store.recent_errors(6)
    cir = rt.circuit.state_dict()
    lines = [f"📈 <b>Telemetry</b> (last 24h)", ""]
    if fb:
        total = sum(n for _, n in fb) or 1
        lines.append("<b>Result classes</b>")
        for cls, n in fb[:10]:
            lines.append(f"  {_h(cls)}: {n:,} ({100.0 * n / total:.1f}%)")
    else:
        lines.append("No test history yet.")
    lines += ["", "<b>Runtime</b>",
              f"  worker restarts {rt.worker_restarts} | browser restarts {rt.pool.restarts}",
              f"  circuit trips {rt.circuit_trips} | network {'DOWN' if rt.netguard.down else 'OK'}",
              f"  fd limit {rt.fd_limit or 'n/a'} | aiohttp {'yes' if AIOHTTP_OK else 'no'} | "
              f"psutil {'yes' if psutil else 'no'}"]
    if cir:
        lines += ["", "<b>Circuit breakers</b>"]
        lines += [f"  {_h(k)}: {_h(v)}" for k, v in list(cir.items())[:8]]
    if CFG.mongo_enabled:
        lines += ["", "<b>Mongo</b> last sync "
                  + (human_seconds(time.time() - MONGO.last_sync) + " ago" if MONGO.last_sync else "never")
                  + (f" | {_h(MONGO.last_error)}" if MONGO.last_error else "")]
    if errs:
        lines += ["", "<b>Recent failures</b>"]
        for e in errs:
            when = human_seconds(time.time() - e["ts"])
            lines.append(f"  {when} ago · {_h(e['status'])} · {_h(e['proxy'])}")
            if e["error"]:
                lines.append(f"     ↳ {_h(e['error'][:110])}")
    return "\n".join(lines)


def codespace_name() -> str:
    return (CFG.codespace_name or os.environ.get("CODESPACE_NAME") or "").strip()


def public_url_for_port(port: int) -> Optional[str]:
    """GitHub Codespaces exposes forwarded ports at
    https://<codespace>-<port>.<forwarding-domain>.  Both parts come from the
    environment, so this is exact rather than guessed."""
    name = codespace_name()
    domain = os.environ.get("GITHUB_CODESPACES_PORT_FORWARDING_DOMAIN", "").strip()
    if not (name and domain):
        return None
    return f"https://{name}-{port}.{domain}"


# ══════════════════════════════════════════════════════════════════════════════
#  GITHUB CODESPACE CONTROL
#  Two backends: the `gh` CLI when it is installed and logged in, otherwise the
#  REST API with a PAT.  Note that $GITHUB_TOKEN inside a Codespace is usually a
#  repo-scoped token WITHOUT the `codespace` scope - set config.github_token to a
#  PAT that has it, or rely on gh.
# ══════════════════════════════════════════════════════════════════════════════
def _gh_available() -> bool:
    return shutil.which("gh") is not None


def _gh(args: list, timeout: int = 60) -> tuple[int, str]:
    try:
        r = subprocess.run(["gh", *args], capture_output=True, text=True, timeout=timeout)
        return r.returncode, (r.stdout or r.stderr).strip()
    except FileNotFoundError:
        return 127, "gh CLI is not installed"
    except subprocess.TimeoutExpired:
        return 124, "gh timed out"
    except Exception as exc:
        return 1, f"{type(exc).__name__}: {exc}"


def _gh_api(method: str, path: str, payload: Optional[dict] = None) -> tuple[int, str]:
    token = CFG.github_token or os.environ.get("GITHUB_TOKEN", "")
    if not token:
        return 401, "no github_token configured and gh CLI unavailable"
    req = urllib.request.Request(
        f"https://api.github.com{path}",
        data=json.dumps(payload).encode() if payload is not None else None,
        headers={"Authorization": f"Bearer {token}",
                 "Accept": "application/vnd.github+json",
                 "X-GitHub-Api-Version": "2022-11-28",
                 "Content-Type": "application/json",
                 "User-Agent": f"radiate/{VERSION}"},
        method=method)
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            return resp.status, resp.read().decode("utf-8", "ignore")[:2000]
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read().decode("utf-8", "ignore")[:400]
    except Exception as exc:
        return 0, f"{type(exc).__name__}: {exc}"


def codespace_info() -> dict:
    name = codespace_name()
    info = {"name": name or "(not in a Codespace)",
            "repo": os.environ.get("GITHUB_REPOSITORY", "?"),
            "gh_cli": _gh_available(),
            "public_url": public_url_for_port(CFG.http_api_port) or "(not exposed)",
            "token": "configured" if (CFG.github_token or os.environ.get("GITHUB_TOKEN")) else "none"}
    if name:
        code, body = _gh_api("GET", f"/user/codespaces/{name}")
        if code == 200:
            with contextlib.suppress(Exception):
                d = json.loads(body)
                info["state"] = d.get("state")
                info["display_name"] = d.get("display_name")
                info["machine"] = (d.get("machine") or {}).get("display_name")
    return info


def codespace_stop() -> tuple[bool, str]:
    name = codespace_name()
    if not name:
        return False, "CODESPACE_NAME is not set - not running inside a Codespace."
    if _gh_available():
        rc, out = _gh(["codespace", "stop", "-c", name])
        if rc == 0:
            return True, "Stop requested via gh CLI."
    code, body = _gh_api("POST", f"/user/codespaces/{name}/stop")
    if 200 <= code < 300:
        return True, "Stop requested via GitHub API."
    return False, f"API said {code}: {body[:200]}"


def codespace_rename(new_name: str) -> tuple[bool, str]:
    name = codespace_name()
    if not name:
        return False, "CODESPACE_NAME is not set."
    code, body = _gh_api("PATCH", f"/user/codespaces/{name}", {"display_name": new_name})
    if 200 <= code < 300:
        return True, f"Display name is now “{new_name}”."
    if _gh_available():
        rc, out = _gh(["codespace", "edit", "-c", name, "-d", new_name])
        if rc == 0:
            return True, f"Display name is now “{new_name}”."
        return False, out[:200]
    return False, f"API said {code}: {body[:200]}"


def make_port_public(port: int) -> tuple[bool, str]:
    """UptimeRobot can only reach the health endpoint if the forwarded port is public."""
    name = codespace_name()
    if not name:
        return False, "not inside a Codespace"
    if not _gh_available():
        return False, "gh CLI not installed - set the port to Public in the Ports tab"
    rc, out = _gh(["codespace", "ports", "visibility", f"{port}:public", "-c", name])
    return (rc == 0), (out[:200] or "ok")


# ══════════════════════════════════════════════════════════════════════════════
#  BOT HANDLERS
# ══════════════════════════════════════════════════════════════════════════════
@router.message(Command("start"))
async def cmd_start(message: Message, rt: Runtime):
    await message.answer(
        f"🚀 <b>Radiate Proxy Monitor v{VERSION}</b>\n"
        f"Codespace: <code>{_h(codespace_name() or 'local')}</code>\n"
        f"State: {_h(rt.pause_text())}\n\nPick a control:",
        reply_markup=main_kb())


@router.message(Command("status"))
async def cmd_status(message: Message, rt: Runtime):
    await message.answer(await render_status(rt), reply_markup=main_kb())


@router.message(Command("help"))
async def cmd_help(message: Message, rt: Runtime):
    await message.answer(
        "<b>Commands</b>\n"
        "/start – control panel\n"
        "/status – one-off status snapshot\n"
        "/pause [minutes] – pause (no argument = until resumed)\n"
        "/resume – resume testing\n"
        "/cancel – leave any input prompt\n\n"
        "Send a <code>.txt</code> file at any time to import proxies.",
        reply_markup=main_kb())


@router.message(Command("cancel"))
async def cmd_cancel(message: Message, state: FSMContext, rt: Runtime):
    await state.clear()
    await message.answer("Cancelled.", reply_markup=main_kb())


@router.message(Command("pause"))
async def cmd_pause(message: Message, rt: Runtime):
    parts = (message.text or "").split()
    mins = 0.0
    if len(parts) > 1:
        with contextlib.suppress(ValueError):
            mins = float(parts[1])
    rt.set_pause(True, mins * 60)
    await message.answer(f"⏸️ {_h(rt.pause_text())}", reply_markup=main_kb())


@router.message(Command("resume"))
async def cmd_resume(message: Message, rt: Runtime):
    rt.set_pause(False)
    await message.answer("▶️ Resumed.", reply_markup=main_kb())


# ── navigation ────────────────────────────────────────────────────────────────
@router.callback_query(F.data == "btn_back")
async def cq_back(cq: CallbackQuery, rt: Runtime):
    await _edit(cq, f"🚀 <b>Radiate v{VERSION}</b> — {_h(rt.pause_text())}", main_kb())


@router.callback_query(F.data == "btn_manage")
async def cq_manage(cq: CallbackQuery, rt: Runtime):
    await _edit(cq, f"⚙️ <b>System</b>\nState: {_h(rt.pause_text())}\n"
                    f"Fresh workers {rt.worker_limit}/{CFG.worker_count} · "
                    f"retry {rt.retry_limit}/{CFG.retry_worker_count} · "
                    f"preflight {CFG.preflight_worker_count}", manage_kb(rt))


@router.callback_query(F.data == "btn_telemetry")
async def cq_telemetry(cq: CallbackQuery, rt: Runtime):
    await _edit(cq, await render_telemetry(rt), back_kb())


# ── live status: ONE message, edited, only when the text changed ──────────────
@router.callback_query(F.data == "btn_status")
async def cq_status(cq: CallbackQuery, rt: Runtime):
    msg = getattr(cq, "message", None)
    if msg is None:
        with contextlib.suppress(Exception):
            await cq.answer()
        return
    chat_id = msg.chat.id
    # Re-anchoring instead of spawning a second live message: the previous one is
    # removed so only one auto-updating message can ever exist per chat.
    if rt.live_status_msg_id and rt.live_status_chat_id == chat_id:
        with contextlib.suppress(Exception):
            await rt.bot.delete_message(chat_id, rt.live_status_msg_id)
    text = await render_status(rt)
    sent = await msg.answer(text, reply_markup=main_kb())
    rt.live_status_chat_id = chat_id
    rt.live_status_msg_id = sent.message_id
    rt._live_hash = hashlib.sha1(text.encode()).hexdigest()
    rt._live_unchanged = 0
    with contextlib.suppress(Exception):
        await cq.answer("Live status pinned - it refreshes itself.")


# ── pause / resume ────────────────────────────────────────────────────────────
@router.callback_query(F.data == "btn_pause")
async def cq_pause_menu(cq: CallbackQuery, rt: Runtime):
    await _edit(cq, "⏸️ <b>Pause for how long?</b>\nTesting stops; the bot stays responsive.",
                pause_kb())


@router.callback_query(F.data.startswith("pause_"))
async def cq_pause_do(cq: CallbackQuery, rt: Runtime):
    secs = float(cq.data.split("_", 1)[1])
    rt.set_pause(True, secs)
    await _edit(cq, f"⏸️ <b>Paused</b> — {_h(rt.pause_text())}", manage_kb(rt))


@router.callback_query(F.data == "sys_resume")
async def cq_resume(cq: CallbackQuery, rt: Runtime):
    rt.set_pause(False)
    await _edit(cq, "▶️ <b>Resumed.</b>", manage_kb(rt))


# ── speed ─────────────────────────────────────────────────────────────────────
def _apply_speed(fresh: int, retry: int, preflight: int, batch: int, rt: Runtime) -> None:
    CFG.auto_tune = False                     # an explicit choice beats the autotuner
    CFG.worker_count, CFG.retry_worker_count = fresh, retry
    CFG.preflight_worker_count, CFG.batch_size_per_tick = preflight, batch
    save_config(CFG)
    rt.worker_limit = min(rt.worker_limit, CFG.worker_count) or 1
    rt.retry_limit = min(rt.retry_limit, CFG.retry_worker_count)


@router.callback_query(F.data == "btn_speed")
async def cq_speed(cq: CallbackQuery, rt: Runtime):
    await _edit(cq, "⚡ <b>Speed presets</b>\n"
                    "Eco = gentle on the Codespace, Turbo = maximum throughput.\n"
                    "Preflight socket changes apply after a restart.", speed_kb())


@router.callback_query(F.data.startswith("speed_"))
async def cq_speed_set(cq: CallbackQuery, rt: Runtime):
    which = cq.data.split("_", 1)[1]
    if which == "eco":
        _apply_speed(2, 2, 128, 10, rt)
    elif which == "normal":
        _apply_speed(6, 6, 512, 30, rt)
    elif which == "turbo":
        _apply_speed(MAX_MAIN_WORKERS, MAX_RETRY_WORKERS, 1024, 80, rt)
    else:
        CFG.auto_tune = True
        apply_auto_tune(CFG)
        save_config(CFG)
        rt.worker_limit, rt.retry_limit = CFG.worker_count, CFG.retry_worker_count
    await _edit(cq, f"⚡ Applied <b>{_h(which)}</b>\nfresh {CFG.worker_count} · "
                    f"retry {CFG.retry_worker_count} · preflight {CFG.preflight_worker_count} · "
                    f"batch {CFG.batch_size_per_tick}", speed_kb())


@router.callback_query(F.data == "sys_speed_up")
async def cq_speed_up(cq: CallbackQuery, rt: Runtime):
    CFG.auto_tune = False
    CFG.worker_count = min(CFG.worker_count + 1, MAX_MAIN_WORKERS)
    CFG.retry_worker_count = min(CFG.retry_worker_count + 1, MAX_RETRY_WORKERS)
    save_config(CFG)
    rt.worker_limit = min(rt.worker_limit + 1, CFG.worker_count)
    rt.retry_limit = min(rt.retry_limit + 1, CFG.retry_worker_count)
    with contextlib.suppress(Exception):
        await cq.answer(f"fresh {CFG.worker_count} / retry {CFG.retry_worker_count}")
    await _edit(cq, f"⚙️ <b>System</b>\nFresh {rt.worker_limit}/{CFG.worker_count} · "
                    f"retry {rt.retry_limit}/{CFG.retry_worker_count}", manage_kb(rt))


@router.callback_query(F.data == "sys_speed_down")
async def cq_speed_down(cq: CallbackQuery, rt: Runtime):
    CFG.auto_tune = False
    CFG.worker_count = max(CFG.worker_count - 1, 1)
    CFG.retry_worker_count = max(CFG.retry_worker_count - 1, 0)
    save_config(CFG)
    rt.worker_limit = max(1, min(rt.worker_limit, CFG.worker_count))
    rt.retry_limit = min(rt.retry_limit, CFG.retry_worker_count)
    with contextlib.suppress(Exception):
        await cq.answer(f"fresh {CFG.worker_count} / retry {CFG.retry_worker_count}")
    await _edit(cq, f"⚙️ <b>System</b>\nFresh {rt.worker_limit}/{CFG.worker_count} · "
                    f"retry {rt.retry_limit}/{CFG.retry_worker_count}", manage_kb(rt))


# ── user agent ────────────────────────────────────────────────────────────────
@router.callback_query(F.data == "btn_ua")
async def cq_ua(cq: CallbackQuery, rt: Runtime):
    await _edit(cq, f"🧬 <b>User-Agent & fingerprint</b>\n"
                    f"Custom profiles: {len(CFG.custom_ua_profiles)}\n"
                    f"Remote pool loaded: {len(_REMOTE_UA_LIST)}\n"
                    f"Host OS template: {_h(_host_os())}\n"
                    f"Chromium: {_h(rt.browser_version or '?')}", ua_kb())


@router.callback_query(F.data.startswith("ua_toggle_"))
async def cq_ua_toggle(cq: CallbackQuery, rt: Runtime):
    what = cq.data.rsplit("_", 1)[1]
    if what == "rot":
        CFG.ua_rotation = not CFG.ua_rotation
    elif what == "remote":
        CFG.ua_pool_remote = not CFG.ua_pool_remote
    else:
        CFG.enable_stealth_script = not CFG.enable_stealth_script
    save_config(CFG)
    await _edit(cq, "🧬 <b>User-Agent & fingerprint</b>\nUpdated.", ua_kb())


@router.callback_query(F.data == "ua_add")
async def cq_ua_add(cq: CallbackQuery, state: FSMContext, rt: Runtime):
    await _ask(cq, "Send a full User-Agent string.\nOptionally append <code>|width|height</code>, "
                   "e.g. <code>Mozilla/5.0 ...|1366|768</code>.", state, BotStates.waiting_for_ua)


@router.message(BotStates.waiting_for_ua, F.text)
async def process_ua(message: Message, state: FSMContext, rt: Runtime):
    await state.clear()
    raw = (message.text or "").strip()
    if len(raw) < 20 or "/" not in raw:
        await message.answer("That does not look like a User-Agent string.", reply_markup=ua_kb())
        return
    parts = raw.split("|")
    ua = parts[0].strip()
    w = int(parts[1]) if len(parts) > 2 and parts[1].strip().isdigit() else 1366
    hgt = int(parts[2]) if len(parts) > 2 and parts[2].strip().isdigit() else 768
    CFG.custom_ua_profiles = list(CFG.custom_ua_profiles) + [
        {"ua": ua, "width": w, "height": hgt, "locale": "en-US", "tz": "America/New_York"}]
    save_config(CFG)
    await message.answer(f"✅ Added. Custom profiles: {len(CFG.custom_ua_profiles)}", reply_markup=ua_kb())


@router.callback_query(F.data == "ua_clear")
async def cq_ua_clear(cq: CallbackQuery, rt: Runtime):
    CFG.custom_ua_profiles = []
    save_config(CFG)
    await _edit(cq, "🧬 Custom UA profiles cleared - built-in rotation is back in use.", ua_kb())


@router.callback_query(F.data == "ua_refresh")
async def cq_ua_refresh(cq: CallbackQuery, rt: Runtime):
    with contextlib.suppress(Exception):
        await cq.answer("Refreshing…")
    rt.track(_ua_refresh_once(rt))


# ── targets ───────────────────────────────────────────────────────────────────
def targets_kb(targets: list[Target]):
    rows = []
    for t in targets[:12]:
        mark = "🟢" if t.enabled else "⚪️"
        rows.append([(f"{mark} {t.target_id[:28]}", f"tgt:{t.target_id}")])
    rows.append([("➕ Add target", "btn_target"), ("⬅️ Back", "btn_back")])
    return _kb(rows)


def target_detail_kb(t: Target):
    return _kb([
        [("⏹ Disable" if t.enabled else "▶️ Enable", f"tg_en:{t.target_id}")],
        [(f"Offsite redirect: {'ON' if t.allow_offsite_redirect else 'OFF'}", f"tg_off:{t.target_id}")],
        [(f"Rule B (redirect=OK): {'ON' if t.redirect_means_success else 'OFF'}", f"tg_rb:{t.target_id}")],
        [(f"Status 200 required: {'ON' if t.require_status_200 else 'OFF'}", f"tg_200:{t.target_id}")],
        [("🗑 Remove", f"tg_rm:{t.target_id}"), ("⬅️ Back", "btn_targets")],
    ])


@router.callback_query(F.data == "btn_targets")
async def cq_targets(cq: CallbackQuery, rt: Runtime):
    try:
        targets = load_targets()
    except ValueError as exc:
        await _edit(cq, f"❌ targets.json is invalid: {_h(exc)}", back_kb())
        return
    if not targets:
        await _edit(cq, "No targets configured yet.", targets_kb([]))
        return
    body = "\n".join(f"{'🟢' if t.enabled else '⚪️'} <code>{_h(t.target_id)}</code>\n   {_h(t.url)}"
                     for t in targets[:12])
    await _edit(cq, f"🔗 <b>Targets</b>\n{body}", targets_kb(targets))


@router.callback_query(F.data.startswith("tgt:"))
async def cq_target_detail(cq: CallbackQuery, rt: Runtime):
    tid = cq.data.split(":", 1)[1]
    t = next((x for x in load_targets() if x.target_id == tid), None)
    if t is None:
        await _edit(cq, "That target no longer exists.", back_kb("btn_targets"))
        return
    await _edit(cq,
                f"🔗 <b>{_h(t.target_id)}</b>\n<code>{_h(t.url)}</code>\n\n"
                f"Enabled: {t.enabled}\nWait: {t.post_load_wait_seconds:.0f}s · "
                f"Nav timeout: {t.navigation_timeout_ms} ms\n"
                f"Min body: {t.min_body_length} chars\n"
                f"Referer: <code>{_h(t.referer or CFG.default_referer or '-')}</code>\n\n"
                f"<i>Rule B turns a redirect away from the target URL into an instant PASS. "
                f"Leave it OFF unless your target really does redirect on success - a proxy "
                f"bounced to a block page also redirects.</i>",
                target_detail_kb(t))


def _mutate_target(tid: str, fn) -> Optional[Target]:
    try:
        targets = load_targets()
    except ValueError:
        return None
    for t in targets:
        if t.target_id == tid:
            fn(t)
            save_targets(targets)
            return t
    return None


@router.callback_query(F.data.startswith("tg_en:"))
async def cq_target_enable(cq: CallbackQuery, rt: Runtime):
    tid = cq.data.split(":", 1)[1]
    t = _mutate_target(tid, lambda x: setattr(x, "enabled", not x.enabled))
    await _edit(cq, f"🔗 <b>{_h(tid)}</b> enabled={t.enabled if t else '?'}",
                target_detail_kb(t) if t else back_kb("btn_targets"))


@router.callback_query(F.data.startswith("tg_off:"))
async def cq_target_offsite(cq: CallbackQuery, rt: Runtime):
    tid = cq.data.split(":", 1)[1]
    t = _mutate_target(tid, lambda x: setattr(x, "allow_offsite_redirect", not x.allow_offsite_redirect))
    await _edit(cq, f"🔗 <b>{_h(tid)}</b> offsite redirect="
                    f"{t.allow_offsite_redirect if t else '?'}",
                target_detail_kb(t) if t else back_kb("btn_targets"))


@router.callback_query(F.data.startswith("tg_rb:"))
async def cq_target_ruleb(cq: CallbackQuery, rt: Runtime):
    tid = cq.data.split(":", 1)[1]

    def flip(x: Target):
        x.redirect_means_success = not x.redirect_means_success
        if x.redirect_means_success:
            x.allow_offsite_redirect = True          # Rule B implies accepting the new host
    t = _mutate_target(tid, flip)
    note = ("\n⚠️ Rule B is now ON: any redirect away from the target URL counts as WORKING "
            "(except a proxy-detection page). Off-site redirects were enabled with it."
            if t and t.redirect_means_success else "")
    await _edit(cq, f"🔗 <b>{_h(tid)}</b> Rule B={t.redirect_means_success if t else '?'}{note}",
                target_detail_kb(t) if t else back_kb("btn_targets"))


@router.callback_query(F.data.startswith("tg_200:"))
async def cq_target_200(cq: CallbackQuery, rt: Runtime):
    tid = cq.data.split(":", 1)[1]
    t = _mutate_target(tid, lambda x: setattr(x, "require_status_200", not x.require_status_200))
    await _edit(cq, f"🔗 <b>{_h(tid)}</b> require 200={t.require_status_200 if t else '?'}",
                target_detail_kb(t) if t else back_kb("btn_targets"))


@router.callback_query(F.data.startswith("tg_rm:"))
async def cq_target_remove(cq: CallbackQuery, rt: Runtime):
    tid = cq.data.split(":", 1)[1]
    try:
        targets = [t for t in load_targets() if t.target_id != tid]
    except ValueError as exc:
        await _edit(cq, f"❌ {_h(exc)}", back_kb("btn_targets"))
        return
    save_targets(targets)
    await _edit(cq, f"🗑 Removed <code>{_h(tid)}</code>. History is kept in the database.",
                targets_kb(targets))


@router.callback_query(F.data == "btn_target")
async def cq_target_add(cq: CallbackQuery, state: FSMContext, rt: Runtime):
    await _ask(cq, "Send the target URL (http:// or https://).", state, BotStates.waiting_for_target)


@router.message(BotStates.waiting_for_target, F.text)
async def process_target(message: Message, state: FSMContext, rt: Runtime):
    await state.clear()                              # cleared first: an error can never wedge the chat
    url = (message.text or "").strip()
    try:
        new = _target_from_dict({"url": url})        # same validation/defaults as targets.json
    except Exception:
        await message.answer("❌ Invalid URL — it must start with http:// or https://",
                             reply_markup=main_kb())
        return
    try:
        targets = load_targets()
    except ValueError as exc:
        await message.answer(f"❌ targets.json is invalid: {_h(exc)}", reply_markup=main_kb())
        return
    if any(t.target_id == new.target_id or t.url == new.url for t in targets):
        await message.answer(f"Already configured: <code>{_h(new.target_id)}</code>",
                             reply_markup=targets_kb(targets))
        return
    targets.append(new)
    save_targets(targets)
    await message.answer(f"✅ Added <code>{_h(new.target_id)}</code> — the daemon hot-reloads it "
                         f"within a few seconds.", reply_markup=targets_kb(targets))


# ── sources (proxy list URLs) ─────────────────────────────────────────────────
def sources_kb():
    rows = [[(f"🗑 {u.split('/')[-1][:26] or u[:26]}", f"srm:{i}")]
            for i, u in enumerate(CFG.fallback_urls[:10])]
    rows.append([("➕ Add source", "src_add"), ("🔄 Fetch now", "btn_fetch")])
    rows.append([("⬅️ Back", "btn_manage")])
    return _kb(rows)


@router.callback_query(F.data == "btn_sources")
async def cq_sources(cq: CallbackQuery, rt: Runtime):
    body = "\n".join(f"{i + 1}. <code>{_h(u)}</code>" for i, u in enumerate(CFG.fallback_urls)) or "(none)"
    await _edit(cq, f"📡 <b>Proxy sources</b>\n{body}\n\n"
                    f"Auto-fetch triggers when validated proxies drop below "
                    f"{CFG.fallback_min_working}.", sources_kb())


@router.callback_query(F.data.startswith("srm:"))
async def cq_source_remove(cq: CallbackQuery, rt: Runtime):
    idx = int(cq.data.split(":", 1)[1])
    urls = list(CFG.fallback_urls)
    if 0 <= idx < len(urls):
        urls.pop(idx)
        CFG.fallback_urls = urls
        save_config(CFG)
    await cq_sources(cq, rt)


@router.callback_query(F.data == "src_add")
async def cq_source_add(cq: CallbackQuery, state: FSMContext, rt: Runtime):
    await _ask(cq, "Send the URL of a plain-text proxy list.", state, BotStates.waiting_for_source)


@router.message(BotStates.waiting_for_source, F.text)
async def process_source(message: Message, state: FSMContext, rt: Runtime):
    await state.clear()
    url = (message.text or "").strip()
    if not _valid_http_url(url):
        await message.answer("❌ That is not an http(s) URL.", reply_markup=main_kb())
        return
    if url not in CFG.fallback_urls:
        CFG.fallback_urls = list(CFG.fallback_urls) + [url]
        save_config(CFG)
    await message.answer("✅ Source added. Use 🔄 Force Fetch to pull it now.", reply_markup=sources_kb())


# ── fetching & uploads ────────────────────────────────────────────────────────
@router.callback_query(F.data == "btn_fetch")
async def cq_fetch(cq: CallbackQuery, rt: Runtime):
    with contextlib.suppress(Exception):
        await cq.answer("Fetching in the background…")
    rt.track(_force_fetch_task(rt))


async def _force_fetch_task(rt: Runtime):
    try:
        proxies = await fetch_fallback_proxies(CFG.fallback_urls)
        if proxies:
            r = await rt.store.ingest_proxies(proxies)
            await _notify(rt, f"✅ Fetched {len(proxies):,} proxies — {r['inserted']:,} new, "
                              f"{r['existing']:,} already known. Preflight will filter them.",
                          key="fetch_result")
        else:
            await _notify(rt, "⚠️ Fetch returned nothing. Check the source URLs "
                              "(📡 Sources) and that outbound HTTPS works.", key="fetch_empty")
    except asyncio.CancelledError:
        raise
    except Exception as exc:
        elog.error("force fetch failed", exc_info=True)
        await _notify(rt, f"❌ Fetch failed: {type(exc).__name__}", key="fetch_error")


@router.callback_query(F.data == "btn_add_proxies")
async def cq_add_proxies(cq: CallbackQuery, rt: Runtime):
    await _edit(cq, "➕ <b>Add proxies</b>\nSend a <code>.txt</code> file with one proxy per line.\n"
                    "Accepted: <code>ip:port</code>, <code>scheme://ip:port</code>, "
                    "<code>ip:port:user:pass</code>, or messy list rows.\n"
                    "Scheme-less lines are protocol-probed automatically.", back_kb())


@router.message(F.document)
async def handle_document(message: Message, state: FSMContext, rt: Runtime):
    """Import a .txt proxy list.  Registered without a state filter so an upload
    works even while another prompt is open - the prompt is cleared first."""
    with contextlib.suppress(Exception):
        await state.clear()
    doc = message.document
    # Only the extension of the supplied name is inspected; the on-disk name is
    # generated here, so "../../x.txt" can never influence where we write.
    if not Path(doc.file_name or "").name.lower().endswith(".txt"):
        await message.answer("Send a <code>.txt</code> file with one proxy per line.")
        return
    if doc.file_size and doc.file_size > MAX_UPLOAD_BYTES:
        await message.answer(f"File too large (limit {MAX_UPLOAD_BYTES // (1024 * 1024)} MB).")
        return
    dest = UPLOAD_DIR / f"upload_{os.getpid()}_{int(time.time() * 1000)}.txt"
    try:
        file = await rt.bot.get_file(doc.file_id)
        await rt.bot.download_file(file.file_path, dest)
        lst, bad = await asyncio.to_thread(load_proxy_file, dest)
        r = await rt.store.ingest_proxies(lst)
    except asyncio.CancelledError:
        raise
    except Exception:
        elog.error("proxy upload failed", exc_info=True)
        await message.answer("❌ Could not process that file.")
        return
    finally:
        with contextlib.suppress(OSError):
            dest.unlink()
    await message.answer(
        f"✅ <b>Imported</b>\nParsed {len(lst):,} unique · {r['inserted']:,} new · "
        f"{r['existing']:,} known · {bad:,} unusable lines.\n"
        f"They enter the preflight queue immediately.", reply_markup=main_kb())


# ── VIP check: one proxy, its own browser context, full diagnostic ────────────
@router.callback_query(F.data == "btn_vip")
async def cq_vip(cq: CallbackQuery, state: FSMContext, rt: Runtime):
    await _ask(cq, "🧪 <b>VIP check</b>\nSend one proxy (<code>ip:port</code> or "
                   "<code>scheme://ip:port</code>).\nIt is probed, then opened in its own browser "
                   "context against the first enabled target, and you get the full verdict.",
               state, BotStates.waiting_for_vip)


@router.message(BotStates.waiting_for_vip, F.text)
async def process_vip(message: Message, state: FSMContext, rt: Runtime):
    await state.clear()
    raw = (message.text or "").strip()
    proxy = normalize_proxy(raw)
    if proxy is None:
        m = _PROXY_TOKEN_RE.search(raw)
        proxy = normalize_proxy(m.group(0)) if m else None
    if proxy is None:
        await message.answer("❌ Could not parse a proxy out of that.", reply_markup=main_kb())
        return
    targets = rt.registry.enabled()
    if not targets:
        await message.answer("❌ No enabled target to test against.", reply_markup=main_kb())
        return
    status_msg = await message.answer("🧪 Stage 1: TCP…")
    rt.track(_vip_check(rt, proxy, targets[0], status_msg.chat.id, status_msg.message_id))


async def _vip_check(rt: Runtime, proxy: str, target: Target, chat_id: int, msg_id: int) -> None:
    """Runs the whole pipeline for a single proxy and edits ONE message with the result."""
    async def upd(text: str) -> None:
        with contextlib.suppress(Exception):
            await rt.bot.edit_message_text(_clip(text), chat_id=chat_id, message_id=msg_id)

    shown = mask_proxy(proxy)
    try:
        t0 = time.monotonic()
        alive = await tcp_preflight(proxy, max(CFG.tcp_preflight_timeout, 3.0))
        tcp_ms = int((time.monotonic() - t0) * 1000)
        if not alive:
            await upd(f"🧪 <code>{_h(shown)}</code>\n❌ Stage 1 TCP: no connection ({tcp_ms} ms)")
            return
        await upd(f"🧪 <code>{_h(shown)}</code>\n✅ Stage 1 TCP {tcp_ms} ms\n⏳ Stage 2: handshake…")

        declared = urlparse(proxy).scheme
        scheme = await detect_protocol(proxy, declared, max(CFG.handshake_timeout, 4.0))
        if scheme is None:
            await upd(f"🧪 <code>{_h(shown)}</code>\n✅ Stage 1 TCP {tcp_ms} ms\n"
                      f"❌ Stage 2: the port is open but it does not answer as an "
                      f"http/socks5/socks4 proxy.")
            return
        effective = apply_scheme(proxy, scheme)
        await upd(f"🧪 <code>{_h(shown)}</code>\n✅ Stage 1 TCP {tcp_ms} ms\n"
                  f"✅ Stage 2: protocol <b>{_h(scheme)}</b>\n⏳ Stage 3: browser on "
                  f"<code>{_h(target.target_id)}</code>…")

        acq = await rt.pool.acquire(timeout=90.0)
        if not acq:
            await upd(f"🧪 <code>{_h(shown)}</code>\n⚠️ No browser slot free — try again shortly.")
            return
        bid, browser = acq
        res = None
        try:
            res = await validate_proxy(browser, effective, target, make_profile(rt.browser_version))
        finally:
            await rt.pool.release(bid, crashed=bool(res and res.browser_crashed))

        icon = "✅" if res.status == "WORKING" else "❌"
        lines = [f"🧪 <code>{_h(shown)}</code>",
                 f"✅ Stage 1 TCP {tcp_ms} ms",
                 f"✅ Stage 2 protocol <b>{_h(scheme)}</b>",
                 f"{icon} Stage 3 <b>{_h(res.status)}</b>",
                 "",
                 f"Target: <code>{_h(target.url)}</code>",
                 f"HTTP status: {res.http_status}",
                 f"First byte: {res.latency_seconds}s · total {res.elapsed_seconds}s",
                 f"Title: {_h((res.title or '-')[:90])}",
                 f"Final URL: <code>{_h((res.final_url or '-')[:120])}</code>",
                 f"Redirected: {res.redirected}"]
        if res.error:
            lines.append(f"Reason: {_h(res.error[:250])}")
        if res.status == "TARGET_VALIDATION_FAILED" and res.redirected \
                and not target.redirect_means_success:
            lines += ["", "<i>This proxy reached the site but landed on a different URL. If your "
                          "target legitimately redirects on success, turn Rule B on for it in "
                          "🔗 Targets.</i>"]
        await upd("\n".join(lines))
    except asyncio.CancelledError:
        raise
    except Exception as exc:
        elog.error("VIP check failed", exc_info=True)
        await upd(f"🧪 <code>{_h(shown)}</code>\n❌ Check crashed: {_h(type(exc).__name__)}")


# ── proxy management ──────────────────────────────────────────────────────────
@router.callback_query(F.data == "btn_proxies")
async def cq_proxies(cq: CallbackQuery, rt: Runtime):
    st = await rt.store.stats()
    g, pf = st["global"], st["preflight"]
    await _edit(cq, f"🗂 <b>Proxy management</b>\n"
                    f"Total {st['proxies_total']:,} · validated {g.get('WORKING', 0):,} · "
                    f"alive {pf.get('ALIVE', 0):,} · dead {pf.get('DEAD', 0):,}\n"
                    f"Protocols: {_h(', '.join(f'{k}:{v}' for k, v in sorted(st['schemes'].items())) or '-')}",
                proxies_kb())


@router.callback_query(F.data == "px_export")
async def cq_px_export(cq: CallbackQuery, rt: Runtime):
    with contextlib.suppress(Exception):
        await cq.answer("Building the file…")
    text = await rt.store.export_working_text()
    if not text:
        await _edit(cq, "No validated proxies to export yet.", proxies_kb())
        return
    data = ("# validated proxies - radiate v" + VERSION + "\n"
            + time.strftime("# %Y-%m-%d %H:%M:%S UTC\n", time.gmtime()) + text).encode()
    msg = getattr(cq, "message", None)
    if msg is not None:
        with contextlib.suppress(Exception):
            await msg.answer_document(
                BufferedInputFile(data, filename=f"validated_{time.strftime('%Y%m%d_%H%M')}.txt"),
                caption=f"{text.count(chr(10)) + 1:,} validated proxies")


@router.callback_query(F.data == "px_top")
async def cq_px_top(cq: CallbackQuery, rt: Runtime):
    rows = await rt.store.top_proxies(12)
    if not rows:
        await _edit(cq, "No working proxies yet.", proxies_kb())
        return
    body = "\n".join(
        f"{i + 1}. <code>{_h(r['proxy'])}</code> [{_h(r['scheme'])}] "
        f"score {r['score']} · {r['ok']}✅/{r['bad']}❌"
        + (f" · {r['latency']}s" if r['latency'] else "")
        for i, r in enumerate(rows))
    await _edit(cq, f"🏆 <b>Top proxies</b>\n{body}", proxies_kb())


@router.callback_query(F.data == "px_counts")
async def cq_px_counts(cq: CallbackQuery, rt: Runtime):
    st = await rt.store.stats()
    g = "\n".join(f"  {_h(k)}: {v:,}" for k, v in sorted(st["global"].items()))
    p = "\n".join(f"  {_h(k)}: {v:,}" for k, v in sorted(st["preflight"].items()))
    t = "\n".join(f"  {_h(tid)}: " + ", ".join(f"{_h(k)} {v:,}" for k, v in sorted(c.items()))
                  for tid, c in list(st["targets"].items())[:6])
    await _edit(cq, f"📊 <b>Counts</b>\n\n<b>Global</b>\n{g}\n\n<b>Preflight</b>\n{p}\n\n"
                    f"<b>Per target</b>\n{t or '  (none)'}", proxies_kb())


# ── settings browser ──────────────────────────────────────────────────────────
def _fmt_value(key: str) -> str:
    v = getattr(CFG, key, "")
    if isinstance(v, bool):
        return "ON" if v else "OFF"
    if isinstance(v, float):
        return f"{v:g}"
    if key in ("mongo_uri",) and v:
        return "(set)"
    return str(v)


@router.callback_query(F.data == "btn_settings")
async def cq_settings(cq: CallbackQuery, rt: Runtime):
    await _edit(cq, "🛠 <b>Settings</b>\nEverything here is saved to <code>config.json</code> "
                    "immediately. Items marked ↻ need a restart.", settings_kb())


@router.callback_query(F.data.startswith("cat:"))
async def cq_settings_cat(cq: CallbackQuery, rt: Runtime):
    cat = cq.data.split(":", 1)[1]
    items = SETTINGS_SCHEMA.get(cat, [])
    body = "\n".join(f"{'↻ ' if k in _RESTART_KEYS else ''}<b>{_h(label)}</b>: "
                     f"<code>{_h(_fmt_value(k))}</code>" for k, label, *_ in items)
    await _edit(cq, f"🛠 <b>{_h(cat.capitalize())}</b>\n{body}\n\nTap a name to change it.",
                settings_cat_kb(cat))


@router.callback_query(F.data.startswith("set:"))
async def cq_setting_pick(cq: CallbackQuery, state: FSMContext, rt: Runtime):
    key = cq.data.split(":", 1)[1]
    meta = _SETTING_INDEX.get(key)
    if not meta:
        await _edit(cq, "Unknown setting.", settings_kb())
        return
    cat, label, kind, lo, hi = meta
    await state.update_data(setting_key=key)
    rng = f"\nAllowed: {lo} … {hi}" if kind in ("int", "float") else ""
    if kind == "bool":
        rng = "\nSend <code>on</code> or <code>off</code>."
    await _ask(cq, f"🛠 <b>{_h(label)}</b>\nCurrent: <code>{_h(_fmt_value(key))}</code>{rng}\n\n"
                   f"Send the new value.", state, BotStates.waiting_for_setting)


@router.message(BotStates.waiting_for_setting, F.text)
async def process_setting(message: Message, state: FSMContext, rt: Runtime):
    data = await state.get_data()
    await state.clear()
    key = data.get("setting_key")
    meta = _SETTING_INDEX.get(key or "")
    if not meta:
        await message.answer("That prompt expired.", reply_markup=settings_kb())
        return
    cat, label, kind, lo, hi = meta
    raw = (message.text or "").strip()
    try:
        if kind == "bool":
            val = raw.lower() in ("1", "on", "true", "yes", "y")
        elif kind == "int":
            val = int(float(raw))
            if not (lo <= val <= hi):
                raise ValueError(f"must be between {lo} and {hi}")
        elif kind == "float":
            val = float(raw)
            if not (lo <= val <= hi):
                raise ValueError(f"must be between {lo} and {hi}")
        else:
            val = raw
            if key == "output_mode" and val not in ("any", "all"):
                raise ValueError("must be 'any' or 'all'")
    except ValueError as exc:
        await message.answer(f"❌ {_h(exc)}", reply_markup=settings_cat_kb(cat))
        return

    setattr(CFG, key, val)
    if key in ("worker_count", "retry_worker_count", "preflight_worker_count",
               "browser_count", "contexts_per_browser"):
        CFG.auto_tune = False                    # a manual choice disables the autotuner
    save_config(CFG)
    rt.worker_limit = max(1, min(rt.worker_limit, CFG.worker_count))
    rt.retry_limit = min(rt.retry_limit, CFG.retry_worker_count)
    tail = "\n↻ Restart the daemon for this to take effect." if key in _RESTART_KEYS else ""
    await message.answer(f"✅ <b>{_h(label)}</b> = <code>{_h(_fmt_value(key))}</code>{tail}",
                         reply_markup=settings_cat_kb(cat))


# ── uptime / public URL ───────────────────────────────────────────────────────
@router.callback_query(F.data == "sys_uptime")
async def cq_uptime(cq: CallbackQuery, state: FSMContext, rt: Runtime):
    cur = CFG.uptimerobot_url or "(none)"
    await _ask(cq, f"⏱️ <b>UptimeRobot heartbeat</b>\nCurrent: <code>{_h(cur)}</code>\n\n"
                   f"Send the heartbeat URL to ping every "
                   f"{int(CFG.uptimerobot_interval_seconds)}s, or <code>off</code> to disable.\n\n"
                   f"<i>This is the outbound 'Heartbeat' monitor type. For an inbound HTTP "
                   f"monitor use 🌐 Public URL instead.</i>",
               state, BotStates.waiting_for_uptime)


@router.message(BotStates.waiting_for_uptime, F.text)
async def process_uptime(message: Message, state: FSMContext, rt: Runtime):
    await state.clear()
    url = (message.text or "").strip()
    if url.lower() in ("off", "none", "-", "disable"):
        CFG.uptimerobot_url = ""
        save_config(CFG)
        await message.answer("✅ Heartbeat pings disabled.", reply_markup=main_kb())
        return
    if not _valid_http_url(url):
        await message.answer("❌ That is not an http(s) URL.", reply_markup=main_kb())
        return
    CFG.uptimerobot_url = url
    save_config(CFG)
    ok = await HTTP.ping(url, timeout=10)
    await message.answer(f"✅ Saved. Test ping: {'reached' if ok else 'no response'}.",
                         reply_markup=main_kb())


@router.callback_query(F.data == "sys_public")
async def cq_public(cq: CallbackQuery, rt: Runtime):
    url = public_url_for_port(CFG.http_api_port)
    lines = ["🌐 <b>Public URL</b>"]
    if url:
        token = f"?token={CFG.http_api_token}" if CFG.http_api_token else ""
        lines += [f"<code>{_h(url)}/health{token}</code>", "",
                  "Point an UptimeRobot <b>HTTP(s)</b> monitor at that address."]
        if CFG.http_api_host in ("127.0.0.1", "localhost", "::1"):
            lines += ["", "⚠️ The endpoint is bound to loopback, so nothing outside can reach it. "
                          "Set <b>HTTP bind host</b> to <code>0.0.0.0</code> in 🛠 Settings → "
                          "Network (and set an HTTP token), then restart."]
        ok, msg = await asyncio.to_thread(make_port_public, CFG.http_api_port)
        lines += ["", f"Port visibility: {'✅ public' if ok else '⚠️ ' + _h(msg)}"]
    else:
        lines += ["Not running inside a GitHub Codespace, so there is no forwarded-port URL.",
                  "Use the outbound ⏱️ Uptime URL heartbeat instead."]
    await _edit(cq, "\n".join(lines), back_kb("btn_manage"))


# ── codespace ─────────────────────────────────────────────────────────────────
@router.callback_query(F.data == "btn_codespace")
async def cq_codespace(cq: CallbackQuery, rt: Runtime):
    await _edit(cq, "💻 <b>Codespace</b>\nStopping the Codespace also stops this bot — "
                    "you will need the GitHub UI or the gh CLI to start it again.", codespace_kb())


@router.callback_query(F.data == "cs_info")
async def cq_cs_info(cq: CallbackQuery, rt: Runtime):
    info = await asyncio.to_thread(codespace_info)
    body = "\n".join(f"{_h(k)}: <code>{_h(v)}</code>" for k, v in info.items())
    await _edit(cq, f"ℹ️ <b>Codespace</b>\n{body}", codespace_kb())


@router.callback_query(F.data == "cs_rename")
async def cq_cs_rename(cq: CallbackQuery, state: FSMContext, rt: Runtime):
    await _ask(cq, "Send the new display name for this Codespace.", state, BotStates.waiting_for_rename)


@router.message(BotStates.waiting_for_rename, F.text)
async def process_rename(message: Message, state: FSMContext, rt: Runtime):
    await state.clear()
    name = (message.text or "").strip()[:60]
    if not name:
        await message.answer("Empty name ignored.", reply_markup=codespace_kb())
        return
    ok, msg = await asyncio.to_thread(codespace_rename, name)
    if ok:
        CFG.codespace_name = CFG.codespace_name or codespace_name()
        save_config(CFG)
    await message.answer(("✅ " if ok else "❌ ") + _h(msg), reply_markup=codespace_kb())


# ── confirmations for destructive actions ─────────────────────────────────────
_CONFIRM_TEXT = {
    "restart": "🔁 Restart the daemon now? Testing stops for a few seconds; the tmux wrapper "
               "brings it straight back.",
    "stop": "🛑 Force-stop the daemon? It will NOT restart by itself — you will need terminal "
            "access (or the tmux wrapper) to start it again.",
    "cs_stop": "🔌 Stop the whole Codespace? Everything including this bot goes offline until you "
               "start it from GitHub.",
    "purge": "🧹 Delete proxies that have been dead for "
             f"{CFG.purge_dead_after_days:g} days? Their history goes too. Proxies that ever "
             "worked are never deleted.",
    "reset_failed": "♻️ Move every FAILED pair back to UNTESTED so they are retried from scratch?",
    "reset_pf": "🔁 Re-run preflight for every proxy (clears all alive/dead verdicts)?",
}


@router.callback_query(F.data.startswith("ask_"))
async def cq_confirm(cq: CallbackQuery, rt: Runtime):
    action = cq.data.split("_", 1)[1]
    await _edit(cq, _CONFIRM_TEXT.get(action, "Are you sure?"), confirm_kb(action))


@router.callback_query(F.data.startswith("do:"))
async def cq_do(cq: CallbackQuery, rt: Runtime):
    action = cq.data.split(":", 1)[1]
    if action == "restart":
        await _edit(cq, "🔁 Restarting… the live status will reconnect shortly.", None)
        rt.restart_requested = True
        rt.stop_event.set()
    elif action == "stop":
        await _edit(cq, "🛑 Stopping. Start it again with "
                        "<code>python3 main.py tmux start</code>.", None)
        rt.restart_requested = False
        rt.stop_event.set()
    elif action == "cs_stop":
        # Tell the operator BEFORE the call - stopping the Codespace kills this process.
        await _edit(cq, "🔌 Requesting Codespace shutdown…", None)
        ok, msg = await asyncio.to_thread(codespace_stop)
        await _notify(rt, ("✅ " if ok else "❌ ") + msg, key="cs_stop")
        if ok:
            rt.stop_event.set()
    elif action == "purge":
        n = await rt.store.purge_dead(CFG.purge_dead_after_days, CFG.purge_dead_min_fails)
        await _edit(cq, f"🧹 Purged {n:,} dead proxies.", proxies_kb())
    elif action == "reset_failed":
        n = await rt.store.reset_states("failed")
        await _edit(cq, f"♻️ {n:,} pairs are queued for a fresh test.", proxies_kb())
    elif action == "reset_pf":
        n = await rt.store.reset_states("preflight")
        await _edit(cq, f"🔁 {n:,} proxies will be re-probed.", proxies_kb())
    else:
        await _edit(cq, "Unknown action.", main_kb())


# ── catch-all so a stray message is never silently swallowed ──────────────────
@router.message(F.text)
async def fallback_text(message: Message, rt: Runtime):
    await message.answer("Use /start for the control panel, or send a <code>.txt</code> "
                         "file to import proxies.", reply_markup=main_kb())


# ══════════════════════════════════════════════════════════════════════════════
#  LIVE STATUS LOOP
#  Edits a single message.  A local hash is compared first, so an unchanged status
#  costs zero Telegram calls, and the interval backs off while nothing moves.
# ══════════════════════════════════════════════════════════════════════════════
async def live_status_updater(rt: Runtime):
    while not rt.stop_event.is_set():
        interval = CFG.live_status_interval
        if rt.bot and rt.live_status_msg_id and rt.live_status_chat_id:
            try:
                text = await render_status(rt)
                digest = hashlib.sha1(text.encode()).hexdigest()
                if digest != rt._live_hash:
                    await rt.bot.edit_message_text(_clip(text), chat_id=rt.live_status_chat_id,
                                                   message_id=rt.live_status_msg_id,
                                                   reply_markup=main_kb())
                    rt._live_hash = digest
                    rt._live_unchanged = 0
                else:
                    rt._live_unchanged += 1
                if rt._live_unchanged >= 6:
                    interval = CFG.live_status_idle_interval
            except TelegramBadRequest:
                rt._live_hash = ""                      # message vanished or is not modified
            except TelegramRetryAfter as exc:
                await _sleep_or_stop(rt, float(getattr(exc, "retry_after", 5)) + 1)
                continue
            except TelegramForbiddenError:
                rt.live_status_msg_id = None            # blocked / kicked: stop trying
            except asyncio.CancelledError:
                raise
            except Exception:
                elog.error("live status update failed", exc_info=True)
        await _sleep_or_stop(rt, interval)


async def bot_polling_supervisor(rt: Runtime, dp) -> None:
    """Restarts long-polling with back-off instead of dying quietly on a network blip."""
    delay = 5.0
    while not rt.stop_event.is_set():
        try:
            await dp.start_polling(rt.bot, rt=rt, handle_signals=False, close_bot_session=False)
            return
        except asyncio.CancelledError:
            raise
        except TelegramUnauthorizedError:
            fatal("telegram bot token rejected - bot control is disabled")
            return
        except Exception as exc:
            elog.error("telegram polling crashed (%s: %.200s) - retry in %.0fs",
                       type(exc).__name__, exc, delay)
            await _sleep_or_stop(rt, delay)
            delay = min(delay * 2, 300.0)


# ══════════════════════════════════════════════════════════════════════════════
#  PREFLIGHT POOL  (stage 1 + stage 2)
#  Hundreds of tiny asyncio sockets.  Everything that fails here never costs a
#  browser context, which is what makes a 40k proxy list tractable.
# ══════════════════════════════════════════════════════════════════════════════
async def preflight_worker(rt: Runtime):
    rt.preflight_workers_alive += 1
    try:
        while not rt.stop_event.is_set():
            if rt.paused:
                await _sleep_or_stop(rt, 2.0)
                continue
            try:
                pid, proxy, scheme_hint = await asyncio.wait_for(rt.preflight_queue.get(), timeout=1.0)
            except asyncio.TimeoutError:
                continue
            try:
                t0 = time.monotonic()
                # Stage 1: is anything listening at all?
                alive = await tcp_preflight(proxy, CFG.tcp_preflight_timeout)
                scheme = None
                if alive and CFG.handshake_probe_enabled:
                    # Stage 2: does it actually speak a proxy protocol, and which one?
                    declared = scheme_hint or urlparse(proxy).scheme or "http"
                    scheme = await detect_protocol(proxy, declared, CFG.handshake_timeout)
                    alive = scheme is not None
                elif alive:
                    scheme = scheme_hint or urlparse(proxy).scheme or "http"
                latency = round(time.monotonic() - t0, 3) if alive else None
                await rt.store.mark_preflight(pid, alive, scheme, latency)
                rt.preflight_done += 1
                if alive:
                    rt.preflight_alive += 1
            except asyncio.CancelledError:
                raise
            except Exception:
                elog.error("preflight failed for %s", mask_proxy(proxy), exc_info=True)
                with contextlib.suppress(Exception):
                    await rt.store.mark_preflight(pid, False, None, None)
            finally:
                rt.preflight_queue.task_done()
            
            # Added a strict delay to prevent network bursts and CPU spikes
            await asyncio.sleep(0.5)
    finally:
        rt.preflight_workers_alive = max(0, rt.preflight_workers_alive - 1)


async def preflight_scheduler(rt: Runtime):
    while not rt.stop_event.is_set():
        try:
            if not rt.paused and rt.preflight_queue.qsize() < CFG.preflight_worker_count:
                room = rt.preflight_queue.maxsize - rt.preflight_queue.qsize()
                batch = await rt.store.claim_preflight_batch(max(1, min(room, CFG.preflight_worker_count)))
                for item in batch:
                    await rt.preflight_queue.put(item)
                if not batch:
                    await _sleep_or_stop(rt, 5.0)       # nothing due: idle politely
                    continue
        except asyncio.CancelledError:
            raise
        except Exception:
            elog.error("preflight scheduling failed", exc_info=True)
        await _sleep_or_stop(rt, 2.0)


# ══════════════════════════════════════════════════════════════════════════════
#  BROWSER WORKER POOLS
#  Two pools sharing one browser pool:
#    * "fresh" - pairs that have never been tested against this target
#    * "retry" - pairs with a prior verdict whose cooldown expired (failed ones to
#                give them another chance, working ones to re-verify they still work)
# ══════════════════════════════════════════════════════════════════════════════
async def browser_worker(wid: int, rt: Runtime, kind: str) -> None:
    queue = rt.queue if kind == "fresh" else rt.retry_queue
    if kind == "fresh":
        rt.workers_alive += 1
    else:
        rt.retry_workers_alive += 1
    try:
        while not rt.stop_event.is_set():
            limit = rt.worker_limit if kind == "fresh" else rt.retry_limit
            if wid >= limit or rt.paused:
                await _sleep_or_stop(rt, 2.0)
                continue
            try:
                item = await asyncio.wait_for(queue.get(), timeout=1.0)
            except asyncio.TimeoutError:
                continue

            pid, proxy, scheme, tid = item
            if kind == "fresh":
                rt.workers_busy += 1
            else:
                rt.retry_workers_busy += 1
            # Exactly one task_done() per get(): it lives in the finally below and
            # every early `continue` inside the try passes through it.
            try:
                target = rt.registry.get(tid)
                if not target or not target.enabled:
                    await rt.store.release_claims([(pid, tid)])
                    continue

                await asyncio.sleep(random.uniform(CFG.connect_jitter_min, CFG.connect_jitter_max))
                acq = await rt.pool.acquire(timeout=45.0)
                if not acq:
                    # No browser slot: hand the item back, or release the claim if the
                    # queue filled up meanwhile, so it is never lost or double-claimed.
                    try:
                        queue.put_nowait(item)
                    except asyncio.QueueFull:
                        await rt.store.release_claims([(pid, tid)])
                    continue

                bid, browser = acq
                effective = apply_scheme(proxy, scheme or None)     # use the proven protocol
                profile = make_profile(rt.browser_version)
                res = None
                try:
                    res = await validate_proxy(browser, effective, target, profile)
                finally:
                    await rt.pool.release(bid, crashed=bool(res and res.browser_crashed))

                rt.tests_done += 1
                if res.status == "WORKING":
                    rt.tests_ok += 1
                vlog.info("%s %s %s %s http=%s %.2fs %s", kind, tid, mask_proxy(effective),
                          res.status, res.http_status, res.elapsed_seconds or 0.0,
                          (res.error or "")[:120])

                _new, prior_success = await rt.store.record(pid, tid, res, wid, bid, target.cooldowns)
                rt.netguard.record(tid, pid, res.status)

                # prior_success tells the breaker "this proxy used to work here", which is
                # how it distinguishes a broken target from a batch of broken proxies.
                forgive, event = rt.circuit.record(tid, pid, res.status, prior_success)
                if forgive:
                    await rt.store.forgive(forgive, CFG.circuit_cooldown)
                if event == "tripped":
                    rt.circuit_trips += 1
                    await _notify(rt, f"🔌 Circuit breaker tripped for <b>{_h(tid)}</b> — "
                                      f"the target looks down, so testing pauses for it and the "
                                      f"affected proxies keep their scores.", key=f"cb:{tid}")

            except asyncio.CancelledError:
                raise
            except Exception:
                elog.error("%s worker %d failed on %s", kind, wid, mask_proxy(proxy), exc_info=True)
                with contextlib.suppress(Exception):
                    await rt.store.release_claims([(pid, tid)])
            finally:
                if kind == "fresh":
                    rt.workers_busy = max(0, rt.workers_busy - 1)
                else:
                    rt.retry_workers_busy = max(0, rt.retry_workers_busy - 1)
                queue.task_done()
    finally:
        if kind == "fresh":
            rt.workers_alive = max(0, rt.workers_alive - 1)
        else:
            rt.retry_workers_alive = max(0, rt.retry_workers_alive - 1)


async def _fill_queue(rt: Runtime, queue: asyncio.Queue, kind: str, cursor_attr: str) -> None:
    """Round-robin over enabled targets so one busy target cannot starve the others."""
    live = rt.registry.enabled()
    if not live:
        return
    cursor = getattr(rt, cursor_attr) % len(live)
    live = live[cursor:] + live[:cursor]
    setattr(rt, cursor_attr, cursor + 1)
    for t in live:
        free = queue.maxsize - queue.qsize()
        if free <= 0:
            return
        if rt.circuit.blocked(t.target_id):
            continue
        want = rt.circuit.reserve(t.target_id, min(free, CFG.batch_size_per_tick))
        if want <= 0:
            continue
        for pid, proxy, scheme in await rt.store.claim_batch(t.target_id, want, kind):
            await queue.put((pid, proxy, scheme, t.target_id))


async def scheduler_loop(rt: Runtime):
    """Fresh-test scheduler; also owns target hot-reload and the RAM autoscaler."""
    while not rt.stop_event.is_set():
        if rt.paused:
            await _sleep_or_stop(rt, 2.0)
            continue
        try:
            if rt.registry.changed():
                if rt.registry.reload():
                    await rt.store.sync_targets(list(rt.registry.targets.values()))
                    log.info("targets reloaded: %d enabled", len(rt.registry.enabled()))

            await _fill_queue(rt, rt.queue, "fresh", "_target_cursor")

            # RAM autoscaler: it only moves the *live* limits inside 1..configured,
            # so it can never fight an explicit Speed Up / Speed Down choice.
            if psutil:
                mem = psutil.virtual_memory().percent
                if mem > CFG.memory_high_percent:
                    rt.worker_limit = max(1, rt.worker_limit - 1)
                    rt.retry_limit = max(0, rt.retry_limit - 1)
                elif mem < 60:
                    rt.worker_limit = min(rt.worker_limit + 1, CFG.worker_count)
                    rt.retry_limit = min(rt.retry_limit + 1, CFG.retry_worker_count)
            rt.worker_limit = max(1, min(rt.worker_limit, CFG.worker_count))
            rt.retry_limit = max(0, min(rt.retry_limit, CFG.retry_worker_count))
        except asyncio.CancelledError:
            raise
        except Exception:
            elog.error("scheduler tick failed", exc_info=True)
        await _sleep_or_stop(rt, CFG.scheduler_tick_seconds)


async def retry_scheduler_loop(rt: Runtime):
    """Feeds the dedicated retry pool.  Runs a little slower than the fresh
    scheduler because retry candidates only become due as cooldowns expire."""
    while not rt.stop_event.is_set():
        if rt.paused or CFG.retry_worker_count <= 0:
            await _sleep_or_stop(rt, 3.0)
            continue
        try:
            await _fill_queue(rt, rt.retry_queue, "retry", "_retry_cursor")
        except asyncio.CancelledError:
            raise
        except Exception:
            elog.error("retry scheduler tick failed", exc_info=True)
        await _sleep_or_stop(rt, max(CFG.scheduler_tick_seconds, 5.0))


async def supervisor_loop(rt: Runtime, groups: list[tuple[str, list]]) -> None:
    """Restarts any browser worker that dies, with a one-second floor so a worker
    that fails instantly cannot spin the event loop."""
    while not rt.stop_event.is_set():
        watch = [t for _, tasks in groups for t in tasks]
        if not watch:
            await _sleep_or_stop(rt, 5.0)
            continue
        done, _ = await asyncio.wait(watch, return_when=asyncio.FIRST_COMPLETED)
        if rt.stop_event.is_set():
            return
        restarted = False
        for kind, tasks in groups:
            for i, w in enumerate(tasks):
                if w in done:
                    exc = None if w.cancelled() else w.exception()
                    if exc is not None:
                        elog.error("%s worker-%d died (%s: %s) - restarting",
                                   kind, i, type(exc).__name__, exc)
                    rt.worker_restarts += 1
                    tasks[i] = asyncio.create_task(browser_worker(i, rt, kind),
                                                   name=f"{kind}-worker-{i}")
                    restarted = True
        if restarted:
            await _sleep_or_stop(rt, 1.0)


# ══════════════════════════════════════════════════════════════════════════════
#  BACKGROUND TASKS
# ══════════════════════════════════════════════════════════════════════════════
async def pool_guard_loop(rt: Runtime):
    """Keeps the browser pool at strength and drives the local-network probe."""
    while not rt.stop_event.is_set():
        try:
            await rt.pool.ensure_capacity()
            forgive = await rt.netguard.check()
            if forgive:
                n = await rt.store.forgive(forgive, CFG.circuit_cooldown)
                await _notify(rt, f"📡 Local network outage detected — testing paused and "
                                  f"{n} results were forgiven.", key="netdown")
            elif rt.netguard.was_down and not rt.netguard.down:
                rt.netguard.was_down = False
                await _notify(rt, "📡 Network restored — testing resumed.", key="netup")
        except asyncio.CancelledError:
            raise
        except Exception:
            elog.error("pool guard failed", exc_info=True)
        # Probe faster while the network is suspect so testing resumes promptly.
        await _sleep_or_stop(rt, 5.0 if (rt.netguard.down or rt.netguard.suspect) else 15.0)


async def fallback_loop(rt: Runtime):
    """Tops the pond up from the configured sources when validated proxies run low."""
    if CFG.fetch_on_start and CFG.fallback_urls:
        await _sleep_or_stop(rt, 10.0)
        if not rt.stop_event.is_set():
            await _force_fetch_task(rt)
    while not rt.stop_event.is_set():
        await _sleep_or_stop(rt, CFG.fallback_cooldown_seconds)
        if rt.stop_event.is_set() or not CFG.fallback_urls:
            return
        try:
            stats = await rt.store.stats()
            working = stats["global"].get("WORKING", 0)
            if working < CFG.fallback_min_working:
                proxies = await fetch_fallback_proxies(CFG.fallback_urls)
                if proxies:
                    r = await rt.store.ingest_proxies(proxies)
                    log.info("auto-fetch: %d proxies, %d new", len(proxies), r["inserted"])
                    await _notify(rt, f"🔄 Auto-fetched {len(proxies):,} proxies "
                                      f"({r['inserted']:,} new) — working count was {working}.",
                                  key="autofetch")
        except asyncio.CancelledError:
            raise
        except Exception:
            elog.error("fallback fetch failed", exc_info=True)


async def uptimerobot_task(rt: Runtime):
    """Outbound heartbeat.  Pairs with an UptimeRobot 'Heartbeat' monitor; the
    inbound HTTP(s) monitor option is the forwarded-port URL instead."""
    while not rt.stop_event.is_set():
        url = CFG.uptimerobot_url
        if url and _valid_http_url(url):
            ok = await HTTP.ping(url, timeout=15)
            if not ok:
                elog.warning("uptime heartbeat did not go through")
        await _sleep_or_stop(rt, max(30.0, CFG.uptimerobot_interval_seconds))


_REMOTE_UA_URL = "https://raw.githubusercontent.com/intoli/user-agents/master/src/user-agents.json.gz"
_UA_PLATFORM = {"Windows": "Win32", "macOS": "MacIntel", "Linux": "Linux x86_64"}
_UA_OS_TOKEN = {"Windows": "Windows NT", "macOS": "Macintosh", "Linux": "X11; Linux"}


def _filter_remote_uas(data, os_name: str) -> list:
    """Keep only desktop Chrome UAs for the host OS, so the advertised UA can never
    contradict the real Chromium we launch."""
    want = _UA_PLATFORM.get(os_name)
    token = _UA_OS_TOKEN.get(os_name, "")
    out = []
    for item in data if isinstance(data, list) else []:
        if not isinstance(item, dict):
            continue
        ua = item.get("userAgent")
        if not ua or item.get("deviceCategory") != "desktop" or item.get("platform") != want:
            continue
        if token not in ua:
            continue
        if "Chrome/" not in ua or any(x in ua for x in ("Edg/", "OPR/", "Firefox/", "Mobile")):
            continue
        out.append(ua)
    return out


async def _ua_refresh_once(rt: Runtime) -> int:
    raw = await HTTP.get_bytes(_REMOTE_UA_URL)
    if not raw:
        return 0
    try:
        data = json.loads(gzip.decompress(raw))
    except Exception:
        return 0
    uas = _filter_remote_uas(data, _host_os())
    if uas:
        _REMOTE_UA_LIST[:] = uas
        log.info("remote UA pool loaded: %d entries", len(uas))
    return len(uas)


async def ua_refresh_loop(rt: Runtime) -> None:
    while not rt.stop_event.is_set():
        if CFG.ua_pool_remote:
            with contextlib.suppress(Exception):
                await _ua_refresh_once(rt)
        await _sleep_or_stop(rt, max(300.0, CFG.ua_pool_refresh_seconds))


async def metrics_loop(rt: Runtime) -> None:
    while not rt.stop_event.is_set():
        try:
            stats = await rt.store.stats()
            out = {
                "version": VERSION,
                "uptime_seconds": int(time.time() - rt.daemon_started),
                "paused": rt.paused, "pause_state": rt.pause_text(),
                "proxies_total": stats["proxies_total"], "global": stats["global"],
                "preflight": stats["preflight"], "schemes": stats["schemes"],
                "targets": stats["targets"], "in_flight": stats["in_flight"], "due": stats["due"],
                "queue_fresh": rt.queue.qsize(), "queue_retry": rt.retry_queue.qsize(),
                "queue_preflight": rt.preflight_queue.qsize(),
                "workers_fresh_busy": rt.workers_busy, "workers_retry_busy": rt.retry_workers_busy,
                "workers_fresh_spawned": rt.workers_alive,
                "workers_retry_spawned": rt.retry_workers_alive,
                "workers_preflight": rt.preflight_workers_alive,
                "worker_limit": rt.worker_limit, "retry_limit": rt.retry_limit,
                "browsers": len(rt.pool.recs), "circuits": rt.circuit.state_dict(),
                "network_down": rt.netguard.down, "circuit_trips": rt.circuit_trips,
                "worker_restarts": rt.worker_restarts, "browser_restarts": rt.pool.restarts,
                "tests_done": rt.tests_done, "tests_ok": rt.tests_ok,
                "preflight_done": rt.preflight_done, "preflight_alive": rt.preflight_alive,
            }
            _atomic_write(_rp(CFG.metrics_file), json.dumps(out, indent=2))
        except asyncio.CancelledError:
            raise
        except Exception:
            elog.error("metrics write failed", exc_info=True)
        await _sleep_or_stop(rt, max(5.0, CFG.metrics_interval_seconds))


def _format_output(per_target: dict, flat: list) -> str:
    lines = [f"# validated_proxies.txt - radiate v{VERSION}",
             "# Proxies below passed the full browser validation for the listed target(s).",
             f"# generated {time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime())}", "",
             f"# ---- all targets (mode={CFG.output_mode}) ----"]
    lines.extend(flat)
    lines.append("")
    for tid, plist in sorted(per_target.items()):
        label = ("preflight-only: port answers as a proxy, NOT browser-validated"
                 if tid == "_preflight_only" else f"target: {tid}")
        lines.append(f"# ---- {label} ({len(plist)}) ----")
        lines.extend(plist)
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


async def output_loop(rt: Runtime) -> None:
    """Rewrites the output file only when its content actually changed."""
    last_sig = None
    while not rt.stop_event.is_set():
        try:
            per_target, flat = await rt.store.working_lists(CFG.output_mode, CFG.output_max_age_seconds)
            content = _format_output(per_target, flat)
            sig = hashlib.sha1(content.encode()).hexdigest()
            if sig != last_sig:
                _atomic_write(OUTPUT_FILE, content)
                last_sig = sig
        except asyncio.CancelledError:
            raise
        except Exception:
            elog.error("output write failed", exc_info=True)
        await _sleep_or_stop(rt, max(5.0, CFG.output_flush_interval))


async def maintenance_loop(rt: Runtime) -> None:
    last_backup = 0.0
    last_sig = proxy_files_signature()
    next_tick = time.time() + 30.0
    while not rt.stop_event.is_set():
        delay = next_tick - time.time()
        if delay > 0:
            await _sleep_or_stop(rt, delay)
        if rt.stop_event.is_set():
            return
        next_tick = time.time() + CFG.maintenance_interval_seconds
        try:
            if CFG.proxy_file_watch:
                sig = proxy_files_signature()
                if sig != last_sig:
                    last_sig = sig
                    proxies = await asyncio.to_thread(load_all_proxy_files)
                    if proxies:
                        r = await rt.store.ingest_proxies(proxies)
                        log.info("proxy files changed: %d new", r["inserted"])

            await rt.store.prune_history(CFG.history_retention_days)
            if CFG.purge_dead_after_days > 0:
                n = await rt.store.purge_dead(CFG.purge_dead_after_days, CFG.purge_dead_min_fails)
                if n:
                    log.info("purged %d long-dead proxies", n)
            await rt.store.checkpoint()
            cleanup_sessions(7)
            cleanup_uploads()

            if time.time() - last_backup >= CFG.backup_interval_hours * 3600:
                last_backup = time.time()
                if await rt.store.integrity() != "ok":
                    await _notify(rt, "⚠️ SQLite integrity check failed — see logs/errors.log",
                                  key="dbintegrity")
                await rt.store.backup(BACKUP_DIR, CFG.backup_keep)
        except asyncio.CancelledError:
            raise
        except Exception:
            elog.error("maintenance failed", exc_info=True)


async def mongo_loop(rt: Runtime) -> None:
    while not rt.stop_event.is_set():
        if CFG.mongo_enabled and CFG.mongo_uri:
            try:
                ok = await MONGO.sync(rt.store)
                if not ok and MONGO.last_error:
                    elog.warning("mongo sync failed: %s", MONGO.last_error)
            except asyncio.CancelledError:
                raise
            except Exception:
                elog.error("mongo sync crashed", exc_info=True)
        await _sleep_or_stop(rt, max(30.0, CFG.mongo_sync_interval_seconds))


async def keepalive_loop(rt: Runtime) -> None:
    """Real, cheap activity: touch a heartbeat file and self-ping the health endpoint.
    A thread that merely slept (as in v6.1) did nothing at all."""
    while not rt.stop_event.is_set():
        with contextlib.suppress(OSError):
            HEARTBEAT_FILE.write_text(str(int(time.time())), encoding="utf-8")
        if CFG.http_api_enabled:
            host = "127.0.0.1" if CFG.http_api_host in ("0.0.0.0", "::") else CFG.http_api_host
            url = f"http://{host}:{CFG.http_api_port}/health"
            if CFG.http_api_token:
                url += f"?token={CFG.http_api_token}"
            with contextlib.suppress(Exception):
                await HTTP.ping(url, timeout=5)
        await _sleep_or_stop(rt, max(30.0, CFG.keepalive_interval_seconds))


# ── tiny HTTP endpoint (/health, /stats, /metrics) ────────────────────────────
async def http_health_server(reader, writer, rt: Runtime):
    try:
        raw = (await asyncio.wait_for(reader.readline(), timeout=3.0)).decode(errors="replace").strip()
        path = raw.split(" ")[1] if len(raw.split(" ")) > 1 else "/"
        base, _, query = path.partition("?")
        token = ""
        for part in query.split("&"):
            if part.startswith("token="):
                token = part[6:]
        # When the endpoint is reachable from outside, a token is mandatory.
        local = CFG.http_api_host in ("127.0.0.1", "localhost", "::1")
        if not local and CFG.http_api_token and token != CFG.http_api_token:
            status, body = "401 Unauthorized", '{"error":"token required"}'
        elif base == "/health":
            status, body = "200 OK", json.dumps({"status": "ok", "version": VERSION,
                                                 "paused": rt.paused, "ts": time.time()})
        elif base in ("/stats", "/metrics"):
            st = await rt.store.stats()
            status = "200 OK"
            body = json.dumps({"version": VERSION, "global": st["global"],
                               "preflight": st["preflight"], "targets": st["targets"],
                               "in_flight": st["in_flight"], "due": st["due"],
                               "queue_fresh": rt.queue.qsize(), "queue_retry": rt.retry_queue.qsize(),
                               "workers_fresh": rt.workers_busy, "workers_retry": rt.retry_workers_busy,
                               "browsers": len(rt.pool.recs), "circuits": rt.circuit.state_dict(),
                               "uptime_seconds": int(time.time() - rt.daemon_started)})
        else:
            status, body = "404 Not Found", '{"error":"not found"}'
        payload = body.encode("utf-8")
        writer.write((f"HTTP/1.1 {status}\r\nContent-Type: application/json\r\n"
                      f"Cache-Control: no-store\r\nContent-Length: {len(payload)}\r\n"
                      f"Connection: close\r\n\r\n").encode() + payload)
        await writer.drain()
    except Exception:
        pass
    finally:
        with contextlib.suppress(Exception):
            writer.close()
            await writer.wait_closed()


# ══════════════════════════════════════════════════════════════════════════════
#  GIT AUTO-UPDATE
#  Fast-forward only, never touches local edits, installs new requirements and
#  restarts through the tmux wrapper when the code itself changed.
# ══════════════════════════════════════════════════════════════════════════════
def _git(args: list, cwd: Path = ROOT, check: bool = False) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(["git", *args], cwd=str(cwd), capture_output=True, text=True,
                              check=check, timeout=120)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(["git", *args], 124, "", "git command timed out")
    except FileNotFoundError:
        return subprocess.CompletedProcess(["git", *args], 127, "", "git is not installed")


def git_is_repo() -> bool:
    return (ROOT / ".git").exists()


def _snapshot_rel() -> Optional[str]:
    try:
        return (STATE_DIR / "snapshot.json").relative_to(ROOT).as_posix()
    except ValueError:
        return None


def _runtime_files() -> set:
    """Files the daemon rewrites itself must never block an update."""
    out = set()
    rel = _snapshot_rel()
    if rel:
        out.add(rel)
    with contextlib.suppress(ValueError):
        out.add(_rp(CFG.metrics_file).relative_to(ROOT).as_posix())
    return out


def _code_files() -> tuple:
    return (Path(__file__).name, "requirements.txt")


def git_pull_and_check() -> dict:
    if not git_is_repo():
        return {"ok": False, "error": "not a git repository"}
    status = _git(["status", "--porcelain", "--untracked-files=no"])
    runtime = _runtime_files()
    dirty = [ln[3:].strip().strip('"') for ln in status.stdout.splitlines() if ln.strip()]
    dirty = [f for f in dirty if f not in runtime]
    if dirty:
        return {"ok": False, "error": "local changes present: " + ", ".join(dirty[:5])}
    fetch = _git(["fetch", CFG.git_remote, CFG.git_branch])
    if fetch.returncode != 0:
        return {"ok": False, "error": f"fetch failed: {fetch.stderr.strip()[:300]}"}
    before = _git(["rev-parse", "HEAD"]).stdout.strip()
    merge = _git(["merge", "--ff-only", f"{CFG.git_remote}/{CFG.git_branch}"])
    if merge.returncode != 0:
        return {"ok": False, "error": f"fast-forward failed: {merge.stderr.strip()[:300]}"}
    after = _git(["rev-parse", "HEAD"]).stdout.strip()
    if before == after:
        return {"ok": True, "changed": False}
    diff = _git(["diff", "--name-only", before, after]).stdout.split()
    return {"ok": True, "changed": True, "before": before[:8], "after": after[:8], "files": diff,
            "code_changed": any(f in _code_files() for f in diff)}


def requirements_hash() -> Optional[str]:
    req = ROOT / "requirements.txt"
    return hashlib.sha1(req.read_bytes()).hexdigest() if req.exists() else None


def pip_install_if_changed() -> bool:
    h = requirements_hash()
    if h is None:
        return False
    prev = DEPS_STAMP.read_text().strip() if DEPS_STAMP.exists() else None
    if h == prev:
        return False
    r = subprocess.run([sys.executable, "-m", "pip", "install", "--break-system-packages", "-q",
                        "-r", str(ROOT / "requirements.txt")], capture_output=True, text=True)
    if r.returncode != 0:
        glog.error("pip install failed: %s", (r.stderr or r.stdout).strip()[-300:])
        return False                                   # no stamp written, so the next update retries
    _atomic_write(DEPS_STAMP, h)
    return True


async def git_watch_loop(rt: Runtime) -> None:
    if not (CFG.git_enabled and git_is_repo()):
        return
    write_gitignore()
    last_push = time.time()
    while not rt.stop_event.is_set():
        await _sleep_or_stop(rt, CFG.git_check_interval_seconds)
        if rt.stop_event.is_set():
            return
        try:
            res = await asyncio.to_thread(git_pull_and_check)
            if not res.get("ok"):
                glog.warning("git update skipped: %s", res.get("error"))
            elif res.get("changed"):
                glog.info("git update %s -> %s: %s", res["before"], res["after"],
                          ", ".join(res["files"]))
                await asyncio.to_thread(pip_install_if_changed)
                if res["code_changed"] and CFG.git_auto_restart:
                    await _notify(rt, "🔄 Code updated from GitHub — restarting to apply it.",
                                  key="gitrestart")
                    rt.restart_requested = True
                    rt.stop_event.set()
                    return
            if CFG.git_push_state and time.time() - last_push >= CFG.git_push_interval_seconds:
                await push_state_snapshot(rt.store)
                last_push = time.time()
        except asyncio.CancelledError:
            raise
        except Exception:
            glog.error("git watch iteration failed", exc_info=True)


def _commit_and_push_snapshot(rel: str) -> None:
    if _git(["add", "--", rel]).returncode != 0:
        glog.warning("state snapshot: git add failed for %s", rel)
        return
    if _git(["diff", "--cached", "--quiet", "--", rel]).returncode == 0:
        return
    msg = f"state snapshot {time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime())}"
    commit = _git(["commit", "-m", msg, "--", rel])        # path-limited on purpose
    if commit.returncode != 0:
        glog.warning("state snapshot: commit failed: %s", (commit.stderr or commit.stdout).strip()[:300])
        return
    push = _git(["push", CFG.git_remote, CFG.git_branch])
    if push.returncode != 0:
        glog.warning("state snapshot: push failed: %s", push.stderr.strip()[:300])
        # Drop our own commit so the branch can still fast-forward next time.
        if _git(["log", "-1", "--format=%s"]).stdout.strip().startswith("state snapshot"):
            _git(["reset", "--mixed", "HEAD~1"])


async def push_state_snapshot(store: Store) -> None:
    data = await store.export_state(mask=True)
    _atomic_write(STATE_DIR / "snapshot.json", json.dumps(data, indent=2))
    if not git_is_repo():
        return
    rel = _snapshot_rel()
    if rel is None:
        glog.warning("state snapshot not pushed: state_dir is outside the repository")
        return
    await asyncio.to_thread(_commit_and_push_snapshot, rel)


# ══════════════════════════════════════════════════════════════════════════════
#  SINGLE-INSTANCE LOCK
# ══════════════════════════════════════════════════════════════════════════════
class InstanceLock:
    def __init__(self, path: Path) -> None:
        self.path = path
        self._fh = None

    def acquire(self) -> bool:
        self._fh = open(self.path, "a+")
        if fcntl is not None:
            try:
                fcntl.flock(self._fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError:
                return False
        self._fh.seek(0)
        self._fh.truncate()
        self._fh.write(str(os.getpid()))
        self._fh.flush()
        return True

    def release(self) -> None:
        if self._fh:
            with contextlib.suppress(Exception):
                if fcntl is not None:
                    fcntl.flock(self._fh.fileno(), fcntl.LOCK_UN)
                self._fh.close()


def _launch_args() -> list[str]:
    """Chromium flags tuned for a headless container: no GPU, no crash reporter,
    capped JS heap so a leak in one context cannot eat the whole box."""
    args = [
        "--disable-features=Translate,BackForwardCache,AcceptCHFrame",
        "--disable-gpu", "--no-first-run", "--no-default-browser-check",
        "--disable-background-timer-throttling", "--disable-renderer-backgrounding",
        "--disable-backgrounding-occluded-windows", "--disable-breakpad",
        "--disable-component-update", "--mute-audio",
        "--js-flags=--max-old-space-size=384",
    ]
    if CFG.chromium_no_sandbox:
        args += ["--no-sandbox", "--disable-dev-shm-usage"]
    return args


# ══════════════════════════════════════════════════════════════════════════════
#  DAEMON
# ══════════════════════════════════════════════════════════════════════════════
async def run_daemon() -> int:
    restart = False
    if not PLAYWRIGHT_OK:
        fatal("playwright is not installed - run: pip install playwright && playwright install chromium")
        return 1

    fd_limit = raise_fd_limit()
    CFG.preflight_worker_count = fd_budget_for_preflight(fd_limit)
    if psutil is None:
        log.warning("psutil is not installed - RAM autoscaling and CPU stats are disabled")
    if CFG.session_cache_enabled:
        cleanup_sessions(7)
    cleanup_uploads()

    registry = TargetRegistry()
    registry.reload()
    if not registry.enabled():
        log.warning("no enabled target in targets.json - preflight will run, browser tests will not")

    store = Store.open_safely(DB_FILE)
    try:
        await store.sync_targets(list(registry.targets.values()))
        proxies = await asyncio.to_thread(load_all_proxy_files)
        if proxies:
            await store.ingest_proxies(proxies)
        await store.reset_claims()

        circuit = TargetCircuit()
        netguard = NetGuard()
        stop_event = asyncio.Event()

        async with async_playwright() as pw:
            def launcher():
                return pw.chromium.launch(headless=CFG.headless, args=_launch_args())

            pool = BrowserPool(launcher)
            await pool.start()
            if not pool.recs:
                fatal("no Chromium instance could be launched - run: playwright install chromium")
                return 1

            rt = Runtime(store, pool, registry, circuit, netguard, stop_event)
            rt.fd_limit = fd_limit
            with contextlib.suppress(Exception):
                rt.browser_version = next(iter(pool.recs.values())).browser.version

            # ---- Telegram ----------------------------------------------------
            bot_task = None
            if CFG.telegram_bot_token and not AIOGRAM_OK:
                fatal("telegram_bot_token is set but aiogram is not installed - bot control disabled")
            elif AIOGRAM_OK and CFG.telegram_bot_token:
                if not _allowed_user_ids():
                    log.warning("Telegram bot has NO authorised users: set telegram_chat_id to your "
                                "private chat id, or list ids in telegram_admin_ids")
                try:
                    bot = Bot(token=CFG.telegram_bot_token,
                              default=DefaultBotProperties(parse_mode="HTML"))
                except TypeError:                          # older aiogram 3.x signature
                    bot = Bot(token=CFG.telegram_bot_token, parse_mode="HTML")
                dp = Dispatcher()
                dp.include_router(router)
                rt.bot = bot
                bot_task = asyncio.create_task(bot_polling_supervisor(rt, dp))
                await _notify(rt, f"🚀 Radiate v{VERSION} online — {len(registry.enabled())} target(s), "
                                  f"{CFG.worker_count}+{CFG.retry_worker_count} browser workers, "
                                  f"{CFG.preflight_worker_count} preflight sockets. /start for controls.",
                              key="boot")

            # ---- background tasks -------------------------------------------
            bg = [
                asyncio.create_task(preflight_scheduler(rt), name="preflight-scheduler"),
                *[asyncio.create_task(preflight_worker(rt), name=f"preflight-{i}")
                  for i in range(CFG.preflight_worker_count)],
                asyncio.create_task(scheduler_loop(rt), name="scheduler"),
                asyncio.create_task(retry_scheduler_loop(rt), name="retry-scheduler"),
                asyncio.create_task(pool_guard_loop(rt), name="pool-guard"),
                asyncio.create_task(fallback_loop(rt), name="fallback"),
                asyncio.create_task(uptimerobot_task(rt), name="uptime"),
                asyncio.create_task(live_status_updater(rt), name="live-status"),
                asyncio.create_task(output_loop(rt), name="output"),
                asyncio.create_task(maintenance_loop(rt), name="maintenance"),
                asyncio.create_task(metrics_loop(rt), name="metrics"),
                asyncio.create_task(ua_refresh_loop(rt), name="ua-refresh"),
                asyncio.create_task(mongo_loop(rt), name="mongo"),
                asyncio.create_task(git_watch_loop(rt), name="git"),
            ]
            if CFG.keepalive_enabled:
                bg.append(asyncio.create_task(keepalive_loop(rt), name="keepalive"))

            srv = None
            if CFG.http_api_enabled:
                if CFG.http_api_host not in ("127.0.0.1", "localhost", "::1") and not CFG.http_api_token:
                    log.warning("HTTP endpoint is bound to %s with no token - set http_api_token",
                                CFG.http_api_host)
                try:
                    srv = await asyncio.start_server(lambda r, w: http_health_server(r, w, rt),
                                                     CFG.http_api_host, CFG.http_api_port)
                    bg.append(asyncio.create_task(srv.serve_forever(), name="http"))
                except OSError as exc:
                    elog.error("HTTP endpoint could not bind %s:%s (%s)",
                               CFG.http_api_host, CFG.http_api_port, exc)

            # ---- browser worker pools ----------------------------------------
            fresh_tasks = [asyncio.create_task(browser_worker(i, rt, "fresh"), name=f"fresh-{i}")
                           for i in range(MAX_MAIN_WORKERS)]
            retry_tasks = [asyncio.create_task(browser_worker(i, rt, "retry"), name=f"retry-{i}")
                           for i in range(MAX_RETRY_WORKERS)]
            groups = [("fresh", fresh_tasks), ("retry", retry_tasks)]
            supervisor = asyncio.create_task(supervisor_loop(rt, groups), name="supervisor")

            loop = asyncio.get_running_loop()
            shutdown = asyncio.Event()
            for sig in (signal.SIGINT, signal.SIGTERM):
                with contextlib.suppress(Exception):
                    loop.add_signal_handler(sig, shutdown.set)
            watchdog = asyncio.create_task(_watch_stop_event(rt, shutdown), name="watchdog")

            log.info("daemon running: %d fresh + %d retry workers, %d preflight sockets, "
                     "%d browsers, fd limit %s", CFG.worker_count, CFG.retry_worker_count,
                     CFG.preflight_worker_count, len(pool.recs), fd_limit)
            await shutdown.wait()

            # ---- shutdown -----------------------------------------------------
            rt.stop_event.set()
            watchdog.cancel()
            supervisor.cancel()
            workers = fresh_tasks + retry_tasks
            with contextlib.suppress(Exception):
                await asyncio.wait_for(asyncio.gather(*workers, return_exceptions=True),
                                       timeout=CFG.shutdown_grace_seconds)
            everything = bg + [supervisor, watchdog] + workers \
                + ([bot_task] if bot_task else []) + list(rt.tasks)
            for t in everything:
                t.cancel()
            with contextlib.suppress(Exception):
                await asyncio.wait_for(asyncio.gather(*everything, return_exceptions=True), timeout=15)
            if srv is not None:
                with contextlib.suppress(Exception):
                    srv.close()
                    await srv.wait_closed()
            await HTTP.close()
            MONGO.close()
            if rt.bot is not None:
                with contextlib.suppress(Exception):
                    await rt.bot.session.close()
            await pool.close()
            restart = rt.restart_requested
            log.info("daemon stopped (restart=%s)", restart)
    finally:
        store.close()
    return RESTART_EXIT_CODE if restart else 0


async def _watch_stop_event(rt: Runtime, shutdown: asyncio.Event) -> None:
    await rt.stop_event.wait()
    shutdown.set()


# ══════════════════════════════════════════════════════════════════════════════
#  CLI
#  These commands are invoked by the operator, so they DO print - the silence rule
#  applies to the daemon, which must leave the Codespace terminal clean.
# ══════════════════════════════════════════════════════════════════════════════
def cli_run() -> None:
    lock = InstanceLock(LOCK_FILE)
    if not lock.acquire():
        _say(f"Another instance is already running (lock: {LOCK_FILE}).", err=True)
        sys.exit(1)
    try:
        code = asyncio.run(run_daemon())
    except KeyboardInterrupt:
        code = 0
    except Exception:
        tb = traceback.format_exc()
        elog.critical("daemon crashed\n%s", tb)
        send_sync_alert(f"⛔ Radiate v{VERSION} CRASHED\n{tb[-1200:]}")
        if not CFG.silent_terminal:
            _say(tb, err=True)
        code = 1
    finally:
        lock.release()
    sys.exit(code)


def cli_status(as_json: bool) -> None:
    async def go():
        if not DB_FILE.exists():
            _say("No database yet - start the daemon or run add-proxies first.")
            return
        store = Store.open_safely(DB_FILE, readonly=True)
        try:
            stats = await store.stats()
        finally:
            store.close()
        if as_json:
            _say(json.dumps(stats, indent=2))
            return
        g, pf = stats["global"], stats["preflight"]
        _say(f"Radiate Proxy Monitor v{VERSION}")
        _say(f"Total proxies : {stats['proxies_total']:,}")
        for label, key in (("Working", "WORKING"), ("Preflight OK", "PREFLIGHT_PASS"),
                           ("Retryable", "RETRYABLE"), ("Quarantined", "QUARANTINED"),
                           ("Failed", "FAILED"), ("Dead", "DEAD"), ("Untested", "UNTESTED")):
            _say(f"  {label:<13}: {g.get(key, 0):,}")
        _say(f"Preflight     : alive {pf.get('ALIVE', 0):,} / dead {pf.get('DEAD', 0):,} / "
             f"unknown {pf.get('UNKNOWN', 0):,}")
        if stats["schemes"]:
            _say("Protocols     : " + ", ".join(f"{k}={v:,}" for k, v in sorted(stats["schemes"].items())))
        _say(f"In-flight     : {stats['in_flight']:,}   Due now: {stats['due']:,}")
    asyncio.run(go())


def cli_add_proxies(fpath: str) -> None:
    async def go():
        p = Path(fpath)
        if not p.exists():
            _say(f"File not found: {fpath}", err=True)
            sys.exit(1)
        proxies, bad = load_proxy_file(p)
        store = Store.open_safely(DB_FILE)
        try:
            r = await store.ingest_proxies(proxies)
            _say(f"Parsed {len(proxies):,} unique proxies ({bad:,} unusable lines). "
                 f"New={r['inserted']:,} Existing={r['existing']:,} NewRows={r['rows_created']:,}")
        finally:
            store.close()
    asyncio.run(go())


def cli_probe(fpath: Optional[str], limit: int) -> None:
    """Run preflight only, straight from the CLI - handy to see how many of a list
    are actually usable before the daemon ever launches a browser."""
    async def go():
        if fpath:
            p = Path(fpath)
            if not p.exists():
                _say(f"File not found: {fpath}", err=True)
                sys.exit(1)
            proxies, _ = load_proxy_file(p)
        else:
            store = Store.open_safely(DB_FILE, readonly=True)
            try:
                proxies = [r[0] for r in store._conn.execute(
                    "SELECT proxy FROM proxies LIMIT ?", (limit,))]
            finally:
                store.close()
        proxies = proxies[:limit]
        if not proxies:
            _say("Nothing to probe.")
            return
        raise_fd_limit()
        sem = asyncio.Semaphore(min(CFG.preflight_worker_count, 500))
        results: dict[str, int] = defaultdict(int)

        async def one(proxy: str):
            async with sem:
                if not await tcp_preflight(proxy, CFG.tcp_preflight_timeout):
                    results["tcp_dead"] += 1
                    return
                scheme = await detect_protocol(proxy, urlparse(proxy).scheme,
                                               CFG.handshake_timeout) if CFG.handshake_probe_enabled else "http"
                results[scheme or "port_open_not_proxy"] += 1

        t0 = time.monotonic()
        await asyncio.gather(*(one(p) for p in proxies))
        took = time.monotonic() - t0
        _say(f"Probed {len(proxies):,} proxies in {took:.1f}s")
        for k, v in sorted(results.items(), key=lambda kv: -kv[1]):
            _say(f"  {k:<22}: {v:,}")
    asyncio.run(go())


def cli_add_target(url: str) -> None:
    try:
        targets = load_targets()
    except ValueError as exc:
        _say(f"targets.json is invalid, fix it first: {exc}", err=True)
        sys.exit(1)
    try:
        new = _target_from_dict({"url": url})
    except ValueError as exc:
        _say(f"Invalid target: {exc}", err=True)
        sys.exit(1)
    if any(t.target_id == new.target_id or t.url == new.url for t in targets):
        _say(f"Target already exists: {new.target_id}")
        return
    targets.append(new)
    save_targets(targets)
    _say(f"Added target {new.target_id} -> {new.url}\nA running daemon hot-reloads it.")


def cli_target_toggle(tid: str, enabled: bool) -> None:
    try:
        targets = load_targets()
    except ValueError as exc:
        _say(f"targets.json is invalid: {exc}", err=True)
        sys.exit(1)
    for t in targets:
        if t.target_id == tid:
            t.enabled = enabled
            save_targets(targets)
            _say(f"{tid}: enabled={enabled}")
            return
    _say(f"No such target: {tid}", err=True)
    sys.exit(1)


def cli_remove_target(tid: str) -> None:
    try:
        targets = load_targets()
    except ValueError as exc:
        _say(f"targets.json is invalid: {exc}", err=True)
        sys.exit(1)
    kept = [t for t in targets if t.target_id != tid]
    if len(kept) == len(targets):
        _say(f"No such target: {tid}", err=True)
        sys.exit(1)
    save_targets(kept)
    _say(f"Removed {tid} from targets.json.")


def cli_list_targets() -> None:
    try:
        targets = load_targets()
    except ValueError as exc:
        _say(f"targets.json is invalid: {exc}", err=True)
        sys.exit(1)
    for t in targets:
        flags = []
        if t.allow_offsite_redirect:
            flags.append("offsite")
        if t.redirect_means_success:
            flags.append("ruleB")
        _say(f"{'ON ' if t.enabled else 'off'}  {t.target_id:<30} {t.url}"
             + (f"  [{','.join(flags)}]" if flags else ""))


def cli_export(path: str, mask: bool) -> None:
    async def go():
        if not DB_FILE.exists():
            _say("No database yet - nothing to export.", err=True)
            sys.exit(1)
        store = Store.open_safely(DB_FILE, readonly=True)
        try:
            data = await store.export_state(mask=mask)
        finally:
            store.close()
        _atomic_write(Path(path), json.dumps(data, indent=2))
        _say(f"Exported state to {path}")
    asyncio.run(go())


def cli_backup() -> None:
    async def go():
        for attempt in range(3):
            try:
                store = Store.open_safely(DB_FILE)
                try:
                    path = await store.backup(BACKUP_DIR, CFG.backup_keep)
                    _say(f"Backup written: {path}")
                    return
                finally:
                    store.close()
            except sqlite3.OperationalError as exc:
                if "locked" in str(exc).lower() and attempt < 2:
                    time.sleep(1)
                else:
                    raise
    asyncio.run(go())


def cli_restore(fpath: str) -> None:
    src = Path(fpath)
    if not src.exists():
        _say(f"File not found: {fpath}", err=True)
        sys.exit(1)
    lock = InstanceLock(LOCK_FILE)
    if not lock.acquire():
        _say("Stop the daemon before restoring (a lock file is present).", err=True)
        sys.exit(1)
    try:
        for suffix in ("-wal", "-shm"):
            with contextlib.suppress(OSError):
                Path(str(DB_FILE) + suffix).unlink()
        shutil.copy2(src, DB_FILE)
        _say(f"Restored {DB_FILE} from {fpath}. Verifying…")
        store = Store.open_safely(DB_FILE)
        ok = store._conn.execute("PRAGMA quick_check").fetchone()[0] == "ok"
        _say("OK" if ok else "WARNING: integrity check failed")
        store.close()
    finally:
        lock.release()


_GITIGNORE_BASE = ["data/", "logs/", "output/", "*.db", "*.db-wal", "*.db-shm", "*.tmp", "*.lock",
                   ".env", "config.json", "metrics.json", "state/*", "!state/snapshot.json"]


def write_gitignore() -> None:
    """config.json holds the bot token and the GitHub PAT; proxy lists may hold credentials."""
    gi = ROOT / ".gitignore"
    wanted = list(_GITIGNORE_BASE)
    for pf in CFG.proxy_files:
        with contextlib.suppress(ValueError):
            wanted.append(_rp(pf).relative_to(ROOT).as_posix())
    have = set()
    if gi.exists():
        have = {ln.strip() for ln in gi.read_text(encoding="utf-8").splitlines()}
    missing = [w for w in wanted if w not in have]
    if not missing:
        return
    prefix = ""
    if gi.exists():
        prefix = "" if gi.read_text(encoding="utf-8").endswith("\n") or not have else "\n"
    with open(gi, "a", encoding="utf-8") as f:
        f.write(prefix + "\n".join(missing) + "\n")


def cli_init() -> None:
    write_gitignore()
    load_config()
    load_targets()
    (ROOT / "proxy_worked.txt").touch(exist_ok=True)
    req = ROOT / "requirements.txt"
    if not req.exists():
        req.write_text("playwright>=1.45\naiohttp>=3.9\npsutil>=5.9\naiogram>=3.7\n"
                       "# optional: pymongo>=4.6\n", encoding="utf-8")
    cpu, ram = _detect_hardware()
    _say(f"Initialised in {ROOT}\nDetected {cpu} cores / {ram:.1f} GB -> "
         f"{CFG.worker_count} fresh + {CFG.retry_worker_count} retry workers, "
         f"{CFG.preflight_worker_count} preflight sockets.\n\nNext:\n"
         f"  1) pip install -r requirements.txt && playwright install chromium\n"
         f"  2) put telegram_bot_token + telegram_chat_id in config.json\n"
         f"  3) python3 {Path(__file__).name} add-target https://your-site.example/\n"
         f"  4) python3 {Path(__file__).name} tmux start")


def cli_update() -> None:
    res = git_pull_and_check()
    if not res.get("ok"):
        _say(f"Update failed: {res.get('error')}", err=True)
        sys.exit(1)
    if not res.get("changed"):
        _say("Already up to date.")
        return
    _say(f"Updated {res['before']} -> {res['after']}: {', '.join(res['files'])}")
    if res["code_changed"]:
        if pip_install_if_changed():
            _say("Dependencies updated.")
        _say("Code changed - restart the daemon (tmux restart).")


def cli_push_state() -> None:
    async def go():
        store = Store.open_safely(DB_FILE, readonly=True)
        try:
            await push_state_snapshot(store)
        finally:
            store.close()
    asyncio.run(go())
    _say("State snapshot pushed (if git_push_state and a remote are configured).")


def cli_purge(days: float) -> None:
    async def go():
        store = Store.open_safely(DB_FILE)
        try:
            n = await store.purge_dead(days, CFG.purge_dead_min_fails)
            _say(f"Purged {n:,} proxies dead for more than {days:g} days.")
        finally:
            store.close()
    asyncio.run(go())


def _tmux(args: list) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(["tmux", *args], capture_output=True, text=True)
    except FileNotFoundError:
        _say("tmux is not installed (apt-get install tmux).", err=True)
        sys.exit(1)


def cli_tmux(action: str) -> None:
    # The wrapper loop is what makes "Restart Daemon" work from Telegram: exit code
    # 75 relaunches, anything else ends the session.
    inner = (f"cd {shlex.quote(str(ROOT))} && "
             f"while true; do {shlex.quote(sys.executable)} {shlex.quote(Path(__file__).name)} "
             f"_runloop; code=$?; [ $code -eq {RESTART_EXIT_CODE} ] || break; done")
    if action == "start":
        if TMUX_SESSION in _tmux(["ls"]).stdout:
            _say(f"tmux session '{TMUX_SESSION}' is already running.")
            return
        _tmux(["new-session", "-d", "-s", TMUX_SESSION, inner])
        _say(f"tmux session '{TMUX_SESSION}' started (terminal stays silent).")
    elif action == "attach":
        subprocess.call(["tmux", "attach", "-t", TMUX_SESSION])
    elif action == "detach":
        _tmux(["detach-client", "-s", TMUX_SESSION])
    elif action == "stop":
        _tmux(["kill-session", "-t", TMUX_SESSION])
        _say("Stopped.")
    elif action == "restart":
        _tmux(["kill-session", "-t", TMUX_SESSION])
        time.sleep(1)
        cli_tmux("start")
    elif action == "status":
        _say(_tmux(["ls"]).stdout or "(no tmux sessions)")


def main() -> None:
    parser = argparse.ArgumentParser(prog="main.py", description=f"RADIATE PROXY MONITOR v{VERSION}")
    sub = parser.add_subparsers(dest="cmd")

    sub.add_parser("init", help="create config.json / targets.json / requirements.txt / .gitignore")
    sub.add_parser("run", help="run the daemon in the foreground (silent terminal)")
    sub.add_parser("_runloop", help=argparse.SUPPRESS)

    p_status = sub.add_parser("status", help="print DB stats")
    p_status.add_argument("--json", action="store_true")

    p_add = sub.add_parser("add-proxies", help="normalise + merge proxies from a file into the DB")
    p_add.add_argument("file")

    p_probe = sub.add_parser("probe", help="preflight only: how many proxies are actually usable")
    p_probe.add_argument("file", nargs="?")
    p_probe.add_argument("--limit", type=int, default=2000)

    p_t = sub.add_parser("add-target", help="register a target URL (hot-reloaded by the daemon)")
    p_t.add_argument("url")
    sub.add_parser("list-targets", help="list configured targets")
    p_en = sub.add_parser("enable-target", help="enable a target")
    p_en.add_argument("target_id")
    p_dis = sub.add_parser("disable-target", help="disable a target (keeps its history)")
    p_dis.add_argument("target_id")
    p_rm = sub.add_parser("remove-target", help="remove a target from targets.json")
    p_rm.add_argument("target_id")

    p_e = sub.add_parser("export", help="export full state to JSON")
    p_e.add_argument("file")
    p_e.add_argument("--mask", action="store_true", help="mask proxy credentials in the export")

    sub.add_parser("backup", help="write a SQLite backup to data/backups/")
    p_r = sub.add_parser("restore", help="restore the DB from a backup (stop the daemon first)")
    p_r.add_argument("file")

    p_pg = sub.add_parser("purge", help="delete long-dead proxies")
    p_pg.add_argument("--days", type=float, default=CFG.purge_dead_after_days)

    sub.add_parser("update", help="git fetch + fast-forward, install deps if requirements changed")
    sub.add_parser("push-state", help="commit+push a masked JSON state snapshot")

    p_tm = sub.add_parser("tmux", help="tmux session control")
    p_tm.add_argument("action", choices=["start", "attach", "detach", "stop", "restart", "status"])

    args = parser.parse_args()
    cmd = args.cmd
    if cmd in ("run", "_runloop"):
        cli_run()
    elif cmd == "init":
        cli_init()
    elif cmd == "status":
        cli_status(args.json)
    elif cmd == "add-proxies":
        cli_add_proxies(args.file)
    elif cmd == "probe":
        cli_probe(args.file, args.limit)
    elif cmd == "add-target":
        cli_add_target(args.url)
    elif cmd == "list-targets":
        cli_list_targets()
    elif cmd == "enable-target":
        cli_target_toggle(args.target_id, True)
    elif cmd == "disable-target":
        cli_target_toggle(args.target_id, False)
    elif cmd == "remove-target":
        cli_remove_target(args.target_id)
    elif cmd == "export":
        cli_export(args.file, args.mask)
    elif cmd == "backup":
        cli_backup()
    elif cmd == "restore":
        cli_restore(args.file)
    elif cmd == "purge":
        cli_purge(args.days)
    elif cmd == "update":
        cli_update()
    elif cmd == "push-state":
        cli_push_state()
    elif cmd == "tmux":
        cli_tmux(args.action)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
