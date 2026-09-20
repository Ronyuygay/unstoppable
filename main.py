#!/usr/bin/env python3
"""
RADIATE PROXY MONITOR v5.1
================================================================================
Multi-target, restart-safe, GitHub-maintainable proxy REVALIDATION system.
It re-tests ONLY the proxies you give it (proxy_worked.txt etc.) - it never
downloads public proxy lists.

Requires Python 3.10+

    python3 main.py init                   # create .gitignore / config / targets template
    python3 main.py run                    # start daemon (foreground)
    python3 main.py status [--json]        # DB stats (works while daemon runs)
    python3 main.py add-proxies FILE       # normalise + merge proxies into the DB
    python3 main.py add-target URL         # register a target (hot-reloaded by daemon)
    python3 main.py list-targets | enable-target ID | disable-target ID | remove-target ID
    python3 main.py export FILE            # dump full state to JSON
    python3 main.py backup | restore FILE  # SQLite backup / restore (stop daemon first)
    python3 main.py update                 # git fetch + fast-forward + pip deps if changed
    python3 main.py push-state             # commit state/ snapshot to GitHub
    python3 main.py tmux start|attach|detach|stop|restart|status

Exit code 75 = "restart requested" (used by the tmux wrapper after a git update).
"""

from __future__ import annotations

import argparse
import asyncio
import contextlib
import dataclasses
import hashlib
import json
import logging
import math
import os
import random
import re
import shlex
import shutil
import signal
import sqlite3
import subprocess
import sys
import threading
import time
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass, field
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Optional
from urllib.parse import unquote, urlparse

try:                                    # POSIX only; used for the single-instance lock
    import fcntl
except ImportError:                     # pragma: no cover
    fcntl = None

try:                                    # optional: memory-pressure guard
    import psutil
except ImportError:                     # pragma: no cover
    psutil = None

try:
    from playwright.async_api import async_playwright
    from playwright.async_api import Error as PlaywrightError
    from playwright.async_api import TimeoutError as PlaywrightTimeout
    PLAYWRIGHT_OK = True
except ImportError:                     # CLI helpers still work without Playwright
    PLAYWRIGHT_OK = False
    async_playwright = None

    class PlaywrightError(Exception):
        pass

    class PlaywrightTimeout(PlaywrightError):
        pass


VERSION = "5.1"
RESTART_EXIT_CODE = 75
ROOT = Path(__file__).resolve().parent
CONFIG_FILE = ROOT / "config.json"
TARGETS_FILE = ROOT / "targets.json"
TMUX_SESSION = "proxy-monitor"

STATUSES_OK = ("WORKING", "RECOVERED")


# ══════════════════════════════════════════════════════════════════════════════
#  CONFIG  (everything tunable lives here or in config.json - no code edits needed)
# ══════════════════════════════════════════════════════════════════════════════
@dataclass
class Config:
    # ---- concurrency / browser pool -----------------------------------------
    worker_count: int = 12
    browser_count: int = 3                  # persistent Chromium processes
    contexts_per_browser: int = 5           # concurrent isolated contexts per browser
    browser_recycle_after: int = 150        # restart a Chromium after N contexts (leak control)
    headless: bool = True
    chromium_no_sandbox: bool = True        # needed in Docker / Cloud Shell as root
    ignore_https_errors: bool = True
    ua_rotation: bool = True                # vary viewport/locale/tz per session (host-OS consistent)
    custom_ua_profiles: list = field(default_factory=list)  # [{"ua","width","height","locale","tz"}]
    ua_pool_remote: bool = False
    ua_pool_refresh_seconds: float = 3600.0

    # ---- verification window ------------------------------------------------
    post_load_wait_seconds: float = 40.0
    navigation_timeout_ms: int = 45_000
    network_idle_timeout_ms: int = 12_000
    connect_jitter_min: float = 0.5         # random start stagger (avoids thundering herd)
    connect_jitter_max: float = 3.0
    tcp_preflight_timeout: float = 1.5
    stability_poll_seconds: float = 5.0     # crash / connection-loss checks during the wait
    hard_timeout_extra_seconds: float = 90.0

    # ---- scheduler ----------------------------------------------------------
    scheduler_tick_seconds: float = 5.0
    claim_timeout_seconds: float = 600.0    # stale in-flight claims are re-eligible after this
    batch_size_per_tick: int = 30
    queue_extra: int = 4                    # queue depth = worker_count + queue_extra
    min_retest_gap_seconds: float = 900.0   # hard floor: a proxy can NEVER be retested on the
                                            # same target sooner than this, no matter its status
                                            # (this is what sends it "to the bottom of the queue")
    cross_target_parallel: bool = False     # allow one proxy in two tests at the same moment

    # ---- cooldown / quarantine ladder ---------------------------------------
    working_cooldown: float = 1_800.0
    retryable_cooldown: float = 900.0
    retryable_attempts: int = 1             # failures that stay RETRYABLE before quarantine
    quarantined_cooldown_1: float = 3_600.0
    quarantined_cooldown_2: float = 21_600.0
    failed_cooldown: float = 86_400.0
    recovered_probe_cooldown: float = 600.0
    soft_retry_cooldown: float = 120.0      # BROWSER_ERROR / RETRYABLE_ERROR (not the proxy's fault)
    soft_max_streak: int = 5                # soft failures in a row before they count as real
    cooldown_jitter: float = 0.10           # +-10% so cohorts don't all fall due together
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
    memory_high_percent: float = 92.0

    # ---- output / dashboard / logging / maintenance -------------------------
    dashboard_refresh: float = 2.0
    output_flush_interval: float = 15.0
    output_mode: str = "any"                # "any": working on >=1 target, "all": on every enabled target
    output_max_age_seconds: float = 0.0     # 0 = ignore age; else drop proxies not confirmed recently
    history_retention_days: float = 7.0
    log_level: str = "INFO"
    log_max_bytes: int = 5_000_000
    log_backup_count: int = 3
    maintenance_interval_seconds: float = 3_600.0
    backup_interval_hours: float = 6.0
    backup_keep: int = 8
    shutdown_grace_seconds: float = 20.0

    # ---- endpoints & stealth features ---------------------------------------
    http_api_enabled: bool = False
    http_api_host: str = "127.0.0.1"
    http_api_port: int = 8080
    enable_stealth_script: bool = False
    session_cache_enabled: bool = False
    metrics_interval_seconds: float = 30.0
    metrics_file: str = "metrics.json"
    keepalive_enabled: bool = False
    keepalive_interval_seconds: float = 90.0

    # ---- inputs / paths -----------------------------------------------------
    proxy_files: list = field(default_factory=lambda: ["proxy_worked.txt"])
    proxy_file_watch: bool = True           # re-ingest automatically when a proxy file changes
    data_dir: str = "data"
    log_dir: str = "logs"
    output_dir: str = "output"
    state_dir: str = "state"                # git-friendly snapshots (NOT the SQLite file)
    output_file: str = "validated_proxies.txt"

    # ---- GitHub -------------------------------------------------------------
    git_enabled: bool = False
    git_remote: str = "origin"
    git_branch: str = "main"
    git_check_interval_seconds: float = 900.0
    git_auto_restart: bool = True           # graceful restart (exit 75) when main.py/requirements.txt changed
    git_push_state: bool = False
    git_push_interval_seconds: float = 3_600.0

    # ---- Telegram notifications (optional; leave blank to disable) ----------
    telegram_bot_token: str = "8247131531:AAFlZgZxdxJ1OS2uRWNeUfvV9tWTfwJUpXs"
    telegram_chat_id: str = "-1004423229118"
    telegram_summary_interval_seconds: float = 3_600.0

    # ---- external fallback (optional; empty list = never fetch externally) --
    fallback_urls: list = field(default_factory=list)
    fallback_min_working: int = 20
    fallback_cooldown_seconds: float = 1_800.0


def _coerce(default, value):
    """Best-effort type coercion so "12" or 12.0 in config.json can't crash the daemon."""
    if isinstance(default, bool):
        return bool(value)
    if isinstance(default, int) and not isinstance(default, bool):
        return int(value)
    if isinstance(default, float):
        return float(value)
    return value


def _atomic_write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
        f.flush()
        with contextlib.suppress(OSError):
            os.fsync(f.fileno())
    os.replace(tmp, path)


def load_config() -> Config:
    cfg = Config()
    if CONFIG_FILE.exists():
        try:
            data = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
            missing = False
            for k, v in data.items():
                if hasattr(cfg, k):
                    with contextlib.suppress(Exception):
                        setattr(cfg, k, _coerce(getattr(cfg, k), v))
            missing = any(k not in data for k in asdict(cfg))
            if missing:      # new options appear in the file, user values are preserved
                with contextlib.suppress(Exception):
                    _atomic_write(CONFIG_FILE, json.dumps(asdict(cfg), indent=2))
        except Exception as exc:
            print(f"[config] failed to load {CONFIG_FILE.name}: {exc} - using defaults", file=sys.stderr)
    else:
        with contextlib.suppress(Exception):
            _atomic_write(CONFIG_FILE, json.dumps(asdict(cfg), indent=2))
            
    cfg.worker_count = max(1, cfg.worker_count)
    cfg.browser_count = max(1, cfg.browser_count)
    cfg.contexts_per_browser = max(1, cfg.contexts_per_browser)
    cfg.circuit_window = max(5, cfg.circuit_window)
    cfg.circuit_probe_count = max(1, cfg.circuit_probe_count)

    if sum(cfg.score_weights.values()) <= 0:
        cfg.score_weights = {"overall": 0.25, "recent": 0.30, "latency": 0.15, "streak": 0.30}
        
    known_failures = {"TCP_FAILURE", "CONNECTION_TIMEOUT", "NAVIGATION_TIMEOUT", "HTTP_ERROR", 
                      "EMPTY_RESPONSE", "TARGET_VALIDATION_FAILED", "BROWSER_ERROR", "RETRYABLE_ERROR"}
    cfg.failure_policy = {k: v for k, v in cfg.failure_policy.items() if k in known_failures}

    return cfg


CFG = load_config()


def _rp(p: str) -> Path:
    q = Path(p)
    return q if q.is_absolute() else ROOT / q


DATA_DIR = _rp(CFG.data_dir)
LOG_DIR = _rp(CFG.log_dir)
OUT_DIR = _rp(CFG.output_dir)
STATE_DIR = _rp(CFG.state_dir)
BACKUP_DIR = DATA_DIR / "backups"
SESSIONS_DIR = DATA_DIR / "sessions"
DB_FILE = DATA_DIR / "proxy_state.db"
LOCK_FILE = DATA_DIR / "monitor.lock"
DEPS_STAMP = DATA_DIR / "requirements.sha1"
OUTPUT_FILE = OUT_DIR / CFG.output_file
for _d in (DATA_DIR, LOG_DIR, OUT_DIR, STATE_DIR, BACKUP_DIR, SESSIONS_DIR):
    _d.mkdir(parents=True, exist_ok=True)


# ══════════════════════════════════════════════════════════════════════════════
#  LOGGING - files only, never stdout (root logger too, so 3rd-party warnings
#  cannot leak onto the dashboard)
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
        if not lg.handlers:
            lg.addHandler(handler(filename))
        return lg

    root = logging.getLogger()
    if not any(isinstance(h, RotatingFileHandler) for h in root.handlers):
        root.addHandler(handler("errors.log"))
    root.setLevel(logging.WARNING)

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


def cleanup_sessions(max_age_days: float):
    now = time.time()
    for f in SESSIONS_DIR.glob("*.json"):
        try:
            if now - f.stat().st_mtime > max_age_days * 86400:
                f.unlink()
        except OSError:
            pass


# ══════════════════════════════════════════════════════════════════════════════
#  TARGETS (configuration-driven; hot-reloaded from targets.json)
# ══════════════════════════════════════════════════════════════════════════════
DEFAULT_FORBIDDEN = [
    "checking your browser",
    "just a moment",
    "verify you are human",
    "attention required",
    "anonymous proxy detected",
    "ddos protection",
    "please wait while we check",
    "enable javascript and cookies",
    "html:cf-chl-",              # "html:" = search the page source instead of visible text
    "html:challenge-platform",
]
# Legacy v5.0 files stored bare "cloudflare" (matches ordinary pages / CDN URLs -> false failures)
_LEGACY_DROP = {"cloudflare"}
_LEGACY_HTML = {"cf-chl-", "challenge-platform"}


@dataclass
class Target:
    target_id: str
    url: str
    enabled: bool = True
    post_load_wait_seconds: float = 40.0
    navigation_timeout_ms: int = 45_000
    interaction_steps: list = field(default_factory=list)
    reload_after_load: bool = False            # refresh requirement
    success_markers: list = field(default_factory=list)      # any visible-text marker must appear
    forbidden_markers: list = field(default_factory=lambda: list(DEFAULT_FORBIDDEN))
    success_selectors: list = field(default_factory=list)    # CSS selectors expected on the page
    success_selectors_mode: str = "any"                      # "any" | "all"
    forbidden_selectors: list = field(default_factory=list)
    title_contains: list = field(default_factory=list)       # any must appear in <title>
    min_body_length: int = 40
    require_status_200: bool = True
    cooldowns: dict = field(default_factory=dict)            # per-target overrides of cooldown settings
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
        "notes": "Replace with a site you own or are authorised to test, then set enabled=true.",
    }]


def save_targets(targets: list[Target]) -> None:
    _atomic_write(TARGETS_FILE, json.dumps([asdict(t) for t in targets], indent=2))


def load_targets() -> list[Target]:
    """Raises ValueError on unreadable/invalid file (caller decides what to do)."""
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
            elog.error("targets.json: duplicate target_id %s skipped", t.target_id)
            continue
        seen.add(t.target_id)
        out.append(t)
    return out


def cooldown_for(overrides: dict, key: str) -> float:
    return float(overrides.get(key, getattr(CFG, key)))


class TargetRegistry:
    """Live view of targets.json; the scheduler polls changed() each tick."""

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


def normalize_proxy(raw: str) -> Optional[str]:
    """Deterministic canonical form: scheme://[user:pass@]host:port  (host lower-cased).
    Accepts host:port, scheme://host:port, user:pass@host:port, host:port:user:pass."""
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
    if scheme not in {"http", "https", "socks5", "socks4"}:
        return None

    user = pwd = None
    if "@" in p:
        cred, hostport = p.rsplit("@", 1)
        user, _, pwd = cred.partition(":")
        pwd = pwd or None
    else:
        hostport = p
    if hostport.startswith("["):                       # [ipv6]:port
        m = re.match(r"^\[([0-9A-Fa-f:.]+)\]:(\d+)$", hostport)
        if not m:
            return None
        host, port_s = m.group(1), m.group(2)
    else:
        parts = hostport.split(":")
        if len(parts) == 2:
            host, port_s = parts
        elif len(parts) == 4 and user is None:          # host:port:user:pass
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
    if scheme.startswith("socks") and user:
        return None                                     # Chromium cannot authenticate SOCKS proxies
    host = host.lower()
    hostpart = f"[{host}]" if ":" in host else host
    auth = ""
    if user:
        auth = f"{user}:{pwd}@" if pwd is not None else f"{user}@"
    return f"{scheme}://{auth}{hostpart}:{port}"


def mask_proxy(proxy: str) -> str:
    """Never write proxy passwords to logs / dashboard."""
    return re.sub(r"(://[^:/@]+):[^@]*@", r"\1:***@", proxy)


def has_credentials(proxy: str) -> bool:
    return bool(re.search(r"://[^/@]+@", proxy))


def build_proxy_config(proxy: str) -> dict:
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


async def tcp_preflight(proxy: str, timeout: float) -> bool:
    u = urlparse(proxy)
    if not u.hostname or not u.port:
        return False
    try:
        _, writer = await asyncio.wait_for(asyncio.open_connection(u.hostname, u.port), timeout=timeout)
        writer.close()
        with contextlib.suppress(Exception):
            await writer.wait_closed()
        return True
    except Exception:
        return False


def load_proxy_file(path: Path) -> tuple[list[str], int]:
    """Returns (unique canonical proxies in file order, number of unusable lines)."""
    out, seen, bad = [], set(), 0
    with path.open("r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            if not line.strip() or line.strip().startswith("#"):
                continue
            p = normalize_proxy(line)
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
            log.warning("proxy file missing: %s", fp)
            continue
        lst, bad = load_proxy_file(fp)
        if bad:
            log.warning("proxy file %s: %d unusable lines skipped", fp.name, bad)
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
#  HEALTH SCORE  (per proxy + target, 0..1, weights configurable)
# ══════════════════════════════════════════════════════════════════════════════
def compute_score(succ: int, fail: int, recent: float, avg_latency: Optional[float],
                  cs: int, cf: int, recoveries: int) -> float:
    total = succ + fail
    if total == 0:
        return 0.0
    overall = (succ + 1) / (total + 2)                       # Laplace-smoothed lifetime success rate
    ref = max(CFG.score_latency_ref_seconds, 0.1)
    lat = 0.5 if avg_latency is None else math.exp(-max(avg_latency, 0.0) / ref)
    streak = min(1.0, max(0.0, 0.5 + 0.10 * min(cs, 5) - 0.15 * min(cf, 5)))
    parts = {"overall": overall, "recent": recent, "latency": lat, "streak": streak}
    w = CFG.score_weights
    wsum = sum(max(float(w.get(k, 0.0)), 0.0) for k in parts) or 1.0
    base = sum(max(float(w.get(k, 0.0)), 0.0) * v for k, v in parts.items()) / wsum
    flap = 1.0 / (1.0 + 0.05 * min(recoveries, 10))          # frequent recoveries = flapping proxy
    return round(max(0.0, min(1.0, base * flap)), 6)


def _jit(x: float) -> float:
    j = CFG.cooldown_jitter
    return x * (1.0 + random.uniform(-j, j)) if j > 0 else x


def failure_ladder(cf: int, overrides: dict) -> tuple[str, float]:
    """cf = consecutive counted failures. RETRYABLE -> QUARANTINED (x2, growing) -> FAILED."""
    r = max(0, CFG.retryable_attempts)
    if cf <= r:
        return "RETRYABLE", cooldown_for(overrides, "retryable_cooldown")
    if cf == r + 1:
        return "QUARANTINED", cooldown_for(overrides, "quarantined_cooldown_1")
    if cf == r + 2:
        return "QUARANTINED", cooldown_for(overrides, "quarantined_cooldown_2")
    return "FAILED", cooldown_for(overrides, "failed_cooldown")


# ══════════════════════════════════════════════════════════════════════════════
#  DATABASE
# ══════════════════════════════════════════════════════════════════════════════
SCHEMA_VERSION = 2

SCHEMA = """
CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT);

CREATE TABLE IF NOT EXISTS proxies (
    proxy_id      INTEGER PRIMARY KEY AUTOINCREMENT,
    proxy         TEXT UNIQUE NOT NULL,
    first_seen    REAL NOT NULL,
    last_seen     REAL NOT NULL,
    global_status TEXT NOT NULL DEFAULT 'UNTESTED',
    global_score  REAL NOT NULL DEFAULT 0.0,
    notes         TEXT
);
CREATE INDEX IF NOT EXISTS idx_proxies_status ON proxies(global_status);

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
CREATE INDEX IF NOT EXISTS idx_hist_ts            ON test_history(ts DESC);
"""

# additive migrations for databases created by v5.0
_MIGRATIONS = [
    ("proxy_target", "avg_latency", "REAL"),
    ("proxy_target", "recent_rate", "REAL NOT NULL DEFAULT 0.5"),
    ("proxy_target", "recoveries",  "INTEGER NOT NULL DEFAULT 0"),
    ("proxy_target", "soft_streak", "INTEGER NOT NULL DEFAULT 0"),
    ("test_history", "latency",     "REAL"),
]

_GLOBAL_STATUS_SQL = """
UPDATE proxies SET
  global_status = COALESCE((
     SELECT CASE
       WHEN SUM(CASE WHEN pt.status IN ('WORKING','RECOVERED') THEN 1 ELSE 0 END) > 0 THEN 'WORKING'
       WHEN SUM(CASE WHEN pt.status = 'RETRYABLE'   THEN 1 ELSE 0 END) > 0 THEN 'RETRYABLE'
       WHEN SUM(CASE WHEN pt.status = 'QUARANTINED' THEN 1 ELSE 0 END) > 0 THEN 'QUARANTINED'
       WHEN SUM(CASE WHEN pt.status = 'UNTESTED'    THEN 1 ELSE 0 END) > 0 THEN 'UNTESTED'
       ELSE 'FAILED' END
     FROM proxy_target pt JOIN targets t ON t.target_id = pt.target_id AND t.enabled = 1
     WHERE pt.proxy_id = proxies.proxy_id), 'UNTESTED'),
  global_score = COALESCE((
     SELECT AVG(pt.score) FROM proxy_target pt JOIN targets t ON t.target_id = pt.target_id AND t.enabled = 1
     WHERE pt.proxy_id = proxies.proxy_id AND pt.status != 'UNTESTED'), 0.0)
"""


class Store:
    """Single-writer SQLite facade. All SQL runs on ONE dedicated thread (no write races);
    every write is an explicit BEGIN IMMEDIATE ... COMMIT transaction."""

    def __init__(self, path: Path, readonly: bool = False) -> None:
        self.path = path
        self.readonly = readonly
        self._ex = ThreadPoolExecutor(max_workers=1, thread_name_prefix="db")
        if readonly:
            self._conn = sqlite3.connect(f"file:{path}?mode=ro", uri=True,
                                         check_same_thread=False, timeout=30.0, isolation_level=None)
            self._conn.row_factory = sqlite3.Row
            return
        self._conn = sqlite3.connect(str(path), check_same_thread=False, timeout=30.0, isolation_level=None)
        self._conn.row_factory = sqlite3.Row
        try:
            self._conn.execute("PRAGMA journal_mode=WAL")
            self._conn.execute("PRAGMA synchronous=NORMAL")      # crash-safe in WAL mode
            self._conn.execute("PRAGMA temp_store=MEMORY")
            self._conn.execute("PRAGMA foreign_keys=ON")
            self._conn.execute("PRAGMA busy_timeout=30000")
            self._conn.execute("PRAGMA wal_autocheckpoint=1000")
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

    # ---------------------------------------------------------------- open / recover
    @classmethod
    def open_safely(cls, path: Path, readonly: bool = False) -> "Store":
        """Open the DB; on corruption quarantine the file and restore the newest backup."""
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
            rlog.error("no usable backup; created a fresh database (proxy files will be re-ingested)")
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
        c.execute("CREATE INDEX IF NOT EXISTS idx_pt_proxy_claim ON proxy_target(proxy_id, last_claimed)")
        if ver < SCHEMA_VERSION:
            with self._tx() as t:
                if added:
                    # v5.0 -> v5.1 (v5.0 never set user_version, so "columns were missing" is the signal):
                    # derive the new fields from the history that already exists
                    t.execute("UPDATE proxy_target SET recent_rate = CASE WHEN success_count+failure_count>0 "
                              "THEN 1.0*success_count/(success_count+failure_count) ELSE 0.5 END")
                    t.execute("UPDATE proxy_target SET last_claimed = NULL")
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
            if added:
                rlog.info("database migrated v5.0 -> v%d (added: %s)", SCHEMA_VERSION,
                          ", ".join(added) or "nothing")

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
            gone = 0
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
        """Ensure a proxy_target row exists for every (proxy, enabled target). Idempotent."""
        return c.execute(
            "INSERT OR IGNORE INTO proxy_target (proxy_id, target_id, status, cooldown_until) "
            "SELECT p.proxy_id, t.target_id, 'UNTESTED', 0 FROM proxies p CROSS JOIN targets t "
            "WHERE t.enabled = 1").rowcount

    async def sync_targets(self, targets):
        return await self._run(self._sync_targets, targets)

    # ---------------------------------------------------------------- proxy ingestion
    def _ingest(self, proxies: list[str]) -> dict:
        now = time.time()
        with self._tx() as c:
            before = c.execute("SELECT COUNT(*) FROM proxies").fetchone()[0]
            c.executemany("INSERT OR IGNORE INTO proxies (proxy, first_seen, last_seen) VALUES (?,?,?)",
                          [(p, now, now) for p in proxies])
            after = c.execute("SELECT COUNT(*) FROM proxies").fetchone()[0]
            c.executemany("UPDATE proxies SET last_seen=? WHERE proxy=?", [(now, p) for p in proxies])
            rows = self._backfill(c)       # new proxies get a row for EVERY enabled target, same transaction
        inserted = after - before
        return {"inserted": inserted, "existing": len(proxies) - inserted, "rows_created": rows}

    async def ingest_proxies(self, proxies):
        return await self._run(self._ingest, proxies)

    # ---------------------------------------------------------------- claims
    def _reset_claims(self) -> int:
        with self._tx() as c:
            return c.execute("UPDATE proxy_target SET last_claimed=NULL WHERE last_claimed IS NOT NULL").rowcount

    async def reset_claims(self):
        return await self._run(self._reset_claims)

    def _release_claims(self, pairs: list[tuple[int, str]]) -> None:
        if not pairs:
            return
        with self._tx() as c:
            c.executemany("UPDATE proxy_target SET last_claimed=NULL WHERE proxy_id=? AND target_id=?", pairs)

    async def release_claims(self, pairs):
        return await self._run(self._release_claims, pairs)

    def _claim_batch(self, target_id: str, limit: int) -> list[tuple[int, str]]:
        if limit <= 0:
            return []
        now = time.time()
        cross = "" if CFG.cross_target_parallel else (
            " AND NOT EXISTS (SELECT 1 FROM proxy_target x WHERE x.proxy_id = pt.proxy_id "
            "AND x.target_id <> pt.target_id AND x.last_claimed IS NOT NULL "
            "AND :now - x.last_claimed < :ct)")
        sql = f"""
            SELECT p.proxy_id, p.proxy
            FROM proxy_target pt
            JOIN proxies p ON p.proxy_id = pt.proxy_id
            WHERE pt.target_id = :tid
              AND pt.cooldown_until <= :now
              AND (pt.last_claimed IS NULL OR :now - pt.last_claimed > :ct)
              AND (pt.last_tested IS NULL OR :now - pt.last_tested >= :gap)
              {cross}
            ORDER BY
              CASE pt.status WHEN 'UNTESTED' THEN 0 WHEN 'RECOVERED' THEN 1 WHEN 'RETRYABLE' THEN 2
                             WHEN 'WORKING' THEN 3 WHEN 'QUARANTINED' THEN 4 WHEN 'FAILED' THEN 5 ELSE 9 END,
              pt.cooldown_until ASC,       -- most overdue first = fair rotation
              pt.score DESC,               -- then healthiest first among equally-due proxies
              RANDOM()                     -- shuffle ties so the same order never repeats
            LIMIT :lim"""
        params = {"tid": target_id, "now": now, "ct": CFG.claim_timeout_seconds,
                  "gap": CFG.min_retest_gap_seconds, "lim": limit}
        with self._tx() as c:
            rows = [(r[0], r[1]) for r in c.execute(sql, params).fetchall()]
            if rows:
                c.executemany("UPDATE proxy_target SET last_claimed=? WHERE proxy_id=? AND target_id=?",
                              [(now, pid, target_id) for pid, _ in rows])
        return rows

    async def claim_batch(self, target_id: str, limit: int):
        return await self._run(self._claim_batch, target_id, limit)

    # ---------------------------------------------------------------- record a result
    def _record(self, proxy_id: int, target_id: str, res, worker_id: int, browser_id: int,
                overrides: dict) -> tuple[str, bool]:
        """Returns (new_status, proxy_had_prior_success)."""
        now = time.time()
        with self._tx() as c:
            c.execute("INSERT OR IGNORE INTO proxy_target (proxy_id, target_id) VALUES (?,?)",
                      (proxy_id, target_id))
            row = c.execute("SELECT * FROM proxy_target WHERE proxy_id=? AND target_id=?",
                            (proxy_id, target_id)).fetchone()
            old = row["status"]
            s, f = row["success_count"], row["failure_count"]
            cs, cf = row["consecutive_successes"], row["consecutive_failures"]
            recent = row["recent_rate"]
            rec_n = row["recoveries"]
            soft = row["soft_streak"]
            avg_lat = row["avg_latency"]
            avg_el = row["avg_elapsed"]
            prior_success = s > 0
            alpha = CFG.score_recent_alpha
            el = res.elapsed_seconds or 0.0
            err = (res.error or "")[:500]

            if res.status == "WORKING":
                s += 1
                cs += 1
                cf = 0
                soft = 0
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
                is_soft = bool(pol.get("soft")) and (soft + 1) < CFG.soft_max_streak
                if is_soft:
                    # local/browser problem - do NOT punish the proxy; just retry soon
                    soft += 1
                    new_status = old
                    cool = max(cooldown_for(overrides, "soft_retry_cooldown"), CFG.min_retest_gap_seconds)
                    c.execute(
                        """UPDATE proxy_target SET failure_class=?, last_tested=?, cooldown_until=?,
                           last_http_status=?, last_elapsed=?, last_error=?, soft_streak=?, last_claimed=NULL
                           WHERE proxy_id=? AND target_id=?""",
                        (res.status, now, now + _jit(cool), res.http_status, el, err, soft, proxy_id, target_id))
                else:
                    f += 1
                    cf += 1
                    cs = 0
                    soft = 0
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
                         recent, compute_score(s, f, recent, avg_lat, cs, cf, rec_n), q_at, proxy_id, target_id))

            c.execute(
                "INSERT INTO test_history (proxy_id, target_id, ts, status, failure_class, http_status, elapsed, "
                "error, worker_id, browser_id, latency) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                (proxy_id, target_id, now, res.status, res.status, res.http_status, res.elapsed_seconds, err,
                 worker_id, browser_id, res.latency_seconds))
            c.execute(_GLOBAL_STATUS_SQL + " WHERE proxy_id = ?", (proxy_id,))
        return new_status, prior_success

    async def record(self, proxy_id, target_id, res, worker_id, browser_id, overrides):
        return await self._run(self._record, proxy_id, target_id, res, worker_id, browser_id, overrides)

    # ---------------------------------------------------------------- circuit-breaker forgiveness
    def _forgive(self, pairs: list[tuple[int, str]], cooldown: float) -> int:
        """Undo the last hard failure for proxies that were only "guilty" because the TARGET / network /
        local environment was down. They are retested after `cooldown` instead of being quarantined."""
        now = time.time()
        n = 0
        with self._tx() as c:
            for pid, tid in set(pairs):
                r = c.execute("SELECT status, consecutive_failures, failure_count, last_success, "
                              "success_count, avg_latency, recent_rate, recoveries, consecutive_successes "
                              "FROM proxy_target WHERE proxy_id=? AND target_id=?", (pid, tid)).fetchone()
                if not r or r["consecutive_failures"] <= 0 or r["status"] not in ("RETRYABLE", "QUARANTINED", "FAILED"):
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
                    "UPDATE proxy_target SET status=?, consecutive_failures=?, failure_count=?, cooldown_until=?, "
                    "last_error='forgiven: environment/target outage', "
                    "quarantined_at=CASE WHEN ?='QUARANTINED' THEN quarantined_at ELSE NULL END, "
                    "score=? "
                    "WHERE proxy_id=? AND target_id=?",
                    (status, cf, fc, now + _jit(cooldown), status, new_score, pid, tid))
                n += 1
            if n:
                c.execute(_GLOBAL_STATUS_SQL)
        return n

    async def forgive(self, pairs, cooldown):
        return await self._run(self._forgive, pairs, cooldown)

    # ---------------------------------------------------------------- stats / resume info
    def _stats(self) -> dict:
        c = self._conn
        now = time.time()
        out: dict = {"proxies_total": 0, "global": {}, "targets": {}, "in_flight": 0, "due": 0}
        for r in c.execute("SELECT global_status, COUNT(*) FROM proxies GROUP BY global_status"):
            out["global"][r[0]] = r[1]
        out["proxies_total"] = sum(out["global"].values())
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
            "WHERE t.enabled=1 AND pt.cooldown_until <= ? "
            "AND (pt.last_claimed IS NULL OR ? - pt.last_claimed >= ?)",
            (now, now, CFG.claim_timeout_seconds)).fetchone()[0]
        return out

    async def stats(self):
        return await self._run(self._stats)

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
        c = self._conn
        age_sql, params = "", []
        if max_age and max_age > 0:
            age_sql = " AND pt.last_success >= ?"
            params.append(time.time() - max_age)
        per: dict[str, list[str]] = defaultdict(list)
        for r in c.execute(
                "SELECT t.target_id, p.proxy FROM proxy_target pt JOIN proxies p ON p.proxy_id=pt.proxy_id "
                "JOIN targets t ON t.target_id=pt.target_id WHERE t.enabled=1 "
                f"AND pt.status IN ('WORKING','RECOVERED'){age_sql} "
                "ORDER BY t.target_id, pt.score DESC, p.proxy", params):
            per[r[0]].append(r[1])
        n_targets = c.execute("SELECT COUNT(*) FROM targets WHERE enabled=1").fetchone()[0]
        need = max(n_targets, 1) if mode == "all" else 1
        flat = [r[0] for r in c.execute(
            "SELECT p.proxy FROM proxies p JOIN proxy_target pt ON pt.proxy_id=p.proxy_id "
            "JOIN targets t ON t.target_id=pt.target_id WHERE t.enabled=1 "
            f"AND pt.status IN ('WORKING','RECOVERED'){age_sql} "
            "GROUP BY p.proxy_id HAVING COUNT(*) >= ? ORDER BY AVG(pt.score) DESC, p.proxy",
            params + [need])]
        return dict(per), flat

    async def working_lists(self, mode: str, max_age: float):
        return await self._run(self._working_lists, mode, max_age)

    # ---------------------------------------------------------------- maintenance
    def _prune_history(self, days: float) -> int:
        with self._tx() as c:
            return c.execute("DELETE FROM test_history WHERE ts < ?", (time.time() - days * 86_400,)).rowcount

    async def prune_history(self, days):
        return await self._run(self._prune_history, days)

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
#  CIRCUIT BREAKER (per target, with half-open probing + exponential back-off)
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
    """Detects TARGET-WIDE failure (target down / blocking us / Chromium broken) as opposed to a few dead
    proxies. While open, no proxies are claimed for that target and the failures that led to the trip are
    forgiven (see Store.forgive) so healthy proxies are not quarantined because of an outage."""

    def __init__(self) -> None:
        self._cb: dict[str, _CB] = {}

    def _get(self, tid: str) -> _CB:
        if tid not in self._cb:
            self._cb[tid] = _CB()
        return self._cb[tid]

    @staticmethod
    def is_systemic(status: str, prior_success: bool) -> bool:
        if status == "WORKING" or status in CFG.circuit_ignore_classes:
            return False
        if status in CFG.circuit_classes:
            return True
        return prior_success                     # a proxy that used to work now fails in a non-proxy-specific way

    def blocked(self, tid: str) -> bool:
        cb = self._get(tid)
        return cb.state == "open" and time.time() < cb.open_until

    def reserve(self, tid: str, want: int) -> int:
        """How many proxies the scheduler may claim for this target right now."""
        cb = self._get(tid)
        if cb.state == "open":
            if time.time() < cb.open_until:
                return 0
            cb.state, cb.probes_issued, cb.probe_results = "half", 0, []
            rlog.info("Circuit HALF-OPEN for %s: sending %d probe test(s)", tid, CFG.circuit_probe_count)
        if cb.state == "half":
            n = max(0, min(want, CFG.circuit_probe_count - cb.probes_issued))
            cb.probes_issued += n
            return n
        return want

    def _open(self, cb: _CB, tid: str, why: str) -> float:
        cooldown = min(CFG.circuit_cooldown * (2 ** cb.level), CFG.circuit_max_cooldown)
        cb.level += 1
        cb.state = "open"
        cb.open_until = time.time() + cooldown
        cb.window.clear()
        rlog.warning("Circuit OPEN for %s (%s) - testing paused %ds", tid, why, int(cooldown))
        return cooldown

    def record(self, tid: str, pid: int, status: str, prior_success: bool) -> tuple[list, Optional[str]]:
        """Returns (pairs_to_forgive, event) with event in {None,'tripped','reopened','closed'}."""
        cb = self._get(tid)
        systemic = self.is_systemic(status, prior_success)
        if cb.state == "open":                   # late result from a test that started before the trip
            return ([(pid, tid)] if systemic else []), None
        if cb.state == "half":
            if status == "WORKING":
                cb.state, cb.level = "closed", 0
                cb.window.clear()
                rlog.info("Circuit CLOSED for %s (probe succeeded)", tid)
                return [], "closed"
            cb.probe_results.append("bad" if systemic else "neutral")
            forgive = [(pid, tid)] if systemic else []
            if len(cb.probe_results) >= CFG.circuit_probe_count:
                if "bad" in cb.probe_results:
                    self._open(cb, tid, "probes failed")
                    return forgive, "reopened"
                cb.probes_issued, cb.probe_results = 0, []
            return forgive, None
        cb.window.append((pid, systemic))
        if len(cb.window) >= CFG.circuit_window:
            bad = [p for p, s in cb.window if s]
            if len(bad) / len(cb.window) >= CFG.circuit_block_ratio:
                forgive = [(p, tid) for p in bad]
                self._open(cb, tid, f"{len(bad)}/{len(cb.window)} systemic failures")
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


async def _tcp_ok(host: str, port: int, timeout: float) -> bool:
    try:
        _, w = await asyncio.wait_for(asyncio.open_connection(host, port), timeout=timeout)
        w.close()
        with contextlib.suppress(Exception):
            await w.wait_closed()
        return True
    except Exception:
        return False


async def probe_local_network() -> bool:
    """True if this machine can open outbound TCP connections to at least one well-known host."""
    async def one(hp: str) -> bool:
        host, _, port = hp.rpartition(":")
        return await _tcp_ok(host, int(port), CFG.net_probe_timeout)
    results = await asyncio.gather(*(one(h) for h in CFG.net_probe_hosts), return_exceptions=True)
    return any(r is True for r in results)


class NetGuard:
    """If almost every recent test failed at TCP/connect level, check whether OUR network is down
    (as opposed to the proxies). While down: testing pauses and the innocent failures are forgiven."""

    def __init__(self) -> None:
        self.window: deque = deque(maxlen=CFG.circuit_window)
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
        """Call periodically. Returns pairs to forgive when an outage has just been detected."""
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


async def diagnose_environment(rt, target: Target) -> dict:
    net = await probe_local_network()
    pu = urlparse(target.url)
    port = pu.port or (443 if pu.scheme == "https" else 80)
    direct = await _tcp_ok(pu.hostname or "", port, CFG.net_probe_timeout) if pu.hostname else False
    diag = {"local_network": "ok" if net else "DOWN",
            "target_direct_tcp": "ok" if direct else "unreachable",
            "browsers_alive": len(rt.pool.recs), "browsers_expected": CFG.browser_count}
    if not net:
        diag["verdict"] = "local network / DNS problem"
    elif not direct:
        diag["verdict"] = "target unreachable from this host (target outage or routing)"
    elif len(rt.pool.recs) < CFG.browser_count:
        diag["verdict"] = "Chromium instability"
    else:
        diag["verdict"] = "target-side blocking or mass proxy failure"
    return diag


# ══════════════════════════════════════════════════════════════════════════════
#  DASHBOARD - a handful of lines, redrawn in place
# ══════════════════════════════════════════════════════════════════════════════
class Dashboard:
    def __init__(self) -> None:
        self.is_tty = sys.stdout.isatty()
        self.started = time.time()
        self.busy = 0
        self.last_action = "booting"
        self.state: dict = {"total": 0, "global": {}, "targets": {}, "circuits": {}, "queue": 0,
                            "in_flight": 0, "due": 0, "workers_alive": 0, "browsers": 0, "paused": ""}
        self._last_render = 0.0

    def update(self, **kw) -> None:
        if "global_" in kw:
            kw["global"] = kw.pop("global_")
        self.state.update(kw)

    def bump(self, d: int) -> None:
        self.busy = max(0, self.busy + d)

    def lines(self) -> list[str]:
        s, g = self.state, self.state["global"]
        up = int(time.time() - self.started)
        h, rem = divmod(up, 3600)
        m, sec = divmod(rem, 60)
        L = [
            f"RADIATE PROXY MONITOR v{VERSION}   Runtime {h:02d}:{m:02d}:{sec:02d}   "
            f"Workers {s['workers_alive']}/{CFG.worker_count} (busy {self.busy})   Browsers {s['browsers']}",
            f"Queue {s['queue']}   Retesting {s['in_flight']}   Due {s['due']:,}   "
            f"Proxies {s['total']:,}   Targets {len(s['targets'])}"
            + (f"   ** PAUSED: {s['paused']} **" if s["paused"] else ""),
            f"Working {g.get('WORKING', 0):,}   Retryable {g.get('RETRYABLE', 0):,}   "
            f"Quarantined {g.get('QUARANTINED', 0):,}   Failed {g.get('FAILED', 0):,}   "
            f"Untested {g.get('UNTESTED', 0):,}",
        ]
        for tid, st in list(s["targets"].items())[:5]:
            ok = st.get("WORKING", 0) + st.get("RECOVERED", 0)
            L.append(f"  {tid[:24]:<24} ok {ok:<5} retry {st.get('RETRYABLE', 0):<4} "
                     f"quar {st.get('QUARANTINED', 0):<4} fail {st.get('FAILED', 0):<4} "
                     f"new {st.get('UNTESTED', 0):<4} circuit {s['circuits'].get(tid, 'closed')}")
        if len(s["targets"]) > 5:
            L.append(f"  (+{len(s['targets']) - 5} more targets)")
        L.append(f"Last: {self.last_action}")
        return L

    def render(self, force: bool = False) -> None:
        if not self.is_tty:
            return
        now = time.time()
        if not force and now - self._last_render < CFG.dashboard_refresh:
            return
        self._last_render = now
        width = shutil.get_terminal_size((100, 24)).columns
        try:
            sys.stdout.write("\033[H" + "".join(ln[:width - 1] + "\033[K\n" for ln in self.lines()) + "\033[J")
            sys.stdout.flush()
        except Exception:
            pass

    def clear(self) -> None:
        if self.is_tty:
            with contextlib.suppress(Exception):
                sys.stdout.write("\033[H\033[J")
                sys.stdout.flush()


# ══════════════════════════════════════════════════════════════════════════════
#  BROWSER PROFILES - internally consistent by construction
#  UA OS == host OS (so Chromium's own Client-Hints agree) and Chrome major == the real engine version.
#  No JS spoofing, no header overrides.
# ══════════════════════════════════════════════════════════════════════════════
_UA_TEMPLATES = {
    "Windows": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
               "Chrome/{v}.0.0.0 Safari/537.36",
    "macOS":   "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) "
               "Chrome/{v}.0.0.0 Safari/537.36",
    "Linux":   "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) "
               "Chrome/{v}.0.0.0 Safari/537.36",
}
_VIEWPORTS = {
    "Windows": [(1280, 720), (1366, 768), (1536, 864), (1920, 1080)],
    "macOS":   [(1440, 900), (1512, 982), (1728, 1117)],
    "Linux":   [(1280, 720), (1366, 768), (1600, 900), (1920, 1080)],
}
_LOCALES = [("en-US", "America/New_York"), ("en-US", "America/Chicago"),
            ("en-US", "America/Los_Angeles"), ("en-GB", "Europe/London")]

_REMOTE_UA_LIST = []


def _host_os() -> str:
    if sys.platform.startswith("win"):
        return "Windows"
    return "macOS" if sys.platform == "darwin" else "Linux"


def make_profile(browser_version: str) -> dict:
    if CFG.custom_ua_profiles:
        p = random.choice(CFG.custom_ua_profiles)
        return {"ua": p["ua"], "viewport": {"width": int(p.get("width", 1366)), "height": int(p.get("height", 768))},
                "locale": p.get("locale", "en-US"), "tz": p.get("tz", "America/New_York")}
    if not CFG.ua_rotation:
        return {}
        
    m = re.match(r"(\d+)", browser_version or "")
    major = m.group(1) if m else "128"
    os_name = _host_os()
    
    if CFG.ua_pool_remote and _REMOTE_UA_LIST:
        ua_str = random.choice(_REMOTE_UA_LIST)
    else:
        ua_str = _UA_TEMPLATES[os_name].format(v=major)
        
    w, h = random.choice(_VIEWPORTS[os_name])
    loc, tz = random.choice(_LOCALES)
    return {"ua": ua_str, "viewport": {"width": w, "height": h},
            "locale": loc, "tz": tz}


# ══════════════════════════════════════════════════════════════════════════════
#  BROWSER POOL - persistent Chromium processes, N isolated contexts each,
#  self-healing (crash -> replace ONCE), periodic recycling (leak control)
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
        self.slots: asyncio.Queue = asyncio.Queue()      # tokens = browser ids (one per free context slot)
        self.recs: dict[int, BrowserRec] = {}
        self._next = 0
        self._lock = asyncio.Lock()
        self._stopping = False
        self.restarts = 0

    async def _launch(self) -> Optional[BrowserRec]:
        try:
            b = await asyncio.wait_for(self._launcher(), timeout=60)
        except Exception as exc:
            elog.error("Chromium launch failed: %s", exc)
            return None
        self._next += 1
        rec = BrowserRec(self._next, b)
        self.recs[rec.bid] = rec
        for _ in range(CFG.contexts_per_browser):
            self.slots.put_nowait(rec.bid)
        rlog.info("Chromium launched id=%d slots=%d browsers=%d", rec.bid, CFG.contexts_per_browser, len(self.recs))
        return rec

    async def start(self) -> None:
        for _ in range(CFG.browser_count):
            await self._launch()

    async def ensure_capacity(self) -> None:
        """Called periodically: relaunch anything that failed to come back."""
        async with self._lock:
            while not self._stopping and len(self.recs) < CFG.browser_count:
                if await self._launch() is None:
                    break

    async def _replace(self, bid: int, reason: str) -> None:
        async with self._lock:
            rec = self.recs.pop(bid, None)          # idempotent: 5 dead slots => ONE replacement
            if rec is None:
                return
            self.restarts += 1
            rlog.warning("Chromium id=%d removed (%s) - launching replacement", bid, reason)
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
                continue                             # stale token of a replaced / retiring browser: drop it
            if not rec.browser.is_connected():
                await self._replace(bid, "disconnected")
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
            await self._replace(bid, "crash detected")
            return
        if not rec.retiring and rec.uses >= CFG.browser_recycle_after:
            rec.retiring = True
        if rec.retiring:
            if rec.active == 0:
                await self._replace(bid, f"recycled after {rec.uses} contexts")
            return
        self.slots.put_nowait(bid)

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
    latency_seconds: Optional[float] = None     # time to first navigation response (used for scoring)
    error: Optional[str] = None
    title: str = ""
    browser_crashed: bool = False


class StepError(Exception):
    pass


class BrowserCrashed(Exception):
    pass


class ConnectionLost(Exception):
    pass


async def run_interaction_steps(page, steps: list) -> None:
    """Configurable, deterministic page interaction (functional testing). Unknown actions are logged."""
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
                else:
                    vlog.debug("move_mouse step ignored: needs explicit x and y")
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
            else:
                vlog.warning("unknown interaction action %r ignored", action)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            if required:
                raise StepError(f"required step {action} failed: {str(exc)[:200]}") from exc
            vlog.debug("optional step %s failed: %s", action, exc)


_NET_ERRORS = [   # (chromium net error substring, our category)
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
    if any(w in low for w in _CRASH_WORDS):
        return "BROWSER_ERROR"
    return "BROWSER_ERROR"


_STRIP_BLOCKS = re.compile(r"(?is)<(script|style|noscript)[^>]*>.*?</\1>")
_STRIP_TAGS = re.compile(r"(?s)<[^>]+>")


async def _inner_validate(browser, proxy: str, target: Target, profile: dict, state_file: Optional[Path]) -> ValidationResult:
    t0 = time.monotonic()
    flags = {"crashed": False, "req_failed": 0}
    ctx = None
    latency: Optional[float] = None
    http_status: Optional[int] = None
    title = ""

    def elapsed() -> float:
        return round(time.monotonic() - t0, 2)

    try:
        kw: dict = {"proxy": build_proxy_config(proxy), "ignore_https_errors": CFG.ignore_https_errors}
        if profile:
            kw.update(user_agent=profile["ua"], viewport=profile["viewport"], screen=profile["viewport"],
                      locale=profile["locale"], timezone_id=profile["tz"])
            # Feature: Set Deep Referer header if requested
            kw["extra_http_headers"] = {"Referer": "https://www.keralacaptain.shop/"}
            
        if CFG.session_cache_enabled and state_file and state_file.exists():
            kw["storage_state"] = str(state_file)
            
        ctx = await browser.new_context(**kw)
        
        if CFG.enable_stealth_script:
            await ctx.add_init_script("""
                Object.defineProperty(navigator, 'webdriver', {get: () => undefined});
                window.chrome = { runtime: {} };
                Object.defineProperty(navigator, 'languages', {get: () => ['en-US', 'en']});
                Object.defineProperty(navigator, 'plugins', {get: () => [1, 2, 3]});
            """)
            
        page = await ctx.new_page()
        page.set_default_timeout(target.navigation_timeout_ms)
        page.on("crash", lambda *_: flags.__setitem__("crashed", True))
        page.on("requestfailed", lambda *_: flags.__setitem__("req_failed", flags["req_failed"] + 1))

        t_nav = time.monotonic()
        response = await page.goto(target.url, wait_until="domcontentloaded",
                                   timeout=target.navigation_timeout_ms)
        latency = round(time.monotonic() - t_nav, 2)
        http_status = response.status if response else None

        if target.interaction_steps:
            await run_interaction_steps(page, target.interaction_steps)
        else:
            # Hyper-Realistic Human Behavior (Anti-Bot Evasion fallback when no steps defined)
            await page.mouse.move(random.randint(100, 500), random.randint(100, 500), steps=random.randint(5, 15))
            await page.mouse.wheel(0, random.randint(200, 600))
            await page.wait_for_timeout(random.randint(800, 2000))
            await page.mouse.move(random.randint(200, 600), random.randint(200, 800), steps=random.randint(5, 20))
            await page.mouse.wheel(0, random.randint(-200, 400))
            
        if target.reload_after_load:
            await page.reload(wait_until="domcontentloaded", timeout=target.navigation_timeout_ms)

        # verification window - sliced so a crash / lost connection is noticed early
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

        visible = ""
        with contextlib.suppress(Exception):
            visible = await page.evaluate("() => document.body ? document.body.innerText : ''")
        html = ""
        need_html = (not visible.strip()) or any(m.startswith("html:") for m in target.forbidden_markers)
        if need_html:
            with contextlib.suppress(Exception):
                html = await page.content()
        if not visible.strip() and html:
            visible = _STRIP_TAGS.sub(" ", _STRIP_BLOCKS.sub(" ", html))
        visible = re.sub(r"\s+", " ", visible).strip()
        text = (title + " " + visible).lower()
        html_l = html.lower()
        el = elapsed()

        for marker in target.forbidden_markers:
            hit = (marker[5:] in html_l) if marker.startswith("html:") else (marker in text)
            if hit:
                return ValidationResult("TARGET_VALIDATION_FAILED", http_status, el, latency,
                                        f"forbidden marker: {marker}", title)
        for sel in target.forbidden_selectors:
            with contextlib.suppress(Exception):
                if await page.locator(sel).count() > 0:
                    return ValidationResult("TARGET_VALIDATION_FAILED", http_status, el, latency,
                                            f"forbidden selector: {sel}", title)
        if target.require_status_200 and http_status != 200:
            return ValidationResult("HTTP_ERROR", http_status, el, latency, f"status {http_status}", title)
        if http_status is not None and http_status >= 400:
            return ValidationResult("HTTP_ERROR", http_status, el, latency, f"status {http_status}", title)
        if len(visible) < target.min_body_length:
            return ValidationResult("EMPTY_RESPONSE", http_status, el, latency, f"body {len(visible)} chars", title)
        if target.success_markers and not any(m in text for m in target.success_markers):
            return ValidationResult("TARGET_VALIDATION_FAILED", http_status, el, latency, "no success marker", title)
        if target.title_contains and not any(m.lower() in title.lower() for m in target.title_contains):
            return ValidationResult("TARGET_VALIDATION_FAILED", http_status, el, latency, "title mismatch", title)
        if target.success_selectors:
            found = []
            for sel in target.success_selectors:
                ok = False
                with contextlib.suppress(Exception):
                    ok = await page.locator(sel).count() > 0
                found.append(ok)
            good = all(found) if target.success_selectors_mode == "all" else any(found)
            if not good:
                return ValidationResult("TARGET_VALIDATION_FAILED", http_status, el, latency,
                                        "expected element missing", title)
                                        
        if CFG.session_cache_enabled and state_file:
            with contextlib.suppress(Exception):
                await ctx.storage_state(path=str(state_file))
                
        return ValidationResult("WORKING", http_status, el, latency, None, title)

    except asyncio.CancelledError:
        raise
    except StepError as exc:
        return ValidationResult("TARGET_VALIDATION_FAILED", http_status, elapsed(), latency, str(exc)[:400], title)
    except BrowserCrashed as exc:
        return ValidationResult("BROWSER_ERROR", http_status, elapsed(), latency, str(exc), title, True)
    except ConnectionLost as exc:
        return ValidationResult("CONNECTION_TIMEOUT", http_status, elapsed(), latency, str(exc), title)
    except PlaywrightError as exc:
        cat = classify_playwright_error(exc)
        return ValidationResult(cat, http_status, elapsed(), latency, str(exc).replace("\n", " ")[:400], title,
                                flags["crashed"] or (cat == "BROWSER_ERROR"
                                                     and any(w in str(exc).lower() for w in _CRASH_WORDS)))
    except Exception as exc:
        return ValidationResult("RETRYABLE_ERROR", http_status, elapsed(), latency,
                                f"{type(exc).__name__}: {exc}"[:400], title)
    finally:
        if ctx is not None:                          # contexts are ALWAYS closed, and closing can never hang a worker
            with contextlib.suppress(Exception):
                await asyncio.wait_for(ctx.close(), timeout=10)


async def validate_proxy(browser, proxy: str, target: Target, profile: dict) -> ValidationResult:
    hard = target.navigation_timeout_ms / 1000.0 * 2 + target.post_load_wait_seconds + CFG.hard_timeout_extra_seconds
    t0 = time.monotonic()
    try:
        state_file = None
        if CFG.session_cache_enabled:
            h = hashlib.sha256(proxy.encode()).hexdigest()[:20]
            state_file = SESSIONS_DIR / f"{h}.json"
            
        return await asyncio.wait_for(_inner_validate(browser, proxy, target, profile, state_file), timeout=hard)
    except asyncio.TimeoutError:
        return ValidationResult("NAVIGATION_TIMEOUT", None, round(time.monotonic() - t0, 2), None,
                                f"hard timeout {int(hard)}s")


# ══════════════════════════════════════════════════════════════════════════════
#  TELEGRAM NOTIFIER - fire-and-forget, never blocks the daemon
# ══════════════════════════════════════════════════════════════════════════════
class TelegramNotifier:
    def __init__(self, token: str, chat_id: str) -> None:
        self.token = token
        self.chat_id = chat_id
        self.enabled = bool(token and chat_id)
        self._queue: asyncio.Queue = asyncio.Queue(maxsize=50)
        self._last_sent: dict[str, float] = {}
        self._session = None
        self._task: Optional[asyncio.Task] = None

    async def start(self) -> None:
        if not self.enabled:
            return
        try:
            import aiohttp  # noqa: F401  -- confirm it's importable before spawning the worker
        except ImportError:
            elog.error("telegram: aiohttp not installed; notifications disabled "
                       "(pip install aiohttp --break-system-packages)")
            self.enabled = False
            return
        self._task = asyncio.create_task(self._worker(), name="telegram")

    def notify(self, text: str, dedupe_key: Optional[str] = None, min_gap: float = 0.0) -> None:
        if not self.enabled:
            return
        if dedupe_key:
            last = self._last_sent.get(dedupe_key, 0.0)
            if time.time() - last < min_gap:
                return
            self._last_sent[dedupe_key] = time.time()
        try:
            self._queue.put_nowait(text)
        except asyncio.QueueFull:
            elog.warning("telegram queue full, dropping message")

    async def _worker(self) -> None:
        import aiohttp
        url = f"https://api.telegram.org/bot{self.token}/sendMessage"
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as sess:
            while True:
                text = await self._queue.get()
                try:
                    async with sess.post(url, json={"chat_id": self.chat_id, "text": text[:4000]}) as r:
                        if r.status != 200:
                            elog.warning("telegram send failed: HTTP %d", r.status)
                except asyncio.CancelledError:
                    raise
                except Exception as exc:
                    elog.warning("telegram send error: %s", exc)

    async def stop(self) -> None:
        if self._task:
            self._task.cancel()
            with contextlib.suppress(asyncio.CancelledError, Exception):
                await self._task


# ══════════════════════════════════════════════════════════════════════════════
#  EXTERNAL PROXY FALLBACK - only used when the pool you provided runs dry;
#  never runs continuously in the background (requirement #1: no permanent
#  external fetching). Disabled unless you set fallback_urls in config.json.
# ══════════════════════════════════════════════════════════════════════════════
_PROXY_LINE_RE = re.compile(r"\b(?:\d{1,3}\.){3}\d{1,3}:\d{1,5}\b")


def parse_fallback_text(text: str) -> list[str]:
    out, seen = [], set()
    for raw in re.split(r"[\r\n]+", text):
        raw = raw.strip()
        if not raw:
            continue
        m = _PROXY_LINE_RE.search(raw)
        candidate = m.group(0) if m else raw
        p = normalize_proxy(candidate)
        if p and p not in seen:
            seen.add(p)
            out.append(p)
    return out


async def fetch_fallback_proxies(urls: list[str], timeout: float = 20.0) -> list[str]:
    try:
        import aiohttp
    except ImportError:
        elog.error("fallback fetch: aiohttp not installed; skipping "
                   "(pip install aiohttp --break-system-packages)")
        return []
    out, seen = [], set()
    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=timeout)) as sess:
        for url in urls:
            try:
                async with sess.get(url) as r:
                    if r.status != 200:
                        log.warning("fallback source %s -> HTTP %d", url, r.status)
                        continue
                    text = await r.text(errors="ignore")
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                log.warning("fallback source %s failed: %s", url, exc)
                continue
            for p in parse_fallback_text(text):
                if p not in seen:
                    seen.add(p)
                    out.append(p)
            log.info("fallback source %s: %d proxies parsed", url, len(parse_fallback_text(text)))
    return out


# ══════════════════════════════════════════════════════════════════════════════
#  MEMORY GUARD - throttles new claims instead of letting Chromium OOM the box
# ══════════════════════════════════════════════════════════════════════════════
def memory_percent() -> Optional[float]:
    if psutil is None:
        return None
    try:
        return psutil.virtual_memory().percent
    except Exception:
        return None


# ══════════════════════════════════════════════════════════════════════════════
#  RUNTIME - everything the loops share
# ══════════════════════════════════════════════════════════════════════════════
class Runtime:
    def __init__(self, store: Store, pool: BrowserPool, registry: TargetRegistry,
                 circuit: TargetCircuit, netguard: NetGuard, dashboard: Dashboard,
                 notifier: TelegramNotifier, stop_event: asyncio.Event) -> None:
        self.store = store
        self.pool = pool
        self.registry = registry
        self.circuit = circuit
        self.netguard = netguard
        self.dashboard = dashboard
        self.notifier = notifier
        self.stop_event = stop_event
        self.queue: asyncio.Queue = asyncio.Queue(maxsize=max(CFG.worker_count + CFG.queue_extra, 8))
        self.workers_alive = 0
        self.paused_reason = ""
        self.browser_version = ""
        self.last_pool_empty_alert = 0.0
        self.restart_requested = False
        self._target_cursor = 0   # rotates which target gets first pick of the queue each tick
        self.circuit_trips = 0
        self.worker_restarts = 0


async def _sleep_or_stop(stop_event: asyncio.Event, seconds: float) -> None:
    with contextlib.suppress(asyncio.TimeoutError):
        await asyncio.wait_for(stop_event.wait(), timeout=seconds)


# ══════════════════════════════════════════════════════════════════════════════
#  SCHEDULER LOOP - claims eligible work per target, applies the circuit
#  breaker's half-open probe budget, and refuses to overfill the queue.
# ══════════════════════════════════════════════════════════════════════════════
async def scheduler_loop(rt: Runtime) -> None:
    while not rt.stop_event.is_set():
        try:
            if rt.registry.changed():
                if rt.registry.reload():
                    r = await rt.store.sync_targets(list(rt.registry.targets.values()))
                    log.info("targets reloaded: %d rows backfilled, %d disabled",
                             r["rows_created"], r["disabled_missing"])

            mem = memory_percent()
            if mem is not None and mem >= CFG.memory_high_percent:
                rt.paused_reason = f"memory {mem:.0f}%"
            else:
                rt.paused_reason = ""

            if not rt.paused_reason:
                live = rt.registry.enabled()
                if live:
                    rt._target_cursor %= len(live)
                    live = live[rt._target_cursor:] + live[:rt._target_cursor]
                    rt._target_cursor += 1
                for t in live:
                    free = rt.queue.maxsize - rt.queue.qsize()
                    if free <= 0:
                        break
                    if rt.circuit.blocked(t.target_id):
                        continue
                    want = rt.circuit.reserve(t.target_id, min(free, CFG.batch_size_per_tick))
                    if want <= 0:
                        continue
                    batch = await rt.store.claim_batch(t.target_id, want)
                    for pid, proxy in batch:
                        await rt.queue.put((pid, proxy, t.target_id))
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            elog.exception("scheduler error: %s", exc)
        await _sleep_or_stop(rt.stop_event, CFG.scheduler_tick_seconds)


# ══════════════════════════════════════════════════════════════════════════════
#  WORKER LOOP
# ══════════════════════════════════════════════════════════════════════════════
async def worker_loop(wid: int, rt: Runtime) -> None:
    rt.workers_alive += 1
    try:
        while not rt.stop_event.is_set():
            try:
                item = await asyncio.wait_for(rt.queue.get(), timeout=1.0)
            except asyncio.TimeoutError:
                continue

            proxy_id, proxy, target_id = item
            target = rt.registry.get(target_id)
            if target is None or not target.enabled:
                with contextlib.suppress(Exception):
                    rt.queue.task_done()
                await rt.store.release_claims([(proxy_id, target_id)])
                continue

            rt.dashboard.bump(1)
            bid = None
            try:
                if not await tcp_preflight(proxy, CFG.tcp_preflight_timeout):
                    res = ValidationResult("TCP_FAILURE", error="tcp preflight failed")
                    await _finish(rt, wid, -1, proxy_id, proxy, target_id, res)  # -1 = no browser used (TCP preflight failed)
                    continue

                await asyncio.sleep(random.uniform(CFG.connect_jitter_min, CFG.connect_jitter_max))
                acquired = await rt.pool.acquire(timeout=45.0)
                if acquired is None:
                    await rt.store.release_claims([(proxy_id, target_id)])
                    elog.error("W%d: no browser slot available within timeout", wid)
                    await asyncio.sleep(2.0)
                    await rt.queue.put(item)
                    rt.queue.task_done()
                    continue
                bid, browser = acquired
                profile = make_profile(rt.browser_version)
                res = None
                try:
                    res = await validate_proxy(browser, proxy, target, profile)
                finally:
                    await rt.pool.release(bid, crashed=bool(res and res.browser_crashed))

                await _finish(rt, wid, bid, proxy_id, proxy, target_id, res)

            except asyncio.CancelledError:
                raise   # the inner `finally` above already released the browser slot exactly once
            except Exception as exc:
                elog.exception("W%d crashed on %s: %s", wid, mask_proxy(proxy), exc)
                with contextlib.suppress(Exception):
                    await rt.store.release_claims([(proxy_id, target_id)])
            finally:
                rt.dashboard.bump(-1)
                with contextlib.suppress(Exception):
                    rt.queue.task_done()
    finally:
        rt.workers_alive = max(0, rt.workers_alive - 1)


async def _finish(rt: Runtime, wid: int, bid: int, proxy_id: int, proxy: str, target_id: str,
                  res: ValidationResult) -> None:
    target = rt.registry.get(target_id)
    overrides = target.cooldowns if target else {}
    new_status, prior_success = await rt.store.record(proxy_id, target_id, res, wid, bid, overrides)
    rt.netguard.record(target_id, proxy_id, res.status)
    forgive, event = rt.circuit.record(target_id, proxy_id, res.status, prior_success)
    if forgive:
        n = await rt.store.forgive(forgive, CFG.circuit_cooldown)
        rlog.info("forgave %d proxy result(s) on %s after circuit event", n, target_id)
    if event == "tripped":
        rt.circuit_trips += 1
        rt.notifier.notify(f"\u26a0\ufe0f Circuit OPEN on {target_id}: abnormal failure rate detected, "
                           f"testing paused and recent failures forgiven.", dedupe_key=f"trip:{target_id}", min_gap=600)
    elif event == "reopened":
        rt.notifier.notify(f"\u26a0\ufe0f {target_id}: recovery probe failed again, staying paused (longer backoff).",
                           dedupe_key=f"reopen:{target_id}", min_gap=600)
    elif event == "closed":
        rt.notifier.notify(f"\u2705 {target_id}: circuit closed, testing resumed normally.",
                           dedupe_key=f"closed:{target_id}", min_gap=60)

    if res.status == "WORKING":
        rt.dashboard.update(last_action=f"OK  {mask_proxy(proxy)} -> {target_id}")
        vlog.info("W%d %s %s WORKING %.2fs http=%s", wid, target_id, mask_proxy(proxy),
                  res.elapsed_seconds or 0, res.http_status)
    else:
        rt.dashboard.update(last_action=f"{res.status}  {mask_proxy(proxy)} -> {target_id}")
        vlog.info("W%d %s %s %s %s", wid, target_id, mask_proxy(proxy), res.status, (res.error or "")[:160])


# ══════════════════════════════════════════════════════════════════════════════
#  SUPERVISOR - restarts a dead worker task; never lets one failure kill the daemon
# ══════════════════════════════════════════════════════════════════════════════
async def supervisor_loop(rt: Runtime, workers: list) -> None:
    while not rt.stop_event.is_set():
        done, _ = await asyncio.wait(workers, return_when=asyncio.FIRST_COMPLETED)
        for i, w in enumerate(workers):
            if w in done and not rt.stop_event.is_set():
                exc = w.exception() if not w.cancelled() else None
                if exc:
                    elog.error("worker-%d died (%s); restarting", i, exc)
                else:
                    rlog.warning("worker-%d exited; restarting", i)
                rt.worker_restarts += 1
                workers[i] = asyncio.create_task(worker_loop(i, rt), name=f"worker-{i}")


# ══════════════════════════════════════════════════════════════════════════════
#  BROWSER POOL MAINTAINER + NET GUARD + FALLBACK TRIGGER
# ══════════════════════════════════════════════════════════════════════════════
async def pool_guard_loop(rt: Runtime) -> None:
    while not rt.stop_event.is_set():
        try:
            await rt.pool.ensure_capacity()
            forgive = await rt.netguard.check()
            if forgive:
                n = await rt.store.forgive(forgive, CFG.circuit_cooldown)
                rt.notifier.notify(f"\U0001f6a8 Local network outage detected - testing paused, "
                                   f"{n} result(s) forgiven.", dedupe_key="netdown", min_gap=600)
            elif rt.netguard.down is False and rt.netguard.window and rt.netguard.was_down:
                rt.notifier.notify("\u2705 Local network restored.", dedupe_key="netup", min_gap=60)
                rt.netguard.was_down = False
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            elog.exception("pool guard error: %s", exc)
        await _sleep_or_stop(rt.stop_event, 15.0)


async def fallback_loop(rt: Runtime, fallback_urls: list[str], min_working: int, cooldown: float) -> None:
    """Optional (disabled unless fallback_urls is set). Fetches MORE proxies only when the pool you
    provided is running dry - never a continuous public-list downloader."""
    if not fallback_urls:
        return
    last_fetch = 0.0
    while not rt.stop_event.is_set():
        try:
            stats = await rt.store.stats()
            working = stats["global"].get("WORKING", 0) + stats["global"].get("RECOVERED", 0)
            if working < min_working and time.time() - last_fetch >= cooldown:
                last_fetch = time.time()
                log.warning("pool depleted (%d working < %d threshold) - fetching fallback proxies", working, min_working)
                rt.notifier.notify(f"\U0001f501 Proxy pool depleted ({working} working) - fetching fallback proxies.",
                                   dedupe_key="fallback", min_gap=cooldown)
                fetched = await fetch_fallback_proxies(fallback_urls)
                if fetched:
                    r = await rt.store.ingest_proxies(fetched)
                    log.info("fallback ingest: %d new, %d existing, %d new proxy_target rows",
                             r["inserted"], r["existing"], r["rows_created"])
                    rt.notifier.notify(f"\u2795 Fallback fetch added {r['inserted']} new proxies "
                                       f"({r['existing']} already known).", dedupe_key="fallback_done", min_gap=60)
                else:
                    elog.warning("fallback fetch returned no usable proxies")
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            elog.exception("fallback loop error: %s", exc)
        await _sleep_or_stop(rt.stop_event, 60.0)


# ══════════════════════════════════════════════════════════════════════════════
#  UA POOL REFRESH LOOP
# ══════════════════════════════════════════════════════════════════════════════
async def ua_refresh_loop(rt: Runtime) -> None:
    if not CFG.ua_pool_remote:
        return
    while not rt.stop_event.is_set():
        try:
            import aiohttp
            async with aiohttp.ClientSession() as sess:
                async with sess.get("https://raw.githubusercontent.com/intoli/user-agents/master/src/user-agents.json", timeout=30) as r:
                    if r.status == 200:
                        data = await r.json()
                        _REMOTE_UA_LIST.clear()
                        _REMOTE_UA_LIST.extend([item["userAgent"] for item in data if "userAgent" in item])
                        log.info("Fetched %d UAs from remote pool", len(_REMOTE_UA_LIST))
        except asyncio.CancelledError:
            raise
        except Exception as e:
            elog.warning("ua fetch failed: %s", e)
        await _sleep_or_stop(rt.stop_event, CFG.ua_pool_refresh_seconds)


# ══════════════════════════════════════════════════════════════════════════════
#  DASHBOARD LOOP
# ══════════════════════════════════════════════════════════════════════════════
async def dashboard_loop(rt: Runtime) -> None:
    while not rt.stop_event.is_set():
        try:
            stats = await rt.store.stats()
            rt.dashboard.update(
                total=stats["proxies_total"], global_=stats["global"], targets=stats["targets"],
                circuits=rt.circuit.state_dict(), queue=rt.queue.qsize(), in_flight=stats["in_flight"],
                due=stats["due"], workers_alive=rt.workers_alive, browsers=len(rt.pool.recs),
                paused=rt.paused_reason or ("network down" if rt.netguard.down else ""))
            rt.dashboard.render()
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            elog.exception("dashboard error: %s", exc)
        await _sleep_or_stop(rt.stop_event, CFG.dashboard_refresh)


# ══════════════════════════════════════════════════════════════════════════════
#  OUTPUT LOOP - validated_proxies.txt, rewritten only when it actually changes
# ══════════════════════════════════════════════════════════════════════════════
def _format_output(per_target: dict, flat: list) -> str:
    lines = ["# validated_proxies.txt - proxies currently WORKING/RECOVERED",
             f"# generated {time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime())}", ""]
    lines.append(f"# ---- all targets (mode={CFG.output_mode}) ----")
    lines.extend(flat)
    lines.append("")
    for tid, plist in sorted(per_target.items()):
        lines.append(f"# ---- target: {tid} ({len(plist)}) ----")
        lines.extend(plist)
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


async def output_loop(rt: Runtime) -> None:
    last_sig = None
    while not rt.stop_event.is_set():
        try:
            per_target, flat = await rt.store.working_lists(CFG.output_mode, CFG.output_max_age_seconds)
            content = _format_output(per_target, flat)
            sig = hashlib.sha1(content.encode()).hexdigest()
            if sig != last_sig:
                _atomic_write(OUTPUT_FILE, content)
                last_sig = sig
                log.info("output updated: %d combined, %d per-target lists", len(flat), len(per_target))
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            elog.exception("output error: %s", exc)
        await _sleep_or_stop(rt.stop_event, CFG.output_flush_interval)


# ══════════════════════════════════════════════════════════════════════════════
#  MAINTENANCE LOOP - history pruning, backups, DB integrity check, proxy-file watch
# ══════════════════════════════════════════════════════════════════════════════
async def maintenance_loop(rt: Runtime) -> None:
    last_backup = 0.0
    last_sig = proxy_files_signature()
    next_tick = time.time() + 30.0
    while not rt.stop_event.is_set():
        delay = next_tick - time.time()
        if delay > 0:
            await _sleep_or_stop(rt.stop_event, delay)
        if rt.stop_event.is_set():
            return
        next_tick = time.time() + CFG.maintenance_interval_seconds
        try:
            if CFG.proxy_file_watch:
                sig = proxy_files_signature()
                if sig != last_sig:
                    last_sig = sig
                    proxies = load_all_proxy_files()
                    if proxies:
                        r = await rt.store.ingest_proxies(proxies)
                        if r["inserted"] or r["rows_created"]:
                            log.info("proxy file change detected: %d new proxies, %d new rows",
                                     r["inserted"], r["rows_created"])

            pruned = await rt.store.prune_history(CFG.history_retention_days)
            if pruned:
                log.info("history pruned: %d rows", pruned)
            await rt.store.checkpoint()

            if time.time() - last_backup >= CFG.backup_interval_hours * 3600:
                last_backup = time.time()
                integ = await rt.store.integrity()
                if integ != "ok":
                    elog.error("integrity check reported: %s", integ)
                    rt.notifier.notify(f"\U0001f6a8 Database integrity check failed: {integ}",
                                       dedupe_key="integrity", min_gap=3600)
                path = await rt.store.backup(BACKUP_DIR, CFG.backup_keep)
                log.info("backup written: %s", path.name)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            elog.exception("maintenance error: %s", exc)


# ══════════════════════════════════════════════════════════════════════════════
#  METRICS SNAPSHOT LOOP
# ══════════════════════════════════════════════════════════════════════════════
async def metrics_loop(rt: Runtime) -> None:
    while not rt.stop_event.is_set():
        try:
            stats = await rt.store.stats()
            out = {
                "proxies_total": stats["proxies_total"],
                "targets": stats["targets"],
                "in_flight": stats["in_flight"],
                "due": stats["due"],
                "queue": rt.queue.qsize(),
                "workers_alive": rt.workers_alive,
                "browsers": len(rt.pool.recs),
                "circuits": rt.circuit.state_dict(),
                "uptime_seconds": int(time.time() - rt.dashboard.started),
                "version": VERSION,
                "circuit_trips": getattr(rt, "circuit_trips", 0),
                "worker_restarts": getattr(rt, "worker_restarts", 0) + rt.pool.restarts
            }
            _atomic_write(_rp(CFG.metrics_file), json.dumps(out, indent=2))
        except asyncio.CancelledError:
            raise
        except Exception as e:
            elog.warning("metrics error: %s", e)
        await _sleep_or_stop(rt.stop_event, CFG.metrics_interval_seconds)


# ══════════════════════════════════════════════════════════════════════════════
#  TELEGRAM SUMMARY LOOP
# ══════════════════════════════════════════════════════════════════════════════
async def telegram_summary_loop(rt: Runtime, interval: float) -> None:
    if not rt.notifier.enabled or interval <= 0:
        return
    started = time.time()
    rt.notifier.notify(f"\U0001f7e2 Radiate Proxy Monitor v{VERSION} started.", dedupe_key="start", min_gap=5)
    while not rt.stop_event.is_set():
        await _sleep_or_stop(rt.stop_event, interval)
        if rt.stop_event.is_set():
            return
        try:
            stats = await rt.store.stats()
            g = stats["global"]
            up = int(time.time() - started)
            h, rem = divmod(up, 3600)
            m, _ = divmod(rem, 60)
            text = (f"\U0001f4ca Radiate summary\n"
                    f"Uptime: {h}h{m:02d}m\n"
                    f"Total proxies: {stats['proxies_total']:,}\n"
                    f"Working: {g.get('WORKING', 0):,}   Retryable: {g.get('RETRYABLE', 0):,}\n"
                    f"Quarantined: {g.get('QUARANTINED', 0):,}   Failed (banned): {g.get('FAILED', 0):,}\n"
                    f"Untested: {g.get('UNTESTED', 0):,}   In-flight: {stats['in_flight']:,}")
            rt.notifier.notify(text)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            elog.exception("telegram summary error: %s", exc)


# ══════════════════════════════════════════════════════════════════════════════
#  HTTP HEALTH ENDPOINT
# ══════════════════════════════════════════════════════════════════════════════
async def http_health_server(reader, writer, rt: Runtime):
    try:
        line = await asyncio.wait_for(reader.readline(), timeout=2.0)
        req = line.decode().strip()
        if not req:
            return
        parts = req.split()
        if len(parts) >= 2 and parts[0] == "GET":
            path = parts[1]
            if path == "/health":
                body = json.dumps({"status": "ok", "ts": time.time()})
            elif path == "/stats":
                stats = await rt.store.stats()
                out = {
                    "proxies_total": stats["proxies_total"],
                    "targets": stats["targets"],
                    "in_flight": stats["in_flight"],
                    "due": stats["due"],
                    "queue": rt.queue.qsize(),
                    "workers_alive": rt.workers_alive,
                    "browsers": len(rt.pool.recs),
                    "circuits": rt.circuit.state_dict(),
                    "uptime_seconds": int(time.time() - rt.dashboard.started),
                    "version": VERSION
                }
                body = json.dumps(out)
            else:
                body = '{"error": "not found"}'
            
            res = f"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {len(body)}\r\nConnection: close\r\n\r\n{body}"
            writer.write(res.encode())
            await writer.drain()
    except Exception:
        pass
    finally:
        with contextlib.suppress(Exception):
            writer.close()
            await writer.wait_closed()


# ══════════════════════════════════════════════════════════════════════════════
#  GIT INTEGRATION - "git pull -> restart" workflow, never a force-push of your data
# ══════════════════════════════════════════════════════════════════════════════
def _git(args: list, cwd: Path = ROOT, check: bool = False) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=str(cwd), capture_output=True, text=True, check=check)


def git_is_repo() -> bool:
    return (ROOT / ".git").exists()


def git_pull_and_check() -> dict:
    """Fetches + fast-forwards only (never overwrites local edits). Returns what changed."""
    if not git_is_repo():
        return {"ok": False, "error": "not a git repository"}
    status = _git(["status", "--porcelain"])
    if status.stdout.strip():
        return {"ok": False, "error": "local changes present; refusing to pull (commit/stash first)"}
    fetch = _git(["fetch", CFG.git_remote, CFG.git_branch])
    if fetch.returncode != 0:
        return {"ok": False, "error": f"fetch failed: {fetch.stderr.strip()[:300]}"}
    before = _git(["rev-parse", "HEAD"]).stdout.strip()
    merge = _git(["merge", "--ff-only", f"{CFG.git_remote}/{CFG.git_branch}"])
    if merge.returncode != 0:
        return {"ok": False, "error": f"fast-forward failed (diverged?): {merge.stderr.strip()[:300]}"}
    after = _git(["rev-parse", "HEAD"]).stdout.strip()
    if before == after:
        return {"ok": True, "changed": False}
    diff = _git(["diff", "--name-only", before, after]).stdout.split()
    code_changed = any(f in ("main.py", "requirements.txt") for f in diff)
    return {"ok": True, "changed": True, "before": before[:8], "after": after[:8],
            "files": diff, "code_changed": code_changed}


def requirements_hash() -> Optional[str]:
    req = ROOT / "requirements.txt"
    if not req.exists():
        return None
    return hashlib.sha1(req.read_bytes()).hexdigest()


def pip_install_if_changed() -> bool:
    h = requirements_hash()
    if h is None:
        return False
    prev = DEPS_STAMP.read_text().strip() if DEPS_STAMP.exists() else None
    if h == prev:
        return False
    glog.info("requirements.txt changed - installing dependencies")
    r = subprocess.run([sys.executable, "-m", "pip", "install", "--break-system-packages", "-q",
                        "-r", str(ROOT / "requirements.txt")], capture_output=True, text=True)
    if r.returncode != 0:
        elog.error("pip install failed: %s", r.stderr[:500])
        return False
    _atomic_write(DEPS_STAMP, h)
    return True


async def git_watch_loop(rt: Runtime) -> None:
    if not (CFG.git_enabled and git_is_repo()):
        return
    _last_push = time.time()
    while not rt.stop_event.is_set():
        await _sleep_or_stop(rt.stop_event, CFG.git_check_interval_seconds)
        if rt.stop_event.is_set():
            return
        try:
            res = git_pull_and_check()
            if not res.get("ok"):
                glog.warning("git check skipped: %s", res.get("error"))
                continue
            if res.get("changed"):
                glog.info("git updated %s -> %s (%s)", res["before"], res["after"], ", ".join(res["files"]))
                if res["code_changed"]:
                    pip_install_if_changed()
                    if CFG.git_auto_restart:
                        glog.info("code changed - requesting graceful restart")
                        rt.notifier.notify("\U0001f504 Code updated from GitHub - restarting to apply changes.",
                                           dedupe_key="restart", min_gap=30)
                        rt.restart_requested = True
                        rt.stop_event.set()
                    else:
                        rt.notifier.notify("\u2139\ufe0f Code updated from GitHub - restart manually to apply.",
                                           dedupe_key="restart_manual", min_gap=30)
                else:
                    pip_install_if_changed()
            if CFG.git_push_state and time.time() - _last_push >= CFG.git_push_interval_seconds:
                await push_state_snapshot(rt.store)
                _last_push = time.time()
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            elog.exception("git watch error: %s", exc)


async def push_state_snapshot(store: Store) -> None:
    """Commits a JSON snapshot (never the raw SQLite file - see write_gitignore) to state/."""
    data = await store.export_state(mask=True)
    _atomic_write(STATE_DIR / "snapshot.json", json.dumps(data, indent=2))
    if not git_is_repo():
        return
    _git(["add", "state/snapshot.json"])
    diff = _git(["diff", "--cached", "--quiet"])
    if diff.returncode == 0:
        return          # nothing changed
    msg = f"state snapshot {time.strftime('%Y-%m-%d %H:%M:%S UTC', time.gmtime())}"
    commit = _git(["commit", "-m", msg])
    if commit.returncode != 0:
        glog.warning("state commit failed: %s", commit.stderr[:300])
        return
    push = _git(["push", CFG.git_remote, CFG.git_branch])
    if push.returncode != 0:
        glog.warning("state push failed: %s", push.stderr[:300])
    else:
        glog.info("state snapshot pushed")


# ══════════════════════════════════════════════════════════════════════════════
#  SINGLE-INSTANCE LOCK - prevents two daemons corrupting the same DB
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


# ══════════════════════════════════════════════════════════════════════════════
#  LAUNCH ARGS - tuned for a 16GB / 4-core box: real multi-process Chromium,
#  each with several contexts, headless, sandboxed off ONLY because most cloud
#  shells run as root without user namespaces (kept as an opt-out flag).
# ══════════════════════════════════════════════════════════════════════════════
def _launch_args() -> list[str]:
    args = [
        "--disable-features=Translate,BackForwardCache",
        "--disable-gpu",
        "--no-first-run",
        "--no-default-browser-check",
        "--disable-background-timer-throttling",
        "--disable-renderer-backgrounding",
        "--disable-backgrounding-occluded-windows",
        "--disable-breakpad",
        "--mute-audio",
        "--js-flags=--max-old-space-size=384",   # cap per-renderer heap; protects the 16GB box under load
    ]
    if CFG.chromium_no_sandbox:
        args += ["--no-sandbox", "--disable-dev-shm-usage"]
    return args


def keepalive_worker(stop_event: asyncio.Event):
    while not stop_event.is_set():
        time.sleep(CFG.keepalive_interval_seconds)
        if stop_event.is_set():
            break
        log.info("keepalive heartbeat")


# ══════════════════════════════════════════════════════════════════════════════
#  DAEMON
# ══════════════════════════════════════════════════════════════════════════════
async def run_daemon() -> int:
    restart = False
    log.info("=" * 78)
    log.info("RADIATE PROXY MONITOR v%s starting  pid=%d", VERSION, os.getpid())
    log.info("workers=%d browsers=%d contexts/browser=%d max_concurrent_contexts=%d",
             CFG.worker_count, CFG.browser_count, CFG.contexts_per_browser,
             CFG.browser_count * CFG.contexts_per_browser)
    if psutil:
        with contextlib.suppress(Exception):
            vm = psutil.virtual_memory()
            log.info("host memory: %.1fGB total, %.1fGB available", vm.total / 2**30, vm.available / 2**30)

    if not PLAYWRIGHT_OK:
        elog.error("playwright is not installed - run: pip install -r requirements.txt && playwright install chromium")
        print("ERROR: playwright is not installed. See logs/errors.log.", file=sys.stderr)
        return 1

    if CFG.session_cache_enabled:
        cleanup_sessions(max_age_days=7)

    registry = TargetRegistry()
    if not registry.reload():
        elog.error("no valid targets.json - aborting; check logs/errors.log")
        return 1
    if not registry.enabled():
        elog.warning("no ENABLED targets found in targets.json - daemon will idle. "
                     "Run: python3 main.py add-target <url>")

    store = Store.open_safely(DB_FILE)
    try:
        r = await store.sync_targets(list(registry.targets.values()))
        log.info("targets synced: %d rows backfilled, %d disabled (removed from file)",
                 r["rows_created"], r["disabled_missing"])

        proxies = load_all_proxy_files()
        if proxies:
            r = await store.ingest_proxies(proxies)
            log.info("proxy ingest: %d new, %d already known, %d new proxy_target rows",
                     r["inserted"], r["existing"], r["rows_created"])
        else:
            log.warning("no proxies found in configured files: %s", ", ".join(CFG.proxy_files))

        released = await store.reset_claims()   # crash-safe resume: nothing stays "in flight" forever
        if released:
            rlog.info("resume: released %d stale in-flight claim(s) from a previous run", released)
        resume = await store.resume_summary()
        log.info("resume state: %s (due now: %d, cooling: %d)",
                 resume["by_status"], resume["due_now"], resume["cooling"])

        circuit = TargetCircuit()
        netguard = NetGuard()
        dashboard = Dashboard()
        notifier = TelegramNotifier(getattr(CFG, "telegram_bot_token", ""), getattr(CFG, "telegram_chat_id", ""))
        await notifier.start()
        stop_event = asyncio.Event()

        if CFG.keepalive_enabled:
            threading.Thread(target=keepalive_worker, args=(stop_event,), daemon=True).start()

        async with async_playwright() as pw:
            async def launcher():
                return await pw.chromium.launch(headless=CFG.headless, args=_launch_args())

            pool = BrowserPool(launcher)
            await pool.start()
            if not pool.recs:
                elog.error("no Chromium browsers could be launched - aborting")
                return 1
                
            rt = Runtime(store, pool, registry, circuit, netguard, dashboard, notifier, stop_event)
            with contextlib.suppress(Exception):
                rt.browser_version = next(iter(pool.recs.values())).browser.version

            workers = [asyncio.create_task(worker_loop(i, rt), name=f"worker-{i}") for i in range(CFG.worker_count)]
            bg = [
                asyncio.create_task(scheduler_loop(rt), name="scheduler"),
                asyncio.create_task(dashboard_loop(rt), name="dashboard"),
                asyncio.create_task(output_loop(rt), name="output"),
                asyncio.create_task(maintenance_loop(rt), name="maintenance"),
                asyncio.create_task(pool_guard_loop(rt), name="pool_guard"),
                asyncio.create_task(metrics_loop(rt), name="metrics"),
                asyncio.create_task(ua_refresh_loop(rt), name="ua_refresh"),
                asyncio.create_task(fallback_loop(rt, getattr(CFG, "fallback_urls", []),
                                                  getattr(CFG, "fallback_min_working", 20),
                                                  getattr(CFG, "fallback_cooldown_seconds", 1800.0)),
                                    name="fallback"),
                asyncio.create_task(telegram_summary_loop(rt, getattr(CFG, "telegram_summary_interval_seconds", 3600.0)),
                                    name="telegram_summary"),
                asyncio.create_task(git_watch_loop(rt), name="git_watch"),
            ]
            
            if CFG.http_api_enabled:
                api_server = await asyncio.start_server(
                    lambda r, w: http_health_server(r, w, rt),
                    CFG.http_api_host, CFG.http_api_port
                )
                bg.append(asyncio.create_task(api_server.serve_forever(), name="http_api"))
                
            supervisor = asyncio.create_task(supervisor_loop(rt, workers), name="supervisor")

            loop = asyncio.get_running_loop()
            shutdown = asyncio.Event()

            def _on_sig(sig_name: str):
                log.info("signal %s received - graceful shutdown", sig_name)
                shutdown.set()

            for sig in (signal.SIGINT, signal.SIGTERM):
                with contextlib.suppress(NotImplementedError, AttributeError, ValueError):
                    loop.add_signal_handler(sig, lambda s=sig: _on_sig(signal.Signals(s).name))

            watchdog = asyncio.create_task(_watch_stop_event(rt, shutdown), name="watchdog")
            await shutdown.wait()

            log.info("shutting down: stop accepting new work, draining current tests "
                     f"(up to {CFG.shutdown_grace_seconds:.0f}s)")
            stop_event.set()
            watchdog.cancel()
            with contextlib.suppress(Exception):
                await asyncio.wait_for(asyncio.gather(*workers, return_exceptions=True),
                                       timeout=CFG.shutdown_grace_seconds)
            for t in bg + [supervisor]:
                t.cancel()
            await asyncio.gather(*bg, supervisor, *workers, return_exceptions=True)
            await notifier.stop()

            with contextlib.suppress(Exception):
                per_target, flat = await store.working_lists(CFG.output_mode, CFG.output_max_age_seconds)
                _atomic_write(OUTPUT_FILE, _format_output(per_target, flat))
                log.info("final output flushed: %d combined", len(flat))

            await pool.close()
            restart = rt.restart_requested

        dashboard.clear()
    finally:
        store.close()

    log.info("shutdown complete")
    return RESTART_EXIT_CODE if restart else 0


async def _watch_stop_event(rt: Runtime, shutdown: asyncio.Event) -> None:
    """Lets an internal component (e.g. git auto-restart) trigger the same clean shutdown path."""
    await rt.stop_event.wait()
    shutdown.set()


# ══════════════════════════════════════════════════════════════════════════════
#  CLI
# ══════════════════════════════════════════════════════════════════════════════
def cli_run() -> None:
    lock = InstanceLock(LOCK_FILE)
    if not lock.acquire():
        print(f"Another instance is already running (lock: {LOCK_FILE}). "
              f"Use `python3 main.py tmux attach` if it's in tmux.", file=sys.stderr)
        sys.exit(1)
    try:
        code = asyncio.run(run_daemon())
    except KeyboardInterrupt:
        code = 0
    except Exception as exc:
        elog.exception("fatal: %s", exc)
        print(f"Fatal error - see {LOG_DIR / 'errors.log'}", file=sys.stderr)
        code = 1
    finally:
        lock.release()
    sys.exit(code)


def _with_store(fn):
    async def _go(*a):
        store = Store.open_safely(DB_FILE)
        try:
            return await fn(store, *a)
        finally:
            store.close()
    return _go


def cli_status(as_json: bool) -> None:
    async def go():
        store = Store.open_safely(DB_FILE, readonly=True)
        try:
            stats = await store.stats()
        finally:
            store.close()
        if as_json:
            print(json.dumps(stats, indent=2))
            return
        g = stats["global"]
        print(f"Radiate Proxy Monitor v{VERSION}")
        print(f"Total proxies : {stats['proxies_total']:,}")
        print(f"  Working     : {g.get('WORKING', 0):,}")
        print(f"  Retryable   : {g.get('RETRYABLE', 0):,}")
        print(f"  Quarantined : {g.get('QUARANTINED', 0):,}")
        print(f"  Failed      : {g.get('FAILED', 0):,}")
        print(f"  Untested    : {g.get('UNTESTED', 0):,}")
        print(f"In-flight     : {stats['in_flight']:,}   Due now: {stats['due']:,}")
        for tid, st in stats["targets"].items():
            ok = st.get("WORKING", 0) + st.get("RECOVERED", 0)
            print(f"  [{tid}] ok={ok} retryable={st.get('RETRYABLE', 0)} "
                  f"quarantined={st.get('QUARANTINED', 0)} failed={st.get('FAILED', 0)} "
                  f"untested={st.get('UNTESTED', 0)}")
    asyncio.run(go())


def cli_add_proxies(fpath: str) -> None:
    async def go():
        p = Path(fpath)
        if not p.exists():
            print(f"File not found: {fpath}", file=sys.stderr)
            sys.exit(1)
        proxies, bad = load_proxy_file(p)
        store = Store.open_safely(DB_FILE)
        try:
            r = await store.ingest_proxies(proxies)
            print(f"Parsed {len(proxies)} unique proxies ({bad} unusable lines skipped). "
                  f"New={r['inserted']} Existing={r['existing']} NewRows={r['rows_created']}")
        finally:
            store.close()
    asyncio.run(go())


def cli_add_target(url: str) -> None:
    try:
        targets = load_targets()
    except ValueError as exc:
        print(f"targets.json is invalid, fix it first: {exc}", file=sys.stderr)
        sys.exit(1)
    tid = _slug(url)
    if any(t.target_id == tid or t.url == url for t in targets):
        print(f"Target already exists: {tid}")
        return
    targets.append(Target(target_id=tid, url=url))
    save_targets(targets)
    print(f"Added target {tid} -> {url}\n"
          f"The running daemon will pick this up automatically (polls targets.json every "
          f"{CFG.scheduler_tick_seconds:.0f}s). No restart needed.")


def cli_target_toggle(tid: str, enabled: bool) -> None:
    try:
        targets = load_targets()
    except ValueError as exc:
        print(f"targets.json is invalid: {exc}", file=sys.stderr)
        sys.exit(1)
    for t in targets:
        if t.target_id == tid:
            t.enabled = enabled
            save_targets(targets)
            print(f"{tid}: enabled={enabled}")
            return
    print(f"No such target: {tid}", file=sys.stderr)
    sys.exit(1)


def cli_remove_target(tid: str) -> None:
    try:
        targets = load_targets()
    except ValueError as exc:
        print(f"targets.json is invalid: {exc}", file=sys.stderr)
        sys.exit(1)
    kept = [t for t in targets if t.target_id != tid]
    if len(kept) == len(targets):
        print(f"No such target: {tid}", file=sys.stderr)
        sys.exit(1)
    save_targets(kept)
    print(f"Removed {tid} from targets.json. (Historical DB rows are kept; the target is just disabled.)")


def cli_list_targets() -> None:
    try:
        targets = load_targets()
    except ValueError as exc:
        print(f"targets.json is invalid: {exc}", file=sys.stderr)
        sys.exit(1)
    for t in targets:
        print(f"{'ON ' if t.enabled else 'off'}  {t.target_id:<30} {t.url}")


def cli_export(path: str, mask: bool) -> None:
    async def go():
        store = Store.open_safely(DB_FILE, readonly=True)
        try:
            data = await store.export_state(mask=mask)
        finally:
            store.close()
        _atomic_write(Path(path), json.dumps(data, indent=2))
        print(f"Exported state to {path}" + (" (proxy credentials masked)" if mask else ""))
    asyncio.run(go())


def cli_backup() -> None:
    async def go():
        for attempt in range(3):
            try:
                store = Store.open_safely(DB_FILE)
                try:
                    path = await store.backup(BACKUP_DIR, CFG.backup_keep)
                    print(f"Backup written: {path}")
                    return
                finally:
                    store.close()
            except sqlite3.OperationalError as e:
                if "locked" in str(e).lower() and attempt < 2:
                    time.sleep(1)
                else:
                    raise
    asyncio.run(go())


def cli_restore(fpath: str) -> None:
    src = Path(fpath)
    if not src.exists():
        print(f"File not found: {fpath}", file=sys.stderr)
        sys.exit(1)
    
    lock = InstanceLock(LOCK_FILE)
    if not lock.acquire():
        print("Stop the daemon before restoring (a lock file is present).", file=sys.stderr)
        sys.exit(1)
        
    try:
        for suffix in ("-wal", "-shm"):
            with contextlib.suppress(OSError):
                Path(str(DB_FILE) + suffix).unlink()
        shutil.copy2(src, DB_FILE)
        print(f"Restored {DB_FILE} from {fpath}. Verifying integrity...")
        store = Store.open_safely(DB_FILE)
        print("OK" if store._conn.execute("PRAGMA quick_check").fetchone()[0] == "ok" else "WARNING: integrity check failed")
        store.close()
    finally:
        lock.release()


def cli_init() -> None:
    write_gitignore()
    load_config()
    load_targets()
    (ROOT / "proxy_worked.txt").touch(exist_ok=True)
    req = ROOT / "requirements.txt"
    if not req.exists():
        req.write_text(REQUIREMENTS_TXT, encoding="utf-8")
    print(f"Initialised project in {ROOT}\n"
          f"  - config.json      (edit worker_count, browser_count, telegram_*, fallback_urls, git_* here)\n"
          f"  - targets.json     (edit your target URL(s), then set enabled=true)\n"
          f"  - proxy_worked.txt (put your ~1300-1400 known-working proxies here, one per line)\n"
          f"  - requirements.txt\n"
          f"  - .gitignore\n"
          f"Next: pip install -r requirements.txt && playwright install --with-deps chromium\n"
          f"Then: python3 main.py add-target https://yourdomain.example/ (or edit targets.json)\n"
          f"Then: python3 main.py tmux start")


GITIGNORE = """\
# Runtime state - never commit these
data/
logs/
output/
*.db
*.db-wal
*.db-shm
*.tmp
.env

# What IS safe and useful to keep in GitHub:
#   main.py, requirements.txt, config.json, targets.json, proxy_worked.txt, state/snapshot.json
# state/snapshot.json is a periodic JSON export (see `git_push_state` in config.json) -
# it is NOT the SQLite file, so concurrent daemons can never corrupt it by both writing at once.
"""

REQUIREMENTS_TXT = """\
playwright>=1.45
aiohttp>=3.9
psutil>=5.9
"""


def write_gitignore() -> None:
    gi = ROOT / ".gitignore"
    if not gi.exists():
        gi.write_text(GITIGNORE, encoding="utf-8")
    else:
        current = gi.read_text(encoding="utf-8")
        missing = [line for line in GITIGNORE.splitlines() if line and line not in current]
        if missing:
            gi.write_text(current + "\n" + "\n".join(missing) + "\n", encoding="utf-8")


def cli_update() -> None:
    res = git_pull_and_check()
    if not res.get("ok"):
        print(f"Update failed: {res.get('error')}", file=sys.stderr)
        sys.exit(1)
    if not res.get("changed"):
        print("Already up to date.")
        return
    print(f"Updated {res['before']} -> {res['after']}: {', '.join(res['files'])}")
    if res["code_changed"]:
        if pip_install_if_changed():
            print("Dependencies updated.")
        print("main.py or requirements.txt changed - restart the daemon:\n"
              "  python3 main.py tmux restart")
    else:
        print("Only data/config files changed - a running daemon will pick most of these up "
              "automatically (targets.json, config.json need `tmux restart` for config.json).")


def cli_push_state() -> None:
    async def go():
        store = Store.open_safely(DB_FILE, readonly=True)
        try:
            await push_state_snapshot(store)
        finally:
            store.close()
    asyncio.run(go())
    print("State snapshot pushed (if git_push_state / git remote configured).")


# ══════════════════════════════════════════════════════════════════════════════
#  TMUX WRAPPER - runs the daemon in a restart loop so a git-triggered graceful
#  restart (exit code 75) transparently relaunches inside the SAME tmux session.
# ══════════════════════════════════════════════════════════════════════════════
def _tmux(args: list, check: bool = False) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(["tmux", *args], capture_output=True, text=True, check=check)
    except FileNotFoundError:
        print("tmux is not installed (apt-get install tmux).", file=sys.stderr)
        sys.exit(1)


def cli_tmux(action: str) -> None:
    inner = (f"cd {shlex.quote(str(ROOT))} && "
             f"while true; do {shlex.quote(sys.executable)} main.py _runloop; "
             f"code=$?; [ $code -eq {RESTART_EXIT_CODE} ] || break; done")
    if action == "start":
        exists = TMUX_SESSION in _tmux(["ls"]).stdout
        if exists:
            print(f"tmux session '{TMUX_SESSION}' already running. Use `tmux attach` or `tmux restart`.")
            return
        _tmux(["new-session", "-d", "-s", TMUX_SESSION, inner])
        print(f"tmux session '{TMUX_SESSION}' started.\n"
              f"  Attach : tmux attach -t {TMUX_SESSION}   (or: python3 main.py tmux attach)\n"
              f"  Detach : Ctrl-b then d   (the daemon keeps running after you disconnect)\n"
              f"  Status : python3 main.py tmux status")
    elif action == "attach":
        subprocess.call(["tmux", "attach", "-t", TMUX_SESSION])
    elif action == "detach":
        _tmux(["detach-client", "-s", TMUX_SESSION])
    elif action == "stop":
        _tmux(["kill-session", "-t", TMUX_SESSION])
        print("Stopped.")
    elif action == "restart":
        _tmux(["kill-session", "-t", TMUX_SESSION])
        time.sleep(1)
        cli_tmux("start")
    elif action == "status":
        r = _tmux(["ls"])
        print(r.stdout or "(no tmux sessions)")
    else:
        print("usage: tmux {start|attach|detach|stop|restart|status}")


# ══════════════════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ══════════════════════════════════════════════════════════════════════════════
def main() -> None:
    parser = argparse.ArgumentParser(prog="main.py", description=f"RADIATE PROXY MONITOR v{VERSION}")
    sub = parser.add_subparsers(dest="cmd")

    sub.add_parser("init", help="create config.json / targets.json / requirements.txt / .gitignore")
    sub.add_parser("run", help="run the daemon in the foreground (Ctrl-C to stop)")
    sub.add_parser("_runloop", help=argparse.SUPPRESS)   # used by `tmux start`'s restart loop

    p_status = sub.add_parser("status", help="print DB stats")
    p_status.add_argument("--json", action="store_true")

    p_add = sub.add_parser("add-proxies", help="normalise + merge proxies from a file into the DB")
    p_add.add_argument("file")

    p_t = sub.add_parser("add-target", help="register a new target URL (hot-reloaded by a running daemon)")
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
    p_r = sub.add_parser("restore", help="restore the DB from a backup file (stop the daemon first)")
    p_r.add_argument("file")

    sub.add_parser("update", help="git fetch + fast-forward, install deps if requirements.txt changed")
    sub.add_parser("push-state", help="commit+push a JSON state snapshot to GitHub")

    p_tm = sub.add_parser("tmux", help="tmux session control")
    p_tm.add_argument("action", choices=["start", "attach", "detach", "stop", "restart", "status"])

    args = parser.parse_args()

    if args.cmd in ("run", "_runloop"):
        cli_run()
    elif args.cmd == "init":
        cli_init()
    elif args.cmd == "status":
        cli_status(args.json)
    elif args.cmd == "add-proxies":
        cli_add_proxies(args.file)
    elif args.cmd == "add-target":
        cli_add_target(args.url)
    elif args.cmd == "list-targets":
        cli_list_targets()
    elif args.cmd == "enable-target":
        cli_target_toggle(args.target_id, True)
    elif args.cmd == "disable-target":
        cli_target_toggle(args.target_id, False)
    elif args.cmd == "remove-target":
        cli_remove_target(args.target_id)
    elif args.cmd == "export":
        cli_export(args.file, args.mask)
    elif args.cmd == "backup":
        cli_backup()
    elif args.cmd == "restore":
        cli_restore(args.file)
    elif args.cmd == "update":
        cli_update()
    elif args.cmd == "push-state":
        cli_push_state()
    elif args.cmd == "tmux":
        cli_tmux(args.action)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
