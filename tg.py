import logging
import sys
from telegram import Update
from telegram.ext import Application, CommandHandler, MessageHandler, ContextTypes, filters
import os
import subprocess
import asyncio
import re
import time
import threading
import signal
import http.server
import socketserver
import json
import concurrent.futures
import cgi
from typing import Union, Optional, Any, Dict
import requests
import jwt # New import for JWT
import datetime # New import for JWT expiry
import socket # Added: Import the socket module for socket.timeout
import base64  # For encoding preview images
import uuid  # For generating unique session IDs
import shutil  # For moving cached preview files
import mimetypes
import atexit
from urllib.parse import urlparse, parse_qs
from env_config import get_env

# Import the gh.py script
from gh import update_github_pages_with_video, delete_video_from_drive_and_github, get_commit_details
from production_benchmark import run_production_benchmark, BENCHMARKING_ENABLED, _save_json_and_csv
from recon_integration import update_recon_index_scores

# Import admin_auth.py for authentication and session management
from admin_auth import authenticate_admin, get_session_expiry_time, update_admin_credential_in_file, verify_password, ADMIN_CREDENTIALS, SESSION_TIMEOUT_ENABLED, SESSION_DURATION_DAYS

# --- Configuration ---
TELEGRAM_BOT_TOKEN = get_env("TELEGRAM_BOT_TOKEN")
USE_GITHUB_PAGES = True  # Switch to enable/disable GitHub Pages integration (set to True to use gh.py)
OUTPUT_SUBDIRECTORY = "output"
INPUT_SUBDIRECTORY = "input"
WEB_SERVER_PORT = 5000 # Port for the local web server
TRACKING_SUBDIRECTORY = "tracking"
LEGACY_TRACKING_DATA_FILE = 'tracking_data.json'
TRACKING_DATA_FILE = os.path.join(TRACKING_SUBDIRECTORY, 'tracking_data.json')
UPTIME_DATA_FILE = os.path.join(TRACKING_SUBDIRECTORY, 'uptime_data.json')
UPTIME_MAX_EVENTS = 200000
UPTIME_HEARTBEAT_INTERVAL_SECONDS = 5
UPTIME_OFFLINE_INFER_MULTIPLIER = 2.5
UPTIME_EVENT_DEDUPE_TOLERANCE_SECONDS = 2.0
UPTIME_SHUTDOWN_BROADCAST_GRACE_SECONDS = 0.75

# Frame Restriction Configuration
FRAME_RESTRICTION_ENABLED = True # Set to True to enable frame count restriction
FRAME_RESTRICTION_VALUE = 20000 # Max allowed frames for video processing
FFPROBE_TIMEOUT_SECONDS = 10 # Timeout for ffprobe command in seconds

# JWT Secret Key (VERY IMPORTANT: Replace with a strong, random key in production!)
JWT_SECRET_KEY = get_env("JWT_SECRET_KEY", "")

# Master Admin Usernames (only these users can trigger global logout and other master actions)
# These users must also exist in ADMIN_CREDENTIALS in admin_auth.py
# FIX: Changed this to a set of individual strings for each master admin.
MASTER_ADMIN_USERNAMES = {"SHITIJ.dev", "sayann70"} # Add more usernames to this set if you have multiple master admins, e.g., {"ExampleAdmin1", "another_master_admin"}

# --- AdSense Configuration (New) ---
# Global flag to enable/disable ads for all users (including non-admins)
_ADS_ENABLED_GLOBALLY = False # Default to False, can be changed by master admin

# Flag to determine if ads should be shown to admins when _ADS_ENABLED_GLOBALLY is True
_SHOW_ADS_TO_ADMINS = False # Default to False, can be changed by master admin

# File to persist ad settings
AD_SETTINGS_FILE = 'ad_settings.json'

# --- ROI Preview Configuration ---
# Directory to store temporary preview files
PREVIEW_SUBDIRECTORY = "preview_temp"
# Directory for chunked upload session files
CHUNK_UPLOAD_SUBDIRECTORY = "chunk_uploads"
# Time in seconds before an abandoned preview is cleaned up (5 minutes)
PREVIEW_CLEANUP_TIMEOUT_SECONDS = 300
# Interval for preview cleanup check (60 seconds)
PREVIEW_CLEANUP_INTERVAL_SECONDS = 60

# Ensure input and output directories exist
os.makedirs(OUTPUT_SUBDIRECTORY, exist_ok=True)
os.makedirs(INPUT_SUBDIRECTORY, exist_ok=True)
os.makedirs(PREVIEW_SUBDIRECTORY, exist_ok=True)
os.makedirs(CHUNK_UPLOAD_SUBDIRECTORY, exist_ok=True)
os.makedirs(TRACKING_SUBDIRECTORY, exist_ok=True)

# --- Logging ---
logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s", level=logging.INFO)
logger = logging.getLogger(__name__)

logging.getLogger("httpx").setLevel(logging.INFO)
logging.getLogger("telegram.ext.Application").setLevel(logging.INFO)
logging.getLogger("telegram").setLevel(logging.INFO)

# --- Global variable for web server status and tracking data ---
_current_processing_status: Union[str, None] = None # Start with None, so frontend hides initially
_status_lock = threading.Lock() # To protect _current_processing_status from race conditions
_tracking_data: list = [] # List to hold processed video tracking data
_tracking_data_lock = threading.Lock() # To protect _tracking_data from race conditions
_uptime_data: dict = {}
_uptime_data_lock = threading.Lock()
_uptime_monitor_stop_event = threading.Event()
_uptime_monitor_thread: Optional[threading.Thread] = None
_admin_tracker_landing_sessions: Dict[str, float] = {}
_admin_tracker_landing_sessions_lock = threading.Lock()

# List to keep track of invalidated JWTs (for immediate logout)
# In a real-world app, this would be a persistent store like a database or Redis.
_invalidated_tokens = set()
_token_invalidation_lock = threading.Lock()


def _record_admin_tracker_landing_once(session_id: str, admin_username: str, source_ip: str) -> bool:
    """Returns True only the first time a landing session ID is seen."""
    clean_session = (session_id or '').strip()
    if not clean_session:
        return False

    now = time.time()
    cutoff = now - 86400
    with _admin_tracker_landing_sessions_lock:
        stale_keys = [k for k, ts in _admin_tracker_landing_sessions.items() if ts < cutoff]
        for stale_key in stale_keys:
            _admin_tracker_landing_sessions.pop(stale_key, None)

        if clean_session in _admin_tracker_landing_sessions:
            return False

        _admin_tracker_landing_sessions[clean_session] = now

    logger.info(f"Admin landed on tracker page: {admin_username} ({source_ip})")
    return True

# --- Preview Session Management ---
# Stores preview sessions: {session_id: {'video_path': str, 'created_at': float, 'used': bool}}
_preview_sessions = {}
_preview_sessions_lock = threading.Lock()

_benchmark_lock = threading.Lock()
_benchmark_in_progress = False
_benchmarking_enabled_runtime = BENCHMARKING_ENABLED
_benchmarking_enabled_lock = threading.Lock()
_active_benchmark_task = None
_benchmark_progress: Dict[str, Any] = {
    "runId": "",
    "progressPct": 0,
    "stage": "idle",
    "detail": "",
    "etaSeconds": None,
    "updatedAt": 0,
}

_processing_job_lock = threading.Lock()
_active_processing_job: Dict[str, Any] = {
    "jobId": "",
    "future": None,
    "startedAt": 0,
    "cancelRequested": False,
    "ownerClientId": "",
    "ownerUsername": "",
    "ownerIsAdmin": False,
}

_active_async_processes_lock = threading.Lock()
_active_async_processes: Dict[int, Dict[str, Any]] = {}


def is_benchmarking_enabled() -> bool:
    """Returns current runtime benchmark enable state."""
    with _benchmarking_enabled_lock:
        return bool(_benchmarking_enabled_runtime)


def set_benchmarking_enabled(enabled: bool) -> bool:
    """Sets runtime benchmark enable state and returns updated value."""
    global _benchmarking_enabled_runtime
    with _benchmarking_enabled_lock:
        _benchmarking_enabled_runtime = bool(enabled)
        return _benchmarking_enabled_runtime


def _new_processing_job_id() -> str:
    return str(uuid.uuid4())


def _new_benchmark_run_id() -> str:
    return f"bench-{int(time.time() * 1000)}"


def _set_benchmark_progress(
    *,
    progress_pct: Optional[int] = None,
    stage: Optional[str] = None,
    detail: Optional[str] = None,
    eta_seconds: Optional[int] = None,
    run_id: Optional[str] = None,
) -> None:
    with _benchmark_lock:
        if run_id is not None:
            _benchmark_progress["runId"] = run_id
        if progress_pct is not None:
            _benchmark_progress["progressPct"] = max(0, min(100, int(progress_pct)))
        if stage is not None:
            _benchmark_progress["stage"] = stage
        if detail is not None:
            _benchmark_progress["detail"] = detail
        _benchmark_progress["etaSeconds"] = eta_seconds
        _benchmark_progress["updatedAt"] = int(time.time())


def _reset_benchmark_progress() -> None:
    with _benchmark_lock:
        _benchmark_progress.update({
            "runId": "",
            "progressPct": 0,
            "stage": "idle",
            "detail": "",
            "etaSeconds": None,
            "updatedAt": int(time.time()),
        })


def _set_active_benchmark_task(task) -> None:
    global _active_benchmark_task
    with _benchmark_lock:
        _active_benchmark_task = task


def _clear_active_benchmark_task(task=None) -> None:
    global _active_benchmark_task
    with _benchmark_lock:
        if task is None or _active_benchmark_task is task:
            _active_benchmark_task = None


def _cancel_active_benchmark_task(main_loop: asyncio.AbstractEventLoop) -> bool:
    with _benchmark_lock:
        task = _active_benchmark_task
        if not task or task.done():
            return False

    def _cancel():
        try:
            if task and not task.done():
                task.cancel()
        except Exception as cancel_error:
            logger.warning(f"Failed to cancel active benchmark task: {cancel_error}")

    main_loop.call_soon_threadsafe(_cancel)
    return True


def _snapshot_active_processing_job() -> Dict[str, Any]:
    with _processing_job_lock:
        job_id = _active_processing_job.get("jobId") or ""
        future = _active_processing_job.get("future")
        started_at = int(_active_processing_job.get("startedAt") or 0)
        cancel_requested = bool(_active_processing_job.get("cancelRequested"))
        owner_client_id = (_active_processing_job.get("ownerClientId") or "").strip()
        owner_username = (_active_processing_job.get("ownerUsername") or "").strip()
        owner_is_admin = bool(_active_processing_job.get("ownerIsAdmin"))
        is_active = bool(job_id and future and not future.done())
        return {
            "jobId": job_id if is_active else "",
            "isActive": is_active,
            "startedAt": started_at if is_active else 0,
            "cancelRequested": cancel_requested if is_active else False,
            "ownerClientId": owner_client_id if is_active else "",
            "ownerUsername": owner_username if is_active else "",
            "ownerIsAdmin": owner_is_admin if is_active else False,
        }


def _clear_active_processing_job_if_matches(job_id: str) -> None:
    with _processing_job_lock:
        if (_active_processing_job.get("jobId") or "") != job_id:
            return
        _active_processing_job.update({
            "jobId": "",
            "future": None,
            "startedAt": 0,
            "cancelRequested": False,
            "ownerClientId": "",
            "ownerUsername": "",
            "ownerIsAdmin": False,
        })


def _register_processing_future(
    job_id: str,
    future: concurrent.futures.Future,
    owner_client_id: str = "",
    owner_username: str = "",
    owner_is_admin: bool = False,
) -> None:
    with _processing_job_lock:
        _active_processing_job.update({
            "jobId": job_id,
            "future": future,
            "startedAt": int(time.time()),
            "cancelRequested": False,
            "ownerClientId": (owner_client_id or "").strip(),
            "ownerUsername": (owner_username or "").strip(),
            "ownerIsAdmin": bool(owner_is_admin),
        })

    def _on_done(done_future: concurrent.futures.Future):
        cancelled = done_future.cancelled()
        _clear_active_processing_job_if_matches(job_id)
        if cancelled:
            set_processing_status("⛔ Processing cancelled. Server is ready for the next video.")
            reset_status_after_delay(4)

    future.add_done_callback(_on_done)


def _cancel_processing_job(job_id: Optional[str]) -> Dict[str, Any]:
    active_future = None
    active_job_id = ""
    with _processing_job_lock:
        active_job_id = _active_processing_job.get("jobId") or ""
        active_future = _active_processing_job.get("future")

        if not active_job_id or not active_future or active_future.done():
            return {"ok": False, "reason": "no_active_job", "jobId": ""}

        if job_id and job_id != active_job_id:
            return {"ok": False, "reason": "job_id_mismatch", "jobId": active_job_id}

        _active_processing_job["cancelRequested"] = True

    # Important: call cancel outside the lock to avoid deadlock from done-callback lock reentry.
    cancelled = active_future.cancel()

    if not cancelled:
        set_processing_status("⛔ Cancellation requested. Stopping current processing...")
    return {
        "ok": True,
        "reason": "cancel_requested",
        "jobId": active_job_id,
        "cancelSignalAccepted": bool(cancelled),
    }


def _sanitize_client_id(raw_client_id: str) -> str:
    candidate = (raw_client_id or "").strip()
    if not candidate:
        return ""
    candidate = re.sub(r'[^A-Za-z0-9._-]', '', candidate)
    return candidate[:96]


def _can_requester_cancel_active_job(active_job_snapshot: Dict[str, Any], requester: Dict[str, Any]) -> bool:
    if not active_job_snapshot.get("isActive"):
        return False
    if requester.get("isAdmin"):
        return True
    owner_client_id = (active_job_snapshot.get("ownerClientId") or "").strip()
    requester_client_id = (requester.get("clientId") or "").strip()
    return bool(owner_client_id and requester_client_id and owner_client_id == requester_client_id)


def run_async_loop(loop: asyncio.AbstractEventLoop):
    """Runs an asyncio event loop forever in a dedicated daemon thread."""
    asyncio.set_event_loop(loop)
    loop.run_forever()


def _log_scheduled_future_error(future, operation_name: str):
    """Logs unhandled exceptions from run_coroutine_threadsafe futures."""
    try:
        if future.cancelled():
            logger.debug(f"Scheduled async operation '{operation_name}' was cancelled.")
            return
        exc = future.exception()
        if exc:
            logger.error(f"Scheduled async operation '{operation_name}' failed: {exc}", exc_info=True)
    except Exception as callback_error:
        logger.error(f"Error while checking future for '{operation_name}': {callback_error}", exc_info=True)


def _schedule_processing_job(
    main_loop: asyncio.AbstractEventLoop,
    coroutine,
    operation_name: str,
    owner_client_id: str = "",
    owner_username: str = "",
    owner_is_admin: bool = False,
) -> tuple[Optional[str], Optional[concurrent.futures.Future], Optional[str]]:
    """
    Schedules a processing coroutine if no active processing job is running.
    Returns (job_id, future, error_message).
    """
    with _processing_job_lock:
        active_future = _active_processing_job.get("future")
        active_job_id = _active_processing_job.get("jobId") or ""
        if active_future and not active_future.done() and active_job_id:
            try:
                coroutine.close()
            except Exception:
                pass
            return None, None, f"Another processing job is already running ({active_job_id})."

    job_id = _new_processing_job_id()
    future = asyncio.run_coroutine_threadsafe(coroutine, main_loop)
    _register_processing_future(
        job_id,
        future,
        owner_client_id=owner_client_id,
        owner_username=owner_username,
        owner_is_admin=owner_is_admin,
    )
    future.add_done_callback(lambda f: _log_scheduled_future_error(f, operation_name))
    return job_id, future, None


def _register_async_process(process: asyncio.subprocess.Process, label: str) -> None:
    if not process:
        return
    with _active_async_processes_lock:
        _active_async_processes[id(process)] = {
            "process": process,
            "label": label,
            "pid": process.pid,
            "registeredAt": int(time.time()),
        }


def _unregister_async_process(process: asyncio.subprocess.Process) -> None:
    if not process:
        return
    with _active_async_processes_lock:
        _active_async_processes.pop(id(process), None)


def _snapshot_async_processes() -> list:
    with _active_async_processes_lock:
        return list(_active_async_processes.values())


def _start_new_session_kwargs() -> Dict[str, Any]:
    # Put spawned subprocesses in independent process groups for reliable cancel semantics.
    return {"start_new_session": True} if os.name == "posix" else {}


def _is_pid_alive(pid: int) -> bool:
    if not pid or pid <= 0:
        return False
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except Exception:
        return False


def _terminate_pid_tree_sync(pid: int, label: str) -> bool:
    if not pid or pid <= 0:
        return False

    try:
        if os.name == "posix":
            try:
                pgid = os.getpgid(pid)
                logger.debug(f"SIGTERM process group for '{label}' (pid={pid}, pgid={pgid})")
                os.killpg(pgid, signal.SIGTERM)
            except ProcessLookupError:
                return False
        else:
            logger.debug(f"SIGTERM process for '{label}' (pid={pid})")
            os.kill(pid, signal.SIGTERM)
    except ProcessLookupError:
        return False
    except Exception as term_error:
        logger.warning(f"Failed to SIGTERM '{label}' (pid={pid}): {term_error}")
        return False

    for _ in range(10):
        if not _is_pid_alive(pid):
            return True
        time.sleep(0.1)

    try:
        if os.name == "posix":
            try:
                pgid = os.getpgid(pid)
                logger.debug(f"SIGKILL process group for '{label}' (pid={pid}, pgid={pgid})")
                os.killpg(pgid, signal.SIGKILL)
            except ProcessLookupError:
                return True
        else:
            logger.debug(f"SIGKILL process for '{label}' (pid={pid})")
            os.kill(pid, signal.SIGKILL)
    except ProcessLookupError:
        return True
    except Exception as kill_error:
        logger.warning(f"Failed to SIGKILL '{label}' (pid={pid}): {kill_error}")
        return False

    for _ in range(10):
        if not _is_pid_alive(pid):
            return True
        time.sleep(0.1)

    return not _is_pid_alive(pid)


def _terminate_registered_async_processes_sync() -> int:
    snapshot = _snapshot_async_processes()
    if not snapshot:
        return 0

    terminated = 0
    for item in snapshot:
        process = item.get("process")
        pid = int(item.get("pid") or 0)
        label = item.get("label") or "subprocess"
        stopped = _terminate_pid_tree_sync(pid, label)
        if stopped:
            terminated += 1
        if stopped and process:
            _unregister_async_process(process)
    return terminated


def _list_child_pids(pid: int) -> list[int]:
    if not pid or pid <= 0:
        return []
    try:
        output = subprocess.check_output(["ps", "-o", "pid=", "--ppid", str(pid)], text=True)
        return [int(line.strip()) for line in output.splitlines() if line.strip().isdigit()]
    except Exception:
        return []


def _collect_descendant_pids(root_pid: int) -> list[int]:
    stack = [root_pid]
    descendants: list[int] = []
    seen: set[int] = set()
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        children = _list_child_pids(current)
        for child in children:
            if child not in seen:
                descendants.append(child)
                stack.append(child)
    return descendants


def _force_kill_pid_family_sync(root_pid: int, label: str) -> int:
    if not root_pid or root_pid <= 0:
        return 0

    killed = 0
    descendants = _collect_descendant_pids(root_pid)
    # Kill descendants first, then root.
    for pid in descendants:
        try:
            os.kill(pid, signal.SIGKILL)
            killed += 1
            logger.debug(f"Force-killed descendant process for '{label}' (pid={pid}, root={root_pid})")
        except Exception:
            pass

    try:
        os.kill(root_pid, signal.SIGKILL)
        killed += 1
        logger.debug(f"Force-killed root process for '{label}' (pid={root_pid})")
    except Exception:
        pass

    return killed


def _force_kill_registered_process_families_sync() -> int:
    snapshot = _snapshot_async_processes()
    killed = 0
    for item in snapshot:
        process = item.get("process")
        pid = int(item.get("pid") or 0)
        label = item.get("label") or "subprocess"
        if pid > 0:
            killed += _force_kill_pid_family_sync(pid, label)
        if process:
            _unregister_async_process(process)
    return killed


def _emergency_kill_registered_processes_sync() -> int:
    """Immediate best-effort kill for tracked subprocesses.
    This is used in cancel handler before any potentially blocking cancellation flows.
    """
    snapshot = _snapshot_async_processes()
    if not snapshot:
        return 0

    killed = 0
    for item in snapshot:
        process = item.get("process")
        pid = int(item.get("pid") or 0)
        label = item.get("label") or "subprocess"

        # Fast path: kill through process handle when available.
        try:
            if process and process.returncode is None:
                process.kill()
                killed += 1
                logger.debug(f"Emergency process.kill() for '{label}' (pid={pid})")
        except Exception as kill_handle_error:
            logger.warning(f"Emergency process.kill() failed for '{label}' (pid={pid}): {kill_handle_error}")

        # Fallback path: kill process group/root pid directly.
        try:
            if pid > 0:
                if os.name == "posix":
                    try:
                        pgid = os.getpgid(pid)
                        os.killpg(pgid, signal.SIGKILL)
                        logger.debug(f"Emergency SIGKILL process group for '{label}' (pid={pid}, pgid={pgid})")
                    except Exception:
                        os.kill(pid, signal.SIGKILL)
                        logger.debug(f"Emergency SIGKILL process for '{label}' (pid={pid})")
                else:
                    os.kill(pid, signal.SIGKILL)
                    logger.debug(f"Emergency SIGKILL process for '{label}' (pid={pid})")
        except Exception as direct_kill_error:
            logger.warning(f"Emergency direct kill failed for '{label}' (pid={pid}): {direct_kill_error}")

        if not _is_pid_alive(pid):
            if process:
                _unregister_async_process(process)
    return killed


async def _terminate_all_registered_async_processes() -> int:
    snapshot = _snapshot_async_processes()
    if not snapshot:
        return 0

    terminated = 0
    for item in snapshot:
        process = item.get("process")
        label = item.get("label") or "subprocess"
        if process:
            await _terminate_async_process(process, label)
            terminated += 1
    return terminated

def generate_preview_session_id():
    """Generates a unique preview session ID."""
    import uuid
    return str(uuid.uuid4())

def create_preview_session(video_path: str, original_filename: str = None) -> str:
    """Creates a new preview session and returns the session ID."""
    session_id = generate_preview_session_id()
    # If no original filename provided, try to extract from path
    if original_filename is None:
        original_filename = os.path.basename(video_path)
    with _preview_sessions_lock:
        _preview_sessions[session_id] = {
            'video_path': video_path,
            'original_filename': original_filename,
            'created_at': time.time(),
            'used': False  # Set to True when processing starts
        }
    logger.info(f"Created preview session {session_id} for {video_path} (original: {original_filename})")
    return session_id

def get_preview_session(session_id: str) -> dict:
    """Gets a preview session by ID."""
    with _preview_sessions_lock:
        return _preview_sessions.get(session_id)

def mark_preview_session_used(session_id: str):
    """Marks a preview session as used (processing started)."""
    with _preview_sessions_lock:
        if session_id in _preview_sessions:
            _preview_sessions[session_id]['used'] = True
            logger.info(f"Preview session {session_id} marked as used")

def remove_preview_session(session_id: str):
    """Removes a preview session."""
    with _preview_sessions_lock:
        if session_id in _preview_sessions:
            del _preview_sessions[session_id]
            logger.info(f"Removed preview session {session_id}")

def cleanup_abandoned_previews():
    """Cleans up preview sessions that have been abandoned (not used within timeout)."""
    current_time = time.time()
    sessions_to_remove = []
    
    with _preview_sessions_lock:
        for session_id, session_data in list(_preview_sessions.items()):
            age = current_time - session_data['created_at']
            if age > PREVIEW_CLEANUP_TIMEOUT_SECONDS and not session_data['used']:
                sessions_to_remove.append((session_id, session_data['video_path']))
    
    # Clean up outside the lock to avoid holding it too long
    for session_id, video_path in sessions_to_remove:
        try:
            if os.path.exists(video_path):
                os.remove(video_path)
                logger.info(f"Cleaned up abandoned preview file: {video_path}")
        except Exception as e:
            logger.error(f"Error cleaning up preview file {video_path}: {e}")
        remove_preview_session(session_id)
    
    if sessions_to_remove:
        logger.info(f"Cleaned up {len(sessions_to_remove)} abandoned preview sessions")

def start_preview_cleanup_scheduler():
    """Starts a background thread to periodically clean up abandoned previews."""
    def cleanup_loop():
        while True:
            time.sleep(PREVIEW_CLEANUP_INTERVAL_SECONDS)
            cleanup_abandoned_previews()
    
    cleanup_thread = threading.Thread(target=cleanup_loop, daemon=True)
    cleanup_thread.start()
    logger.info("Preview cleanup scheduler started")

def extract_video_frame(video_path: str, output_image_path: str, seek_time: float = 1.0) -> bool:
    """
    Extracts a single frame from a video using FFmpeg.
    
    Args:
        video_path: Path to the video file
        output_image_path: Path to save the extracted frame (JPEG)
        seek_time: Time in seconds to seek to (default 1 second)
    
    Returns:
        bool: True if successful, False otherwise
    """
    try:
        # Get video duration first to determine a good seek time
        duration_cmd = [
            "ffprobe", "-v", "error",
            "-show_entries", "format=duration",
            "-of", "default=noprint_wrappers=1:nokey=1",
            video_path
        ]
        result = subprocess.run(duration_cmd, capture_output=True, text=True, timeout=15)
        
        if result.returncode == 0 and result.stdout.strip():
            try:
                duration = float(result.stdout.strip())
                # Seek to 10% of duration or 1 second, whichever is smaller
                seek_time = min(seek_time, duration * 0.1, duration - 0.1)
                seek_time = max(0, seek_time)  # Ensure non-negative
            except ValueError:
                seek_time = 0  # Fallback to first frame
        
        # Extract frame using FFmpeg
        extract_cmd = [
            "ffmpeg", "-y",
            "-ss", str(seek_time),
            "-i", video_path,
            "-vframes", "1",
            "-q:v", "2",  # High quality JPEG
            output_image_path
        ]
        
        result = subprocess.run(extract_cmd, capture_output=True, text=True, timeout=30)
        
        if result.returncode == 0 and os.path.exists(output_image_path):
            logger.info(f"Extracted frame from {video_path} at {seek_time:.2f}s")
            return True
        else:
            logger.error(f"FFmpeg frame extraction failed: {result.stderr}")
            return False
            
    except subprocess.TimeoutExpired:
        logger.error(f"Frame extraction timed out for {video_path}")
        return False
    except Exception as e:
        logger.error(f"Error extracting frame: {e}")
        return False

def resolve_uploaded_filename(upload_field, fallback_prefix: str = "uploaded_video") -> str:
    """Builds a filesystem-safe upload filename while preserving original names when available."""
    raw_name = (getattr(upload_field, "filename", "") or "").strip()
    filename = os.path.basename(raw_name).replace("\x00", "")

    # Some clients submit multipart files without filename metadata.
    if not filename:
        content_type = (getattr(upload_field, "type", "") or "").split(";", 1)[0].strip().lower()
        guessed_ext = mimetypes.guess_extension(content_type) if content_type else None
        if guessed_ext in (".jpe",):
            guessed_ext = ".jpg"
        if not guessed_ext:
            guessed_ext = ".mp4"
        filename = f"{fallback_prefix}_{int(time.time())}{guessed_ext}"

    return filename.replace("/", "_").replace("\\", "_")

def sanitize_chunk_upload_id(upload_id: str) -> str:
    """Allows only safe characters for chunk upload session IDs."""
    cleaned = re.sub(r'[^A-Za-z0-9_-]', '', (upload_id or '').strip())
    if 8 <= len(cleaned) <= 80:
        return cleaned
    return ""

def sanitize_filename_value(filename: str, fallback_prefix: str = "uploaded_video") -> str:
    """Sanitizes a raw filename string and preserves extension when possible."""
    safe_name = os.path.basename((filename or "").strip()).replace("\x00", "")
    safe_name = safe_name.replace("/", "_").replace("\\", "_")
    if not safe_name:
        safe_name = f"{fallback_prefix}_{int(time.time())}.mp4"
    return safe_name

def invalidate_token(token: str):
    """Adds a token to the invalidated list."""
    with _token_invalidation_lock:
        _invalidated_tokens.add(token)
        logger.info(f"Token invalidated: {token[:10]}...")

def clear_all_sessions():
    """Simulates logging out all admins by invalidating all current and future tokens
    until a new master key is generated or some other persistent store is used.
    For this example, we'll effectively invalidate all current tokens.
    In a true production app, this would involve more sophisticated session management (e.g., refreshing JWT secret or using a blacklist in a DB).
    For now, we'll just log and let session timeout handle cleanup.
    """
    logger.warning("MASTER ADMIN COMMAND: All admin sessions are being invalidated!")
    # In a real system, you might rotate the JWT_SECRET_KEY or use a shared blacklist in a DB.
    # For this simple implementation, we'll log, but rely on token expiry for long-term invalidation.
    # A more robust solution might involve:
    # 1. Storing active JWTs in a database.
    # 2. Deleting all JWTs from that database.
    # 3. Requiring re-login for all users.
    # For now, we'll just log this critical event.
    global JWT_SECRET_KEY
    # Rotate the key to invalidate all existing tokens that were signed with the old key
    JWT_SECRET_KEY = os.urandom(32).hex() 
    logger.info("JWT Secret Key rotated. All old tokens are now invalid.")
    # Also clear the in-memory invalidated tokens set, as they refer to old keys
    with _token_invalidation_lock:
        _invalidated_tokens.clear()


_status_update_counter = 0

def set_processing_status(message: Union[str, None]):
    """Sets the global processing status message."""
    global _current_processing_status, _status_update_counter
    with _status_lock:
        _current_processing_status = message
        _status_update_counter += 1
    
    if message:
        # For recurring high-frequency updates, draw in-place
        if (
            message.startswith("Processing:") or
            message.startswith("Downloading:") or
            message.startswith("Merging") or
            message.startswith("Uploading:") or
            message.startswith("📊 Benchmark")
        ):
            sys.stdout.write(f"\r\033[K\033[1;36mProgress:\033[0m {message}")
            sys.stdout.flush()
        else:
            # Clear any existing in-place progress line, then log cleanly
            sys.stdout.write("\r\033[K")
            sys.stdout.flush()
            logger.info(f"Global Status Update: {message}")

def _status_indicates_processing_complete(status_message: str) -> bool:
    """Returns True when status indicates a processing success path finished."""
    if not status_message:
        return False

    normalized = status_message.lower()
    completion_markers = (
        "object tracking and github pages update complete",
        "object tracking complete! output saved locally"
    )
    return any(marker in normalized for marker in completion_markers)


def _format_eta_seconds(eta_seconds: Optional[int]) -> str:
    """Formats ETA seconds into a compact human-readable string."""
    if eta_seconds is None:
        return ""
    try:
        total = max(0, int(eta_seconds))
    except Exception:
        return ""

    minutes, seconds = divmod(total, 60)
    hours, minutes = divmod(minutes, 60)
    if hours > 0:
        return f"{hours}h {minutes}m {seconds}s"
    if minutes > 0:
        return f"{minutes}m {seconds}s"
    return f"{seconds}s"

def get_status_payload(requester: Optional[Dict[str, Any]] = None) -> dict:
    """Builds a consistent status payload for REST and SSE consumers."""
    with _status_lock:
        status_message = _current_processing_status
        status_counter = _status_update_counter

    active_job = _snapshot_active_processing_job()
    requester_info = requester or {}
    with _benchmark_lock:
        benchmark_progress = dict(_benchmark_progress)
        benchmark_in_progress = bool(_benchmark_in_progress)

    is_processing_complete = _status_indicates_processing_complete(status_message if status_message is not None else "")

    benchmark_one_line = ""
    if benchmark_in_progress:
        benchmark_one_line = (
            f"Benchmark {benchmark_progress.get('progressPct', 0)}% | "
            f"Stage: {benchmark_progress.get('stage', 'running')}"
        )
        detail = (benchmark_progress.get("detail") or "").strip()
        if detail:
            benchmark_one_line += f" | {detail}"
        eta_text = _format_eta_seconds(benchmark_progress.get("etaSeconds"))
        if eta_text:
            benchmark_one_line += f" | ETA: {eta_text}"

    return {
        "status": status_message if status_message is not None else "",
        "statusCounter": status_counter,
        "processingComplete": is_processing_complete,
        "galleryRefreshSuggested": is_processing_complete,
        "processingActive": active_job.get("isActive", False),
        "activeProcessingJobId": active_job.get("jobId", ""),
        "cancelRequested": active_job.get("cancelRequested", False),
        "processingStartedAt": active_job.get("startedAt", 0),
        "canCancelActiveJob": _can_requester_cancel_active_job(active_job, requester_info),
        "frameRestrictionEnabled": FRAME_RESTRICTION_ENABLED,
        "frameRestrictionValue": FRAME_RESTRICTION_VALUE,
        "benchmarkingEnabled": is_benchmarking_enabled(),
        "benchmarkInProgress": benchmark_in_progress,
        "benchmarkProgress": benchmark_progress,
        "benchmarkStatusLine": benchmark_one_line,
    }

def reset_status_after_delay(delay_seconds: int = 5):
    """Schedules a task to reset the status to None after a delay, ONLY if no new status has been set."""
    logger.info(f"Scheduling status reset to 'None' (hide) in {delay_seconds} seconds.")
    
    with _status_lock:
        current_counter = _status_update_counter
    
    def delayed_reset():
        global _current_processing_status, _status_update_counter
        with _status_lock:
            # Only reset if the status hasn't been updated since we started the timer
            if _status_update_counter == current_counter:
                _current_processing_status = None
                _status_update_counter += 1
                logger.info("Global Status Reset to None.")
            else:
                logger.info("Global Status Reset cancelled: new status was set in the meantime.")

    timer = threading.Timer(delay_seconds, delayed_reset)
    timer.daemon = True  # Ensure timer runs even if main thread state changes
    timer.start()


def _default_uptime_data() -> dict:
    return {
        "version": 1,
        "currentStatus": "off",
        "lastHeartbeatTs": 0,
        "updatedAt": 0,
        "events": [],
        "sessions": [],
    }


def _sanitize_uptime_status(status: Any) -> str:
    s = str(status or '').strip().lower()
    return 'on' if s in ('on', 'connected', 'live') else 'off'


def _rebuild_uptime_sessions_from_events_locked(now_ts: Optional[int] = None) -> None:
    now_value = float(now_ts if now_ts is not None else time.time())
    events = _uptime_data.get("events", [])
    sessions = []
    active_session = None

    for event in events:
        if not isinstance(event, dict):
            continue
        status = _sanitize_uptime_status(event.get("status"))
        ts = float(event.get("ts", 0) or 0)
        reason = str(event.get("reason", "") or "")

        if status == "on":
            if active_session is None:
                active_session = {"startTs": ts, "endTs": None, "startReason": reason}
            else:
                # Back-to-back ON events can happen after reconnect/recovery; keep earliest open start.
                if ts < float(active_session.get("startTs", ts)):
                    active_session["startTs"] = ts
                if reason and not active_session.get("startReason"):
                    active_session["startReason"] = reason
        else:
            if active_session is not None:
                active_session["endTs"] = ts
                active_session["endReason"] = reason
                sessions.append(active_session)
                active_session = None

    if active_session is not None:
        sessions.append(active_session)

    _uptime_data["sessions"] = sessions
    _uptime_data["lastHeartbeatTs"] = float(_uptime_data.get("lastHeartbeatTs", now_value) or now_value)
    _uptime_data["updatedAt"] = float(_uptime_data.get("updatedAt", now_value) or now_value)


def _repair_uptime_data_locked(now_ts: Optional[int] = None) -> None:
    now_value = float(now_ts if now_ts is not None else time.time())

    raw_events = _uptime_data.get("events", [])
    cleaned_events = []
    if isinstance(raw_events, list):
        for item in raw_events:
            if not isinstance(item, dict):
                continue
            ts_raw = item.get("ts", 0)
            try:
                ts = float(ts_raw or 0)
            except Exception:
                continue
            if ts <= 0:
                continue
            cleaned_events.append({
                "ts": ts,
                "status": _sanitize_uptime_status(item.get("status")),
                "reason": str(item.get("reason", "") or "")
            })

    cleaned_events.sort(key=lambda e: e["ts"])

    # Keep all event transitions (no dedupe) so rapid restart tests remain visible and truthful.
    _uptime_data["events"] = cleaned_events
    _uptime_data["version"] = 1

    if cleaned_events:
        _uptime_data["currentStatus"] = cleaned_events[-1]["status"]
        _uptime_data["updatedAt"] = cleaned_events[-1]["ts"]
    else:
        _uptime_data["currentStatus"] = "off"
        _uptime_data["updatedAt"] = now_value

    _uptime_data["lastHeartbeatTs"] = float(_uptime_data.get("lastHeartbeatTs", now_value) or now_value)
    _rebuild_uptime_sessions_from_events_locked(now_ts=now_value)


def _safe_uptime_snapshot_locked() -> dict:
    return json.loads(json.dumps(_uptime_data, ensure_ascii=False))


def _save_uptime_data_locked() -> None:
    try:
        with open(UPTIME_DATA_FILE, 'w', encoding='utf-8') as f:
            json.dump(_uptime_data, f, indent=2, ensure_ascii=False)
    except Exception as e:
        logger.error(f"Error saving {UPTIME_DATA_FILE}: {e}")


def _close_open_sessions_locked(end_ts: int, end_reason: str) -> None:
    sessions = _uptime_data.get("sessions", [])
    for session in reversed(sessions):
        if session.get("endTs") is None:
            session["endTs"] = float(end_ts)
            session["endReason"] = end_reason
            break


def _event_exists_near_locked(status: str, event_ts: float, tolerance_seconds: float = UPTIME_EVENT_DEDUPE_TOLERANCE_SECONDS) -> bool:
    target_status = _sanitize_uptime_status(status)
    ts_value = float(event_ts or 0)
    if ts_value <= 0:
        return False

    events = _uptime_data.get("events", [])
    if not isinstance(events, list) or not events:
        return False

    for event in reversed(events):
        if not isinstance(event, dict):
            continue
        existing_status = _sanitize_uptime_status(event.get("status"))
        if existing_status != target_status:
            continue
        try:
            existing_ts = float(event.get("ts", 0) or 0)
        except Exception:
            continue
        if abs(existing_ts - ts_value) <= float(tolerance_seconds):
            return True
    return False


def _append_uptime_event_if_missing_locked(status: str, reason: str, event_ts: Optional[int] = None) -> bool:
    ts_value = float(event_ts if event_ts is not None else time.time())
    if _event_exists_near_locked(status=status, event_ts=ts_value):
        return False
    _append_uptime_event_locked(status=status, reason=reason, event_ts=ts_value)
    return True


def _infer_unrecorded_offline_gap_locked(startup_ts: float) -> None:
    """If previous run was marked ON but process restarted, infer OFF start from last heartbeat.
    This preserves true overnight downtime gaps instead of collapsing OFF at restart time.
    """
    if _sanitize_uptime_status(_uptime_data.get("currentStatus")) != "on":
        return

    events = _uptime_data.get("events", [])
    if isinstance(events, list) and events:
        last_event = events[-1]
        if isinstance(last_event, dict) and _sanitize_uptime_status(last_event.get("status")) == "off":
            return

    last_seen_candidates = []
    for value in (
        _uptime_data.get("lastHeartbeatTs", 0),
        _uptime_data.get("updatedAt", 0),
    ):
        try:
            parsed = float(value or 0)
            if parsed > 0:
                last_seen_candidates.append(parsed)
        except Exception:
            pass

    if isinstance(events, list) and events:
        try:
            last_event_ts = float((events[-1] or {}).get("ts", 0) or 0)
            if last_event_ts > 0:
                last_seen_candidates.append(last_event_ts)
        except Exception:
            pass

    if not last_seen_candidates:
        return

    last_seen_ts = max(last_seen_candidates)
    infer_after = last_seen_ts + (UPTIME_HEARTBEAT_INTERVAL_SECONDS * UPTIME_OFFLINE_INFER_MULTIPLIER)
    inferred_off_ts = min(float(startup_ts), max(last_seen_ts, infer_after))

    if inferred_off_ts >= float(startup_ts):
        inferred_off_ts = max(last_seen_ts, float(startup_ts) - 0.001)

    _append_uptime_event_if_missing_locked(
        status="off",
        reason="inferred_offline_gap",
        event_ts=inferred_off_ts,
    )


def _append_uptime_event_locked(status: str, reason: str, event_ts: Optional[int] = None) -> None:
    ts = float(event_ts if event_ts is not None else time.time())
    status = _sanitize_uptime_status(status)
    events = _uptime_data.setdefault("events", [])
    sessions = _uptime_data.setdefault("sessions", [])

    events.append({"ts": ts, "status": status, "reason": reason})
    if len(events) > UPTIME_MAX_EVENTS:
        del events[:-UPTIME_MAX_EVENTS]

    if status == "on":
        sessions.append({"startTs": ts, "endTs": None, "startReason": reason})
    elif status == "off":
        _close_open_sessions_locked(ts, reason)

    _uptime_data["currentStatus"] = status
    _uptime_data["updatedAt"] = ts
    _uptime_data["lastHeartbeatTs"] = ts


def _write_uptime_event(status: str, reason: str, event_ts: Optional[int] = None) -> None:
    with _uptime_data_lock:
        _append_uptime_event_if_missing_locked(status=status, reason=reason, event_ts=event_ts)
        _repair_uptime_data_locked()
        _save_uptime_data_locked()


def _touch_uptime_heartbeat() -> None:
    with _uptime_data_lock:
        now_ts = float(time.time())
        # Self-heal stale OFF state while process is alive (prevents lingering red timeline after recovery).
        if _sanitize_uptime_status(_uptime_data.get("currentStatus")) != "on":
            _append_uptime_event_locked(status="on", reason="heartbeat_recover", event_ts=now_ts)

        _uptime_data["lastHeartbeatTs"] = now_ts
        _uptime_data["updatedAt"] = now_ts
        _repair_uptime_data_locked(now_ts=now_ts)
        _save_uptime_data_locked()


def _run_uptime_monitor() -> None:
    logger.info("Uptime monitor thread started")
    while not _uptime_monitor_stop_event.wait(UPTIME_HEARTBEAT_INTERVAL_SECONDS):
        _touch_uptime_heartbeat()
    logger.info("Uptime monitor thread stopped")


def start_uptime_monitor() -> None:
    global _uptime_monitor_thread
    if _uptime_monitor_thread and _uptime_monitor_thread.is_alive():
        return
    _uptime_monitor_stop_event.clear()
    _uptime_monitor_thread = threading.Thread(target=_run_uptime_monitor, daemon=True)
    _uptime_monitor_thread.start()


def stop_uptime_monitor() -> None:
    _uptime_monitor_stop_event.set()


def load_uptime_data() -> None:
    global _uptime_data
    loaded = _default_uptime_data()

    if os.path.exists(UPTIME_DATA_FILE):
        try:
            with open(UPTIME_DATA_FILE, 'r', encoding='utf-8') as f:
                parsed = json.load(f)
            if isinstance(parsed, dict):
                loaded["events"] = parsed.get("events", []) if isinstance(parsed.get("events"), list) else []
                loaded["sessions"] = parsed.get("sessions", []) if isinstance(parsed.get("sessions"), list) else []
                loaded["currentStatus"] = str(parsed.get("currentStatus", "off") or "off")
                loaded["lastHeartbeatTs"] = float(parsed.get("lastHeartbeatTs", 0) or 0)
                loaded["updatedAt"] = float(parsed.get("updatedAt", 0) or 0)
        except Exception as e:
            logger.error(f"Error loading {UPTIME_DATA_FILE}: {e}. Starting with default uptime data.")

    with _uptime_data_lock:
        _uptime_data = loaded
        now_ts = float(time.time())
        _repair_uptime_data_locked(now_ts=now_ts)
        _infer_unrecorded_offline_gap_locked(startup_ts=now_ts)
        _append_uptime_event_locked(status="on", reason="startup", event_ts=now_ts)
        _repair_uptime_data_locked(now_ts=now_ts)
        _save_uptime_data_locked()


def mark_uptime_shutdown(reason: str = "shutdown") -> None:
    try:
        _write_uptime_event(status="off", reason=reason)
    except Exception as e:
        logger.warning(f"Failed to mark uptime shutdown: {e}")


def get_uptime_payload() -> dict:
    with _uptime_data_lock:
        _repair_uptime_data_locked()
        data = _safe_uptime_snapshot_locked()
    return {"uptimeData": data}


def migrate_tracking_data_file_if_needed() -> None:
    if os.path.exists(LEGACY_TRACKING_DATA_FILE) and not os.path.exists(TRACKING_DATA_FILE):
        try:
            shutil.move(LEGACY_TRACKING_DATA_FILE, TRACKING_DATA_FILE)
            logger.info(f"Migrated {LEGACY_TRACKING_DATA_FILE} -> {TRACKING_DATA_FILE}")
        except Exception as e:
            logger.warning(f"Could not migrate tracking data file: {e}")

def load_tracking_data():
    """Loads tracking data from the JSON file on startup."""
    global _tracking_data
    migrate_tracking_data_file_if_needed()
    if os.path.exists(TRACKING_DATA_FILE):
        with _tracking_data_lock:
            try:
                with open(TRACKING_DATA_FILE, 'r', encoding='utf-8') as f:
                    _tracking_data = json.load(f)
                logger.info(f"Loaded {len(_tracking_data)} entries from {TRACKING_DATA_FILE}")
            except json.JSONDecodeError as e:
                logger.error(f"Error decoding {TRACKING_DATA_FILE}: {e}. Starting with empty tracking data.")
                _tracking_data = []
            except Exception as e:
                logger.error(f"Error loading {TRACKING_DATA_FILE}: {e}. Starting with empty tracking data.")
                _tracking_data = []
    else:
        logger.info(f"{TRACKING_DATA_FILE} not found. Starting with empty tracking data.")
        _tracking_data = []

def save_tracking_data():
    """Saves tracking data to the JSON file."""
    with _tracking_data_lock:
        try:
            with open(TRACKING_DATA_FILE, 'w', encoding='utf-8') as f:
                json.dump(_tracking_data, f, indent=4)
            logger.info(f"Saved {len(_tracking_data)} entries to {TRACKING_DATA_FILE}")
        except Exception as e:
            logger.error(f"Error saving {TRACKING_DATA_FILE}: {e}")

def load_ad_settings():
    """Loads ad settings from the JSON file on startup."""
    global _ADS_ENABLED_GLOBALLY, _SHOW_ADS_TO_ADMINS
    if os.path.exists(AD_SETTINGS_FILE):
        try:
            with open(AD_SETTINGS_FILE, 'r') as f:
                settings = json.load(f)
                _ADS_ENABLED_GLOBALLY = settings.get('ads_enabled_globally', _ADS_ENABLED_GLOBALLY)
                _SHOW_ADS_TO_ADMINS = settings.get('show_ads_to_admins', _SHOW_ADS_TO_ADMINS)
            logger.info(f"Loaded ad settings from {AD_SETTINGS_FILE}: Globally Enabled={_ADS_ENABLED_GLOBALLY}, Show to Admins={_SHOW_ADS_TO_ADMINS}")
        except json.JSONDecodeError as e:
            logger.error(f"Error decoding {AD_SETTINGS_FILE}: {e}. Using default ad settings.")
        except Exception as e:
            logger.error(f"Error loading {AD_SETTINGS_FILE}: {e}. Using default ad settings.")
    else:
        logger.info(f"{AD_SETTINGS_FILE} not found. Using default ad settings.")
        save_ad_settings() # Create the file with default settings

def save_ad_settings():
    """Saves ad settings to the JSON file."""
    settings = {
        'ads_enabled_globally': _ADS_ENABLED_GLOBALLY,
        'show_ads_to_admins': _SHOW_ADS_TO_ADMINS
    }
    try:
        with open(AD_SETTINGS_FILE, 'w') as f:
            json.dump(settings, f, indent=4)
        logger.info(f"Saved ad settings to {AD_SETTINGS_FILE}")
    except Exception as e:
        logger.error(f"Error saving {AD_SETTINGS_FILE}: {e}")

def get_client_ip(handler):
    """
    Extracts the client's IP address from the request handler.
    Prioritizes X-Forwarded-For header for proxy compatibility (e.g., Cloudflare).
    """
    x_forwarded_for = handler.headers.get('X-Forwarded-For')
    if x_forwarded_for:
        # X-Forwarded-For can contain multiple IPs, the client's IP is usually the first
        ip = x_forwarded_for.split(',')[0].strip()
        logger.info(f"Client IP (X-Forwarded-For): {ip}")
        return ip
    
    # Fallback to direct client address
    ip = handler.client_address[0]
    logger.info(f"Client IP (Direct Connection): {ip}")
    return ip

def get_geolocation_data(ip_address: str) -> dict:
    """
    Fetches geolocation data for a given IP address using ip-api.com.
    Includes comprehensive details like country, region, city, lat/lon, ISP, etc.
    Handles localhost (127.0.0.1) explicitly.
    """
    # Default values for "N/A" or "Unknown"
    default_geo_data = {
        "query": ip_address,
        "country": "Unknown", "countryCode": "N/A", "region": "N/A",
        "regionName": "Unknown", "city": "Unknown", "district": "N/A", "zip": "N/A",
        "lat": "N/A", "lon": "N/A", "timezone": "N/A", "offset": "N/A",
        "currency": "N/A", "isp": "Unknown", "org": "Unknown", "as": "Unknown",
        "asname": "Unknown", "mobile": "N/A", "proxy": "N/A", "hosting": "N/A",
        "status": "fail", "message": "Geolocation data not available"
    }

    if ip_address == '127.0.0.1':
        return {
            **default_geo_data, # Start with all default keys
            "query": "127.0.0.1",
            "country": "Localhost", "countryCode": "LO", "regionName": "N/A",
            "city": "N/A", "status": "success", "message": "Localhost IP"
        }
    
    try:
        response = requests.get(f"http://ip-api.com/json/{ip_address}")
        response.raise_for_status() # Raise HTTPError for bad responses (4xx or 5xx)
        data = response.json()

        if data.get('status') == 'success':
            return {
                "query": data.get('query', ip_address),
                "country": data.get('country', 'N/A'),
                "countryCode": data.get('countryCode', 'N/A'),
                "region": data.get('region', 'N/A'),
                "regionName": data.get('regionName', 'N/A'),
                "city": data.get('city', 'N/A'),
                "district": data.get('district', 'N/A'),
                "zip": data.get('zip', 'N/A'),
                "lat": data.get('lat', 'N/A'),
                "lon": data.get('lon', 'N/A'),
                "timezone": data.get('timezone', 'N/A'),
                "offset": data.get('offset', 'N/A'),
                "currency": data.get('currency', 'N/A'),
                "isp": data.get('isp', 'N/A'),
                "org": data.get('org', 'N/A'),
                "as": data.get('as', 'N/A'),
                "asname": data.get('asname', 'N/A'),
                "mobile": "N/A", "proxy": "N/A", "hosting": "N/A",
                "status": "success",
                "message": data.get('message', 'Lookup successful')
            }
        else:
            logger.warning(f"Geolocation API returned non-success status for {ip_address}: {data.get('message')}")
            return {
                **default_geo_data,
                "status": "fail",
                "message": data.get('message', 'API lookup failed')
            }
    except requests.exceptions.RequestException as e:
        logger.error(f"Error fetching geolocation for {ip_address}: {e}")
        return {
            **default_geo_data,
            "status": "error",
            "message": str(e)
        }

async def get_video_frame_count(video_path: str) -> Union[int, None]:
    """
    Uses ffprobe to get the total number of frames in a video.
    Strategy:
      1. Read nb_frames from container metadata (instant, no decoding).
      2. If unavailable (returns 'N/A' or empty), calculate from duration × fps (also instant).
    Returns the frame count as an int, or None if it cannot be determined.
    """
    async def run_ffprobe(args: list) -> tuple[int, str, str]:
        """Helper to run an ffprobe command with timeout, returns (returncode, stdout, stderr)."""
        process = await asyncio.create_subprocess_exec(
            *args,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            **_start_new_session_kwargs()
        )
        _register_async_process(process, "ffprobe-frame-count")
        try:
            stdout, stderr = await asyncio.wait_for(process.communicate(), timeout=FFPROBE_TIMEOUT_SECONDS)
        except asyncio.TimeoutError:
            logger.error(f"FFprobe command timed out after {FFPROBE_TIMEOUT_SECONDS} seconds for {video_path}. Terminating process.")
            process.kill()
            await process.wait()
            _unregister_async_process(process)
            return -1, "", "timeout"
        finally:
            _unregister_async_process(process)
        return process.returncode, stdout.decode('utf-8', errors='ignore').strip(), stderr.decode('utf-8', errors='ignore').strip()

    try:
        # --- Step 1: Try reading nb_frames from container metadata (near-instant) ---
        cmd_metadata = [
            "ffprobe", "-v", "error",
            "-select_streams", "v:0",
            "-show_entries", "stream=nb_frames",
            "-of", "default=nokey=1:noprint_wrappers=1",
            video_path
        ]
        logger.info(f"Running ffprobe (metadata) to get frame count: {' '.join(cmd_metadata)}")
        rc, stdout, stderr = await run_ffprobe(cmd_metadata)

        if rc == 0 and stdout and stdout not in ('N/A', 'n/a', ''):
            try:
                frame_count = int(stdout)
                logger.info(f"FFprobe (metadata) retrieved frame count: {frame_count} for {video_path}")
                return frame_count
            except ValueError:
                logger.warning(f"Could not parse nb_frames from metadata output: '{stdout}', falling back to duration×fps.")
        elif rc == -1:
            return None  # Timed out
        else:
            logger.warning(f"nb_frames not available in metadata (output: '{stdout}'), falling back to duration×fps.")

        # --- Step 2: Fallback — calculate from duration and avg_frame_rate (also near-instant) ---
        cmd_duration = [
            "ffprobe", "-v", "error",
            "-select_streams", "v:0",
            "-show_entries", "stream=duration,avg_frame_rate",
            "-of", "default=nokey=1:noprint_wrappers=1",
            video_path
        ]
        logger.info(f"Running ffprobe (duration+fps) fallback for frame count: {' '.join(cmd_duration)}")
        rc, stdout, stderr = await run_ffprobe(cmd_duration)

        if rc == 0 and stdout:
            lines = [l.strip() for l in stdout.splitlines() if l.strip() and l.strip() not in ('N/A', 'n/a')]
            try:
                # ffprobe outputs avg_frame_rate first, then duration (order depends on show_entries)
                # Parse both: one will be a fraction (fps), one a float (duration)
                duration = None
                fps = None
                for token in lines:
                    if '/' in token:
                        num, den = token.split('/')
                        if float(den) != 0:
                            fps = float(num) / float(den)
                    else:
                        try:
                            duration = float(token)
                        except ValueError:
                            pass
                if duration is not None and fps is not None and fps > 0:
                    frame_count = int(round(duration * fps))
                    logger.info(f"FFprobe (duration×fps) calculated frame count: {frame_count} (duration={duration:.2f}s, fps={fps:.3f}) for {video_path}")
                    return frame_count
                else:
                    logger.error(f"Could not extract valid duration/fps from ffprobe output: {lines}")
                    return None
            except Exception as parse_err:
                logger.error(f"Error parsing duration/fps from ffprobe output '{stdout}': {parse_err}")
                return None
        elif rc == -1:
            return None  # Timed out
        else:
            logger.error(f"FFprobe (duration+fps) failed with exit code {rc}: {stderr}")
            return None

    except FileNotFoundError:
        logger.error("ffprobe command not found. Please ensure FFmpeg is installed and in your system's PATH.")
        return None
    except Exception as e:
        logger.error(f"An unexpected error occurred while getting frame count: {e}", exc_info=True)
        return None


# --- Codec Compatibility Check and Transcode ---

async def _terminate_async_process(process: asyncio.subprocess.Process, label: str) -> None:
    """Best-effort graceful shutdown for subprocesses used by processing jobs."""
    if not process:
        return
    try:
        if process.returncode is not None:
            _unregister_async_process(process)
            return
        pid = process.pid or 0
        if os.name == "posix" and pid > 0:
            try:
                pgid = os.getpgid(pid)
                logger.debug(f"Terminating active subprocess group '{label}' (pid={pid}, pgid={pgid})")
                os.killpg(pgid, signal.SIGTERM)
            except ProcessLookupError:
                _unregister_async_process(process)
                return
            except Exception:
                logger.debug(f"Falling back to direct terminate for subprocess '{label}' (pid={pid})")
                process.terminate()
        else:
            logger.debug(f"Terminating active subprocess '{label}' (pid={process.pid})")
            process.terminate()
        await asyncio.wait_for(process.wait(), timeout=2)
    except Exception:
        try:
            if process.returncode is None:
                pid = process.pid or 0
                if os.name == "posix" and pid > 0:
                    try:
                        pgid = os.getpgid(pid)
                        logger.debug(f"Force-killing subprocess group '{label}' (pid={pid}, pgid={pgid})")
                        os.killpg(pgid, signal.SIGKILL)
                    except Exception:
                        logger.debug(f"Falling back to direct kill for subprocess '{label}' (pid={pid})")
                        process.kill()
                else:
                    logger.debug(f"Force-killing active subprocess '{label}' (pid={process.pid})")
                    process.kill()
                await asyncio.wait_for(process.wait(), timeout=2)
        except Exception as kill_error:
            logger.warning(f"Failed to force-stop subprocess '{label}': {kill_error}")
    finally:
        if process.returncode is not None:
            _unregister_async_process(process)
        else:
            logger.warning(f"Subprocess '{label}' (pid={process.pid}) still appears alive after termination attempts.")

async def ensure_h264_codec(video_path: str, progress_message_obj=None) -> tuple[bool, str]:
    """
    Checks if the video uses a codec compatible with OpenCV (H.264).
    If it's AV1, VP9, or other incompatible codec, transcodes to H.264 using GPU if available.
    Overwrites the original file with the transcoded version so paths stay consistent.
    Returns (success, final_video_path).
    """
    # Codecs that OpenCV's VideoCapture cannot reliably decode
    INCOMPATIBLE_CODECS = {'av1', 'av01', 'vp9', 'vp8'}
    try:
        # Detect codec using ffprobe
        cmd = [
            "ffprobe", "-v", "error",
            "-select_streams", "v:0",
            "-show_entries", "stream=codec_name",
            "-of", "default=nokey=1:noprint_wrappers=1",
            video_path
        ]
        process = await asyncio.create_subprocess_exec(
            *cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            **_start_new_session_kwargs()
        )
        _register_async_process(process, "ffprobe-codec")
        try:
            stdout, _ = await asyncio.wait_for(process.communicate(), timeout=10)
        except asyncio.CancelledError:
            await _terminate_async_process(process, "ffprobe-codec")
            raise
        finally:
            _unregister_async_process(process)
        codec = stdout.decode('utf-8', errors='ignore').strip().lower()
        logger.info(f"Detected video codec: '{codec}' for {video_path}")

        if codec not in INCOMPATIBLE_CODECS:
            logger.info(f"Codec '{codec}' is OpenCV-compatible. No transcode needed.")
            return True, video_path

        # Codec is incompatible — need to transcode to H.264
        logger.warning(f"Codec '{codec}' is not compatible with OpenCV. Transcoding to H.264...")
        if progress_message_obj:
            await progress_message_obj.edit_text(f"Transcoding from {codec.upper()} to H.264 for processing (this may take a moment)...")
        set_processing_status(f"Transcoding from {codec.upper()} to H.264...")

        temp_path = video_path + '.transcode_tmp.mp4'

        # Try GPU (NVENC) first for speed, fall back to CPU
        for encoder, extra_args in [('h264_nvenc', ['-preset', 'p4']), ('libx264', ['-preset', 'ultrafast', '-crf', '18'])]:
            transcode_cmd = [
                "ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
                "-i", video_path,
                "-c:v", encoder, *extra_args,
                "-c:a", "copy",
                temp_path
            ]
            logger.info(f"Transcoding with {encoder}: {' '.join(transcode_cmd)}")
            transcode_proc = await asyncio.create_subprocess_exec(
                *transcode_cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                **_start_new_session_kwargs()
            )
            _register_async_process(transcode_proc, f"ffmpeg-transcode-{encoder}")
            try:
                _, stderr = await transcode_proc.communicate()
            except asyncio.CancelledError:
                await _terminate_async_process(transcode_proc, f"ffmpeg-transcode-{encoder}")
                raise
            finally:
                _unregister_async_process(transcode_proc)
            if transcode_proc.returncode == 0:
                # Replace original file with transcoded version
                try:
                    os.replace(temp_path, video_path)
                except OSError as e:
                    logger.error(f"Could not replace original file after transcode: {e}")
                    return False, video_path
                logger.info(f"Transcode to H.264 successful using {encoder}. File updated: {video_path}")
                return True, video_path
            else:
                err_msg = stderr.decode('utf-8', errors='ignore').strip()
                logger.warning(f"Transcode with {encoder} failed (will try next): {err_msg[:200]}")
                # Clean up failed temp file if it exists
                if os.path.exists(temp_path):
                    try:
                        os.remove(temp_path)
                    except OSError:
                        pass

        logger.error(f"All transcode attempts failed for {video_path}.")
        return False, video_path

    except asyncio.TimeoutError:
        logger.error("Codec detection timed out.")
        return False, video_path
    except FileNotFoundError:
        logger.error("ffprobe/ffmpeg not found during codec check.")
        return False, video_path
    except Exception as e:
        logger.error(f"Unexpected error in ensure_h264_codec: {e}", exc_info=True)
        return False, video_path


# --- Helper Functions for Streaming Subprocess Output ---

async def _stream_output_and_update_message(
    stream: asyncio.StreamReader,
    progress_message_obj, # Can be Update.message or WebProgressReporter
    context: ContextTypes.DEFAULT_TYPE,
    stream_name: str,
    progress_type: str # 'wget', 'tqdm', 'ffmpeg', 'general', 'yt-dlp'
):
    """
    Reads from a subprocess stream, handling carriage returns for real-time updates,
    and updates the Telegram message or web progress.
    """
    last_update_time = time.time()
    last_progress_text = ""
    current_line_buffer = ""

    wget_progress_regex = re.compile(r"^\s*\d+[KMGT]?\s+[\.\s]+\s*\d+%.*")
    tqdm_regex = re.compile(r"Processing Frames \(.*\): (.*)")
    ffmpeg_regex = re.compile(r"frame=\s*\d+\s+fps=[\d\.]+\s+q=[\d\.\-]+.*")
    # New regex for yt-dlp progress
    yt_dlp_progress_regex = re.compile(r"\[download\]\s+.*% of.*\s+at\s+.*B/s.*")
    yt_dlp_post_process_regex = re.compile(r'\[Merger\] Merging formats into \"(.*)\"')
    # Regex to detect [ADAPTIVE] telemetry lines (suppressed to DEBUG)
    adaptive_line_regex = re.compile(r"\[ADAPTIVE\]")


    while True:
        chunk = await stream.read(128)
        if not chunk:
            break
        
        decoded_chunk = chunk.decode('utf-8', errors='ignore')

        for char in decoded_chunk:
            if char == '\r':
                if current_line_buffer:
                    progress_info = current_line_buffer.strip()
                    new_progress_text = ""

                    if progress_type == 'wget':
                        if wget_progress_regex.search(progress_info):
                            new_progress_text = f"Downloading: {progress_info}"
                    elif progress_type == 'yt-dlp':
                        if yt_dlp_progress_regex.search(progress_info):
                            new_progress_text = f"Downloading: {progress_info}"
                        elif yt_dlp_post_process_regex.search(progress_info):
                            new_progress_text = f"Post-processing: {progress_info}"
                    elif progress_type == 'tqdm':
                        tqdm_match = tqdm_regex.search(progress_info)
                        if tqdm_match:
                            new_progress_text = f"Processing: {tqdm_match.group(1).strip()}"
                    elif progress_type == 'ffmpeg':
                        ffmpeg_match = ffmpeg_regex.search(progress_info)
                        if ffmpeg_match:
                            new_progress_text = f"Merging Audio: {ffmpeg_match.group(0).strip()}"
                    
                    if new_progress_text and new_progress_text != last_progress_text and (time.time() - last_update_time > 1):
                        set_processing_status(new_progress_text)
                        try:
                            if progress_message_obj:
                                await progress_message_obj.edit_text(new_progress_text)
                            last_progress_text = new_progress_text
                            last_update_time = time.time()
                        except Exception as e:
                            logger.warning(f"Could not edit progress message ({progress_type} progress): {e}")
                current_line_buffer = ""
            elif char == '\n':
                full_line = current_line_buffer.strip()
                # Suppress [ADAPTIVE] telemetry to DEBUG to avoid terminal spam
                if adaptive_line_regex.search(full_line):
                    logger.debug(f"[{stream_name} full line] {full_line}")
                else:
                    logger.info(f"[{stream_name} full line] {full_line}")
                if "ERROR" in full_line:
                    if progress_message_obj and context: # Only send new Telegram message if context is available
                        try:
                            await context.bot.send_message(chat_id=progress_message_obj.chat_id, text=f"Error from {stream_name}: {full_line}")
                        except Exception as e:
                            logger.warning(f"Could not send new Telegram message for error: {e}")
                current_line_buffer = ""
            else:
                current_line_buffer += char
        
        if current_line_buffer and time.time() - last_update_time > 1:
            progress_info = current_line_buffer.strip()
            new_progress_text = ""
            if progress_type == 'wget':
                if wget_progress_regex.search(progress_info):
                    new_progress_text = f"Downloading: {progress_info}"
            elif progress_type == 'yt-dlp':
                if yt_dlp_progress_regex.search(progress_info):
                    new_progress_text = f"Downloading: {progress_info}"
                elif yt_dlp_post_process_regex.search(progress_info):
                    new_progress_text = f"Post-processing: {progress_info}"
            elif progress_type == 'tqdm':
                tqdm_match = tqdm_regex.search(progress_info)
                if tqdm_match:
                    new_progress_text = f"Processing: {tqdm_match.group(1).strip()}"
            elif progress_type == 'ffmpeg':
                ffmpeg_match = ffmpeg_regex.search(progress_info)
                if ffmpeg_match:
                    new_progress_text = f"Merging Audio: {ffmpeg_match.group(0).strip()}"

            if new_progress_text and new_progress_text != last_progress_text:
                set_processing_status(new_progress_text)
                try:
                    if progress_message_obj:
                        await progress_message_obj.edit_text(new_progress_text)
                    last_progress_text = new_progress_text
                    last_update_time = time.time()
                except Exception as e:
                    logger.warning(f"Could not edit progress message (partial {progress_type} progress): {e}")

# MODIFIED: Use yt-dlp for video downloads instead of wget for robustness
async def download_video_async(url: str, output_dir: str, progress_message_obj=None, context=None) -> tuple[bool, str]:
    """
    Asynchronously downloads a video from a URL using yt-dlp and streams progress.
    Returns (success, actual_output_filepath).
    """
    try:
        # Use yt-dlp for robust video downloading
        # -o: output template. %(id)s.%(ext)s ensures a unique filename with correct extension.
        # -f: format selection. 'bestvideo+bestaudio/best' to get the highest quality available.
        # --progress: show progress bar.
        # --no-playlist: prevent downloading entire playlists if URL is part of one.
        # --output-na-placeholder "": prevents outputting 'NA' for missing fields in filename
        # --restrict-filenames: avoids special characters in filenames that might cause issues.
        # --continue: resume download if file partially exists.
        # --external-downloader aria2c: if aria2c is installed, it can speed up downloads.
        # --external-downloader-args "-x 16 -s 16 -k 1M": arguments for aria2c (16 connections, 16 segments, 1MB min size).
        
        # Determine the full output path including filename using yt-dlp's output template logic
        # yt-dlp automatically names files based on the video's title and extension.
        # We need to ensure it saves to INPUT_SUBDIRECTORY.
        
        # First, dry-run to get the expected filename.
        dry_run_command = [
            "yt-dlp",
            "--simulate",
            "--get-filename",
            "-o", "%(title)s.%(ext)s",  # No dir prefix; we join manually below
            "-f", "bestvideo[ext=mp4][vcodec^=avc]+bestaudio[ext=m4a]/bestvideo[ext=mp4][vcodec!*=av01]+bestaudio[ext=m4a]/bestvideo[vcodec^=avc]+bestaudio/best",
            "--merge-output-format", "mp4",  # Ensure output format is mp4
            "--no-playlist",  # Only get filename for the target video, not the entire playlist
            "--restrict-filenames",  # Sanitise to ASCII-safe chars (matches actual download)
            "--js-runtimes", "node",  # Use Node.js as JS runtime for YouTube extraction
            url
        ]
        logger.info(f"Starting yt-dlp dry-run to get filename: {' '.join(dry_run_command)}")
        dry_run_process = await asyncio.create_subprocess_exec(
            *dry_run_command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            **_start_new_session_kwargs()
        )
        _register_async_process(dry_run_process, "yt-dlp-dry-run")
        try:
            stdout, stderr = await dry_run_process.communicate()
        except asyncio.CancelledError:
            await _terminate_async_process(dry_run_process, "yt-dlp-dry-run")
            raise
        finally:
            _unregister_async_process(dry_run_process)
        
        if dry_run_process.returncode != 0:
            error_msg = stderr.decode('utf-8', errors='ignore').strip()
            logger.error(f"yt-dlp dry-run failed with exit code {dry_run_process.returncode}: {error_msg}")
            if progress_message_obj:
                await progress_message_obj.edit_text(f"Download setup failed (dry-run): {error_msg[:200]}...")
            return False, ""

        raw_dry_run_output = stdout.decode('utf-8', errors='ignore').strip()
        # Take only the FIRST non-empty line — safety net if playlist output slips through
        actual_output_filename = next(
            (line.strip() for line in raw_dry_run_output.splitlines() if line.strip()), ""
        )
        # Remove any remaining OS-unsafe characters
        actual_output_filename = re.sub(r'[\\/:*?"<>|]', '_', actual_output_filename)
        # Ensure filename ends with .mp4
        if not actual_output_filename.lower().endswith('.mp4'):
            actual_output_filename = os.path.splitext(actual_output_filename)[0] + '.mp4'
        # Truncate stem so total filename stays well within the Linux 255-byte limit
        stem, ext = os.path.splitext(actual_output_filename)
        max_stem_bytes = 180  # leaves room for extension + headroom
        encoded_stem = stem.encode('utf-8')
        if len(encoded_stem) > max_stem_bytes:
            stem = encoded_stem[:max_stem_bytes].decode('utf-8', errors='ignore').rstrip()
            logger.warning(f"Filename stem truncated to {max_stem_bytes} bytes to avoid OS limit.")
        actual_output_filename = stem + ext
        actual_output_path = os.path.join(output_dir, actual_output_filename)

        command = [
            "yt-dlp",
            "-o", actual_output_path,
            # Prefer H.264 (avc) to ensure OpenCV compatibility. Explicitly avoid AV1 (av01) and VP9.
            # Fallback chain: H.264 mp4 → non-AV1 mp4 → H.264 any container → absolute best
            "-f", "bestvideo[ext=mp4][vcodec^=avc]+bestaudio[ext=m4a]/bestvideo[ext=mp4][vcodec!*=av01]+bestaudio[ext=m4a]/bestvideo[vcodec^=avc]+bestaudio/best",
            "--merge-output-format", "mp4",  # Ensure output is mp4
            "--progress",
            "--no-playlist",
            "--output-na-placeholder", "",
            "--restrict-filenames",
            "--continue",
            "--js-runtimes", "node",  # Use Node.js as JS runtime for YouTube extraction
            url
        ]
        logger.info(f"Starting yt-dlp command: {' '.join(command)}")

        process = await asyncio.create_subprocess_exec(
            *command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            **_start_new_session_kwargs()
        )
        _register_async_process(process, "yt-dlp-download")

        stdout_task = asyncio.create_task(
            _stream_output_and_update_message(process.stdout, progress_message_obj, context, "yt-dlp_stdout", 'yt-dlp')
        )
        stderr_task = asyncio.create_task(
            _stream_output_and_update_message(process.stderr, progress_message_obj, context, "yt-dlp_stderr", 'yt-dlp')
        )

        try:
            return_code = await process.wait()
            await stdout_task
            await stderr_task
        except asyncio.CancelledError:
            await _terminate_async_process(process, "yt-dlp-download")
            stdout_task.cancel()
            stderr_task.cancel()
            raise
        finally:
            _unregister_async_process(process)

        if return_code == 0:
            logger.info(f"yt-dlp download finished successfully. Saved to: {actual_output_path}")
            return True, actual_output_path
        else:
            remaining_stderr = (await process.stderr.read()).decode('utf-8', errors='ignore').strip()
            if remaining_stderr:
                logger.error(f"yt-dlp download failed with exit code {return_code}:\n{remaining_stderr}")
                if progress_message_obj:
                    await progress_message_obj.edit_text(f"Download failed with exit code {return_code}. Details: {remaining_stderr[:200]}...")
            else:
                logger.error(f"yt-dlp download failed with exit code {return_code}.")
                if progress_message_obj:
                    await progress_message_obj.edit_text(f"Download failed with exit code {return_code}. Check logs for details.")
            return False, ""

    except FileNotFoundError:
        logger.error("yt-dlp command not found. Please ensure it is installed (e.g., pip install yt-dlp) and in your system's PATH.")
        if progress_message_obj:
            await progress_message_obj.edit_text("Error: yt-dlp command not found on the server. Please install it.")
        return False, ""
    except Exception as e:
        logger.error(f"An unexpected error occurred during yt-dlp download: {e}", exc_info=True)
        if progress_message_obj:
            await progress_message_obj.edit_text(f"An unexpected error occurred during download: {e}")
        return False, ""


async def run_tracking_script_and_stream_output(
    input_path: str, output_path: str, progress_message_obj=None, context=None,
    roi_params: dict = None, allowed_classes: list = None, confidence_threshold: float = None
) -> bool:
    """
    Runs your video tracking script by passing arguments and streams its output.
    progress_message_obj and context are optional for web server usage.
    roi_params is a dict with ROI parameters.
    allowed_classes is a list of object names to track.
    confidence_threshold is the minimum confidence score.
    """
    try:
        command = [
            "python3",
            "-u",
            "ot.py",
            "--model", "yolov8m.pt",
            "--preset", "ultrafast",
            "--crf", "24",
            # Pass the full .mp4 path — ot.py already does: if not endswith('.mp4'): strip+add .mp4
            # DO NOT strip .mp4 here: titles like 'R.D._Burman' have dots that os.path.splitext
            # mistakes for an extension, silently dropping the last segment from the output filename.
            "--output_video", output_path,
            "--input_video", input_path # Pass input video path as an argument
        ]
        
        # Add allowed classes if provided
        if allowed_classes:
            command.append("--allowed_classes")
            command.extend(allowed_classes)
            logger.info(f"Custom allowed classes: {allowed_classes}")
            
        # Add confidence threshold if provided
        if confidence_threshold is not None:
            command.extend(["--confidence_threshold", str(confidence_threshold)])
            logger.info(f"Custom confidence threshold: {confidence_threshold}")
        
        # Add ROI parameters if provided
        if roi_params and roi_params.get('roi_enabled') == 'true':
            command.extend([
                "--roi_enabled", "true",
                "--roi_x", str(roi_params.get('roi_x', '0')),
                "--roi_y", str(roi_params.get('roi_y', '0')),
                "--roi_width", str(roi_params.get('roi_width', '1')),
                "--roi_height", str(roi_params.get('roi_height', '1')),
                "--roi_show_overlay", str(roi_params.get('roi_show_overlay', 'true')),
                "--roi_overlay_opacity", str(roi_params.get('roi_overlay_opacity', '30'))
            ])
            logger.info(f"ROI enabled with params: x={roi_params.get('roi_x')}, y={roi_params.get('roi_y')}, w={roi_params.get('roi_width')}, h={roi_params.get('roi_height')}")
        
        logger.info(f"Starting tracking command: {' '.join(command)}")

        process = await asyncio.create_subprocess_exec(
            *command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            **_start_new_session_kwargs()
        )
        _register_async_process(process, "ot.py")

        stdout_task = asyncio.create_task(
            _stream_output_and_update_message(process.stdout, progress_message_obj, context, "ot_stdout", 'general')
        )
        stderr_task = asyncio.create_task(
            _stream_output_and_update_message(process.stderr, progress_message_obj, context, "ot_stderr", 'tqdm')
        )

        try:
            return_code = await process.wait()
            await stdout_task
            await stderr_task
        except asyncio.CancelledError:
            await _terminate_async_process(process, "ot.py")
            stdout_task.cancel()
            stderr_task.cancel()
            raise
        finally:
            _unregister_async_process(process)

        if return_code == 0:
            logger.info("ot.py script finished successfully.")
            return True
        else:
            logger.error(f"ot.py script exited with code {return_code}.")
            if progress_message_obj:
                await progress_message_obj.edit_text(f"Processing failed with exit code {return_code}. Check logs for details.")
            return False

    except FileNotFoundError:
        logger.error("ot.py script not found. Ensure it's in the same directory or accessible via PATH.")
        if progress_message_obj:
            await progress_message_obj.edit_text("Error: Tracking script (ot.py) not found on the server.")
        return False
    except Exception as e:
        logger.error(f"An unexpected error occurred while running ot.py: {e}", exc_info=True)
        if progress_message_obj:
            await progress_message_obj.edit_text(f"An unexpected error occurred during processing: {e}")
        return False


# --- Unified Video Processing Function ---
async def process_video_unified(video_source: Union[str, cgi.FieldStorage], is_file_upload: bool, progress_message_obj=None, telegram_context=None, client_ip: str = "N/A", geolocation_info: dict = None, roi_params: dict = None, original_filename: str = None, allowed_classes: list = None, confidence_threshold: float = None):
    """
    Unified function to process video, upload to GDrive, and update GitHub Pages.
    progress_message_obj is the actual Telegram message object to edit (for Telegram)
    or a WebProgressReporter instance (for web).
    telegram_context is needed for sending new messages in case of errors from subprocess streams (for Telegram).
    client_ip and geolocation_info are new parameters for tracking.
    roi_params is a dict with ROI parameters from the frontend.
    original_filename is the original filename from a preview session (for cached files).
    allowed_classes is a list of strings specifying which objects to track.
    confidence_threshold is a float specifying the minimum confidence for detection.
    """
    # Ensure geolocation_info has all expected keys, even if N/A
    default_geolocation_data = {
        "query": "N/A", "country": "N/A", "countryCode": "N/A", "region": "N/A",
        "regionName": "N/A", "city": "N/A", "district": "N/A", "zip": "N/A",
        "lat": "N/A", "lon": "N/A", "timezone": "N/A", "offset": "N/A",
        "currency": "N/A", "isp": "N/A", "org": "N/A", "as": "N/A",
        "asname": "N/A", "mobile": "N/A", "proxy": "N/A", "hosting": "N/A",
        "status": "unknown", "message": "No geolocation lookup performed"
    }
    if geolocation_info is None:
        geolocation_info = default_geolocation_data
    else:
        # Merge provided info with defaults to ensure all keys are present
        geolocation_info = {**default_geolocation_data, **geolocation_info}


    # Reset status immediately when a new processing task starts
    set_processing_status("Initializing video processing...")

    input_filename = "" # Initialize input_filename
    local_input_path = "" # Initialize local_input_path

    if not is_file_upload:
        # For URL, yt-dlp will determine the filename
        # We'll get the actual filename from the download_video_async return
        input_filename = "downloaded_video" # Placeholder, will be updated
        local_input_path = os.path.join(INPUT_SUBDIRECTORY, input_filename)
    else:
        # Check if video_source is a cached file path (string) or a FieldStorage object
        if isinstance(video_source, str) and os.path.exists(video_source):
            # It's a cached file path from preview session
            # Use the original_filename parameter if provided (from preview session)
            if original_filename:
                input_filename = original_filename
                logger.info(f"Using original filename from preview session: {input_filename}")
            else:
                # Fallback: extract from path (legacy behavior)
                cached_basename = os.path.basename(video_source)
                parts = cached_basename.split('_', 1)
                if len(parts) > 1 and len(parts[0]) == 36:  # UUID is 36 chars
                    input_filename = parts[1]
                else:
                    input_filename = cached_basename
                logger.info(f"Using filename extracted from path: {input_filename}")
        else:
            input_filename = resolve_uploaded_filename(video_source)
        local_input_path = os.path.join(INPUT_SUBDIRECTORY, input_filename)
        
    output_filename = f"processed_{os.path.splitext(input_filename)[0]}.mp4" # Ensure .mp4 extension for output
    local_output_path = os.path.join(OUTPUT_SUBDIRECTORY, output_filename)


    if progress_message_obj:
        await asyncio.sleep(0.5)
        await progress_message_obj.edit_text("Starting video processing...")
        set_processing_status("Starting video processing...") # Update global status

    download_success = True
    actual_download_path = ""

    if not is_file_upload:
        # Pass INPUT_SUBDIRECTORY to yt-dlp, it will create file with title and extension
        download_success, actual_download_path = await download_video_async(video_source, INPUT_SUBDIRECTORY, progress_message_obj, telegram_context)
        if download_success:
            local_input_path = actual_download_path # Update local_input_path to the actual downloaded file
            input_filename = os.path.basename(local_input_path) # Update input_filename as well
            output_filename = f"processed_{os.path.splitext(input_filename)[0]}.mp4"
            local_output_path = os.path.join(OUTPUT_SUBDIRECTORY, output_filename)
    else:
        # Check if video_source is a string path (cached preview file) or a FieldStorage object
        if isinstance(video_source, str) and os.path.exists(video_source):
            # It's a cached file path from preview session - move it to input directory
            try:
                # Move the file from preview directory to input directory
                shutil.move(video_source, local_input_path)
                logger.info(f"Moved cached preview file to: {local_input_path}")
            except Exception as e:
                logger.error(f"Error moving cached preview file: {e}")
                if progress_message_obj:
                    await progress_message_obj.edit_text(f"Failed to process cached file: {e}")
                set_processing_status(f"Failed to process cached file: {e}")
                reset_status_after_delay()
                return False
        else:
            # It's a FieldStorage object from direct upload
            try:
                if hasattr(video_source.file, "seek"):
                    video_source.file.seek(0)
                with open(local_input_path, 'wb') as f:
                    f.write(video_source.file.read())
                logger.info(f"Uploaded file saved to: {local_input_path}")
            except Exception as e:
                logger.error(f"Error saving uploaded file: {e}")
                if progress_message_obj:
                    await progress_message_obj.edit_text(f"Failed to save uploaded file: {e}")
                set_processing_status(f"Failed to save uploaded file: {e}") # Update global status
                reset_status_after_delay() # Reset status after failure
                return False

    if not download_success:
        set_processing_status("Video download failed.") # Update global status
        reset_status_after_delay() # Reset status after failure
        return False

    # --- Codec Compatibility Check (must run before frame count and tracking) ---
    # OpenCV cannot decode AV1 or VP9. Transcode to H.264 if needed.
    codec_ok, local_input_path = await ensure_h264_codec(local_input_path, progress_message_obj)
    if not codec_ok:
        message = "Video codec is not supported and transcoding failed. Please try a different video or format."
        logger.error(message)
        if progress_message_obj:
            await progress_message_obj.edit_text(message)
        set_processing_status(message)
        reset_status_after_delay()
        if os.path.exists(local_input_path):
            try:
                os.remove(local_input_path)
            except OSError:
                pass
        return False
    # Update dependent paths in case filename changed (it shouldn't, but be safe)
    input_filename = os.path.basename(local_input_path)
    output_filename = f"processed_{os.path.splitext(input_filename)[0]}.mp4"
    local_output_path = os.path.join(OUTPUT_SUBDIRECTORY, output_filename)

    # --- Frame Restriction Check ---
    if FRAME_RESTRICTION_ENABLED:
        if progress_message_obj:
            await progress_message_obj.edit_text("Checking video frame count...")
            set_processing_status("Checking video frame count...")

        frame_count = await get_video_frame_count(local_input_path)
        if frame_count is None:
            message = "Could not determine video frame count within timeout. This video may be too large or problematic for processing."
            logger.warning(message)
            if progress_message_obj:
                await progress_message_obj.edit_text(message)
            set_processing_status(message) # Update status for frontend
            reset_status_after_delay()
            # Clean up the downloaded/uploaded file if ffprobe failed or timed out
            if os.path.exists(local_input_path):
                try:
                    os.remove(local_input_path)
                    logger.info(f"Cleaned up problematic video file: {local_input_path}")
                except OSError as e:
                    logger.warning(f"Error deleting problematic video file '{local_input_path}': {e}")
            return False # Stop processing due to ffprobe failure/timeout
        elif frame_count > FRAME_RESTRICTION_VALUE:
            message = f"Video rejected: The video has {frame_count} frames, which exceeds the limit of {FRAME_RESTRICTION_VALUE} frames. Please try a shorter video."
            logger.warning(message)
            if progress_message_obj:
                await progress_message_obj.edit_text(message)
            set_processing_status(message)
            reset_status_after_delay()
            # Clean up the downloaded/uploaded file if rejected
            if os.path.exists(local_input_path):
                try:
                    os.remove(local_input_path)
                    logger.info(f"Cleaned up rejected video file: {local_input_path}")
                except OSError as e:
                    logger.warning(f"Error deleting rejected video file '{local_input_path}': {e}")
            return False # Stop processing
        else:
            message = f"Video has {frame_count} frames (within limit of {FRAME_RESTRICTION_VALUE}). Proceeding with processing."
            logger.info(message)
            if progress_message_obj:
                await progress_message_obj.edit_text(message)
    # --- End Frame Restriction Check ---

    if progress_message_obj:
        await progress_message_obj.edit_text("Video downloaded/saved. Starting object tracking...")
        set_processing_status("Video downloaded/saved. Starting object tracking...") # Update global status
    
    # Pass the correctly determined local_input_path for processing, along with ROI params, classes, and confidence
    tracking_success = await run_tracking_script_and_stream_output(
        local_input_path, local_output_path, progress_message_obj, telegram_context,
        roi_params=roi_params,
        allowed_classes=allowed_classes,
        confidence_threshold=confidence_threshold
    )

    if not tracking_success:
        cancel_snapshot = _snapshot_active_processing_job()
        if cancel_snapshot.get("cancelRequested"):
            set_processing_status("⛔ Processing cancelled. Server is ready for the next video.")
            reset_status_after_delay(4)
            return False
        set_processing_status("Object tracking failed.") # Update global status
        reset_status_after_delay() # Reset status after failure
        return False

    video_title_for_gh = os.path.splitext(input_filename)[0].replace('_', ' ').title()
    video_description_for_gh = f"Object tracking results for {input_filename}"
    
    commit_sha = None # Initialize commit_sha here

    if USE_GITHUB_PAGES:
        if progress_message_obj:
            await progress_message_obj.edit_text("Object tracking complete! Uploading to Google Drive and updating GitHub Pages...")
            set_processing_status("Object tracking complete! Uploading to Google Drive and updating GitHub Pages...") # Update global status

        # Progress callback that relays Google Drive upload progress to the frontend
        def _upload_progress_callback(percent, uploaded_mb, total_mb):
            if percent == -1:
                # Sentinel from gh.py: upload done, now committing to GitHub
                set_processing_status("Uploading: \u2705 Upload complete. Committing to GitHub Pages...")
            else:
                set_processing_status(f"Uploading: {percent}% ({uploaded_mb:.1f}/{total_mb:.1f} MB) \u2192 Google Drive")

        # update_github_pages_with_video returns success, commit SHA, and latest Drive download URL
        gh_update_success, commit_sha, drive_download_url = await update_github_pages_with_video(
            processed_video_path=local_output_path,
            original_video_title=video_title_for_gh,
            description=video_description_for_gh,
            progress_callback=_upload_progress_callback
        )
        if gh_update_success:
            if progress_message_obj:
                await progress_message_obj.edit_text("🎉 Object tracking and GitHub Pages update complete!")
            set_processing_status("🎉 Object tracking and GitHub Pages update complete!") # Update global status
            logger.info("GitHub Pages update successful.")

            if is_benchmarking_enabled():
                telemetry_path = f"{local_output_path}.telemetry.json"
                with _benchmark_lock:
                    global _benchmark_in_progress
                    _benchmark_in_progress = True
                benchmark_run_id = _new_benchmark_run_id()
                _set_benchmark_progress(
                    run_id=benchmark_run_id,
                    progress_pct=1,
                    stage="queued",
                    detail="Preparing benchmark run",
                    eta_seconds=None,
                )
                benchmark_status_message = "📊 Running quality benchmark (VMAF/SSIM/PSNR)... New uploads blocked until complete."
                set_processing_status(benchmark_status_message)
                if progress_message_obj:
                    await progress_message_obj.edit_text(benchmark_status_message)

                async def _run_benchmark_background():
                    global _benchmark_in_progress
                    try:
                        last_status_key = None
                        last_status_emit_at = 0.0

                        def _benchmark_progress_callback(progress_pct: int, stage: str, detail: str = "", eta_seconds: Optional[int] = None):
                            nonlocal last_status_key, last_status_emit_at
                            _set_benchmark_progress(
                                run_id=benchmark_run_id,
                                progress_pct=progress_pct,
                                stage=stage,
                                detail=detail,
                                eta_seconds=eta_seconds,
                            )

                            eta_text = _format_eta_seconds(eta_seconds)
                            detail_suffix = f" | {detail}" if detail else ""
                            eta_suffix = f" | ETA: {eta_text}" if eta_text else ""
                            status_message = f"📊 Benchmark {progress_pct}% | Stage: {stage}{detail_suffix}{eta_suffix}"

                            # Keep ETA dynamic in payload, but avoid emitting every tiny ETA fluctuation.
                            status_key = (int(progress_pct), str(stage), str(detail))
                            now = time.monotonic()
                            is_terminal_stage = str(stage).lower() in {"complete", "failed", "cancelled"}
                            should_emit = (
                                status_key != last_status_key and (
                                    is_terminal_stage or
                                    now - last_status_emit_at >= 1.5 or
                                    progress_pct in (0, 100)
                                )
                            )

                            # Heartbeat every 8 seconds during long unchanged segments.
                            if (not should_emit) and (now - last_status_emit_at >= 8.0):
                                should_emit = True

                            if should_emit:
                                set_processing_status(status_message)
                                last_status_key = status_key
                                last_status_emit_at = now

                        stats_path = f"{local_output_path}.stats.json"
                        benchmark_result = await run_production_benchmark(
                            original_video_path=local_input_path,
                            processed_video_path=local_output_path,
                            video_title=video_title_for_gh,
                            google_drive_url=drive_download_url or "",
                            commit_sha=commit_sha,
                            telemetry_path=telemetry_path if os.path.exists(telemetry_path) else None,
                            stats_path=stats_path if os.path.exists(stats_path) else None,
                            progress_callback=_benchmark_progress_callback,
                        )

                        vmaf_value = benchmark_result.get("vmaf", benchmark_result.get("VMAF", "")) if isinstance(benchmark_result, dict) else ""
                        mota_value = benchmark_result.get("MOTA_Score", benchmark_result.get("mota_score", "")) if isinstance(benchmark_result, dict) else ""
                        try:
                            update_recon_index_scores(
                                project_root=os.getcwd(),
                                video_filename=os.path.basename(local_input_path),
                                vmaf_score=vmaf_value,
                                mota_score=mota_value,
                                stage="post_process",
                            )
                        except Exception as recon_score_error:
                            logger.warning(f"Could not update recon_index scores: {recon_score_error}")

                        set_processing_status("✅ Benchmark complete. Benchmark dashboard data updated.")
                        reset_status_after_delay(5)
                    except asyncio.CancelledError:
                        set_processing_status("⛔ Benchmark cancelled. Server is ready for the next video.")
                        _set_benchmark_progress(
                            run_id=benchmark_run_id,
                            progress_pct=0,
                            stage="cancelled",
                            detail="Cancelled by user",
                            eta_seconds=None,
                        )
                        reset_status_after_delay(4)
                        raise
                    except Exception as benchmark_error:
                        logger.error(f"Production benchmark failed: {benchmark_error}", exc_info=True)
                        set_processing_status("⚠️ Benchmark failed. Core upload succeeded, check backend logs.")
                        _set_benchmark_progress(
                            run_id=benchmark_run_id,
                            progress_pct=100,
                            stage="failed",
                            detail="Benchmark error",
                            eta_seconds=None,
                        )
                        reset_status_after_delay(8)
                    finally:
                        with _benchmark_lock:
                            _benchmark_in_progress = False
                        _clear_active_benchmark_task(asyncio.current_task())
                        _reset_benchmark_progress()

                benchmark_task = asyncio.get_running_loop().create_task(_run_benchmark_background())
                _set_active_benchmark_task(benchmark_task)
            
            # --- Add tracking entry after successful GitHub update ---
            if commit_sha: # Only add if commit_sha is available
                tracking_entry = {
                    "timestamp": int(time.time()),
                    "videoTitle": video_title_for_gh,
                    "commitSha": commit_sha,
                    "ipAddress": client_ip,
                    "googleDriveFileId": None,
                    "driveDownloadUrl": drive_download_url or "",
                    "geolocation": { # Nested geolocation details
                        "country": geolocation_info.get('country', 'N/A'),
                        "countryCode": geolocation_info.get('countryCode', 'N/A'),
                        "region": geolocation_info.get('region', 'N/A'),
                        "regionName": geolocation_info.get('regionName', 'N/A'),
                        "city": geolocation_info.get('city', 'N/A'),
                        "district": geolocation_info.get('district', 'N/A'),
                        "zip": geolocation_info.get('zip', 'N/A'),
                        "lat": geolocation_info.get('lat', 'N/A'),
                        "lon": geolocation_info.get('lon', 'N/A'),
                        "timezone": geolocation_info.get('timezone', 'N/A'),
                        "offset": geolocation_info.get('offset', 'N/A'),
                        "currency": geolocation_info.get('currency', 'N/A'),
                        "isp": geolocation_info.get('isp', 'N/A'),
                        "org": geolocation_info.get('org', 'N/A'),
                        "as": geolocation_info.get('as', 'N/A'),
                        "asname": geolocation_info.get('asname', 'N/A'),
                        "mobile": geolocation_info.get('mobile', 'N/A'),
                        "proxy": geolocation_info.get('proxy', 'N/A'),
                        "hosting": geolocation_info.get('hosting', 'N/A'),
                        "status": geolocation_info.get('status', 'unknown'),
                        "message": geolocation_info.get('message', 'N/A')
                    }
                }
                # To get googleDriveFileId for tracking_entry, we need to fetch videos.json again
                # or modify gh.py to return it. For now, we'll keep it as None here
                # or fetch it from the latest videos.json in gh.py if that's easier.
                # Since gh.py update_github_pages_with_video returns (success, commit_sha)
                # it does not return the file_id directly. If you modify gh.py later
                # to return the file_id, you can update tracking_entry["googleDriveFileId"] here.
                
                with _tracking_data_lock:
                    _tracking_data.insert(0, tracking_entry) # Add to the beginning (most recent first)
                save_tracking_data()
                logger.info(f"Added tracking entry for video '{video_title_for_gh}' from IP {client_ip}")

            if not is_benchmarking_enabled():
                reset_status_after_delay() # Reset status after success only when benchmark mode is off
            return True
        else:
            if progress_message_obj:
                await progress_message_obj.edit_text("⚠️ Object tracking complete, but GitHub Pages update failed. Check bot logs.")
            set_processing_status("⚠️ Object tracking complete, but GitHub Pages update failed.") # Update global status
            logger.error("GitHub Pages update failed.")
            reset_status_after_delay() # Reset status after failure
            return False
    else:
        if progress_message_obj:
            await progress_message_obj.edit_text(f"🎉 Object tracking complete! Output saved locally: {local_output_path}")
        set_processing_status(f"🎉 Object tracking complete! Output saved locally: {local_output_path}") # Update global status
        logger.info(f"Object tracking complete. Output: {local_output_path}")
        reset_status_after_delay() # Reset status after success
        return True
    
    # Optional: Clean up local processed video file after upload/commit
    # if os.path.exists(local_output_path):
    #     try:
    #         os.remove(local_output_path)
    #         logger.info(f"Cleaned up local processed video: {local_output_path}")
    #     except OSError as e:
    #         logger.warning(f"Error deleting local processed video file '{local_output_path}': {e}")


# --- Telegram Command Handlers ---
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /start command."""
    await update.message.reply_text(
        "👋 Welcome to the Video Tracking Master Bot!\n\n"
        "I can process videos for object tracking. "
        "To get started, simply send me a video link using the /track command."
    )

async def track_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /track command to initiate video processing."""
    if len(context.args) == 1:
        video_url = context.args[0]
        initial_message = await update.message.reply_text(f"🔗 Received your video link: `{video_url}`\n\n"
                                        "🚀 Starting the download process now. Please wait...",
                                        parse_mode='Markdown')
        # For Telegram requests, client_ip and geolocation_info are not directly available here
        # or relevant for the web-based tracker, so we pass defaults.
        await process_video_unified(video_url, False, initial_message, context, client_ip="Telegram User", geolocation_info={})
    else:
        await update.message.reply_text(
            "❌ Invalid usage. Please provide a video link.\n"
            "Example: `/track https://example.com/your_video.mp4`\n\n"
            "Need help? Use the /help command.",
            parse_mode='Markdown'
        )

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles the /help command."""
    help_text = (
        "💡 <b>Here's how to use me:</b>\n\n"
        "➡️ <code>/track &lt;video_url&gt;</code>: <b>Provide a direct link to a video file.</b>\n"
        "I will download it, perform object tracking, and then provide you with a download link to the processed video.\n\n"
        "<b>For example:</b>\n"
        "<code>/track https://videos.pexels.com/video-files/example.mp4</code>\n\n"
        "Please ensure the video link is publicly accessible."
    )
    await update.message.reply_text(
        help_text,
        parse_mode='HTML'
    )

async def unknown_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles unknown commands."""
    await update.message.reply_text(
        "🤔 Sorry, I don't understand that command.\n"
        "Please use /help to see the available commands."
    )

async def handle_non_command_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handles any text messages that are not commands."""
    await update.message.reply_text(
        "👋 Hi there! I'm a bot designed to track objects in videos.\n"
        "To see what I can do, please use the /help command."
    )


# --- Local Web Server ---

class LocalAPIHandler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, format, *args):
        logger.debug(f"Web Server: {format % args}")

    def log_request(self, code='-', size='-'):
        """
        Log an arbitrary request, but filter out frequent /status checks
        and simplify the log message.
        """
        request_path = urlparse(self.path).path

        # Filter out high-frequency health/status/event and polling endpoints to reduce log verbosity.
        if request_path in (
            '/status',
            '/events/status',
            '/events/admin_tracker_data',
            '/events/admin_auth',
            '/events/admin_uptime_data',
            '/admin_tracker_data',
            '/admin_uptime_data',
            '/admin_tracker_land',
        ) and (self.command == 'GET' or self.command == 'HEAD' or self.command == 'POST'):
            return

        # Chunk uploads are high-frequency; suppress per-chunk request lines to avoid log spam.
        if request_path == '/upload_chunk' and self.command == 'POST':
            return

        # Log other requests with a simplified format
        logger.info(f"Incoming Request: {self.command} {self.path}")

    def handle_one_request(self):
        """Handle a single HTTP request.
        This is overridden to add the general request logging.
        """
        try:
            self.raw_requestline = self.rfile.readline(65537)
            if not self.raw_requestline:
                self.close_connection = True
                return
            if not self.parse_request():
                # An error code has been sent, just exit
                return
            
            mname = 'do_' + self.command
            if not hasattr(self, mname):
                self.send_error(
                    501, "Unsupported method (%r)" % self.command)
                return
            method = getattr(self, mname)
            method()
            self.wfile.flush() #actually send the response if not already done.
        except socket.timeout as e:
            self.log_error("Request timed out: %r", e)
            self.close_connection = True
            return
        except Exception as e:
            self.log_error("Error handling request: %r", e)
            self.close_connection = True
            return

    def _set_cors_headers(self):
        self.send_header('Access-Control-Allow-Origin', '*')
        self.send_header('Access-Control-Allow-Methods', 'POST, GET, OPTIONS, HEAD') # Explicitly allow HEAD
        self.send_header('Access-Control-Allow-Headers', 'Content-Type, X-Forwarded-For, Authorization, X-Client-Id') # Added Authorization and X-Client-Id headers
        self.send_header('Access-Control-Max-Age', '86400') # Cache preflight for 24 hours

    def do_OPTIONS(self):
        self.send_response(200)
        self._set_cors_headers()
        self.send_header('Content-Length', '0') # No content for OPTIONS
        self.end_headers()
        logger.info("Handled OPTIONS preflight request.")

    # Renamed _send_response to send_api_response to avoid conflict and be more explicit
    def send_api_response(self, status_code, data):
        """Sends a JSON response with appropriate headers."""
        try:
            self.send_response(status_code)
            self.send_header('Content-type', 'application/json')
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self._set_cors_headers() # Set CORS headers for all responses
            self.end_headers()
            self.wfile.write(json.dumps(data).encode('utf-8'))
        except BrokenPipeError:
            logger.warning("Client disconnected before response could be sent (broken pipe)")
        except ConnectionResetError:
            logger.warning("Client connection reset before response could be sent")
        except Exception as e:
            logger.warning(f"Error sending response: {e}")

    def do_HEAD(self):
        """Handle HEAD requests for status check."""
        request_path = urlparse(self.path).path
        if request_path == '/status':
            self.send_response(200)
            self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
            self.send_header('Pragma', 'no-cache')
            self.send_header('Expires', '0')
            self._set_cors_headers()
            self.end_headers()
            logger.debug("Handled HEAD request for /status.")
        else:
            # Fallback for other HEAD requests, might return 404 or just headers
            super().do_HEAD() # Call the base class method

    def _send_sse_event(self, event_name: str, data: dict):
        """Sends one SSE event to the connected client."""
        event_payload = json.dumps(data, ensure_ascii=False)
        self.wfile.write(f"event: {event_name}\n".encode('utf-8'))
        self.wfile.write(f"data: {event_payload}\n\n".encode('utf-8'))
        self.wfile.flush()

    def _get_client_id(self) -> str:
        header_value = self.headers.get('X-Client-Id', '')
        query_params = parse_qs(urlparse(self.path).query)
        query_value = query_params.get('client_id', [''])[0]
        resolved = _sanitize_client_id(header_value or query_value)
        if resolved:
            return resolved

        # Reject weak identity fallbacks (IP/User-Agent) because they can collide across users.
        # A missing client id means owner-based cancel auth cannot be trusted for non-admins.
        return ""

    def _decode_optional_admin_payload(self) -> dict | None:
        token = self._get_auth_token()
        if not token:
            return None
        payload = self._decode_jwt(token)
        if not payload:
            return None
        username = payload.get('username')
        if username not in ADMIN_CREDENTIALS:
            return None
        return payload

    def _get_request_actor(self) -> dict:
        admin_payload = self._decode_optional_admin_payload()
        username = admin_payload.get('username') if admin_payload else ''
        return {
            "clientId": self._get_client_id(),
            "isAdmin": bool(admin_payload),
            "username": username or "",
        }

    def _stream_status_events(self):
        """Streams realtime status updates using Server-Sent Events."""
        self.send_response(200)
        self.send_header('Content-type', 'text/event-stream')
        self.send_header('Cache-Control', 'no-cache, no-transform')
        self.send_header('Connection', 'keep-alive')
        self._set_cors_headers()
        self.end_headers()

        logger.debug("SSE status stream connected")

        requester = self._get_request_actor()

        last_seen_counter = -1
        last_heartbeat = time.time()

        try:
            while True:
                payload = get_status_payload(requester)
                current_counter = payload.get("statusCounter", -1)

                if current_counter != last_seen_counter:
                    self._send_sse_event("status", payload)
                    last_seen_counter = current_counter

                now = time.time()
                if now - last_heartbeat >= 20:
                    self._send_sse_event("heartbeat", {"ts": int(now)})
                    last_heartbeat = now

                time.sleep(0.5)
        except (BrokenPipeError, ConnectionResetError):
            logger.debug("SSE status stream disconnected")
        except Exception as e:
            logger.warning(f"SSE stream error: {e}")

    def _stream_admin_tracker_events(self, admin_username: str):
        """Streams realtime admin tracker updates using Server-Sent Events."""
        self.send_response(200)
        self.send_header('Content-type', 'text/event-stream')
        self.send_header('Cache-Control', 'no-cache, no-transform')
        self.send_header('Connection', 'keep-alive')
        self._set_cors_headers()
        self.end_headers()

        logger.debug(f"SSE admin tracker stream connected for admin: {admin_username}")

        last_signature = None
        last_heartbeat = time.time()

        try:
            while True:
                with _tracking_data_lock:
                    tracking_data_snapshot = json.loads(json.dumps(_tracking_data, ensure_ascii=False))

                payload = {"trackingData": tracking_data_snapshot}
                current_signature = json.dumps(payload, ensure_ascii=False, sort_keys=True)

                if current_signature != last_signature:
                    self._send_sse_event("trackingData", payload)
                    last_signature = current_signature

                now = time.time()
                if now - last_heartbeat >= 20:
                    self._send_sse_event("heartbeat", {"ts": int(now)})
                    last_heartbeat = now

                time.sleep(0.75)
        except (BrokenPipeError, ConnectionResetError):
            logger.debug(f"SSE admin tracker stream disconnected for admin: {admin_username}")
        except Exception as e:
            logger.warning(f"SSE admin tracker stream error for {admin_username}: {e}")

    def _stream_admin_uptime_events(self, admin_username: str):
        """Streams realtime admin uptime updates using Server-Sent Events."""
        self.send_response(200)
        self.send_header('Content-type', 'text/event-stream')
        self.send_header('Cache-Control', 'no-cache, no-transform')
        self.send_header('Connection', 'keep-alive')
        self._set_cors_headers()
        self.end_headers()

        logger.debug(f"SSE admin uptime stream connected for admin: {admin_username}")

        last_signature = None
        last_heartbeat = time.time()

        try:
            while True:
                payload = get_uptime_payload()
                uptime_data = payload.get("uptimeData", {}) if isinstance(payload, dict) else {}
                events = uptime_data.get("events", []) if isinstance(uptime_data, dict) else []
                sessions = uptime_data.get("sessions", []) if isinstance(uptime_data, dict) else []
                last_event = events[-1] if isinstance(events, list) and events else {}
                last_session = sessions[-1] if isinstance(sessions, list) and sessions else {}
                signature_payload = {
                    "currentStatus": uptime_data.get("currentStatus", ""),
                    "eventCount": len(events) if isinstance(events, list) else 0,
                    "sessionCount": len(sessions) if isinstance(sessions, list) else 0,
                    "lastEventTs": last_event.get("ts", 0) if isinstance(last_event, dict) else 0,
                    "lastEventStatus": last_event.get("status", "") if isinstance(last_event, dict) else "",
                    "lastSessionStart": last_session.get("startTs", 0) if isinstance(last_session, dict) else 0,
                    "lastSessionEnd": last_session.get("endTs", None) if isinstance(last_session, dict) else None,
                }
                current_signature = json.dumps(signature_payload, ensure_ascii=False, sort_keys=True)

                if current_signature != last_signature:
                    self._send_sse_event("uptimeData", payload)
                    last_signature = current_signature

                now = time.time()
                if now - last_heartbeat >= 20:
                    self._send_sse_event("heartbeat", {"ts": int(now)})
                    last_heartbeat = now

                time.sleep(0.75)
        except (BrokenPipeError, ConnectionResetError):
            logger.debug(f"SSE admin uptime stream disconnected for admin: {admin_username}")
        except Exception as e:
            logger.warning(f"SSE admin uptime stream error for {admin_username}: {e}")

    def _stream_admin_auth_events(self):
        """Streams realtime auth validation events for admin clients."""
        self.send_response(200)
        self.send_header('Content-type', 'text/event-stream')
        self.send_header('Cache-Control', 'no-cache, no-transform')
        self.send_header('Connection', 'keep-alive')
        self._set_cors_headers()
        self.end_headers()

        token = self._get_auth_token()
        if not token:
            self._send_sse_event("authRevoked", {"reason": "missing_token"})
            return

        initial_payload = self._decode_jwt(token)
        if not initial_payload or initial_payload.get('username') not in ADMIN_CREDENTIALS:
            self._send_sse_event("authRevoked", {"reason": "invalid_or_expired_token"})
            return

        admin_username = initial_payload.get('username', 'unknown')
        logger.debug(f"SSE admin auth stream connected for admin: {admin_username}")

        last_heartbeat = time.time()

        try:
            while True:
                active_payload = self._decode_jwt(token)
                if not active_payload or active_payload.get('username') not in ADMIN_CREDENTIALS:
                    self._send_sse_event("authRevoked", {"reason": "session_invalidated"})
                    logger.info(f"SSE admin auth revoked for admin: {admin_username}")
                    break

                now = time.time()
                if now - last_heartbeat >= 15:
                    self._send_sse_event("authHeartbeat", {"ts": int(now)})
                    last_heartbeat = now

                time.sleep(1.0)
        except (BrokenPipeError, ConnectionResetError):
            logger.debug(f"SSE admin auth stream disconnected for admin: {admin_username}")
        except Exception as e:
            logger.warning(f"SSE admin auth stream error for {admin_username}: {e}")

    def _get_auth_token(self):
        """Extracts JWT from Authorization header or SSE query string token."""
        auth_header = self.headers.get('Authorization')
        if auth_header and auth_header.startswith('Bearer '):
            return auth_header.split(' ')[1]

        query_params = parse_qs(urlparse(self.path).query)
        token_from_query = query_params.get('token', [None])[0]
        if token_from_query:
            return token_from_query

        return None

    def _decode_jwt(self, token: str) -> dict | None:
        """Decodes and validates a JWT."""
        with _token_invalidation_lock:
            if token in _invalidated_tokens:
                logger.warning(f"Attempted to use invalidated token: {token[:10]}...")
                return None
        try:
            # Verify the token with the secret key
            decoded_token = jwt.decode(token, JWT_SECRET_KEY, algorithms=["HS256"])
            # Check for expiry if enabled
            if SESSION_TIMEOUT_ENABLED and decoded_token.get('exp'):
                if datetime.datetime.fromtimestamp(decoded_token['exp']) < datetime.datetime.now():
                    logger.warning(f"Expired token used for user: {decoded_token.get('username')}")
                    invalidate_token(token) # Add to blacklist immediately
                    return None
            return decoded_token
        except jwt.ExpiredSignatureError:
            logger.warning("Expired JWT.")
            invalidate_token(token) # Add to blacklist
            return None
        except jwt.InvalidTokenError as e:
            logger.error(f"Invalid JWT: {e}")
            return None
        except Exception as e:
            logger.error(f"Unexpected error decoding JWT: {e}")
            return None

    def _authenticate_request(self) -> dict | None:
        """
        Authenticates a request by checking for a valid JWT.
        Returns the decoded payload if valid, None otherwise.
        """
        token = self._get_auth_token()
        if not token:
            # Use self.send_api_response for consistency
            self.send_api_response(401, {"message": "Authorization token missing."})
            return None
        
        payload = self._decode_jwt(token)
        if not payload:
            # Use self.send_api_response for consistency
            self.send_api_response(401, {"message": "Invalid or expired token."})
            return None
        
        # Optionally, check if the username exists in ADMIN_CREDENTIALS for extra security
        if payload.get('username') not in ADMIN_CREDENTIALS:
            logger.warning(f"Attempted login with non-existent username in token: {payload.get('username')}")
            # Use self.send_api_response for consistency
            self.send_api_response(401, {"message": "Invalid token (user not found)."})
            return None

        return payload

    def _authenticate_sse_request(self) -> dict | None:
        """
        Authenticates SSE requests using the same JWT validation path,
        returning None and sending 401 headers when invalid.
        """
        token = self._get_auth_token()
        if not token:
            self.send_response(401)
            self._set_cors_headers()
            self.end_headers()
            return None

        payload = self._decode_jwt(token)
        if not payload:
            self.send_response(401)
            self._set_cors_headers()
            self.end_headers()
            return None

        if payload.get('username') not in ADMIN_CREDENTIALS:
            logger.warning(f"Attempted SSE access with non-existent username in token: {payload.get('username')}")
            self.send_response(401)
            self._set_cors_headers()
            self.end_headers()
            return None

        return payload

    def _authorize_master_admin(self, admin_payload: dict) -> bool:
        """Checks if the authenticated admin is a master admin."""
        if admin_payload.get('username') not in MASTER_ADMIN_USERNAMES:
            self.send_api_response(403, {"message": "Forbidden: Only a master admin can perform this action."})
            logger.warning(f"Unauthorized master admin action attempt by '{admin_payload.get('username')}'")
            return False
        return True


    def do_POST(self):
        global _ADS_ENABLED_GLOBALLY, _SHOW_ADS_TO_ADMINS

        if self.path == '/admin_uptime_reconcile':
            admin_payload = self._authenticate_request()
            if not admin_payload:
                return

            try:
                content_length = int(self.headers.get('Content-Length', 0))
                post_body = self.rfile.read(content_length) if content_length > 0 else b'{}'
                payload = json.loads(post_body.decode('utf-8') or '{}')
            except json.JSONDecodeError:
                self.send_api_response(400, {"message": "Invalid JSON payload."})
                return

            raw_segments = payload.get('segments', [])
            if not isinstance(raw_segments, list):
                self.send_api_response(400, {"message": "'segments' must be an array."})
                return

            now_ts = float(time.time())
            appended_events = 0
            accepted_segments = 0

            with _uptime_data_lock:
                for item in raw_segments[:300]:
                    if not isinstance(item, dict):
                        continue
                    try:
                        off_ts = float(item.get('offTs', 0) or 0)
                        on_ts = float(item.get('onTs', 0) or 0)
                    except Exception:
                        continue

                    if off_ts <= 0 or on_ts <= 0 or on_ts <= off_ts:
                        continue

                    # Reject extreme clock skew / unrealistic segments.
                    if on_ts > now_ts + 120:
                        continue
                    if (on_ts - off_ts) > (90 * 24 * 3600):
                        continue

                    accepted_segments += 1
                    if _append_uptime_event_if_missing_locked(
                        status='off',
                        reason='frontend_sse_disconnect',
                        event_ts=off_ts,
                    ):
                        appended_events += 1
                    if _append_uptime_event_if_missing_locked(
                        status='on',
                        reason='frontend_sse_reconnect',
                        event_ts=on_ts,
                    ):
                        appended_events += 1

                if appended_events > 0:
                    _repair_uptime_data_locked(now_ts=now_ts)
                    _save_uptime_data_locked()
                uptime_snapshot = _safe_uptime_snapshot_locked()

            self.send_api_response(200, {
                "ok": True,
                "acceptedSegments": accepted_segments,
                "appendedEvents": appended_events,
                "uptimeData": uptime_snapshot,
            })
            return

        if self.path == '/admin_tracker_land':
            admin_payload = self._authenticate_request()
            if not admin_payload:
                return
            try:
                content_length = int(self.headers.get('Content-Length', 0))
                post_body = self.rfile.read(content_length) if content_length > 0 else b'{}'
                payload = json.loads(post_body.decode('utf-8') or '{}')
            except json.JSONDecodeError:
                self.send_api_response(400, {"message": "Invalid JSON payload."})
                return

            session_id = str(payload.get('sessionId', '')).strip()
            if not session_id:
                self.send_api_response(400, {"message": "sessionId is required."})
                return

            source_ip = self.client_address[0] if self.client_address else 'unknown-ip'
            _record_admin_tracker_landing_once(
                session_id=session_id,
                admin_username=admin_payload.get('username', 'unknown'),
                source_ip=source_ip,
            )
            self.send_api_response(200, {"ok": True})
            return

        if self.path == '/upload_chunk':
            try:
                ctype, pdict = cgi.parse_header(self.headers.get('content-type', ''))
                if ctype != 'multipart/form-data' or 'boundary' not in pdict:
                    self.send_api_response(400, {"success": False, "message": "Expected multipart/form-data payload."})
                    return

                pdict['boundary'] = bytes(pdict['boundary'], "utf-8")
                form = cgi.FieldStorage(
                    fp=self.rfile,
                    headers=self.headers,
                    environ={
                        'REQUEST_METHOD': 'POST',
                        'CONTENT_TYPE': self.headers['Content-Type'],
                        'CONTENT_LENGTH': str(self.headers['Content-Length'])
                    }
                )

                upload_id = sanitize_chunk_upload_id(form['upload_id'].value if 'upload_id' in form else '')
                if not upload_id:
                    self.send_api_response(400, {"success": False, "message": "Invalid or missing upload_id."})
                    return

                if 'chunk' not in form or getattr(form['chunk'], 'file', None) is None:
                    self.send_api_response(400, {"success": False, "message": "Missing chunk file payload."})
                    return

                try:
                    chunk_index = int(form['chunk_index'].value)
                    total_chunks = int(form['total_chunks'].value)
                except Exception:
                    self.send_api_response(400, {"success": False, "message": "Invalid chunk index metadata."})
                    return

                if chunk_index < 0 or total_chunks <= 0 or chunk_index >= total_chunks:
                    self.send_api_response(400, {"success": False, "message": "Chunk index out of bounds."})
                    return

                raw_filename = form['original_filename'].value if 'original_filename' in form else ''
                original_filename = sanitize_filename_value(raw_filename, fallback_prefix="chunk_upload")

                upload_dir = os.path.join(CHUNK_UPLOAD_SUBDIRECTORY, upload_id)
                os.makedirs(upload_dir, exist_ok=True)

                chunk_path = os.path.join(upload_dir, f"chunk_{chunk_index:06d}.part")
                chunk_field = form['chunk']
                if hasattr(chunk_field.file, 'seek'):
                    chunk_field.file.seek(0)
                with open(chunk_path, 'wb') as chunk_out:
                    shutil.copyfileobj(chunk_field.file, chunk_out)

                metadata_path = os.path.join(upload_dir, 'metadata.json')
                metadata = {
                    "upload_id": upload_id,
                    "original_filename": original_filename,
                    "total_chunks": total_chunks,
                    "updated_at": time.time()
                }
                with open(metadata_path, 'w', encoding='utf-8') as metadata_file:
                    json.dump(metadata, metadata_file)

                received_chunks = len([name for name in os.listdir(upload_dir) if name.startswith('chunk_') and name.endswith('.part')])
                percent = int((received_chunks / max(total_chunks, 1)) * 100)
                set_processing_status(f"Uploading: chunks {received_chunks}/{total_chunks} ({percent}%)")
                self.send_api_response(200, {
                    "success": True,
                    "upload_id": upload_id,
                    "chunk_index": chunk_index,
                    "total_chunks": total_chunks,
                    "received_chunks": received_chunks
                })
            except Exception as e:
                logger.error(f"Error handling chunk upload: {e}", exc_info=True)
                self.send_api_response(500, {"success": False, "message": f"Chunk upload failed: {e}"})
            return

        if self.path == '/complete_chunked_upload':
            try:
                with _benchmark_lock:
                    if _benchmark_in_progress:
                        self.send_api_response(429, {
                            "message": "📊 Running quality benchmark (VMAF/SSIM/PSNR)... New uploads blocked until complete.",
                            "benchmarkInProgress": True
                        })
                        return

                content_length = int(self.headers.get('Content-Length', 0))
                raw_body = self.rfile.read(content_length) if content_length > 0 else b'{}'
                payload = json.loads(raw_body.decode('utf-8') or '{}')

                upload_id = sanitize_chunk_upload_id(payload.get('upload_id', ''))
                if not upload_id:
                    self.send_api_response(400, {"success": False, "message": "Invalid or missing upload_id."})
                    return

                upload_dir = os.path.join(CHUNK_UPLOAD_SUBDIRECTORY, upload_id)
                metadata_path = os.path.join(upload_dir, 'metadata.json')
                if not os.path.isdir(upload_dir) or not os.path.exists(metadata_path):
                    self.send_api_response(404, {"success": False, "message": "Upload session not found or expired."})
                    return

                with open(metadata_path, 'r', encoding='utf-8') as metadata_file:
                    metadata = json.load(metadata_file)

                total_chunks = int(metadata.get('total_chunks', 0))
                if total_chunks <= 0:
                    self.send_api_response(400, {"success": False, "message": "Invalid upload metadata."})
                    return

                missing_chunks = []
                for i in range(total_chunks):
                    if not os.path.exists(os.path.join(upload_dir, f"chunk_{i:06d}.part")):
                        missing_chunks.append(i)
                if missing_chunks:
                    self.send_api_response(400, {
                        "success": False,
                        "message": f"Upload incomplete: missing {len(missing_chunks)} chunk(s).",
                        "missingChunks": missing_chunks[:10]
                    })
                    return

                original_filename = sanitize_filename_value(metadata.get('original_filename', ''), fallback_prefix="chunk_upload")
                assembled_input_path = os.path.join(INPUT_SUBDIRECTORY, original_filename)
                assembled_input_dir = os.path.dirname(assembled_input_path) or INPUT_SUBDIRECTORY
                os.makedirs(assembled_input_dir, exist_ok=True)
                if os.path.exists(assembled_input_path):
                    stem, ext = os.path.splitext(original_filename)
                    assembled_input_path = os.path.join(INPUT_SUBDIRECTORY, f"{stem}_{int(time.time())}{ext or '.mp4'}")

                with open(assembled_input_path, 'wb') as assembled_file:
                    for i in range(total_chunks):
                        chunk_path = os.path.join(upload_dir, f"chunk_{i:06d}.part")
                        with open(chunk_path, 'rb') as chunk_file:
                            shutil.copyfileobj(chunk_file, assembled_file)

                try:
                    shutil.rmtree(upload_dir)
                except Exception as cleanup_error:
                    logger.warning(f"Could not clean chunk upload dir {upload_dir}: {cleanup_error}")

                client_ip = get_client_ip(self)
                geolocation_info = get_geolocation_data(client_ip)
                requester = self._get_request_actor()

                if not requester.get("isAdmin") and not requester.get("clientId"):
                    self.send_api_response(400, {
                        "success": False,
                        "message": "Missing client identity. Refresh the page and retry.",
                    })
                    return

                roi_params = None
                if str(payload.get('roi_enabled', '')).lower() == 'true':
                    roi_params = {
                        'roi_enabled': 'true',
                        'roi_x': str(payload.get('roi_x', '0')),
                        'roi_y': str(payload.get('roi_y', '0')),
                        'roi_width': str(payload.get('roi_width', '1')),
                        'roi_height': str(payload.get('roi_height', '1')),
                        'roi_show_overlay': 'false',
                        'roi_overlay_opacity': '0'
                    }

                allowed_classes = None
                allowed_classes_raw = payload.get('allowed_classes')
                if isinstance(allowed_classes_raw, list):
                    allowed_classes = [str(item).strip() for item in allowed_classes_raw if str(item).strip()]
                elif isinstance(allowed_classes_raw, str) and allowed_classes_raw.strip():
                    allowed_classes = [c.strip() for c in allowed_classes_raw.split(',') if c.strip()]

                confidence_threshold = None
                if payload.get('confidence_threshold') is not None:
                    try:
                        conf_val = float(payload.get('confidence_threshold'))
                        if 0.0 < conf_val < 1.0:
                            confidence_threshold = conf_val
                    except (ValueError, TypeError):
                        pass

                class WebProgressReporter:
                    async def edit_text(self, message):
                        set_processing_status(message)

                main_loop = self.server.main_asyncio_loop
                job_id, _, schedule_error = _schedule_processing_job(
                    main_loop,
                    process_video_unified(
                        assembled_input_path,
                        is_file_upload=True,
                        progress_message_obj=WebProgressReporter(),
                        telegram_context=None,
                        client_ip=client_ip,
                        geolocation_info=geolocation_info,
                        roi_params=roi_params,
                        original_filename=os.path.basename(assembled_input_path),
                        allowed_classes=allowed_classes,
                        confidence_threshold=confidence_threshold
                    ),
                    "complete_chunked_upload",
                    owner_client_id=requester.get("clientId", ""),
                    owner_username=requester.get("username", ""),
                    owner_is_admin=requester.get("isAdmin", False),
                )

                if schedule_error:
                    active_job_snapshot = _snapshot_active_processing_job()
                    if os.path.exists(assembled_input_path):
                        try:
                            os.remove(assembled_input_path)
                        except OSError:
                            pass
                    self.send_api_response(409, {
                        "success": False,
                        "message": schedule_error,
                        "processingActive": True,
                        "activeProcessingJobId": active_job_snapshot.get("jobId", "")
                    })
                    return

                self.send_api_response(200, {
                    "success": True,
                    "message": "Chunked upload assembled and processing initiated.",
                    "jobId": job_id
                })
            except json.JSONDecodeError:
                self.send_api_response(400, {"success": False, "message": "Invalid JSON payload."})
            except Exception as e:
                logger.error(f"Error finalizing chunked upload: {e}", exc_info=True)
                self.send_api_response(500, {"success": False, "message": f"Failed to finalize chunked upload: {e}"})
            return

        if self.path == '/process_web_video':
            try:
                with _benchmark_lock:
                    if _benchmark_in_progress:
                        self.send_api_response(429, {
                            "message": "📊 Running quality benchmark (VMAF/SSIM/PSNR)... New uploads blocked until complete.",
                            "benchmarkInProgress": True
                        })
                        return

                # Get client IP and geolocation data immediately
                client_ip = get_client_ip(self)
                geolocation_info = get_geolocation_data(client_ip)
                requester = self._get_request_actor()

                if not requester.get("isAdmin") and not requester.get("clientId"):
                    self.send_api_response(400, {
                        "message": "Missing client identity. Refresh the page and retry."
                    })
                    return

                logger.info(f"Request from IP: {client_ip}, Geo: {geolocation_info}")

                ctype, pdict = cgi.parse_header(self.headers.get('content-type'))
                pdict['boundary'] = bytes(pdict['boundary'], "utf-8")
                
                form = cgi.FieldStorage(
                    fp=self.rfile,
                    headers=self.headers,
                    environ={'REQUEST_METHOD': 'POST',
                             'CONTENT_TYPE': self.headers['Content-Type'],
                             'CONTENT_LENGTH': str(self.headers['Content-Length'])
                            }
                )
                
                video_url = None
                video_file = None
                preview_session_id = None
                cached_video_path = None
                cached_original_filename = None  # Store original filename from preview session

                # Check for preview session first (video already downloaded/uploaded)
                if 'preview_session_id' in form:
                    preview_session_id = form['preview_session_id'].value
                    session = get_preview_session(preview_session_id)
                    if session and os.path.exists(session['video_path']):
                        cached_video_path = session['video_path']
                        cached_original_filename = session.get('original_filename')  # Get original filename
                        mark_preview_session_used(preview_session_id)
                        logger.info(f"Using cached preview video: {cached_video_path} (original: {cached_original_filename})")
                    else:
                        logger.warning(f"Preview session {preview_session_id} not found or expired, falling back to regular upload/url")

                # Only require video_url or video_file if we don't have a cached video from preview session.
                # Prefer file when both fields are present (many forms always send an empty video_url).
                if not cached_video_path:
                    if 'video_file' in form:
                        video_file = form['video_file']
                        if getattr(video_file, 'file', None) is not None:
                            logger.info(f"Received uploaded file from web: {getattr(video_file, 'filename', '') or '<unnamed upload>'}")
                        else:
                            video_file = None

                    if video_file is None and 'video_url' in form:
                        video_url = (form['video_url'].value or "").strip()
                        if video_url:
                            logger.info(f"Received video URL from web: {video_url}")

                    if video_file is None and not video_url:
                        self.send_api_response(400, {"message": "No video URL or file provided."})
                        return
                else:
                    # For cached videos, check if fallback URL/file is provided (optional)
                    if 'video_url' in form:
                        video_url = form['video_url'].value
                        logger.info(f"Received fallback video URL (not used, using cached): {video_url}")
                    elif 'video_file' in form:
                        video_file = form['video_file']
                        logger.info(f"Received fallback video file (not used, using cached): {getattr(video_file, 'filename', 'unknown')}")

                # Extract ROI (Region of Interest) parameters from form data
                roi_params = None
                if 'roi_enabled' in form and form['roi_enabled'].value.lower() == 'true':
                    roi_params = {
                        'roi_enabled': 'true',
                        'roi_x': form['roi_x'].value if 'roi_x' in form else '0',
                        'roi_y': form['roi_y'].value if 'roi_y' in form else '0',
                        'roi_width': form['roi_width'].value if 'roi_width' in form else '1',
                        'roi_height': form['roi_height'].value if 'roi_height' in form else '1',
                        'roi_show_overlay': 'false',  # Disabled - no overlay in output
                        'roi_overlay_opacity': '0'
                    }
                    logger.info(f"ROI enabled: x={roi_params['roi_x']}, y={roi_params['roi_y']}, "
                               f"w={roi_params['roi_width']}, h={roi_params['roi_height']}")

                # Extract allowed_classes and confidence_threshold
                allowed_classes = None
                if 'allowed_classes' in form:
                    # Expecting comma-separated string e.g. "person,car,dog"
                    classes_str = form['allowed_classes'].value
                    if classes_str:
                         allowed_classes = [c.strip() for c in classes_str.split(',') if c.strip()]
                         logger.info(f"Custom allowed classes from web: {allowed_classes}")

                confidence_threshold = None
                if 'confidence_threshold' in form:
                    try:
                        conf_val = float(form['confidence_threshold'].value)
                        # Basic validation
                        if 0.0 < conf_val < 1.0:
                            confidence_threshold = conf_val
                            logger.info(f"Custom confidence threshold from web: {confidence_threshold}")
                    except ValueError:
                        logger.warning("Invalid confidence_threshold value provided.")

                class WebProgressReporter:
                    """A dummy reporter for web progress that updates the global status."""
                    async def edit_text(self, message):
                        set_processing_status(message) # Update the global status variable

                web_progress_reporter_instance = WebProgressReporter()

                main_loop = self.server.main_asyncio_loop
                
                # Determine the video source and whether it's a file upload
                is_file_upload = False
                video_source = None
                
                if cached_video_path:
                    # Use the cached video from preview session
                    # Create a file-like object for the cached video
                    video_source = cached_video_path
                    is_file_upload = True  # Treat cached file as a file upload
                    logger.info(f"Processing with cached video: {cached_video_path}")
                elif video_file is not None and getattr(video_file, 'file', None) is not None:
                    video_source = video_file
                    is_file_upload = True
                else:
                    video_source = video_url

                job_id, _, schedule_error = _schedule_processing_job(
                    main_loop,
                    process_video_unified(
                        video_source,
                        is_file_upload=is_file_upload,
                        progress_message_obj=web_progress_reporter_instance,
                        telegram_context=None,
                        client_ip=client_ip, # Pass client IP
                        geolocation_info=geolocation_info, # Pass geolocation info
                        roi_params=roi_params,  # Pass ROI parameters
                        original_filename=cached_original_filename,  # Pass original filename from preview session
                        allowed_classes=allowed_classes,
                        confidence_threshold=confidence_threshold
                    ),
                    "process_web_video",
                    owner_client_id=requester.get("clientId", ""),
                    owner_username=requester.get("username", ""),
                    owner_is_admin=requester.get("isAdmin", False),
                )

                if schedule_error:
                    active_job_snapshot = _snapshot_active_processing_job()
                    self.send_api_response(409, {
                        "message": schedule_error,
                        "processingActive": True,
                        "activeProcessingJobId": active_job_snapshot.get("jobId", "")
                    })
                    return

                self.send_api_response(200, {
                    "message": "Processing initiated. Check GitHub Pages for updates.",
                    "jobId": job_id
                })

            except Exception as e:
                logger.error(f"Error handling web video processing: {e}", exc_info=True)
                self.send_api_response(500, {"message": f"Server error: {e}"})
        
        elif self.path == '/get_video_preview':
            # Endpoint to get a preview frame for ROI selection
            # Works with both uploaded files and URLs
            try:
                ctype, pdict = cgi.parse_header(self.headers.get('content-type'))
                pdict['boundary'] = bytes(pdict['boundary'], "utf-8")
                
                form = cgi.FieldStorage(
                    fp=self.rfile,
                    headers=self.headers,
                    environ={'REQUEST_METHOD': 'POST',
                             'CONTENT_TYPE': self.headers['Content-Type'],
                             'CONTENT_LENGTH': str(self.headers['Content-Length'])
                            }
                )
                
                video_url = None
                video_file = None
                preview_session_id = None
                
                # Check if using an existing preview session
                if 'preview_session_id' in form:
                    preview_session_id = form['preview_session_id'].value
                    session = get_preview_session(preview_session_id)
                    if session and os.path.exists(session['video_path']):
                        # Session exists, extract frame from existing video
                        video_path = session['video_path']
                        frame_path = os.path.join(PREVIEW_SUBDIRECTORY, f"{preview_session_id}_frame.jpg")
                        
                        if extract_video_frame(video_path, frame_path):
                            with open(frame_path, 'rb') as f:
                                frame_data = base64.b64encode(f.read()).decode('utf-8')
                            # Clean up frame file
                            os.remove(frame_path)
                            
                            self.send_api_response(200, {
                                "success": True,
                                "preview_session_id": preview_session_id,
                                "frame": f"data:image/jpeg;base64,{frame_data}",
                                "message": "Preview frame extracted successfully"
                            })
                        else:
                            self.send_api_response(500, {"success": False, "message": "Failed to extract frame from video"})
                        return
                    else:
                        # Session expired or invalid, need new upload/download
                        pass
                
                # Handle new video upload or URL. Prefer file if both fields are present.
                if 'video_file' in form:
                    video_file = form['video_file']
                    if getattr(video_file, 'file', None) is not None:
                        logger.info(f"Preview request for uploaded file: {getattr(video_file, 'filename', '') or '<unnamed upload>'}")
                    else:
                        video_file = None

                if video_file is None and 'video_url' in form:
                    video_url = (form['video_url'].value or "").strip()
                    if video_url:
                        logger.info(f"Preview request for URL: {video_url}")

                if not video_file and not video_url:
                    self.send_api_response(400, {"success": False, "message": "No video URL or file provided."})
                    return
                
                # Generate a new session ID
                new_session_id = str(uuid.uuid4())
                video_title = None  # Will store the video title from yt-dlp (only for URLs)
                
                if video_file is not None and getattr(video_file, 'file', None) is not None:
                    # Handle file upload
                    input_filename = resolve_uploaded_filename(video_file, fallback_prefix="preview_upload")
                    # Use session ID in filename to make it unique
                    safe_filename = f"{new_session_id}_{input_filename}"
                    local_video_path = os.path.join(PREVIEW_SUBDIRECTORY, safe_filename)
                    
                    try:
                        if hasattr(video_file.file, "seek"):
                            video_file.file.seek(0)
                        with open(local_video_path, 'wb') as f:
                            f.write(video_file.file.read())
                        logger.info(f"Preview file saved to: {local_video_path}")
                    except Exception as e:
                        logger.error(f"Error saving preview file: {e}")
                        self.send_api_response(500, {"success": False, "message": f"Failed to save uploaded file: {e}"})
                        return
                else:
                    # Handle URL - download video using yt-dlp
                    local_video_path = os.path.join(PREVIEW_SUBDIRECTORY, f"{new_session_id}_downloaded")
                    
                    try:
                        # First, try to get the video title using yt-dlp (for better filename)
                        title_cmd = [
                            "yt-dlp",
                            "--no-playlist",
                            "--print", "title",
                            "--no-warnings",
                            video_url
                        ]
                        title_result = subprocess.run(title_cmd, capture_output=True, text=True, timeout=30)
                        if title_result.returncode == 0 and title_result.stdout.strip():
                            video_title = title_result.stdout.strip()
                            # Sanitize the title for use as filename
                            video_title = re.sub(r'[\\/:*?"<>|]', '_', video_title)
                            video_title = video_title[:100]  # Limit length
                            logger.info(f"Got video title from yt-dlp: {video_title}")
                        
                        # Use yt-dlp to download the video
                        # Use 'bestvideo+bestaudio/best' and let yt-dlp merge to mp4
                        download_cmd = [
                            "yt-dlp",
                            "--no-playlist",
                            "-f", "bestvideo[ext=mp4]+bestaudio[ext=m4a]/bestvideo+bestaudio/best",
                            "--merge-output-format", "mp4",  # Ensure output is mp4
                            "-o", f"{local_video_path}.%(ext)s",
                            "--no-warnings",
                            video_url
                        ]
                        
                        logger.info(f"Downloading video for preview: {' '.join(download_cmd)}")
                        result = subprocess.run(download_cmd, capture_output=True, text=True, timeout=300)  # Increased timeout for larger videos
                        
                        if result.returncode != 0:
                            logger.error(f"yt-dlp failed: {result.stderr}")
                            self.send_api_response(400, {"success": False, "message": f"Failed to download video: {result.stderr[:200]}"})
                            return
                        
                        # Find the downloaded file (yt-dlp adds extension)
                        # Filter out .part and .ytdl files which are incomplete downloads
                        downloaded_files = [
                            f for f in os.listdir(PREVIEW_SUBDIRECTORY) 
                            if f.startswith(f"{new_session_id}_downloaded") 
                            and not f.endswith('.part') 
                            and not f.endswith('.ytdl')
                        ]
                        if not downloaded_files:
                            self.send_api_response(500, {"success": False, "message": "Downloaded video file not found. Download may have failed."})
                            return
                        
                        local_video_path = os.path.join(PREVIEW_SUBDIRECTORY, downloaded_files[0])
                        logger.info(f"Video downloaded for preview: {local_video_path}")
                        
                    except subprocess.TimeoutExpired:
                        self.send_api_response(408, {"success": False, "message": "Video download timed out. Try a shorter video."})
                        return
                    except Exception as e:
                        logger.error(f"Error downloading video: {e}")
                        self.send_api_response(500, {"success": False, "message": f"Failed to download video: {e}"})
                        return
                
                # Create preview session with original filename
                # Extract original filename based on source type
                original_fn = None
                if video_file is not None:
                    # File upload - preserve original name when present; fallback if multipart filename is missing.
                    original_fn = resolve_uploaded_filename(video_file, fallback_prefix="preview_upload")
                elif video_url:
                    # URL download - use video_title from yt-dlp if available, otherwise extract from URL
                    if video_title:
                        # Use the video title we got from yt-dlp (already sanitized)
                        original_fn = f"{video_title}.mp4"
                        logger.info(f"Using yt-dlp video title for filename: {original_fn}")
                    else:
                        # Fallback: extract filename from URL or use a sanitized version
                        from urllib.parse import urlparse, unquote, parse_qs
                        parsed_url = urlparse(video_url)
                        url_path = unquote(parsed_url.path)
                        url_filename = os.path.basename(url_path)
                        
                        # Try to extract YouTube video ID from various URL formats
                        youtube_video_id = None
                        hostname = parsed_url.netloc.lower()
                        
                        # Handle different YouTube URL formats:
                        # 1. youtube.com/watch?v=VIDEO_ID
                        # 2. youtu.be/VIDEO_ID
                        # 3. youtube.com/embed/VIDEO_ID
                        # 4. youtube.com/v/VIDEO_ID
                        # 5. youtube.com/shorts/VIDEO_ID
                        # 6. m.youtube.com/watch?v=VIDEO_ID
                        if 'youtube.com' in hostname or 'youtu.be' in hostname:
                            if 'youtu.be' in hostname:
                                # Short URL format: youtu.be/VIDEO_ID
                                youtube_video_id = url_path.strip('/')
                            elif '/watch' in url_path:
                                # Standard watch URL: youtube.com/watch?v=VIDEO_ID
                                query_params = parse_qs(parsed_url.query)
                                youtube_video_id = query_params.get('v', [None])[0]
                            elif '/embed/' in url_path or '/v/' in url_path:
                                # Embed URL: youtube.com/embed/VIDEO_ID or /v/VIDEO_ID
                                youtube_video_id = url_path.split('/')[-1]
                            elif '/shorts/' in url_path:
                                # Shorts URL: youtube.com/shorts/VIDEO_ID
                                youtube_video_id = url_path.split('/shorts/')[-1].split('?')[0]
                            
                            if youtube_video_id:
                                # Remove any query parameters from the video ID
                                youtube_video_id = youtube_video_id.split('?')[0].split('&')[0]
                                original_fn = f"youtube_{youtube_video_id}.mp4"
                                logger.info(f"Extracted YouTube video ID: {youtube_video_id}")
                        
                        # If not YouTube or couldn't extract ID, use generic fallback
                        if not original_fn:
                            if url_filename and '.' in url_filename:
                                original_fn = url_filename
                            else:
                                # Fallback: use the domain + timestamp as filename
                                original_fn = f"{parsed_url.netloc.replace('.', '_')}_{int(time.time())}.mp4"
                        logger.info(f"Extracted original filename from URL: {original_fn}")
                session_id = create_preview_session(local_video_path, original_fn)
                
                # Extract a frame from the video
                frame_path = os.path.join(PREVIEW_SUBDIRECTORY, f"{session_id}_frame.jpg")
                
                if extract_video_frame(local_video_path, frame_path):
                    with open(frame_path, 'rb') as f:
                        frame_data = base64.b64encode(f.read()).decode('utf-8')
                    # Clean up frame file (keep the video for later processing)
                    os.remove(frame_path)
                    
                    self.send_api_response(200, {
                        "success": True,
                        "preview_session_id": session_id,
                        "frame": f"data:image/jpeg;base64,{frame_data}",
                        "message": "Preview frame extracted successfully"
                    })
                else:
                    # Clean up failed preview
                    if os.path.exists(local_video_path):
                        os.remove(local_video_path)
                    remove_preview_session(session_id)
                    self.send_api_response(500, {"success": False, "message": "Failed to extract frame from video"})
                    
            except Exception as e:
                logger.error(f"Error handling video preview: {e}", exc_info=True)
                self.send_api_response(500, {"success": False, "message": f"Server error: {e}"})
        
        elif self.path == '/cancel_preview':
            # Endpoint to cancel a preview session and clean up the file
            try:
                content_length = int(self.headers['Content-Length'])
                post_body = self.rfile.read(content_length)
                data = json.loads(post_body.decode('utf-8'))
                session_id = data.get('preview_session_id')
                
                if not session_id:
                    self.send_api_response(400, {"success": False, "message": "preview_session_id is required"})
                    return
                
                session = get_preview_session(session_id)
                if session:
                    video_path = session['video_path']
                    if os.path.exists(video_path):
                        os.remove(video_path)
                        logger.info(f"Cancelled preview, deleted: {video_path}")
                    remove_preview_session(session_id)
                    self.send_api_response(200, {"success": True, "message": "Preview cancelled and cleaned up"})
                else:
                    self.send_api_response(404, {"success": False, "message": "Preview session not found"})
                    
            except Exception as e:
                logger.error(f"Error cancelling preview: {e}", exc_info=True)
                self.send_api_response(500, {"success": False, "message": f"Server error: {e}"})

        elif self.path == '/cancel_video_processing':
            # Cancels active processing and benchmark tasks while keeping server runtime alive.
            try:
                content_length = int(self.headers.get('Content-Length', 0))
                post_body = self.rfile.read(content_length) if content_length > 0 else b'{}'
                data = json.loads(post_body.decode('utf-8') or '{}')
                requested_job_id = (data.get('job_id') or "").strip() or None

                active_job_snapshot = _snapshot_active_processing_job()
                requester = self._get_request_actor()
                tracked_before = _snapshot_async_processes()
                logger.info(
                    f"Cancel requested by client. requested_job_id={requested_job_id}, "
                    f"active_job={active_job_snapshot.get('jobId')}, active={active_job_snapshot.get('isActive')}"
                )
                logger.debug(
                    "Tracked subprocesses before cancel: "
                    + ", ".join(
                        [f"{item.get('label')} pid={item.get('pid')}" for item in tracked_before]
                    ) if tracked_before else "Tracked subprocesses before cancel: <none>"
                )

                if active_job_snapshot.get("isActive") and not _can_requester_cancel_active_job(active_job_snapshot, requester):
                    logger.warning(
                        "Cancel denied: requester is not owner/admin. "
                        f"requester_client_id={requester.get('clientId')}, requester_admin={requester.get('isAdmin')}, "
                        f"owner_client_id={active_job_snapshot.get('ownerClientId')}, owner_admin={active_job_snapshot.get('ownerIsAdmin')}"
                    )
                    self.send_api_response(403, {
                        "success": False,
                        "message": "Only the job owner or an admin can cancel this processing job.",
                        "processingActive": True,
                        "activeProcessingJobId": active_job_snapshot.get("jobId", ""),
                        "canCancelActiveJob": False,
                    })
                    return

                emergency_kills = _emergency_kill_registered_processes_sync()

                processing_cancel = _cancel_processing_job(requested_job_id)

                benchmark_cancelled = _cancel_active_benchmark_task(self.server.main_asyncio_loop)

                terminated_subprocesses_sync = _terminate_registered_async_processes_sync()

                terminate_future = asyncio.run_coroutine_threadsafe(
                    _terminate_all_registered_async_processes(),
                    self.server.main_asyncio_loop
                )
                terminated_subprocesses_async = 0
                try:
                    terminated_subprocesses_async = int(terminate_future.result(timeout=4))
                except Exception as terminate_error:
                    logger.warning(f"Subprocess termination wait failed during cancel: {terminate_error}")
                terminated_subprocesses = max(terminated_subprocesses_sync, terminated_subprocesses_async)
                tracked_after = _snapshot_async_processes()
                fallback_family_kills = 0
                if tracked_after:
                    fallback_family_kills = _force_kill_registered_process_families_sync()
                    tracked_after = _snapshot_async_processes()
                logger.debug(
                    "Tracked subprocesses after cancel: "
                    + ", ".join(
                        [f"{item.get('label')} pid={item.get('pid')}" for item in tracked_after]
                    ) if tracked_after else "Tracked subprocesses after cancel: <none>"
                )
                if fallback_family_kills:
                    terminated_subprocesses = max(terminated_subprocesses, fallback_family_kills)
                if emergency_kills:
                    terminated_subprocesses = max(terminated_subprocesses, emergency_kills)

                summary_job_id = processing_cancel.get("jobId") or active_job_snapshot.get("jobId") or requested_job_id or "unknown"
                logger.info(
                    f"[AISC] CANCEL OK | job={summary_job_id} | stopped={terminated_subprocesses} | ready=1"
                )

                if not processing_cancel.get("ok") and not benchmark_cancelled:
                    self.send_api_response(404, {
                        "success": False,
                        "message": "No active processing or benchmark job found.",
                        "terminatedSubprocesses": terminated_subprocesses,
                    })
                    return

                self.send_api_response(200, {
                    "success": True,
                    "message": f"Processing cancelled for job {summary_job_id}. System is ready for the next video.",
                    "processing": processing_cancel,
                    "benchmarkCancelled": benchmark_cancelled,
                    "terminatedSubprocesses": terminated_subprocesses,
                })
            except json.JSONDecodeError:
                self.send_api_response(400, {"success": False, "message": "Invalid JSON payload."})
            except Exception as e:
                logger.error(f"Error cancelling active processing: {e}", exc_info=True)
                self.send_api_response(500, {"success": False, "message": f"Server error: {e}"})
        
        elif self.path == '/delete_video': # New endpoint for video deletion (protected)
            admin_payload = self._authenticate_request()
            if not admin_payload: return # _authenticate_request already sent response

            try:
                content_length = int(self.headers['Content-Length'])
                post_body = self.rfile.read(content_length)
                data = json.loads(post_body.decode('utf-8'))
                file_id = data.get('googleDriveFileId')

                if not file_id:
                    self.send_api_response(400, {"message": "googleDriveFileId is required for deletion."})
                    return

                logger.info(f"Received delete request for Google Drive File ID: {file_id} from admin: {admin_payload.get('username')}")
                
                class WebProgressReporter:
                    async def edit_text(self, message):
                        set_processing_status(message)

                web_progress_reporter_instance = WebProgressReporter()
                set_processing_status(f"Initiating deletion for video ID: {file_id}...")

                main_loop = self.server.main_asyncio_loop
                
                delete_future = asyncio.run_coroutine_threadsafe(
                    self._perform_delete_operation(file_id, web_progress_reporter_instance),
                    main_loop
                )
                delete_future.add_done_callback(lambda future: _log_scheduled_future_error(future, "delete_video"))
                
                self.send_api_response(200, {"message": f"Deletion initiated for video ID: {file_id}. Gallery will update shortly."})

            except json.JSONDecodeError:
                self.send_api_response(400, {"message": "Invalid JSON payload."})
            except Exception as e:
                logger.error(f"Error handling video deletion: {e}", exc_info=True)
                self.send_api_response(500, {"message": f"Server error during deletion: {e}"})
        elif self.path == '/benchmark_data/delete_records':
            admin_payload = self._authenticate_request()
            if not admin_payload:
                return

            try:
                with _benchmark_lock:
                    if _benchmark_in_progress:
                        self.send_api_response(409, {
                            "message": "Cannot delete benchmark records while benchmark run is in progress.",
                            "benchmarkInProgress": True
                        })
                        return

                content_length = int(self.headers.get('Content-Length', 0))
                post_body = self.rfile.read(content_length) if content_length > 0 else b'{}'
                data = json.loads(post_body.decode('utf-8') or '{}')

                raw_indices = data.get('recordIndices')
                if not isinstance(raw_indices, list) or not raw_indices:
                    self.send_api_response(400, {"message": "'recordIndices' must be a non-empty array."})
                    return

                sanitized_indices = []
                for value in raw_indices:
                    try:
                        idx = int(value)
                    except (TypeError, ValueError):
                        continue
                    if idx >= 0:
                        sanitized_indices.append(idx)
                unique_indices = sorted(set(sanitized_indices))

                if not unique_indices:
                    self.send_api_response(400, {"message": "No valid record indices provided for deletion."})
                    return

                records = []
                if os.path.exists('benchmark_data.json'):
                    with open('benchmark_data.json', 'r', encoding='utf-8') as benchmark_file:
                        loaded = json.load(benchmark_file)
                    if isinstance(loaded, dict) and isinstance(loaded.get('records'), list):
                        records = loaded.get('records', [])
                    elif isinstance(loaded, list):
                        records = loaded

                if not records:
                    self.send_api_response(404, {"message": "No benchmark records available to delete."})
                    return

                max_index = len(records) - 1
                valid_indices = [idx for idx in unique_indices if idx <= max_index]
                if not valid_indices:
                    self.send_api_response(400, {"message": "Selected record indices are out of bounds."})
                    return

                index_set = set(valid_indices)
                remaining_records = [record for i, record in enumerate(records) if i not in index_set]
                deleted_count = len(records) - len(remaining_records)

                if deleted_count <= 0:
                    self.send_api_response(400, {"message": "No benchmark records were deleted."})
                    return

                _save_json_and_csv(remaining_records)

                logger.info(
                    f"Deleted {deleted_count} benchmark record(s) by admin '{admin_payload.get('username')}'. "
                    f"Indices: {valid_indices}"
                )
                self.send_api_response(200, {
                    "message": f"Deleted {deleted_count} benchmark record(s).",
                    "deletedCount": deleted_count,
                    "deletedIndices": valid_indices,
                    "remainingCount": len(remaining_records)
                })
            except json.JSONDecodeError:
                self.send_api_response(400, {"message": "Invalid JSON payload."})
            except Exception as e:
                logger.error(f"Error deleting benchmark records: {e}", exc_info=True)
                self.send_api_response(500, {"message": f"Server error deleting benchmark records: {e}"})
        elif self.path == '/benchmark_settings':
            admin_payload = self._authenticate_request()
            if not admin_payload:
                return

            try:
                content_length = int(self.headers.get('Content-Length', 0))
                post_body = self.rfile.read(content_length) if content_length > 0 else b'{}'
                data = json.loads(post_body.decode('utf-8') or '{}')

                if 'enabled' not in data:
                    self.send_api_response(400, {"message": "'enabled' boolean is required."})
                    return

                requested_state = bool(data.get('enabled'))
                updated_state = set_benchmarking_enabled(requested_state)
                logger.info(
                    f"Benchmarking runtime flag updated by admin '{admin_payload.get('username')}' -> {updated_state}"
                )
                self.send_api_response(200, {
                    "message": f"Benchmarking {'enabled' if updated_state else 'disabled'}.",
                    "benchmarkingEnabled": updated_state,
                    "benchmarkInProgress": _benchmark_in_progress,
                    "benchmarkProgress": dict(_benchmark_progress)
                })
            except json.JSONDecodeError:
                self.send_api_response(400, {"message": "Invalid JSON payload."})
            except Exception as e:
                logger.error(f"Error updating benchmark settings: {e}", exc_info=True)
                self.send_api_response(500, {"message": f"Server error updating benchmark settings: {e}"})
        elif self.path == '/get_github_commit_info': # New endpoint for GitHub commit info (protected)
            admin_payload = self._authenticate_request()
            if not admin_payload: return # _authenticate_request already sent response

            try:
                content_length = int(self.headers['Content-Length'])
                post_body = self.rfile.read(content_length)
                data = json.loads(post_body.decode('utf-8'))
                commit_sha = data.get('commitSha')

                if not commit_sha:
                    self.send_api_response(400, {"message": "commitSha is required."})
                    return
                
                logger.info(f"Received request for commit info for SHA: {commit_sha} from admin: {admin_payload.get('username')}")
                
                commit_details = get_commit_details(commit_sha)

                if commit_details:
                    self.send_api_response(200, {"message": "Commit details fetched successfully.", "commitInfo": commit_details})
                else:
                    self.send_api_response(404, {"message": f"Could not find commit details for SHA: {commit_sha}. Ensure the SHA is correct and the GitHub token has appropriate permissions."})
                
            except json.JSONDecodeError:
                self.send_api_response(400, {"message": "Invalid JSON payload."})
            except Exception as e:
                logger.error(f"Error handling GitHub commit info request: {e}", exc_info=True)
                self.send_api_response(500, {"message": f"Server error fetching commit info: {e}"})
        elif self.path == '/login': # New endpoint for admin login
            try:
                content_length = int(self.headers['Content-Length'])
                post_body = self.rfile.read(content_length)
                data = json.loads(post_body.decode('utf-8'))
                username = data.get('username')
                password = data.get('password')

                if not username or not password:
                    self.send_api_response(400, {"message": "Username and password are required."})
                    return

                if authenticate_admin(username, password):
                    is_master_admin = username in MASTER_ADMIN_USERNAMES
                    expiry = get_session_expiry_time() # Get expiry based on config
                    payload = {
                        'username': username,
                        'isMasterAdmin': is_master_admin,
                        'exp': expiry if expiry > 0 else None, # Set exp only if timeout is enabled
                        'iat': datetime.datetime.now(datetime.timezone.utc)
                    }
                    if not SESSION_TIMEOUT_ENABLED:
                         del payload['exp'] # Remove exp if session timeout is disabled

                    token = jwt.encode(payload, JWT_SECRET_KEY, algorithm="HS256")
                    logger.info(f"Admin '{username}' logged in successfully.")
                    self.send_api_response(200, {
                        "message": "Login successful.",
                        "token": token,
                        "username": username,
                        "isMasterAdmin": is_master_admin,
                        "sessionTimeoutEnabled": SESSION_TIMEOUT_ENABLED,
                        "sessionDurationDays": SESSION_DURATION_DAYS
                    })
                else:
                    logger.warning(f"Failed login attempt for username: {username}")
                    self.send_api_response(401, {"message": "Invalid username or password."})
            except json.JSONDecodeError:
                self.send_api_response(400, {"message": "Invalid JSON payload."})
            except Exception as e:
                logger.error(f"Error during login: {e}", exc_info=True)
                self.send_api_response(500, {"message": f"Server error during login: {e}"})
        elif self.path == '/logout': # New endpoint for logout
            token = self._get_auth_token()
            if token:
                invalidate_token(token)
                logger.info(f"Token {token[:10]}... invalidated for logout.")
                self.send_api_response(200, {"message": "Logged out successfully."})
            else:
                self.send_api_response(400, {"message": "No token provided for logout."})
        elif self.path == '/logout_all_admins': # New endpoint for master admin to logout all
            admin_payload = self._authenticate_request()
            if not admin_payload: return

            # Check if the authenticated user is one of the master admins
            if self._authorize_master_admin(admin_payload):
                clear_all_sessions() # Invalidate all sessions
                logger.info(f"Master admin '{admin_payload.get('username')}' triggered logout of all sessions.")
                self.send_api_response(200, {"message": "All admin sessions have been invalidated."})
        elif self.path == '/update_credentials': # New endpoint for admin password update (protected)
            admin_payload = self._authenticate_request()
            if not admin_payload: return # _authenticate_request already sent response

            try:
                content_length = int(self.headers['Content-Length'])
                post_body = self.rfile.read(content_length)
                data = json.loads(post_body.decode('utf-8'))
                
                current_password = data.get('current_password')
                new_password = data.get('new_password')
                
                username = admin_payload.get('username') # Get username from validated token

                if not current_password or not new_password:
                    self.send_api_response(400, {"message": "Current password and new password are required."})
                    return

                # Verify current password using the stored hash
                stored_hash = ADMIN_CREDENTIALS.get(username)
                if not stored_hash or not verify_password(stored_hash, current_password):
                    logger.warning(f"Failed password update attempt for '{username}': Invalid current password.")
                    self.send_api_response(401, {"message": "Invalid current password."})
                    return

                # Update the password in admin_auth.py file
                # The comment will now reflect the new plaintext password
                comment_text = f"bcrypt hash for '{new_password}'"
                self.server.main_asyncio_loop.run_in_executor(
                    None, # Use default thread pool
                    update_admin_credential_in_file,
                    username, new_password, comment_text
                )
                
                # Invalidate the current token after password change for security
                token_to_invalidate = self._get_auth_token();
                if token_to_invalidate:
                    invalidate_token(token_to_invalidate)

                logger.info(f"Admin '{username}' successfully updated their password.")
                self.send_api_response(200, {"message": "Password updated successfully. Please log in again with your new password."})

            except json.JSONDecodeError:
                self.send_api_response(400, {"message": "Invalid JSON payload."})
            except Exception as e:
                logger.error(f"Error handling password update: {e}", exc_info=True)
                self.send_api_response(500, {"message": f"Server error during password update: {e}"})
        elif self.path == '/update_ad_settings': # New endpoint for updating ad settings (master admin only)
            admin_payload = self._authenticate_request()
            if not admin_payload: return

            if not self._authorize_master_admin(admin_payload): return

            try:
                content_length = int(self.headers['Content-Length'])
                post_body = self.rfile.read(content_length)
                data = json.loads(post_body.decode('utf-8'))
                
                new_ads_enabled_globally = data.get('ads_enabled_globally')
                new_show_ads_to_admins = data.get('show_ads_to_admins')

                if new_ads_enabled_globally is None or new_show_ads_to_admins is None:
                    self.send_api_response(400, {"message": "Both 'ads_enabled_globally' and 'show_ads_to_admins' are required."})
                    return
                
                _ADS_ENABLED_GLOBALLY = bool(new_ads_enabled_globally)
                _SHOW_ADS_TO_ADMINS = bool(new_show_ads_to_admins)
                save_ad_settings() # Persist changes to file

                logger.info(f"Ad settings updated by master admin '{admin_payload.get('username')}': Globally Enabled={_ADS_ENABLED_GLOBALLY}, Show to Admins={_SHOW_ADS_TO_ADMINS}")
                self.send_api_response(200, {"message": "Ad settings updated successfully.", "ads_enabled_globally": _ADS_ENABLED_GLOBALLY, "show_ads_to_admins": _SHOW_ADS_TO_ADMINS})

            except json.JSONDecodeError:
                self.send_api_response(400, {"message": "Invalid JSON payload."})
            except Exception as e:
                logger.error(f"Error updating ad settings: {e}", exc_info=True)
                self.send_api_response(500, {"message": f"Server error updating ad settings: {e}"})
        else:
            self.send_api_response(404, {"message": "Not Found"})

    async def _perform_delete_operation(self, file_id: str, progress_reporter):
        """Helper to run the deletion in the asyncio loop."""
        try:
            success = await delete_video_from_drive_and_github(file_id)
            if success:
                await progress_reporter.edit_text(f"Successfully deleted video with ID: {file_id}.")
                # Remove from tracking data as well
                with _tracking_data_lock:
                    global _tracking_data
                    _tracking_data = [entry for entry in _tracking_data if entry.get('googleDriveFileId') != file_id] # Assuming file_id can be used as unique ID for tracking
                    save_tracking_data()
                logger.info(f"Deletion process completed successfully for {file_id}.")
            else:
                await progress_reporter.edit_text(f"Failed to delete video with ID: {file_id}. Check server logs.")
                logger.error(f"Deletion process failed for {file_id}.")
        except Exception as e:
            await progress_reporter.edit_text(f"An unexpected error occurred during deletion: {e}")
            logger.error(f"Unhandled exception during deletion for {file_id}: {e}", exc_info=True)
        finally:
            # We use a short delay of 2 seconds here to avoid the status message from 
            # flashing repeatedly in the frontend's 2-second polling loop.
            reset_status_after_delay(2)


    def do_GET(self):
        request_path = urlparse(self.path).path

        if request_path == '/status':
            self.send_api_response(200, get_status_payload(self._get_request_actor()))
        elif request_path == '/events/status':
            self._stream_status_events()
        elif request_path == '/events/admin_auth':
            self._stream_admin_auth_events()
        elif request_path == '/events/admin_tracker_data':
            admin_payload = self._authenticate_sse_request()
            if not admin_payload:
                return

            self._stream_admin_tracker_events(admin_payload.get('username', 'unknown'))
        elif request_path == '/events/admin_uptime_data':
            admin_payload = self._authenticate_sse_request()
            if not admin_payload:
                return

            self._stream_admin_uptime_events(admin_payload.get('username', 'unknown'))
        elif request_path == '/admin_tracker_data': # New endpoint for admin tracker data (protected)
            admin_payload = self._authenticate_request()
            if not admin_payload: return # _authenticate_request already sent response

            with _tracking_data_lock:
                tracking_snapshot = json.loads(json.dumps(_tracking_data, ensure_ascii=False))
            uptime_snapshot = get_uptime_payload().get("uptimeData", {})
            self.send_api_response(200, {"trackingData": tracking_snapshot, "uptimeData": uptime_snapshot})
        elif request_path == '/admin_uptime_data':
            admin_payload = self._authenticate_request()
            if not admin_payload:
                return
            self.send_api_response(200, get_uptime_payload())
        elif request_path == '/benchmark_data':
            admin_payload = self._authenticate_request()
            if not admin_payload:
                return

            benchmark_payload = {
                "generatedAt": None,
                "recordCount": 0,
                "records": [],
                "aggregates": {}
            }

            try:
                if os.path.exists('benchmark_data.json'):
                    with open('benchmark_data.json', 'r', encoding='utf-8') as benchmark_file:
                        loaded = json.load(benchmark_file)
                    if isinstance(loaded, dict):
                        benchmark_payload = {
                            "generatedAt": loaded.get("generatedAt"),
                            "recordCount": int(loaded.get("recordCount", len(loaded.get("records", [])) if isinstance(loaded.get("records"), list) else 0)),
                            "records": loaded.get("records", []) if isinstance(loaded.get("records"), list) else [],
                            "aggregates": loaded.get("aggregates", {}) if isinstance(loaded.get("aggregates"), dict) else {}
                        }
                    elif isinstance(loaded, list):
                        benchmark_payload["records"] = loaded
                        benchmark_payload["recordCount"] = len(loaded)
                benchmark_payload["benchmarkInProgress"] = _benchmark_in_progress
                benchmark_payload["benchmarkingEnabled"] = is_benchmarking_enabled()
                benchmark_payload["benchmarkProgress"] = dict(_benchmark_progress)
                self.send_api_response(200, benchmark_payload)
            except Exception as benchmark_read_error:
                logger.error(f"Failed serving benchmark data: {benchmark_read_error}", exc_info=True)
                self.send_api_response(500, {
                    "message": "Failed to load benchmark data.",
                    "benchmarkInProgress": _benchmark_in_progress,
                    "benchmarkingEnabled": is_benchmarking_enabled(),
                    "benchmarkProgress": dict(_benchmark_progress)
                })
        elif request_path == '/benchmark_settings':
            admin_payload = self._authenticate_request()
            if not admin_payload:
                return

            self.send_api_response(200, {
                "benchmarkingEnabled": is_benchmarking_enabled(),
                "benchmarkInProgress": _benchmark_in_progress,
                "benchmarkProgress": dict(_benchmark_progress)
            })
        elif request_path == '/benchmark_data.csv':
            admin_payload = self._authenticate_request()
            if not admin_payload:
                return

            csv_path = 'benchmark_data.csv'
            if not os.path.exists(csv_path):
                self.send_api_response(404, {"message": "Benchmark CSV not found."})
                return

            try:
                with open(csv_path, 'rb') as csv_file:
                    csv_bytes = csv_file.read()

                self.send_response(200)
                self.send_header('Content-type', 'text/csv; charset=utf-8')
                self.send_header('Content-Disposition', 'attachment; filename="benchmark_data.csv"')
                self.send_header('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0')
                self.send_header('Pragma', 'no-cache')
                self.send_header('Expires', '0')
                self._set_cors_headers()
                self.end_headers()
                self.wfile.write(csv_bytes)
                logger.info(f"Served protected /benchmark_data.csv to admin: {admin_payload.get('username')}")
            except Exception as csv_error:
                logger.error(f"Failed serving benchmark CSV: {csv_error}", exc_info=True)
                self.send_api_response(500, {"message": "Failed to load benchmark CSV."})
        elif request_path == '/benchmark_data.json':
            admin_payload = self._authenticate_request()
            if not admin_payload:
                return

            json_path = 'benchmark_data.json'
            if not os.path.exists(json_path):
                self.send_api_response(404, {"message": "Benchmark JSON not found."})
                return

            try:
                with open(json_path, 'r', encoding='utf-8') as benchmark_json_file:
                    benchmark_json_payload = json.load(benchmark_json_file)
                self.send_api_response(200, benchmark_json_payload)
                logger.info(f"Served protected /benchmark_data.json to admin: {admin_payload.get('username')}")
            except Exception as benchmark_json_error:
                logger.error(f"Failed serving benchmark JSON: {benchmark_json_error}", exc_info=True)
                self.send_api_response(500, {"message": "Failed to load benchmark JSON."})
        elif request_path == '/get_ad_settings': # New endpoint for getting ad settings
            # This endpoint is public, no authentication needed
            self.send_api_response(200, {
                "ads_enabled_globally": _ADS_ENABLED_GLOBALLY,
                "show_ads_to_admins": _SHOW_ADS_TO_ADMINS
            })
            logger.info("Served /get_ad_settings")
        else:
            # For other GET requests, serve files as before (if any) or return 404
            super().do_GET() # Use base class's do_GET for serving files


class ThreadedHTTPServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    """
    A threaded HTTP server that also stores a reference to the main asyncio loop.
    """
    def __init__(self, server_address, RequestHandlerClass, main_asyncio_loop):
        super().__init__(server_address, RequestHandlerClass)
        self.main_asyncio_loop = main_asyncio_loop


def run_web_server(port, main_loop):
    """Runs the local HTTP server in a separate thread."""
    with ThreadedHTTPServer(("", port), LocalAPIHandler, main_loop) as httpd:
        logger.info(f"Local Web Server serving at port {port}")
        httpd.serve_forever()


# --- Main Function ---
def main():
    # Load tracking data and ad settings at startup
    load_tracking_data()
    load_uptime_data()
    start_uptime_monitor()
    atexit.register(mark_uptime_shutdown, "atexit")
    load_ad_settings()
    
    # Start the preview cleanup scheduler (removes abandoned preview files)
    start_preview_cleanup_scheduler()
    logger.info("Preview cleanup scheduler started")

    if not TELEGRAM_BOT_TOKEN:
        logger.error("TELEGRAM_BOT_TOKEN is not configured. Set it in environment or .env before starting tg.py.")
        return

    # Ensure JWT_SECRET_KEY is available
    global JWT_SECRET_KEY
    if not JWT_SECRET_KEY:
        logger.warning("JWT_SECRET_KEY is not configured. Generating a temporary key for this process.")
        JWT_SECRET_KEY = os.urandom(32).hex()
        logger.warning("Set JWT_SECRET_KEY in .env for stable and secure auth across restarts.")

    web_asyncio_loop = asyncio.new_event_loop()
    web_asyncio_thread = threading.Thread(target=run_async_loop, args=(web_asyncio_loop,), daemon=True)
    web_asyncio_thread.start()
    logger.info("Dedicated web asyncio loop started")

    web_server_thread = threading.Thread(target=run_web_server, args=(WEB_SERVER_PORT, web_asyncio_loop,), daemon=True)
    web_server_thread.start()
    logger.info(f"Web server thread started on port {WEB_SERVER_PORT}")

    def _build_telegram_application() -> Application:
        # Build app with longer timeouts (60s to tolerate transient network delays)
        app = (Application.builder()
               .token(TELEGRAM_BOT_TOKEN)
               .read_timeout(60)
               .write_timeout(60)
               .connect_timeout(60)
               .pool_timeout(60)
               .build())

        async def telegram_error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
            """Catches Telegram polling/network errors gracefully instead of logging raw tracebacks."""
            from telegram.error import NetworkError, TimedOut
            err = context.error
            if isinstance(err, (NetworkError, TimedOut)):
                logger.warning(f"Telegram polling network error (will retry): {type(err).__name__}: {err}")
            else:
                logger.error(f"Unhandled Telegram error: {err}", exc_info=context.error)

        app.add_error_handler(telegram_error_handler)
        app.add_handler(CommandHandler("start", start))
        app.add_handler(CommandHandler("track", track_command))
        app.add_handler(CommandHandler("help", help_command))
        app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_non_command_text))
        app.add_handler(MessageHandler(filters.COMMAND, unknown_command))
        return app

    first_start = True
    retry_delay_seconds = 5

    try:
        while True:
            app = _build_telegram_application()
            logger.info("Telegram Bot started. Listening for updates...")
            try:
                app.run_polling(
                    drop_pending_updates=first_start,
                    bootstrap_retries=-1,
                )
                logger.info("Telegram polling exited normally.")
                break
            except KeyboardInterrupt:
                logger.info("Telegram polling interrupted by user.")
                break
            except Exception as e:
                logger.error(
                    f"Telegram polling crashed ({type(e).__name__}: {e}). "
                    f"Retrying in {retry_delay_seconds}s..."
                )
                time.sleep(retry_delay_seconds)
                retry_delay_seconds = min(retry_delay_seconds * 2, 60)
            finally:
                first_start = False
    finally:
        stop_uptime_monitor()
        mark_uptime_shutdown("process_exit")
        time.sleep(UPTIME_SHUTDOWN_BROADCAST_GRACE_SECONDS)
        try:
            web_asyncio_loop.call_soon_threadsafe(web_asyncio_loop.stop)
        except Exception:
            pass

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        logger.info("Bot stopped by user")
    except Exception as e:
        logger.error(f"Bot crashed: {e}")
        
