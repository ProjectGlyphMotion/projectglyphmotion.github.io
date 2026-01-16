import logging
from telegram import Update
from telegram.ext import Application, CommandHandler, MessageHandler, ContextTypes, filters
import os
import subprocess
import asyncio
import re
import time
import threading
import http.server
import socketserver
import json
import cgi
from typing import Union
import requests
import jwt # New import for JWT
import datetime # New import for JWT expiry
import socket # Added: Import the socket module for socket.timeout
import base64  # For encoding preview images
import uuid  # For generating unique session IDs
import shutil  # For moving cached preview files

# Import the gh.py script
from gh import update_github_pages_with_video, delete_video_from_drive_and_github, get_commit_details

# Import admin_auth.py for authentication and session management
from admin_auth import authenticate_admin, get_session_expiry_time, update_admin_credential_in_file, verify_password, ADMIN_CREDENTIALS, SESSION_TIMEOUT_ENABLED, SESSION_DURATION_DAYS

# --- Configuration ---
TELEGRAM_BOT_TOKEN = "YOUR_BOT_TOKEN_HERE"  # Replace with your bot token
USE_GITHUB_PAGES = True  # Switch to enable/disable GitHub Pages integration (set to True to use gh.py)
OUTPUT_SUBDIRECTORY = "output"
INPUT_SUBDIRECTORY = "input"
WEB_SERVER_PORT = 5000 # Port for the local web server
TRACKING_DATA_FILE = 'tracking_data.json' # New file to store tracking data

# Frame Restriction Configuration
FRAME_RESTRICTION_ENABLED = True # Set to True to enable frame count restriction
FRAME_RESTRICTION_VALUE = 7000 # Max allowed frames for video processing
FFPROBE_TIMEOUT_SECONDS = 30 # Timeout for ffprobe command in seconds

# JWT Secret Key (VERY IMPORTANT: Replace with a strong, random key in production!)
JWT_SECRET_KEY = 'YOUR_JWT_SECRET_KEY_HERE' # Generate a secure key, e.g., using os.urandom(32) and base64 encoding

# Master Admin Usernames (only these users can trigger global logout and other master actions)
# These users must also exist in ADMIN_CREDENTIALS in admin_auth.py
# FIX: Changed this to a set of individual strings for each master admin.
MASTER_ADMIN_USERNAMES = {"ExampleAdmin1", "ExampleAdmin2"} # Add more usernames to this set if you have multiple master admins, e.g., {"ExampleAdmin1", "another_master_admin"}
# Global flag to enable/disable ads for all users (including non-admins)
_ADS_ENABLED_GLOBALLY = False # Default to False, can be changed by master admin

# Flag to determine if ads should be shown to admins when _ADS_ENABLED_GLOBALLY is True
_SHOW_ADS_TO_ADMINS = False # Default to False, can be changed by master admin

# File to persist ad settings
AD_SETTINGS_FILE = 'ad_settings.json'

# --- ROI Preview Configuration ---
# Directory to store temporary preview files
PREVIEW_SUBDIRECTORY = "preview_temp"
# Time in seconds before an abandoned preview is cleaned up (5 minutes)
PREVIEW_CLEANUP_TIMEOUT_SECONDS = 300
# Interval for preview cleanup check (60 seconds)
PREVIEW_CLEANUP_INTERVAL_SECONDS = 60

# Ensure input and output directories exist
os.makedirs(OUTPUT_SUBDIRECTORY, exist_ok=True)
os.makedirs(INPUT_SUBDIRECTORY, exist_ok=True)
os.makedirs(PREVIEW_SUBDIRECTORY, exist_ok=True)

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

# List to keep track of invalidated JWTs (for immediate logout)
# In a real-world app, this would be a persistent store like a database or Redis.
_invalidated_tokens = set()
_token_invalidation_lock = threading.Lock()

# --- Preview Session Management ---
# Stores preview sessions: {session_id: {'video_path': str, 'created_at': float, 'used': bool}}
_preview_sessions = {}
_preview_sessions_lock = threading.Lock()

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


def set_processing_status(message: Union[str, None]):
    """Sets the global processing status message."""
    global _current_processing_status
    with _status_lock:
        _current_processing_status = message
    logger.info(f"Global Status Update: {message}")

def reset_status_after_delay(delay_seconds: int = 5): # Reduced delay to 5 seconds
    """Schedules a task to reset the status to None after a delay."""
    logger.info(f"Scheduling status reset to 'None' (hide) in {delay_seconds} seconds.")
    threading.Timer(delay_seconds, set_processing_status, args=(None,)).start() # Pass None

def load_tracking_data():
    """Loads tracking data from the JSON file on startup."""
    global _tracking_data
    if os.path.exists(TRACKING_DATA_FILE):
        with _tracking_data_lock:
            try:
                with open(TRACKING_DATA_FILE, 'r') as f:
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
            with open(TRACKING_DATA_FILE, 'w') as f:
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
    Returns the frame count as an int, or None if it cannot be determined (e.g., timeout, error).
    """
    try:
        # Command to get number of frames using ffprobe
        command = [
            "ffprobe",
            "-v", "error",
            "-select_streams", "v:0", # Select only the first video stream
            "-count_frames", # Count frames
            "-show_entries", "stream=nb_read_frames", # Show number of read frames
            "-of", "default=nokey=1:noprint_wrappers=1", # Output format: raw number
            video_path
        ]
        logger.info(f"Running ffprobe to get frame count: {' '.join(command)}")
        process = await asyncio.create_subprocess_exec(
            *command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        try:
            # Use communicate with a timeout
            stdout, stderr = await asyncio.wait_for(process.communicate(), timeout=FFPROBE_TIMEOUT_SECONDS)
        except asyncio.TimeoutError:
            logger.error(f"FFprobe command timed out after {FFPROBE_TIMEOUT_SECONDS} seconds for {video_path}. Terminating process.")
            process.kill() # Terminate the ffprobe process
            await process.wait() # Wait for it to clean up
            return None # Indicate failure due to timeout

        if process.returncode == 0:
            try:
                frame_count = int(stdout.decode('utf-8').strip())
                logger.info(f"FFprobe successfully retrieved frame count: {frame_count} for {video_path}")
                return frame_count
            except ValueError:
                logger.error(f"Could not parse frame count from ffprobe output: {stdout.decode('utf-8').strip()}")
                return None
        else:
            logger.error(f"FFprobe failed with exit code {process.returncode}: {stderr.decode('utf-8').strip()}")
            return None
    except FileNotFoundError:
        logger.error("ffprobe command not found. Please ensure FFmpeg is installed and in your system's PATH.")
        return None
    except Exception as e:
        logger.error(f"An unexpected error occurred while getting frame count: {e}", exc_info=True)
        return None


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
    yt_dlp_post_process_regex = re.compile(r"\[Merger\] Merging formats into \"(.*)\"")


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
                            new_progress_text = f"Merging Audio: {ffmpeg_match.group(0).strip()}" # Fixed: use group(0) for full match
                    
                    if new_progress_text and new_progress_text != last_progress_text and (time.time() - last_update_time > 1):
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
                    new_progress_text = f"Merging Audio: {ffmpeg_match.group(0).strip()}" # Fixed: use group(0) for full match

            if new_progress_text and new_progress_text != last_progress_text:
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
            "-o", os.path.join(output_dir, "%(title)s.%(ext)s"), # Use title for filename
            "-f", "bestvideo[ext=mp4]+bestaudio[ext=m4a]/bestvideo+bestaudio/best",
            "--merge-output-format", "mp4",  # Ensure output format is mp4
            url
        ]
        logger.info(f"Starting yt-dlp dry-run to get filename: {' '.join(dry_run_command)}")
        dry_run_process = await asyncio.create_subprocess_exec(
            *dry_run_command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        stdout, stderr = await dry_run_process.communicate()
        
        if dry_run_process.returncode != 0:
            error_msg = stderr.decode('utf-8', errors='ignore').strip()
            logger.error(f"yt-dlp dry-run failed with exit code {dry_run_process.returncode}: {error_msg}")
            if progress_message_obj:
                await progress_message_obj.edit_text(f"Download setup failed (dry-run): {error_msg[:200]}...")
            return False, ""

        actual_output_filename = stdout.decode('utf-8', errors='ignore').strip()
        # Clean up any potential invalid characters in the filename, though yt-dlp --restrict-filenames helps
        actual_output_filename = re.sub(r'[\\/:*?"<>|]', '_', actual_output_filename)
        # Ensure filename ends with .mp4
        if not actual_output_filename.lower().endswith('.mp4'):
            actual_output_filename = os.path.splitext(actual_output_filename)[0] + '.mp4'
        actual_output_path = os.path.join(output_dir, actual_output_filename)

        command = [
            "yt-dlp",
            "-o", actual_output_path,
            # Use format selection compatible with mp4 output
            "-f", "bestvideo[ext=mp4]+bestaudio[ext=m4a]/bestvideo+bestaudio/best",
            "--merge-output-format", "mp4",  # Ensure output is mp4
            "--progress",
            "--no-playlist",
            "--output-na-placeholder", "",
            "--restrict-filenames",
            "--continue",
            url
        ]
        logger.info(f"Starting yt-dlp command: {' '.join(command)}")

        process = await asyncio.create_subprocess_exec(
            *command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )

        stdout_task = asyncio.create_task(
            _stream_output_and_update_message(process.stdout, progress_message_obj, context, "yt-dlp_stdout", 'yt-dlp')
        )
        stderr_task = asyncio.create_task(
            _stream_output_and_update_message(process.stderr, progress_message_obj, context, "yt-dlp_stderr", 'yt-dlp')
        )

        return_code = await process.wait()

        await stdout_task
        await stderr_task

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
    roi_params: dict = None
) -> bool:
    """
    Runs your video tracking script by passing arguments and streams its output.
    progress_message_obj and context are optional for web server usage.
    roi_params is a dict with ROI parameters (roi_enabled, roi_x, roi_y, roi_width, roi_height, roi_show_overlay, roi_overlay_opacity)
    """
    try:
        command = [
            "python3",
            "-u",
            "ot.py",
            "--model", "yolov8m.pt",
            # Ensure output_path has an extension (e.g., .mp4) if not already present
            "--output_video", os.path.splitext(output_path)[0], # ot.py expects path without .mp4
            "--input_video", input_path # Pass input video path as an argument
        ]
        
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
            stderr=subprocess.PIPE
        )

        stdout_task = asyncio.create_task(
            _stream_output_and_update_message(process.stdout, progress_message_obj, context, "ot_stdout", 'general')
        )
        stderr_task = asyncio.create_task(
            _stream_output_and_update_message(process.stderr, progress_message_obj, context, "ot_stderr", 'tqdm')
        )

        return_code = await process.wait()

        await stdout_task
        await stderr_task

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
async def process_video_unified(video_source: Union[str, cgi.FieldStorage], is_file_upload: bool, progress_message_obj=None, telegram_context=None, client_ip: str = "N/A", geolocation_info: dict = None, roi_params: dict = None, original_filename: str = None):
    """
    Unified function to process video, upload to GDrive, and update GitHub Pages.
    progress_message_obj is the actual Telegram message object to edit (for Telegram)
    or a WebProgressReporter instance (for web).
    telegram_context is needed for sending new messages in case of errors from subprocess streams (for Telegram).
    client_ip and geolocation_info are new parameters for tracking.
    roi_params is a dict with ROI parameters from the frontend.
    original_filename is the original filename from a preview session (for cached files).
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
            input_filename = os.path.basename(getattr(video_source, "filename", "uploaded_file.mp4"))
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
    
    # Pass the correctly determined local_input_path for processing, along with ROI params
    tracking_success = await run_tracking_script_and_stream_output(
        local_input_path, local_output_path, progress_message_obj, telegram_context,
        roi_params=roi_params
    )

    if not tracking_success:
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
        
        # update_github_pages_with_video now returns the commit SHA upon success
        gh_update_success, commit_sha = await update_github_pages_with_video( # Modified to capture commit_sha
            processed_video_path=local_output_path,
            original_video_title=video_title_for_gh,
            description=video_description_for_gh
        )
        if gh_update_success:
            if progress_message_obj:
                await progress_message_obj.edit_text("🎉 Object tracking and GitHub Pages update complete!")
            set_processing_status("🎉 Object tracking and GitHub Pages update complete!") # Update global status
            logger.info("GitHub Pages update successful.")
            
            # --- Add tracking entry after successful GitHub update ---
            if commit_sha: # Only add if commit_sha is available
                tracking_entry = {
                    "timestamp": int(time.time()),
                    "videoTitle": video_title_for_gh,
                    "commitSha": commit_sha,
                    "ipAddress": client_ip,
                    "googleDriveFileId": None, # Placeholder for file_id, to be filled from videos.json if needed
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

            reset_status_after_delay() # Reset status after success
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
        # Filter out /status GET and HEAD requests to reduce log verbosity
        if self.path == '/status' and (self.command == 'GET' or self.command == 'HEAD'):
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
            
            # Log the request here, after parsing it
            self.log_request() # This will log the method and path

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
        self.send_header('Access-Control-Allow-Headers', 'Content-Type, X-Forwarded-For, Authorization') # Added Authorization header
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
        if self.path == '/status':
            self.send_response(200)
            self._set_cors_headers()
            self.end_headers()
            logger.info("Handled HEAD request for /status.")
        else:
            # Fallback for other HEAD requests, might return 404 or just headers
            super().do_HEAD() # Call the base class method

    def _get_auth_token(self):
        """Extracts JWT from Authorization header."""
        auth_header = self.headers.get('Authorization')
        if auth_header and auth_header.startswith('Bearer '):
            return auth_header.split(' ')[1]
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

    def _authorize_master_admin(self, admin_payload: dict) -> bool:
        """Checks if the authenticated admin is a master admin."""
        if admin_payload.get('username') not in MASTER_ADMIN_USERNAMES:
            self.send_api_response(403, {"message": "Forbidden: Only a master admin can perform this action."})
            logger.warning(f"Unauthorized master admin action attempt by '{admin_payload.get('username')}'")
            return False
        return True


    def do_POST(self):
        global _ADS_ENABLED_GLOBALLY, _SHOW_ADS_TO_ADMINS

        if self.path == '/process_web_video':
            try:
                # Get client IP and geolocation data immediately
                client_ip = get_client_ip(self)
                geolocation_info = get_geolocation_data(client_ip)
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

                # Only require video_url or video_file if we don't have a cached video from preview session
                if not cached_video_path:
                    if 'video_url' in form:
                        video_url = form['video_url'].value
                        logger.info(f"Received video URL from web: {video_url}")
                    elif 'video_file' in form:
                        video_file = form['video_file']
                        logger.info(f"Received uploaded file from web: {video_file.filename}")
                    else:
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
                elif video_file is not None and hasattr(video_file, "filename") and video_file.filename:
                    video_source = video_file
                    is_file_upload = True
                else:
                    video_source = video_url

                asyncio.run_coroutine_threadsafe(
                    process_video_unified(
                        video_source,
                        is_file_upload=is_file_upload,
                        progress_message_obj=web_progress_reporter_instance,
                        telegram_context=None,
                        client_ip=client_ip, # Pass client IP
                        geolocation_info=geolocation_info, # Pass geolocation info
                        roi_params=roi_params,  # Pass ROI parameters
                        original_filename=cached_original_filename  # Pass original filename from preview session
                    ),
                    main_loop
                )

                self.send_api_response(200, {"message": "Processing initiated. Check GitHub Pages for updates."})

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
                
                # Handle new video upload or URL
                if 'video_url' in form:
                    video_url = form['video_url'].value
                    logger.info(f"Preview request for URL: {video_url}")
                elif 'video_file' in form:
                    video_file = form['video_file']
                    logger.info(f"Preview request for uploaded file: {video_file.filename}")
                else:
                    self.send_api_response(400, {"success": False, "message": "No video URL or file provided."})
                    return
                
                # Generate a new session ID
                new_session_id = str(uuid.uuid4())
                video_title = None  # Will store the video title from yt-dlp (only for URLs)
                
                if video_file is not None and hasattr(video_file, "filename") and video_file.filename:
                    # Handle file upload
                    input_filename = os.path.basename(video_file.filename)
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
                    # File upload - use the original filename
                    original_fn = os.path.basename(video_file.filename) if hasattr(video_file, 'filename') else None
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
                
                asyncio.run_coroutine_threadsafe(
                    self._perform_delete_operation(file_id, web_progress_reporter_instance),
                    main_loop
                )
                
                self.send_api_response(200, {"message": f"Deletion initiated for video ID: {file_id}. Gallery will update shortly."})

            except json.JSONDecodeError:
                self.send_api_response(400, {"message": "Invalid JSON payload."})
            except Exception as e:
                logger.error(f"Error handling video deletion: {e}", exc_info=True)
                self.send_api_response(500, {"message": f"Server error during deletion: {e}"})
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
                    expiry = get_session_expiry_time() # Get expiry based on config
                    payload = {
                        'username': username,
                        'exp': expiry if expiry > 0 else None, # Set exp only if timeout is enabled
                        'iat': datetime.datetime.now(datetime.timezone.utc)
                    }
                    if not SESSION_TIMEOUT_ENABLED:
                         del payload['exp'] # Remove exp if session timeout is disabled

                    token = jwt.encode(payload, JWT_SECRET_KEY, algorithm="HS256")
                    logger.info(f"Admin '{username}' logged in successfully.")
                    self.send_api_response(200, {"message": "Login successful.", "token": token, "username": username, "sessionTimeoutEnabled": SESSION_TIMEOUT_ENABLED, "sessionDurationDays": SESSION_DURATION_DAYS})
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
            reset_status_after_delay()


    def do_GET(self):
        if self.path == '/status':
            with _status_lock: # Read the global status safely
                status_message = _current_processing_status
            
            # Include frame restriction config in the status response
            response_data = {
                "status": status_message if status_message is not None else "",
                "frameRestrictionEnabled": FRAME_RESTRICTION_ENABLED,
                "frameRestrictionValue": FRAME_RESTRICTION_VALUE
            }
            self.send_api_response(200, response_data)
        elif self.path == '/admin_tracker_data': # New endpoint for admin tracker data (protected)
            admin_payload = self._authenticate_request()
            if not admin_payload: return # _authenticate_request already sent response

            with _tracking_data_lock:
                self.send_api_response(200, {"trackingData": _tracking_data})
            logger.info(f"Served /admin_tracker_data to admin: {admin_payload.get('username')}")
        elif self.path == '/get_ad_settings': # New endpoint for getting ad settings
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
    load_ad_settings()
    
    # Start the preview cleanup scheduler (removes abandoned preview files)
    start_preview_cleanup_scheduler()
    logger.info("Preview cleanup scheduler started")

    # Ensure JWT_SECRET_KEY is not the default placeholder
    global JWT_SECRET_KEY
    if JWT_SECRET_KEY == 'YOUR_VERY_SECRET_JWT_KEY_HERE':
        logger.error("!!! WARNING: JWT_SECRET_KEY is still the default placeholder. Please change it to a strong, random key for security. !!!")
        # For demonstration, generate a temporary one if not set, but warn
        JWT_SECRET_KEY = os.urandom(32).hex()
        logger.warning(f"Generated a temporary JWT_SECRET_KEY: {JWT_SECRET_KEY}. CHANGE THIS IN PRODUCTION!")

    main_loop = asyncio.get_event_loop()

    web_server_thread = threading.Thread(target=run_web_server, args=(WEB_SERVER_PORT, main_loop,), daemon=True)
    web_server_thread.start()
    logger.info(f"Web server thread started on port {WEB_SERVER_PORT}")

    # Build app with longer timeouts
    app = (Application.builder()
           .token(TELEGRAM_BOT_TOKEN)
           .read_timeout(30)
           .write_timeout(30)
           .connect_timeout(30)
           .pool_timeout(30)
           .build())

    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("track", track_command))
    app.add_handler(CommandHandler("help", help_command))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_non_command_text))
    app.add_handler(MessageHandler(filters.COMMAND, unknown_command))

    logger.info("Telegram Bot started. Listening for updates...")
    
    try:
        app.run_polling(drop_pending_updates=True)
    except Exception as e:
        logger.error(f"Bot error: {e}")
        raise

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        logger.info("Bot stopped by user")
    except Exception as e:
        logger.error(f"Bot crashed: {e}")
        
