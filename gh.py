import os
import sys
import json
import logging
import time
import asyncio
from datetime import datetime
from typing import Tuple, Optional, Callable
from env_config import get_env

# Google Drive API imports
from google.oauth2.credentials import Credentials
from google_auth_oauthlib.flow import InstalledAppFlow
from google.auth.transport.requests import Request
from googleapiclient.discovery import build
from googleapiclient.http import MediaFileUpload
from googleapiclient.errors import HttpError

# GitHub API imports
from github import Github, InputGitTreeElement
from github.GithubException import GithubException

# --- Logging Setup ---
logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s", level=logging.INFO)
logger = logging.getLogger(__name__)

# --- Configuration (loaded from .env/environment) ---

# Google Drive API
GOOGLE_DRIVE_SCOPES = ['https://www.googleapis.com/auth/drive.file']
GOOGLE_DRIVE_CLIENT_SECRET_FILE = get_env('GOOGLE_DRIVE_CLIENT_SECRET_FILE', 'client_secret.json')

GOOGLE_DRIVE_TOKEN_FILE = get_env('GOOGLE_DRIVE_TOKEN_FILE', 'token.json')

GOOGLE_DRIVE_OUTPUT_FOLDER_NAME = get_env('GOOGLE_DRIVE_OUTPUT_FOLDER_NAME', 'ObjectTrackerMaster/output')


GITHUB_ACCESS_TOKEN = get_env('GITHUB_ACCESS_TOKEN')
if not GITHUB_ACCESS_TOKEN or GITHUB_ACCESS_TOKEN == "YOUR_GITHUB_PERSONAL_ACCESS_TOKEN_HERE":
    logger.error("GITHUB_ACCESS_TOKEN is not set or is still the placeholder. GitHub operations will fail!")

GITHUB_USERNAME = get_env('GITHUB_USERNAME', 'ProjectGlyphMotion')
GITHUB_REPO_NAME = get_env('GITHUB_REPO_NAME', 'ProjectGlyphMotion.github.io')

GITHUB_BRANCH = get_env('GITHUB_BRANCH', 'main')
# Path to the JSON file in your GitHub repository that stores video metadata
GITHUB_VIDEOS_JSON_PATH = 'videos.json'


# --- Google Drive Functions ---

def authenticate_google_drive():
    """Authenticates with Google Drive API, handles token refresh."""
    creds = None
    # The file token.json stores the user's access and refresh tokens, and is
    # created automatically when the authorization flow completes for the first time.
    if os.path.exists(GOOGLE_DRIVE_TOKEN_FILE):
        creds = Credentials.from_authorized_user_file(GOOGLE_DRIVE_TOKEN_FILE, GOOGLE_DRIVE_SCOPES)
    # If there are no (valid) credentials available, let the user log in.
    if not creds or not creds.valid:
        if creds and creds.expired and creds.refresh_token:
            logger.info("Google Drive token expired, attempting refresh.")
            try:
                creds.refresh(Request())
            except Exception as e:
                logger.error(f"Error refreshing Google Drive token: {e}")
                return None
        else:
            if not os.path.exists(GOOGLE_DRIVE_CLIENT_SECRET_FILE):
                logger.error(f"Google Drive client_secret.json not found at {GOOGLE_DRIVE_CLIENT_SECRET_FILE}. "
                             "Please download it from Google Cloud Console and place it in the script directory.")
                return None
            logger.info("Initiating Google Drive authentication flow (opening browser).")
            try:
                flow = InstalledAppFlow.from_client_secrets_file(
                    GOOGLE_DRIVE_CLIENT_SECRET_FILE, GOOGLE_DRIVE_SCOPES)
                creds = flow.run_local_server(port=0)
            except Exception as e:
                logger.error(f"Error during Google Drive local server authentication flow: {e}")
                return None
        # Save the credentials for the next run
        if creds:
            with open(GOOGLE_DRIVE_TOKEN_FILE, 'w') as token:
                token.write(creds.to_json())
            logger.info("Google Drive token saved successfully.")
        else:
            logger.error("Failed to obtain Google Drive credentials.")
            return None
    return build('drive', 'v3', credentials=creds)

def get_or_create_google_drive_folder(service, folder_path, parent_id=None):
    """
    Gets an existing folder or creates a new one (and its parents) in Google Drive.
    folder_path can be a single name or a nested path like 'Parent/Child/Grandchild'.
    """
    folder_names = folder_path.split('/')
    current_parent_id = parent_id

    for folder_name in folder_names:
        # Search for the folder within the current_parent_id
        query = f"name='{folder_name}' and mimeType='application/vnd.google-apps.folder' and trashed=false"
        if current_parent_id:
            query += f" and '{current_parent_id}' in parents"

        try:
            response = service.files().list(q=query, spaces='drive', fields='files(id, name)').execute()
            items = response.get('files', [])

            if items:
                # Folder found, update current_parent_id to this folder's ID
                current_parent_id = items[0]['id']
                logger.info(f"Found Google Drive folder: '{folder_name}' (ID: {current_parent_id})")
            else:
                # Folder not found, create it
                file_metadata = {
                    'name': folder_name,
                    'mimeType': 'application/vnd.google-apps.folder'
                }
                if current_parent_id:
                    file_metadata['parents'] = [current_parent_id]

                folder = service.files().create(body=file_metadata, fields='id').execute()
                current_parent_id = folder.get('id')
                logger.info(f"Created Google Drive folder: '{folder_name}' (ID: {current_parent_id})")
        except Exception as e:
            logger.error(f"Error getting or creating Google Drive folder '{folder_name}': {e}")
            return None # Return None if any step fails
            
    return current_parent_id # Return the ID of the innermost folder

# Chunk size for resumable Google Drive uploads (5 MB - sweet spot for performance/progress)
_GDRIVE_UPLOAD_CHUNK_SIZE = 5 * 1024 * 1024
# Max retries per chunk on transient errors
_GDRIVE_CHUNK_MAX_RETRIES = 3


def upload_to_google_drive(service, file_path, folder_id, progress_callback: Callable = None):
    """
    Uploads a file to Google Drive within a specified folder using chunked
    resumable uploads for reliability with large files.

    Args:
        service: Authenticated Google Drive API service instance.
        file_path: Local path of the file to upload.
        folder_id: Google Drive folder ID to upload into.
        progress_callback: Optional callable(percent: int, uploaded_mb: float, total_mb: float)
                           invoked after each chunk for progress reporting.
    """
    file_name = os.path.basename(file_path)
    file_size_bytes = os.path.getsize(file_path)
    file_size_mb = file_size_bytes / (1024 * 1024)

    file_metadata = {
        'name': file_name,
        'parents': [folder_id]
    }
    # Determine mimetype based on file extension, default to video/mp4
    mime_type = 'video/mp4'
    if file_name.lower().endswith('.mov'):
        mime_type = 'video/quicktime'
    elif file_name.lower().endswith('.avi'):
        mime_type = 'video/x-msvideo'
    elif file_name.lower().endswith('.webm'):
        mime_type = 'video/webm'

    media = MediaFileUpload(
        file_path,
        mimetype=mime_type,
        resumable=True,
        chunksize=_GDRIVE_UPLOAD_CHUNK_SIZE
    )

    logger.info(f"Starting Google Drive upload for '{file_name}' ({file_size_mb:.1f} MB) "
                f"in {_GDRIVE_UPLOAD_CHUNK_SIZE // (1024*1024)} MB chunks...")

    try:
        request = service.files().create(
            body=file_metadata,
            media_body=media,
            fields='id, webContentLink, webViewLink'
        )

        response = None
        last_progress_log_time = 0
        while response is None:
            chunk_retries = 0
            while True:
                try:
                    status, response = request.next_chunk()
                    break  # Chunk succeeded
                except Exception as chunk_err:
                    chunk_retries += 1
                    if chunk_retries > _GDRIVE_CHUNK_MAX_RETRIES:
                        logger.error(
                            f"Google Drive upload chunk failed after {_GDRIVE_CHUNK_MAX_RETRIES} retries: {chunk_err}"
                        )
                        raise  # Re-raise to be caught by outer handler
                    backoff = 2 ** chunk_retries
                    logger.warning(
                        f"Google Drive chunk upload error (retry {chunk_retries}/{_GDRIVE_CHUNK_MAX_RETRIES}, "
                        f"backoff {backoff}s): {chunk_err}"
                    )
                    time.sleep(backoff)

            if status is not None:
                percent = int(status.progress() * 100)
                uploaded_mb = (status.resumable_progress or 0) / (1024 * 1024)
                now = time.time()
                # Log at most once per second to avoid spam
                if now - last_progress_log_time >= 1.0:
                    sys.stdout.write(
                        f"\r\033[K\033[1;35mUploading:\033[0m {percent}% "
                        f"({uploaded_mb:.1f}/{file_size_mb:.1f} MB) → Google Drive"
                    )
                    sys.stdout.flush()
                    last_progress_log_time = now
                if progress_callback:
                    try:
                        progress_callback(percent, uploaded_mb, file_size_mb)
                    except Exception:
                        pass  # Never let callback errors kill the upload

        # Clear the in-place progress line and log final success
        sys.stdout.write("\r\033[K")
        sys.stdout.flush()

        file_id = response.get('id')
        web_view_link = response.get('webViewLink')
        logger.info(f"✅ File '{file_name}' uploaded to Google Drive ({file_size_mb:.1f} MB). File ID: {file_id}")

        # Make file publicly accessible - necessary for embedding on GitHub Pages
        # Check if permissions already exist to avoid errors on re-runs
        permissions = service.permissions().list(fileId=file_id).execute().get('permissions', [])
        public_permission_exists = any(p.get('type') == 'anyone' and p.get('role') == 'reader' for p in permissions)

        if not public_permission_exists:
            service.permissions().create(
                fileId=file_id,
                body={'role': 'reader', 'type': 'anyone'},
                fields='id'
            ).execute()
            logger.info(f"File '{file_name}' permissions updated to public.")
        else:
            logger.info(f"File '{file_name}' already has public permissions.")

        # Notify 100% complete
        if progress_callback:
            try:
                progress_callback(100, file_size_mb, file_size_mb)
            except Exception:
                pass

        return file_id, web_view_link
    except Exception as e:
        # Clear any lingering progress line
        sys.stdout.write("\r\033[K")
        sys.stdout.flush()
        logger.error(f"Error uploading '{file_name}' to Google Drive: {e}", exc_info=True)
        return None, None

def get_google_drive_embed_url(file_id):
    """Generates a Google Drive embed URL from a file ID using the /preview format."""
    if file_id:
        return f"https://drive.google.com/file/d/{file_id}/preview" # Changed to /preview
    return None

def delete_from_google_drive(service, file_id: str) -> bool:
    """Deletes a file from Google Drive."""
    try:
        service.files().delete(fileId=file_id).execute()
        logger.info(f"Successfully deleted file with ID: {file_id} from Google Drive.")
        return True
    except HttpError as e:
        # Idempotency: deleting an already-missing Drive file should not fail the overall delete flow.
        status = getattr(e, "status_code", None) or getattr(getattr(e, "resp", None), "status", None)
        if status == 404:
            logger.warning(
                f"Google Drive file already missing (treated as deleted): {file_id}. "
                f"Continuing GitHub cleanup."
            )
            return True
        logger.error(f"Error deleting file with ID: {file_id} from Google Drive: {e}", exc_info=True)
        return False
    except Exception as e:
        logger.error(f"Error deleting file with ID: {file_id} from Google Drive: {e}", exc_info=True)
        return False

# --- GitHub Functions ---

def authenticate_github():
    """Authenticates with GitHub API using a Personal Access Token."""
    if not GITHUB_ACCESS_TOKEN or len(GITHUB_ACCESS_TOKEN) < 30: # Basic check for placeholder/empty token
        logger.error("GITHUB_ACCESS_TOKEN is not set or is invalid. Cannot authenticate with GitHub.")
        return None
    try:
        return Github(GITHUB_ACCESS_TOKEN)
    except Exception as e:
        logger.error(f"Error authenticating with GitHub: {e}")
        return None

def get_github_repo(g):
    """Gets the GitHub repository object."""
    if not GITHUB_USERNAME or not GITHUB_REPO_NAME:
        logger.error("GITHUB_USERNAME or GITHUB_REPO_NAME is not set. Cannot get GitHub repository.")
        return None
    try:
        return g.get_user(GITHUB_USERNAME).get_repo(GITHUB_REPO_NAME)
    except Exception as e:
        logger.error(f"Error getting GitHub repository '{GITHUB_USERNAME}/{GITHUB_REPO_NAME}': {e}")
        logger.error("Please ensure the GitHub username and repository name are correct and the PAT has 'repo' scope.")
        return None

def get_github_file_content(repo, file_path, branch):
    """Fetches content of a file from GitHub."""
    try:
        contents = repo.get_contents(file_path, ref=branch)
        return contents.decoded_content.decode('utf-8')
    except Exception as e:
        logger.warning(f"File '{file_path}' not found or error fetching from GitHub: {e}. Assuming empty or new file.")
        return None

def update_and_commit_github_file(repo, file_path, new_content, commit_message, branch, max_retries: int = 3):
    """
    Updates a file and commits it to GitHub.
    Returns the SHA of the new commit if successful, otherwise None.
    """
    for attempt in range(1, max_retries + 1):
        try:
            # Get the current file SHA to update it
            sha = None
            try:
                contents = repo.get_contents(file_path, ref=branch)
                sha = contents.sha
                logger.info(f"Found existing file '{file_path}' with SHA: {sha}")
            except Exception:
                # File does not exist, so we'll create it (no SHA needed)
                logger.info(f"File '{file_path}' does not exist, will create it.")

            if sha:
                commit = repo.update_file(file_path, commit_message, new_content, sha, branch=branch)
                logger.info(f"Successfully updated and committed '{file_path}' to '{branch}' branch. Commit SHA: {commit['commit'].sha}")
            else:
                commit = repo.create_file(file_path, commit_message, new_content, branch=branch)
                logger.info(f"Successfully created and committed '{file_path}' to '{branch}' branch. Commit SHA: {commit['commit'].sha}")

            return commit['commit'].sha # Return the commit SHA
        except GithubException as e:
            status = getattr(e, "status", None)
            is_conflict = status == 409 or "does not match" in str(e).lower()
            if is_conflict and attempt < max_retries:
                delay = 0.6 * attempt
                logger.warning(
                    f"GitHub conflict while committing '{file_path}' (attempt {attempt}/{max_retries}). "
                    f"Retrying in {delay:.1f}s..."
                )
                time.sleep(delay)
                continue

            logger.error(f"Error committing file '{file_path}' to GitHub: {e}", exc_info=True)
            return None
        except Exception as e:
            logger.error(f"Error committing file '{file_path}' to GitHub: {e}", exc_info=True)
            return None

    return None


def _load_videos_json_and_sha(repo, branch: str) -> tuple[list, Optional[str]]:
    """Loads videos.json list and current blob SHA (if file exists)."""
    try:
        contents = repo.get_contents(GITHUB_VIDEOS_JSON_PATH, ref=branch)
        raw = contents.decoded_content.decode('utf-8')
        parsed = json.loads(raw) if raw else []
        if not isinstance(parsed, list):
            parsed = []
        return parsed, contents.sha
    except Exception:
        return [], None


def _video_entries_match(a: dict, b: dict) -> bool:
    """Best-effort identity matching for videos.json entries."""
    a_drive = str(a.get("googleDriveFileId") or "").strip()
    b_drive = str(b.get("googleDriveFileId") or "").strip()
    if a_drive and b_drive and a_drive == b_drive:
        return True

    a_commit = str(a.get("commitSha") or "").strip()
    b_commit = str(b.get("commitSha") or "").strip()
    if a_commit and b_commit and a_commit == b_commit:
        return True

    a_download = str(a.get("downloadUrl") or "").strip()
    b_download = str(b.get("downloadUrl") or "").strip()
    if a_download and b_download and a_download == b_download:
        return True

    a_embed = str(a.get("embedUrl") or "").strip()
    b_embed = str(b.get("embedUrl") or "").strip()
    if a_embed and b_embed and a_embed == b_embed:
        return True

    a_title = str(a.get("title") or "").strip()
    b_title = str(b.get("title") or "").strip()
    a_ts = int(a.get("timestamp") or 0)
    b_ts = int(b.get("timestamp") or 0)
    return bool(a_title and b_title and a_title == b_title and a_ts > 0 and b_ts > 0 and abs(a_ts - b_ts) <= 5)


def _merge_video_entry(existing: dict, incoming: dict) -> dict:
    merged = dict(existing or {})
    for key, value in incoming.items():
        if value is None:
            continue
        if isinstance(value, str) and value.strip() == "":
            continue
        merged[key] = value
    if "timestamp" in incoming:
        try:
            merged["timestamp"] = int(incoming.get("timestamp") or merged.get("timestamp") or int(time.time()))
        except Exception:
            pass
    return merged


def upsert_video_entry_merge_safe(
    repo,
    entry: dict,
    commit_message: str,
    branch: str,
    max_retries: int = 6,
) -> Optional[str]:
    """Upserts a video entry into videos.json with conflict-safe merge retries."""
    candidate = dict(entry or {})
    for attempt in range(1, max_retries + 1):
        videos, sha = _load_videos_json_and_sha(repo, branch)

        if not isinstance(videos, list):
            videos = []

        match_index = -1
        for idx, current in enumerate(videos):
            if isinstance(current, dict) and _video_entries_match(current, candidate):
                match_index = idx
                break

        if match_index >= 0:
            merged = _merge_video_entry(videos[match_index], candidate)
            del videos[match_index]
            videos.insert(0, merged)
        else:
            videos.insert(0, candidate)

        content = json.dumps(videos, indent=4)
        try:
            if sha:
                commit = repo.update_file(GITHUB_VIDEOS_JSON_PATH, commit_message, content, sha, branch=branch)
            else:
                commit = repo.create_file(GITHUB_VIDEOS_JSON_PATH, commit_message, content, branch=branch)
            commit_sha = commit['commit'].sha
            logger.info(
                f"Upserted videos.json entry for '{candidate.get('title', 'unknown')}' "
                f"on attempt {attempt}/{max_retries}. Commit SHA: {commit_sha}"
            )
            return commit_sha
        except GithubException as e:
            status = getattr(e, "status", None)
            is_conflict = status == 409 or "does not match" in str(e).lower()
            if is_conflict and attempt < max_retries:
                delay = 0.4 * attempt
                logger.warning(
                    f"Conflict while upserting videos.json (attempt {attempt}/{max_retries}). "
                    f"Retrying in {delay:.1f}s..."
                )
                time.sleep(delay)
                continue
            logger.error(f"Failed upserting videos.json entry: {e}", exc_info=True)
            return None
        except Exception as e:
            logger.error(f"Failed upserting videos.json entry: {e}", exc_info=True)
            return None

    return None


def _video_entry_exists(repo, branch: str, entry: dict) -> bool:
    """Checks whether videos.json already contains an entry matching candidate identity."""
    videos, _ = _load_videos_json_and_sha(repo, branch)
    if not isinstance(videos, list):
        return False
    for current in videos:
        if isinstance(current, dict) and _video_entries_match(current, entry):
            return True
    return False


def _video_entry_has_commit_sha(repo, branch: str, entry: dict, expected_commit_sha: str) -> bool:
    """Checks whether a matched videos.json entry has the expected commitSha persisted."""
    expected = str(expected_commit_sha or "").strip()
    if not expected:
        return False

    videos, _ = _load_videos_json_and_sha(repo, branch)
    if not isinstance(videos, list):
        return False

    for current in videos:
        if not isinstance(current, dict):
            continue
        if _video_entries_match(current, entry):
            current_commit = str(current.get("commitSha") or "").strip()
            return current_commit == expected
    return False

def get_commit_details(commit_sha: str):
    """
    Fetches details for a given commit SHA from GitHub.
    Returns a dictionary with commit info or None if not found/error.
    """
    g = authenticate_github()
    if not g:
        logger.error("GitHub authentication failed for get_commit_details.")
        return None
    
    repo = get_github_repo(g)
    if not repo:
        logger.error("Could not access GitHub repository for get_commit_details.")
        return None
    
    try:
        commit = repo.get_commit(sha=commit_sha)
        return {
            "sha": commit.sha,
            "author_name": commit.author.name if commit.author else "Unknown",
            "author_email": commit.author.email if commit.author else "Unknown",
            "date": commit.commit.author.date.isoformat(),
            "message": commit.commit.message,
            "html_url": commit.html_url
        }
    except Exception as e:
        logger.error(f"Error fetching commit details for SHA {commit_sha}: {e}")
        return None

# --- Main Integration Functions ---

async def update_github_pages_with_video(processed_video_path: str, original_video_title: str, description: str = "", progress_callback: Callable = None) -> Tuple[bool, Optional[str], Optional[str]]:
    """
    Uploads processed video to Google Drive, generates embed link,
    and updates videos.json on GitHub Pages.

    Args:
        processed_video_path: Path to the processed video file.
        original_video_title: Title for the video entry.
        description: Description for the video entry.
        progress_callback: Optional callable(percent, uploaded_mb, total_mb)
                           forwarded to the Google Drive upload for live progress.
    Returns a tuple: (success_status: bool, commit_sha: Optional[str], download_url: Optional[str])
    """
    def _run_update_flow() -> Tuple[bool, Optional[str], Optional[str]]:
        logger.info(f"Starting GitHub Pages update process for: {processed_video_path}")

        # 1. Authenticate Google Drive
        drive_service = authenticate_google_drive()
        if not drive_service:
            logger.error("Google Drive authentication failed. Aborting GitHub Pages update.")
            return False, None, None

        # 2. Get or Create Google Drive Output Folder
        folder_id = get_or_create_google_drive_folder(drive_service, GOOGLE_DRIVE_OUTPUT_FOLDER_NAME)
        if not folder_id:
            logger.error("Could not get or create Google Drive output folder. Aborting GitHub Pages update.")
            return False, None, None

        # 3. Upload Video to Google Drive
        if not os.path.exists(processed_video_path):
            logger.error(f"Processed video file not found on disk: '{processed_video_path}'. "
                         f"Check that ot.py saved it at exactly this path (watch for dot-in-title truncation bugs).")
            return False, None, None
        file_id, web_view_link = upload_to_google_drive(
            drive_service, processed_video_path, folder_id,
            progress_callback=progress_callback
        )
        if not file_id:
            logger.error(f"Failed to upload {processed_video_path} to Google Drive. Aborting GitHub Pages update.")
            return False, None, None

        # CORRECTED LINE: Ensure the embed URL uses the /preview format
        embed_url = get_google_drive_embed_url(file_id)
        if not embed_url:
            logger.error("Failed to generate Google Drive embed URL. Aborting GitHub Pages update.")
            return False, None, None

        logger.info(f"Google Drive Embed URL: {embed_url}")
        logger.info(f"Google Drive Web View Link: {web_view_link}")

        # 4. Authenticate GitHub
        g = authenticate_github()
        if not g:
            logger.error("GitHub authentication failed. Aborting GitHub Pages update.")
            return False, None, None

        repo = get_github_repo(g)
        if not repo:
            logger.error("Could not access GitHub repository. Aborting GitHub Pages update.")
            return False, None, None

        # 5. Prepare new video entry
        new_video_entry = {
            "title": original_video_title,
            "description": description,
            "embedUrl": embed_url,
            "downloadUrl": web_view_link, # Provide webViewLink for direct download/view
            "timestamp": int(time.time()), # Unix timestamp for sorting
            "googleDriveFileId": file_id, # Store for potential future management
            "commitSha": "" # Kept empty to avoid mandatory second commit backfill.
        }
        commit_message = f"Add processed video: {original_video_title}"

        # Notify caller that upload is done and we're now committing to GitHub
        if progress_callback:
            try:
                progress_callback(-1, 0, 0)  # Special sentinel: -1 means "committing to GitHub"
            except Exception:
                pass

        # 6. Merge-safe upsert into videos.json (initial publish commit)
        initial_commit_sha = upsert_video_entry_merge_safe(
            repo,
            new_video_entry,
            commit_message,
            GITHUB_BRANCH,
        )

        if not initial_commit_sha:
            logger.error("Failed to make initial commit for new video entry.")
            return False, None, None

        logger.info(f"Successfully created initial commit for '{original_video_title}'. SHA: {initial_commit_sha}")

        # 7. Self-check: ensure entry exists after initial publish commit.
        if not _video_entry_exists(repo, GITHUB_BRANCH, new_video_entry):
            logger.error(
                f"Publish verification failed for '{original_video_title}' after initial upsert. "
                "Aborting to avoid silent publish drift."
            )
            return False, None, None

        # 8. Stamp the entry with the initial commit SHA so admin commit-details always work.
        stamped_entry = dict(new_video_entry)
        stamped_entry["commitSha"] = initial_commit_sha
        metadata_commit_sha = upsert_video_entry_merge_safe(
            repo,
            stamped_entry,
            f"Stamp commit SHA metadata: {original_video_title}",
            GITHUB_BRANCH,
        )
        if not metadata_commit_sha:
            logger.error(
                f"Failed to stamp commitSha metadata for '{original_video_title}'. "
                "Aborting to avoid publishing entries without commit identity."
            )
            return False, None, None

        if not _video_entry_has_commit_sha(repo, GITHUB_BRANCH, stamped_entry, initial_commit_sha):
            logger.error(
                f"commitSha verification failed for '{original_video_title}' after metadata stamp commit "
                f"{metadata_commit_sha}."
            )
            return False, None, None

        logger.info(
            f"Publish verification passed for '{original_video_title}' with commitSha={initial_commit_sha}. "
            f"Metadata commit SHA: {metadata_commit_sha}"
        )
        return True, initial_commit_sha, web_view_link

    return await asyncio.to_thread(_run_update_flow)

async def delete_video_from_drive_and_github(
    file_id: Optional[str] = None,
    commit_sha: Optional[str] = None,
    video_title: Optional[str] = None,
    video_timestamp: Optional[int] = None,
) -> bool:
    """
    Deletes a video from Google Drive and removes its entry from videos.json on GitHub.
    """
    def _run_delete_flow() -> bool:
        logger.info(
            "Initiating deletion request with identifiers: "
            f"file_id={file_id}, commit_sha={commit_sha}, "
            f"title={video_title}, timestamp={video_timestamp}"
        )

        if not any([file_id, commit_sha, video_title]):
            logger.error("Deletion requires at least one identifier (file_id, commit_sha, or title).")
            return False

        # 1. Try Google Drive deletion first, but never abort GitHub cleanup on Drive-side failures.
        drive_delete_success = False
        drive_service = authenticate_google_drive()
        if not drive_service:
            logger.warning("Google Drive authentication failed. Continuing with GitHub cleanup only.")
        else:
            if file_id:
                drive_delete_success = delete_from_google_drive(drive_service, file_id)
                if not drive_delete_success:
                    logger.warning(
                        f"Could not delete file {file_id} from Google Drive. "
                        "Continuing with GitHub cleanup to keep frontend state consistent."
                    )
            else:
                logger.info("No direct Drive file ID provided; Drive deletion will use matched videos.json entries.")

        # 2. Authenticate GitHub
        g = authenticate_github()
        if not g:
            logger.error("GitHub authentication failed. Cannot clean up videos.json.")
            return False

        repo = get_github_repo(g)
        if not repo:
            logger.error("Could not access GitHub repository. Cannot clean up videos.json.")
            return False

        # 3. Fetch existing videos.json content
        existing_content = get_github_file_content(repo, GITHUB_VIDEOS_JSON_PATH, GITHUB_BRANCH)
        videos_data = []
        if existing_content:
            try:
                videos_data = json.loads(existing_content)
                if not isinstance(videos_data, list):
                    logger.warning(f"{GITHUB_VIDEOS_JSON_PATH} content is not a list. Treating as empty list for delete safety.")
                    videos_data = []
            except json.JSONDecodeError:
                logger.warning(f"Error decoding existing {GITHUB_VIDEOS_JSON_PATH}. Treating as empty list for delete safety.")
                videos_data = []
        else:
            logger.warning(f"{GITHUB_VIDEOS_JSON_PATH} is empty or not found. Nothing to delete from GitHub list.")
            # Idempotent success: Drive was attempted above; frontend state is already effectively clean.
            return True

        # 4. Filter out the video entry
        original_video_title = video_title or "Unknown Video"
        initial_count = len(videos_data)
        matched_entries = []

        def _matches(video: dict) -> bool:
            video_file_id = str(video.get("googleDriveFileId") or "").strip()
            video_commit_sha = str(video.get("commitSha") or "").strip()
            video_title_value = str(video.get("title") or "").strip()

            matches_file_id = bool(file_id and video_file_id == str(file_id).strip())
            matches_commit_sha = bool(commit_sha and video_commit_sha == str(commit_sha).strip())

            matches_title = bool(video_title and video_title_value == str(video_title).strip())
            matches_title_and_timestamp = False
            if matches_title and video_timestamp is not None:
                try:
                    matches_title_and_timestamp = int(video.get("timestamp")) == int(video_timestamp)
                except Exception:
                    matches_title_and_timestamp = False

            # Priority: exact file_id/commitSha. Title requires timestamp when provided.
            return matches_file_id or matches_commit_sha or matches_title_and_timestamp or (matches_title and video_timestamp is None)

        for video in videos_data:
            if _matches(video):
                matched_entries.append(video)

        matched_drive_ids = [
            str(entry.get("googleDriveFileId") or "").strip()
            for entry in matched_entries
            if entry.get("googleDriveFileId")
        ]

        if drive_service and not file_id and matched_drive_ids:
            for matched_drive_id in matched_drive_ids:
                deleted = delete_from_google_drive(drive_service, matched_drive_id)
                if not deleted:
                    logger.warning(
                        f"Could not delete matched Drive file {matched_drive_id}. Continuing with GitHub cleanup."
                    )

        new_videos_data = [video for video in videos_data if not _matches(video)]
        
        if len(new_videos_data) < initial_count:
            # Find the title of the deleted video for the commit message
            deleted_video_entry = matched_entries[0] if matched_entries else None
            if deleted_video_entry:
                original_video_title = deleted_video_entry.get("title", original_video_title)
            
            new_json_content = json.dumps(new_videos_data, indent=4)
            identifier_hint = commit_sha or file_id or f"{video_title or 'unknown'}"
            if commit_sha:
                short_ref = str(commit_sha)[:7]
                commit_message = f"Delete processed video: {original_video_title} (ref {short_ref})"
            else:
                commit_message = f"Delete processed video: {original_video_title} (ref: {identifier_hint})"

            # 5. Commit updated videos.json to GitHub
            github_commit_success = update_and_commit_github_file(repo, GITHUB_VIDEOS_JSON_PATH, new_json_content, commit_message, GITHUB_BRANCH)
            
            if github_commit_success:
                logger.info(f"Successfully removed entry for '{original_video_title}' from {GITHUB_VIDEOS_JSON_PATH} and committed.")
                return True
            else:
                logger.error(f"Failed to commit updated {GITHUB_VIDEOS_JSON_PATH} after deleting from Drive.")
                return False
        else:
            logger.warning(
                f"No matching entry found in {GITHUB_VIDEOS_JSON_PATH} for "
                f"file_id={file_id}, commit_sha={commit_sha}, title={video_title}, timestamp={video_timestamp}. "
                "Treating as already deleted (idempotent success)."
            )
            return True

    return await asyncio.to_thread(_run_delete_flow)


# Example usage (for testing this script directly, not part of tg.py integration)
async def test_github_pages_updater():
    # This path needs to be a real video file on your system for testing
    test_video_file = "path/to/your/test_video.mp4"
    if not os.path.exists(test_video_file):
        logger.error(f"Test video file not found: {test_video_file}. Please update path or create file.")
        return

    # Set environment variables for testing:
    # export GITHUB_ACCESS_TOKEN="YOUR_TOKEN"
    # export GITHUB_USERNAME="YOUR_USERNAME"
    # export GITHUB_REPO_NAME="YOUR_REPO_NAME"

    # Ensure you have client_secret.json and token.json for Google Drive API
    # The first run will open a browser for Google authentication.

    success, commit_sha, download_url = await update_github_pages_with_video(
        processed_video_path=test_video_file,
        original_video_title=f"Test Video {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        description="This is a test video uploaded via the script."
    )
    if success:
        print(f"\nTest update successful! Commit SHA: {commit_sha}, Download URL: {download_url}")
    else:
        print("\nTest update failed.")

# Example usage for deletion (for testing this script directly)
async def test_delete_video():
    # Replace with an actual Google Drive File ID from your videos.json
    file_id_to_delete = "YOUR_GOOGLE_DRIVE_FILE_ID_HERE" 
    if file_id_to_delete == "YOUR_GOOGLE_DRIVE_FILE_ID_HERE":
        logger.error("Please replace 'YOUR_GOOGLE_DRIVE_FILE_ID_HERE' with a real file ID to test deletion.")
        return

    success = await delete_video_from_drive_and_github(file_id_to_delete)
    if success:
        print(f"\nTest deletion of {file_id_to_delete} successful!")
    else:
        print(f"\nTest deletion of {file_id_to_delete} failed.")


if __name__ == "__main__":
    # To run this directly for testing:
    # 1. Make sure you have client_secret.json in the same directory.
    # 2. Set GITHUB_ACCESS_TOKEN, GITHUB_USERNAME, GITHUB_REPO_NAME environment variables.
    # 3. Replace "path/to/your/test_video.mp4" with a real video file for update test.
    # 4. Replace "YOUR_GOOGLE_DRIVE_FILE_ID_HERE" with a real file ID for delete test.
    # 5. Uncomment the asyncio.run(...) lines below for the test you want to run.
    import asyncio
    # asyncio.run(test_github_pages_updater())
    # asyncio.run(test_delete_video())
    logger.info("This script is primarily designed to be imported and used by tg.py.")
    logger.info("Uncomment the test functions and set up credentials to test directly.")
