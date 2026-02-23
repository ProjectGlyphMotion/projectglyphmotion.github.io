import os
import json
import logging
import time
from datetime import datetime
from typing import Tuple, Optional

# Google Drive API imports
from google.oauth2.credentials import Credentials
from google_auth_oauthlib.flow import InstalledAppFlow
from google.auth.transport.requests import Request
from googleapiclient.discovery import build
from googleapiclient.http import MediaFileUpload

# GitHub API imports
from github import Github, InputGitTreeElement

# --- Logging Setup ---
logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s", level=logging.INFO)
logger = logging.getLogger(__name__)

# --- Configuration (IMPORTANT: Use Environment Variables for Production) ---
# Hardcoded values will be used first, environment variables as fallback.
# For deployment, strongly consider using only environment variables for security.

# Google Drive API
GOOGLE_DRIVE_SCOPES = ['https://www.googleapis.com/auth/drive.file']
# Hardcoded path for client_secret.json (replace with your actual path if different)
_HARDCODED_GOOGLE_DRIVE_CLIENT_SECRET_FILE = 'client_secret.json'
GOOGLE_DRIVE_CLIENT_SECRET_FILE = _HARDCODED_GOOGLE_DRIVE_CLIENT_SECRET_FILE or os.getenv('GOOGLE_DRIVE_CLIENT_SECRET_FILE', 'client_secret.json')

# Hardcoded path for token.json (replace with your actual path if different)
_HARDCODED_GOOGLE_DRIVE_TOKEN_FILE = 'token.json'
GOOGLE_DRIVE_TOKEN_FILE = _HARDCODED_GOOGLE_DRIVE_TOKEN_FILE or os.getenv('GOOGLE_DRIVE_TOKEN_FILE', 'token.json')

# Name of the parent folder in Google Drive for processed videos
# Changed to support nested path
GOOGLE_DRIVE_OUTPUT_FOLDER_NAME = 'ObjectTrackerMaster/output'


# GitHub API
# Hardcoded Personal Access Token (REPLACE WITH YOUR ACTUAL TOKEN)
# WARNING: Exposing PAT directly in code is not recommended for production.
# Use environment variables or a secure secret management system.
_HARDCODED_GITHUB_ACCESS_TOKEN = "YOUR_GITHUB_PERSONAL_ACCESS_TOKEN_HERE" 
GITHUB_ACCESS_TOKEN = _HARDCODED_GITHUB_ACCESS_TOKEN if _HARDCODED_GITHUB_ACCESS_TOKEN != "YOUR_GITHUB_PERSONAL_ACCESS_TOKEN_HERE" else os.getenv('GITHUB_ACCESS_TOKEN')
if not GITHUB_ACCESS_TOKEN or GITHUB_ACCESS_TOKEN == "YOUR_GITHUB_PERSONAL_ACCESS_TOKEN_HERE":
    logger.error("GITHUB_ACCESS_TOKEN is not set or is still the placeholder. GitHub operations will fail!")

# Hardcoded GitHub username (REPLACE WITH YOUR ACTUAL USERNAME)
_HARDCODED_GITHUB_USERNAME = "ProjectGlyphMotion" # <--- CHANGE THIS TO YOUR GITHUB USERNAME
# Note: This should be your GitHub username, not an email.
GITHUB_USERNAME = _HARDCODED_GITHUB_USERNAME if _HARDCODED_GITHUB_USERNAME != "YOUR_GITHUB_USERNAME_HERE" else os.getenv('GITHUB_USERNAME')

# Hardcoded GitHub repository name (REPLACE WITH YOUR ACTUAL REPO NAME)
_HARDCODED_GITHUB_REPO_NAME = "ProjectGlyphMotion.github.io" # <--- CHANGE THIS TO YOUR REPO NAME
GITHUB_REPO_NAME = _HARDCODED_GITHUB_REPO_NAME if _HARDCODED_GITHUB_REPO_NAME != "YOUR_GITHUB_REPO_NAME_HERE" else os.getenv('GITHUB_REPO_NAME')

# Branch to commit to (usually 'main' or 'master' for GitHub Pages)
GITHUB_BRANCH = 'main'
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

def upload_to_google_drive(service, file_path, folder_id):
    """Uploads a file to Google Drive within a specified folder."""
    file_name = os.path.basename(file_path)
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
    
    media = MediaFileUpload(file_path, mimetype=mime_type, resumable=True) 
    try:
        file = service.files().create(body=file_metadata, media_body=media, fields='id, webContentLink, webViewLink').execute()
        logger.info(f"File '{file_name}' uploaded to Google Drive. File ID: {file.get('id')}")
        
        # Make file publicly accessible - necessary for embedding on GitHub Pages
        # Check if permissions already exist to avoid errors on re-runs
        permissions = service.permissions().list(fileId=file.get('id')).execute().get('permissions', [])
        public_permission_exists = any(p.get('type') == 'anyone' and p.get('role') == 'reader' for p in permissions)

        if not public_permission_exists:
            service.permissions().create(
                fileId=file.get('id'),
                body={'role': 'reader', 'type': 'anyone'},
                fields='id'
            ).execute()
            logger.info(f"File '{file_name}' permissions updated to public.")
        else:
            logger.info(f"File '{file_name}' already has public permissions.")

        return file.get('id'), file.get('webViewLink') # webViewLink is good for embedding
    except Exception as e:
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

def update_and_commit_github_file(repo, file_path, new_content, commit_message, branch):
    """
    Updates a file and commits it to GitHub.
    Returns the SHA of the new commit if successful, otherwise None.
    """
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
    except Exception as e:
        logger.error(f"Error committing file '{file_path}' to GitHub: {e}", exc_info=True)
        return None

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

async def update_github_pages_with_video(processed_video_path: str, original_video_title: str, description: str = "") -> Tuple[bool, Optional[str]]:
    """
    Uploads processed video to Google Drive, generates embed link,
    and updates videos.json on GitHub Pages.
    Returns a tuple: (success_status: bool, commit_sha: Optional[str])
    """
    logger.info(f"Starting GitHub Pages update process for: {processed_video_path}")

    # 1. Authenticate Google Drive
    drive_service = authenticate_google_drive()
    if not drive_service:
        logger.error("Google Drive authentication failed. Aborting GitHub Pages update.")
        return False, None

    # 2. Get or Create Google Drive Output Folder
    folder_id = get_or_create_google_drive_folder(drive_service, GOOGLE_DRIVE_OUTPUT_FOLDER_NAME)
    if not folder_id:
        logger.error("Could not get or create Google Drive output folder. Aborting GitHub Pages update.")
        return False, None

    # 3. Upload Video to Google Drive
    if not os.path.exists(processed_video_path):
        logger.error(f"Processed video file not found on disk: '{processed_video_path}'. "
                     f"Check that ot.py saved it at exactly this path (watch for dot-in-title truncation bugs).")
        return False, None
    file_id, web_view_link = upload_to_google_drive(drive_service, processed_video_path, folder_id)
    if not file_id:
        logger.error(f"Failed to upload {processed_video_path} to Google Drive. Aborting GitHub Pages update.")
        return False, None

    # CORRECTED LINE: Ensure the embed URL uses the /preview format
    embed_url = get_google_drive_embed_url(file_id)
    if not embed_url:
        logger.error("Failed to generate Google Drive embed URL. Aborting GitHub Pages update.")
        return False, None

    logger.info(f"Google Drive Embed URL: {embed_url}")
    logger.info(f"Google Drive Web View Link: {web_view_link}")

    # 4. Authenticate GitHub
    g = authenticate_github()
    if not g:
        logger.error("GitHub authentication failed. Aborting GitHub Pages update.")
        return False, None

    repo = get_github_repo(g)
    if not repo:
        logger.error("Could not access GitHub repository. Aborting GitHub Pages update.")
        return False, None

    # 5. Fetch existing videos.json content
    existing_content = get_github_file_content(repo, GITHUB_VIDEOS_JSON_PATH, GITHUB_BRANCH)
    videos_data = []
    if existing_content:
        try:
            videos_data = json.loads(existing_content)
            if not isinstance(videos_data, list): # Ensure it's a list
                logger.warning(f"{GITHUB_VIDEOS_JSON_PATH} content is not a list. Initializing as empty list.")
                videos_data = []
        except json.JSONDecodeError:
            logger.error(f"Error decoding existing {GITHUB_VIDEOS_JSON_PATH}. Initializing as empty list.")
            videos_data = []

    # 6. Prepare new video entry
    # Initially, commitSha is None. It will be updated in a second commit.
    new_video_entry = {
        "title": original_video_title,
        "description": description,
        "embedUrl": embed_url,
        "downloadUrl": web_view_link, # Provide webViewLink for direct download/view
        "timestamp": int(time.time()), # Unix timestamp for sorting
        "googleDriveFileId": file_id, # Store for potential future management
        "commitSha": None # Placeholder for commit SHA
    }

    # Add the new video entry to the beginning of the list (most recent first)
    videos_data.insert(0, new_video_entry)

    new_json_content = json.dumps(videos_data, indent=4)
    commit_message = f"Add processed video: {original_video_title}"

    # 7. Commit updated videos.json to GitHub (initial commit)
    initial_commit_sha = update_and_commit_github_file(repo, GITHUB_VIDEOS_JSON_PATH, new_json_content, commit_message, GITHUB_BRANCH)

    if initial_commit_sha:
        logger.info(f"Successfully created initial commit for '{original_video_title}'. SHA: {initial_commit_sha}")
        
        # Now, update the commitSha for the newly added video in videos_data
        # This requires fetching the file again or carefully updating the local copy
        
        # Fetch the updated content (which now includes the new video)
        updated_content_after_first_commit = get_github_file_content(repo, GITHUB_VIDEOS_JSON_PATH, GITHUB_BRANCH)
        if updated_content_after_first_commit:
            updated_videos_data = json.loads(updated_content_after_first_commit)
            # Find the video we just added (it's the first one, or by file_id) and set its commitSha
            for video in updated_videos_data:
                if video.get("googleDriveFileId") == file_id and video.get("commitSha") is None:
                    video["commitSha"] = initial_commit_sha # Use the SHA from the first commit
                    break
            
            final_json_content = json.dumps(updated_videos_data, indent=4)
            final_commit_message = f"Update commit SHA for: {original_video_title} (ref {initial_commit_sha[:7]})"
            
            # Commit the file again with the commit SHA included
            # This is a temporary workaround for the limitation of the GitHub API which returns the commit SHA after the commit is made.
            # In a real-world scenario, you might want to consider using Git operations locally or a different approach for this.
            final_commit_success = update_and_commit_github_file(repo, GITHUB_VIDEOS_JSON_PATH, final_json_content, final_commit_message, GITHUB_BRANCH)
            if final_commit_success:
                logger.info(f"Successfully updated commit SHA for video: {original_video_title}")
                return True, initial_commit_sha # Return success and the initial commit SHA
            else:
                logger.error(f"Failed to update commit SHA for video: {original_video_title}")
                return False, None
        else:
            logger.error("Could not fetch updated videos.json content after initial commit.")
            return False, None
    else:
        logger.error("Failed to make initial commit for new video entry.")
        return False, None

async def delete_video_from_drive_and_github(file_id: str) -> bool:
    """
    Deletes a video from Google Drive and removes its entry from videos.json on GitHub.
    """
    logger.info(f"Initiating deletion for Google Drive File ID: {file_id}")

    # 1. Authenticate Google Drive
    drive_service = authenticate_google_drive()
    if not drive_service:
        logger.error("Google Drive authentication failed. Aborting video deletion.")
        return False

    # 2. Delete file from Google Drive
    drive_delete_success = delete_from_google_drive(drive_service, file_id)
    if not drive_delete_success:
        logger.error(f"Failed to delete file {file_id} from Google Drive. Aborting GitHub update.")
        return False

    # 3. Authenticate GitHub
    g = authenticate_github()
    if not g:
        logger.error("GitHub authentication failed. Aborting GitHub update for deletion.")
        return False

    repo = get_github_repo(g)
    if not repo:
        logger.error("Could not access GitHub repository. Aborting GitHub update for deletion.")
        return False

    # 4. Fetch existing videos.json content
    existing_content = get_github_file_content(repo, GITHUB_VIDEOS_JSON_PATH, GITHUB_BRANCH)
    videos_data = []
    if existing_content:
        try:
            videos_data = json.loads(existing_content)
            if not isinstance(videos_data, list):
                logger.warning(f"{GITHUB_VIDEOS_JSON_PATH} content is not a list. Cannot delete entry.")
                return False
        except json.JSONDecodeError:
            logger.error(f"Error decoding existing {GITHUB_VIDEOS_JSON_PATH}. Cannot delete entry.")
            return False
    else:
        logger.warning(f"{GITHUB_VIDEOS_JSON_PATH} is empty or not found. No entry to delete.")
        return False

    # 5. Filter out the video entry
    original_video_title = "Unknown Video"
    initial_count = len(videos_data)
    new_videos_data = [video for video in videos_data if video.get("googleDriveFileId") != file_id]
    
    if len(new_videos_data) < initial_count:
        # Find the title of the deleted video for the commit message
        deleted_video_entry = next((video for video in videos_data if video.get("googleDriveFileId") == file_id), None)
        if deleted_video_entry:
            original_video_title = deleted_video_entry.get("title", original_video_title)
        
        new_json_content = json.dumps(new_videos_data, indent=4)
        commit_message = f"Delete processed video: {original_video_title} (ID: {file_id})"

        # 6. Commit updated videos.json to GitHub
        github_commit_success = update_and_commit_github_file(repo, GITHUB_VIDEOS_JSON_PATH, new_json_content, commit_message, GITHUB_BRANCH)
        
        if github_commit_success:
            logger.info(f"Successfully removed entry for '{original_video_title}' from {GITHUB_VIDEOS_JSON_PATH} and committed.")
            return True
        else:
            logger.error(f"Failed to commit updated {GITHUB_VIDEOS_JSON_PATH} after deleting from Drive.")
            return False
    else:
        logger.warning(f"Video with ID {file_id} not found in {GITHUB_VIDEOS_JSON_PATH}. No changes to commit.")
        return False


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

    success, commit_sha = await update_github_pages_with_video(
        processed_video_path=test_video_file,
        original_video_title=f"Test Video {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        description="This is a test video uploaded via the script."
    )
    if success:
        print(f"\nTest update successful! Commit SHA: {commit_sha}")
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
