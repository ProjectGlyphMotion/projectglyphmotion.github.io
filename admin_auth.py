# admin_auth.py
import bcrypt
import time
import json
import os
import re # For regex-based file parsing/editing
import logging

# --- Logging Setup ---
logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s", level=logging.INFO)
logger = logging.getLogger(__name__)

# --- Admin Credentials Storage (SECURITY NOTE: This file itself must be protected on the server) ---
# IMPORTANT: This dictionary stores usernames and their bcrypt hashes.
# The plaintext password is included as a comment for easy reference during *manual* editing
# by the project owner. In a production environment, you would NOT even include this comment.
# However, for this project's defined workflow, it's explicitly requested.
# New admins or password updates should primarily be done via the admin_hash_gen.py script.
# Update the admin credentials using the script, which will modify this file directly.
# Ensure this file is not publicly accessible and is secured on the server.
ADMIN_CREDENTIALS = {
    # Placeholder for the admin credentials.
    # Format: "username": "bcrypt_hash"
    "ExampleAdmin1": "$2b$12$HpMRBKbYYqGtGtasvAzDCOJ.oGXRBAANln4VRpmuzmv6mPznR1U12", # bcrypt hash for 'examplepassword1'
    "ExampleAdmin2": "$2b$12$/Um7zQcy9.MFEtC8QTUWfefxbm/yCbtsp1s4DwPdue7B4A09ldIY2", # bcrypt hash for 'examplepassword2'
}

# --- Session Management Configuration ---
# Enable/Disable session timeout for admin logins.
# If True, sessions will expire after `SESSION_DURATION_DAYS`.
# If False, sessions will not expire based on time (though they can still be manually logged out).
SESSION_TIMEOUT_ENABLED = True # Set to True or False

# Duration of an admin session in days, if SESSION_TIMEOUT_ENABLED is True.
SESSION_DURATION_DAYS = 7 # Example: 7 days

# The path to this file, used by admin_hash_gen.py to update credentials directly.
# This ensures that the script updates the correct file.
THIS_FILE_PATH = os.path.abspath(__file__)

# --- Authentication and Authorization Functions ---

def verify_password(stored_hash: str, provided_password: str) -> bool:
    """
    Verifies a provided password against a bcrypt hash.
    """
    try:
        # bcrypt.checkpw takes bytes, so encode the password
        return bcrypt.checkpw(provided_password.encode('utf-8'), stored_hash.encode('utf-8'))
    except Exception as e:
        logger.error(f"Error during password verification: {e}")
        return False

def get_admin_credentials(username: str) -> str:
    """
    Retrieves the hashed password for a given username.
    Returns the hash string if found, None otherwise.
    """
    return ADMIN_CREDENTIALS.get(username)

def authenticate_admin(username: str, password: str) -> bool:
    """
    Authenticates an admin user.
    """
    stored_hash = get_admin_credentials(username)
    if stored_hash:
        return verify_password(stored_hash, password)
    return False

def get_session_expiry_time() -> int:
    """
    Calculates the session expiry time in Unix timestamp (seconds since epoch).
    Returns 0 if session timeout is disabled, otherwise a future timestamp.
    """
    if SESSION_TIMEOUT_ENABLED:
        return int(time.time() + (SESSION_DURATION_DAYS * 24 * 60 * 60))
    return 0 # 0 indicates no specific expiry time (handled by the client or indefinite)

# --- Admin Management (For admin_hash_gen.py to modify this file) ---

def update_admin_credential_in_file(username: str, new_password_plaintext: str, comment_text: str):
    """
    Generates a new bcrypt hash for the password and updates the ADMIN_CREDENTIALS
    dictionary in this file, including the plaintext password as a comment.
    This function directly modifies the admin_auth.py file.
    """
    new_hash = bcrypt.hashpw(new_password_plaintext.encode('utf-8'), bcrypt.gensalt()).decode('utf-8')
    
    # Line to be added/updated in the file
    new_entry_line = f'    "{username}": "{new_hash}", # {comment_text}'

    try:
        with open(THIS_FILE_PATH, 'r') as f:
            lines = f.readlines()

        # Find the start and end of the ADMIN_CREDENTIALS dictionary
        start_index = -1
        end_index = -1
        for i, line in enumerate(lines):
            if "ADMIN_CREDENTIALS = {" in line:
                start_index = i
            if start_index != -1 and "}" in line and i > start_index:
                end_index = i
                break

        if start_index == -1 or end_index == -1:
            logger.error("Could not find ADMIN_CREDENTIALS dictionary in admin_auth.py.")
            raise ValueError("ADMIN_CREDENTIALS dictionary structure not found.")

        # Check if username already exists and update it, otherwise add new entry
        found_existing = False
        new_lines = lines[:start_index + 1] # Keep lines up to the opening brace
        for i in range(start_index + 1, end_index):
            line = lines[i]
            if f'"{username}":' in line:
                new_lines.append(new_entry_line + '\n')
                found_existing = True
                logger.info(f"Updated password for existing admin: {username}")
            else:
                new_lines.append(line)
        
        if not found_existing:
            # Add the new entry just before the closing brace
            # Ensure proper indentation for a new entry
            if len(new_lines) > start_index + 1 and not new_lines[-1].strip().endswith('{'):
                # Add a comma to the previous line if it's not the opening brace and doesn't end with a comma
                if new_lines[-1].strip() and not new_lines[-1].strip().endswith(','):
                    new_lines[-1] = new_lines[-1].rstrip('\n') + ',\n'
            new_lines.append(new_entry_line + '\n')
            logger.info(f"Added new admin: {username}")

        new_lines.extend(lines[end_index:]) # Add lines from closing brace onwards

        with open(THIS_FILE_PATH, 'w') as f:
            f.writelines(new_lines)
        
        # Update the in-memory dictionary immediately
        ADMIN_CREDENTIALS[username] = new_hash
        logger.info(f"Successfully updated admin '{username}' credentials in {THIS_FILE_PATH}")

    except Exception as e:
        logger.error(f"Failed to update admin credentials in file {THIS_FILE_PATH}: {e}", exc_info=True)
        raise

if __name__ == "__main__":
    # This block is primarily for demonstration or initial testing purposes.
    # In a real scenario, this file is imported by tg.py.
    # The actual update of ADMIN_CREDENTIALS via script will be handled by admin_hash_gen.py
    logger.info("admin_auth.py loaded.")
    logger.info(f"Current admins: {list(ADMIN_CREDENTIALS.keys())}")
    logger.info(f"Session Timeout Enabled: {SESSION_TIMEOUT_ENABLED}")
    if SESSION_TIMEOUT_ENABLED:
        logger.info(f"Session Duration: {SESSION_DURATION_DAYS} days")

    # Example of how you'd verify a password (this won't work without actual hashes)
    # print(f"Verifying 'SHITIJ.dev' with 'wrongpassword': {authenticate_admin('SHITIJ.dev', 'wrongpassword')}")
    # print(f"Verifying 'SHITIJ.dev' with 'onlyforherforever': {authenticate_admin('SHITIJ.dev', 'onlyforherforever')}")
