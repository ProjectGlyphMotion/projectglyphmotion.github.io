# admin_hash_gen.py
import sys
import os
import re
# import getpass # Removed: getpass does not work in this web environment
import logging

# Add the parent directory of admin_auth.py to sys.path if not already there,
# so we can import it and access THIS_FILE_PATH.
# Assumes admin_auth.py is in the same directory as this script.
script_dir = os.path.dirname(os.path.abspath(__file__))
if script_dir not in sys.path:
    sys.path.insert(0, script_dir)

try:
    from admin_auth import update_admin_credential_in_file, THIS_FILE_PATH, ADMIN_CREDENTIALS
except ImportError as e:
    print(f"❌ ERROR: Could not import from admin_auth.py: {e}")
    print("Please ensure admin_auth.py is in the same directory as admin_hash_gen.py")
    sys.exit(1)

# --- Logging Setup ---
logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s", level=logging.INFO)
logger = logging.getLogger(__name__)

def generate_and_update_admin_password():
    """
    Prompts the user for a username and password, then updates/adds the admin
    credential directly in the admin_auth.py file.
    """
    print("\n--- Admin Credential Management ---")
    # Removed the warning about password visibility as requested
    print("This script allows you to add new admins or update existing admin passwords.")
    print("This will directly modify the 'admin_auth.py' file on your server.")
    print("Existing admins:", list(ADMIN_CREDENTIALS.keys()))

    username = input("Enter the admin username: ").strip()
    if not username:
        print("Username cannot be empty. Aborting.")
        return

    # Check if username exists, if so, it's an update. Otherwise, a new user.
    is_update = username in ADMIN_CREDENTIALS
    if is_update:
        print(f"Detected existing admin: '{username}'. You are updating their password.")
    else:
        print(f"Adding new admin: '{username}'.")

    # Use input() instead of getpass.getpass() for compatibility in this environment
    password = input("Enter the new password for this admin: ").strip() # Removed visibility warning
    if not password:
        print("Password cannot be empty. Aborting.")
        return
    print("✅ Password entered.") # Tickmark after successful password input

    confirm_password = input("Confirm the new password: ").strip() # Removed visibility warning

    if password != confirm_password:
        print("Passwords do not match. Aborting.")
        return
    print("✅ Password confirmed.") # Tickmark after successful password confirmation

    # Create the comment text for the plaintext password
    comment_text = f"bcrypt hash for '{password}'"

    try:
        # Call the function from admin_auth.py to modify the file
        update_admin_credential_in_file(username, password, comment_text)
        
        # Updated success message as requested
        action_text = "updated" if is_update else "registered"
        print(f"\n✅ User '{username}' password has been {action_text} successfully in admin_auth.py!")
        print("Remember to restart your tg.py backend server for changes to take effect.")
    except Exception as e:
        print(f"\n❌ FAILED to {'update' if is_update else 'add'} admin '{username}': {e}")
        print("Please check the console for more details and ensure 'admin_auth.py' is writable.")

if __name__ == "__main__":
    generate_and_update_admin_password()
