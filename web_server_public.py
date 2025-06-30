import os
import subprocess
import time
import sys
import re
import json
import threading
import signal
import psutil # For checking if processes are running

# --- Configuration ---
# IMPORTANT: Fill these out!
GITHUB_REPO_NAME = "Project-GlyphMotion" # Your GitHub username
GITHUB_REPO_NAME = "Project-GlyphMotion" # Your GitHub repository name
GITHUB_PAT = "YOUR_ACTUAL_GITHUB_PAT" # <--- IMPORTANT: Replace with your actual GitHub Personal Access Token (with 'repo' scope)
GITHUB_BRANCH = "main" # Your GitHub Pages branch (usually 'main' or 'master')

# Cloudflare Tunnel Configuration
# Tunnel Name (must match the name used when you ran 'cloudflared tunnel create')
CLOUDFLARE_TUNNEL_NAME = "project-glyph-motion-org-tunnel" # Change this to your actual tunnel name 
# Your custom domain that you configured with Cloudflare Tunnel
# This MUST match the 'hostname' in your config.yml and the CNAME record in Cloudflare DNS
CLOUDFLARE_CUSTOM_DOMAIN = "projectglyphmotion.studio" # Change this to your actual custom domain

# Local Server Configuration
TG_PY_SCRIPT = "tg.py"
LOCAL_SERVER_PORT = 5000 # This must match WEB_SERVER_PORT in tg.py

# HTML File to Update
INDEX_HTML_PATH = "index.html"

# --- Global Process Variables ---
tg_process = None
cloudflared_process = None

def run_command(command, cwd=None, capture_output=False, shell=False):
    """Helper to run shell commands."""
    try:
        if capture_output:
            result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, check=True, shell=shell)
            return result.stdout.strip()
        else:
            # For background processes, capture stdout/stderr to see logs
            process = subprocess.Popen(command, cwd=cwd, shell=shell, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            # Start a thread to read and print the output in real-time
            threading.Thread(target=read_process_output, args=(process, command[0]), daemon=True).start()
            return process
    except subprocess.CalledProcessError as e:
        print(f"❌ Error running command: {' '.join(command)}\n{e.stderr}")
        return None
    except FileNotFoundError:
        print(f"❌ Command not found: {command[0]}. Please ensure it's installed and in your PATH.")
        return None
    except Exception as e:
        print(f"❌ An unexpected error occurred: {e}")
        return None

def read_process_output(process, name):
    """Reads and prints output from a subprocess in real-time."""
    for line in process.stdout:
        print(f"[{name}]: {line.strip()}")

def start_tg_py():
    """Starts the tg.py server in the background."""
    global tg_process
    print(f"🚀 Starting {TG_PY_SCRIPT} server on port {LOCAL_SERVER_PORT}...")
    try:
        # Use sys.executable to ensure the correct python interpreter is used
        tg_process = run_command([sys.executable, TG_PY_SCRIPT])
        if tg_process:
            print(f"✅ {TG_PY_SCRIPT} started (PID: {tg_process.pid}).")
            # Give it a moment to start up
            time.sleep(5) 
            return True
        return False
    except Exception as e:
        print(f"❌ Failed to start {TG_PY_SCRIPT}: {e}")
        return False

def start_cloudflared_tunnel_process():
    """Starts the Cloudflare Tunnel in the background with debug logging."""
    global cloudflared_process
    print(f"🚀 Starting Cloudflare Tunnel '{CLOUDFLARE_TUNNEL_NAME}' for domain '{CLOUDFLARE_CUSTOM_DOMAIN}' with DEBUG logging...")
    try:
        # Added --loglevel debug for verbose output
        cloudflared_process = run_command(["sudo", "cloudflared", "--config", "config.yml", "tunnel", "--loglevel", "debug", "run", CLOUDFLARE_TUNNEL_NAME])
        if cloudflared_process:
            print(f"✅ Cloudflare Tunnel process started (PID: {cloudflared_process.pid}).")
            # Give it a moment to establish the tunnel
            time.sleep(10) 
            return True
        return False
    except Exception as e:
        print(f"❌ Failed to start Cloudflare Tunnel process: {e}")
        return False

def update_index_html(public_url):
    """Updates index.html with the new public URL."""
    print(f"Updating {INDEX_HTML_PATH} with public URL: {public_url}...")
    try:
        with open(INDEX_HTML_PATH, 'r') as f:
            content = f.read()

        # Regex to find and replace the NGROK_PUBLIC_URL or similar constant
        # This makes it robust to previous ngrok URLs or initial placeholders
        updated_content = re.sub(
            r"(const\s+(?:NGROK_PUBLIC_URL|BACKEND_PUBLIC_URL)\s*=\s*['\"]).*?(['\"];)",
            rf"\1{public_url}\2",
            content
        )

        if content == updated_content:
            print(f"ℹ️ {INDEX_HTML_PATH} already contains the correct URL. No changes needed.")
            return True

        with open(INDEX_HTML_PATH, 'w') as f:
            f.write(updated_content)
        print(f"✅ {INDEX_HTML_PATH} updated successfully.")
        return True
    except Exception as e:
        print(f"❌ Failed to update {INDEX_HTML_PATH}: {e}")
        return False

def git_commit_and_push():
    """Commits and pushes the updated index.html to GitHub."""
    print("Committing and pushing changes to GitHub...")
    try:
        # Set Git credentials temporarily for this operation
        # WARNING: Storing PAT directly in script is not recommended for production.
        # Consider using Git credential manager or environment variables.
        os.environ['GIT_ASKPASS'] = 'echo'
        os.environ['GIT_USERNAME'] = GITHUB_USERNAME
        os.environ['GIT_PASSWORD'] = GITHUB_PAT

        # Add the index.html file
        add_cmd = ["git", "add", INDEX_HTML_PATH]
        run_command(add_cmd, capture_output=True)

        # Commit the changes
        commit_cmd = ["git", "commit", "-m", "Automated: Update backend URL via automation script"]
        # Check if there's anything to commit before committing
        status_output = run_command(["git", "status", "--porcelain"], capture_output=True)
        if INDEX_HTML_PATH in status_output: # Check if index.html is actually staged/modified
            run_command(commit_cmd, capture_output=True)
            print("✅ Changes committed.")
        else:
            print("ℹ️ No changes to commit for index.html.")

        # Push to GitHub
        push_cmd = ["git", "push", "origin", GITHUB_BRANCH]
        run_command(push_cmd, capture_output=True)
        print("✅ Changes pushed to GitHub.")
        return True
    except Exception as e:
        print(f"❌ Failed to commit and push to GitHub: {e}")
        return False
    finally:
        # Clean up temporary environment variables
        if 'GIT_ASKPASS' in os.environ:
            del os.environ['GIT_ASKPASS']
        if 'GIT_USERNAME' in os.environ:
            del os.environ['GIT_USERNAME']
        if 'GIT_PASSWORD' in os.environ:
            del os.environ['GIT_PASSWORD']

def cleanup_processes(signum, frame):
    """Gracefully terminates background processes on script exit."""
    print("\nShutting down background processes...")
    if tg_process and psutil.pid_exists(tg_process.pid):
        print(f"Terminating {TG_PY_SCRIPT} (PID: {tg_process.pid})...")
        tg_process.terminate()
        tg_process.wait(timeout=5)
        if psutil.pid_exists(tg_process.pid):
            print(f"Force killing {TG_PY_SCRIPT} (PID: {tg_process.pid})...")
            tg_process.kill()
    
    if cloudflared_process and psutil.pid_exists(cloudflared_process.pid):
        print(f"Terminating Cloudflare Tunnel (PID: {cloudflared_process.pid})...")
        cloudflared_process.terminate()
        cloudflared_process.wait(timeout=5)
        if psutil.pid_exists(cloudflared_process.pid):
            print(f"Force killing Cloudflare Tunnel (PID: {cloudflared_process.pid})...")
            cloudflared_process.kill()
    
    print("Cleanup complete. Exiting.")
    sys.exit(0)

def main():
    # Register signal handlers for graceful exit
    signal.signal(signal.SIGINT, cleanup_processes) # Ctrl+C
    signal.signal(signal.SIGTERM, cleanup_processes) # kill command

    print("--- Starting Public Tracker Automation ---")

    # 1. Start tg.py
    if not start_tg_py():
        print("Automation failed: Could not start tg.py. Exiting.")
        cleanup_processes(None, None)

    # 2. The public URL is now a configured custom domain, not dynamically fetched
    public_backend_url = f"https://{CLOUDFLARE_CUSTOM_DOMAIN}"
    print(f"Using configured public backend URL: {public_backend_url}")

    # 3. Start Cloudflare Tunnel process
    if not start_cloudflared_tunnel_process():
        print("Automation failed: Could not start Cloudflare Tunnel process. Exiting.")
        cleanup_processes(None, None)

    # 4. Update index.html with the stable Cloudflare Tunnel URL
    if not update_index_html(public_backend_url):
        print("Automation failed: Could not update index.html. Exiting.")
        cleanup_processes(None, None)

    # 5. Commit and Push to GitHub
    if not git_commit_and_push():
        print("Automation failed: Could not commit and push to GitHub. Exiting.")
        cleanup_processes(None, None)

    print("\n--- Setup Complete! ---")
    print(f"Your tracker backend is now publicly accessible at: {public_backend_url}")
    print(f"Access your GitHub Pages frontend: https://{GITHUB_USERNAME.lower()}.github.io/{GITHUB_REPO_NAME}/")
    print("\nKeep this script running to maintain the tunnel and backend server.")
    print("Press Ctrl+C to stop all processes gracefully.")

    # Keep the main script running to keep the background processes alive
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        cleanup_processes(None, None)

if __name__ == "__main__":
    main()
# This script automates the setup of a public tracker backend using Cloudflare Tunnel and GitHub Pages.
# It starts the tg.py server, establishes a Cloudflare Tunnel, updates the frontend HTML,
# and commits the changes to GitHub. It handles graceful shutdown of background processes.
# Make sure to run this script in the same directory as tg.py and index.html.
# Ensure you have the required permissions and configurations set up in your GitHub repository.