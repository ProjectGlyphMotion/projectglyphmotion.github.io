import os
from pathlib import Path


_PROJECT_ROOT = Path(__file__).resolve().parent
_DEFAULT_ENV_FILE = _PROJECT_ROOT / ".env"


def load_env_file(env_file: str = ".env") -> None:
    """Loads simple KEY=VALUE pairs from an env file into os.environ.

    Existing environment variables are preserved and not overridden.
    Supports optional single or double quoted values.
    """
    path = _PROJECT_ROOT / env_file
    if not path.exists() or not path.is_file():
        return

    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue

        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip()

        if value and len(value) >= 2 and value[0] == value[-1] and value[0] in {"\"", "'"}:
            value = value[1:-1]

        if key and key not in os.environ:
            os.environ[key] = value


def get_env(name: str, default: str | None = None) -> str | None:
    """Returns an environment variable value, or default when unset/blank."""
    value = os.getenv(name)
    if value is None:
        return default

    value = value.strip()
    return value if value else default


# Load .env as soon as this module is imported.
load_env_file()
