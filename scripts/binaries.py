"""Locate native QCP tools in the repository, then on PATH."""

import platform
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Binaries:
    symexec: Path
    strategy_check: Path
    lsp: Path
    mcp: Path


def native_folder():
    folders = {"linux": "linux", "win32": "windows"}
    if sys.platform == "darwin":
        architectures = {
            "arm64": "macos-arm64",
            "aarch64": "macos-arm64",
            "x86_64": "macos-x86_64",
            "amd64": "macos-x86_64",
        }
        machine = platform.machine().lower()
        if machine not in architectures:
            raise OSError("Unsupported macOS architecture: " + machine)
        folders["darwin"] = architectures[machine]
    if sys.platform not in folders:
        raise OSError("Unsupported platform: " + sys.platform)
    return ROOT / "bin" / folders[sys.platform]


def _find_binary(name, folder) -> Path:
    filename = name + (".exe" if sys.platform == "win32" else "")
    bundled = folder / filename
    executable = shutil.which(str(bundled))
    executable = executable or shutil.which(filename)
    if executable:
        return Path(executable)
    raise FileNotFoundError(
        f"{filename} not found or not executable (checked {bundled} and PATH)"
    )


def find_binary(name) -> Path:
    """Prefer the native bundled tool; fall back to the user's PATH."""
    return _find_binary(name, native_folder())


def find_binaries() -> Binaries:
    """Locate every QCP tool, failing immediately if any is unavailable."""
    folder = native_folder()
    return Binaries(
        symexec=_find_binary("symexec", folder),
        strategy_check=_find_binary("StrategyCheck", folder),
        lsp=_find_binary("lsp", folder),
        mcp=_find_binary("mcp", folder),
    )
