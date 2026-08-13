"""Shared bounded subprocess execution for controller-owned tools."""

from __future__ import annotations

import os
import signal
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, Sequence


@dataclass(frozen=True)
class ProcessResult:
    returncode: int
    stdout: str
    stderr: str
    cleanup_incomplete: bool = False


def _terminate_process_group(proc: subprocess.Popen[str]) -> bool:
    """Terminate a complete tool process group and bound the final pipe drain."""

    if os.name == "nt":
        try:
            subprocess.run(
                ["taskkill", "/PID", str(proc.pid), "/T", "/F"],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=5,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired):
            pass
        if proc.poll() is None:
            try:
                proc.kill()
            except OSError:
                pass
    else:
        try:
            os.killpg(proc.pid, signal.SIGTERM)
            proc.wait(timeout=2)
        except (OSError, subprocess.TimeoutExpired):
            pass
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except OSError:
            pass

    try:
        proc.communicate(timeout=1)
    except subprocess.TimeoutExpired:
        for stream in (proc.stdout, proc.stderr):
            if stream is not None:
                try:
                    stream.close()
                except OSError:
                    pass
        try:
            proc.wait(timeout=0.2)
        except (OSError, subprocess.TimeoutExpired):
            try:
                proc.kill()
            except OSError:
                pass
        return True
    return False


def run_bounded_process(
    argv: Sequence[str],
    *,
    cwd: Path,
    timeout_seconds: float,
    environment: Mapping[str, str] | None = None,
    timeout_message: str,
    detached_pipe_message: str,
    launch_error_prefix: str = "",
) -> ProcessResult:
    """Run one direct argv in its own process group with bounded cleanup."""

    try:
        popen_kwargs: dict[str, object] = {}
        if os.name == "nt":
            popen_kwargs["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
        else:
            popen_kwargs["start_new_session"] = True
        proc = subprocess.Popen(
            list(argv),
            cwd=cwd,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=(dict(environment) if environment is not None else None),
            **popen_kwargs,
        )
        stdout, stderr = proc.communicate(timeout=timeout_seconds)
        return ProcessResult(proc.returncode, stdout, stderr)
    except subprocess.TimeoutExpired as exc:
        cleanup_incomplete = _terminate_process_group(proc)
        # ``communicate`` in the termination helper may have consumed the
        # remaining pipe contents.  TimeoutExpired still carries the stable
        # prefix captured before cleanup, which is sufficient failure
        # evidence and avoids a second unbounded read.
        stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr = exc.stderr if isinstance(exc.stderr, str) else ""
        stderr += timeout_message
        if cleanup_incomplete:
            stderr += detached_pipe_message
        return ProcessResult(124, stdout, stderr, cleanup_incomplete)
    except OSError as exc:
        return ProcessResult(127, "", f"{launch_error_prefix}{exc}")
