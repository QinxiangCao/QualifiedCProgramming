"""Shared bounded subprocess execution for controller-owned tools."""

from __future__ import annotations

import json
import math
import os
import signal
import subprocess
import sys
import time
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, Sequence

CONTROL_SIGNAL_ENV = "QCP_CONTROLLER_CONTROL_SIGNAL"


class ProcessCancelled(SystemExit):
    """A cooperative stop that aborts the controller command, not its proof."""


@dataclass(frozen=True)
class ProcessResult:
    returncode: int
    stdout: str
    stderr: str
    cleanup_incomplete: bool = False
    cancelled: bool = False


def tool_progress(label: str) -> Callable[[float, str, str], None]:
    """Report the active build step every 30 seconds without mixing JSON stdout."""
    next_report = 30.0

    def report(elapsed: float, stdout: str, stderr: str) -> None:
        nonlocal next_report
        if elapsed < next_report:
            return
        next_report = elapsed + 30.0
        diagnostic = (stderr or stdout).strip().splitlines()
        suffix = f"; {diagnostic[-1][-300:]}" if diagnostic else ""
        print(f"[QCP] {label}: {elapsed:.0f}s elapsed{suffix}", file=sys.stderr, flush=True)

    return report


def control_signal_requests_stop(path: Path) -> bool:
    """Fail closed when a present control signal is malformed or paused."""

    try:
        if not path.is_file():
            return False
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return True
    return not isinstance(payload, dict) or payload.get("status") != "active"


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
        # ponytail: detached Windows pipes stay with daemon readers until EOF;
        # closing here blocks on their read locks. Stronger tree cleanup would
        # be needed to reclaim those handles before detached descendants exit.
        if os.name != "nt":
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
    cancel_requested: Callable[[], bool] | None = None,
    cancel_message: str = "\nprocess cancelled by controller request",
    progress_callback: Callable[[float, str, str], None] | None = None,
    poll_interval_seconds: float = 5.0,
    return_cancelled_result: bool = False,
) -> ProcessResult:
    """Run one direct argv in its own process group with bounded cleanup.

    ``communicate`` is polled rather than left blocked for the full tool budget.
    This preserves its deadlock-safe pipe handling while giving controller
    pause/cancel requests and low-frequency progress reporting a cooperative
    boundary.  Once ``Popen`` succeeds, *every* exceptional exit first tears
    down the complete process group and then preserves the original exception.
    """

    if not math.isfinite(timeout_seconds) or timeout_seconds < 0:
        raise ValueError("process timeout must be non-negative and finite")
    if not math.isfinite(poll_interval_seconds) or poll_interval_seconds <= 0:
        raise ValueError("process poll interval must be positive and finite")

    if cancel_requested is None:
        raw_control_path = os.environ.get(CONTROL_SIGNAL_ENV)
        if raw_control_path:
            control_path = Path(raw_control_path)
            cancel_requested = lambda: control_signal_requests_stop(control_path)

    if cancel_requested is not None and cancel_requested():
        if not return_cancelled_result:
            raise ProcessCancelled(cancel_message.strip())
        return ProcessResult(130, "", cancel_message, cancelled=True)
    if timeout_seconds == 0:
        return ProcessResult(124, "", timeout_message)

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
    except OSError as exc:
        return ProcessResult(127, "", f"{launch_error_prefix}{exc}")

    started = time.monotonic()
    deadline = started + float(timeout_seconds)
    latest_stdout = ""
    latest_stderr = ""
    try:
        while True:
            if cancel_requested is not None and cancel_requested():
                cleanup_incomplete = _terminate_process_group(proc)
                if not cleanup_incomplete:
                    # Windows only exposes captured output once reader threads finish.
                    latest_stdout, latest_stderr = proc.communicate(timeout=0)
                stderr = latest_stderr + cancel_message
                if cleanup_incomplete:
                    stderr += detached_pipe_message
                if not return_cancelled_result:
                    raise ProcessCancelled(cancel_message.strip())
                return ProcessResult(
                    130,
                    latest_stdout,
                    stderr,
                    cleanup_incomplete,
                    True,
                )
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                # A timeout is not just reported: explicitly terminate the
                # complete process group, including any coqc descendants.
                cleanup_incomplete = _terminate_process_group(proc)
                if not cleanup_incomplete:
                    # Windows only exposes captured output once reader threads finish.
                    latest_stdout, latest_stderr = proc.communicate(timeout=0)
                stderr = latest_stderr + timeout_message
                if cleanup_incomplete:
                    stderr += detached_pipe_message
                return ProcessResult(
                    124,
                    latest_stdout,
                    stderr,
                    cleanup_incomplete,
                )
            try:
                stdout, stderr = proc.communicate(
                    timeout=min(float(poll_interval_seconds), remaining)
                )
            except subprocess.TimeoutExpired as exc:
                # TimeoutExpired carries bytes even with Popen(text=True).
                latest_stdout = (
                    exc.stdout.decode("utf-8", errors="replace")
                    if isinstance(exc.stdout, bytes)
                    else exc.stdout if isinstance(exc.stdout, str) else latest_stdout
                )
                latest_stderr = (
                    exc.stderr.decode("utf-8", errors="replace")
                    if isinstance(exc.stderr, bytes)
                    else exc.stderr if isinstance(exc.stderr, str) else latest_stderr
                )
                if progress_callback is not None:
                    progress_callback(
                        time.monotonic() - started,
                        latest_stdout,
                        latest_stderr,
                    )
                continue
            if progress_callback is not None:
                progress_callback(time.monotonic() - started, stdout, stderr)
            return ProcessResult(proc.returncode, stdout, stderr)
    except ProcessCancelled:
        # The cancellation branch already completed process-group cleanup.
        raise
    except BaseException:
        # KeyboardInterrupt and SystemExit intentionally retain their normal
        # meaning, but never before the controller-owned child process group
        # has been terminated and its pipes have been boundedly drained.
        try:
            _terminate_process_group(proc)
        except BaseException:
            # A second asynchronous interrupt must not erase the original
            # exception or leave the direct child knowingly alive.
            try:
                proc.kill()
            except BaseException:
                pass
        raise
