"""Public command execution and timing boundary."""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from datetime import UTC, datetime
from pathlib import Path
from uuid import uuid4

from controller_control import require_active_run
from controller_state import _record_timing, _run_root_from_id
from path_utils import fixed_path_under
from process_adapter import CONTROL_SIGNAL_ENV, ProcessCancelled


def _append_tool_log(path: Path, record: dict) -> None:
    # Each group has one owner and its own log; no shared business-state write.
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, ensure_ascii=True) + "\n")


def start_group_tool_log(args: argparse.Namespace, state: dict, group: dict, command: str) -> None:
    """Bind diagnostics to the validated group before starting a build."""
    try:
        path = fixed_path_under(
            Path(group["report_directory"]) / "tool_calls.jsonl", Path(state["report_root"]),
            label="group tool log",
        )
        record = {
            "call_id": uuid4().hex, "command": command, "round": args.round,
            "group": args.group, "target_kind": getattr(args, "target_kind", None),
            "started_at": datetime.now(UTC).isoformat(),
        }
        args._group_tool_log = (path, record, time.monotonic())
        _append_tool_log(path, {**record, "event": "started"})
    except (OSError, ValueError) as exc:
        print(f"Tool log diagnostic: {exc}", file=sys.stderr)


def _finish_group_tool_log(args: argparse.Namespace, exit_code: int, error: str | None) -> None:
    log = getattr(args, "_group_tool_log", None)
    if log is None:
        return
    path, record, started = log
    evidence = getattr(args, "_tool_evidence", {})
    try:
        _append_tool_log(path, {
            **record, "event": "finished", "finished_at": datetime.now(UTC).isoformat(),
            "elapsed_seconds": round(time.monotonic() - started, 6), "exit_code": exit_code,
            "status": evidence.get("status", "cancelled" if exit_code == 130 else "failed"),
            **{key: evidence[key] for key in ("returncode", "first_failure") if key in evidence},
            **({"error": error} if error else {}),
        })
    except (OSError, ValueError) as exc:
        print(f"Tool log diagnostic: {exc}", file=sys.stderr)


def _args_main_root(args: argparse.Namespace) -> Path:
    return (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )


def _record_command_timing(
    args: argparse.Namespace,
    *,
    started_at: str,
    elapsed_seconds: float,
    exit_code: int,
) -> None:
    if args.command not in {
        "symexec", "coq-check", "coq-debug", "vc-proving-preparing",
        "vc-proving-verify", "dune-build", "finalize-delivery", "final-apply", "final-check",
    }:
        return
    if not getattr(args, "run", None) or getattr(args, "group", None):
        return
    try:
        run_root = _run_root_from_id(_args_main_root(args), args.run)
        _record_timing(
            run_root,
            args.command,
            started_at=started_at,
            elapsed_seconds=elapsed_seconds,
            exit_code=exit_code,
            round_id=getattr(args, "round", None),
            attempt_id=getattr(args, "attempt", None),
        )
    except (OSError, ValueError, TypeError, KeyError, SystemExit) as exc:
        print(f"Timing diagnostic: {exc}", file=sys.stderr)


def execute_command(args: argparse.Namespace) -> int:
    """Execute one public command directly.

    Main serializes business-state mutations. Group development commands may
    run concurrently; Dune coordinates shared dependency refreshes separately.
    """

    started = time.monotonic()
    started_at = (
        datetime.now(UTC)
        .isoformat(timespec="microseconds")
        .replace("+00:00", "Z")
    )
    control_path: Path | None = None
    previous_control_environment = os.environ.get(CONTROL_SIGNAL_ENV)
    exit_code = 1
    error = None
    try:
        if args.command not in {
            "init-run",
            "step",
            "pause-run",
            "cancel-action",
            "resume-run",
            "validate-artifact",
        }:
            control_path = require_active_run(args)
        if control_path is not None:
            os.environ[CONTROL_SIGNAL_ENV] = str(control_path)
        exit_code = int(args.func(args))
        return exit_code
    except BaseException as exc:
        error = f"{type(exc).__name__}: {exc}"
        if isinstance(exc, (KeyboardInterrupt, ProcessCancelled)):
            exit_code = 130
        elif isinstance(exc, SystemExit) and isinstance(exc.code, int):
            exit_code = exc.code
        raise
    finally:
        _finish_group_tool_log(args, exit_code, error)
        if previous_control_environment is None:
            os.environ.pop(CONTROL_SIGNAL_ENV, None)
        else:
            os.environ[CONTROL_SIGNAL_ENV] = previous_control_environment
        _record_command_timing(
            args,
            started_at=started_at,
            elapsed_seconds=time.monotonic() - started,
            exit_code=exit_code,
        )
