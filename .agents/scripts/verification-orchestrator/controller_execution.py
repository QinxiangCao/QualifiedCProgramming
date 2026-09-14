"""Public command execution and timing boundary."""

from __future__ import annotations

import argparse
import os
import time
from datetime import UTC, datetime
from pathlib import Path

from controller_control import require_active_run
from controller_state import _record_timing, _run_root_from_id
from process_adapter import CONTROL_SIGNAL_ENV


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
) -> None:
    if args.command in {
        "init-run",
        "pause-run",
        "cancel-action",
        "resume-run",
        "symexec",
        "coq-check",
        "unfreeze",
    }:
        return
    if not getattr(args, "run", None):
        return
    try:
        run_root = _run_root_from_id(_args_main_root(args), args.run)
        _record_timing(
            run_root,
            args.command,
            started_at=started_at,
            elapsed_seconds=elapsed_seconds,
            round_id=getattr(args, "round", None),
            attempt_id=getattr(args, "attempt", None),
        )
    except SystemExit:
        # A command that failed before resolving a valid run has no timing row.
        pass


def execute_command(args: argparse.Namespace) -> int:
    """Execute one public command directly.

    The controller contract permits only one active run command, so no run,
    target, workspace, or dependency synchronization layer is needed here.
    Individual services retain atomic file replacement and generation checks.
    """

    started = time.monotonic()
    started_at = (
        datetime.now(UTC)
        .isoformat(timespec="microseconds")
        .replace("+00:00", "Z")
    )
    control_path: Path | None = None
    previous_control_environment = os.environ.get(CONTROL_SIGNAL_ENV)
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
        return int(args.func(args))
    finally:
        if previous_control_environment is None:
            os.environ.pop(CONTROL_SIGNAL_ENV, None)
        else:
            os.environ[CONTROL_SIGNAL_ENV] = previous_control_environment
        _record_command_timing(
            args,
            started_at=started_at,
            elapsed_seconds=time.monotonic() - started,
        )
