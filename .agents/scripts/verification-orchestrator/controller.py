#!/usr/bin/env python3
"""Single public CLI for the QCP verification agent system."""

from __future__ import annotations

import sys


REQUIRED_PYTHON = (3, 12)


def require_python_312() -> None:
    """Reject unsupported interpreters before importing workflow services."""

    actual = sys.version_info[:2]
    if actual == REQUIRED_PYTHON:
        return
    required_text = ".".join(map(str, REQUIRED_PYTHON))
    actual_text = ".".join(map(str, actual))
    raise SystemExit(
        "QCP verification controller requires exactly Python "
        f"{required_text}; current interpreter is Python {actual_text}. "
        "From the repository root run: "
        "`uv run --frozen --python 3.12 python "
        ".agents/scripts/verification-orchestrator/controller.py ...`"
    )


require_python_312()


# The scripts remain standalone files rather than a package.  Resolve the one
# shared implementation directory only after the no-side-effect runtime gate.
from pathlib import Path  # noqa: E402
from typing import Any  # noqa: E402


SCRIPT_DIR = Path(__file__).resolve().parent
VC_PROVING_SCRIPTS = SCRIPT_DIR.parent / "vc-proving"
if str(VC_PROVING_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(VC_PROVING_SCRIPTS))


import controller_tools as _controller_tools  # noqa: E402
from controller_artifacts import (  # noqa: E402
    validate_artifact,
    validate_artifact_payload,
)
from controller_cli import (  # noqa: E402
    build_parser as _build_parser,
    public_command_schema,
)
from controller_execution import execute_command  # noqa: E402
from controller_proving import vc_proving_verify  # noqa: E402


# These patchable aliases are retained for the external characterization suite
# and for maintainers injecting real-tool smoke adapters.  Workflow code takes
# the selected adapter explicitly; it no longer reaches back into this CLI.
run_symexec = _controller_tools.run_symexec
run_coqc_check = _controller_tools.run_coqc_check
run_coqtop_debug = _controller_tools.run_coqtop_debug


def symexec(args: Any) -> int:
    return _controller_tools.symexec(args, symexec_runner=run_symexec)


def coq_check(args: Any) -> int:
    return _controller_tools.coq_check(args, coq_check_runner=run_coqc_check)


def coq_debug(args: Any) -> int:
    return _controller_tools.coq_debug(
        args,
        coq_check_runner=run_coqc_check,
        coq_debug_runner=run_coqtop_debug,
    )


def build_parser() -> Any:
    return _build_parser(
        tool_handlers={
            "symexec": symexec,
            "coq-check": coq_check,
            "coq-debug": coq_debug,
        }
    )


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    return execute_command(args)


if __name__ == "__main__":
    raise SystemExit(main())
