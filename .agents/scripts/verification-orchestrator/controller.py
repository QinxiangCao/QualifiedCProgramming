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


SCRIPT_DIR = Path(__file__).resolve().parent
VC_PROVING_SCRIPTS = SCRIPT_DIR.parent / "vc-proving"
if str(VC_PROVING_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(VC_PROVING_SCRIPTS))


from controller_cli import build_parser, public_command_schema  # noqa: E402
from controller_execution import execute_command  # noqa: E402
from path_utils import fixed_path_under  # noqa: E402


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    root = Path(args.main_root).expanduser().absolute() if args.main_root else Path.cwd()
    args.main_root = str(fixed_path_under(root, root, label="main root"))
    return execute_command(args)


if __name__ == "__main__":
    raise SystemExit(main())
