"""Parser-owned public command schema and command-to-service dispatch."""

from __future__ import annotations

import argparse
from collections.abc import Callable, Mapping
from typing import Any

from controller_artifacts import validate_artifact
from controller_attempts import claim_attempt, finalize_delivery, retry_round
from controller_final import final_apply, final_check
from controller_proving import vc_proving_preparing, vc_proving_verify
from controller_round_checks import annotation_check_round, vc_checking_check_round
from controller_rounds import (
    DEFAULT_MAX_PARALLEL_GROUP_WORKERS,
    annotation_summary_ready,
    step,
)
from controller_state import init_run, timing_stage
from controller_tools import coq_check, coq_debug, symexec
from controller_dune import dune_build

DEFAULT_MAX_WITNESSES_PER_GROUP = 12
DEFAULT_MAX_COMPACT_ATTEMPTS = 3

PUBLIC_COMMAND_DESCRIPTIONS = {
    "init-run": "Create one fixed verification run and its initial controller state.",
    "step": "Return the current hydrated action list or an explicit waiting reason.",
    "claim-attempt": "Atomically claim one agent delivery and return its exact handoff.",
    "finalize-delivery": "Seal a stopped owner's delivery and run controller validation.",
    "retry-round": "Create a controller-authorized annotation or VC-checking retry.",
    "annotation-summary-ready": "Validate and seal the main-agent annotation retry summary.",
    "timing-stage": "Record optional annotation-checking stage timing.",
    "annotation-check-round": "Run the main-owned annotation acceptance checks.",
    "vc-checking-check-round": "Validate the sealed VC group plan and reuse evidence.",
    "dune-build": "Prepare the exact accepted goal-check with the selected build backend and seal its dependency snapshot.",
    "vc-proving-preparing": "Create one proving round and its fixed group workspaces.",
    "vc-proving-verify": "Merge accepted groups and run parent full verification.",
    "symexec": "Transactionally refresh generated files for a claimed annotation round.",
    "coq-check": "Run a controller-owned Rocq check for an allowed target kind.",
    "coq-debug": "Run controller-owned Rocq debug for current or preserved goals.",
    "final-apply": "Transactionally apply the accepted merged candidate to main root.",
    "final-check": "Run final freshness, Rocq, structure, and cleanup checks.",
    "validate-artifact": "Validate one public controller JSON artifact.",
}


def _command_parser(
    subparsers: Any,
    command: str,
) -> argparse.ArgumentParser:
    description = PUBLIC_COMMAND_DESCRIPTIONS[command]
    return subparsers.add_parser(
        command,
        help=description,
        description=description,
    )


def build_parser(
    *,
    tool_handlers: Mapping[str, Callable[[argparse.Namespace], int]] | None = None,
) -> argparse.ArgumentParser:
    selected_tools = {
        "symexec": symexec,
        "coq-check": coq_check,
        "coq-debug": coq_debug,
        **dict(tool_handlers or {}),
    }
    parser = argparse.ArgumentParser(
        description="Controller for QCP verification runs."
    )
    parser.add_argument(
        "--main-root",
        default=None,
        help="Absolute repository root; defaults to the current directory.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    init = _command_parser(sub, "init-run")
    init.add_argument(
        "--case",
        required=True,
        help=(
            "Legal Rocq artifact stem for the generated case family; it may "
            "differ from the C filename stem."
        ),
    )
    init.add_argument(
        "--target-c-file",
        required=True,
        help="Absolute or repository-relative C source under QCP_examples/.",
    )
    init.add_argument("--timestamp", default=None)
    init.add_argument(
        "--max-compact-attempts", type=int, default=DEFAULT_MAX_COMPACT_ATTEMPTS
    )
    init.add_argument(
        "--max-witnesses-per-group", type=int, default=DEFAULT_MAX_WITNESSES_PER_GROUP
    )
    init.add_argument(
        "--max-parallel-group-workers",
        type=int,
        default=DEFAULT_MAX_PARALLEL_GROUP_WORKERS,
    )
    init.add_argument("--problem-statement", default="")
    init.add_argument("--problem-statement-file", default=None)
    init.add_argument("--target-function", default="")
    init.add_argument("--expected-behavior", default="")
    init.add_argument("--input-output-contract", default="")
    init.add_argument("--spec-hint", action="append", default=[])
    init.add_argument("--preferred-hidden-property", action="append", default=[])
    init.add_argument("--forbidden-pattern", action="append", default=[])
    init.add_argument("--reference-case-hint", action="append", default=[])
    init.set_defaults(func=init_run)

    step_cmd = _command_parser(sub, "step")
    step_cmd.add_argument("--run", required=True)
    step_cmd.set_defaults(func=step)

    claim = _command_parser(sub, "claim-attempt")
    claim.add_argument("--run", required=True)
    claim.add_argument("--next-action", required=True)
    claim.add_argument("--owner", required=True)
    claim.set_defaults(func=claim_attempt)

    finalize = _command_parser(sub, "finalize-delivery")
    finalize.add_argument("--run", required=True)
    finalize.add_argument("--attempt", required=True)
    finalize.add_argument("--owner", required=True)
    finalize.set_defaults(func=finalize_delivery)

    retry = _command_parser(sub, "retry-round")
    retry.add_argument("--run", required=True)
    retry.add_argument("--phase", choices=["annotation", "vc-checking"], required=True)
    retry.add_argument("--reason", required=True)
    retry.add_argument("--previous-attempt", required=True)
    retry.set_defaults(func=retry_round)

    summary_ready = _command_parser(sub, "annotation-summary-ready")
    summary_ready.add_argument("--run", required=True)
    summary_ready.add_argument("--attempt", required=True)
    summary_ready.set_defaults(func=annotation_summary_ready)

    timing = _command_parser(sub, "timing-stage")
    timing.add_argument("--run", required=True)
    timing.add_argument("--round", required=True)
    timing.add_argument("--stage", choices=["annotation-checking"], required=True)
    timing.add_argument("--event", choices=["start", "finish"], required=True)
    timing.set_defaults(func=timing_stage)

    annotation = _command_parser(sub, "annotation-check-round")
    annotation.add_argument("--run", required=True)
    annotation.add_argument("--round", required=True)
    annotation.set_defaults(func=annotation_check_round)

    vc_check = _command_parser(sub, "vc-checking-check-round")
    vc_check.add_argument("--run", required=True)
    vc_check.add_argument("--round", required=True)
    vc_check.add_argument("--group-plan", default=None)
    vc_check.set_defaults(func=vc_checking_check_round)

    dune = _command_parser(sub, "dune-build")
    dune.add_argument("--run", required=True)
    dune.set_defaults(func=dune_build)

    prepare = _command_parser(sub, "vc-proving-preparing")
    prepare.add_argument("--run", required=True)
    prepare.add_argument("--round", required=True)
    prepare.set_defaults(func=vc_proving_preparing)

    verify = _command_parser(sub, "vc-proving-verify")
    verify.add_argument("--run", required=True)
    verify.add_argument("--round", required=True)
    verify.set_defaults(func=vc_proving_verify)

    symexec_cmd = _command_parser(sub, "symexec")
    symexec_cmd.add_argument("--run", required=True)
    symexec_cmd.add_argument("--round", required=True)
    symexec_cmd.set_defaults(func=selected_tools["symexec"])

    coq_check_cmd = _command_parser(sub, "coq-check")
    coq_check_cmd.add_argument("--run", required=True)
    coq_check_cmd.add_argument("--round", required=True)
    coq_check_cmd.add_argument(
        "--target-kind",
        choices=["formal-case-lib", "group-development", "group-check"],
        required=True,
    )
    coq_check_cmd.add_argument("--group", default=None)
    coq_check_cmd.set_defaults(func=selected_tools["coq-check"])

    coq_debug_cmd = _command_parser(sub, "coq-debug")
    coq_debug_cmd.add_argument("--run", required=True)
    coq_debug_cmd.add_argument("--round", required=True)
    coq_debug_cmd.add_argument("--group", default=None)
    coq_debug_cmd.set_defaults(func=selected_tools["coq-debug"])

    apply_cmd = _command_parser(sub, "final-apply")
    apply_cmd.add_argument("--run", required=True)
    apply_cmd.set_defaults(func=final_apply)

    final = _command_parser(sub, "final-check")
    final.add_argument("--run", required=True)
    final.set_defaults(func=final_check)

    validate = _command_parser(sub, "validate-artifact")
    validate.add_argument(
        "--kind",
        choices=[
            "agent-report",
            "group-worker-report",
            "manifest",
            "group-plan",
            "merge-result",
            "controller-state",
            "run-log",
        ],
        required=True,
    )
    validate.add_argument("--path", required=True)
    validate.set_defaults(func=validate_artifact)
    return parser


def public_command_schema() -> dict[str, Any]:
    """Export parser-owned command metadata for documentation drift checks."""

    parser = build_parser()
    subparsers = next(
        action
        for action in parser._actions
        if isinstance(action, argparse._SubParsersAction)
    )
    commands: dict[str, Any] = {}
    for name, command_parser in sorted(subparsers.choices.items()):
        arguments: list[dict[str, Any]] = []
        for action in command_parser._actions:
            if action.dest in {"help", "func"}:
                continue
            default = action.default
            if default is argparse.SUPPRESS:
                rendered_default: Any = None
            elif isinstance(default, (str, int, float, bool, list, type(None))):
                rendered_default = default
            else:
                rendered_default = repr(default)
            arguments.append(
                {
                    "options": list(action.option_strings),
                    "dest": action.dest,
                    "required": bool(getattr(action, "required", False)),
                    "choices": (
                        list(action.choices)
                        if action.choices is not None
                        else None
                    ),
                    "default": rendered_default,
                    "nargs": action.nargs,
                    "action": action.__class__.__name__,
                }
            )
        commands[name] = {
            "description": command_parser.description,
            "arguments": arguments,
        }
    return {
        "global_arguments": [
            {
                "options": ["--main-root"],
                "required": False,
                "default": None,
            }
        ],
        "commands": commands,
    }
