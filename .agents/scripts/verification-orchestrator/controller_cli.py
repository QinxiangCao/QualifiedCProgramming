"""Public commands. Finalize owns the complete acceptance of each delivery."""
from __future__ import annotations

import argparse

from annotation_design import unfreeze
from controller_artifacts import validate_artifact
from controller_attempts import claim_attempt, finalize_delivery, retry_round
from controller_control import cancel_action, pause_run, resume_run
from controller_dune import dune_build
from controller_final import final_apply, final_check
from controller_proving import vc_proving_preparing, vc_proving_verify
from controller_rounds import DEFAULT_MAX_PARALLEL_GROUP_WORKERS, step
from controller_state import init_run
from controller_tools import coq_check, coq_debug, symexec
from symexec_tooling import DEFAULT_SYMEXEC_PROFILE, SYMEXEC_PROFILES


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Controller for one C verification case.")
    parser.add_argument("--main-root", help="Repository root; defaults to cwd.")
    sub = parser.add_subparsers(dest="command", required=True)
    handlers = {
        "init-run": init_run, "step": step, "pause-run": pause_run, "cancel-action": cancel_action,
        "resume-run": resume_run, "claim-attempt": claim_attempt, "finalize-delivery": finalize_delivery,
        "retry-round": retry_round, "unfreeze": unfreeze, "dune-build": dune_build,
        "vc-proving-preparing": vc_proving_preparing, "vc-proving-verify": vc_proving_verify,
        "symexec": symexec, "coq-check": coq_check, "coq-debug": coq_debug,
        "final-apply": final_apply, "final-check": final_check, "validate-artifact": validate_artifact,
    }
    commands = {}
    for name, handler in handlers.items():
        command = sub.add_parser(name, help=(handler.__doc__ or name).splitlines()[0])
        command.set_defaults(func=handler)
        if name not in {"init-run", "validate-artifact"}:
            command.add_argument("--run", required=True)
        commands[name] = command
    init = commands["init-run"]
    init.add_argument("--case", required=True, help="Authoritative Rocq artifact stem; independent of the C filename.")
    init.add_argument("--target-c-file", required=True, help="Absolute or repository-relative C file under QCP_examples.")
    init.add_argument("--timestamp")
    init.add_argument("--formal-case-lib-policy", choices=["present", "create", "absent"])
    init.add_argument("--freeze-spec", action="append", default=[], metavar="FUNCTION",
                      help="User-provided spec functions; repeatable or comma-separated. Existing shared declarations are also frozen.")
    init.add_argument("--max-witnesses-per-group", type=int, default=12)
    init.add_argument("--max-parallel-group-workers", type=int, default=DEFAULT_MAX_PARALLEL_GROUP_WORKERS)
    init.add_argument("--symexec-profile", choices=sorted(SYMEXEC_PROFILES), default=DEFAULT_SYMEXEC_PROFILE)
    for option in ("problem-statement", "problem-statement-file", "target-function", "expected-behavior", "input-output-contract"):
        init.add_argument("--" + option, default="")
    for option in ("spec-hint", "preferred-hidden-property", "forbidden-pattern", "reference-case-hint"):
        init.add_argument("--" + option, action="append", default=[])
    for name in ("pause-run", "cancel-action"):
        commands[name].add_argument("--reason", required=True)
    commands["cancel-action"].add_argument("--action", required=True)
    commands["claim-attempt"].add_argument("--next-action", required=True)
    commands["claim-attempt"].add_argument("--owner", required=True)
    commands["finalize-delivery"].add_argument("--attempt", required=True)
    commands["finalize-delivery"].add_argument("--owner", required=True)
    retry = commands["retry-round"]
    retry.add_argument("--phase", choices=["annotation", "vc-checking"], required=True)
    retry.add_argument("--reason", required=True)
    retry.add_argument("--previous-attempt", required=True)
    for name in ("unfreeze", "vc-proving-preparing", "vc-proving-verify", "symexec", "coq-check", "coq-debug"):
        commands[name].add_argument("--round", required=True)
    commands["coq-check"].add_argument("--target-kind", required=True,
        choices=["formal-case-lib-design", "formal-case-lib", "group-development", "group-check"])
    for name in ("coq-check", "coq-debug"):
        commands[name].add_argument("--group")
    commands["validate-artifact"].add_argument("--kind", required=True,
        choices=["agent-report", "group-worker-report", "annotation-plan", "controller-state", "run-log"])
    commands["validate-artifact"].add_argument("--path", required=True)
    return parser


def public_command_schema() -> dict:
    parser = build_parser()
    sub = next(action for action in parser._actions if isinstance(action, argparse._SubParsersAction))
    return {"commands": {name: {"arguments": [
        {"options": action.option_strings, "dest": action.dest, "required": action.required,
         "choices": list(action.choices) if action.choices is not None else None, "default": action.default}
        for action in command._actions if action.dest != "help"]}
        for name, command in sub.choices.items()}}
