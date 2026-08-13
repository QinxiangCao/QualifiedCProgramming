"""Strict validators for every public controller JSON artifact."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

from controller_state import (
    CONTROLLER_STATE_OPTIONAL_FIELDS,
    CONTROLLER_STATE_REQUIRED_FIELDS,
    _json_load,
)
from path_utils import TARGET_FILE_FIELDS

SHA256_RE = re.compile(r"[0-9a-f]{64}")
TERMINAL_REPORT_STATUSES = {"completed", "blocked", "compact-error"}
BLOCKER_FIELDS = {
    "failure_class",
    "kind",
    "location",
    "message",
    "repair_boundary",
}


def _nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value)


def _sha256(value: Any) -> bool:
    return _nonempty_string(value) and SHA256_RE.fullmatch(value) is not None


def _nullable_sha256(value: Any) -> bool:
    return value is None or _sha256(value)


def _positive_integer(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def _nonnegative_integer(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def _report_errors(payload: dict[str, Any], *, context: str) -> list[str]:
    errors: list[str] = []
    allowed = {"status", "blocker"} if payload.get("status") == "blocked" else {"status"}
    if set(payload) != allowed:
        errors.append(f"{context} report contains unsupported fields")
    if payload.get("status") not in TERMINAL_REPORT_STATUSES:
        errors.append(f"{context} report requires a terminal status")
    if payload.get("status") == "blocked":
        blocker = payload.get("blocker")
        if not isinstance(blocker, dict) or set(blocker) != BLOCKER_FIELDS:
            errors.append(f"{context} blocked report requires one complete blocker")
        elif any(not _nonempty_string(blocker.get(field)) for field in BLOCKER_FIELDS):
            errors.append(f"{context} blocker fields must be non-empty strings")
    return errors


def _base_manifest_errors(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    expected = {
        "source_goal_version",
        "proof_manual",
        "formal_case_lib",
        "seed_sha256",
    }
    if set(payload) != expected:
        errors.append("base manifest contains unsupported or missing fields")
    for field in ("source_goal_version", "proof_manual", "formal_case_lib"):
        if not _nonempty_string(payload.get(field)):
            errors.append(f"base manifest requires non-empty {field}")
    seed = payload.get("seed_sha256")
    if (
        not isinstance(seed, dict)
        or set(seed) != {"proof_manual", "formal_case_lib"}
        or not all(_nullable_sha256(value) for value in seed.values())
    ):
        errors.append("base manifest seed digests must be sha256 or null")
    return errors


def _reuse_source_errors(source: Any) -> bool:
    return not (
        isinstance(source, dict)
        and set(source) == {"relative_path", "sha256"}
        and _nonempty_string(source.get("relative_path"))
        and _sha256(source.get("sha256"))
    )


def _workers_manifest_errors(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    expected = {
        "base_manifest_sha256",
        "group_plan",
        "group_plan_sha256",
        "public_helper_snapshot_sha256",
        "groups",
        "dispatch_order",
    }
    if set(payload) != expected:
        errors.append("group workers manifest has unsupported or missing fields")
    for field in (
        "base_manifest_sha256",
        "group_plan_sha256",
        "public_helper_snapshot_sha256",
    ):
        if not _sha256(payload.get(field)):
            errors.append(f"group workers manifest requires {field} as sha256")
    if not _nonempty_string(payload.get("group_plan")):
        errors.append("group workers manifest requires group_plan")

    raw_groups = payload.get("groups")
    groups = (
        raw_groups
        if isinstance(raw_groups, list)
        and all(isinstance(group, dict) for group in raw_groups)
        else []
    )
    if groups is not raw_groups:
        errors.append("group workers manifest requires object groups")
    ids: list[str] = []
    for group in groups:
        allowed = {"id", "proof_reuse_sha256", "proof_reuse_sources"}
        if set(group) - allowed or not _nonempty_string(group.get("id")):
            errors.append("group workers manifest group has invalid fields")
            continue
        ids.append(str(group["id"]))
        has_digest = "proof_reuse_sha256" in group
        if has_digest != ("proof_reuse_sources" in group):
            errors.append("group workers manifest proof reuse seal is incomplete")
        if has_digest and not _sha256(group.get("proof_reuse_sha256")):
            errors.append("group workers manifest proof reuse digest must be sha256")
        sources = group.get("proof_reuse_sources", [])
        if not isinstance(sources, list) or any(
            _reuse_source_errors(source) for source in sources
        ):
            errors.append("group workers manifest proof reuse sources are invalid")
    if len(ids) != len(set(ids)):
        errors.append("group workers manifest group ids must be unique")
    dispatch = payload.get("dispatch_order")
    if (
        not isinstance(dispatch, list)
        or not all(_nonempty_string(item) for item in dispatch)
        or len(dispatch) != len(set(dispatch))
        or set(dispatch) != set(ids)
    ):
        errors.append("group workers manifest dispatch order must cover groups exactly")
    return errors


def _manifest_errors(payload: dict[str, Any]) -> list[str]:
    base_markers = {"proof_manual", "formal_case_lib", "seed_sha256"}
    return (
        _base_manifest_errors(payload)
        if set(payload) & base_markers
        else _workers_manifest_errors(payload)
    )


def _helper_errors(helper: Any, *, context: str) -> list[str]:
    if not isinstance(helper, dict):
        return [f"{context} helper must be an object"]
    errors: list[str] = []
    if set(helper) != {"name", "strategy", "visibility"}:
        errors.append(f"{context} helper requires exact fields")
    if not _nonempty_string(helper.get("name")):
        errors.append(f"{context} helper requires a name")
    if not _nonempty_string(helper.get("strategy")):
        errors.append(f"{context} helper requires a strategy")
    if helper.get("visibility") not in {"local", "public"}:
        errors.append(f"{context} helper visibility must be local or public")
    return errors


def _plan_witness_errors(witness: Any) -> list[str]:
    if not isinstance(witness, dict):
        return ["group plan witness must be an object"]
    errors: list[str] = []
    mode = witness.get("proof_mode")
    expected = (
        {"name", "proof_mode", "split_strategies"}
        if mode == "aggressive_pre_process"
        else {"name", "proof_mode", "strategy"}
    )
    if set(witness) != expected:
        errors.append("group plan witness has invalid fields")
    if not _nonempty_string(witness.get("name")):
        errors.append("group plan witness requires a name")
    if mode not in {"aggressive_pre_process", "LLM_pre_process"}:
        errors.append("group plan witness has invalid proof_mode")
    if mode == "aggressive_pre_process":
        strategies = witness.get("split_strategies")
        if (
            not isinstance(strategies, dict)
            or not strategies
            or not all(
                _nonempty_string(name) and _nonempty_string(strategy)
                for name, strategy in strategies.items()
            )
        ):
            errors.append("aggressive group plan witness requires split_strategies")
    elif mode == "LLM_pre_process" and not _nonempty_string(
        witness.get("strategy")
    ):
        errors.append("LLM_pre_process group plan witness requires a strategy")
    return errors


def _group_plan_errors(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if set(payload) != {"groups"}:
        errors.append("group plan contains unsupported top-level fields")
    raw_groups = payload.get("groups")
    if not isinstance(raw_groups, list):
        return [*errors, "group-plan requires groups as list"]
    if not all(isinstance(group, dict) for group in raw_groups):
        errors.append("group plan requires object groups")
    group_ids: list[str] = []
    witness_names: list[str] = []
    for group in raw_groups:
        if not isinstance(group, dict):
            continue
        if set(group) - {"id", "estimated_difficulty", "witnesses", "helpers"}:
            errors.append("group plan group contains unsupported fields")
        witnesses = group.get("witnesses")
        if (
            not _nonempty_string(group.get("id"))
            or not isinstance(witnesses, list)
            or not witnesses
        ):
            errors.append("group plan group requires id and witnesses")
        else:
            group_ids.append(str(group["id"]))
        if not (
            isinstance(group.get("estimated_difficulty"), int)
            and not isinstance(group.get("estimated_difficulty"), bool)
            and 1 <= group["estimated_difficulty"] <= 5
        ):
            errors.append("group plan estimated_difficulty must be 1 through 5")
        if isinstance(witnesses, list):
            for witness in witnesses:
                errors.extend(_plan_witness_errors(witness))
                if isinstance(witness, dict) and _nonempty_string(witness.get("name")):
                    witness_names.append(str(witness["name"]))
        helpers = group.get("helpers", [])
        if not isinstance(helpers, list):
            errors.append("group plan helpers have an invalid contract")
        else:
            for helper in helpers:
                errors.extend(_helper_errors(helper, context="group plan"))
    if len(group_ids) != len(set(group_ids)):
        errors.append("group plan group ids must be unique")
    if len(witness_names) != len(set(witness_names)):
        errors.append("group plan witness assignment must be unique")
    return errors


def _merge_result_errors(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    required = {
        "status",
        "source_goal_version",
        "candidate",
        "group_count",
        "added_declarations",
    }
    allowed = {*required, "proof_reuse"}
    if payload.get("status") == "failed":
        allowed.update({"error_count", "blocker_count", "failure"})
    if set(payload) - allowed or not required <= set(payload):
        errors.append("merge result contains unsupported or missing fields")
    if payload.get("status") not in {"passed", "failed"}:
        errors.append("merge result status must be passed or failed")
    if not _nonempty_string(payload.get("source_goal_version")):
        errors.append("merge result requires source_goal_version")
    candidate = payload.get("candidate")
    if (
        not isinstance(candidate, dict)
        or set(candidate)
        != {"proof_manual_sha256", "proving_merged_lib_sha256"}
        or not all(_nullable_sha256(value) for value in candidate.values())
    ):
        errors.append("merge result candidate digests are invalid")
    if not _nonnegative_integer(payload.get("group_count")):
        errors.append("merge result group_count must be non-negative")
    if not isinstance(payload.get("added_declarations"), list):
        errors.append("merge result added_declarations must be a list")
    if "proof_reuse" in payload and not isinstance(payload.get("proof_reuse"), dict):
        errors.append("merge result proof_reuse must be an object")
    if payload.get("status") == "failed":
        for field in ("error_count", "blocker_count"):
            if not _nonnegative_integer(payload.get(field)):
                errors.append(f"failed merge result {field} is invalid")
        if "failure" in payload and not isinstance(payload.get("failure"), dict):
            errors.append("failed merge result failure must be an object")
    return errors


def _controller_state_errors(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    fields = set(payload)
    if (
        CONTROLLER_STATE_REQUIRED_FIELDS - fields
        or fields
        - CONTROLLER_STATE_REQUIRED_FIELDS
        - CONTROLLER_STATE_OPTIONAL_FIELDS
    ):
        errors.append("controller state contains unsupported or missing fields")
    for field in ("run_id", "case", "phase", "main_root", "run_root", "report_root"):
        if not _nonempty_string(payload.get(field)):
            errors.append(f"controller state requires non-empty {field}")
    if not _positive_integer(payload.get("generation")):
        errors.append("controller state generation must be a positive integer")
    for field in (
        "max_compact_attempts",
        "max_witnesses_per_group",
        "max_parallel_group_workers",
    ):
        if not _positive_integer(payload.get(field)):
            errors.append(f"controller state {field} must be a positive integer")
    for field in ("rounds", "attempts", "accepted_rounds", "problem_context"):
        if not isinstance(payload.get(field), dict):
            errors.append(f"controller state requires {field} as dict")
    for field in ("next_actions", "waiting_for", "current_blockers"):
        if not isinstance(payload.get(field), list):
            errors.append(f"controller state requires {field} as list")
    target_files = payload.get("target_files")
    if (
        not isinstance(target_files, dict)
        or set(target_files) != TARGET_FILE_FIELDS
        or not all(_nonempty_string(value) for value in target_files.values())
    ):
        errors.append("controller state target_files contract is invalid")
    public_pool = payload.get("public_helper_lemma_lib")
    if (
        not isinstance(public_pool, dict)
        or set(public_pool)
        != {"path", "sha256", "declaration_count", "helper_count"}
        or not _nonempty_string(public_pool.get("path"))
        or not _sha256(public_pool.get("sha256"))
        or not _nonnegative_integer(public_pool.get("declaration_count"))
        or not _nonnegative_integer(public_pool.get("helper_count"))
    ):
        errors.append("controller state public helper record is invalid")
    for field in ("created_at", "updated_at"):
        if not _nonempty_string(payload.get(field)):
            errors.append(f"controller state requires non-empty {field}")
    return errors


def _run_log_errors(path: Path | None) -> list[str]:
    if path is None or not path.is_file():
        return ["run-log validation requires an existing --path"]
    errors: list[str] = []
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as exc:
            errors.append(f"line {line_number}: {exc}")
            continue
        if not isinstance(record, dict):
            errors.append(f"line {line_number}: run log record must be an object")
        elif (
            set(record) != {"at", "event", "phase", "details"}
            or not _nonempty_string(record.get("at"))
            or not _nonempty_string(record.get("event"))
            or not _nonempty_string(record.get("phase"))
            or not isinstance(record.get("details"), dict)
        ):
            errors.append(f"line {line_number}: invalid run log record")
    return errors


def validate_artifact_payload(
    kind: str,
    payload: Any,
    *,
    path: Path | None = None,
) -> list[str]:
    """Validate one artifact against its exact public field contract."""

    if kind == "run-log":
        return _run_log_errors(path)
    if not isinstance(payload, dict):
        return ["artifact must be a JSON object"]
    validators = {
        "agent-report": lambda value: _report_errors(value, context="agent"),
        "group-worker-report": lambda value: _report_errors(
            value, context="group worker"
        ),
        "manifest": _manifest_errors,
        "group-plan": _group_plan_errors,
        "merge-result": _merge_result_errors,
        "controller-state": _controller_state_errors,
    }
    validator = validators.get(kind)
    return (
        validator(payload)
        if validator is not None
        else [f"unsupported artifact kind: {kind}"]
    )


def validate_artifact(args: argparse.Namespace) -> int:
    path = Path(args.path).expanduser().resolve()
    try:
        payload = None if args.kind == "run-log" else _json_load(path)
        errors = validate_artifact_payload(args.kind, payload, path=path)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        errors = [f"artifact cannot be parsed: {exc}"]
    print(
        json.dumps(
            {
                "status": "valid" if not errors else "invalid",
                "errors": errors,
                "path": str(path),
            },
            indent=2,
        )
    )
    return 0 if not errors else 1
