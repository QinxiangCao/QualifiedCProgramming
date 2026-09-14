#!/usr/bin/env python3
"""Annotation-plan validation, VC comparison, and user-spec unfreeze."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

from controller_attempts import _attempt_for_round
from controller_state import (
    _append_event,
    _failed_vcs_errors,
    _load_state,
    _run_root_from_id,
    _save_state,
    _state_transaction,
    _validated_annotation_attempt_paths,
)

COMPARISON_RESULTS = {"resolved", "unresolved"}
COQ_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
C_COMMENT_RE = re.compile(r"/\*.*?\*/|//[^\n]*", re.DOTALL)
C_STRING_RE = re.compile(r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'')
ANNOTATED_FUNCTION_RE = re.compile(
    r"\b(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*"
    r"\([^;{}]*\)\s*/\*@.*?\*/\s*\{",
    re.DOTALL,
)


def annotation_plan_path(state: dict[str, Any], attempt: dict[str, Any]) -> Path:
    return _validated_annotation_attempt_paths(state, attempt)["plan"]


def _c_loop_count(source: str) -> int:
    stripped = C_COMMENT_RE.sub(" ", C_STRING_RE.sub(" ", source))
    return len(re.findall(r"\b(?:for|while)\s*\(", stripped))


def _function_spec_errors(
    function_specs: Any, *, c_source: str | None
) -> list[str]:
    if not isinstance(function_specs, list):
        return ["annotation plan function_specs must be a list"]
    errors: list[str] = []
    names: set[str] = set()
    for index, item in enumerate(function_specs):
        location = f"function_specs[{index}]"
        if not isinstance(item, dict) or set(item) != {"name", "meaning"}:
            errors.append(f"{location} requires exactly name and meaning")
            continue
        name = item["name"]
        meaning = item["meaning"]
        if not isinstance(name, str) or not name.strip():
            errors.append(f"{location}.name must be a non-empty string")
            continue
        if name in names:
            errors.append(f"duplicate function specification summary: {name}")
        names.add(name)
        if not isinstance(meaning, str) or not meaning.strip():
            errors.append(f"{location}.meaning must be a non-empty string")
    if c_source is not None:
        expected = {
            match.group("name") for match in ANNOTATED_FUNCTION_RE.finditer(c_source)
        }
        missing = sorted(expected - names)
        extra = sorted(names - expected)
        if missing:
            errors.append(
                "annotation plan is missing function specification summaries: "
                + ", ".join(missing)
            )
        if extra:
            errors.append(
                "annotation plan names functions without a C specification: "
                + ", ".join(extra)
            )
    return errors


def _loop_invariant_errors(
    loop_invariants: Any, *, c_source: str | None
) -> list[str]:
    if not isinstance(loop_invariants, list):
        return ["annotation plan loop_invariants must be a list"]
    errors: list[str] = []
    locations: set[str] = set()
    for index, item in enumerate(loop_invariants):
        location = f"loop_invariants[{index}]"
        if not isinstance(item, dict) or set(item) != {"location", "progress"}:
            errors.append(f"{location} requires exactly location and progress")
            continue
        point = item["location"]
        progress = item["progress"]
        if not isinstance(point, str) or not point.strip():
            errors.append(f"{location}.location must be a non-empty string")
            continue
        if point in locations:
            errors.append(f"duplicate loop location: {point}")
        locations.add(point)
        if not isinstance(progress, str) or not progress.strip():
            errors.append(f"{location}.progress must be a non-empty string")
    if c_source is not None:
        required = _c_loop_count(c_source)
        if len(loop_invariants) != required:
            errors.append(
                "annotation plan must contain one progress summary for every "
                f"lexical C loop: found {required}, recorded {len(loop_invariants)}"
            )
    return errors


def _new_predicate_errors(predicates: Any) -> list[str]:
    if not isinstance(predicates, list):
        return ["annotation plan new_predicates must be a list"]
    errors: list[str] = []
    names: set[str] = set()
    fields = {"name", "meaning", "why_needed"}
    for index, predicate in enumerate(predicates):
        location = f"new_predicates[{index}]"
        if not isinstance(predicate, dict) or set(predicate) != fields:
            errors.append(
                f"{location} requires exactly name, meaning, and why_needed"
            )
            continue
        name = predicate["name"]
        if not isinstance(name, str) or COQ_IDENTIFIER_RE.fullmatch(name) is None:
            errors.append(f"{location}.name must be a legal unqualified Rocq identifier")
            continue
        if name in names:
            errors.append(f"duplicate new predicate name: {name}")
        names.add(name)
        for field in ("meaning", "why_needed"):
            if not isinstance(predicate[field], str) or not predicate[field].strip():
                errors.append(f"{location}.{field} must be a non-empty string")
    return errors


def _comparison_shape_errors(comparisons: Any) -> list[str]:
    if not isinstance(comparisons, list):
        return ["annotation plan vc_comparisons must be a list"]
    errors: list[str] = []
    fields = {"source", "current", "old_gap", "change", "result"}
    for index, comparison in enumerate(comparisons):
        location = f"vc_comparisons[{index}]"
        if not isinstance(comparison, dict) or set(comparison) != fields:
            errors.append(f"{location} requires exact fields")
            continue
        source = comparison["source"]
        source_fields = {"attempt", "name", "annotation_location"}
        if not isinstance(source, dict) or set(source) != source_fields:
            errors.append(f"{location}.source requires exact fields")
        else:
            for field in source_fields:
                if not isinstance(source[field], str) or not source[field].strip():
                    errors.append(
                        f"{location}.source.{field} must be a non-empty string"
                    )
        current = comparison["current"]
        if not isinstance(current, list) or not current:
            errors.append(f"{location}.current must contain at least one VC name")
        elif any(not isinstance(name, str) or not name.strip() for name in current):
            errors.append(f"{location}.current must contain non-empty VC names")
        elif len(current) != len(set(current)):
            errors.append(f"{location}.current must not repeat a VC")
        for field in ("old_gap", "change"):
            if not isinstance(comparison[field], str) or not comparison[field].strip():
                errors.append(f"{location}.{field} must be a non-empty string")
        if comparison["result"] not in COMPARISON_RESULTS:
            errors.append(
                f"{location}.result must be one of: "
                + ", ".join(sorted(COMPARISON_RESULTS))
            )
    return errors


def annotation_vc_comparison_errors(
    plan: dict[str, Any],
    *,
    failed_vcs: Any,
    current_vcs: dict[str, Any],
    require_resolved: bool = True,
) -> list[str]:
    """Match each failed VC to the current manual without duplicating statements."""

    failed_errors = _failed_vcs_errors(failed_vcs)
    if failed_errors:
        return failed_errors
    comparisons = plan["vc_comparisons"]
    if not failed_vcs:
        return (
            ["first annotation attempt requires empty vc_comparisons"]
            if comparisons
            else []
        )
    failed_by_identity = {
        (item["source_attempt"], item["name"]): item for item in failed_vcs
    }
    current_by_name = current_vcs["by_name"]
    errors: list[str] = []
    seen: set[tuple[str, str]] = set()
    for index, comparison in enumerate(comparisons):
        location = f"vc_comparisons[{index}]"
        source = comparison["source"]
        identity = (source["attempt"], source["name"])
        if identity in seen:
            errors.append(f"{location} duplicates a source VC comparison")
            continue
        seen.add(identity)
        failed = failed_by_identity.get(identity)
        if failed is None:
            errors.append(f"{location} does not match a failed VC")
            continue
        if source["annotation_location"] != failed["annotation_location"]:
            errors.append(f"{location} annotation location differs from the failed VC")
        for name in comparison["current"]:
            if name not in current_by_name:
                errors.append(f"{location} current VC does not exist: {name}")
        if require_resolved and comparison["result"] != "resolved":
            errors.append(
                f"{location} must be resolved before annotation status is ready"
            )
    missing = set(failed_by_identity) - seen
    for source_attempt, name in sorted(missing):
        errors.append(f"failed VC has no comparison: {source_attempt}:{name}")
    return errors


def annotation_plan_errors(
    plan: Any,
    *,
    c_source: str | None = None,
    failed_vcs: Any | None = None,
    current_vcs: dict[str, Any] | None = None,
    require_ready: bool = True,
) -> list[str]:
    """Validate concise specification, loop, predicate, and retry summaries."""

    if not isinstance(plan, dict):
        return ["annotation_plan.json must contain one JSON object"]
    expected = {
        "version",
        "status",
        "function_specs",
        "loop_invariants",
        "new_predicates",
        "vc_comparisons",
    }
    if set(plan) != expected:
        return ["annotation_plan.json requires the concise version 2 fields"]
    errors: list[str] = []
    if plan["version"] != 2:
        errors.append("annotation plan version must be 2")
    if plan["status"] not in {"planning", "ready"}:
        errors.append("annotation plan status must be planning or ready")
    elif require_ready and plan["status"] != "ready":
        errors.append("annotation plan status must be ready before completion")
    errors.extend(
        _function_spec_errors(plan["function_specs"], c_source=c_source)
    )
    errors.extend(
        _loop_invariant_errors(plan["loop_invariants"], c_source=c_source)
    )
    errors.extend(_new_predicate_errors(plan["new_predicates"]))
    comparison_shape_errors = _comparison_shape_errors(plan["vc_comparisons"])
    errors.extend(comparison_shape_errors)
    if (
        not comparison_shape_errors
        and failed_vcs is not None
        and current_vcs is not None
    ):
        errors.extend(
            annotation_vc_comparison_errors(
                plan,
                failed_vcs=failed_vcs,
                current_vcs=current_vcs,
                require_resolved=require_ready,
            )
        )
    return errors


def _read_plan(
    path: Path,
    *,
    c_source: str,
    failed_vcs: list[dict[str, Any]],
    current_vcs: dict[str, Any],
) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    errors = annotation_plan_errors(
        payload,
        c_source=c_source,
        failed_vcs=failed_vcs,
        current_vcs=current_vcs,
    )
    if errors:
        raise ValueError("; ".join(errors))
    return payload


def unfreeze(args: argparse.Namespace) -> int:
    """Allow the current annotation attempt to revise a user-provided spec."""

    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    with _state_transaction(run_root):
        state = _load_state(run_root)
        attempt = _attempt_for_round(state, args.round, "annotation")
        if attempt.get("status") != "running":
            raise SystemExit("unfreeze requires the current running annotation attempt")
        record = state.get("spec_freeze")
        if not isinstance(record, dict) or not record.get("functions"):
            raise SystemExit("unfreeze requires a user-provided specification")
        record["baseline"] = None
        _append_event(
            run_root,
            state,
            "unfreeze",
            round=args.round,
            attempt=attempt["attempt_id"],
        )
        _save_state(run_root, state)
    print(
        json.dumps(
            {
                "status": "passed",
                "command": "unfreeze",
                "round": args.round,
                "attempt": attempt["attempt_id"],
            },
            indent=2,
        )
    )
    return 0
