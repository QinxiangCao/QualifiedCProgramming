#!/usr/bin/env python3
"""Annotation-plan validation, VC comparison, and user-spec unfreeze."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from controller_state import _append_event, _failed_vcs_errors, _save_state, load_run, require_attempt

COMPARISON_RESULTS = ("resolved", "unresolved")


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
    failed_vcs: Any | None = None,
    current_vcs: dict[str, Any] | None = None,
    require_ready: bool = True,
) -> list[str]:
    """Validate the plan fields and failed-VC identities; prose belongs to the owner."""

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
    if plan["status"] not in ("planning", "ready"):
        errors.append("annotation plan status must be planning or ready")
    elif require_ready and plan["status"] != "ready":
        errors.append("annotation plan status must be ready before completion")
    for field in ("function_specs", "loop_invariants", "new_predicates"):
        if not isinstance(plan[field], list):
            errors.append(f"annotation plan {field} must be a list")
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


def unfreeze(args: argparse.Namespace) -> int:
    state = load_run(args)
    attempt = require_attempt(state, args.round, "annotation")
    if state["phase"] != "annotation" or attempt["status"] != "running":
        raise SystemExit("unfreeze requires the current running annotation attempt")
    record = state.get("spec_freeze")
    if not record or not record.get("functions"):
        raise SystemExit("unfreeze requires a user-provided specification")
    record["baseline"] = None
    _save_state(Path(state["run_root"]), state)
    _append_event(Path(state["run_root"]), state, "unfreeze", attempt=attempt["attempt_id"])
    print(json.dumps({"status": "passed", "attempt": attempt["attempt_id"]}))
    return 0
