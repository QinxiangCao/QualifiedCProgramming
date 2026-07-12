#!/usr/bin/env python3
"""Proof-group planning helpers for vc-proving group worktrees."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def load_group_plan(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise SystemExit(f"group plan is not a JSON object: {path}")
    return data


def fallback_group_entries(lemmas: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "group_id": str(lemma["name"]),
            "witness_names": [str(lemma["name"])],
            "representative_witness": str(lemma["name"]),
            "proof_strategy": "single witness fallback group",
            "dependencies": [],
        }
        for lemma in lemmas
    ]


def _plan_target_witnesses(plan: dict[str, Any]) -> list[str] | None:
    value = plan.get("target_witnesses")
    if value is None and isinstance(plan.get("group_plan"), dict):
        value = plan["group_plan"].get("target_witnesses")
    if value is None:
        return None
    if not isinstance(value, list):
        raise SystemExit("group plan target_witnesses must be a list")
    return [str(item) for item in value]


def _require_controller_verified(
    *,
    lemmas: list[dict[str, Any]],
    plan: dict[str, Any],
    source_goal_version: str | None,
) -> None:
    verified = plan.get("controller_verified")
    if verified not in (True, "yes"):
        raise SystemExit("group plan must be controller-verified before preparing group worktrees")
    if source_goal_version is not None and plan.get("source_goal_version") != source_goal_version:
        raise SystemExit("group plan source_goal_version does not match current manifest")
    target_witnesses = _plan_target_witnesses(plan)
    if target_witnesses is None:
        raise SystemExit("controller-verified group plan must include target_witnesses")
    expected = [str(lemma["name"]) for lemma in lemmas]
    if sorted(target_witnesses) != sorted(expected):
        raise SystemExit("group plan target_witnesses must match manual obligations exactly")
    if len(target_witnesses) != len(set(target_witnesses)):
        raise SystemExit("group plan target_witnesses contains duplicates")
    policy = plan.get("grouping_policy") if isinstance(plan.get("grouping_policy"), dict) else {}
    if policy.get("controller_policy") != "bounded-witness-groups/v1" or policy.get("controller_enforced") != "yes":
        raise SystemExit("controller-verified group plan must include bounded-witness-groups/v1 grouping_policy")
    try:
        max_per_group = int(policy.get("max_witnesses_per_group"))
    except (TypeError, ValueError):
        raise SystemExit("controller grouping_policy.max_witnesses_per_group must be an integer")
    proof_groups = plan.get("proof_groups") if isinstance(plan.get("proof_groups"), list) else []
    if len(expected) > max_per_group and len(proof_groups) == 1:
        raise SystemExit("controller grouping_policy forbids an oversized single proof group")
    for group in proof_groups:
        if not isinstance(group, dict):
            continue
        witnesses = group.get("witness_names") if isinstance(group.get("witness_names"), list) else []
        if len(witnesses) > max_per_group:
            raise SystemExit(
                f"proof group `{group.get('group_id')}` exceeds controller max_witnesses_per_group={max_per_group}"
            )


def group_entries_from_plan(
    lemmas: list[dict[str, Any]],
    plan: dict[str, Any],
    *,
    require_controller_verified: bool = False,
    source_goal_version: str | None = None,
) -> list[dict[str, Any]]:
    if require_controller_verified:
        _require_controller_verified(lemmas=lemmas, plan=plan, source_goal_version=source_goal_version)
    known = {str(lemma["name"]): lemma for lemma in lemmas}
    proof_groups = plan.get("proof_groups")
    if not isinstance(proof_groups, list) or not proof_groups:
        raise SystemExit("group plan must contain non-empty proof_groups")

    seen: set[str] = set()
    entries: list[dict[str, Any]] = []
    group_ids: set[str] = set()
    for raw in proof_groups:
        if not isinstance(raw, dict):
            raise SystemExit("each proof group must be a JSON object")
        group_id = str(raw.get("group_id") or "").strip()
        if not group_id:
            raise SystemExit("proof group missing group_id")
        if group_id in group_ids:
            raise SystemExit(f"duplicate proof group id: {group_id}")
        group_ids.add(group_id)
        witness_names = [str(name) for name in raw.get("witness_names", [])]
        if not witness_names:
            raise SystemExit(f"proof group `{group_id}` has no witness_names")
        missing = [name for name in witness_names if name not in known]
        if missing:
            raise SystemExit(f"proof group `{group_id}` references unknown witnesses: {', '.join(missing)}")
        repeated = [name for name in witness_names if name in seen]
        if repeated:
            raise SystemExit(f"proof group `{group_id}` repeats witnesses: {', '.join(repeated)}")
        seen.update(witness_names)
        entries.append(
            {
                "group_id": group_id,
                "witness_names": witness_names,
                "goals": [known[name] for name in witness_names],
                "vc_checking_group_entry": raw,
                "per_witness_plan": raw.get("per_witness_plan", {}),
                "vc_shape": raw.get("vc_shape", {}),
                "witness_instantiation": raw.get("witness_instantiation", {}),
                "space_plan": raw.get("space_plan", {}),
                "pure_plan": raw.get("pure_plan", {}),
                "refinement_plan": raw.get("refinement_plan", {}),
                "candidate_helper_declarations": raw.get("candidate_helper_declarations", []),
                "premise_discharge": raw.get("premise_discharge", {}),
                "difficulty": raw.get("difficulty"),
                "representative_witness": raw.get("representative_witness") or witness_names[0],
                "proof_strategy": raw.get("proof_strategy", ""),
                "expected_helpers": raw.get("expected_helpers", []),
                "dependencies": [str(item) for item in raw.get("dependencies", [])],
                "confidence": raw.get("confidence", "medium"),
            }
        )
    expected = set(known)
    if seen != expected:
        raise SystemExit("group plan does not cover exactly the current witness set")
    _reject_dependency_cycles(entries)
    return entries


def _reject_dependency_cycles(entries: list[dict[str, Any]]) -> None:
    groups = {str(entry["group_id"]): entry for entry in entries}
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(group_id: str) -> None:
        if group_id in visited:
            return
        if group_id in visiting:
            raise SystemExit(f"group plan contains dependency cycle at `{group_id}`")
        if group_id not in groups:
            raise SystemExit(f"group plan references unknown dependency `{group_id}`")
        visiting.add(group_id)
        for dep in groups[group_id].get("dependencies", []):
            visit(str(dep))
        visiting.remove(group_id)
        visited.add(group_id)

    for entry in entries:
        visit(str(entry["group_id"]))
