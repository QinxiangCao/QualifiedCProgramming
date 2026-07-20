#!/usr/bin/env python3
"""Proof-group planning helpers for copied vc-proving group directories."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def load_group_plan(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise SystemExit(f"group plan is not a JSON object: {path}")
    return data


def _require_controller_verified(
    *,
    lemmas: list[dict[str, Any]],
    plan: dict[str, Any],
    source_goal_version: str | None,
) -> None:
    if plan.get("verified") is not True:
        raise SystemExit("group plan must be controller-verified before preparing group directories")
    if source_goal_version is not None and plan.get("source_goal_version") != source_goal_version:
        raise SystemExit("group plan source_goal_version does not match current manifest")
    expected = [str(lemma["name"]) for lemma in lemmas]
    assigned = [str(name) for group in plan.get("groups", []) for name in group.get("witnesses", [])]
    if len(assigned) != len(expected) or set(assigned) != set(expected):
        raise SystemExit("group plan groups must cover the manual obligations exactly")


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
    proof_groups = plan.get("groups")
    if not isinstance(proof_groups, list) or not proof_groups:
        raise SystemExit("group plan must contain non-empty groups")

    seen: set[str] = set()
    entries: list[dict[str, Any]] = []
    group_ids: set[str] = set()
    for raw in proof_groups:
        if not isinstance(raw, dict):
            raise SystemExit("each proof group must be a JSON object")
        group_id = str(raw.get("id") or "").strip()
        if not group_id:
            raise SystemExit("proof group missing group_id")
        if group_id in group_ids:
            raise SystemExit(f"duplicate proof group id: {group_id}")
        group_ids.add(group_id)
        witness_names = [str(name) for name in raw.get("witnesses", [])]
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
                "proof_strategy": str(raw.get("strategy") or ""),
                "expected_helpers": [str(item) for item in raw.get("helpers", [])],
                "dependencies": [str(item) for item in raw.get("depends_on", [])],
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
