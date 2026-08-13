#!/usr/bin/env python3
"""Proof-group planning helpers for copied vc-proving group directories."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from proof_manual_utils import helper_namespace_for_group_id, partition_manual_lemmas


PROOF_MODES = {"LLM_pre_process", "aggressive_pre_process"}
MIN_ESTIMATED_DIFFICULTY = 1
MAX_ESTIMATED_DIFFICULTY = 5


def group_witness_names(group: dict[str, Any]) -> list[str]:
    return [
        str(item["name"])
        for item in group.get("witnesses", [])
        if isinstance(item, dict)
    ]


def group_aggressive_split_goal_names(group: dict[str, Any]) -> list[str]:
    return [
        str(split_goal["name"])
        for witness in group.get("witnesses", [])
        if isinstance(witness, dict)
        and witness.get("proof_mode") == "aggressive_pre_process"
        for split_goal in witness.get("split_goals", [])
        if isinstance(split_goal, dict)
    ]


def group_check_names(group: dict[str, Any]) -> list[str]:
    return [*group_witness_names(group), *group_aggressive_split_goal_names(group)]


def load_group_plan(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise SystemExit(f"group plan is not a JSON object: {path}")
    return data


def _require_accepted_shape(
    *,
    lemmas: list[dict[str, Any]],
    plan: dict[str, Any],
) -> None:
    if set(plan) != {"groups"}:
        raise SystemExit("group plan contains unsupported top-level fields")
    witnesses, _split_goals = partition_manual_lemmas(lemmas)
    expected = [str(lemma["name"]) for lemma in witnesses]
    assigned = [
        str(witness.get("name"))
        for group in plan.get("groups", [])
        for witness in group.get("witnesses", [])
        if isinstance(witness, dict)
    ]
    if len(assigned) != len(expected) or set(assigned) != set(expected):
        raise SystemExit("group plan groups must cover the top-level VCs exactly")


def group_entries_from_plan(
    lemmas: list[dict[str, Any]],
    plan: dict[str, Any],
    *,
    require_accepted: bool = False,
) -> list[dict[str, Any]]:
    if require_accepted:
        _require_accepted_shape(lemmas=lemmas, plan=plan)
    if set(plan) != {"groups"}:
        raise SystemExit("group plan contains unsupported top-level fields")
    witness_lemmas, split_goal_lemmas = partition_manual_lemmas(lemmas)
    known = {str(lemma["name"]): lemma for lemma in witness_lemmas}
    known_split_goals = {
        name: {str(lemma["name"]): lemma for lemma in items}
        for name, items in split_goal_lemmas.items()
    }
    proof_groups = plan.get("groups")
    if not isinstance(proof_groups, list):
        raise SystemExit("group plan groups must be a list")
    if not proof_groups:
        if known:
            raise SystemExit(
                "group plan does not cover exactly the current witness set"
            )
        return []

    seen: set[str] = set()
    entries: list[dict[str, Any]] = []
    group_ids: set[str] = set()
    for raw in proof_groups:
        if not isinstance(raw, dict):
            raise SystemExit("each proof group must be a JSON object")
        extra_group_fields = set(raw) - {
            "id",
            "witnesses",
            "helpers",
            "estimated_difficulty",
        }
        if extra_group_fields:
            raise SystemExit(
                f"proof group contains unsupported fields: {sorted(extra_group_fields)}"
            )
        group_id = str(raw.get("id") or "").strip()
        if not group_id:
            raise SystemExit("proof group missing group_id")
        if group_id in group_ids:
            raise SystemExit(f"duplicate proof group id: {group_id}")
        group_ids.add(group_id)
        estimated_difficulty = raw.get("estimated_difficulty")
        if (
            not isinstance(estimated_difficulty, int)
            or isinstance(estimated_difficulty, bool)
            or not MIN_ESTIMATED_DIFFICULTY
            <= estimated_difficulty
            <= MAX_ESTIMATED_DIFFICULTY
        ):
            raise SystemExit(
                f"proof group `{group_id}` estimated_difficulty must be an integer from "
                f"{MIN_ESTIMATED_DIFFICULTY} to {MAX_ESTIMATED_DIFFICULTY}"
            )
        raw_witnesses = raw.get("witnesses")
        if (
            not isinstance(raw_witnesses, list)
            or not raw_witnesses
            or not all(isinstance(item, dict) for item in raw_witnesses)
        ):
            raise SystemExit(f"proof group `{group_id}` must contain witness objects")
        witness_names = [str(item.get("name") or "") for item in raw_witnesses]
        if any(not name for name in witness_names):
            raise SystemExit(f"proof group `{group_id}` has a witness without a name")
        missing = [name for name in witness_names if name not in known]
        if missing:
            raise SystemExit(
                f"proof group `{group_id}` references unknown witnesses: {', '.join(missing)}"
            )
        repeated = [name for name in witness_names if name in seen]
        if repeated:
            raise SystemExit(
                f"proof group `{group_id}` repeats witnesses: {', '.join(repeated)}"
            )
        seen.update(witness_names)
        witnesses: list[dict[str, Any]] = []
        for item in raw_witnesses:
            name = str(item["name"])
            proof_mode = str(item.get("proof_mode") or "")
            if proof_mode not in PROOF_MODES:
                raise SystemExit(f"witness `{name}` has an unsupported proof_mode")
            expected_split_names = list(known_split_goals[name])
            if proof_mode == "aggressive_pre_process":
                allowed = {"name", "proof_mode", "split_strategies"}
            else:
                allowed = {"name", "proof_mode", "strategy"}
            extra = set(item) - allowed
            if extra:
                raise SystemExit(
                    f"witness `{name}` contains unsupported fields: {sorted(extra)}"
                )
            strategy = ""
            if proof_mode == "LLM_pre_process":
                strategy = str(item.get("strategy") or "").strip()
                if not strategy:
                    raise SystemExit(
                        f"LLM_pre_process witness `{name}` requires a proof strategy"
                    )
                if "split_strategies" in item:
                    raise SystemExit(
                        f"LLM_pre_process witness `{name}` must omit split_strategies"
                    )
                split_strategies: dict[str, Any] = {}
            else:
                if not expected_split_names:
                    raise SystemExit(
                        f"aggressive witness `{name}` requires generated split goals"
                    )
                raw_split_strategies = item.get("split_strategies")
                if not isinstance(raw_split_strategies, dict):
                    raise SystemExit(
                        f"aggressive witness `{name}` requires split_strategies"
                    )
                split_names = [str(split) for split in raw_split_strategies]
                if split_names != expected_split_names:
                    raise SystemExit(
                        f"witness `{name}` split_strategies must match the raw manual in order"
                    )
                if not all(
                    isinstance(value, str) and value.strip()
                    for value in raw_split_strategies.values()
                ):
                    raise SystemExit(
                        f"witness `{name}` requires a strategy for every split goal"
                    )
                split_strategies = dict(raw_split_strategies)
            witness = {
                "name": name,
                "goal": known[name],
                "proof_mode": proof_mode,
                "split_goals": [
                    {
                        "name": split_name,
                        "goal": known_split_goals[name][split_name],
                        **(
                            {
                                "strategy": str(
                                    split_strategies.get(split_name) or ""
                                )
                            }
                            if proof_mode == "aggressive_pre_process"
                            else {}
                        ),
                    }
                    for split_name in expected_split_names
                ],
            }
            if proof_mode == "LLM_pre_process":
                witness["strategy"] = strategy
            witnesses.append(witness)
        raw_helpers = raw.get("helpers", [])
        if not isinstance(raw_helpers, list) or not all(
            isinstance(item, dict) for item in raw_helpers
        ):
            raise SystemExit(
                f"proof group `{group_id}` helpers must be a planned-helper object list"
            )
        helpers: list[dict[str, Any]] = []
        for helper in raw_helpers:
            allowed_helper_fields = {"name", "strategy", "visibility"}
            extra_helper_fields = set(helper) - allowed_helper_fields
            if extra_helper_fields:
                raise SystemExit(
                    f"proof group `{group_id}` helper contains unsupported fields: "
                    f"{sorted(extra_helper_fields)}"
                )
            name = str(helper.get("name") or "")
            strategy = str(helper.get("strategy") or "").strip()
            if not name or not strategy:
                raise SystemExit(
                    f"proof group `{group_id}` helper requires name and strategy"
                )
            visibility = helper.get("visibility")
            if visibility not in {"local", "public"}:
                raise SystemExit(
                    f"proof group `{group_id}` helper visibility must be local or public"
                )
            helpers.append(
                {
                    "name": name,
                    "strategy": strategy,
                    "visibility": visibility,
                }
            )
        entries.append(
            {
                "group_id": group_id,
                "witnesses": witnesses,
                "estimated_difficulty": estimated_difficulty,
                "planned_helpers": helpers,
            }
        )
    expected = set(known)
    if seen != expected:
        raise SystemExit("group plan does not cover exactly the current witness set")
    helper_names: set[str] = set()
    for entry in entries:
        group_id = str(entry["group_id"])
        required_suffix = helper_namespace_for_group_id(group_id)["suffix"]
        for helper in entry["planned_helpers"]:
            name = str(helper["name"])
            if not name.endswith(required_suffix):
                raise SystemExit(
                    f"planned helper `{name}` must use owner suffix `{required_suffix}`"
                )
            if name in helper_names:
                raise SystemExit(f"duplicate planned helper name: {name}")
            helper_names.add(name)
    return entries
