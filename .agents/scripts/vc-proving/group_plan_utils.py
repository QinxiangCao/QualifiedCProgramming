"""Validate the VC owner's plan and derive one group representation."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from proof_manual_utils import HELPER_NAMESPACE_SUFFIX_RE, helper_namespace_for_group_id

PROOF_MODES = {"LLM_pre_process", "aggressive_pre_process"}


def group_witness_names(group: dict[str, Any]) -> list[str]:
    return [item["name"] for item in group["witnesses"]]


def group_aggressive_split_goal_names(group: dict[str, Any]) -> list[str]:
    return [split["name"] for witness in group["witnesses"]
            if witness["proof_mode"] == "aggressive_pre_process"
            for split in witness["split_goals"]]


def group_check_names(group: dict[str, Any]) -> list[str]:
    return group_witness_names(group) + group_aggressive_split_goal_names(group)


def load_group_plan(path: Path) -> dict[str, Any]:
    plan = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(plan, dict):
        raise ValueError(f"group plan must contain an object: {path}")
    return plan


def _fields(value: Any, required: set[str], optional: set[str], label: str) -> None:
    if not isinstance(value, dict) or not required <= value.keys() or value.keys() - required - optional:
        raise ValueError(f"{label} requires {sorted(required)} with optional {sorted(optional)}")


def _strategy(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{label} requires a nonempty proof strategy")
    return value.strip()


def group_entries_from_plan(vc_index: dict[str, Any], plan: dict[str, Any]) -> list[dict[str, Any]]:
    """Cover every top-level VC exactly once, preserving the owner's plan order."""
    _fields(plan, {"groups"}, set(), "group plan")
    if not isinstance(plan["groups"], list):
        raise ValueError("group plan groups must be a list")
    known = set(vc_index["top_level"])
    seen: set[str] = set()
    ids: set[str] = set()
    helper_names: set[str] = set()
    groups: list[dict[str, Any]] = []
    for raw in plan["groups"]:
        _fields(raw, {"id", "estimated_difficulty", "witnesses"}, {"helpers"}, "proof group")
        group_id = raw["id"]
        namespace = helper_namespace_for_group_id(group_id)
        if group_id in ids:
            raise ValueError(f"duplicate proof group id: {group_id}")
        ids.add(group_id)
        difficulty = raw["estimated_difficulty"]
        if type(difficulty) is not int or not 1 <= difficulty <= 5:
            raise ValueError(f"group `{group_id}` estimated_difficulty must be an integer from 1 to 5")
        if not isinstance(raw["witnesses"], list) or not raw["witnesses"]:
            raise ValueError(f"group `{group_id}` must contain witnesses")
        witnesses = []
        for item in raw["witnesses"]:
            if not isinstance(item, dict):
                raise ValueError("each witness must be an object")
            mode = item.get("proof_mode")
            if not isinstance(mode, str) or mode not in PROOF_MODES:
                raise ValueError("witness has an unsupported proof_mode")
            aggressive = mode == "aggressive_pre_process"
            _fields(item, {"name", "proof_mode", "split_strategies" if aggressive else "strategy"}, set(), "witness")
            name = item["name"]
            if not isinstance(name, str) or name not in known:
                raise ValueError(f"group `{group_id}` references unknown witness: {name!r}")
            if name in seen:
                raise ValueError(f"group `{group_id}` repeats witness: {name}")
            seen.add(name)
            splits = vc_index["split_goals"][name]
            if aggressive:
                strategies = item["split_strategies"]
                if not splits or not isinstance(strategies, dict) or list(strategies) != splits:
                    raise ValueError(f"witness `{name}` split_strategies must match generated split goals in order")
                for split, strategy in strategies.items():
                    _strategy(strategy, f"split goal `{split}`")
            else:
                strategies = {}
            witness = {
                "name": name, "goal": vc_index["by_name"][name], "proof_mode": mode,
                "split_goals": [{"name": split, "goal": vc_index["by_name"][split],
                                  **({"strategy": strategies[split]} if aggressive else {})}
                                 for split in splits],
            }
            if not aggressive:
                witness["strategy"] = _strategy(item["strategy"], f"witness `{name}`")
            witnesses.append(witness)
        helpers = raw.get("helpers", [])
        if not isinstance(helpers, list):
            raise ValueError(f"group `{group_id}` helpers must be a list")
        for helper in helpers:
            _fields(helper, {"name", "strategy", "visibility"}, set(), "helper")
            name = helper["name"]
            suffix = HELPER_NAMESPACE_SUFFIX_RE.search(name) if isinstance(name, str) else None
            if suffix is None or suffix.group() != namespace["suffix"]:
                raise ValueError(f"helper `{name}` must use owner suffix `{namespace['suffix']}`")
            if name in helper_names:
                raise ValueError(f"duplicate planned helper name: {name}")
            helper_names.add(name)
            _strategy(helper["strategy"], f"helper `{name}`")
            if helper["visibility"] not in ("local", "public"):
                raise ValueError("helper visibility must be local or public")
        groups.append({"id": group_id, "estimated_difficulty": difficulty,
                       "witnesses": witnesses, "helpers": helpers, "helper_namespace": namespace})
    if seen != known:
        raise ValueError("group plan does not cover exactly the current witness set")
    return groups
