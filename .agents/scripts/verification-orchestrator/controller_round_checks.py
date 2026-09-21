"""Role acceptance checks. Owner lifecycle and state transitions live elsewhere."""
from __future__ import annotations

from pathlib import Path

from annotation_design import annotation_plan_errors
from annotation_refresh import file_contents
from controller_state import (
    GENERATED_KEYS, _archive_annotation_stage, _formal_case_lib_is_active, _json_load, _manual_obligations, attempt_paths,
)
from file_integrity import _lexical_regular_file_snapshot, _snapshot_text
from group_plan_utils import group_entries_from_plan
from proof_manual_utils import coq_token_text, lemma_proof_parts, parse_manual
from spec_freeze import extract_spec_surface, spec_freeze_findings


def _failure(errors: list[str]) -> dict:
    return {"status": "failed", "errors": errors, "recoverable": True}


def _manual_signature(text: str) -> tuple:
    manual = parse_manual(text)
    declarations = []
    for lemma in manual.lemmas:
        statement, proof, trailing = lemma_proof_parts(lemma)
        tokens = coq_token_text(proof).splitlines()
        retained, index = [], 0
        while index < len(tokens):
            if tokens[index:index + 2] == ["Show", "."]:
                index += 2
            else:
                retained.append(tokens[index])
                index += 1
        declarations.append((lemma["name"], coq_token_text(statement), tuple(retained), coq_token_text(trailing)))
    return coq_token_text(manual.prelude), tuple(declarations)


def debug_manual_errors(state: dict, task: dict) -> list[str]:
    root = Path(state["main_root"])
    source = state["target_files"]["proof_manual_file"]
    debug = attempt_paths(state, task)["debug_manual"]
    raw = _snapshot_text(_lexical_regular_file_snapshot(root=root, relative=source, label="canonical manual"), label="canonical manual")
    copied = _snapshot_text(_lexical_regular_file_snapshot(root=root, relative=debug.relative_to(root).as_posix(), label="debug manual"), label="debug manual")
    if _manual_signature(raw) != _manual_signature(copied):
        return ["VC debug manual may only add Show commands inside proof bodies"]
    return []


def annotation_accept(state: dict, task: dict) -> dict:
    from controller_tools import library_check, refresh_annotation
    paths = attempt_paths(state, task)
    plan = _json_load(paths["plan"])
    errors = annotation_plan_errors(plan)
    root, target = Path(state["main_root"]), state["target_files"]
    freeze = spec_freeze_findings(state.get("spec_freeze"), c_file=root / target["c_file"],
                                 lib_file=root / target["formal_case_lib"])
    errors.extend(f"frozen specification changed: {item}" for item in freeze)
    if errors:
        return _failure(errors)
    generated = refresh_annotation(state, task, progress_name="symexec-progress-acceptance.json")
    if generated["status"] != "passed":
        return generated
    errors = annotation_plan_errors(plan, failed_vcs=task["failed_vcs"], current_vcs=_manual_obligations(state))
    if errors:
        return _failure(errors)
    files = {role: target[role] for role in ("c_file", "formal_case_lib", *GENERATED_KEYS)}
    checked_inputs = file_contents(root, files)
    library = library_check(state, task)
    if library["status"] != "passed":
        return library
    if file_contents(root, files) != checked_inputs:
        return _failure(["annotation inputs changed during library validation"])
    _archive_annotation_stage(state, task, "after")
    if file_contents(root, files) != checked_inputs:
        return _failure(["annotation inputs changed before acceptance"])
    record = state.get("spec_freeze")
    if record and record["baseline"] is None:
        record["baseline"] = extract_spec_surface(root / target["c_file"], root / target["formal_case_lib"])
    return {"status": "passed"}


def vc_accept(state: dict, task: dict) -> dict:
    errors = debug_manual_errors(state, task)
    if errors:
        return _failure(errors)
    plan = _json_load(attempt_paths(state, task)["group_plan"])
    groups = group_entries_from_plan(_manual_obligations(state), plan)
    for group in groups:
        if len(group["witnesses"]) > state["max_witnesses_per_group"]:
            errors.append(f"group {group['id']} exceeds the witness limit")
        if group["helpers"] and not _formal_case_lib_is_active(state):
            errors.append("helpers require an active case library")
    return _failure(errors) if errors else {"status": "passed"}
