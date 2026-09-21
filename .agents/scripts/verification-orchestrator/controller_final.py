"""Validate the current proof candidate, publish it, and check current obligations."""
from __future__ import annotations

import json
import os
import re
import shutil
from pathlib import Path

from annotation_refresh import AnnotationRefreshError, file_contents, publish_file_contents, rollback_publication
from controller_control import control_signal_path
from controller_rounds import require_action
from controller_state import (
    GENERATED_KEYS, _append_event, _current_files_errors, _formal_case_lib_is_active,
    _load_state, _save_state, _utc, load_run, require_attempt,
)
from coq_tooling import audit_formal_case_lib_closure, run_coqc_check
from coq_tooling_common import normalize_current_source_texts
from path_utils import fixed_path_under, path_is_link_like, run_builds_root
from process_adapter import control_signal_requests_stop
from proof_manual_utils import (
    HELPER_DECL_KINDS, HELPER_NAMESPACE_SUFFIX_RE, Manual, coq_token_text,
    incomplete_proof_markers, mask_coq_strings, parse_manual, proof_mode_errors,
    strip_coq_comments, top_level_commands, unsafe_commands,
)
from proving import FORBIDDEN_TOKENS, Library, _parse_library
from spec_freeze import spec_freeze_findings
from symexec_tooling import clean_output_freshness, run_symexec, symexec_profile_for_state

FINAL_ROLES = ("proof_manual_file", "formal_case_lib")
CHECK_ERRORS = (OSError, ValueError, TypeError, KeyError, SystemExit, AnnotationRefreshError)


class CheckInterrupted(RuntimeError):
    def __init__(self, status: str, message: str):
        super().__init__(message)
        self.status = status


def _checkpoint(state: dict, command: str) -> dict:
    """A long check may finish after pause or another controller action."""
    fresh = _load_state(Path(state["run_root"]))
    if fresh["run_control"]["status"] == "paused" or control_signal_requests_stop(control_signal_path(fresh)):
        raise CheckInterrupted("paused", "The check stopped before committing; resume the run before retrying.")
    if fresh["generation"] != state["generation"]:
        raise CheckInterrupted("interrupted", "Controller state changed during the check; follow its current action.")
    require_action(fresh, command)
    return fresh


def _context(state: dict):
    from controller_proving import _context as proving_context
    candidate = state.get("final_candidate")
    if not isinstance(candidate, dict) or set(candidate) != {"round"}:
        raise ValueError("final candidate must name the current proving task")
    task = require_attempt(state, candidate["round"], "vc-proving")
    if task["status"] != "accepted":
        raise ValueError("final candidate requires an accepted proving task")
    return proving_context(state, task)


def _publication(state: dict) -> tuple[Path, dict[str, str]]:
    record = state.get("final_apply_transaction")
    if not isinstance(record, dict) or set(record) != {"roles", "status"}:
        raise ValueError("final publication record is missing or malformed")
    roles = record["roles"]
    if not isinstance(roles, list) or roles != [role for role in FINAL_ROLES if role in roles]:
        raise ValueError("invalid final publication roles")
    reports = Path(state["report_root"])
    backup = fixed_path_under(reports / "final-check/backup", reports, label="final publication backup")
    return backup, {role: state["target_files"][role] for role in roles}


def _rollback(state: dict) -> str | None:
    try:
        backup, files = _publication(state)
        if backup.exists():
            rollback_publication(main_root=Path(state["main_root"]), target_files=files, transaction=backup)
        elif state["final_apply_transaction"]["status"] != "preparing":
            raise ValueError("final publication backup is missing")
        state["final_apply_transaction"]["status"] = "rolled-back"
    except CHECK_ERRORS as exc:
        return str(exc)
    return None


def _forbidden(text: str) -> list[str]:
    code = mask_coq_strings(strip_coq_comments(text))
    return [f"forbidden lemma/tactic: {token}" for token in FORBIDDEN_TOKENS
            if re.search(rf"(?<![A-Za-z0-9_']){re.escape(token)}(?![A-Za-z0-9_'])", code)]


def _manual_errors(raw: Manual | None, proved: Manual | None, groups: list[dict],
                   *, root: Path, raw_root: Path, target: dict) -> list[str]:
    if raw is None or proved is None:
        return [] if raw is proved else ["fresh and proved manual presence differ"]
    errors = []
    relative = Path(target["proof_manual_file"])
    sources = [Path(target[role]) for role in ("formal_case_lib", *GENERATED_KEYS)]
    preludes = [normalize_current_source_texts(workspace_root=root, build_workspace=raw_root,
                texts={relative: manual.prelude}, sources=sources)[relative] for manual in (raw, proved)]
    if coq_token_text(preludes[0]) != coq_token_text(preludes[1]):
        errors.append("manual prelude or scope changed")
    if list(raw.by_name) != list(proved.by_name):
        errors.append("manual declaration order or VC set changed")
    routes = {witness["name"]: witness["proof_mode"] for group in groups for witness in group["witnesses"]}
    for name, vc in raw.vc_index["by_name"].items():
        current = proved.vc_index["by_name"].get(name)
        if current is None:
            continue
        if coq_token_text(vc["statement"]) != coq_token_text(current["statement"]):
            errors.append(f"statement changed: {name}")
        parent = vc["parent"]
        mode = routes.get(parent or name)
        if mode is None:
            errors.append(f"missing proof route: {name}")
            continue
        block = proved.by_name[name]["block"]
        for marker in incomplete_proof_markers(block):
            if not (parent and mode == "LLM_pre_process" and marker["kind"] == "Abort"):
                errors.append(f"{name} contains {marker['kind']}")
        if parent is None or mode == "aggressive_pre_process":
            errors.extend(f"{name}: {message}" for message in proof_mode_errors(
                block, "LLM_pre_process" if parent else mode))
    commands = top_level_commands(proved.text, include_proof_commands=True)
    errors.extend(f"unsafe command: {command['kind']}" for command in unsafe_commands(commands))
    if any(command["kind"] in {"Definition", "Fixpoint", "CoFixpoint", "Inductive", "CoInductive", "Notation"}
           for command in commands):
        errors.append("manual contains a forbidden declaration")
    top = [command for command in commands if not command["in_proof"]]
    prelude_count = len(top_level_commands(proved.prelude))
    if [command["name"] for command in top[prelude_count:]] != list(raw.by_name):
        errors.append("manual contains an extra top-level command")
    errors.extend(_forbidden(proved.text))
    return errors


def _library_errors(original: Library | None, candidate: Library | None, groups: list[dict],
                    *, root: Path, staging_root: Path, target: dict) -> list[str]:
    if candidate is None:
        return [] if original is None else ["active case library is missing"]
    errors = list(candidate.errors)
    if original is not None:
        relative = Path(target["formal_case_lib"])
        sources = [Path(target[role]) for role in ("formal_case_lib", *GENERATED_KEYS)]
        seed, current = [coq_token_text(normalize_current_source_texts(
            workspace_root=root, build_workspace=staging_root, texts={relative: library.text}, sources=sources,
        )[relative]).splitlines() for library in (original, candidate)]
        if current[:len(seed)] != seed:
            errors.append("case library must preserve the complete annotation seed before all additions")
    existing = {item["name"] for item in original.declarations} if original else set()
    suffixes = {group["helper_namespace"]["suffix"] for group in groups}
    for item in candidate.declarations:
        if item["kind"] in HELPER_DECL_KINDS and item["name"] not in existing:
            suffix = HELPER_NAMESPACE_SUFFIX_RE.search(item["name"])
            if suffix is None or suffix.group() not in suffixes:
                errors.append(f"helper must use a current group suffix: {item['name']}")
    return errors


def _parse_candidates(contents: dict, forbidden_modules):
    manual = contents.get("proof_manual_file")
    library = contents.get("formal_case_lib")
    return (parse_manual(manual.decode("utf-8")) if manual is not None else None,
            _parse_library(library.decode("utf-8"), forbidden_modules) if library is not None else None)


def _compile(state: dict, stage: str, overlays=None) -> dict:
    target = state["target_files"]
    return run_coqc_check(workspace_root=Path(state["main_root"]),
                         build_workspace=run_builds_root(Path(state["run_root"])) / stage / "src",
                         target_file=Path(target["goal_check_file"]), target_kind="check",
                         current_case_anchor=Path(target["proof_auto_file"]), overlays=overlays)


def _finish(state: dict, command: str, errors: list, *, conflict: str | None = None, **details) -> int:
    status = "failed" if errors else "passed"
    state["current_blockers"] = [{"failure_class": "publication-conflict", "message": conflict}] if conflict else []
    state[command.replace("-", "_")] = {"status": status, "checked_at": _utc(), "errors": errors, **details}
    run = Path(state["run_root"])
    _save_state(run, state)
    _append_event(run, state, command + "-" + status)
    print(json.dumps({"status": status, "phase": state["phase"], "errors": errors,
                      **({"blockers": state["current_blockers"]} if conflict else {})}, indent=2))
    return int(bool(errors))


def final_apply(args) -> int:
    state = load_run(args)
    require_action(state, "final-apply")
    try:
        if state.get("final_apply_transaction"):
            conflict = _rollback(state)
            if conflict:
                return _finish(state, "final-apply", [conflict], conflict=conflict)
            backup, _files = _publication(state)
            if backup.exists():
                shutil.rmtree(backup)
            state.pop("final_apply_transaction")
            _save_state(Path(state["run_root"]), state)
        ctx = _context(state)
        target = state["target_files"]
        files = {role: target[role] for role in FINAL_ROLES}
        merged = fixed_path_under(ctx.directory / "proving_merged", ctx.directory, label="latest proof candidate")
        candidates = {role: Path(relative).name for role, relative in files.items()}
        payloads = file_contents(merged, candidates)
        originals = file_contents(ctx.main_root, files)
        if (payloads["formal_case_lib"] is not None) != _formal_case_lib_is_active(state):
            raise ValueError("candidate case library presence differs from the run policy")
        if any(payloads[role] is None and originals[role] is not None for role in FINAL_ROLES):
            raise ValueError("candidate is missing a current formal file")
        active = {role: relative for role, relative in files.items() if payloads[role] is not None}
        check = _compile(state, "final-apply", {Path(relative): merged / candidates[role] for role, relative in active.items()})
        state = _checkpoint(state, "final-apply")
        if check.get("status") != "passed":
            return _finish(state, "final-apply", [check.get("first_failure") or check])
        # Validate and publish the exact staged source bytes that Rocq compiled.
        checked = run_builds_root(ctx.run_root) / "final-apply/src"
        payloads = file_contents(checked, active)
        manual, library = _parse_candidates(payloads, ctx.forbidden_modules)
        errors = _manual_errors(ctx.manual, manual, ctx.groups, root=ctx.main_root, raw_root=ctx.main_root, target=target)
        errors.extend(_library_errors(ctx.library_model, library, ctx.groups,
                                      root=ctx.main_root, staging_root=checked, target=target))
        if errors:
            return _finish(state, "final-apply", errors)
        state["final_apply_transaction"] = {"roles": list(active), "status": "preparing"}
        _save_state(ctx.run_root, state)
        state = _checkpoint(state, "final-apply")
        backup, _files = _publication(state)
        publish_file_contents(main_root=ctx.main_root, target_files=active, payloads=payloads,
                              transaction=backup, expected={role: originals[role] for role in active}, keep_backup=True)
        state = _checkpoint(state, "final-apply")
        state["final_apply_transaction"]["status"] = "applied"
        state["final_apply"] = {"status": "applied", "applied_at": _utc(), "files": list(active.values())}
        state["phase"] = "final-check"
        state["current_blockers"] = []
        _save_state(ctx.run_root, state)
        _append_event(ctx.run_root, state, "final-candidate-applied", files=list(active.values()))
        print(json.dumps({"status": "passed", "files": list(active.values())}, indent=2))
        return 0
    except CheckInterrupted as exc:
        print(json.dumps({"status": exc.status, "message": str(exc)}))
        return 1
    except CHECK_ERRORS as exc:
        try:
            state = _checkpoint(state, "final-apply")
        except (CheckInterrupted, *CHECK_ERRORS) as changed:
            print(json.dumps({"status": getattr(changed, "status", "interrupted"), "message": str(changed)}))
            return 1
        conflict = _rollback(state) if state.get("final_apply_transaction") else None
        return _finish(state, "final-apply", [str(exc)], conflict=conflict)


def _side_products(state: dict) -> list[Path]:
    root, run = Path(state["main_root"]), Path(state["run_root"])
    suffixes = {".vo", ".vos", ".vok", ".glob", ".aux"}
    paths = set()
    def collect(path):
        if not os.path.lexists(path):
            return
        if path_is_link_like(path):
            raise OSError(f"cleanup encountered a link/reparse file: {path}")
        if path.is_file():
            paths.add(path)
        elif not path.is_dir():
            raise OSError(f"cleanup encountered a nonregular file: {path}")
    for role in ("formal_case_lib", *GENERATED_KEYS):
        source = root / state["target_files"][role]
        for path in [*(source.with_suffix(suffix) for suffix in suffixes), source.with_name(f".{source.stem}.aux")]:
            collect(path)
    def scan_error(error):
        raise error
    for directory, directories, files in os.walk(run, onerror=scan_error):
        parent = Path(directory)
        if parent == run:
            directories[:] = [name for name in directories if name != "_coq_builds"]
        if any(path_is_link_like(parent / name) for name in directories):
            raise OSError(f"cleanup encountered a link/reparse directory: {parent}")
        for name in files:
            if Path(name).suffix in suffixes:
                collect(parent / name)
    return sorted(paths)


def final_check(args) -> int:
    state = load_run(args)
    require_action(state, "final-check")
    if (state.get("final_apply") or {}).get("status") != "applied":
        raise SystemExit("final-check requires an applied candidate")
    errors = []
    removed = 0
    try:
        errors = _current_files_errors(state)
        if errors:
            raise ValueError(errors[0])
        root, target = Path(state["main_root"]), state["target_files"]
        inputs = {role: target[role] for role in ("c_file", "formal_case_lib", *GENERATED_KEYS)}
        before = file_contents(root, inputs)
        def unchanged_inputs():
            if file_contents(root, inputs) != before:
                raise ValueError("current verification inputs changed during final-check")
        ctx = _context(state)
        for path in _side_products(state):
            path.unlink()
            removed += 1
        profile = symexec_profile_for_state(state)
        refresh = Path(state["report_root"]) / "final-check/symexec-refresh"
        freshness = clean_output_freshness(
            main_root=ctx.main_root, target_c_file=Path(target["c_file"]), target_files=target,
            reference_root=ctx.main_root, refresh_root=refresh, manual_mode="proved", symexec_runner=run_symexec,
            timeout_seconds=float(profile["timeout_seconds"]), profile_name=str(profile["name"]),
            heartbeat_seconds=float(profile["heartbeat_seconds"]),
            cancel_requested=lambda: control_signal_requests_stop(control_signal_path(state)),
            progress_path=refresh.parent / "symexec-progress.json",
        )
        state = _checkpoint(state, "final-check")
        unchanged_inputs()
        if freshness.get("status") != "passed":
            errors.append({"kind": "current-obligations", "evidence": freshness})
        check = _compile(state, "final-check")
        state = _checkpoint(state, "final-check")
        unchanged_inputs()
        if check.get("status") != "passed":
            errors.append({"kind": "current-proof", "evidence": check})
        fresh_payload = file_contents(refresh, {"proof_manual_file": target["proof_manual_file"]})
        raw, _library = _parse_candidates(fresh_payload, ())
        errors.extend(_manual_errors(raw, ctx.manual, ctx.groups, root=ctx.main_root, raw_root=refresh, target=target))
        if _formal_case_lib_is_active(state):
            backup, _files = _publication(state)
            original = file_contents(backup, {"formal_case_lib": "formal_case_lib.original"})
            _manual, seed = _parse_candidates(original, ctx.forbidden_modules)
            errors.extend(_library_errors(seed, ctx.library_model, ctx.groups, root=ctx.main_root,
                                          staging_root=run_builds_root(ctx.run_root) / "final-check/src", target=target))
            audit = audit_formal_case_lib_closure(workspace_root=ctx.main_root,
                build_workspace=run_builds_root(ctx.run_root) / "final-check/src",
                formal_case_lib=Path(target["formal_case_lib"]), current_case_anchor=Path(target["proof_auto_file"]))
            state = _checkpoint(state, "final-check")
            unchanged_inputs()
            if audit.get("status") != "passed":
                errors.append({"kind": "case-library-closure", "evidence": audit})
        errors.extend(spec_freeze_findings(state.get("spec_freeze"), c_file=ctx.main_root / target["c_file"],
                                           lib_file=ctx.main_root / target["formal_case_lib"]))
        if _side_products(state):
            errors.append("current module side products remain after final checks")
        state = _checkpoint(state, "final-check")
        unchanged_inputs()
    except CheckInterrupted as exc:
        print(json.dumps({"status": exc.status, "message": str(exc)}))
        return 1
    except CHECK_ERRORS as exc:
        try:
            state = _checkpoint(state, "final-check")
        except (CheckInterrupted, *CHECK_ERRORS) as changed:
            print(json.dumps({"status": getattr(changed, "status", "interrupted"), "message": str(changed)}))
            return 1
        errors.append(str(exc))
    conflict = _rollback(state) if errors else None
    if errors:
        state["phase"] = "final-apply"
        state["final_apply"]["status"] = "rollback-failed" if conflict else "rolled-back"
        if conflict:
            errors.append(conflict)
    else:
        state.update(phase="done", finished_at=_utc())
    return _finish(state, "final-check", errors, conflict=conflict, cleanup_removed_count=removed)
