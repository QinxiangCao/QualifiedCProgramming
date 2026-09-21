"""Current proof groups: load once, copy, validate, and mechanically merge.

Controller state supplies identities. This module writes no manifests, tracks
no owner lifecycle, and never compiles or rewrites a submitted proof.
"""

from __future__ import annotations

import json
import re
from collections.abc import Collection
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from file_integrity import _lexical_regular_file_snapshot
from group_plan_utils import group_entries_from_plan
from path_utils import (
    fixed_path_under, group_worker_commands, init_group_worker_files,
    path_is_link_like, prepare_group_directory, slug, write_bytes,
)
from proof_manual_utils import (
    HELPER_DECL_KINDS, HELPER_NAMESPACE_SUFFIX_RE, Manual, block_has_incomplete_proof,
    coq_token_text, incomplete_proof_markers, is_official_library_import,
    lemma_proof_parts, lib_contract_errors, mask_coq_strings, parse_lib_declarations,
    parse_manual, proof_mode_errors, strip_coq_comments, top_level_commands,
    unsafe_commands,
)

FORBIDDEN_LEMMAS = (
    "logic_equiv_refl",
    "elim_wand_emp_emp",
    "logic_equiv_symm",
    "sepcon_emp_logic_equiv'",
    "logic_equiv_andp_comm",
    "logic_equiv_sepcon_comm",
    "logic_equiv_sepcon_emp",
    "logic_equiv_andp_truep",
    "logic_equiv_truep_andp",
    "truep_andp_right_equiv",
    "logic_equiv_orp_comm",
    "logic_equiv_trans",
    "logic_equiv_orp_assoc",
    "logic_equiv_sepcon_assoc",
    "logic_equiv_andp_assoc",
    "logic_equiv_sepcon_orp",
    "logic_equiv_sepcon_orp_distr",
    "logic_equiv_orp_sepcon",
    "derivable1_trans",
    "derivable1_refl",
    "derivable1_sepcon_comm",
    "coq_prop_andp_right",
    "derivable1_sepcon_mono",
    "logic_equiv_coq_prop_andp_sepcon",
    "derivable1_sepcon_assoc1",
    "derivable1_sepcon_assoc2",
    "derivable1_orp_assoc1",
    "derivable1_andp_assoc",
    "provable_sepcon_assoc",
    "provable_sepcon_assoc1",
    "provable_sepcon_assoc2",
    "provable_orp_assoc",
    "provable_andp_assoc",
)

FORBIDDEN_TACTICS = (
    "entailer!",
    "pre_process",
)

FORBIDDEN_TOKENS = FORBIDDEN_LEMMAS + FORBIDDEN_TACTICS



def _forbidden_findings(text: str) -> list[str]:
    code = mask_coq_strings(strip_coq_comments(text))
    return [token for token in FORBIDDEN_TOKENS
            if re.search(rf"(?<![A-Za-z0-9_']){re.escape(token)}(?![A-Za-z0-9_'])", code)]


def _snapshot(path: Path, root: Path) -> bytes | None:
    item = _lexical_regular_file_snapshot(root=root, relative=path.relative_to(root).as_posix(), label="formal source")
    if item["state"] not in {"present", "missing"}:
        raise ValueError(item.get("message") or f"invalid formal source: {path}")
    return item.get("data")


@dataclass
class Library:
    text: str
    tokens: list[str]
    declarations: list[dict[str, Any]]
    commands: list[dict[str, Any]]
    errors: list[str]


def _parse_library(text: str, forbidden_modules: Collection[str]) -> Library:
    commands = top_level_commands(text, include_proof_commands=True)
    errors = lib_contract_errors(text, forbidden_modules=forbidden_modules, commands=commands)
    errors.extend(f"library uses forbidden lemma/tactic `{name}`" for name in _forbidden_findings(text))
    return Library(text, coq_token_text(text).splitlines(), parse_lib_declarations(text),
                   [item for item in commands if not item["in_proof"]], errors)


@dataclass
class ProvingContext:
    main_root: Path
    run_root: Path
    round_id: str
    directory: Path
    report_directory: Path
    group_plan_path: Path
    proof_manual: Path
    formal_case_lib: Path
    groups: list[dict[str, Any]]
    manual: Manual | None
    library: str | None
    forbidden_modules: tuple[str, ...]
    files: dict[str, bytes] = field(repr=False)
    library_model: Library | None = field(repr=False)


def load_proving_context(
    *, main_root: Path, run_root: Path, round_id: str, group_plan_path: Path,
    proof_manual: Path, formal_case_lib: Path, previous_round: str | None = None,
    forbidden_modules: Collection[str] = (),
) -> ProvingContext:
    """Read current canonical sources and the accepted plan exactly once."""
    root_input = main_root.expanduser().absolute()
    root = fixed_path_under(root_input, root_input, label="main root")
    run = fixed_path_under(run_root, root, label="run root")
    if run.parent != root / "verification_runs":
        raise ValueError("run root must be a direct child of verification_runs")
    if not isinstance(round_id, str) or not round_id or slug(round_id) != round_id:
        raise ValueError("proving round must be a fixed directory name")
    directory = fixed_path_under(run / round_id, run, label="proving directory")
    reports = fixed_path_under(root / "reports" / run.name, root, label="run reports")
    report = fixed_path_under(reports / "rounds" / round_id, reports, label="proving reports")
    plan_path = fixed_path_under(group_plan_path, reports, label="accepted group plan")
    manual_path = fixed_path_under(proof_manual, root, label="current manual")
    library_path = fixed_path_under(formal_case_lib, root, label="current case library")
    manual_rel, library_rel = manual_path.relative_to(root), library_path.relative_to(root)
    if (not manual_rel.parts or manual_rel.parts[0] != "Rocq" or not manual_rel.name.endswith("_proof_manual.v")
        or library_rel != manual_rel.with_name(manual_rel.name.removesuffix("_proof_manual.v") + "_lib.v")):
        raise ValueError("manual and library must be one canonical Rocq case family")
    manual_bytes, library_bytes = _snapshot(manual_path, root), _snapshot(library_path, root)
    manual = parse_manual(manual_bytes.decode("utf-8")) if manual_bytes is not None else None
    library = library_bytes.decode("utf-8") if library_bytes is not None else None
    index = manual.vc_index if manual else {"top_level": [], "by_name": {}, "split_goals": {}}
    plan_bytes = _snapshot(plan_path, root)
    if plan_bytes is None:
        raise ValueError("accepted group plan is missing")
    groups = group_entries_from_plan(index, json.loads(plan_bytes.decode("utf-8")))
    if library is None and any(group["helpers"] for group in groups):
        raise ValueError("planned helpers require a current formal_case_lib")
    if previous_round is not None and (
        not isinstance(previous_round, str) or not previous_round or slug(previous_round) != previous_round
        or previous_round == round_id
    ):
        raise ValueError("previous proving round must be another fixed directory in this run")
    for number, group in enumerate(groups):
        name = f"group_{number:02d}__{slug(group['id'])}"
        group_dir = fixed_path_under(directory / "groups" / name, directory, label="group directory")
        group_report = fixed_path_under(report / "groups" / name, report, label="group report")
        group.update({
            "index": number, "directory": str(group_dir), "report_directory": str(group_report),
            "proof_manual": str(group_dir / manual_path.name),
            "proof_reuse": str(group_report / "proof_reuse.md"),
            "annotation_history_directory": str(run / "annotation_history"),
            "commands": group_worker_commands(main_root=root, run_root=run, round_id=round_id,
                                               group_id=group["id"], group_directory=group_dir),
        })
        if library is not None:
            group["group_worker_lib"] = str(group_dir / library_path.name)
        if previous_round is not None:
            group["previous_proving_round"] = str(fixed_path_under(run / previous_round, run, label="previous proving round"))
    files = {path.name: content for path, content in ((manual_path, manual_bytes), (library_path, library_bytes))
             if content is not None}
    modules = tuple(forbidden_modules)
    return ProvingContext(root, run, round_id, directory, report, plan_path, manual_rel, library_rel,
                          groups, manual, library, modules, files,
                          _parse_library(library, modules) if library is not None else None)


def prepare_groups(context: ProvingContext) -> list[dict[str, Any]]:
    """Copy current inputs, then write each owner's handoff. History stays read-only."""
    context.directory.mkdir(parents=True, exist_ok=True)
    context.report_directory.mkdir(parents=True, exist_ok=True)
    for group in context.groups:
        prepare_group_directory(groups_root=context.directory / "groups", group_id=group["id"],
                                index=group["index"], files=context.files, run_root=context.run_root, force=True)
        init_group_worker_files(report_dir=Path(group["report_directory"]), group=group,
                                formal_case_lib=context.formal_case_lib.as_posix() if context.library is not None else None,
                                commands=group["commands"])
    return context.groups


def _library_additions(seed: Library, candidate: Library, group: dict[str, Any]) -> tuple[list[dict[str, Any]], list[str]]:
    """Require an unchanged seed prefix and standalone official imports/proved helpers."""
    errors = [*seed.errors, *candidate.errors]
    if candidate.tokens[:len(seed.tokens)] != seed.tokens:
        errors.append("group_worker_lib must preserve the complete seed before all additions")
    commands = candidate.commands[len(seed.commands):]
    declarations = candidate.declarations[len(seed.declarations):]
    seed_names = {item["name"] for item in seed.declarations if item["kind"] != "Import"}
    parsed = {(item["kind"], item["name"]) for item in declarations}
    suffix = group["helper_namespace"]["suffix"]
    for command in commands:
        kind, name = command["kind"], command["name"]
        if kind in {"From", "Require"}:
            continue
        if kind not in HELPER_DECL_KINDS or (kind, name) not in parsed:
            errors.append(f"new top-level command `{name}` has forbidden or unparseable kind `{kind}`")
    additions = []
    seen = set(seed_names)
    for declaration in declarations:
        kind, name = declaration["kind"], declaration["name"]
        if kind == "Import":
            if not is_official_library_import(name):
                errors.append(f"new import `{name}` is not an allowed official Rocq import")
        elif kind not in HELPER_DECL_KINDS:
            errors.append(f"new declaration `{name}` has forbidden kind `{kind}`")
        else:
            if name in seen:
                errors.append(f"duplicate helper declaration `{name}`")
            seen.add(name)
            match = HELPER_NAMESPACE_SUFFIX_RE.search(name)
            if match is None or match.group() != suffix:
                errors.append(f"helper `{name}` must use current suffix `{suffix}`")
            if block_has_incomplete_proof(declaration["block"]):
                errors.append(f"helper `{name}` must contain a complete proof")
        additions.append({**declaration, "group_id": group["id"]})
    # Every new import must also have a complete standalone declaration block.
    if sum(item["kind"] in {"From", "Require"} for item in commands) != sum(item["kind"] == "Import" for item in declarations):
        errors.append("new import command is not a standalone parseable block")
    return additions, errors


def _manual_errors(seed: Manual, candidate: Manual, group: dict[str, Any], complete: bool) -> list[str]:
    errors = []
    routes = {witness["name"]: witness["proof_mode"] for witness in group["witnesses"]}
    routes.update({split["name"]: "LLM_pre_process" for witness in group["witnesses"]
                   if witness["proof_mode"] == "aggressive_pre_process" for split in witness["split_goals"]})
    if coq_token_text(seed.prelude) != coq_token_text(candidate.prelude):
        errors.append("protected manual prelude tokens changed")
    if list(seed.by_name) != list(candidate.by_name):
        errors.append("copied manual declaration order or witness set changed")
    for name, original in seed.by_name.items():
        current = candidate.by_name.get(name)
        if current is None:
            continue
        if name not in routes:
            if coq_token_text(original["block"]) != coq_token_text(current["block"]):
                errors.append(f"protected unassigned block `{name}` tokens changed")
            continue
        try:
            old_statement, _old_proof, old_tail = lemma_proof_parts(original)
            statement, _proof, tail = lemma_proof_parts(current)
        except ValueError as exc:
            errors.append(f"editable block `{name}` cannot be parsed: {exc}")
            continue
        if coq_token_text(statement) != coq_token_text(old_statement):
            errors.append(f"protected statement of `{name}` changed")
        if coq_token_text(tail) != coq_token_text(old_tail):
            errors.append(f"protected tokens after `{name}` changed")
        markers = incomplete_proof_markers(current["block"])
        if any(item["kind"] == "Admitted" or complete for item in markers):
            errors.append(f"witness `{name}` contains Admitted/Abort")
        if complete:
            errors.extend(f"witness `{name}` {message}" for message in proof_mode_errors(current["block"], routes[name]))
    commands = top_level_commands(candidate.text, include_proof_commands=True)
    errors.extend(f"manual contains unsafe command `{item['kind']}`" for item in unsafe_commands(commands))
    top = [item for item in commands if not item["in_proof"]]
    if any(item["kind"] in {"Definition", "Fixpoint", "CoFixpoint", "Inductive", "CoInductive", "Notation"} for item in commands):
        errors.append("manual contains forbidden top-level declarations")
    # The prelude is fixed; the remainder can contain only original lemma declarations.
    prelude_count = len(top_level_commands(candidate.prelude))
    if [item["name"] for item in top[prelude_count:]] != list(seed.by_name):
        errors.append("manual contains an extra top-level command")
    errors.extend(f"manual uses forbidden lemma/tactic `{name}`" for name in _forbidden_findings(candidate.text))
    return errors


def validate_group(context: ProvingContext, group_id: str, *, complete: bool = True) -> dict[str, Any]:
    """Use one ownership/safety check for development, exact delivery, and merge."""
    group = next((item for item in context.groups if item["id"] == group_id), None)
    if group is None:
        return {"errors": [f"unknown current group: {group_id}"], "recoverable": False, "group": None}
    errors: list[str] = []
    additions: list[dict[str, Any]] = []
    candidate = None
    report_bytes = None
    directory = Path(group["directory"])
    expected = {context.proof_manual.name}
    if context.library is not None:
        expected.add(context.formal_case_lib.name)
    try:
        fixed_path_under(directory, context.run_root, label="group directory")
        if {path.name for path in directory.iterdir()} != expected:
            errors.append("group directory must contain only its assigned formal files")
        for filename in ("group_worker_input.md", "group_worker_report.json"):
            path = fixed_path_under(Path(group["report_directory"]) / filename, context.report_directory, label="group delivery file")
            payload = _snapshot(path, context.main_root)
            if payload is None:
                return {"errors": [f"missing {filename}"], "recoverable": False, "group": group}
            if filename == "group_worker_report.json":
                report_bytes = payload
        payload = _snapshot(Path(group["proof_manual"]), context.main_root)
        if payload is None or context.manual is None:
            raise ValueError("current group manual is missing")
        candidate = parse_manual(payload.decode("utf-8"))
        errors.extend(_manual_errors(context.manual, candidate, group, complete))
        if context.library_model is not None:
            payload = _snapshot(Path(group["group_worker_lib"]), context.main_root)
            if payload is None:
                raise ValueError("current group library is missing")
            additions, library_errors = _library_additions(
                context.library_model, _parse_library(payload.decode("utf-8"), context.forbidden_modules), group)
            errors.extend(library_errors)
    except (OSError, UnicodeError, ValueError, SystemExit) as exc:
        errors.append(str(exc))
    return {"errors": [f"{group_id}: {error}" for error in errors], "recoverable": bool(errors),
            "group": group, "manual": candidate, "additions": additions, "report_bytes": report_bytes}


def merge_groups(context: ProvingContext) -> dict[str, Any]:
    """Validate every current delivery once, then concatenate accepted spans."""
    errors: list[str] = list(context.library_model.errors) if context.library_model else []
    group_errors: dict[str, list[str]] = {}
    replacements: dict[str, str] = {}
    additions: list[dict[str, Any]] = []
    helper_names: set[str] = set()
    imports: set[str] = set()
    for group in context.groups:
        result = validate_group(context, group["id"], complete=True)
        errors.extend(result["errors"])
        if result["errors"]:
            group_errors[group["id"]] = result["errors"]
            continue
        report_errors = []
        try:
            report = json.loads(result["report_bytes"].decode("utf-8"))
            if report != {"status": "completed"}:
                report_errors.append(f"{group['id']}: report must be exactly completed")
        except (OSError, UnicodeError, ValueError) as exc:
            report_errors.append(f"{group['id']}: invalid group report: {exc}")
        if report_errors:
            errors.extend(report_errors)
            group_errors[group["id"]] = report_errors
            continue
        for witness in group["witnesses"]:
            names = [witness["name"]]
            if witness["proof_mode"] == "aggressive_pre_process":
                names.extend(item["name"] for item in witness["split_goals"])
            for name in names:
                replacements[name] = result["manual"].by_name[name]["block"]
        for declaration in result["additions"]:
            name = declaration["name"]
            if declaration["kind"] == "Import":
                if name in imports:
                    continue
                imports.add(name)
            elif name in helper_names:
                message = f"conflicting helper declaration `{name}`; the owning group must rename it"
                errors.append(message)
                group_errors.setdefault(group["id"], []).append(message)
            else:
                helper_names.add(name)
            additions.append(declaration)
    candidate = {"proof_manual": None, "formal_case_lib": None}
    merged = {}
    if context.manual is not None:
        merged[context.proof_manual.name] = context.manual.prelude + "".join(
            replacements.get(item["name"], item["block"]) for item in context.manual.lemmas)
    if context.library is not None:
        # Imports precede helpers so every submitted helper retains its import environment.
        ordered = sorted(additions, key=lambda item: item["kind"] != "Import")
        merged[context.formal_case_lib.name] = context.library + (
            "\n\n" + "\n".join(item["block"].rstrip() for item in ordered) + "\n" if ordered else "")
    directory = fixed_path_under(context.directory / "proving_merged", context.run_root, label="proving_merged directory")
    if directory.exists():
        for path in directory.iterdir():
            if path.name not in merged or path_is_link_like(path) or not path.is_file():
                errors.append(f"unexpected proving_merged entry: {path}")
    if not errors:
        directory.mkdir(parents=True, exist_ok=True)
        for role, relative in (("proof_manual", context.proof_manual), ("formal_case_lib", context.formal_case_lib)):
            if relative.name in merged:
                path = directory / relative.name
                write_bytes(path, merged[relative.name].encode("utf-8"), label="mechanically merged source")
                candidate[role] = str(path)
    result = {"status": "failed" if errors else "passed", "candidate": candidate,
              "group_count": len(context.groups), "group_errors": group_errors,
              "added_declarations": [{key: item[key] for key in ("name", "kind", "group_id")} for item in additions]}
    if errors:
        result.update(errors=errors, error_count=len(errors), failure={"category": "merge", "kind": "proving-merged-failed", "message": errors[0]})
    return result
