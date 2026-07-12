#!/usr/bin/env python3
"""Small Coq/manual utilities for vc-proving preparation and group workers."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any


LEMMA_KEYWORDS = "Lemma|Theorem|Proposition|Corollary|Example|Fact|Remark"
LEMMA_RE = re.compile(rf"^(?:{LEMMA_KEYWORDS})\s+([A-Za-z0-9_']+)\s*:", re.MULTILINE)
PROOF_START_RE = re.compile(r"\bProof(?:\s+using\s+[^.]+)?\.", re.MULTILINE)
PROOF_ABORT_RE = re.compile(r"\bProof(?:\s+using\s+[^.]+)?\.\s*Abort\.", re.MULTILINE)
SPLIT_GOAL_RE = re.compile(r"\b[A-Za-z0-9_']*_split_goal_[A-Za-z0-9_']*\b")
SIMPLE_TARGET_RE = re.compile(
    rf"^\s*(?:{LEMMA_KEYWORDS})\s+([A-Za-z0-9_']+)\s*:\s*([A-Za-z0-9_']+)\s*\.\s*$",
    re.DOTALL,
)
CASE_LIB_DECL_RE = re.compile(
    r"^\s*(?:(Require\s+Import\b|From\s+[A-Za-z0-9_.]+\s+Require\s+Import\b)|"
    r"(Lemma|Theorem|Fact|Remark|Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Notation|Axiom)\s+([A-Za-z0-9_']+)\b)",
    re.MULTILINE,
)
HELPER_DECL_KINDS = {"Lemma", "Theorem", "Fact", "Remark"}
FORBIDDEN_CASE_IMPORT_RE = re.compile(r"^\s*From\s+SimpleC\.EE\.[A-Za-z0-9_.]+\s+Require\s+Import\s+.*(?:_goal|_proof_auto|_proof_manual|_goal_check)\b")
HELPER_NAMESPACE_SUFFIX_RE = re.compile(r"__[A-Za-z0-9_]+$")
REQUIRE_IMPORT_RE = re.compile(r"^Require\s+Import\s+(.+)\.$")
FROM_REQUIRE_IMPORT_RE = re.compile(r"^From\s+([A-Za-z0-9_.]+)\s+Require\s+Import\s+(.+)\.$")


def strip_coq_comments(text: str) -> str:
    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if depth == 0 and char == '"':
            result.append(char)
            in_string = not in_string
            index += 1
            continue
        if not in_string and pair == "(*":
            depth += 1
            index += 2
            continue
        if not in_string and pair == "*)" and depth > 0:
            depth -= 1
            index += 2
            continue
        if depth == 0:
            result.append(char)
        index += 1
    return "".join(result)


def normalize_coq_text(text: str) -> str:
    text = strip_coq_comments(text).replace("\r\n", "\n").replace("\r", "\n")
    lines = [line.rstrip() for line in text.split("\n")]
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    return "\n".join(lines) + "\n"


def stable_text_digest(text: str) -> str:
    return hashlib.sha256(normalize_coq_text(text).encode("utf-8")).hexdigest()


def diagnostics_file_for_manual(manual_path: str | Path) -> Path:
    path = Path(manual_path)
    if path.name.endswith("_proof_manual.v"):
        return path.with_name(path.name[: -len("_proof_manual.v")] + "_proof_diagnostics.v")
    return path.with_name(path.stem + "_diagnostics.v")


def diagnostics_snapshot_for_manual(manual_path: str | Path) -> Path:
    return Path(manual_path).with_name("diagnostics_snapshot.json")


def lemma_has_abort(block_or_lemma: str | dict[str, Any]) -> bool:
    block = str(block_or_lemma.get("block", "")) if isinstance(block_or_lemma, dict) else str(block_or_lemma)
    return PROOF_ABORT_RE.search(strip_coq_comments(block)) is not None


def is_diagnostic_lemma(block_or_lemma: str | dict[str, Any]) -> bool:
    block = str(block_or_lemma.get("block", "")) if isinstance(block_or_lemma, dict) else str(block_or_lemma)
    return SPLIT_GOAL_RE.search(strip_coq_comments(block)) is not None or lemma_has_abort(block)


def manual_diagnostic_errors(text: str) -> list[str]:
    uncommented = strip_coq_comments(text)
    errors: list[str] = []
    if SPLIT_GOAL_RE.search(uncommented):
        errors.append("proof manual contains diagnostic _split_goal_ lemma or target")
    if PROOF_ABORT_RE.search(uncommented):
        errors.append("proof manual contains Proof. Abort. diagnostic block")
    return errors


def _parse_manual_file_unchecked(text: str) -> tuple[str, list[dict[str, Any]]]:
    lines = text.splitlines(keepends=True)
    offsets: list[int] = []
    offset = 0
    for line in lines:
        offsets.append(offset)
        offset += len(line)

    starts: list[tuple[int, str]] = []
    for idx, line in enumerate(lines):
        match = LEMMA_RE.match(line)
        if match:
            starts.append((idx, match.group(1)))
    if not starts:
        raise ValueError("No lemma blocks found in proof manual.")

    prelude = "".join(lines[: starts[0][0]])
    lemmas: list[dict[str, Any]] = []
    for pos, (start_idx, name) in enumerate(starts):
        end_idx = starts[pos + 1][0] if pos + 1 < len(starts) else len(lines)
        start_offset = offsets[start_idx]
        end_offset = offsets[end_idx] if end_idx < len(lines) else len(text)
        block = text[start_offset:end_offset]
        lemmas.append(
            {
                "name": name,
                "block": block,
                "header_line": lines[start_idx].rstrip("\n"),
                "start_line": start_idx + 1,
                "end_line": end_idx,
                "start_offset": start_offset,
                "end_offset": end_offset,
            }
        )
    return prelude, lemmas


def parse_manual_file(text: str, *, allow_diagnostics: bool = False) -> tuple[str, list[dict[str, Any]]]:
    if not allow_diagnostics:
        errors = manual_diagnostic_errors(text)
        if errors:
            raise ValueError("; ".join(errors))
    return _parse_manual_file_unchecked(text)


def split_manual_diagnostics(text: str) -> dict[str, Any]:
    """Physically split diagnostic split-goal blocks out of a manual proof file."""
    prelude, lemmas = _parse_manual_file_unchecked(text)
    manual_blocks: list[str] = []
    diagnostic_blocks: list[str] = []
    diagnostics: list[dict[str, Any]] = []
    obligations: list[dict[str, Any]] = []
    for lemma in lemmas:
        block = str(lemma["block"])
        entry = {
            "name": str(lemma["name"]),
            "statement_hash": lemma_statement_hash(lemma),
            "target_symbol": lemma_target_symbol(lemma),
            "start_line": int(lemma["start_line"]),
            "end_line": int(lemma["end_line"]),
        }
        if is_diagnostic_lemma(lemma):
            diagnostic_blocks.append(block if block.endswith("\n") else block + "\n")
            diagnostics.append(
                {
                    **entry,
                    "has_abort": lemma_has_abort(lemma),
                    "has_split_goal": SPLIT_GOAL_RE.search(strip_coq_comments(block)) is not None,
                }
            )
        else:
            manual_blocks.append(block if block.endswith("\n") else block + "\n")
            obligations.append(entry)
    manual_text = prelude + "".join(manual_blocks)
    diagnostics_text = prelude + "".join(diagnostic_blocks)
    snapshot = {
        "schema_version": "qcp-diagnostics-snapshot/v1",
        "manual_obligations": obligations,
        "diagnostics": diagnostics,
        "manual_obligation_count": len(obligations),
        "diagnostic_count": len(diagnostics),
    }
    return {
        "proof_manual_text": manual_text,
        "proof_diagnostics_text": diagnostics_text,
        "diagnostics_snapshot": snapshot,
    }


def write_split_manual_artifacts(
    manual_path: Path,
    *,
    diagnostics_path: Path | None = None,
    snapshot_path: Path | None = None,
) -> dict[str, Any]:
    manual_path = manual_path.expanduser().resolve()
    diagnostics_path = (diagnostics_path or diagnostics_file_for_manual(manual_path)).expanduser().resolve()
    snapshot_path = (snapshot_path or diagnostics_snapshot_for_manual(manual_path)).expanduser().resolve()
    split = split_manual_diagnostics(manual_path.read_text(encoding="utf-8"))
    manual_path.write_text(str(split["proof_manual_text"]), encoding="utf-8")
    diagnostics_path.write_text(str(split["proof_diagnostics_text"]), encoding="utf-8")
    write_payload = split["diagnostics_snapshot"]
    snapshot_path.write_text(
        json.dumps(write_payload, indent=2, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )
    return {
        "proof_manual_file": str(manual_path),
        "proof_diagnostics_file": str(diagnostics_path),
        "diagnostics_snapshot": str(snapshot_path),
        **write_payload,
    }


def ensure_unique_lemma_names(lemmas: list[dict[str, Any]]) -> None:
    seen: set[str] = set()
    duplicates: list[str] = []
    for lemma in lemmas:
        name = str(lemma["name"])
        if name in seen:
            duplicates.append(name)
        seen.add(name)
    if duplicates:
        raise ValueError("duplicate lemma names: " + ", ".join(sorted(set(duplicates))))


def lemma_by_name(lemmas: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    return {str(lemma["name"]): lemma for lemma in lemmas}


def block_has_admitted(block: str) -> bool:
    return "Admitted." in strip_coq_comments(block)


def lemma_statement_text(block_or_lemma: str | dict[str, Any]) -> str:
    block = str(block_or_lemma.get("block", "")) if isinstance(block_or_lemma, dict) else str(block_or_lemma)
    match = PROOF_START_RE.search(block)
    statement = block[: match.start()] if match else block
    return statement.rstrip() + "\n"


def lemma_statement_hash(block_or_lemma: str | dict[str, Any]) -> str:
    statement = normalize_coq_text(lemma_statement_text(block_or_lemma))
    canonical = re.sub(
        rf"^(\s*(?:{LEMMA_KEYWORDS})\s+)[A-Za-z0-9_']+(\s*:)",
        r"\1__LEMMA_NAME__\2",
        statement,
        count=1,
        flags=re.DOTALL,
    )
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def lemma_target_symbol(block_or_lemma: str | dict[str, Any]) -> str | None:
    statement = normalize_coq_text(lemma_statement_text(block_or_lemma))
    match = SIMPLE_TARGET_RE.match(statement)
    return match.group(2) if match else None


def case_lib_contract_errors(text: str) -> list[str]:
    errors: list[str] = []
    uncommented = strip_coq_comments(text)
    if "Admitted." in uncommented:
        errors.append("case_lib contains Admitted.")
    for line in uncommented.splitlines():
        stripped = line.strip()
        if stripped.startswith("Axiom "):
            errors.append(f"case_lib contains extra Axiom: {stripped}")
        if FORBIDDEN_CASE_IMPORT_RE.match(stripped):
            errors.append(f"case_lib imports generated case artifact: {stripped}")
    return errors


def parse_case_lib_declarations(text: str) -> list[dict[str, str]]:
    starts: list[tuple[int, re.Match[str]]] = [(m.start(), m) for m in CASE_LIB_DECL_RE.finditer(text)]
    declarations: list[dict[str, str]] = []
    for idx, (start, match) in enumerate(starts):
        end = starts[idx + 1][0] if idx + 1 < len(starts) else len(text)
        block = text[start:end].strip() + "\n"
        import_head = match.group(1)
        kind = "Import" if import_head else str(match.group(2))
        name = normalize_import_line(block.splitlines()[0]) if import_head else str(match.group(3))
        declarations.append({"kind": kind, "name": name, "block": block})
    return declarations


def normalize_import_line(line: str) -> str:
    return " ".join(line.strip().rstrip(".").split()) + "."


def is_official_rocq_import(line: str) -> bool:
    normalized = normalize_import_line(line)
    require_match = REQUIRE_IMPORT_RE.match(normalized)
    if require_match:
        modules = require_match.group(1).split()
        return bool(modules) and all(module == "Coq" or module.startswith("Coq.") for module in modules)

    from_match = FROM_REQUIRE_IMPORT_RE.match(normalized)
    if from_match:
        prefix = from_match.group(1)
        modules = from_match.group(2).split()
        return bool(modules) and (prefix == "Coq" or prefix.startswith("Coq."))

    return False


def helper_namespace_for_group_id(group_id: object) -> dict[str, str]:
    """Return the strict helper namespace block for a proof group."""
    sanitized = re.sub(r"[^A-Za-z0-9_]+", "_", str(group_id).strip())
    if not sanitized:
        raise ValueError(f"group_id does not produce a valid helper namespace suffix: {group_id!r}")
    return {
        "policy": "group-id-suffixed",
        "group_id": str(group_id),
        "suffix": "__" + sanitized,
        "required": "yes",
    }


def _helper_namespace_errors(group_id: str, namespace: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    try:
        expected = helper_namespace_for_group_id(group_id)
    except ValueError as exc:
        return [str(exc)]
    for key, value in expected.items():
        if namespace.get(key) != value:
            errors.append(f"{group_id}: helper_namespace.{key} must be {value!r}")
    return errors


def _declaration_statement_hash(decl: dict[str, str]) -> str:
    if decl.get("kind") in HELPER_DECL_KINDS:
        return lemma_statement_hash(decl["block"])
    return stable_text_digest(decl["block"])


def merge_case_lib(
    seed_text: str,
    group_texts: list[tuple[str, str, dict[str, Any]]],
) -> tuple[str, list[dict[str, str]], list[str]]:
    """Merge new group helper declarations into seed case_lib.

    Returns ``(merged_text, added_declarations, errors)``.
    """
    errors = case_lib_contract_errors(seed_text)
    seed_declarations = parse_case_lib_declarations(seed_text)
    seed_decls = {f"{d['kind']}:{d['name']}": d for d in seed_declarations}
    seed_names = {d["name"] for d in seed_declarations if d["kind"] != "Import"}
    helper_additions_by_name: dict[str, dict[str, str]] = {}
    import_additions_by_name: dict[str, dict[str, str]] = {}
    import_additions: list[dict[str, str]] = []
    helper_additions: list[dict[str, str]] = []

    for group_id, text, namespace in group_texts:
        suffix = str(namespace.get("suffix", ""))
        errors.extend(_helper_namespace_errors(group_id, namespace))
        errors.extend(f"{group_id}: {error}" for error in case_lib_contract_errors(text))
        group_decls = parse_case_lib_declarations(text)
        group_by_key = {f"{d['kind']}:{d['name']}": d for d in group_decls}
        for key, seed in seed_decls.items():
            group_seed = group_by_key.get(key)
            if group_seed is None:
                errors.append(f"{group_id}: removed seed case_lib declaration `{seed['name']}`")
            elif normalize_coq_text(seed["block"]) != normalize_coq_text(group_seed["block"]):
                errors.append(f"{group_id}: modified seed case_lib declaration `{seed['name']}`")
        for decl in group_decls:
            key = f"{decl['kind']}:{decl['name']}"
            if key in seed_decls:
                continue
            if decl["kind"] == "Import":
                if not is_official_rocq_import(decl["name"]):
                    errors.append(f"{group_id}: new case_lib import `{decl['name']}` is not an allowed official Rocq import")
                    continue
                if decl["name"] not in import_additions_by_name:
                    added = {
                        **decl,
                        "group_id": group_id,
                        "statement_hash": _declaration_statement_hash(decl),
                        "helper_namespace_suffix": "",
                    }
                    import_additions_by_name[decl["name"]] = added
                    import_additions.append(added)
                continue
            if decl["kind"] not in HELPER_DECL_KINDS:
                errors.append(f"{group_id}: new case_lib declaration `{decl['name']}` has forbidden kind `{decl['kind']}`")
                continue
            if decl["name"] in seed_names:
                errors.append(f"{group_id}: new case_lib declaration `{decl['name']}` duplicates seed declaration name")
                continue
            if not suffix or not decl["name"].endswith(suffix):
                errors.append(f"{group_id}: new helper declaration `{decl['name']}` must end with current suffix `{suffix}`")
                continue
            foreign_suffix = HELPER_NAMESPACE_SUFFIX_RE.search(decl["name"])
            if foreign_suffix and foreign_suffix.group(0) != suffix:
                errors.append(f"{group_id}: new helper declaration `{decl['name']}` uses foreign helper suffix `{foreign_suffix.group(0)}`")
                continue
            if decl["name"] in helper_additions_by_name:
                errors.append(f"{group_id}: duplicate new case_lib declaration name `{decl['name']}`")
                continue
            added = {
                **decl,
                "group_id": group_id,
                "statement_hash": _declaration_statement_hash(decl),
                "helper_namespace_suffix": suffix,
            }
            helper_additions_by_name[decl["name"]] = added
            helper_additions.append(added)

    additions = import_additions + helper_additions
    if errors:
        return seed_text, additions, errors
    added_text = "\n".join(decl["block"].rstrip() for decl in additions)
    if not added_text:
        return seed_text, [], []
    merged = seed_text.rstrip() + "\n\n" + added_text + "\n"
    return merged, additions, []
