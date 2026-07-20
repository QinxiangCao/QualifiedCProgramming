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
ADMITTED_RE = re.compile(r"\bAdmitted\s*\.")
ABORT_RE = re.compile(r"\bAbort\s*\.")
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
COMMAND_SIMPLE_MODIFIERS = {
    "Local",
    "Global",
    "Polymorphic",
    "Monomorphic",
    "Program",
    "Time",
    "Instructions",
    "Fail",
    "Succeed",
}
COMMAND_WORD_RE = re.compile(r"[A-Za-z][A-Za-z0-9_']*")
COMMAND_NATURAL_RE = re.compile(r"(?:0[xX][0-9A-Fa-f][0-9A-Fa-f_]*|[0-9][0-9_]*)\b")
BYPASS_CHECK_RE = re.compile(r"\bbypass_check\s*\(\s*(guard|positivity|universes)\s*\)", re.IGNORECASE)
UNSAFE_TYPING_RE = re.compile(r"^Unset\s+(Guard|Positivity|Universe)\s+Checking\s*\.", re.DOTALL)
ROLLBACK_CONTROL_KINDS = {"Fail", "Succeed"}
TOP_LEVEL_DECLARATION_KINDS = {
    "Lemma",
    "Theorem",
    "Proposition",
    "Corollary",
    "Example",
    "Fact",
    "Remark",
    "Definition",
    "Fixpoint",
    "CoFixpoint",
    "Inductive",
    "CoInductive",
    "Notation",
    "Axiom",
    "Axioms",
    "Parameter",
    "Parameters",
    "Conjecture",
    "Conjectures",
    "Hypothesis",
    "Hypotheses",
    "Variable",
    "Variables",
    "Record",
    "Structure",
    "Class",
    "Instance",
    "Module",
    "Section",
    "Context",
    "Let",
    "Ltac",
    "Ltac2",
    "Scheme",
    "Goal",
}
UNCONDITIONAL_ASSUMPTION_KINDS = {"Axiom", "Axioms", "Parameter", "Parameters", "Conjecture", "Conjectures"}
SECTION_CONTEXT_DECLARATION_KINDS = {"Hypothesis", "Hypotheses", "Variable", "Variables", "Context"}
ASSUMPTION_DECLARATION_KINDS = UNCONDITIONAL_ASSUMPTION_KINDS | SECTION_CONTEXT_DECLARATION_KINDS
PROOF_DECLARATION_KINDS = set(LEMMA_KEYWORDS.split("|"))
PROOF_TERMINATORS = {"Qed", "Defined", "Admitted", "Abort"}


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
            if depth == 0:
                result.append(" ")
            depth += 1
            index += 2
            continue
        if not in_string and pair == "*)" and depth > 0:
            depth -= 1
            index += 2
            continue
        if depth == 0:
            result.append(char)
        elif char == "\n":
            result.append("\n")
        index += 1
    return "".join(result)


def _coq_commands(text: str) -> list[tuple[str, int]]:
    """Split comment-free Rocq text at command-ending periods."""

    uncommented = strip_coq_comments(text)
    commands: list[tuple[str, int]] = []
    start = 0
    in_string = False
    index = 0
    while index < len(uncommented):
        char = uncommented[index]
        if char == '"':
            if in_string and index + 1 < len(uncommented) and uncommented[index + 1] == '"':
                index += 2
                continue
            in_string = not in_string
        if char == "." and not in_string and (index + 1 == len(uncommented) or uncommented[index + 1].isspace()):
            segment = uncommented[start : index + 1]
            if segment.strip():
                commands.append((segment, start))
            start = index + 1
        index += 1
    trailing = uncommented[start:]
    if trailing.strip():
        commands.append((trailing, start))
    return commands


def _skip_space(text: str, index: int) -> int:
    while index < len(text) and text[index].isspace():
        index += 1
    return index


def _skip_string(text: str, index: int) -> int | None:
    if index >= len(text) or text[index] != '"':
        return None
    index += 1
    while index < len(text):
        if text[index] == '"':
            if index + 1 < len(text) and text[index + 1] == '"':
                index += 2
                continue
            return index + 1
        index += 1
    return None


def _skip_attribute(text: str, index: int) -> int | None:
    if not text.startswith("#[", index):
        return None
    depth = 1
    index += 2
    while index < len(text):
        if text[index] == '"':
            string_end = _skip_string(text, index)
            if string_end is None:
                return None
            index = string_end
            continue
        if text[index] == "[":
            depth += 1
        elif text[index] == "]":
            depth -= 1
            if depth == 0:
                return index + 1
        index += 1
    return None


def _command_prefix(command: str) -> tuple[str, int, int, list[str], list[str]] | None:
    """Parse attributes and command wrappers, returning the persistent inner head."""

    index = _skip_space(command, 0)
    modifiers: list[str] = []
    attributes: list[str] = []
    while True:
        while True:
            attribute_start = index
            attribute_end = _skip_attribute(command, index)
            if attribute_end is None:
                break
            attributes.append(command[attribute_start:attribute_end])
            index = _skip_space(command, attribute_end)

        word_match = COMMAND_WORD_RE.match(command, index)
        if word_match is None:
            return None
        word = word_match.group(0)
        if word in COMMAND_SIMPLE_MODIFIERS:
            modifiers.append(word)
            index = _skip_space(command, word_match.end())
            continue
        if word == "Timeout":
            natural_start = _skip_space(command, word_match.end())
            natural_match = COMMAND_NATURAL_RE.match(command, natural_start)
            if natural_match is not None:
                modifiers.append(word)
                index = _skip_space(command, natural_match.end())
                continue
        if word == "Redirect":
            string_start = _skip_space(command, word_match.end())
            string_end = _skip_string(command, string_start)
            if string_end is not None:
                modifiers.append(word)
                index = _skip_space(command, string_end)
                continue
        return word, word_match.start(), word_match.end(), modifiers, attributes


def top_level_commands(text: str) -> list[dict[str, Any]]:
    """Return command heads outside proofs."""

    uncommented = strip_coq_comments(text)
    commands: list[dict[str, Any]] = []
    in_proof = False
    for command, offset in _coq_commands(text):
        prefix = _command_prefix(command)
        if prefix is None:
            continue
        inner_head, head_start, head_end, modifiers, attributes = prefix
        control = next((item for item in modifiers if item in ROLLBACK_CONTROL_KINDS), None)
        head = control or inner_head
        if in_proof:
            if head in PROOF_TERMINATORS:
                in_proof = False
            continue
        name_match = re.match(r"\s+([A-Za-z0-9_']+)", command[head_end:])
        name = name_match.group(1) if name_match else hashlib.sha256(command.strip().encode("utf-8")).hexdigest()[:16]
        command_hash = hashlib.sha256(normalize_coq_text(command).encode("utf-8")).hexdigest()
        bypass_checks = sorted({match.group(1).lower() for attribute in attributes for match in BYPASS_CHECK_RE.finditer(attribute)})
        unsafe_typing_match = UNSAFE_TYPING_RE.match(command[head_start:])
        commands.append(
            {
                "kind": head,
                "name": name,
                "command_hash": command_hash,
                "line": uncommented.count("\n", 0, offset + head_start) + 1,
                **({"wrapped_kind": inner_head} if control else {}),
                **({"bypass_checks": bypass_checks} if bypass_checks else {}),
                **(
                    {"unsafe_typing_control": unsafe_typing_match.group(1).lower()}
                    if unsafe_typing_match is not None
                    else {}
                ),
            }
        )
        if control:
            continue
        if head in PROOF_DECLARATION_KINDS or (head == "Definition" and ":=" not in command):
            in_proof = True
    return commands


def top_level_declarations(text: str) -> list[dict[str, Any]]:
    """Return declaration command heads without confusing proof commands for top level."""

    return [item for item in top_level_commands(text) if str(item["kind"]) in TOP_LEVEL_DECLARATION_KINDS]


def forbidden_top_level_declarations(text: str, kinds: set[str]) -> list[dict[str, Any]]:
    return [item for item in top_level_declarations(text) if str(item["kind"]) in kinds]


def rollback_control_commands(text: str) -> list[dict[str, Any]]:
    return [item for item in top_level_commands(text) if str(item["kind"]) in ROLLBACK_CONTROL_KINDS]


def unsafe_typing_commands(text: str) -> list[dict[str, Any]]:
    return [
        item
        for item in top_level_commands(text)
        if item.get("unsafe_typing_control") or item.get("bypass_checks")
    ]


def unsafe_assumption_declarations(text: str) -> list[dict[str, Any]]:
    """Find axioms and section-context commands that occur outside a Section."""

    active_sections: list[str] = []
    findings: list[dict[str, Any]] = []
    for command in top_level_commands(text):
        kind = str(command["kind"])
        name = str(command["name"])
        if kind == "Section":
            active_sections.append(name)
        elif kind == "End" and active_sections and name == active_sections[-1]:
            active_sections.pop()
        elif kind in UNCONDITIONAL_ASSUMPTION_KINDS or (
            kind in SECTION_CONTEXT_DECLARATION_KINDS and not active_sections
        ):
            findings.append(command)
    return findings


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
    return ABORT_RE.search(strip_coq_comments(block)) is not None


def is_diagnostic_lemma(block_or_lemma: str | dict[str, Any]) -> bool:
    block = str(block_or_lemma.get("block", "")) if isinstance(block_or_lemma, dict) else str(block_or_lemma)
    return SPLIT_GOAL_RE.search(strip_coq_comments(block)) is not None or lemma_has_abort(block)


def manual_diagnostic_errors(text: str) -> list[str]:
    uncommented = strip_coq_comments(text)
    errors: list[str] = []
    if SPLIT_GOAL_RE.search(uncommented):
        errors.append("proof manual contains diagnostic _split_goal_ lemma or target")
    if ABORT_RE.search(uncommented):
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
    manual_obligation_count = 0
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
            manual_obligation_count += 1
    manual_text = prelude + "".join(manual_blocks)
    diagnostics_text = prelude + "".join(diagnostic_blocks)
    snapshot = {
        "schema_version": "qcp-diagnostics-snapshot/v2",
        "diagnostics": diagnostics,
        "manual_obligation_count": manual_obligation_count,
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
    return bool(incomplete_proof_markers(block))


def incomplete_proof_markers(text: str) -> list[dict[str, Any]]:
    """Find incomplete proof terminators after removing nested Coq comments."""

    uncommented = strip_coq_comments(text)
    findings: list[dict[str, Any]] = []
    for pattern, kind in ((ADMITTED_RE, "Admitted"), (ABORT_RE, "Abort")):
        for match in pattern.finditer(uncommented):
            findings.append({"kind": kind, "line": uncommented.count("\n", 0, match.start()) + 1})
    return findings


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


def lib_contract_errors(text: str) -> list[str]:
    errors: list[str] = []
    uncommented = strip_coq_comments(text)
    for marker in incomplete_proof_markers(text):
        errors.append(f"lib contains {marker['kind']}.")
    for command in rollback_control_commands(text):
        errors.append(f"lib contains forbidden rollback control command {command['kind']}.")
    for command in unsafe_typing_commands(text):
        detail = command.get("unsafe_typing_control") or ",".join(command.get("bypass_checks", []))
        errors.append(f"lib contains unsafe typing control {detail}.")
    for declaration in unsafe_assumption_declarations(text):
        errors.append(f"lib contains assumption declaration {declaration['kind']}.")
    for line in uncommented.splitlines():
        stripped = line.strip()
        if FORBIDDEN_CASE_IMPORT_RE.match(stripped):
            errors.append(f"lib imports generated case artifact: {stripped}")
    return errors


def parse_lib_declarations(text: str) -> list[dict[str, str]]:
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


def is_official_library_import(line: str) -> bool:
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


def merge_group_worker_libs(
    seed_text: str,
    group_texts: list[tuple[str, str, dict[str, Any]]],
) -> tuple[str, list[dict[str, str]], list[str]]:
    """Merge group_worker_lib helper declarations onto formal_case_lib seed.

    Returns ``(merged_text, added_declarations, errors)``.
    """
    errors = lib_contract_errors(seed_text)
    seed_declarations = parse_lib_declarations(seed_text)
    seed_decls = {f"{d['kind']}:{d['name']}": d for d in seed_declarations}
    seed_names = {d["name"] for d in seed_declarations if d["kind"] != "Import"}
    seed_commands = top_level_commands(seed_text)
    seed_command_keys = [
        (str(item["kind"]), str(item["name"]), str(item["command_hash"])) for item in seed_commands
    ]
    helper_additions_by_name: dict[str, dict[str, str]] = {}
    import_additions_by_name: dict[str, dict[str, str]] = {}
    import_additions: list[dict[str, str]] = []
    helper_additions: list[dict[str, str]] = []

    for group_id, text, namespace in group_texts:
        suffix = str(namespace.get("suffix", ""))
        errors.extend(_helper_namespace_errors(group_id, namespace))
        errors.extend(f"{group_id}: {error}" for error in lib_contract_errors(text))
        group_decls = parse_lib_declarations(text)
        group_commands = top_level_commands(text)
        group_command_keys = [
            (str(item["kind"]), str(item["name"]), str(item["command_hash"])) for item in group_commands
        ]

        seed_position = 0
        for command_key in group_command_keys:
            if seed_position < len(seed_command_keys) and command_key == seed_command_keys[seed_position]:
                seed_position += 1
        if seed_position != len(seed_command_keys):
            errors.append(f"{group_id}: group_worker_lib removed, changed, or reordered seed top-level commands")

        remaining_seed = list(seed_command_keys)
        added_commands: list[dict[str, Any]] = []
        for command, command_key in zip(group_commands, group_command_keys):
            try:
                remaining_seed.remove(command_key)
            except ValueError:
                added_commands.append(command)
        if remaining_seed:
            errors.append(f"{group_id}: group_worker_lib removed or changed seed top-level commands")

        parsed_helper_commands: set[tuple[str, str, str]] = set()
        parsed_import_commands: set[tuple[str, str, str]] = set()
        for declaration in group_decls:
            commands = top_level_commands(str(declaration["block"]))
            if not commands:
                continue
            first = commands[0]
            key = (str(first["kind"]), str(first["name"]), str(first["command_hash"]))
            if declaration["kind"] == "Import":
                parsed_import_commands.add(key)
            elif declaration["kind"] in HELPER_DECL_KINDS and declaration["name"] == first["name"]:
                parsed_helper_commands.add(key)

        for command in added_commands:
            kind = str(command["kind"])
            name = str(command["name"])
            key = (kind, name, str(command["command_hash"]))
            if kind in {"Require", "From"}:
                if key not in parsed_import_commands:
                    errors.append(f"{group_id}: new import command is not a standalone parseable block")
            elif kind in HELPER_DECL_KINDS:
                if key not in parsed_helper_commands:
                    errors.append(f"{group_id}: new helper declaration `{name}` is not a standalone parseable block")
                elif name in seed_names:
                    errors.append(f"{group_id}: new helper declaration `{name}` duplicates formal_case_lib seed name")
            else:
                errors.append(f"{group_id}: new top-level command `{name}` has forbidden kind `{kind}`")
        group_by_key = {f"{d['kind']}:{d['name']}": d for d in group_decls}
        for key, seed in seed_decls.items():
            group_seed = group_by_key.get(key)
            if group_seed is None:
                errors.append(f"{group_id}: removed formal_case_lib seed declaration `{seed['name']}`")
            elif normalize_coq_text(seed["block"]) != normalize_coq_text(group_seed["block"]):
                errors.append(f"{group_id}: modified formal_case_lib seed declaration `{seed['name']}`")
        for decl in group_decls:
            key = f"{decl['kind']}:{decl['name']}"
            if key in seed_decls:
                continue
            if decl["kind"] == "Import":
                if not is_official_library_import(decl["name"]):
                    errors.append(f"{group_id}: new group_worker_lib import `{decl['name']}` is not an allowed official Rocq import")
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
                errors.append(f"{group_id}: new group_worker_lib declaration `{decl['name']}` has forbidden kind `{decl['kind']}`")
                continue
            if decl["name"] in seed_names:
                errors.append(f"{group_id}: new group_worker_lib declaration `{decl['name']}` duplicates formal_case_lib seed name")
                continue
            if not suffix or not decl["name"].endswith(suffix):
                errors.append(f"{group_id}: new helper declaration `{decl['name']}` must end with current suffix `{suffix}`")
                continue
            foreign_suffix = HELPER_NAMESPACE_SUFFIX_RE.search(decl["name"])
            if foreign_suffix and foreign_suffix.group(0) != suffix:
                errors.append(f"{group_id}: new helper declaration `{decl['name']}` uses foreign helper suffix `{foreign_suffix.group(0)}`")
                continue
            if decl["name"] in helper_additions_by_name:
                errors.append(f"{group_id}: duplicate new group_worker_lib declaration name `{decl['name']}`")
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
