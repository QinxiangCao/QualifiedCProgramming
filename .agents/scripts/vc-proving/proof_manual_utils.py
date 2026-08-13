#!/usr/bin/env python3
"""Small Coq/manual utilities for vc-proving preparation and group workers."""

from __future__ import annotations

import json
import re
from collections.abc import Collection, Iterable, Mapping
from pathlib import Path
from typing import Any

from coq_tooling import _dependency_modules
from file_integrity import sha256_text

LEMMA_KEYWORDS = "Lemma|Theorem|Proposition|Corollary|Example|Fact|Remark"
LEMMA_RE = re.compile(rf"^(?:{LEMMA_KEYWORDS})\s+([A-Za-z0-9_']+)\s*:", re.MULTILINE)
PROOF_START_RE = re.compile(r"\bProof(?:\s+using\s+[^.]+)?\.", re.MULTILINE)
PROOF_TERMINATOR_RE = re.compile(r"\b(?:Qed|Defined|Admitted|Abort)\s*\.", re.MULTILINE)
PROOF_TERMINATOR_COMMAND_RE = re.compile(
    r"\b(?P<kind>Qed|Defined|Admitted|Abort)\s*\.\s*\Z"
)
ADMITTED_RE = re.compile(r"\bAdmitted\s*\.")
ABORT_RE = re.compile(r"\bAbort\s*\.")
SPLIT_GOAL_NAME_RE = re.compile(
    r"^(?P<witness>[A-Za-z0-9_']+)_split_goal_(?P<label>[A-Za-z0-9_']+)$"
)
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
GENERATED_ARTIFACT_ROLES = (
    "goal_file",
    "proof_auto_file",
    "proof_manual_file",
    "goal_check_file",
)
HELPER_NAMESPACE_SUFFIX_RE = re.compile(r"__[A-Za-z0-9_]+$")
REQUIRE_IMPORT_RE = re.compile(r"^Require\s+Import\s+(.+)\.$")
FROM_REQUIRE_IMPORT_RE = re.compile(
    r"^From\s+([A-Za-z0-9_.]+)\s+Require\s+Import\s+(.+)\.$"
)
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
COQ_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
COMMAND_NATURAL_RE = re.compile(r"(?:0[xX][0-9A-Fa-f][0-9A-Fa-f_]*|[0-9][0-9_]*)\b")
BYPASS_CHECK_RE = re.compile(
    r"\bbypass_check\s*\(\s*(guard|positivity|universes)\s*\)", re.IGNORECASE
)
UNSAFE_TYPING_RE = re.compile(
    r"^Unset\s+(Guard|Positivity|Universe)\s+Checking\s*\.", re.DOTALL
)
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
UNCONDITIONAL_ASSUMPTION_KINDS = {
    "Axiom",
    "Axioms",
    "Parameter",
    "Parameters",
    "Conjecture",
    "Conjectures",
}
SECTION_CONTEXT_DECLARATION_KINDS = {
    "Hypothesis",
    "Hypotheses",
    "Variable",
    "Variables",
    "Context",
}
ASSUMPTION_DECLARATION_KINDS = (
    UNCONDITIONAL_ASSUMPTION_KINDS | SECTION_CONTEXT_DECLARATION_KINDS
)
PROOF_DECLARATION_KINDS = set(LEMMA_KEYWORDS.split("|"))


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


def mask_coq_comments(text: str) -> str:
    """Replace comments with spaces while preserving every source offset.

    Exact group write-boundary checks need to locate proof delimiters in the
    original byte layout.  ``strip_coq_comments`` intentionally produces a
    smaller string, so it is unsuitable for slicing the source text.
    """

    result = list(text)
    index = 0
    depth = 0
    in_string = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if depth == 0 and char == '"':
            in_string = not in_string
            index += 1
            continue
        if not in_string and pair == "(*":
            result[index] = " "
            result[index + 1] = " "
            depth += 1
            index += 2
            continue
        if not in_string and pair == "*)" and depth > 0:
            result[index] = " "
            result[index + 1] = " "
            depth -= 1
            index += 2
            continue
        if depth > 0 and char != "\n":
            result[index] = " "
        index += 1
    return "".join(result)


def mask_coq_strings(text: str) -> str:
    """Replace string literals with spaces while preserving source offsets."""

    result = list(text)
    index = 0
    in_string = False
    while index < len(text):
        if not in_string:
            if text[index] == '"':
                result[index] = " "
                in_string = True
            index += 1
            continue
        if text[index] == '"':
            result[index] = " "
            if index + 1 < len(text) and text[index + 1] == '"':
                result[index + 1] = " "
                index += 2
                continue
            in_string = False
            index += 1
            continue
        if text[index] != "\n":
            result[index] = " "
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
            if (
                in_string
                and index + 1 < len(uncommented)
                and uncommented[index + 1] == '"'
            ):
                index += 2
                continue
            in_string = not in_string
        if (
            char == "."
            and not in_string
            and (index + 1 == len(uncommented) or uncommented[index + 1].isspace())
        ):
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
        if in_proof:
            # A tactic block can leave proof punctuation (for example a closing
            # ``}``) in the same command segment as ``Qed.``.  Such a segment
            # has no ordinary command prefix, but the trailing reserved proof
            # terminator still closes the proof.  Match only at the end of the
            # complete comment-free command so proof text cannot be promoted to
            # a top-level declaration.
            if PROOF_TERMINATOR_COMMAND_RE.search(command) is not None:
                in_proof = False
            continue
        prefix = _command_prefix(command)
        if prefix is None:
            continue
        inner_head, head_start, head_end, modifiers, attributes = prefix
        control = next(
            (item for item in modifiers if item in ROLLBACK_CONTROL_KINDS), None
        )
        head = control or inner_head
        name_match = re.match(r"\s+([A-Za-z0-9_']+)", command[head_end:])
        name = (
            name_match.group(1)
            if name_match
            else sha256_text(command.strip())[:16]
        )
        command_hash = coq_token_digest(command)
        if name_match is not None:
            name_start = head_end + name_match.start(1)
            name_end = head_end + name_match.end(1)
            semantic_command = (
                command[:name_start] + "__DECL_NAME__" + command[name_end:]
            )
        else:
            semantic_command = command
        semantic_command_hash = sha256_text(normalize_coq_text(semantic_command))
        bypass_checks = sorted(
            {
                match.group(1).lower()
                for attribute in attributes
                for match in BYPASS_CHECK_RE.finditer(attribute)
            }
        )
        unsafe_typing_match = UNSAFE_TYPING_RE.match(command[head_start:])
        commands.append(
            {
                "kind": head,
                "name": name,
                "command_hash": command_hash,
                "semantic_command_hash": semantic_command_hash,
                "semantic_command": normalize_coq_text(semantic_command),
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
        if head in PROOF_DECLARATION_KINDS or (
            head == "Definition" and ":=" not in command
        ):
            in_proof = True
    return commands


def top_level_declarations(text: str) -> list[dict[str, Any]]:
    """Return declaration command heads without confusing proof commands for top level."""

    return [
        item
        for item in top_level_commands(text)
        if str(item["kind"]) in TOP_LEVEL_DECLARATION_KINDS
    ]


def goal_definition_hashes(
    text: str, *, formal_case_lib_text: str = ""
) -> dict[str, str]:
    """Fingerprint generated goals with their local-definition dependency closure.

    A target fingerprint intentionally ignores its own declared name, but binds
    the non-definition module environment, the current formal-case lib, and all
    locally referenced generated definitions.  If a target cannot be resolved,
    callers can use ``__whole_goal_file__`` as a conservative fallback.
    """

    commands = top_level_commands(text)
    definitions: dict[str, str] = {}
    environment_commands: list[str] = []
    for command in commands:
        kind = str(command["kind"])
        name = str(command["name"])
        semantic_command = str(command["semantic_command"])
        if kind != "Definition":
            environment_commands.append(semantic_command)
            continue
        if name in definitions:
            raise ValueError(f"duplicate generated goal definition: {name}")
        definitions[name] = semantic_command

    environment_hash = sha256_text(
        (
            "".join(environment_commands)
            + "\n--FORMAL-CASE-LIB--\n"
            + normalize_coq_text(formal_case_lib_text)
        )
    )
    whole_hash = sha256_text(
        (
            normalize_coq_text(text)
            + "\n--FORMAL-CASE-LIB--\n"
            + normalize_coq_text(formal_case_lib_text)
        )
    )
    identifier_re = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\b")
    dependencies = {
        name: sorted(
            {
                token
                for token in identifier_re.findall(command)
                if token in definitions and token != name
            }
        )
        for name, command in definitions.items()
    }
    resolved: dict[str, str] = {}
    visiting: set[str] = set()

    def resolve(name: str) -> str:
        if name in resolved:
            return resolved[name]
        if name in visiting:
            return whole_hash
        visiting.add(name)
        payload = {
            "command": definitions[name],
            "environment_hash": environment_hash,
            "dependencies": [
                {"name": dependency, "hash": resolve(dependency)}
                for dependency in dependencies[name]
            ],
        }
        visiting.remove(name)
        resolved[name] = sha256_text(
            json.dumps(payload, sort_keys=True, separators=(",", ":"))
        )
        return resolved[name]

    for name in definitions:
        resolve(name)
    resolved["__whole_goal_file__"] = whole_hash
    return resolved


def goal_semantic_hash_for_lemma(
    lemma: dict[str, Any], definitions: dict[str, str]
) -> str:
    """Bind a manual wrapper to its generated goal definition or safe fallback."""

    target_symbol = lemma_target_symbol(lemma)
    if target_symbol is not None and target_symbol in definitions:
        return definitions[target_symbol]
    return sha256_text(
        definitions["__whole_goal_file__"] + ":" + lemma_statement_hash(lemma)
    )


def forbidden_top_level_declarations(
    text: str, kinds: set[str]
) -> list[dict[str, Any]]:
    return [item for item in top_level_declarations(text) if str(item["kind"]) in kinds]


def rollback_control_commands(text: str) -> list[dict[str, Any]]:
    return [
        item
        for item in top_level_commands(text)
        if str(item["kind"]) in ROLLBACK_CONTROL_KINDS
    ]


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


def coq_token_text(text: str) -> str:
    """Return a stable lexical form which ignores comments and formatting.

    This is intentionally a small identity lexer, not a Rocq parser.  It keeps
    strings and symbolic token boundaries intact while discarding only nested
    comments, whitespace and line-ending choices.  The ordinary parser and
    kernel check remain the authorities for declaration and proof validity.
    """

    source = strip_coq_comments(text).replace("\r\n", "\n").replace("\r", "\n")
    tokens: list[str] = []
    index = 0
    delimiters = set("()[]{},;")
    symbolic = set("!#$%&*+-./:<=>?@\\^|~")
    while index < len(source):
        char = source[index]
        if char.isspace():
            index += 1
            continue
        if char == '"':
            start = index
            index += 1
            while index < len(source):
                if source[index] != '"':
                    index += 1
                    continue
                if index + 1 < len(source) and source[index + 1] == '"':
                    index += 2
                    continue
                index += 1
                break
            tokens.append(source[start:index])
            continue
        if char.isalnum() or char == "_":
            start = index
            index += 1
            while index < len(source) and (
                source[index].isalnum() or source[index] in "_'"
            ):
                index += 1
            tokens.append(source[start:index])
            continue
        if char in delimiters:
            tokens.append(char)
            index += 1
            continue
        if char in symbolic:
            start = index
            index += 1
            while index < len(source) and source[index] in symbolic:
                index += 1
            tokens.append(source[start:index])
            continue
        # Preserve any Unicode or notation character not covered above as its
        # own token.  Ignoring it would be an unsafe widening of the boundary.
        tokens.append(char)
        index += 1
    return "\n".join(tokens)


def coq_token_digest(text: str) -> str:
    return sha256_text(coq_token_text(text))


def show_command_count(text: str) -> int:
    """Count executable standalone `Show.` commands outside comments/strings."""

    return sum(
        re.fullmatch(r"\s*Show\s*\.", command) is not None
        for command, _offset in _coq_commands(text)
    )


def markdown_table_cells(line: str) -> list[str]:
    """Split one Markdown table row while respecting code/escaped pipes."""

    stripped = line.strip()
    if not (stripped.startswith("|") and stripped.endswith("|")):
        return []
    cells: list[str] = []
    current: list[str] = []
    in_code = False
    escaped = False
    for char in stripped[1:-1]:
        if escaped:
            current.append(char)
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        if char == "`":
            in_code = not in_code
            current.append(char)
            continue
        if char == "|" and not in_code:
            cells.append(_markdown_table_cell("".join(current)))
            current = []
            continue
        current.append(char)
    if escaped:
        current.append("\\")
    cells.append(_markdown_table_cell("".join(current)))
    return cells


def _markdown_table_cell(value: str) -> str:
    cell = value.strip()
    if len(cell) >= 2 and cell.startswith("`") and cell.endswith("`"):
        return cell[1:-1].strip()
    return cell


def normalize_reuse_decision(value: str) -> str:
    return " ".join(value.lower().split())


def shown_goal_targets(text: str) -> list[str]:
    """Return fully qualified targets from strict debug inspection blocks."""

    _errors, shown = debug_goal_show_contract(text)
    return shown


def debug_goal_show_contract(text: str) -> tuple[list[str], list[str]]:
    """Validate imports and Goal/Show/.../Abort proof-reuse debug blocks."""

    commands = [command.strip() for command, _offset in _coq_commands(text)]
    harmless = re.compile(
        r"(?:"
        r"From\s+[A-Za-z0-9_.]+\s+Require\s+Import\s+[A-Za-z0-9_'.\s]+|"
        r"Require\s+Import\s+[A-Za-z0-9_'.\s]+|"
        r"Import\s+[A-Za-z0-9_'.\s]+|"
        r"(?:Local\s+)?Open\s+Scope\s+[A-Za-z0-9_']+|"
        r"Set\s+Printing\s+All"
        r")\s*\.",
        flags=re.DOTALL,
    )
    goal = re.compile(
        r"Goal\s+((?:[A-Za-z_][A-Za-z0-9_']*\.)+"
        r"[A-Za-z_][A-Za-z0-9_']*)\s*\.",
        flags=re.DOTALL,
    )
    show = re.compile(r"Show\s*\.", flags=re.DOTALL)
    abort = re.compile(r"Abort\s*\.", flags=re.DOTALL)
    forbidden_inside = TOP_LEVEL_DECLARATION_KINDS | {
        "Abort",
        "Load",
        "Cd",
        "Add",
        "Remove",
        "Require",
        "From",
        "Import",
        "Export",
        "Include",
        "Declare",
        "Open",
        "Set",
        "Unset",
        "End",
        "Qed",
        "Defined",
        "Admitted",
        "Ltac",
        "Ltac2",
        "Timeout",
        "Control",
    }
    errors: list[str] = []
    shown: list[str] = []
    index = 0
    while index < len(commands):
        command = commands[index]
        if harmless.fullmatch(command) is not None:
            index += 1
            continue
        target = goal.fullmatch(command)
        if target is None:
            errors.append(f"forbidden debug command: {command[:80]}")
            index += 1
            continue
        if index + 1 >= len(commands) or show.fullmatch(commands[index + 1]) is None:
            errors.append(
                f"Goal {target.group(1)} must be followed immediately by Show."
            )
            index += 1
            continue
        shown.append(target.group(1))
        index += 2
        closed = False
        while index < len(commands):
            proof_command = commands[index]
            if abort.fullmatch(proof_command) is not None:
                closed = True
                index += 1
                break
            prefix = _command_prefix(proof_command)
            if prefix is None:
                errors.append(
                    f"unparseable command in debug Goal {target.group(1)}: {proof_command[:80]}"
                )
            else:
                inner_head, _start, _end, modifiers, attributes = prefix
                if inner_head in forbidden_inside or modifiers or attributes:
                    errors.append(
                        f"forbidden command in debug Goal {target.group(1)}: {proof_command[:80]}"
                    )
            index += 1
        if not closed:
            errors.append(f"debug Goal {target.group(1)} must end with Abort.")
    if not shown:
        errors.append("debug script has no Goal/Show/.../Abort block")
    return errors, shown


def stable_text_digest(text: str) -> str:
    return sha256_text(normalize_coq_text(text))


def declaration_block_digest(text: str) -> str:
    """Hash declaration tokens while ignoring comments and formatting.

    The containing artifact still has an exact byte seal.  This digest answers
    the narrower merge/namespace question: whether statement and proof tokens
    changed.  Kernel validation remains mandatory after reuse or merge.
    """

    return coq_token_digest(text)


def rewrite_coq_identifiers(text: str, renames: dict[str, str]) -> str:
    """Rewrite exact Coq identifier tokens outside comments and strings.

    Parent merge uses this only for helper names whose independently checked
    group declarations collide.  Masking preserves source offsets, so the
    replacement cannot rewrite a substring of a longer identifier or textual
    examples embedded in comments/string literals.  The transformed merged
    candidate is still required to pass the parent full Coq check.
    """

    if not renames:
        return text
    invalid = [
        name
        for name in [*renames, *renames.values()]
        if COQ_IDENTIFIER_RE.fullmatch(name) is None
    ]
    if invalid:
        raise ValueError(
            "helper rename map contains an invalid Coq identifier: "
            + ", ".join(sorted(set(invalid)))
        )
    masked = mask_coq_strings(mask_coq_comments(text))
    parts: list[str] = []
    previous = 0
    for match in COQ_IDENTIFIER_RE.finditer(masked):
        replacement = renames.get(match.group(0))
        if replacement is None:
            continue
        parts.append(text[previous : match.start()])
        parts.append(replacement)
        previous = match.end()
    if not parts:
        return text
    parts.append(text[previous:])
    return "".join(parts)


def is_exact_declaration_line_range(
    start: int, end: int, *, declaration_start: int, declaration_end: int
) -> bool:
    """Return whether a hint names one complete declaration, not a subrange."""

    return start == declaration_start and end == declaration_end


def parse_manual_file(text: str) -> tuple[str, list[dict[str, Any]]]:
    lines = text.splitlines(keepends=True)
    masked_lines = mask_coq_strings(mask_coq_comments(text)).splitlines(keepends=True)
    offsets: list[int] = []
    offset = 0
    for line in lines:
        offsets.append(offset)
        offset += len(line)

    starts: list[tuple[int, str]] = []
    for idx, line in enumerate(masked_lines):
        match = LEMMA_RE.match(line)
        if match:
            starts.append((idx, match.group(1)))
    if not starts:
        commands = top_level_commands(text)
        allowed = {"Require", "From", "Import", "Export", "Open", "Close"}
        if not commands or any(
            str(command["kind"]) not in allowed for command in commands
        ):
            raise ValueError(
                "proof manual without lemma blocks must contain only imports and scope commands"
            )
        return text, []

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


def split_goal_parent(name: str) -> str | None:
    """Return the owning top-level VC name for one generated split goal."""

    match = SPLIT_GOAL_NAME_RE.fullmatch(name)
    return match.group("witness") if match else None


def partition_manual_lemmas(
    lemmas: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], dict[str, list[dict[str, Any]]]]:
    """Partition raw symexec lemmas into top-level VCs and their split goals."""

    witnesses = [
        lemma for lemma in lemmas if split_goal_parent(str(lemma["name"])) is None
    ]
    witness_names = {str(lemma["name"]) for lemma in witnesses}
    split_goals = {str(lemma["name"]): [] for lemma in witnesses}
    orphaned: list[str] = []
    for lemma in lemmas:
        name = str(lemma["name"])
        parent = split_goal_parent(name)
        if parent is None:
            continue
        if parent not in witness_names:
            orphaned.append(name)
            continue
        split_goals[parent].append(lemma)
    if orphaned:
        raise ValueError("split goals have no owning witness: " + ", ".join(orphaned))
    return witnesses, split_goals


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


def lemma_proof_parts(
    block_or_lemma: str | dict[str, Any],
) -> tuple[str, str, str]:
    """Return exact ``(statement, proof span, trailing bytes)`` for a lemma.

    The editable span begins at ``Proof.`` (including ``Proof using``) and
    ends at the first proof terminator's period.  Everything before and after
    that span is protected, including spaces after ``Admitted.``/``Abort.``,
    blank lines between declarations, and the file's final newline state.
    """

    block = (
        str(block_or_lemma.get("block", ""))
        if isinstance(block_or_lemma, dict)
        else str(block_or_lemma)
    )
    masked = mask_coq_strings(mask_coq_comments(block))
    proof = PROOF_START_RE.search(masked)
    if proof is None:
        raise ValueError("lemma block has no Proof delimiter")
    terminator = PROOF_TERMINATOR_RE.search(masked, proof.end())
    if terminator is None:
        raise ValueError("lemma proof has no Qed/Defined/Admitted/Abort terminator")
    return (
        block[: proof.start()],
        block[proof.start() : terminator.end()],
        block[terminator.end() :],
    )


def block_has_incomplete_proof(block: str) -> bool:
    if incomplete_proof_markers(block):
        return True
    masked = mask_coq_strings(mask_coq_comments(block))
    terminators = list(PROOF_TERMINATOR_RE.finditer(masked))
    if not terminators:
        return True
    final_terminator = terminators[-1].group(0).strip()
    return re.match(r"(?:Qed|Defined)\b", final_terminator) is None


def proof_mode_errors(block: str, proof_mode: str) -> list[str]:
    """Check that a solved top-level VC follows its controller-verified route."""

    uncommented = mask_coq_strings(strip_coq_comments(block))
    errors: list[str] = []
    if proof_mode == "aggressive_pre_process":
        if re.search(r"\baggressive_pre_process\b", uncommented) is None:
            errors.append("does not use aggressive_pre_process")
        if re.search(r"\bLLM_pre_process\b", uncommented) is not None:
            errors.append(
                "uses LLM_pre_process despite the aggressive_pre_process plan"
            )
    elif proof_mode == "LLM_pre_process":
        if re.search(r"\baggressive_pre_process\b", uncommented) is not None:
            errors.append("uses aggressive_pre_process despite the LLM_pre_process plan")
        if re.search(r"\bLLM_pre_process\b", uncommented) is None:
            errors.append("does not use LLM_pre_process")
    else:
        errors.append(f"has unsupported proof mode `{proof_mode}`")
    return errors


def incomplete_proof_markers(text: str) -> list[dict[str, Any]]:
    """Find executable incomplete proof terminators outside comments/strings."""

    uncommented = mask_coq_strings(strip_coq_comments(text))
    findings: list[dict[str, Any]] = []
    for pattern, kind in ((ADMITTED_RE, "Admitted"), (ABORT_RE, "Abort")):
        for match in pattern.finditer(uncommented):
            findings.append(
                {"kind": kind, "line": uncommented.count("\n", 0, match.start()) + 1}
            )
    return findings


def lemma_statement_text(block_or_lemma: str | dict[str, Any]) -> str:
    block = (
        str(block_or_lemma.get("block", ""))
        if isinstance(block_or_lemma, dict)
        else str(block_or_lemma)
    )
    masked = mask_coq_strings(mask_coq_comments(block))
    match = PROOF_START_RE.search(masked)
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
    return coq_token_digest(canonical)


def lemma_target_symbol(block_or_lemma: str | dict[str, Any]) -> str | None:
    statement = normalize_coq_text(lemma_statement_text(block_or_lemma))
    match = SIMPLE_TARGET_RE.match(statement)
    return match.group(2) if match else None


def generated_artifact_module_spellings(
    target_files: Mapping[str, Any],
    *,
    roles: Iterable[str] | None = None,
) -> frozenset[str]:
    """Return exact Require spellings for selected current generated modules.

    Rocq dependencies may spell a module either with the sealed logical prefix
    or as the local module stem.  The returned set deliberately contains only
    those two exact spellings for the selected generated artifacts; unrelated
    shared or alias modules with conventional generated-file suffixes are not
    classified as current-case dependencies.
    """

    selected_roles = tuple(GENERATED_ARTIFACT_ROLES if roles is None else roles)
    unsupported = sorted(set(selected_roles) - set(GENERATED_ARTIFACT_ROLES))
    if unsupported:
        raise ValueError(
            "unsupported generated artifact role(s): " + ", ".join(unsupported)
        )
    active_theory = str(target_files.get("active_case_theory") or "").strip(".")
    if not active_theory:
        raise ValueError("target_files active_case_theory is missing")
    modules: set[str] = set()
    for role in selected_roles:
        raw_relative = target_files.get(role)
        if not isinstance(raw_relative, str) or not raw_relative:
            raise ValueError(f"target_files {role} is missing")
        relative = Path(raw_relative)
        if relative.suffix != ".v" or not relative.stem:
            raise ValueError(f"target_files {role} is not a Rocq source path")
        modules.add(relative.stem)
        modules.add(f"{active_theory}.{relative.stem}")
    return frozenset(modules)


def required_rocq_modules(
    text: str,
    *,
    source_label: str = "Rocq source",
) -> list[str]:
    """Parse direct Require dependencies with the canonical Coq parser."""

    return _dependency_modules(text, source_label=Path(source_label))


def lib_contract_errors(
    text: str,
    *,
    forbidden_modules: Collection[str] = (),
) -> list[str]:
    errors: list[str] = []
    for marker in incomplete_proof_markers(text):
        errors.append(f"lib contains {marker['kind']}.")
    for command in rollback_control_commands(text):
        errors.append(
            f"lib contains forbidden rollback control command {command['kind']}."
        )
    for command in unsafe_typing_commands(text):
        detail = command.get("unsafe_typing_control") or ",".join(
            command.get("bypass_checks", [])
        )
        errors.append(f"lib contains unsafe typing control {detail}.")
    for declaration in unsafe_assumption_declarations(text):
        errors.append(f"lib contains assumption declaration {declaration['kind']}.")
    forbidden = frozenset(str(module) for module in forbidden_modules)
    if forbidden:
        try:
            dependencies = required_rocq_modules(
                text,
                source_label="formal_case_lib.v",
            )
        except ValueError as exc:
            errors.append(f"lib dependency parsing failed: {exc}")
        else:
            for module in dependencies:
                if module in forbidden:
                    errors.append(
                        "lib imports generated case artifact module: " + module
                    )
    return errors


def parse_lib_declarations(text: str) -> list[dict[str, Any]]:
    masked = mask_coq_strings(mask_coq_comments(text))
    starts: list[tuple[int, re.Match[str]]] = [
        (m.start(1) if m.group(1) is not None else m.start(2), m)
        for m in CASE_LIB_DECL_RE.finditer(masked)
    ]
    declarations: list[dict[str, Any]] = []
    for idx, (start, match) in enumerate(starts):
        end = starts[idx + 1][0] if idx + 1 < len(starts) else len(text)
        block = text[start:end].strip() + "\n"
        import_head = match.group(1)
        kind = "Import" if import_head else str(match.group(2))
        name = (
            normalize_import_line(block.splitlines()[0])
            if import_head
            else str(match.group(3))
        )
        declarations.append(
            {
                "kind": kind,
                "name": name,
                "block": block,
                "start_offset": start,
                "end_offset": end,
                "start_line": text.count("\n", 0, start) + 1,
                "end_line": max(
                    text.count("\n", 0, start) + 1,
                    text.count("\n", 0, end),
                ),
            }
        )
    return declarations


def normalize_import_line(line: str) -> str:
    return " ".join(line.strip().rstrip(".").split()) + "."


def is_official_library_import(line: str) -> bool:
    normalized = normalize_import_line(line)
    require_match = REQUIRE_IMPORT_RE.match(normalized)
    if require_match:
        modules = require_match.group(1).split()
        return bool(modules) and all(
            module == "Coq" or module.startswith("Coq.") for module in modules
        )

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
        raise ValueError(
            f"group_id does not produce a valid helper namespace suffix: {group_id!r}"
        )
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


def _group_helper_conflict_renames(
    seed_text: str,
    group_texts: list[tuple[str, str, dict[str, Any]]],
    allowed_public_helpers_by_group: dict[str, dict[str, set[str]]],
) -> dict[str, dict[str, str]]:
    """Plan deterministic per-group names for valid same-name helper variants.

    A token-identical public/reuse block is the canonical declaration when one
    is present; otherwise the first declaration in manifest merge order is
    canonical.  Every other token-distinct variant receives a fresh name
    ending in its own group namespace suffix.  Invalid foreign/unsuffixed
    helpers are deliberately excluded here so the ordinary merge contract
    still rejects them instead of laundering them through a generated name.
    """

    seed_keys = {
        (str(item["kind"]), str(item["name"]))
        for item in parse_lib_declarations(seed_text)
    }
    reserved_names = {
        str(item["name"])
        for item in parse_lib_declarations(seed_text)
        if str(item["kind"]) != "Import"
    }
    occurrences: dict[str, list[dict[str, Any]]] = {}
    for group_id, text, namespace in group_texts:
        suffix = str(namespace.get("suffix") or "")
        allowed = allowed_public_helpers_by_group.get(group_id, {})
        for declaration in parse_lib_declarations(text):
            kind = str(declaration["kind"])
            name = str(declaration["name"])
            if kind != "Import":
                reserved_names.add(name)
            if kind not in HELPER_DECL_KINDS or (kind, name) in seed_keys or not name:
                continue
            digest = declaration_block_digest(str(declaration["block"]))
            is_public = digest in allowed.get(name, set())
            is_owned = bool(suffix and name.endswith(suffix))
            if not is_public and not is_owned:
                continue
            occurrences.setdefault(name, []).append(
                {
                    "group_id": group_id,
                    "digest": digest,
                    "is_public": is_public,
                    "suffix": suffix,
                }
            )

    renames: dict[str, dict[str, str]] = {}
    for name, records in occurrences.items():
        digests = {str(item["digest"]) for item in records}
        if len(digests) <= 1:
            continue
        # One group cannot give two token-distinct declarations with the same
        # name a single unambiguous rename map.  Its exact group check should
        # already reject that source, and the normal merge error remains the
        # correct fallback if a malformed artifact reaches this boundary.
        per_group_digests: dict[str, set[str]] = {}
        for item in records:
            per_group_digests.setdefault(str(item["group_id"]), set()).add(
                str(item["digest"])
            )
        if any(len(group_digests) != 1 for group_digests in per_group_digests.values()):
            continue
        canonical = next(
            (item for item in records if bool(item["is_public"])),
            records[0],
        )
        canonical_digest = str(canonical["digest"])
        for item in records:
            if str(item["digest"]) == canonical_digest:
                continue
            group_id = str(item["group_id"])
            suffix = str(item["suffix"])
            if not suffix:
                continue
            # A helper name has exactly one controller namespace suffix.
            # Appending a second ``__group`` tail would be parsed as one
            # foreign composite suffix by the existing namespace contract.
            # Replace the historical suffix and add a deterministic variant
            # marker only when the natural current-group name is occupied.
            stem = HELPER_NAMESPACE_SUFFIX_RE.sub("", name)
            candidate = stem + suffix
            while candidate in reserved_names:
                stem += "_variant"
                candidate = stem + suffix
            reserved_names.add(candidate)
            renames.setdefault(group_id, {})[name] = candidate
    return renames


def merge_group_worker_libs(
    seed_text: str,
    group_texts: list[tuple[str, str, dict[str, Any]]],
    *,
    allowed_public_helpers_by_group: dict[str, dict[str, set[str]]] | None = None,
    forbidden_modules: Collection[str] = (),
) -> tuple[
    str,
    list[dict[str, str]],
    dict[str, dict[str, str]],
    list[str],
]:
    """Merge group_worker_lib helper declarations onto formal_case_lib seed.

    The caller supplies groups in manifest merge order.  Token-identical helper
    blocks keep the first declaration.  For a same-name token-distinct variant,
    a token-identical public/reuse block remains canonical when available;
    otherwise the first manifest-order block remains canonical.  Other valid
    variants and their local references are deterministically renamed with
    their own group namespace suffix.  Parent verification must apply the
    returned rename maps to that group's assigned manual proof blocks before
    the full Coq check.

    Returns ``(merged_text, added_declarations, helper_renames, errors)``.
    """
    allowed_by_group = allowed_public_helpers_by_group or {}
    helper_renames = _group_helper_conflict_renames(
        seed_text,
        group_texts,
        allowed_by_group,
    )
    seed_declarations = parse_lib_declarations(seed_text)
    transformed_group_texts: list[tuple[str, str, dict[str, Any]]] = []
    for group_id, text, namespace in group_texts:
        renames = helper_renames.get(group_id, {})
        group_declarations = parse_lib_declarations(text)
        seed_prefix_is_intact = (
            len(group_declarations) >= len(seed_declarations)
            and all(
                str(seed["kind"]) == str(candidate["kind"])
                and str(seed["name"]) == str(candidate["name"])
                and declaration_block_digest(str(seed["block"]))
                == declaration_block_digest(str(candidate["block"]))
                for seed, candidate in zip(
                    seed_declarations,
                    group_declarations[: len(seed_declarations)],
                    strict=True,
                )
            )
        )
        if (
            renames
            and seed_prefix_is_intact
            and len(group_declarations) > len(seed_declarations)
        ):
            # Keep every seed byte in this group copy untouched.  Identifier
            # rewrites apply only to declarations appended after the complete
            # token-identical seed prefix.
            additions_start = int(
                group_declarations[len(seed_declarations)]["start_offset"]
            )
            text = text[:additions_start] + rewrite_coq_identifiers(
                text[additions_start:],
                renames,
            )
        transformed_group_texts.append((group_id, text, namespace))

    errors = lib_contract_errors(
        seed_text,
        forbidden_modules=forbidden_modules,
    )
    seed_decls = {f"{d['kind']}:{d['name']}": d for d in seed_declarations}
    seed_names = {d["name"] for d in seed_declarations if d["kind"] != "Import"}
    seed_commands = top_level_commands(seed_text)
    seed_command_keys = [
        (str(item["kind"]), str(item["name"]), str(item["command_hash"]))
        for item in seed_commands
    ]
    helper_additions_by_name: dict[str, dict[str, str]] = {}
    import_additions_by_name: dict[str, dict[str, str]] = {}
    import_additions: list[dict[str, str]] = []
    helper_additions: list[dict[str, str]] = []

    for group_id, text, namespace in transformed_group_texts:
        suffix = str(namespace.get("suffix", ""))
        allowed_public_helpers = allowed_by_group.get(group_id, {})
        errors.extend(_helper_namespace_errors(group_id, namespace))
        errors.extend(
            f"{group_id}: {error}"
            for error in lib_contract_errors(
                text,
                forbidden_modules=forbidden_modules,
            )
        )
        group_decls = parse_lib_declarations(text)
        group_commands = top_level_commands(text)
        group_command_keys = [
            (str(item["kind"]), str(item["name"]), str(item["command_hash"]))
            for item in group_commands
        ]
        if group_command_keys[: len(seed_command_keys)] != seed_command_keys:
            errors.append(
                f"{group_id}: group_worker_lib must keep all formal_case_lib seed commands first, in order, with identical tokens"
            )

        added_commands = group_commands[len(seed_command_keys) :]

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
            elif (
                declaration["kind"] in HELPER_DECL_KINDS
                and declaration["name"] == first["name"]
            ):
                parsed_helper_commands.add(key)

        for command in added_commands:
            kind = str(command["kind"])
            name = str(command["name"])
            key = (kind, name, str(command["command_hash"]))
            if kind in {"Require", "From"}:
                if key not in parsed_import_commands:
                    errors.append(
                        f"{group_id}: new import command is not a standalone parseable block"
                    )
            elif kind in HELPER_DECL_KINDS:
                if key not in parsed_helper_commands:
                    errors.append(
                        f"{group_id}: new helper declaration `{name}` is not a standalone parseable block"
                    )
                elif name in seed_names:
                    errors.append(
                        f"{group_id}: new helper declaration `{name}` duplicates formal_case_lib seed name"
                    )
            else:
                errors.append(
                    f"{group_id}: new top-level command `{name}` has forbidden kind `{kind}`"
                )
        group_by_key = {f"{d['kind']}:{d['name']}": d for d in group_decls}
        for key, seed in seed_decls.items():
            group_seed = group_by_key.get(key)
            if group_seed is None:
                errors.append(
                    f"{group_id}: removed formal_case_lib seed declaration `{seed['name']}`"
                )
            elif declaration_block_digest(
                str(seed["block"])
            ) != declaration_block_digest(str(group_seed["block"])):
                errors.append(
                    f"{group_id}: modified formal_case_lib seed declaration `{seed['name']}`"
                )
        for decl in group_decls:
            key = f"{decl['kind']}:{decl['name']}"
            if key in seed_decls:
                continue
            if decl["kind"] == "Import":
                if not is_official_library_import(decl["name"]):
                    errors.append(
                        f"{group_id}: new group_worker_lib import `{decl['name']}` is not an allowed official Rocq import"
                    )
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
                errors.append(
                    f"{group_id}: new group_worker_lib declaration `{decl['name']}` has forbidden kind `{decl['kind']}`"
                )
                continue
            if decl["name"] in seed_names:
                errors.append(
                    f"{group_id}: new group_worker_lib declaration `{decl['name']}` duplicates formal_case_lib seed name"
                )
                continue
            block_digest = declaration_block_digest(str(decl["block"]))
            is_exact_public_reuse = block_digest in allowed_public_helpers.get(
                str(decl["name"]), set()
            )
            is_owned_suffix = bool(suffix and decl["name"].endswith(suffix))
            if not is_owned_suffix and not is_exact_public_reuse:
                errors.append(
                    f"{group_id}: new helper declaration `{decl['name']}` must end with current suffix `{suffix}` or have the same declaration/proof tokens as a sealed public/reuse candidate"
                )
                continue
            foreign_suffix = HELPER_NAMESPACE_SUFFIX_RE.search(decl["name"])
            if (
                foreign_suffix
                and foreign_suffix.group(0) != suffix
                and not is_exact_public_reuse
            ):
                errors.append(
                    f"{group_id}: new helper declaration `{decl['name']}` uses foreign helper suffix `{foreign_suffix.group(0)}`"
                )
                continue
            if decl["name"] in helper_additions_by_name:
                prior = helper_additions_by_name[str(decl["name"])]
                if declaration_block_digest(str(prior["block"])) != block_digest:
                    errors.append(
                        f"{group_id}: conflicting new group_worker_lib declaration name `{decl['name']}` already supplied by group `{prior['group_id']}`"
                    )
                continue
            added = {
                **decl,
                "group_id": group_id,
                "statement_hash": _declaration_statement_hash(decl),
                "helper_namespace_suffix": (
                    foreign_suffix.group(0)
                    if not is_owned_suffix and is_exact_public_reuse and foreign_suffix
                    else suffix
                ),
                "helper_origin": (
                    "public-reuse"
                    if not is_owned_suffix and is_exact_public_reuse
                    else "group-owned"
                ),
            }
            helper_additions_by_name[decl["name"]] = added
            helper_additions.append(added)

    additions = import_additions + helper_additions
    if errors:
        return seed_text, additions, helper_renames, errors
    added_text = "\n".join(decl["block"].rstrip() for decl in additions)
    if not added_text:
        return seed_text, [], helper_renames, []
    separator = (
        ""
        if seed_text.endswith("\n\n")
        else "\n"
        if seed_text.endswith("\n")
        else "\n\n"
    )
    merged = seed_text + separator + added_text + "\n"
    return merged, additions, helper_renames, []
