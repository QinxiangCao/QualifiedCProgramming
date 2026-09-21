#!/usr/bin/env python3
"""Small Coq/manual utilities for vc-proving preparation and group workers."""

from __future__ import annotations

import re
from dataclasses import dataclass
from collections.abc import Collection, Iterable, Mapping
from pathlib import Path
from typing import Any

from coq_tooling import _dependency_modules

LEMMA_KEYWORDS = "Lemma|Theorem|Proposition|Corollary|Example|Fact|Remark"
LEMMA_RE = re.compile(rf"^[ \t]*(?:{LEMMA_KEYWORDS})\s+([A-Za-z0-9_']+)\s*:", re.MULTILINE)
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


def top_level_commands(
    text: str, *, include_proof_commands: bool = False
) -> list[dict[str, Any]]:
    """Read command heads, including proof commands when checking safety.

    Rocq permits commands such as Axiom and Unset Guard Checking inside an
    open proof. Safety scans must inspect those commands as well.
    """

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
            if not include_proof_commands:
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
            else head
        )
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
                "line": uncommented.count("\n", 0, offset + head_start) + 1,
                **({"in_proof": in_proof} if include_proof_commands else {}),
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


def forbidden_top_level_declarations(
    text: str, kinds: set[str]
) -> list[dict[str, Any]]:
    return [item for item in top_level_declarations(text) if str(item["kind"]) in kinds]


def rollback_control_commands(text: str) -> list[dict[str, Any]]:
    return [
        item
        for item in top_level_commands(text, include_proof_commands=True)
        if str(item["kind"]) in ROLLBACK_CONTROL_KINDS
    ]


def unsafe_typing_commands(text: str) -> list[dict[str, Any]]:
    return [
        item
        for item in top_level_commands(text, include_proof_commands=True)
        if item.get("unsafe_typing_control") or item.get("bypass_checks")
    ]


def unsafe_assumption_declarations(text: str) -> list[dict[str, Any]]:
    """Find axioms and section-context commands that occur outside a Section."""

    active_sections: list[str] = []
    findings: list[dict[str, Any]] = []
    for command in top_level_commands(text, include_proof_commands=True):
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


def unsafe_commands(commands: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    """Find all forbidden assumptions, rollback and typing controls in one scan."""
    sections: list[str] = []
    findings: list[dict[str, Any]] = []
    for command in commands:
        kind, name = command["kind"], command["name"]
        if kind == "Section":
            sections.append(name)
        elif kind == "End" and sections and name == sections[-1]:
            sections.pop()
        elif (
            kind in UNCONDITIONAL_ASSUMPTION_KINDS | ROLLBACK_CONTROL_KINDS
            or (kind in SECTION_CONTEXT_DECLARATION_KINDS and not sections)
            or command.get("unsafe_typing_control") or command.get("bypass_checks")
        ):
            findings.append(command)
    return findings


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


def parse_manual_file(text: str) -> tuple[str, list[dict[str, Any]]]:
    lines = text.splitlines(keepends=True)
    masked_lines = mask_coq_strings(mask_coq_comments(text)).splitlines(keepends=True)

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
        lemmas.append(
            {
                "name": name,
                "block": "".join(lines[start_idx:end_idx]),
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
    that span has protected tokens. Callers compare those tokens while allowing
    comments, whitespace and line-ending changes.
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
    """Check the required opening tactic, rather than a word anywhere in a proof."""

    if proof_mode not in {"LLM_pre_process", "aggressive_pre_process"}:
        return [f"has unsupported proof mode `{proof_mode}`"]
    try:
        _statement, proof, _trailing = lemma_proof_parts(block)
    except ValueError as exc:
        return [str(exc)]
    commands = _coq_commands(proof)
    if len(commands) < 2 or re.match(
        rf"\s*{proof_mode}\b", mask_coq_strings(commands[1][0])
    ) is None:
        return [f"must open its proof with {proof_mode}"]
    other_mode = (
        "aggressive_pre_process"
        if proof_mode == "LLM_pre_process"
        else "LLM_pre_process"
    )
    if re.search(rf"\b{other_mode}\b", mask_coq_strings(strip_coq_comments(proof))):
        return [f"uses {other_mode} despite the {proof_mode} plan"]
    return []


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


@dataclass
class Manual:
    """One parsed current source shared by planning, validation and merge."""

    text: str
    prelude: str
    lemmas: list[dict[str, Any]]
    by_name: dict[str, dict[str, Any]]
    vc_index: dict[str, Any]


def parse_manual(text: str) -> Manual:
    prelude, lemmas = parse_manual_file(text)
    ensure_unique_lemma_names(lemmas)
    witnesses, split_goals = partition_manual_lemmas(lemmas)
    by_name = lemma_by_name(lemmas)
    index = {
        "by_name": {
            name: {"name": name, "parent": split_goal_parent(name),
                   "statement": lemma_statement_text(lemma)}
            for name, lemma in by_name.items()
        },
        "top_level": [str(item["name"]) for item in witnesses],
        "split_goals": {name: [str(item["name"]) for item in splits]
                        for name, splits in split_goals.items()},
    }
    return Manual(text, prelude, lemmas, by_name, index)


def manual_vc_index(text: str) -> dict[str, Any]:
    return parse_manual(text).vc_index


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
    commands: list[dict[str, Any]] | None = None,
) -> list[str]:
    errors: list[str] = []
    for marker in incomplete_proof_markers(text):
        errors.append(f"lib contains {marker['kind']}.")
    for command in unsafe_commands(
        commands if commands is not None else top_level_commands(text, include_proof_commands=True)
    ):
        if command["kind"] in ROLLBACK_CONTROL_KINDS:
            errors.append(f"lib contains forbidden rollback control command {command['kind']}.")
        elif command.get("unsafe_typing_control") or command.get("bypass_checks"):
            errors.append("lib contains unsafe typing control.")
        else:
            errors.append(f"lib contains assumption declaration {command['kind']}.")
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
            normalize_import_line(_coq_commands(block)[0][0])
            if import_head
            else str(match.group(3))
        )
        declarations.append(
            {
                "kind": kind,
                "name": name,
                "block": block,
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
    if not isinstance(group_id, str) or re.fullmatch(r"[A-Za-z0-9_]+", group_id) is None:
        raise ValueError(
            f"group id must contain only ASCII letters, digits, or underscores: {group_id!r}"
        )
    return {
        "policy": "group-id-suffixed",
        "group_id": str(group_id),
        "suffix": "__" + group_id,
        "required": "yes",
    }
