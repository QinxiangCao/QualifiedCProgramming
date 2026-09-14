"""Batch diagnostics for QCP function contracts before staged spec freeze.

The canonical symbolic executor reports only its first reachable contract
error.  These deliberately conservative surface checks identify three QCP
failure shapes that can otherwise consume separate annotation design rounds.
They do not replace symbolic execution and do not weaken any freeze gate.
"""

from __future__ import annotations

import re
from typing import Any

ANNOTATED_FUNCTION_RE = re.compile(
    r"\b(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*"
    r"\((?P<parameters>[^;{}]*)\)\s*"
    r"/\*@(?P<contract>.*?)\*/\s*\{",
    re.DOTALL,
)
IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
ALIAS_EQUALITY_RE = re.compile(
    r"\b(?P<left>[A-Za-z_][A-Za-z0-9_]*)\s*==\s*"
    r"(?P<right>[A-Za-z_][A-Za-z0-9_]*)\b"
)
SAFE_CALL_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*Safe)\s*\(")
COMPOUND_ASSIGNMENT_RE = re.compile(r"(?:\+=|-=)\s*(?P<rhs>[^;]+);")
PRODUCT_LEFT_OPERAND_RE = re.compile(
    r"\b(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*\*(?!=)"
)
TOP_LEVEL_DECLARATION_RE = re.compile(
    r"^\s*(?:Definition|Fixpoint|CoFixpoint|Lemma|Theorem|Fact|Remark|"
    r"Inductive|CoInductive|Record|Structure|Class)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b",
    re.MULTILINE,
)


def _parameter_names(parameters: str) -> set[str]:
    result: set[str] = set()
    for parameter in parameters.split(","):
        identifiers = IDENTIFIER_RE.findall(parameter)
        if identifiers:
            result.add(identifiers[-1])
    return result


def _contract_parts(contract: str) -> tuple[str, str]:
    require = re.search(r"\bRequire\b(?P<body>.*?)\bEnsure\b", contract, re.DOTALL)
    ensure = re.search(r"\bEnsure\b(?P<body>.*)\Z", contract, re.DOTALL)
    return (
        require.group("body") if require is not None else "",
        ensure.group("body") if ensure is not None else "",
    )


def _matching_brace(source: str, opening: int) -> int:
    depth = 0
    index = opening
    in_string: str | None = None
    in_line_comment = False
    in_block_comment = False
    while index < len(source):
        pair = source[index : index + 2]
        char = source[index]
        if in_line_comment:
            if char == "\n":
                in_line_comment = False
            index += 1
            continue
        if in_block_comment:
            if pair == "*/":
                in_block_comment = False
                index += 2
            else:
                index += 1
            continue
        if in_string is not None:
            if char == "\\":
                index += 2
                continue
            if char == in_string:
                in_string = None
            index += 1
            continue
        if pair == "//":
            in_line_comment = True
            index += 2
            continue
        if pair == "/*":
            in_block_comment = True
            index += 2
            continue
        if char in {'"', "'"}:
            in_string = char
            index += 1
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return index
        index += 1
    return len(source)


def _function_contracts(source: str) -> list[dict[str, Any]]:
    functions: list[dict[str, Any]] = []
    for match in ANNOTATED_FUNCTION_RE.finditer(source):
        opening = match.end() - 1
        closing = _matching_brace(source, opening)
        require, ensure = _contract_parts(match.group("contract"))
        functions.append(
            {
                "name": match.group("name"),
                "parameters": _parameter_names(match.group("parameters")),
                "require": require,
                "ensure": ensure,
                "body": source[opening + 1 : closing],
            }
        )
    return functions


def _lib_declarations(text: str) -> dict[str, str]:
    matches = list(TOP_LEVEL_DECLARATION_RE.finditer(text))
    return {
        match.group("name"): text[
            match.start() : (
                matches[index + 1].start()
                if index + 1 < len(matches)
                else len(text)
            )
        ]
        for index, match in enumerate(matches)
    }


def _bounded_intermediate_product(block: str, multiplier: str) -> bool:
    normalized = " ".join(block.split())
    lower = r"(?:INT_MIN|-2147483648)"
    upper = r"(?:INT_MAX|2147483647)"
    for match in re.finditer(
        rf"let\s+(?P<product>[A-Za-z_][A-Za-z0-9_']*)\s*:=\s*"
        rf"(?P<expression>.*?\b{re.escape(multiplier)}\s*\*.*?)\s+in\b",
        normalized,
    ):
        product = re.escape(match.group("product"))
        if re.search(
            rf"{lower}\s*<=\s*{product}\s*<=\s*{upper}",
            normalized,
        ):
            return True
    for bound in re.finditer(
        rf"{lower}\s*<=\s*(?P<expression>.*?)\s*<=\s*{upper}",
        normalized,
    ):
        expression = bound.group("expression")
        if (
            re.search(rf"\b{re.escape(multiplier)}\s*\*", expression)
            and "+" not in expression
            and " - " not in expression
        ):
            return True
    return False


def contract_surface_lint(c_source: str, lib_text: str) -> list[dict[str, str]]:
    """Return every recognized pre-freeze contract issue in one pass."""

    findings: list[dict[str, str]] = []
    lib_declarations = _lib_declarations(lib_text)
    for function in _function_contracts(c_source):
        name = str(function["name"])
        parameters = set(function["parameters"])
        require = str(function["require"])
        ensure = str(function["ensure"])

        if "||" in require and "@pre" in ensure:
            findings.append(
                {
                    "kind": "branch-prestate-ambiguity",
                    "function": name,
                    "location": f"{name} Require/Ensure",
                    "message": (
                        "a disjunctive Require creates multiple entry branches "
                        "while Ensure binds @pre values"
                    ),
                    "repair": (
                        "replace the branch-shaped premise with an equivalent "
                        "non-branch fact, or redesign the postcondition so @pre "
                        "has one canonical entry binding"
                    ),
                }
            )

        seen_aliases: set[tuple[str, str]] = set()
        for alias in ALIAS_EQUALITY_RE.finditer(require):
            left = alias.group("left")
            right = alias.group("right")
            pair = tuple(sorted((left, right)))
            if (
                left == right
                or left not in parameters
                or right not in parameters
                or pair in seen_aliases
            ):
                continue
            seen_aliases.add(pair)
            if f"{left}@pre" in ensure and f"{right}@pre" in ensure:
                findings.append(
                    {
                        "kind": "aliased-formals-prestate-ambiguity",
                        "function": name,
                        "location": f"{name} Require/Ensure",
                        "message": (
                            f"Require aliases {left} and {right}, but Ensure "
                            "requests both pre-state representatives"
                        ),
                        "repair": (
                            "choose one canonical aliased formal in the "
                            "postcondition and omit redundant @pre equalities"
                        ),
                    }
                )

        safe_names = sorted(set(SAFE_CALL_RE.findall(require)))
        safe_blocks = {
            safe_name: lib_declarations[safe_name]
            for safe_name in safe_names
            if safe_name in lib_declarations
        }
        if not safe_blocks:
            continue
        reported_products: set[tuple[str, tuple[str, ...]]] = set()
        for assignment in COMPOUND_ASSIGNMENT_RE.finditer(str(function["body"])):
            rhs = assignment.group("rhs")
            products = PRODUCT_LEFT_OPERAND_RE.findall(rhs)
            # The first binary product in the compound RHS is evaluated before
            # the outer update. Later products are commonly address arithmetic
            # inside a dereference and have separate generated safety VCs.
            for multiplier in products[:1]:
                relevant = {
                    safe_name: block
                    for safe_name, block in safe_blocks.items()
                    if re.search(rf"\b{re.escape(multiplier)}\b", block)
                    and "*" in block
                }
                identity = (multiplier, tuple(sorted(relevant)))
                if not relevant or identity in reported_products:
                    continue
                reported_products.add(identity)
                if any(
                    _bounded_intermediate_product(block, multiplier)
                    for block in relevant.values()
                ):
                    continue
                findings.append(
                    {
                        "kind": "signed-intermediate-overflow-gap",
                        "function": name,
                        "location": f"{name} compound assignment",
                        "message": (
                            f"the C expression computes {multiplier} * (...) "
                            "before the compound addition/subtraction, but the "
                            "referenced safety predicate only bounds a larger "
                            "expression"
                        ),
                        "repair": (
                            "add a caller-visible bound for the multiplication "
                            "intermediate as well as the final stored value"
                        ),
                    }
                )
    return findings
