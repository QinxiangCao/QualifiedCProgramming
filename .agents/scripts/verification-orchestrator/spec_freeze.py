#!/usr/bin/env python3
"""Extract the frozen-specification surface of an annotated C file and its case lib.

The annotation agent owns the whole C file and the case lib, but a run may fix
part of that surface as an input rather than something to redesign.  This module
extracts exactly that surface so the controller can compare it before and after
an annotation attempt.

One rule governs every artifact: **a baseline entry must survive token-identical;
new entries are unconstrained.**  Adding an ``Extern Coq`` declaration, importing
another module, or proving a new lemma in the case lib is always allowed; editing
one that existed at baseline is not.

Extracted (frozen when ``--freeze-spec`` names the owning function, or always for
the shared surface):

``extern_coq``    one entry per ``(name : type)`` inside ``/*@ Extern Coq ... */``
``import_coq``    one entry per module in ``/*@ Import Coq Require Import ... */``
``specs``         one entry per function spec block, keyed ``<function>::<spec>``;
                  covers named specs and the ``<= other_spec`` refinement clause
``lib``           one entry per top-level declaration in the case lib

Not extracted, and therefore always editable: ``Inv Assert``, ``Assert``,
``Given``, ``where`` and every other call-site or body annotation.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
# `proof_manual_utils` is the shared Coq-source implementation and lives beside
# the vc-proving scripts.  controller.py already puts that directory on the path;
# repeat it here so this module also works as a standalone command.
VC_PROVING_SCRIPTS = SCRIPT_DIR.parent / "vc-proving"
for _path in (SCRIPT_DIR, VC_PROVING_SCRIPTS):
    if str(_path) not in sys.path:
        sys.path.insert(0, str(_path))

from proof_manual_utils import coq_token_digest, parse_lib_declarations

ANNOTATION_RE = re.compile(r"/\*@(.*?)\*/", re.S)
EXTERN_ENTRY_RE = re.compile(r"\(\s*([A-Za-z_][A-Za-z0-9_:']*)\s*:(.*?)\)\s*(?=\(|$)", re.S)
IMPORT_RE = re.compile(r"Import\s+Coq\s+Require\s+Import\s+(.+)", re.S)
SPEC_HEAD_RE = re.compile(
    r"^\s*(?:(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*(?P<refines><=\s*[A-Za-z_][A-Za-z0-9_']*)?\s*)?"
    r"(?=With\b|Require\b)",
    re.S,
)
# `int *foo(...)`, `static long long solver(...)`, `int * constr(char *patn)`
DECLARATOR_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*\([^;{]*$", re.S)
BODY_ONLY_KEYWORDS = ("Inv", "Assert", "Given", "where", "Branch")


def normalize(text: str) -> str:
    """Collapse formatting so only tokens remain significant."""

    return " ".join(text.split())


def _strip_comments(text: str) -> str:
    """Drop every comment: annotations first, then ordinary C comments.

    Ordinary comments matter because prose routinely contains text that looks
    like a declarator -- a file header reading ``Codeforces 32/A - Reconnaissance
    (rating 800)`` otherwise wins over the real signature below it.
    """

    text = ANNOTATION_RE.sub(" ", text)
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", "", text)


def _enclosing_function(source: str, comment_start: int) -> str:
    """Return the function whose signature precedes this annotation block."""

    head = _strip_comments(source[:comment_start])
    head = head[head.rfind(";") + 1 :]
    head = head[head.rfind("}") + 1 :]
    match = DECLARATOR_RE.search(head)
    return match.group(1) if match else "<unknown>"


def extract_c(source: str) -> dict[str, Any]:
    extern: dict[str, str] = {}
    imports: dict[str, str] = {}
    specs: dict[str, str] = {}

    for match in ANNOTATION_RE.finditer(source):
        body = match.group(1)
        stripped = body.strip()

        if stripped.startswith("Extern Coq"):
            for entry in EXTERN_ENTRY_RE.finditer(stripped[len("Extern Coq") :]):
                extern[normalize(entry.group(1))] = normalize(entry.group(2))
            continue

        importing = IMPORT_RE.search(stripped)
        if importing:
            for module in importing.group(1).replace(",", " ").split():
                imports[normalize(module)] = normalize(module)
            continue

        if stripped.startswith(BODY_ONLY_KEYWORDS):
            continue
        if "Require" not in stripped and "Ensure" not in stripped:
            continue

        head = SPEC_HEAD_RE.match(stripped)
        spec_name = (head.group("name") if head else None) or "<default>"
        function = _enclosing_function(source, match.start())
        specs[f"{function}::{spec_name}"] = normalize(stripped)

    return {"extern_coq": extern, "import_coq": imports, "specs": specs}


def extract_lib(text: str) -> dict[str, dict[str, str]]:
    """Return the lib surface, split by what a key means.

    ``parse_lib_declarations`` reports imports as declarations whose ``name`` is
    the whole ``Require Import ...`` line, so they are separated here: an import
    is keyed by the module it names, a definition by its identifier.
    """

    declarations: dict[str, str] = {}
    imports: dict[str, str] = {}
    for declaration in parse_lib_declarations(text):
        name = str(declaration["name"])
        digest = coq_token_digest(str(declaration["block"]))
        if str(declaration.get("kind")) == "Import":
            module = normalize(name).rstrip(".").split()[-1]
            imports[module] = digest
        else:
            declarations[name] = digest
    return {"declarations": declarations, "imports": imports}


def extract_spec_surface(c_file: Path, lib_file: Path | None) -> dict[str, Any]:
    """Controller entry point: extract the surface a frozen run must preserve."""

    return extract(c_file, lib_file)


def spec_freeze_findings(
    record: dict[str, Any] | None,
    *,
    c_file: Path,
    lib_file: Path | None,
) -> list[dict[str, str]]:
    """Controller entry point: compare the current surface with the baseline.

    ``record`` is ``state["spec_freeze"]``; ``None`` means the run did not freeze
    anything, so there is nothing to compare.
    """

    if not record:
        return []
    return compare(
        record["baseline"],
        extract(c_file, lib_file),
        list(record.get("functions") or []) or None,
    )


def extract(c_file: Path, lib_file: Path | None) -> dict[str, Any]:
    surface = extract_c(c_file.read_text(encoding="utf-8"))
    surface["lib"] = (
        extract_lib(lib_file.read_text(encoding="utf-8"))
        if lib_file is not None and lib_file.is_file()
        else {}
    )
    return surface


def compare(
    baseline: dict[str, Any],
    current: dict[str, Any],
    frozen_functions: list[str] | None,
) -> list[dict[str, str]]:
    """Report baseline entries that were removed or altered.

    ``frozen_functions`` restricts the ``specs`` section; ``None`` freezes every
    function.  The shared surface -- ``extern_coq``, ``import_coq`` and ``lib`` --
    is always compared, because a frozen spec's meaning depends on it.
    """

    findings: list[dict[str, str]] = []
    sections = {
        "extern_coq": baseline.get("extern_coq", {}),
        "import_coq": baseline.get("import_coq", {}),
        "specs": baseline.get("specs", {}),
        "lib.declarations": baseline.get("lib", {}).get("declarations", {}),
        "lib.imports": baseline.get("lib", {}).get("imports", {}),
    }
    for section, entries in sections.items():
        for key, before in entries.items():
            if (
                section == "specs"
                and frozen_functions is not None
                and key.split("::", 1)[0] not in frozen_functions
            ):
                continue
            scope: Any = current
            for part in section.split("."):
                scope = scope.get(part, {}) if isinstance(scope, dict) else {}
            after = scope.get(key) if isinstance(scope, dict) else None
            if after is None:
                findings.append(
                    {"section": section, "entry": key, "kind": "removed"}
                )
            elif after != before:
                findings.append(
                    {
                        "section": section,
                        "entry": key,
                        "kind": "changed",
                        "baseline": before,
                        "current": after,
                    }
                )
    return findings


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c-file", required=True, type=Path)
    parser.add_argument("--lib-file", type=Path)
    parser.add_argument("--baseline", type=Path, help="compare against this extraction")
    parser.add_argument(
        "--freeze-spec",
        help="comma-separated function names whose specs are frozen; omit to freeze all",
    )
    parser.add_argument("--out", type=Path, help="write the extraction here")
    args = parser.parse_args(argv)

    surface = extract(args.c_file, args.lib_file)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(surface, indent=2, sort_keys=True), encoding="utf-8")

    if args.baseline:
        frozen = (
            [name.strip() for name in args.freeze_spec.split(",") if name.strip()]
            if args.freeze_spec
            else None
        )
        findings = compare(
            json.loads(args.baseline.read_text(encoding="utf-8")), surface, frozen
        )
        print(json.dumps({"findings": findings}, indent=2, sort_keys=True))
        return 1 if findings else 0

    print(json.dumps(surface, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
