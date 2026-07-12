#!/usr/bin/env python3
"""Fixed Coq command tooling for the verification worktree pipeline.

This module is the only active place that constructs Coq command arguments.
It runs ``coqc`` for batch checks and ``coqtop -batch`` for debug scripts with
one fixed set of ``-R`` flags.  It mirrors source ``.v`` files into a build
workspace first, so Coq side products stay out of formal worktrees.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any, Iterable


FIXED_R_MAPPINGS: tuple[tuple[str, str], ...] = (
    ("SeparationLogic/SeparationLogic", "SimpleC.SL"),
    ("SeparationLogic/unifysl", "Logic"),
    ("SeparationLogic/sets", "SetsClass"),
    ("SeparationLogic/compcert_lib", "compcert.lib"),
    ("SeparationLogic/auxlibs", "AUXLib"),
    ("SeparationLogic/examples", "SimpleC.EE"),
    ("SeparationLogic/stdlib", "SimpleC.StdLib"),
    ("SeparationLogic/StrategyLib", "SimpleC.StrategyLib"),
    ("SeparationLogic/Common", "SimpleC.Common"),
    ("SeparationLogic/fixedpoints", "FP"),
    ("SeparationLogic/MonadLib", "MonadLib"),
    ("SeparationLogic/listlib", "ListLib"),
    ("SeparationLogic/MaxMinLib", "MaxMinLib"),
    ("SeparationLogic/GraphLib", "GraphLib"),
    ("SeparationLogic/SumLib", "SumLib"),
)
FIXED_COQC = "coqc"
FIXED_COQTOP = "coqtop"
DIAGNOSTIC_RE = re.compile(
    r'File "(?P<file>[^"]+)", line (?P<line>\d+), characters (?P<characters>[0-9-]+):\s*\n(?P<message>.*?)(?=\nFile "|\Z)',
    re.DOTALL,
)
COMMENT_RE = re.compile(r"\(\*.*?\*\)", re.DOTALL)
STANDARD_PREFIXES = (
    "Coq",
    "Ltac2",
)


def fixed_flags() -> list[str]:
    flags: list[str] = []
    for physical, logical in FIXED_R_MAPPINGS:
        flags.extend(["-R", physical, logical])
    return flags


def fixed_flags_hash() -> str:
    return hashlib.sha256(json.dumps(fixed_flags(), separators=(",", ":")).encode("utf-8")).hexdigest()


def make_coqc_argv(target_file: str | Path) -> list[str]:
    target = Path(str(target_file)).as_posix()
    if " -o " in target or target == "-o":
        raise ValueError("coqc -o is forbidden")
    return [FIXED_COQC, "-q", *fixed_flags(), target]


def make_coqtop_argv(debug_script: str | Path) -> list[str]:
    script = Path(str(debug_script)).as_posix()
    return [FIXED_COQTOP, "-q", "-batch", *fixed_flags(), "-l", script]


def text_sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tail(text: str, limit: int = 8000) -> str:
    if len(text) <= limit:
        return text
    return text[-limit:]


def extract_first_coq_diagnostic(output: str) -> dict[str, Any] | None:
    match = DIAGNOSTIC_RE.search(output)
    if not match:
        return None
    return {
        "file": match.group("file"),
        "line": int(match.group("line")),
        "characters": match.group("characters"),
        "message": match.group("message").strip(),
    }


def coq_version() -> str:
    try:
        proc = subprocess.run(
            [FIXED_COQC, "-v"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
    except FileNotFoundError:
        return "coqc-not-found"
    output = "\n".join(part for part in [proc.stdout, proc.stderr] if part).strip()
    return output.splitlines()[0] if output else "unknown"


def coqc_transient_retries() -> int:
    raw = os.environ.get("COQC_TRANSIENT_RETRIES", "2").strip()
    try:
        value = int(raw)
    except ValueError:
        return 2
    return max(0, value)


def infer_main_workspace_root(round_or_case_path: Path) -> Path:
    resolved = round_or_case_path.expanduser().resolve()
    candidate_self = resolved if resolved.is_dir() else resolved.parent
    if (candidate_self / "dune-project").is_file() or (candidate_self / "SeparationLogic").is_dir():
        return candidate_self.resolve()
    parts = resolved.parts
    if "worktrees" in parts:
        index = parts.index("worktrees")
        candidate = Path(*parts[:index])
        if (candidate / "dune-project").is_file() or (candidate / "SeparationLogic").is_dir():
            return candidate.resolve()
    for parent in (resolved if resolved.is_dir() else resolved.parent).parents:
        if "worktrees" in parent.parts:
            continue
        if (parent / "dune-project").is_file() or (parent / "SeparationLogic").is_dir():
            return parent.resolve()
    raise ValueError(f"cannot infer main worktree root from {round_or_case_path}")


def relative_to_workspace(path: Path, workspace_root: Path) -> Path:
    return path.expanduser().resolve().relative_to(workspace_root.expanduser().resolve())


def infer_case_config(workspace_root: Path, case_dir: Path) -> dict[str, str]:
    workspace_root = workspace_root.expanduser().resolve()
    case_dir = case_dir.expanduser().resolve()
    rel = relative_to_workspace(case_dir, workspace_root)
    parts = rel.parts
    if "SeparationLogic" in parts and "examples" in parts:
        sep_index = parts.index("SeparationLogic")
        theory_parts = parts[sep_index + 2 :] if sep_index + 1 < len(parts) and parts[sep_index + 1] == "examples" else (case_dir.name,)
    else:
        theory_parts = (case_dir.name,)
    case_name = theory_parts[-1]
    rel_posix = rel.as_posix()
    return {
        "case_name": case_name,
        "active_theory": "SimpleC.EE." + ".".join(theory_parts),
        "physical_path": rel_posix,
        "check_file": f"{rel_posix}/{case_name}_goal_check.v",
        "proof_manual_file": f"{rel_posix}/{case_name}_proof_manual.v",
    }


def target_file_for_kind(manual_rel: Path, target_kind: str) -> Path:
    if target_kind == "proof_manual":
        return manual_rel
    if target_kind == "check":
        if manual_rel.name.endswith("_proof_manual.v"):
            return manual_rel.with_name(manual_rel.name[: -len("_proof_manual.v")] + "_goal_check.v")
        raise ValueError(f"cannot infer check file from {manual_rel}")
    if target_kind == "group-check":
        if manual_rel.name.endswith("_proof_manual.v"):
            case_name = manual_rel.name[: -len("_proof_manual.v")]
            return Path(".coq_group_checks") / f"{case_name}_group_check.v"
        raise ValueError(f"cannot infer group check file from {manual_rel}")
    raise ValueError(f"unsupported target kind: {target_kind}")


def _copy_if_changed(src: Path, dest: Path) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists() and dest.stat().st_size == src.stat().st_size:
        try:
            if file_sha256(dest) == file_sha256(src):
                return
        except OSError:
            pass
    shutil.copy2(src, dest)


def mirror_sources(workspace_root: Path, build_workspace: Path, extra_relatives: Iterable[Path] = ()) -> list[str]:
    workspace_root = workspace_root.expanduser().resolve()
    build_workspace = build_workspace.expanduser().resolve()
    copied: list[str] = []
    roots = [Path(physical) for physical, _logical in FIXED_R_MAPPINGS]
    for root in roots:
        (build_workspace / root).mkdir(parents=True, exist_ok=True)
        src_root = workspace_root / root
        if not src_root.is_dir():
            continue
        for src in src_root.rglob("*.v"):
            rel = src.relative_to(workspace_root)
            _copy_if_changed(src, build_workspace / rel)
            copied.append(rel.as_posix())
    for rel in extra_relatives:
        src = workspace_root / rel
        if src.is_file():
            _copy_if_changed(src, build_workspace / rel)
            copied.append(rel.as_posix())
    return sorted(set(copied))


def _strip_comments(text: str) -> str:
    previous = None
    current = text
    while previous != current:
        previous = current
        current = COMMENT_RE.sub("", current)
    return current


def _required_modules(text: str) -> list[str]:
    result: list[str] = []
    tokens = _strip_comments(text).replace("\n", " ").split()
    index = 0
    while index < len(tokens):
        prefix: str | None = None
        if tokens[index] == "From" and index + 2 < len(tokens) and tokens[index + 2] == "Require":
            prefix = tokens[index + 1].strip(".")
            index += 3
        elif tokens[index] == "Require":
            index += 1
        else:
            index += 1
            continue
        while index < len(tokens) and tokens[index] in {"Import", "Export"}:
            index += 1
        while index < len(tokens):
            token = tokens[index].strip()
            index += 1
            done = token.endswith(".")
            token = token.rstrip(".")
            if token and token not in {"as", "using"}:
                module = f"{prefix}.{token}" if prefix else token
                if module and module not in result:
                    result.append(module)
            if done:
                break
    return result


def logical_module_to_relative(module: str) -> Path | None:
    if module.startswith(STANDARD_PREFIXES):
        return None
    matches: list[tuple[int, Path, str]] = []
    for physical, logical in FIXED_R_MAPPINGS:
        if module == logical:
            matches.append((len(logical), Path(physical + ".v"), logical))
        elif module.startswith(logical + "."):
            suffix = module[len(logical) + 1 :].replace(".", "/") + ".v"
            matches.append((len(logical), Path(physical) / suffix, logical))
    if not matches:
        return None
    matches.sort(reverse=True, key=lambda item: item[0])
    return matches[0][1]


def relative_to_logical_module(rel: Path) -> str | None:
    rel = Path(rel.as_posix())
    matches: list[tuple[int, str]] = []
    for physical, logical in FIXED_R_MAPPINGS:
        physical_path = Path(physical)
        try:
            suffix = rel.relative_to(physical_path)
        except ValueError:
            continue
        if suffix.suffix != ".v":
            continue
        module_suffix = ".".join(suffix.with_suffix("").parts)
        module = f"{logical}.{module_suffix}" if module_suffix else logical
        matches.append((len(physical_path.parts), module))
    if not matches:
        return None
    matches.sort(reverse=True, key=lambda item: item[0])
    return matches[0][1]


def _local_alias_wrapper(build_workspace: Path, current_rel: Path, module: str) -> Path | None:
    if "." in module or module.startswith(STANDARD_PREFIXES):
        return None
    sibling = current_rel.parent / f"{module}.v"
    if not (build_workspace / sibling).is_file():
        return None
    logical = relative_to_logical_module(sibling)
    if logical is None:
        return None
    wrapper = Path(f"{module}.v")
    wrapper_path = build_workspace / wrapper
    wrapper_text = f"Require Export {logical}.\n"
    if not wrapper_path.exists() or wrapper_path.read_text(encoding="utf-8") != wrapper_text:
        wrapper_path.write_text(wrapper_text, encoding="utf-8")
    return wrapper


def _run(
    argv: list[str],
    *,
    cwd: Path,
    timeout_seconds: int | None = None,
    sigkill_retries: int = 0,
) -> dict[str, Any]:
    started = time.time()
    attempts = 0
    retry_returncodes: list[int] = []
    while True:
        attempts += 1
        try:
            proc = subprocess.run(
                argv,
                cwd=cwd,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout_seconds,
                check=False,
            )
            stdout = proc.stdout
            stderr = proc.stderr
            returncode = proc.returncode
        except subprocess.TimeoutExpired as exc:
            stdout = exc.stdout if isinstance(exc.stdout, str) else ""
            stderr = exc.stderr if isinstance(exc.stderr, str) else ""
            stderr += f"\nCoq command timed out after {timeout_seconds} seconds."
            returncode = 124
        except FileNotFoundError as exc:
            stdout = ""
            stderr = str(exc)
            returncode = 127
        if returncode == -9 and attempts <= sigkill_retries:
            retry_returncodes.append(returncode)
            continue
        break
    combined = "\n".join(part for part in [stdout, stderr] if part)
    return {
        "argv": argv,
        "cwd": str(cwd),
        "returncode": returncode,
        "attempts": attempts,
        "sigkill_retries_configured": sigkill_retries,
        "transient_retry_returncodes": retry_returncodes,
        "stdout_tail": tail(stdout),
        "stderr_tail": tail(stderr),
        "first_diagnostic": extract_first_coq_diagnostic(combined),
        "elapsed_seconds": round(time.time() - started, 3),
    }


def _compile_order(build_workspace: Path, target_rel: Path) -> tuple[list[Path], list[str]]:
    ordered: list[Path] = []
    errors: list[str] = []
    visiting: set[Path] = set()
    visited: set[Path] = set()

    def visit(rel: Path) -> None:
        rel = Path(rel.as_posix())
        if rel in visited:
            return
        if rel in visiting:
            errors.append(f"dependency cycle involving {rel.as_posix()}")
            return
        path = build_workspace / rel
        if not path.is_file():
            errors.append(f"missing Coq source in build workspace: {rel.as_posix()}")
            return
        visiting.add(rel)
        for module in _required_modules(path.read_text(encoding="utf-8")):
            dep = logical_module_to_relative(module)
            if dep is None:
                dep = _local_alias_wrapper(build_workspace, rel, module)
            if dep is not None and (build_workspace / dep).is_file():
                visit(dep)
        visiting.remove(rel)
        visited.add(rel)
        ordered.append(rel)

    visit(target_rel)
    return ordered, errors


def source_digests(build_workspace: Path, rels: Iterable[Path]) -> dict[str, str]:
    digests: dict[str, str] = {}
    for rel in rels:
        path = build_workspace / rel
        if path.is_file():
            digests[rel.as_posix()] = file_sha256(path)
    return digests


def _write_group_check_wrapper(build_workspace: Path, target_rel: Path, group_check: dict[str, Any]) -> None:
    case_theory = str(group_check.get("case_theory") or "").strip()
    require_modules = [str(item).strip() for item in group_check.get("require_modules", []) if str(item).strip()]
    assigned = [str(item).strip() for item in group_check.get("assigned_witnesses", []) if str(item).strip()]
    if not case_theory:
        raise ValueError("group-check requires case_theory")
    if not require_modules:
        raise ValueError("group-check requires require_modules")
    if not assigned:
        raise ValueError("group-check requires assigned_witnesses")
    lines = [
        "(* Generated build-workspace-only group check wrapper. *)",
        f"From {case_theory} Require Import {' '.join(require_modules)}.",
        "",
    ]
    lines.extend(f"Check {name}." for name in assigned)
    path = build_workspace / target_rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run_coqc_check(
    *,
    workspace_root: Path,
    build_workspace: Path,
    target_file: Path,
    target_kind: str,
    source_goal_version: str | None,
    timeout_seconds: int | None = None,
    compile_dependencies: bool = True,
    group_check: dict[str, Any] | None = None,
) -> dict[str, Any]:
    started = time.time()
    workspace_root = workspace_root.expanduser().resolve()
    build_workspace = build_workspace.expanduser().resolve()
    target_rel = Path(target_file.as_posix())
    build_workspace.mkdir(parents=True, exist_ok=True)
    mirrored = mirror_sources(workspace_root, build_workspace, [target_rel])
    group_check_errors: list[str] = []
    if target_kind == "group-check":
        try:
            _write_group_check_wrapper(build_workspace, target_rel, group_check or {})
        except ValueError as exc:
            group_check_errors.append(str(exc))
    order, dependency_errors = _compile_order(build_workspace, target_rel)
    if not compile_dependencies:
        order = [target_rel]
    target_argv = make_coqc_argv(target_rel)
    sigkill_retries = coqc_transient_retries()
    evidence: dict[str, Any] = {
        "schema_version": "qcp-coqc-check-evidence/v1",
        "status": "pending",
        "tool": "coqc",
        "kind": "coqc_check",
        "argv": target_argv,
        "cwd": str(build_workspace),
        "coq_version": coq_version(),
        "fixed_flags_hash": fixed_flags_hash(),
        "target_file": target_rel.as_posix(),
        "target_kind": target_kind,
        "source_goal_version": source_goal_version,
        "source_digests": source_digests(build_workspace, order or [target_rel]),
        "mirrored_sources_count": len(mirrored),
        "coqc_transient_retry_policy": {
            "env": "COQC_TRANSIENT_RETRIES",
            "configured_retries": sigkill_retries,
            "retry_returncode": -9,
            "retry_signal": "SIGKILL",
        },
        "build_workspace": str(build_workspace),
        "dependency_order": [rel.as_posix() for rel in order],
        "dependency_errors": dependency_errors + group_check_errors,
        "executed_argvs": [],
        "returncode": None,
        "stdout_tail": "",
        "stderr_tail": "",
        "first_diagnostic": None,
    }
    if dependency_errors or group_check_errors:
        evidence["status"] = "failed"
        evidence["stderr_tail"] = "\n".join(dependency_errors + group_check_errors)
        return evidence

    for rel in order:
        argv = make_coqc_argv(rel)
        result = _run(
            argv,
            cwd=build_workspace,
            timeout_seconds=timeout_seconds,
            sigkill_retries=sigkill_retries,
        )
        evidence["executed_argvs"].append(argv)
        if result["returncode"] != 0:
            evidence.update(
                {
                    "status": "failed",
                    "failed_target_file": rel.as_posix(),
                    "returncode": result["returncode"],
                    "stdout_tail": result["stdout_tail"],
                    "stderr_tail": result["stderr_tail"],
                    "first_diagnostic": result["first_diagnostic"],
                    "elapsed_seconds": result["elapsed_seconds"],
                }
            )
            return evidence
    evidence.update(
        {
            "status": "passed",
            "returncode": 0,
            "failed_target_file": None,
            "elapsed_seconds": round(time.time() - started, 3),
        }
    )
    return evidence


def run_coqtop_debug(
    *,
    workspace_root: Path,
    build_workspace: Path,
    debug_script: Path,
    source_goal_version: str | None,
    timeout_seconds: int | None = None,
) -> dict[str, Any]:
    workspace_root = workspace_root.expanduser().resolve()
    build_workspace = build_workspace.expanduser().resolve()
    debug_rel = Path(debug_script.as_posix())
    build_workspace.mkdir(parents=True, exist_ok=True)
    mirror_sources(workspace_root, build_workspace, [debug_rel])
    argv = make_coqtop_argv(build_workspace / debug_rel)
    result = _run(argv, cwd=build_workspace, timeout_seconds=timeout_seconds)
    return {
        "schema_version": "qcp-coqtop-debug-evidence/v1",
        "status": "passed" if result["returncode"] == 0 else "failed",
        "tool": "coqtop",
        "kind": "coqtop_debug",
        "argv": argv,
        "cwd": str(build_workspace),
        "coq_version": coq_version(),
        "fixed_flags_hash": fixed_flags_hash(),
        "debug_script": debug_rel.as_posix(),
        "source_goal_version": source_goal_version,
        "source_digests": source_digests(build_workspace, [debug_rel]),
        **result,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Run fixed-argv Coq tooling and emit JSON evidence.")
    sub = parser.add_subparsers(dest="command", required=True)

    check = sub.add_parser("check", help="Run fixed coqc check in an isolated build workspace")
    check.add_argument("--workspace-root", required=True)
    check.add_argument("--build-workspace", required=True)
    check.add_argument("--target-file", required=True)
    check.add_argument("--target-kind", choices=["proof_manual", "case_lib", "check", "group-check"], required=True)
    check.add_argument("--source-goal-version", required=True)
    check.add_argument("--timeout-seconds", type=int, default=None)
    check.add_argument("--no-deps", action="store_true")
    check.add_argument("--group-check-case-theory", default=None)
    check.add_argument("--group-check-require", action="append", default=[])
    check.add_argument("--assigned-witness", action="append", default=[])

    debug = sub.add_parser("debug", help="Run fixed coqtop -batch debug script")
    debug.add_argument("--workspace-root", required=True)
    debug.add_argument("--build-workspace", required=True)
    debug.add_argument("--debug-script", required=True)
    debug.add_argument("--source-goal-version", required=True)
    debug.add_argument("--timeout-seconds", type=int, default=None)

    args = parser.parse_args()
    if args.command == "check":
        evidence = run_coqc_check(
            workspace_root=Path(args.workspace_root),
            build_workspace=Path(args.build_workspace),
            target_file=Path(args.target_file),
            target_kind=args.target_kind,
            source_goal_version=args.source_goal_version,
            timeout_seconds=args.timeout_seconds,
            compile_dependencies=not args.no_deps,
            group_check={
                "case_theory": args.group_check_case_theory,
                "require_modules": args.group_check_require,
                "assigned_witnesses": args.assigned_witness,
            }
            if args.target_kind == "group-check"
            else None,
        )
    elif args.command == "debug":
        evidence = run_coqtop_debug(
            workspace_root=Path(args.workspace_root),
            build_workspace=Path(args.build_workspace),
            debug_script=Path(args.debug_script),
            source_goal_version=args.source_goal_version,
            timeout_seconds=args.timeout_seconds,
        )
    print(json.dumps(evidence, indent=2, ensure_ascii=True))
    return 0 if evidence.get("status") == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
