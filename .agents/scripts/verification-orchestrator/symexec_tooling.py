#!/usr/bin/env python3
"""Internal canonical symbolic-execution implementation used by controller.py.

The controller supplies the repository root, target C file, and output root.
This module selects the platform driver and constructs the required include,
SLP, logic, generated-file, input-file, and cwd arguments.
"""

# ruff: noqa: E402 -- this internal module resolves vc-proving path helpers at runtime.

from __future__ import annotations

import json
import math
import os
import platform
import re
import shutil
import stat
import sys
import time
from collections.abc import Callable, Mapping
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
VC_PROVING_SCRIPTS = SCRIPT_DIR.parent / "vc-proving"
sys.path.insert(0, str(VC_PROVING_SCRIPTS))

from file_integrity import sha256_bytes, sha256_text
from path_utils import fixed_path_under
from process_adapter import run_bounded_process
from proof_manual_utils import (
    ensure_unique_lemma_names,
    generated_artifact_module_spellings,
    goal_definition_hashes,
    goal_semantic_hash_for_lemma,
    lemma_statement_hash,
    lemma_target_symbol,
    parse_manual_file,
    partition_manual_lemmas,
    required_rocq_modules,
)
GENERATED_FILE_KEYS = (
    "goal_file",
    "proof_auto_file",
    "proof_manual_file",
    "goal_check_file",
)
MANDATORY_GENERATED_FILE_KEYS = (
    "goal_file",
    "proof_auto_file",
    "goal_check_file",
)
QUOTED_INCLUDE_RE = re.compile(
    r'^\s*#\s*include\s*"(?P<path>[^"\r\n]+)"', re.MULTILINE
)
ANNOTATION_BLOCK_RE = re.compile(r"/\*@(?P<body>.*?)\*/", re.DOTALL)
STRATEGY_INCLUDE_RE = re.compile(
    r'\binclude\s+strategies\s+"(?P<path>[^"\r\n]+)"'
)
ROCQ_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
SYMEXEC_TIMEOUT_SECONDS = 600
STRATEGY_PROFILE_BY_COLLECTION = {
    "Applications_human": "QCP_demos_human",
    "LLM_bench": "QCP_demos_LLM",
    "QCP_demos_LLM": "QCP_demos_LLM",
    "QCP_demos_human": "QCP_demos_human",
    "QCP_demos_tutorial": "QCP_demos_tutorial",
}
STRATEGY_PROFILE_BY_TARGET_PREFIX: dict[tuple[str, ...], str | None] = {
    ("Applications_human", "convex_hull"): "QCP_demos_LLM",
    ("Applications_human", "fme_ge_gmp"): None,
}
SYMEXEC_FLAGS_BY_TARGET_PREFIX: dict[tuple[str, ...], tuple[str, ...]] = {
    ("LLM_bench", "Algorithms", "convex_hull_float"): ("--float-finite-vc",),
}


def _tail(text: str, limit: int = 8000) -> str:
    return text if len(text) <= limit else text[-limit:]


def _normalize_generated_freshness_text(text: str, root: Path) -> str:
    """Mask only the controller-selected output root in generated Coq text."""

    owner = root.expanduser().resolve()
    variants = {
        str(owner),
        str(owner).replace("\\", "/"),
        str(owner).replace("/", "\\"),
    }
    normalized = text
    for item in sorted(variants, key=len, reverse=True):
        normalized = normalized.replace(item, "$QCP_OUTPUT_ROOT")
    return normalized


def _fixed_artifact_leaf(
    *,
    root: Path,
    relative: str,
    label: str,
) -> Path:
    """Return one confined lexical leaf without resolving that leaf itself."""

    owner_input = Path(os.path.abspath(os.fspath(root.expanduser())))
    relative_path = Path(relative)
    if (
        relative_path.is_absolute()
        or ".." in relative_path.parts
        or not relative_path.name
    ):
        raise ValueError(f"{label} must be a repository-relative file: {relative}")
    try:
        owner = fixed_path_under(owner_input, owner_input, label=f"{label} root")
        parent = fixed_path_under(
            (owner / relative_path).parent,
            owner,
            label=f"{label} parent",
        )
    except SystemExit as exc:
        raise ValueError(str(exc)) from exc
    return parent / relative_path.name


def _metadata_is_link_like(metadata: os.stat_result) -> bool:
    return stat.S_ISLNK(metadata.st_mode) or bool(
        int(getattr(metadata, "st_file_attributes", 0) or 0)
        & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400)
    )


def _stable_metadata(metadata: os.stat_result) -> tuple[int, int, int, int]:
    return (
        int(metadata.st_dev),
        int(metadata.st_ino),
        int(metadata.st_size),
        int(metadata.st_mtime_ns),
    )


def _lexical_regular_file_snapshot(
    *,
    root: Path,
    relative: str,
    label: str,
) -> dict[str, Any]:
    """Read one stable non-link regular leaf without following a replacement.

    ``lstat`` rejects directories, FIFOs, and link/reparse leaves before open;
    ``O_NONBLOCK`` ensures a FIFO swapped in during the race cannot stall the
    controller. The descriptor and a second lexical stat must identify the
    same unchanged regular file before any bytes are accepted.
    """

    try:
        path = _fixed_artifact_leaf(root=root, relative=relative, label=label)
    except ValueError as exc:
        return {
            "path": Path(os.path.abspath(os.fspath(root.expanduser()))) / relative,
            "state": "invalid",
            "message": str(exc),
        }
    try:
        before = os.lstat(path)
    except FileNotFoundError:
        return {"path": path, "state": "missing"}
    except OSError as exc:
        return {"path": path, "state": "unreadable", "message": str(exc)}
    if _metadata_is_link_like(before) or not stat.S_ISREG(before.st_mode):
        return {
            "path": path,
            "state": "nonregular",
            "message": f"{label} is not a non-link regular file: {relative}",
        }

    flags = os.O_RDONLY
    for name in ("O_BINARY", "O_CLOEXEC", "O_NOFOLLOW", "O_NONBLOCK"):
        flags |= int(getattr(os, name, 0) or 0)
    descriptor: int | None = None
    try:
        descriptor = os.open(path, flags)
        opened = os.fstat(descriptor)
        if (
            not stat.S_ISREG(opened.st_mode)
            or (opened.st_dev, opened.st_ino) != (before.st_dev, before.st_ino)
        ):
            raise OSError("generated file changed to a non-regular or different leaf")
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        after_open = os.fstat(descriptor)
        after_lexical = os.lstat(path)
        if (
            _metadata_is_link_like(after_lexical)
            or not stat.S_ISREG(after_lexical.st_mode)
            or _stable_metadata(before) != _stable_metadata(opened)
            or _stable_metadata(opened) != _stable_metadata(after_open)
            or _stable_metadata(after_open) != _stable_metadata(after_lexical)
        ):
            raise OSError("generated file changed while it was being read")
    except OSError as exc:
        return {"path": path, "state": "unreadable", "message": str(exc)}
    finally:
        if descriptor is not None:
            os.close(descriptor)

    payload = b"".join(chunks)
    return {
        "path": path,
        "state": "present",
        "size": len(payload),
        "sha256": sha256_bytes(payload),
        "data": payload,
        "identity": (int(after_open.st_dev), int(after_open.st_ino)),
    }


def _snapshot_text(snapshot: Mapping[str, Any], *, label: str) -> str:
    if snapshot.get("state") != "present" or not isinstance(
        snapshot.get("data"), bytes
    ):
        raise ValueError(f"{label} is not a readable non-link regular file")
    try:
        return snapshot["data"].decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError(f"{label} is not valid UTF-8: {exc}") from exc


def _normalized_generated_digest(path: Path, root: Path) -> str:
    owner = Path(os.path.abspath(os.fspath(root.expanduser())))
    try:
        relative = path.relative_to(owner)
    except ValueError as exc:
        raise ValueError(f"generated freshness path escaped its root: {path}") from exc
    snapshot = _lexical_regular_file_snapshot(
        root=owner,
        relative=relative.as_posix(),
        label="generated freshness file",
    )
    normalized = _normalize_generated_freshness_text(
        _snapshot_text(snapshot, label="generated freshness file"), root
    )
    return sha256_text(normalized)


def source_goal_version_at_root(
    *,
    root: Path,
    target_files: dict[str, str],
    formal_case_lib_root: Path | None = None,
) -> dict[str, Any]:
    """Derive the canonical source-goal version from any controller-owned root."""

    owner = Path(os.path.abspath(os.fspath(root.expanduser())))
    generated: list[dict[str, Any]] = []
    generated_snapshots: dict[str, dict[str, Any]] = {}
    for key in GENERATED_FILE_KEYS:
        relative = str(target_files[key])
        snapshot = _lexical_regular_file_snapshot(
            root=owner,
            relative=relative,
            label=f"source-goal {key}",
        )
        artifact_state = str(snapshot.get("state") or "invalid")
        if artifact_state not in {"present", "missing"}:
            raise ValueError(
                str(snapshot.get("message") or f"source-goal {key} is invalid")
            )
        generated_snapshots[key] = snapshot
        generated.append(
            {
                "relative_path": relative,
                "role": key,
                "state": artifact_state,
                "sha256": snapshot.get("sha256"),
            }
        )
    manual_snapshot = generated_snapshots["proof_manual_file"]
    goal_snapshot = generated_snapshots["goal_file"]
    formal_owner = (
        Path(os.path.abspath(os.fspath(formal_case_lib_root.expanduser())))
        if formal_case_lib_root is not None
        else owner
    )
    formal_case_lib_snapshot = _lexical_regular_file_snapshot(
        root=formal_owner,
        relative=str(target_files["formal_case_lib"]),
        label="source-goal formal_case_lib",
    )
    formal_case_lib_state = str(
        formal_case_lib_snapshot.get("state") or "invalid"
    )
    if formal_case_lib_state not in {"present", "missing"}:
        raise ValueError(
            str(
                formal_case_lib_snapshot.get("message")
                or "source-goal formal_case_lib is invalid"
            )
        )
    normalized_goal_text = _normalize_generated_freshness_text(
        _snapshot_text(goal_snapshot, label="source-goal goal_file"), owner
    )
    formal_case_lib_text = (
        _snapshot_text(
            formal_case_lib_snapshot,
            label="source-goal formal_case_lib",
        )
        if formal_case_lib_state == "present"
        else ""
    )
    goal_hashes = goal_definition_hashes(
        normalized_goal_text,
        formal_case_lib_text=formal_case_lib_text,
    )
    if manual_snapshot["state"] == "present":
        _prelude, lemmas = parse_manual_file(
            _snapshot_text(manual_snapshot, label="source-goal proof_manual_file")
        )
    else:
        lemmas = []
    ensure_unique_lemma_names(lemmas)
    witness_lemmas, split_goal_lemmas = partition_manual_lemmas(lemmas)
    witnesses: list[dict[str, str]] = []
    for lemma in witness_lemmas:
        name = str(lemma["name"])
        target_symbol = lemma_target_symbol(lemma)
        semantic_hash = goal_semantic_hash_for_lemma(lemma, goal_hashes)
        witnesses.append(
            {
                "name": name,
                "statement_hash": lemma_statement_hash(lemma),
                "goal_symbol": target_symbol or "",
                "goal_definition_hash": semantic_hash,
            }
        )
    split_goals: dict[str, list[dict[str, str]]] = {
        str(witness["name"]): [] for witness in witnesses
    }
    for witness in witnesses:
        witness_name = str(witness["name"])
        for lemma in split_goal_lemmas[witness_name]:
            name = str(lemma["name"])
            target_symbol = lemma_target_symbol(lemma)
            semantic_hash = goal_semantic_hash_for_lemma(lemma, goal_hashes)
            split_goals[witness_name].append(
                {
                    "name": name,
                    "statement_hash": lemma_statement_hash(lemma),
                    "goal_symbol": target_symbol or "",
                    "goal_definition_hash": semantic_hash,
                }
            )
    payload = {
        "generated_files": generated,
        "target_witnesses": [item["name"] for item in witnesses],
        "witness_statement_hashes": {
            item["name"]: item["statement_hash"] for item in witnesses
        },
        "witness_goal_definition_hashes": {
            item["name"]: item["goal_definition_hash"] for item in witnesses
        },
        "split_goals": split_goals,
    }
    return {
        "digest": sha256_text(
            json.dumps(payload, sort_keys=True, separators=(",", ":"))
        ),
        **payload,
    }


def clean_output_freshness(
    *,
    main_root: Path,
    target_c_file: Path,
    target_files: dict[str, str],
    reference_root: Path,
    refresh_root: Path,
    manual_mode: str,
    symexec_runner: Callable[..., dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Replay canonical symexec and compare exact raw or proved-manual obligations."""

    if manual_mode not in {"raw", "proved"}:
        raise ValueError("manual_mode must be raw or proved")
    refresh = fixed_path_under(
        refresh_root,
        main_root,
        label="clean symbolic-execution replay directory",
    )
    if refresh.exists():
        shutil.rmtree(refresh)
    refresh.mkdir(parents=True)
    runner = symexec_runner or run_symexec
    symexec = runner(
        main_root=main_root,
        target_c_file=target_c_file,
        output_root=refresh,
        target_files=target_files,
    )
    mismatches: list[dict[str, Any]] = []
    reference_version: dict[str, Any] | None = None
    fresh_version: dict[str, Any] | None = None
    if symexec.get("status") == "passed":
        try:
            reference_version = source_goal_version_at_root(
                root=reference_root,
                target_files=target_files,
                formal_case_lib_root=main_root,
            )
            fresh_version = source_goal_version_at_root(
                root=refresh,
                target_files=target_files,
                formal_case_lib_root=main_root,
            )
        except (OSError, UnicodeDecodeError, ValueError) as exc:
            mismatches.append({"kind": "source-goal-version", "message": str(exc)})
        else:
            reference_generated = {
                str(item["role"]): item for item in reference_version["generated_files"]
            }
            fresh_generated = {
                str(item["role"]): item for item in fresh_version["generated_files"]
            }
            exact_roles = (
                GENERATED_FILE_KEYS
                if manual_mode == "raw"
                else tuple(
                    key for key in GENERATED_FILE_KEYS if key != "proof_manual_file"
                )
            )
            for role in exact_roles:
                reference_record = reference_generated.get(role)
                fresh_record = fresh_generated.get(role)
                reference_path = (
                    reference_root.expanduser().resolve() / target_files[role]
                )
                fresh_path = refresh / target_files[role]
                reference_state = (
                    reference_record.get("state")
                    if isinstance(reference_record, dict)
                    else None
                )
                fresh_state = (
                    fresh_record.get("state")
                    if isinstance(fresh_record, dict)
                    else None
                )
                same_content = reference_state == fresh_state == "missing"
                if (
                    isinstance(reference_record, dict)
                    and isinstance(fresh_record, dict)
                    and reference_state == "present"
                    and fresh_state == "present"
                ):
                    try:
                        same_content = _normalized_generated_digest(
                            reference_path, reference_root
                        ) == _normalized_generated_digest(fresh_path, refresh)
                    except (OSError, UnicodeDecodeError):
                        same_content = False
                if not same_content:
                    mismatches.append(
                        {
                            "kind": role,
                            "relative_path": target_files[role],
                        }
                    )
            declaration_keys = (
                "target_witnesses",
                "witness_statement_hashes",
                "witness_goal_definition_hashes",
                "split_goals",
            )
            if any(
                reference_version[key] != fresh_version[key] for key in declaration_keys
            ):
                mismatches.append({"kind": "manual-witness-statements"})
    return {
        "status": (
            "passed"
            if symexec.get("status") == "passed" and not mismatches
            else "failed"
        ),
        "symexec": {
            key: symexec.get(key)
            for key in ("status", "returncode", "first_failure", "elapsed_seconds")
            if symexec.get(key) is not None
        },
        "mismatches": mismatches,
        "source_goal_version": {
            "reference": (
                reference_version.get("digest")
                if isinstance(reference_version, dict)
                else None
            ),
            "fresh": (
                fresh_version.get("digest") if isinstance(fresh_version, dict) else None
            ),
        },
        "refresh_root": str(refresh),
    }


def _invoke_symexec(
    plan: dict[str, Any], timeout_seconds: int | float | None
) -> tuple[int, str, str]:
    requested_timeout = (
        float(SYMEXEC_TIMEOUT_SECONDS)
        if timeout_seconds is None
        else float(timeout_seconds)
    )
    if not math.isfinite(requested_timeout) or requested_timeout < 0:
        raise ValueError("symexec timeout must be a finite non-negative number")
    if requested_timeout <= 0:
        return (
            124,
            "",
            "Symbolic execution was not started because its shared deadline expired during planning or an earlier run.",
        )
    result = run_bounded_process(
        plan["argv"],
        cwd=plan["cwd"],
        timeout_seconds=requested_timeout,
        timeout_message=f"\nsymexec timed out after {requested_timeout} seconds",
        detached_pipe_message=(
            "; detached descendants retained output pipes, so controller "
            "stopped draining them after 1 second"
        ),
        launch_error_prefix="symexec could not be launched: ",
    )
    return result.returncode, result.stdout, result.stderr


def _required_rocq_modules(text: str) -> list[str]:
    """Extract direct Require modules from generated, controller-owned text."""

    return required_rocq_modules(
        text,
        source_label="<generated-goal-check>",
    )


def _generated_artifact_snapshots(
    plan: Mapping[str, Any], output: Path
) -> dict[str, dict[str, Any]]:
    return {
        key: _lexical_regular_file_snapshot(
            root=output,
            relative=str(plan["target_files"][key]),
            label=f"generated output {key}",
        )
        for key in GENERATED_FILE_KEYS
    }


def _generated_snapshot_records(
    plan: Mapping[str, Any],
    snapshots: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    return [
        {
            "role": key,
            "relative_path": str(plan["target_files"][key]),
            "state": str(snapshots[key].get("state") or "invalid"),
            "sha256": (
                snapshots[key].get("sha256")
                if snapshots[key].get("state") == "present"
                else None
            ),
        }
        for key in GENERATED_FILE_KEYS
    ]


def _generated_preflight_failure(
    plan: Mapping[str, Any],
    snapshots: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any] | None:
    for key in GENERATED_FILE_KEYS:
        snapshot = snapshots[key]
        artifact_state = str(snapshot.get("state") or "invalid")
        if artifact_state in {"present", "missing"}:
            continue
        return {
            "category": "structure",
            "kind": "generated-output-path-invalid",
            "role": key,
            "relative_path": str(plan["target_files"][key]),
            "message": str(
                snapshot.get("message")
                or "generated output leaf is not a fixed non-link regular file or truly absent"
            ),
            "repair": "Restore the exact generated leaf and all of its ancestors to the fixed non-link topology before rerunning symbolic execution.",
        }
    return None


def _unlink_unchanged_snapshot_leaf(
    snapshot: Mapping[str, Any],
    *,
    label: str,
) -> None:
    path = snapshot.get("path")
    identity = snapshot.get("identity")
    if (
        snapshot.get("state") != "present"
        or not isinstance(path, Path)
        or not isinstance(identity, tuple)
        or len(identity) != 2
    ):
        raise OSError(f"{label} has no stable present-file identity")
    current = os.lstat(path)
    if (
        _metadata_is_link_like(current)
        or not stat.S_ISREG(current.st_mode)
        or (int(current.st_dev), int(current.st_ino)) != identity
    ):
        raise OSError(f"{label} changed before controller recovery unlink")
    path.unlink()


def _goal_check_requires_manual(
    plan: Mapping[str, Any],
    *,
    goal_check_snapshot: Mapping[str, Any],
) -> bool:
    target_files = plan["target_files"]
    modules = frozenset(
        _required_rocq_modules(
            _snapshot_text(
                goal_check_snapshot,
                label="generated output goal_check_file",
            )
        )
    )
    manual_modules = generated_artifact_module_spellings(
        target_files,
        roles=("proof_manual_file",),
    )
    return not modules.isdisjoint(manual_modules)


def _generated_output_failure(
    plan: dict[str, Any],
    output: Path,
    *,
    snapshots: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any] | None:
    current = (
        _generated_artifact_snapshots(plan, output)
        if snapshots is None
        else dict(snapshots)
    )
    if set(current) != set(GENERATED_FILE_KEYS):
        raise ValueError("generated output snapshot set is incomplete")
    for key in MANDATORY_GENERATED_FILE_KEYS:
        relative = str(plan["target_files"][key])
        snapshot = current[key]
        artifact_state = str(snapshot.get("state") or "invalid")
        if artifact_state not in {"present", "missing"}:
            return {
                "category": "generated-output",
                "kind": (
                    "generated-file-unreadable"
                    if artifact_state == "unreadable"
                    else (
                        "generated-file-nonregular"
                        if artifact_state == "nonregular"
                        else "generated-file-invalid"
                    )
                ),
                "role": key,
                "relative_path": relative,
                "message": str(
                    snapshot.get("message")
                    or "generated output is not a non-link regular file"
                ),
                "repair": "Restore the exact generated-output leaf as a regular file and rerun the unchanged controller symexec command.",
            }
        if artifact_state == "missing":
            return {
                "category": "generated-output",
                "kind": "generated-file-missing",
                "role": key,
                "relative_path": relative,
                "message": "symexec returned success without creating a required generated file",
                "repair": "Rerun the unchanged controller symexec command; if the file remains absent, inspect the target annotation and symbolic-execution output for the first failing function.",
            }
        if snapshot.get("size") == 0:
            return {
                "category": "generated-output",
                "kind": "generated-file-empty",
                "role": key,
                "relative_path": relative,
                "message": "symexec returned success with a zero-byte generated file",
                "repair": "Remove only the invalid zero-byte output through the controller recovery path and rerun symbolic execution; do not hand-edit generated files.",
            }

    relative = str(plan["target_files"]["proof_manual_file"])
    manual_snapshot = current["proof_manual_file"]
    manual_state = str(manual_snapshot.get("state") or "invalid")
    if manual_state not in {"present", "missing"}:
        return {
            "category": "generated-output",
            "kind": (
                "generated-file-unreadable"
                if manual_state == "unreadable"
                else (
                    "generated-file-nonregular"
                    if manual_state == "nonregular"
                    else "generated-file-invalid"
                )
            ),
            "role": "proof_manual_file",
            "relative_path": relative,
            "message": str(
                manual_snapshot.get("message")
                or "generated proof manual is not a non-link regular file"
            ),
            "repair": "Restore the exact generated-output leaf as a regular file or truly absent and rerun the unchanged controller symexec command.",
        }
    if manual_state == "missing":
        try:
            requires_manual = _goal_check_requires_manual(
                plan,
                goal_check_snapshot=current["goal_check_file"],
            )
        except ValueError as exc:
            return {
                "category": "generated-output",
                "kind": "goal-check-contract",
                "role": "goal_check_file",
                "relative_path": plan["target_files"]["goal_check_file"],
                "message": str(exc),
                "repair": "Repair the generated goal-check source and rerun canonical symbolic execution.",
            }
        if requires_manual:
            return {
                "category": "generated-output",
                "kind": "generated-file-missing",
                "role": "proof_manual_file",
                "relative_path": relative,
                "message": (
                    "symexec returned success without creating the proof manual "
                    "which the generated goal-check directly imports"
                ),
                "repair": "Repair the annotation or generator output so the imported manual module is generated, then rerun canonical symbolic execution.",
            }
        return None
    if manual_snapshot.get("size") == 0:
        return {
            "category": "generated-output",
            "kind": "generated-file-empty",
            "role": "proof_manual_file",
            "relative_path": relative,
            "message": "symexec returned success with a zero-byte generated file",
            "repair": "Remove only the invalid zero-byte output through the controller recovery path and rerun symbolic execution; do not hand-edit generated files.",
        }
    try:
        _prelude, lemmas = parse_manual_file(
            _snapshot_text(
                manual_snapshot,
                label="generated output proof_manual_file",
            )
        )
        ensure_unique_lemma_names(lemmas)
        partition_manual_lemmas(lemmas)
    except ValueError as exc:
        return {
            "category": "generated-output",
            "kind": "proof-manual-contract",
            "role": "proof_manual_file",
            "relative_path": relative,
            "message": str(exc),
            "repair": "Repair the C annotation or formal specification that produced the malformed manual, then rerun canonical symbolic execution.",
        }
    return None


def _relative_target(main_root: Path, target_c_file: Path) -> Path:
    target = target_c_file.expanduser()
    if not target.is_absolute():
        target = main_root / target
    target = target.resolve()
    try:
        relative = target.relative_to(main_root)
    except ValueError as exc:
        raise ValueError(f"target C file must be under main root: {target}") from exc
    if not target.is_file():
        raise ValueError(f"target C file does not exist: {target}")
    return relative


def _validate_output_root(main_root: Path, output_root: Path) -> Path:
    output = output_root.expanduser().resolve()
    if output == main_root:
        return output
    allowed = (main_root / "verification_runs", main_root / "reports")
    if any(_is_relative_to(output, root) for root in allowed):
        return output
    raise ValueError(
        f"output root must be the main root or be under main-root/verification_runs or main-root/reports: {output}"
    )


def _is_relative_to(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root.resolve())
        return True
    except ValueError:
        return False


def _runtime_platform() -> tuple[str, str, str]:
    return os.name, sys.platform, platform.machine()


def _driver_for_platform(main_root: Path) -> Path:
    os_name, platform_name, machine = _runtime_platform()
    normalized_machine = machine.strip().lower()

    if os_name == "nt":
        return main_root / "win-binary" / "symexec.exe"
    if platform_name.startswith("linux"):
        if normalized_machine not in {"x86_64", "amd64"}:
            raise ValueError(
                f"unsupported Linux architecture for bundled symexec: {machine or '<unknown>'}"
            )
        return main_root / "linux-binary" / "symexec"
    if platform_name == "darwin":
        if normalized_machine in {"arm64", "aarch64"}:
            return main_root / "mac-arm64-binary" / "symexec"
        if normalized_machine in {"x86_64", "amd64"}:
            return main_root / "mac-x86-64-binary" / "symexec"
        raise ValueError(
            f"unsupported macOS architecture for symexec: {machine or '<unknown>'}"
        )
    raise ValueError(
        "unsupported platform for symexec: "
        f"os.name={os_name!r}, sys.platform={platform_name!r}, machine={machine!r}"
    )


def _c_without_comments(text: str) -> str:
    """Mask C comments so commented-out include directives are never followed."""

    output: list[str] = []
    index = 0
    in_block = False
    in_line = False
    quote: str | None = None
    escaped = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if in_block:
            if pair == "*/":
                output.extend("  ")
                in_block = False
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_line:
            if char == "\n":
                in_line = False
                output.append(char)
            else:
                output.append(" ")
            index += 1
            continue
        if quote is None and pair == "/*":
            in_block = True
            output.extend("  ")
            index += 2
            continue
        if quote is None and pair == "//":
            in_line = True
            output.extend("  ")
            index += 2
            continue
        output.append(char)
        if quote is not None:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
        elif char in {'"', "'"}:
            quote = char
        index += 1
    if in_block:
        raise ValueError("unterminated C block comment while resolving quoted includes")
    return "".join(output)


def _quoted_include_paths(source: Path) -> list[str]:
    try:
        text = source.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise ValueError(f"cannot read include source {source}: {exc}") from exc
    uncommented = _c_without_comments(text)
    result: list[str] = []
    for match in QUOTED_INCLUDE_RE.finditer(uncommented):
        value = match.group("path").strip()
        if not value or "\0" in value:
            raise ValueError(f"invalid quoted include in {source}: {value!r}")
        if value not in result:
            result.append(value)
    return result


def _strategy_include_paths(source: Path) -> list[str]:
    """Return strategy files named by SimpleC annotation blocks."""

    try:
        text = source.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise ValueError(f"cannot read strategy include source {source}: {exc}") from exc
    result: list[str] = []
    for annotation in ANNOTATION_BLOCK_RE.finditer(text):
        for match in STRATEGY_INCLUDE_RE.finditer(annotation.group("body")):
            value = match.group("path").strip()
            if not value or "\0" in value:
                raise ValueError(f"invalid strategy include in {source}: {value!r}")
            if value not in result:
                result.append(value)
    return result


def _under_directory(path: Path, directory: Path) -> bool:
    try:
        path.relative_to(directory)
        return True
    except ValueError:
        return False


def _include_search_root(candidate: Path, include_parts: tuple[str, ...]) -> Path:
    root = candidate
    for _part in include_parts:
        root = root.parent
    return root


def _resolve_quoted_include(
    *,
    qcp_root: Path,
    including_source: Path,
    include_text: str,
    known_include_dirs: list[Path],
    strategy_profile_dirs: tuple[Path, ...],
) -> tuple[Path, Path]:
    """Resolve one include according to explicit repository search boundaries.

    The including directory and its top-level collection have deterministic C
    search precedence.  The target collection's explicit strategy profile is
    then searched in its declared order.  A repository-wide fallback is
    accepted only when it is unique; duplicate basenames therefore still fail
    for collections without a deterministic profile.
    """

    normalized_text = include_text.replace("\\", "/")
    include_path = Path(normalized_text)
    include_parts = tuple(part for part in include_path.parts if part not in {"."})
    if (
        not include_parts
        or include_path.is_absolute()
        or ".." in include_parts
        or include_path.drive
    ):
        raise ValueError(
            f"quoted include must stay under QCP_examples: {include_text!r} "
            f"from {including_source}"
        )

    local = (including_source.parent / Path(*include_parts)).resolve()
    if local.is_file() and _under_directory(local, qcp_root):
        return local, including_source.parent.resolve()

    source_relative = including_source.resolve().relative_to(qcp_root)
    collection_root = (qcp_root / source_relative.parts[0]).resolve()
    collection_candidate = (collection_root / Path(*include_parts)).resolve()
    if collection_candidate.is_file() and _under_directory(
        collection_candidate, collection_root
    ):
        return collection_candidate, collection_root

    for profile_dir in strategy_profile_dirs:
        candidate = (profile_dir / Path(*include_parts)).resolve()
        if candidate.is_file() and _under_directory(candidate, profile_dir):
            return candidate, profile_dir

    known_matches: dict[Path, Path] = {}
    for include_dir in known_include_dirs:
        candidate = (include_dir / Path(*include_parts)).resolve()
        if candidate.is_file() and _under_directory(candidate, qcp_root):
            known_matches[candidate] = include_dir
    if len(known_matches) == 1:
        return next(iter(known_matches.items()))
    if len(known_matches) > 1:
        choices = ", ".join(str(path) for path in sorted(known_matches))
        raise ValueError(
            f"ambiguous quoted include {include_text!r} from {including_source}: "
            + choices
        )

    repository_matches: list[Path] = []
    for candidate in qcp_root.rglob(include_parts[-1]):
        if not candidate.is_file():
            continue
        relative = candidate.resolve().relative_to(qcp_root)
        if len(relative.parts) < len(include_parts):
            continue
        if tuple(relative.parts[-len(include_parts) :]) == include_parts:
            repository_matches.append(candidate.resolve())
    repository_matches = sorted(set(repository_matches))
    if not repository_matches:
        raise ValueError(
            f"cannot resolve quoted include {include_text!r} from {including_source} "
            "under QCP_examples"
        )
    if len(repository_matches) > 1:
        choices = ", ".join(str(path) for path in repository_matches)
        raise ValueError(
            f"ambiguous quoted include {include_text!r} from {including_source}: "
            + choices
        )
    candidate = repository_matches[0]
    return candidate, _include_search_root(candidate, include_parts)


def _resolve_strategy_include(
    *,
    qcp_root: Path,
    including_source: Path,
    include_text: str,
    known_include_dirs: list[Path],
    strategy_profile_dirs: tuple[Path, ...],
) -> Path:
    """Resolve one annotation strategy path inside ``QCP_examples``.

    Unlike C preprocessor includes, existing strategy annotations use a
    confined ``..`` path to share a sibling strategy directory.  That spelling
    is accepted only when its direct resolution remains below ``QCP_examples``.
    """

    normalized_text = include_text.replace("\\", "/")
    include_path = Path(normalized_text)
    if include_path.is_absolute() or include_path.drive:
        raise ValueError(
            f"strategy include must stay under QCP_examples: {include_text!r} "
            f"from {including_source}"
        )
    direct = (including_source.parent / include_path).resolve()
    if direct.is_file() and _under_directory(direct, qcp_root):
        return direct
    if ".." in include_path.parts:
        raise ValueError(
            f"cannot resolve confined strategy include {include_text!r} "
            f"from {including_source}"
        )
    resolved, _search_root = _resolve_quoted_include(
        qcp_root=qcp_root,
        including_source=including_source,
        include_text=include_text,
        known_include_dirs=known_include_dirs,
        strategy_profile_dirs=strategy_profile_dirs,
    )
    return resolved


def _strategy_profile_directories(
    qcp_root: Path,
    target_relative: Path,
) -> tuple[Path, ...]:
    """Return the repository-defined strategy profile for one target path."""

    target_parts = target_relative.parts
    target_collection = target_parts[0]
    profile_collection = STRATEGY_PROFILE_BY_COLLECTION.get(target_collection)
    for prefix, override in sorted(
        STRATEGY_PROFILE_BY_TARGET_PREFIX.items(),
        key=lambda item: len(item[0]),
        reverse=True,
    ):
        if target_parts[: len(prefix)] == prefix:
            profile_collection = override
            break
    if profile_collection is None:
        return ()
    profile_root = (qcp_root / profile_collection).resolve()
    if not profile_root.is_dir() or not _under_directory(profile_root, qcp_root):
        raise ValueError(
            "strategy profile directory is missing for "
            f"QCP_examples/{target_collection}: {profile_root}"
        )
    return (profile_root,)


def _relative_directory_argument(path: Path, main_root: Path) -> str:
    relative = path.resolve().relative_to(main_root).as_posix()
    return relative.rstrip("/") + "/"


def _strategy_directory_pair(
    directory: Path,
    *,
    main_root: Path,
    qcp_root: Path,
) -> tuple[str, str]:
    relative = directory.resolve().relative_to(qcp_root)
    if not relative.parts or any(
        ROCQ_IDENTIFIER_RE.fullmatch(part) is None for part in relative.parts
    ):
        raise ValueError(
            "strategy directory cannot form an SLP logical path: "
            + relative.as_posix()
        )
    if relative.parts[0] == "stdlib":
        logical = "SimpleC.StdLib" + (
            "." + ".".join(relative.parts[1:])
            if len(relative.parts) > 1
            else ""
        )
    else:
        logical = "SimpleC.EE." + ".".join(relative.parts)
    return _relative_directory_argument(directory, main_root), logical


def _extra_symexec_flags(target_relative: Path) -> tuple[str, ...]:
    try:
        qcp_relative = target_relative.relative_to("QCP_examples")
    except ValueError:
        return ()
    for prefix, flags in sorted(
        SYMEXEC_FLAGS_BY_TARGET_PREFIX.items(),
        key=lambda item: len(item[0]),
        reverse=True,
    ):
        if qcp_relative.parts[: len(prefix)] == prefix:
            return flags
    return ()


def _symexec_search_paths(
    main_root: Path, target_rel: Path
) -> tuple[list[str], list[tuple[str, str]]]:
    """Discover include roots plus exact-strategy and collection SLP pairs."""

    qcp_root = (main_root / "QCP_examples").resolve()
    target = (main_root / target_rel).resolve()
    try:
        target_relative = target.relative_to(qcp_root)
    except ValueError as exc:
        raise ValueError(f"target C escaped QCP_examples: {target}") from exc
    if len(target_relative.parts) < 2:
        raise ValueError(f"target C lacks a QCP_examples collection: {target}")
    strategy_profile_dirs = _strategy_profile_directories(
        qcp_root,
        target_relative,
    )
    include_dirs: list[Path] = [target.parent]
    source_queue: list[Path] = [target]
    visited: set[Path] = set()
    collections: list[str] = []
    strategy_directories: list[Path] = []

    while source_queue:
        source = source_queue.pop(0).resolve()
        if source in visited:
            continue
        visited.add(source)
        try:
            source_relative = source.relative_to(qcp_root)
        except ValueError as exc:
            raise ValueError(
                f"quoted include escaped QCP_examples: {source}"
            ) from exc
        if len(source_relative.parts) < 2:
            raise ValueError(f"include source lacks a QCP_examples collection: {source}")
        collection = source_relative.parts[0]
        if ROCQ_IDENTIFIER_RE.fullmatch(collection) is None:
            raise ValueError(
                f"QCP_examples collection cannot form an SLP module: {collection!r}"
            )
        if collection not in collections:
            collections.append(collection)
        for include_text in _quoted_include_paths(source):
            included, search_root = _resolve_quoted_include(
                qcp_root=qcp_root,
                including_source=source,
                include_text=include_text,
                known_include_dirs=include_dirs,
                strategy_profile_dirs=strategy_profile_dirs,
            )
            if search_root not in include_dirs:
                include_dirs.append(search_root)
            if included not in visited:
                source_queue.append(included)
        for include_text in _strategy_include_paths(source):
            strategy = _resolve_strategy_include(
                qcp_root=qcp_root,
                including_source=source,
                include_text=include_text,
                known_include_dirs=include_dirs,
                strategy_profile_dirs=strategy_profile_dirs,
            )
            strategy_directory = strategy.parent.resolve()
            if strategy_directory not in strategy_directories:
                strategy_directories.append(strategy_directory)
            if strategy not in visited:
                source_queue.append(strategy)

    # A collection's default strategy profile participates even when the C
    # include graph does not name one of its headers directly.  This preserves
    # the existing Applications_human/LLM_bench symexec environment while the
    # include traversal remains otherwise data-driven.
    for profile_dir in strategy_profile_dirs:
        if profile_dir not in include_dirs:
            include_dirs.append(profile_dir)
        profile_collection = profile_dir.relative_to(qcp_root).parts[0]
        if profile_collection not in collections:
            collections.append(profile_collection)

    include_args = [
        _relative_directory_argument(directory, main_root) for directory in include_dirs
    ]
    collection_pairs = [
        (
            f"QCP_examples/{collection}/",
            (
                "SimpleC.StdLib"
                if collection == "stdlib"
                else f"SimpleC.EE.{collection}"
            ),
        )
        for collection in collections
    ]
    slp_pairs: list[tuple[str, str]] = []
    for pair in (
        *(
            _strategy_directory_pair(
                directory,
                main_root=main_root,
                qcp_root=qcp_root,
            )
            for directory in strategy_directories
            if len(directory.resolve().relative_to(qcp_root).parts) > 1
        ),
        *collection_pairs,
    ):
        if pair not in slp_pairs:
            slp_pairs.append(pair)
    return include_args, slp_pairs


def _sealed_target_files(
    *,
    target_rel: Path,
    target_files: Mapping[str, str],
) -> dict[str, str]:
    if any(
        not isinstance(key, str) or not isinstance(value, str)
        for key, value in target_files.items()
    ):
        raise ValueError("sealed target_files fields and values must all be strings")
    supplied = dict(target_files)
    required = {
        "c_file",
        "formal_directory",
        "formal_case_lib",
        "goal_file",
        "proof_auto_file",
        "proof_manual_file",
        "goal_check_file",
        "case_name",
        "active_case_theory",
    }
    missing = sorted(required - set(supplied))
    if missing:
        raise ValueError(
            "sealed target_files is missing required field(s): " + ", ".join(missing)
        )
    unexpected = sorted(set(supplied) - required)
    if unexpected:
        raise ValueError(
            "sealed target_files has unexpected field(s): " + ", ".join(unexpected)
        )
    if supplied["c_file"] != target_rel.as_posix():
        raise ValueError(
            "sealed target_files c_file does not match the requested target C: "
            f"{supplied['c_file']!r} != {target_rel.as_posix()!r}"
        )
    case_name = supplied["case_name"]
    if ROCQ_IDENTIFIER_RE.fullmatch(case_name) is None:
        raise ValueError(f"sealed target_files has an invalid Rocq case name: {case_name!r}")
    formal_directory = Path(supplied["formal_directory"])
    if (
        formal_directory.is_absolute()
        or ".." in formal_directory.parts
        or formal_directory.parts[:2] != ("Rocq", "examples")
        or len(formal_directory.parts) < 3
    ):
        raise ValueError(
            "sealed target_files formal_directory must stay under "
            f"Rocq/examples/<collection>: {formal_directory}"
        )
    logical_parts = formal_directory.parts[2:]
    if any(ROCQ_IDENTIFIER_RE.fullmatch(part) is None for part in logical_parts):
        raise ValueError(
            "sealed target_files formal_directory cannot form a Rocq logical path"
        )
    expected_theory = "SimpleC.EE." + ".".join(logical_parts)
    if supplied["active_case_theory"] != expected_theory:
        raise ValueError(
            "sealed target_files active_case_theory does not match formal_directory"
        )
    artifact_suffixes = {
        "formal_case_lib": "_lib.v",
        "goal_file": "_goal.v",
        "proof_auto_file": "_proof_auto.v",
        "proof_manual_file": "_proof_manual.v",
        "goal_check_file": "_goal_check.v",
    }
    for key, suffix in artifact_suffixes.items():
        expected_path = formal_directory / f"{case_name}{suffix}"
        if supplied[key] != expected_path.as_posix():
            raise ValueError(
                f"sealed target_files {key} is outside its exact canonical path: "
                f"{supplied[key]!r}"
            )
    return dict(supplied)


def build_symexec_plan(
    *,
    main_root: Path,
    target_c_file: Path,
    output_root: Path,
    target_files: Mapping[str, str],
) -> dict[str, Any]:
    main_root = main_root.expanduser().resolve()
    if (
        not (main_root / "QCP_examples").is_dir()
        or not (main_root / "Rocq").is_dir()
    ):
        raise ValueError(
            f"main root does not look like the QCP repository: {main_root}"
        )
    target_rel = _relative_target(main_root, target_c_file)
    output_root = _validate_output_root(main_root, output_root)
    planned_target_files = _sealed_target_files(
        target_rel=target_rel,
        target_files=target_files,
    )
    driver = _driver_for_platform(main_root)
    include_args, slp_pairs = _symexec_search_paths(main_root, target_rel)
    argv = [
        str(driver),
        f"--goal-file={output_root / planned_target_files['goal_file']}",
        f"--proof-auto-file={output_root / planned_target_files['proof_auto_file']}",
        f"--proof-manual-file={output_root / planned_target_files['proof_manual_file']}",
    ]
    argv.extend(f"-I{directory}" for directory in include_args)
    for physical, logical in slp_pairs:
        argv.extend(("-slp", physical, logical))
    argv.extend(
        (
            f"--coq-logic-path={planned_target_files['active_case_theory']}",
            f"--input-file={planned_target_files['c_file']}",
        )
    )
    extra_flags = _extra_symexec_flags(target_rel)
    argv.extend(extra_flags)
    argv.append("--no-exec-info")
    return {
        "helper": str(Path(__file__).resolve()),
        "driver": str(driver),
        "cwd": str(main_root),
        "main_root": str(main_root),
        "output_root": str(output_root),
        "target_c_file": planned_target_files["c_file"],
        "target_files": planned_target_files,
        "include_args": include_args,
        "slp_args": [item for pair in slp_pairs for item in pair],
        "extra_flags": list(extra_flags),
        "argv": argv,
    }


def _run_symexec_with_budget(
    *,
    main_root: Path,
    target_c_file: Path,
    output_root: Path,
    target_files: Mapping[str, str],
    timeout_seconds: int | None = SYMEXEC_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    started = time.time()
    # A zero-byte-manual recovery may invoke the driver twice. Both launches
    # share this one command budget so recovery cannot double the stall bound.
    budget = float(
        timeout_seconds if timeout_seconds is not None else SYMEXEC_TIMEOUT_SECONDS
    )
    if not math.isfinite(budget) or budget < 0:
        raise ValueError("symexec timeout must be a finite non-negative number")
    deadline = time.monotonic() + budget
    plan = build_symexec_plan(
        main_root=main_root,
        target_c_file=target_c_file,
        output_root=output_root,
        target_files=target_files,
    )
    driver = Path(plan["driver"])
    evidence: dict[str, Any] = {
        "target_c_file": plan["target_c_file"],
    }
    if not driver.is_file():
        return {
            **evidence,
            "status": "skipped",
            "reason": "canonical symexec driver not found",
            "first_failure": {
                "category": "tool",
                "kind": "driver-missing",
                "message": f"canonical symexec driver not found: {driver}",
                "repair": "Install or restore the controller-selected platform driver; do not substitute a different executable or raw command.",
            },
            "returncode": None,
            "generated_files": [],
            "elapsed_seconds": round(time.time() - started, 3),
        }
    if os.name != "nt" and not os.access(driver, os.X_OK):
        return {
            **evidence,
            "status": "skipped",
            "reason": "canonical symexec driver is not executable",
            "first_failure": {
                "category": "tool",
                "kind": "driver-not-executable",
                "message": f"canonical symexec driver is not executable: {driver}",
                "repair": "Restore executable permission for the selected platform driver, then rerun the unchanged controller command.",
            },
            "returncode": None,
            "generated_files": [],
            "elapsed_seconds": round(time.time() - started, 3),
        }
    output = Path(plan["output_root"])
    preflight_snapshots = _generated_artifact_snapshots(plan, output)
    preflight_failure = _generated_preflight_failure(plan, preflight_snapshots)
    if preflight_failure is not None:
        return {
            **evidence,
            "status": "failed",
            "returncode": None,
            "generated_files": _generated_snapshot_records(
                plan,
                preflight_snapshots,
            ),
            "first_failure": preflight_failure,
            "elapsed_seconds": round(time.time() - started, 3),
        }
    try:
        formal_directory = fixed_path_under(
            output / str(plan["target_files"]["formal_directory"]),
            output,
            label="generated formal directory",
        )
        formal_directory.mkdir(parents=True, exist_ok=True)
    except (OSError, SystemExit) as exc:
        return {
            **evidence,
            "status": "failed",
            "returncode": None,
            "generated_files": _generated_snapshot_records(
                plan,
                preflight_snapshots,
            ),
            "first_failure": {
                "category": "structure",
                "kind": "generated-output-directory-invalid",
                "message": str(exc),
                "repair": "Restore the fixed non-link generated formal directory before rerunning symbolic execution.",
            },
            "elapsed_seconds": round(time.time() - started, 3),
        }
    returncode, stdout, stderr = _invoke_symexec(plan, deadline - time.monotonic())
    snapshots = _generated_artifact_snapshots(plan, output)
    manual_snapshot = snapshots["proof_manual_file"]
    recovery: dict[str, Any] | None = None
    recovery_failure: dict[str, Any] | None = None
    zero_byte_manual = (
        returncode == 0
        and manual_snapshot.get("state") == "present"
        and manual_snapshot.get("size") == 0
    )
    if zero_byte_manual:
        recovery = {
            "kind": "zero-byte-proof-manual",
        }
        try:
            recovery["removed_sha256"] = str(manual_snapshot["sha256"])
            _unlink_unchanged_snapshot_leaf(
                manual_snapshot,
                label="zero-byte generated proof manual",
            )
        except OSError as exc:
            recovery["status"] = "failed"
            recovery_failure = {
                "category": "tool",
                "kind": "zero-byte-proof-manual-recovery",
                "role": "proof_manual_file",
                "relative_path": plan["target_files"]["proof_manual_file"],
                "message": str(exc),
                "repair": "Fix the generated-output filesystem problem, then rerun the unchanged controller symexec command.",
            }
        else:
            returncode, stdout, stderr = _invoke_symexec(
                plan, deadline - time.monotonic()
            )
            recovery["rerun_returncode"] = returncode
            snapshots = _generated_artifact_snapshots(plan, output)

    generated = _generated_snapshot_records(plan, snapshots)
    if recovery_failure is not None:
        output_failure = recovery_failure
    elif returncode == 0:
        output_failure = _generated_output_failure(
            plan,
            output,
            snapshots=snapshots,
        )
    else:
        category = "tool" if returncode == 124 else "symbolic-execution"
        output_failure = {
            "category": category,
            "kind": "timeout" if returncode == 124 else "symexec-error",
            "message": _tail(stderr or stdout, 1600).strip()
            or f"symbolic execution exited with return code {returncode}",
            "repair": (
                "Rerun the unchanged controller command once; if the timeout repeats, report a tooling blocker with the failing phase."
                if category == "tool"
                else "Inspect the named C function and nearest Require/Ensure/Assert/Inv/where boundary, repair the annotation or spec, and rerun canonical symbolic execution."
            ),
        }
    passed = returncode == 0 and output_failure is None
    if recovery is not None and "status" not in recovery:
        recovery["status"] = "passed" if passed else "failed"
    result = {
        **evidence,
        "status": "passed" if passed else "failed",
        "returncode": returncode,
        "generated_files": generated,
        "elapsed_seconds": round(time.time() - started, 3),
    }
    if recovery is not None:
        result["recovery"] = recovery
    if output_failure is not None:
        result["first_failure"] = output_failure
    if not passed:
        result["stdout_tail"] = _tail(stdout)
        result["stderr_tail"] = _tail(stderr)
    return result


def run_symexec(
    *,
    main_root: Path,
    target_c_file: Path,
    output_root: Path,
    target_files: Mapping[str, str],
    timeout_seconds: int | None = SYMEXEC_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Run symbolic execution for canonical or replay output."""

    root = main_root.expanduser().resolve()
    output = output_root.expanduser().resolve()
    return _run_symexec_with_budget(
        main_root=root,
        target_c_file=target_c_file,
        output_root=output,
        target_files=target_files,
        timeout_seconds=timeout_seconds,
    )
