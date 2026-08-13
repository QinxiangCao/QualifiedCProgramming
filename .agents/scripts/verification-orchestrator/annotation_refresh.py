#!/usr/bin/env python3
"""Transactional generated-output refresh for one annotation attempt.

The public controller creates and seals the attempt's immutable ``before``
history before the annotation owner starts.  Immediately before canonical
main-root symbolic execution, this module backs up all four generated files,
classifies the existing manual, removes only a raw seed or an exact copy of the
sealed attempt-before manual, and leaves a durable transaction receipt.  A
failed command restores the whole generated bundle; an interrupted command is
rolled back on the next invocation before a new transaction starts.
"""

# ruff: noqa: E402 -- standalone controller modules resolve shared helpers at runtime.

from __future__ import annotations

import json
import os
import re
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
VC_PROVING_SCRIPTS = SCRIPT_DIR.parent / "vc-proving"
if str(VC_PROVING_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(VC_PROVING_SCRIPTS))

from atomic_file import atomic_copy_file
from file_integrity import sha256_file as _sha256
from path_utils import fixed_path_under, path_is_link_like, write_json
from proof_manual_utils import (
    ensure_unique_lemma_names,
    lemma_proof_parts,
    parse_manual_file,
    partition_manual_lemmas,
    split_goal_parent,
    strip_coq_comments,
)

TRANSACTION_DIRECTORY_NAME = ".annotation-owner-main-refresh-transaction"
TRANSACTION_MANIFEST_NAME = "transaction.json"
PREPARING_DIRECTORY_PREFIX = ".annotation-owner-main-refresh-preparing-"
GENERATED_FILE_KEYS = (
    "goal_file",
    "proof_auto_file",
    "proof_manual_file",
    "goal_check_file",
)


class AnnotationRefreshError(RuntimeError):
    """One compact controller-facing refresh failure."""

    def __init__(
        self,
        *,
        kind: str,
        message: str,
        repair: str,
        category: str = "generated-output",
    ) -> None:
        super().__init__(message)
        self.category = category
        self.kind = kind
        self.message = message
        self.repair = repair

    def failure(self) -> dict[str, str]:
        return {
            "category": self.category,
            "kind": self.kind,
            "message": self.message,
            "repair": self.repair,
        }


def transaction_root_for_attempt(report_directory: Path) -> Path:
    report = report_directory.expanduser().absolute()
    if not report.is_dir() or report.resolve() != report:
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-report-path",
            message=(
                "annotation report directory is missing, uses a symlink, or escaped "
                f"its fixed path: {report}"
            ),
            repair=(
                "Restore the controller-owned fixed annotation report directory, "
                "then rerun the unchanged controller symexec command."
            ),
        )
    transaction = report / TRANSACTION_DIRECTORY_NAME
    if path_is_link_like(transaction):
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-transaction-path",
            message=(
                f"annotation refresh transaction cannot be a symlink: {transaction}"
            ),
            repair=(
                "Remove the unexpected symlink without changing formal files, then "
                "rerun the unchanged controller symexec command."
            ),
        )
    return transaction


def _generated_paths(
    main_root: Path, target_files: dict[str, str]
) -> dict[str, Path]:
    owner_input = Path(os.path.abspath(os.fspath(main_root.expanduser())))
    try:
        owner = fixed_path_under(
            owner_input,
            owner_input,
            label="annotation refresh main root",
        )
    except SystemExit as exc:
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-target-path",
            message=str(exc),
            repair=(
                "Restore the fixed non-symlink main root, then rerun the unchanged "
                "controller symexec command."
            ),
        ) from exc
    paths: dict[str, Path] = {}
    for role in GENERATED_FILE_KEYS:
        relative = Path(str(target_files[role]))
        if relative.is_absolute() or ".." in relative.parts:
            raise AnnotationRefreshError(
                category="structure",
                kind="annotation-refresh-target-path",
                message=f"generated target is not repository-relative: {relative}",
                repair=(
                    "Repair the controller target-file mapping before retrying; do "
                    "not delete or move generated files manually."
                ),
            )
        try:
            fixed_parent = fixed_path_under(
                (owner / relative).parent,
                owner,
                label=f"annotation refresh {role} parent",
            )
        except SystemExit as exc:
            raise AnnotationRefreshError(
                category="structure",
                kind="annotation-refresh-target-path",
                message=str(exc),
                repair=(
                    "Restore the fixed non-symlink formal target path, then rerun the "
                    "unchanged controller symexec command."
                ),
            ) from exc
        paths[role] = fixed_parent / relative.name
    return paths


def _clear_exact_generated_leaf(path: Path) -> None:
    """Remove only one already-validated generated leaf without following it."""

    if not os.path.lexists(path):
        return
    if path_is_link_like(path):
        try:
            path.unlink()
        except IsADirectoryError:
            path.rmdir()
    elif path.is_dir():
        shutil.rmtree(path)
    else:
        path.unlink()


def _manual_refresh_state(
    manual: Path, *, sealed_before_manual: Path | None
) -> str:
    if not os.path.lexists(manual):
        return "missing"
    if path_is_link_like(manual) or not manual.is_file():
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-manual-path",
            message=f"proof manual is not a fixed regular file: {manual}",
            repair=(
                "Restore the proof manual as a regular main-root file, then rerun the "
                "unchanged controller symexec command."
            ),
        )
    try:
        if manual.stat().st_size == 0:
            return "zero-byte"
        _prelude, lemmas = parse_manual_file(manual.read_text(encoding="utf-8"))
        ensure_unique_lemma_names(lemmas)
        partition_manual_lemmas(lemmas)
        for lemma in lemmas:
            _statement, proof_span, _trailing = lemma_proof_parts(lemma)
            proof = strip_coq_comments(proof_span).strip()
            expected = (
                "Abort" if split_goal_parent(str(lemma["name"])) else "Admitted"
            )
            if (
                re.fullmatch(
                    rf"Proof(?:\s+using\s+[^.]+)?\.\s*{expected}\s*\.",
                    proof,
                    flags=re.DOTALL,
                )
                is None
            ):
                raise ValueError(
                    f"lemma `{lemma['name']}` is not an untouched generated "
                    f"{expected} seed"
                )
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        if (
            sealed_before_manual is not None
            and not sealed_before_manual.is_symlink()
            and sealed_before_manual.is_file()
            and sealed_before_manual.resolve() == sealed_before_manual.absolute()
        ):
            try:
                if _sha256(manual) == _sha256(sealed_before_manual):
                    return "sealed-before-manual"
            except OSError:
                pass
        raise AnnotationRefreshError(
            kind="protected-proof-manual",
            message=(
                "refusing to replace a proof manual that is neither an untouched "
                "raw generation seed nor the exact sealed attempt-before manual: "
                f"{exc}"
            ),
            repair=(
                "Restore the exact controller-sealed attempt-before manual or a raw "
                "Admitted/Abort seed. A history copy preserves old proof bytes but "
                "does not itself authorize proof reuse."
            ),
        ) from exc
    return "raw-seed"


def _load_manifest(
    transaction_root: Path, target_files: dict[str, str]
) -> dict[str, Any]:
    manifest_path = transaction_root / TRANSACTION_MANIFEST_NAME
    if (
        path_is_link_like(manifest_path)
        or manifest_path.resolve() != manifest_path.absolute()
    ):
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-transaction-contract",
            message="annotation refresh transaction manifest uses a symlink",
            repair=(
                "Restore the controller-owned transaction manifest and backup "
                "without following external paths."
            ),
        )
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-transaction-contract",
            message=f"cannot read annotation refresh transaction: {exc}",
            repair=(
                "Restore the transaction manifest and its backup files, or recover "
                "the generated bundle from the sealed attempt before snapshot."
            ),
        ) from exc
    if set(manifest) != {"status", "generated_files"}:
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-transaction-contract",
            message="annotation refresh transaction has unsupported or missing fields",
            repair=(
                "Recover the generated bundle from the sealed attempt before "
                "snapshot before retrying symbolic execution."
            ),
        )
    if manifest.get("status") not in {"prepared", "committed"}:
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-transaction-contract",
            message="annotation refresh transaction has an invalid status",
            repair=(
                "Recover the generated bundle from the sealed attempt before "
                "snapshot before retrying symbolic execution."
            ),
        )
    records = manifest.get("generated_files")
    if not isinstance(records, list) or len(records) != len(GENERATED_FILE_KEYS):
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-transaction-contract",
            message="annotation refresh transaction does not cover all generated files",
            repair=(
                "Recover the complete generated bundle from the sealed attempt "
                "before snapshot before retrying symbolic execution."
            ),
        )
    by_role: dict[str, dict[str, Any]] = {}
    for record in records:
        if not isinstance(record, dict):
            by_role = {}
            break
        role = str(record.get("role") or "")
        if role in by_role:
            by_role = {}
            break
        by_role[role] = record
    if set(by_role) != set(GENERATED_FILE_KEYS):
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-transaction-contract",
            message="annotation refresh transaction has invalid generated-file roles",
            repair=(
                "Recover the complete generated bundle from the sealed attempt "
                "before snapshot before retrying symbolic execution."
            ),
        )
    for role in GENERATED_FILE_KEYS:
        record = by_role[role]
        if (
            set(record) != {"role", "relative_path", "state", "sha256"}
            or record.get("relative_path") != str(target_files[role])
            or record.get("state") not in {"present", "missing"}
        ):
            raise AnnotationRefreshError(
                category="structure",
                kind="annotation-refresh-transaction-contract",
                message=f"annotation refresh transaction record is invalid: {role}",
                repair=(
                    "Recover the generated bundle from the sealed attempt before "
                    "snapshot before retrying symbolic execution."
                ),
            )
    return manifest


def _atomic_restore(source: Path, destination: Path) -> None:
    atomic_copy_file(
        source,
        destination,
        suffix=".annotation-refresh",
        preserve_metadata=True,
    )


def _restore_transaction(
    *,
    main_root: Path,
    target_files: dict[str, str],
    transaction_root: Path,
) -> None:
    manifest = _load_manifest(transaction_root, target_files)
    paths = _generated_paths(main_root, target_files)
    records = {
        str(record["role"]): record for record in manifest["generated_files"]
    }

    for role in GENERATED_FILE_KEYS:
        record = records[role]
        if record["state"] != "present":
            continue
        backup = transaction_root / "backup" / str(record["relative_path"])
        if (
            path_is_link_like(backup)
            or backup.resolve() != backup.absolute()
            or not backup.is_file()
            or _sha256(backup) != record.get("sha256")
        ):
            raise AnnotationRefreshError(
                category="structure",
                kind="annotation-refresh-backup-integrity",
                message=f"annotation refresh backup is missing or changed: {role}",
                repair=(
                    "Recover the complete generated bundle from the sealed attempt "
                    "before snapshot before retrying symbolic execution."
                ),
            )

    try:
        for role in GENERATED_FILE_KEYS:
            record = records[role]
            destination = paths[role]
            if record["state"] == "present":
                source = transaction_root / "backup" / str(
                    record["relative_path"]
                )
                _clear_exact_generated_leaf(destination)
                _atomic_restore(source, destination)
            else:
                _clear_exact_generated_leaf(destination)
    except OSError as exc:
        raise AnnotationRefreshError(
            category="tool",
            kind="annotation-refresh-rollback",
            message=f"failed to restore the generated bundle: {exc}",
            repair=(
                "Restore write access and rerun the unchanged controller symexec "
                "command; the durable transaction backup must not be edited."
            ),
        ) from exc


def _discard_transaction(transaction_root: Path) -> None:
    try:
        shutil.rmtree(transaction_root)
    except OSError as exc:
        raise AnnotationRefreshError(
            category="tool",
            kind="annotation-refresh-transaction-cleanup",
            message=f"failed to remove annotation refresh transaction: {exc}",
            repair=(
                "Restore delete access to the annotation attempt report directory, "
                "then rerun the unchanged controller symexec command."
            ),
        ) from exc


def recover_interrupted_refresh(
    *,
    main_root: Path,
    target_files: dict[str, str],
    transaction_root: Path,
) -> str | None:
    if not os.path.lexists(transaction_root):
        return None
    if path_is_link_like(transaction_root) or not transaction_root.is_dir():
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-transaction-path",
            message=(
                "annotation refresh transaction is not a fixed directory: "
                f"{transaction_root}"
            ),
            repair=(
                "Restore the controller-owned transaction directory without changing "
                "its backup, then rerun the unchanged controller symexec command."
            ),
        )
    manifest = _load_manifest(transaction_root, target_files)
    if manifest["status"] == "prepared":
        _restore_transaction(
            main_root=main_root,
            target_files=target_files,
            transaction_root=transaction_root,
        )
        recovery = "rolled-back-interrupted"
    else:
        recovery = "discarded-committed"
    _discard_transaction(transaction_root)
    return recovery


def _discard_interrupted_preparations(report_directory: Path) -> int:
    removed = 0
    for candidate in report_directory.iterdir():
        if not candidate.name.startswith(PREPARING_DIRECTORY_PREFIX):
            continue
        if path_is_link_like(candidate) or not candidate.is_dir():
            raise AnnotationRefreshError(
                category="structure",
                kind="annotation-refresh-preparation-path",
                message=(
                    "interrupted annotation refresh preparation is not a fixed "
                    f"directory: {candidate}"
                ),
                repair=(
                    "Restore the controller-owned attempt report directory without "
                    "following external paths, then rerun the unchanged command."
                ),
            )
        _discard_transaction(candidate)
        removed += 1
    return removed


def begin_generated_refresh(
    *,
    main_root: Path,
    target_files: dict[str, str],
    report_directory: Path,
    before_snapshot_directory: Path | None = None,
) -> dict[str, Any]:
    transaction_root = transaction_root_for_attempt(report_directory)
    recovered = recover_interrupted_refresh(
        main_root=main_root,
        target_files=target_files,
        transaction_root=transaction_root,
    )
    discarded_preparations = _discard_interrupted_preparations(
        transaction_root.parent
    )
    paths = _generated_paths(main_root, target_files)
    manual = paths["proof_manual_file"]
    sealed_before_manual = (
        before_snapshot_directory.expanduser().absolute()
        / str(target_files["proof_manual_file"])
        if before_snapshot_directory is not None
        else None
    )
    manual_state = _manual_refresh_state(
        manual, sealed_before_manual=sealed_before_manual
    )

    temporary = Path(
        tempfile.mkdtemp(
            prefix=PREPARING_DIRECTORY_PREFIX,
            dir=transaction_root.parent,
        )
    )
    try:
        records: list[dict[str, Any]] = []
        for role in GENERATED_FILE_KEYS:
            source = paths[role]
            if os.path.lexists(source):
                if path_is_link_like(source) or not source.is_file():
                    raise AnnotationRefreshError(
                        category="structure",
                        kind="annotation-refresh-target-path",
                        message=f"generated target is not a regular file: {source}",
                        repair=(
                            "Restore the fixed generated target path, then rerun the "
                            "unchanged controller symexec command."
                        ),
                    )
                destination = temporary / "backup" / str(target_files[role])
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, destination)
                records.append(
                    {
                        "role": role,
                        "relative_path": str(target_files[role]),
                        "state": "present",
                        "sha256": _sha256(destination),
                    }
                )
            else:
                records.append(
                    {
                        "role": role,
                        "relative_path": str(target_files[role]),
                        "state": "missing",
                        "sha256": None,
                    }
                )
        write_json(
            temporary / TRANSACTION_MANIFEST_NAME,
            {
                "status": "prepared",
                "generated_files": records,
            },
        )
        os.replace(temporary, transaction_root)
        if os.path.lexists(manual):
            _clear_exact_generated_leaf(manual)
    except AnnotationRefreshError:
        if temporary.exists():
            shutil.rmtree(temporary, ignore_errors=True)
        raise
    except OSError as exc:
        if (
            os.path.lexists(transaction_root)
            and not path_is_link_like(transaction_root)
            and transaction_root.is_dir()
        ):
            try:
                _restore_transaction(
                    main_root=main_root,
                    target_files=target_files,
                    transaction_root=transaction_root,
                )
                _discard_transaction(transaction_root)
            except AnnotationRefreshError as rollback_exc:
                raise rollback_exc from exc
        if temporary.exists():
            shutil.rmtree(temporary, ignore_errors=True)
        raise AnnotationRefreshError(
            category="tool",
            kind="annotation-refresh-prepare",
            message=f"failed to prepare the generated refresh transaction: {exc}",
            repair=(
                "Restore write access to the main generated files and annotation "
                "report directory, then rerun the unchanged controller command."
            ),
        ) from exc
    return {
        "status": "prepared",
        "manual_state": manual_state,
        **(
            {"interrupted_transaction": recovered}
            if recovered is not None
            else {}
        ),
        **(
            {"discarded_interrupted_preparations": discarded_preparations}
            if discarded_preparations
            else {}
        ),
    }


def rollback_generated_refresh(
    *,
    main_root: Path,
    target_files: dict[str, str],
    report_directory: Path,
) -> dict[str, str]:
    transaction_root = transaction_root_for_attempt(report_directory)
    if path_is_link_like(transaction_root) or not transaction_root.is_dir():
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-transaction-missing",
            message="generated refresh transaction is missing during rollback",
            repair=(
                "Recover the generated bundle from the sealed attempt before "
                "snapshot before retrying symbolic execution."
            ),
        )
    _restore_transaction(
        main_root=main_root,
        target_files=target_files,
        transaction_root=transaction_root,
    )
    _discard_transaction(transaction_root)
    return {"status": "rolled-back"}


def commit_generated_refresh(
    *, target_files: dict[str, str], report_directory: Path
) -> dict[str, str]:
    transaction_root = transaction_root_for_attempt(report_directory)
    if path_is_link_like(transaction_root) or not transaction_root.is_dir():
        raise AnnotationRefreshError(
            category="structure",
            kind="annotation-refresh-transaction-missing",
            message="generated refresh transaction is missing during commit",
            repair=(
                "Rerun the unchanged controller symexec command so it can establish "
                "a complete refresh transaction."
            ),
        )
    manifest = _load_manifest(transaction_root, target_files)
    manifest["status"] = "committed"
    write_json(transaction_root / TRANSACTION_MANIFEST_NAME, manifest)
    _discard_transaction(transaction_root)
    return {"status": "committed"}
