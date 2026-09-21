#!/usr/bin/env python3
"""Publish a completed generated bundle with exact-file backups and recovery.

Symbolic execution runs in a separate directory. This transaction covers only
publication; a failed generator never removes or modifies canonical output.
"""

from __future__ import annotations

import json
import os
import shutil
import tempfile
from pathlib import Path
from typing import Any

from atomic_file import atomic_write_bytes
from path_utils import fixed_path_under, write_json
from symexec_tooling import (
    GENERATED_FILE_KEYS,
    _generated_output_failure,
    _lexical_regular_file_snapshot,
    _snapshot_text,
)

TRANSACTION_DIRECTORY_NAME = ".generated-refresh-transaction"
TRANSACTION_MANIFEST_NAME = "transaction.json"


class AnnotationRefreshError(RuntimeError):
    def __init__(
        self, *, kind: str, message: str,
        repair: str = "Restore the named file or its original backup, then rerun the unchanged symexec command.",
        category: str = "generated-output",
    ) -> None:
        super().__init__(message)
        self.category, self.kind, self.repair = category, kind, repair

    def failure(self) -> dict[str, str]:
        return {"category": self.category, "kind": self.kind, "message": str(self), "repair": self.repair}


def transaction_root_for_attempt(report_directory: Path) -> Path:
    return fixed_path_under(
        report_directory / TRANSACTION_DIRECTORY_NAME,
        report_directory, label="generated publication transaction",
    )


def _bundle(root: Path, target_files: dict[str, str]) -> dict[str, dict[str, Any]]:
    snapshots = {role: _lexical_regular_file_snapshot(root=root, relative=relative, label=f"publication {role}")
                 for role, relative in target_files.items()}
    for role, snapshot in snapshots.items():
        if snapshot.get("state") not in {"present", "missing"}:
            raise AnnotationRefreshError(
                kind="generated-output-path-invalid", message=f"{role}: {snapshot.get('message') or snapshot['state']}"
            )
    return snapshots


def generated_output_contents(root: Path, target_files: dict[str, str]) -> dict[str, bytes | None]:
    return file_contents(root, {role: target_files[role] for role in GENERATED_FILE_KEYS})


def file_contents(root: Path, files: dict[str, str]) -> dict[str, bytes | None]:
    return {role: snapshot.get("data") for role, snapshot in _bundle(root, files).items()}


def _expect_contents(root: Path, relative: str, expected: bytes | None) -> None:
    snapshot = _lexical_regular_file_snapshot(root=root, relative=relative, label="publication target")
    if snapshot.get("state") not in {"present", "missing"} or snapshot.get("data") != expected:
        raise ValueError(f"publication would overwrite an external edit: {relative}")


def _load_transaction(transaction: Path, target_files: dict[str, str]) -> dict[str, Any]:
    snapshot = _lexical_regular_file_snapshot(root=transaction, relative=TRANSACTION_MANIFEST_NAME, label="publication manifest")
    manifest = json.loads(_snapshot_text(snapshot, label="publication manifest"))
    if (not isinstance(manifest, dict) or set(manifest) != {"status", "files"}
        or manifest.get("status") not in {"prepared", "committed"}
        or not isinstance(manifest["files"], dict) or set(manifest["files"]) != set(target_files)):
        raise ValueError("invalid generated publication manifest")
    for role, record in manifest["files"].items():
        if (not isinstance(record, dict) or set(record) != {"relative_path", "original_present", "candidate_present"}
            or record["relative_path"] != target_files[role]
            or type(record["original_present"]) is not bool or type(record["candidate_present"]) is not bool):
            raise ValueError(f"invalid generated publication record: {role}")
    return manifest


def _saved_contents(transaction: Path, role: str, kind: str, present: bool) -> bytes | None:
    snapshot = _lexical_regular_file_snapshot(root=transaction, relative=f"{role}.{kind}", label="publication recovery file")
    if snapshot["state"] != ("present" if present else "missing"):
        raise ValueError(f"publication recovery file is missing or invalid: {role}.{kind}")
    return snapshot.get("data")


def _restore_transaction(main_root: Path, target_files: dict[str, str], transaction: Path, manifest: dict[str, Any]) -> None:
    current = file_contents(main_root, target_files)
    originals = {role: _saved_contents(transaction, role, "original", record["original_present"])
                 for role, record in manifest["files"].items()}
    candidates = {role: _saved_contents(transaction, role, "candidate", record["candidate_present"])
                  for role, record in manifest["files"].items()}
    for role in current:
        if current[role] not in (originals[role], candidates[role]):
            raise ValueError(f"publication recovery would overwrite an external edit: {target_files[role]}")
    for role, payload in originals.items():
        if current[role] == payload:
            continue
        destination = fixed_path_under(main_root / target_files[role], main_root, label="recovery target")
        def confirm_candidate() -> None:
            _expect_contents(main_root, target_files[role], candidates[role])
        if payload is None:
            confirm_candidate()
            destination.unlink()
        else:
            atomic_write_bytes(destination, payload, suffix=".generated-restore", validate_commit=confirm_candidate)


def recover_interrupted_refresh(
    *, main_root: Path, target_files: dict[str, str], transaction_root: Path,
) -> str | None:
    target_files = {role: target_files[role] for role in GENERATED_FILE_KEYS}
    try:
        transaction = fixed_path_under(transaction_root, transaction_root.parent, label="generated publication transaction")
        if not os.path.lexists(transaction):
            return None
        if not transaction.is_dir():
            raise ValueError(f"generated publication transaction is not a directory: {transaction}")
        manifest = _load_transaction(transaction, target_files)
        if manifest["status"] == "prepared":
            _restore_transaction(main_root, target_files, transaction, manifest)
            result = "rolled-back-interrupted"
        else:
            result = "discarded-committed"
        shutil.rmtree(transaction)
        return result
    except (OSError, ValueError, SystemExit) as exc:
        raise AnnotationRefreshError(category="tool" if isinstance(exc, OSError) else "structure", kind="generated-publication-recovery", message=str(exc)) from exc


def publish_generated_output(
    *, main_root: Path, target_files: dict[str, str], output_root: Path,
    report_directory: Path, expected: dict[str, bytes | None],
) -> dict[str, Any]:
    files = {role: target_files[role] for role in GENERATED_FILE_KEYS}
    generated = _bundle(output_root, files)
    failure = _generated_output_failure({"target_files": target_files}, output_root, snapshots=generated)
    if failure:
        raise AnnotationRefreshError(**{key: failure[key] for key in ("category", "kind", "message", "repair")})
    payloads: dict[str, bytes | None] = {}
    for role, snapshot in generated.items():
        if snapshot["state"] == "missing":
            payloads[role] = None
            continue
        text = _snapshot_text(snapshot, label=f"generated {role}")
        for source, destination in (
            (str(output_root), str(main_root)), (output_root.as_posix(), main_root.as_posix()),
            (str(output_root).replace("/", "\\"), str(main_root).replace("/", "\\")),
        ):
            text = text.replace(source, destination)
        payloads[role] = text.replace("\r\n", "\n").encode("utf-8")
    return publish_file_contents(main_root=main_root, target_files=files, payloads=payloads,
                                 transaction=transaction_root_for_attempt(report_directory), expected=expected)


def publish_file_contents(
    *, main_root: Path, target_files: dict[str, str], payloads: dict[str, bytes | None],
    transaction: Path, expected: dict[str, bytes | None] | None = None, keep_backup: bool = False,
) -> dict[str, Any]:
    transaction = fixed_path_under(transaction, main_root, label="publication transaction")
    report_directory = transaction.parent
    report_directory.mkdir(parents=True, exist_ok=True)
    if os.path.lexists(transaction):
        raise AnnotationRefreshError(kind="publication-pending", message="Recover the existing publication before writing another candidate.")
    if set(target_files) != set(payloads):
        raise ValueError("publication payload roles differ from the fixed targets")
    manifest: dict[str, Any] | None = None
    try:
        originals = _bundle(main_root, target_files)
        if expected is None:
            expected = {role: item.get("data") for role, item in originals.items()}
        if {role: item.get("data") for role, item in originals.items()} != expected:
            raise ValueError("canonical generated files changed while symbolic execution was running")
        manifest = {
            "status": "prepared",
            "files": {
                role: {"relative_path": target_files[role], "original_present": originals[role]["state"] == "present",
                       "candidate_present": payload is not None}
                for role, payload in payloads.items()
            },
        }
        # Building the backup cannot alter main-root files. Its atomic rename
        # makes only a complete backup visible to recovery after a crash.
        with tempfile.TemporaryDirectory(prefix=".publish-", dir=report_directory) as temporary:
            preparation = Path(temporary) / "transaction"
            preparation.mkdir()
            for role, snapshot in originals.items():
                if snapshot["state"] == "present":
                    atomic_write_bytes(preparation / f"{role}.original", snapshot["data"])
            for role, payload in payloads.items():
                if payload is not None:
                    atomic_write_bytes(preparation / f"{role}.candidate", payload)
            write_json(preparation / TRANSACTION_MANIFEST_NAME, manifest)
            os.replace(preparation, transaction)
        for role, payload in payloads.items():
            destination = fixed_path_under(main_root / target_files[role], main_root, label="generated publication target")
            current = _lexical_regular_file_snapshot(root=main_root, relative=target_files[role], label="generated publication target")
            if current.get("state") not in {"present", "missing"} or current.get("data") != expected[role]:
                raise ValueError(f"generated publication conflict: {target_files[role]}")
            if current.get("data") == payload:
                continue
            def confirm_original() -> None:
                _expect_contents(main_root, target_files[role], expected[role])

            if payload is None:
                confirm_original()
                destination.unlink()
            else:
                atomic_write_bytes(destination, payload, suffix=".generated-publish", validate_commit=confirm_original)
        manifest["status"] = "committed"
        write_json(transaction / TRANSACTION_MANIFEST_NAME, manifest)
    except (OSError, ValueError, SystemExit, AnnotationRefreshError) as exc:
        if manifest is not None and os.path.lexists(transaction):
            try:
                _restore_transaction(main_root, target_files, transaction, _load_transaction(transaction, target_files))
                shutil.rmtree(transaction)
            except (OSError, ValueError, SystemExit, AnnotationRefreshError) as recovery_error:
                raise AnnotationRefreshError(kind="generated-publication-recovery", message=f"{exc}; recovery: {recovery_error}") from exc
        if isinstance(exc, AnnotationRefreshError):
            raise
        raise AnnotationRefreshError(category="tool" if isinstance(exc, OSError) else "generated-output", kind="generated-publication-failed", message=str(exc)) from exc
    result: dict[str, Any] = {"status": "committed"}
    if keep_backup:
        return result
    try:
        shutil.rmtree(transaction)
    except OSError as exc:
        # The committed marker makes deferred backup cleanup safe on restart.
        result["cleanup_diagnostic"] = str(exc)
    return result


def rollback_publication(*, main_root: Path, target_files: dict[str, str], transaction: Path) -> None:
    transaction = fixed_path_under(transaction, main_root, label="publication recovery")
    _restore_transaction(main_root, target_files, transaction, _load_transaction(transaction, target_files))
