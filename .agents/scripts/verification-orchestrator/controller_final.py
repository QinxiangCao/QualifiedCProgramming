#!/usr/bin/env python3
"""Apply the accepted proving_merged candidate and perform final checks.

This module is internal to controller.py and is the only implementation that
copies an accepted proof candidate back to the formal main-root paths.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import stat
import uuid
from contextlib import nullcontext
from pathlib import Path
from typing import Any

from atomic_file import atomic_write_bytes
from controller_artifacts import validate_artifact_payload
from controller_attempts import (
    _artifact_integrity_errors,
    _proving_manifest_errors,
    _public_helper_pool_errors,
)
from controller_rounds import VC_PROVING_PHASE, _accepted_group_ids
from controller_state import (
    _annotation_after_snapshot_errors,
    _append_event,
    _file_digest,
    _is_relative_to,
    _json_load,
    _load_state,
    _run_root_from_id,
    _save_state,
    _utc,
    _validated_annotation_attempt_paths,
    _validated_proving_attempt_paths,
)
from coq_tooling import audit_formal_case_lib_closure, run_coqc_check
from path_utils import (
    fixed_path_under,
    path_is_link_like,
    run_builds_root,
    write_bytes,
)
from prepare_group_workers import (
    resolve_group_workers_manifest,
)
from proof_manual_utils import (
    ASSUMPTION_DECLARATION_KINDS,
    PROOF_DECLARATION_KINDS,
    forbidden_top_level_declarations,
    incomplete_proof_markers,
    mask_coq_strings,
    parse_manual_file,
    partition_manual_lemmas,
    proof_mode_errors,
    rollback_control_commands,
    strip_coq_comments,
    top_level_commands,
    unsafe_assumption_declarations,
    unsafe_typing_commands,
)
from symexec_tooling import clean_output_freshness, run_symexec
from verify_group_results import FORBIDDEN_TOKENS


def _block_final_apply(
    run_root: Path,
    state: dict[str, Any],
    *,
    reason: str,
    blocker: dict[str, Any],
    event: str,
) -> int:
    """Consume an unrecoverable apply action without stranding formal files.

    Candidate/provenance failures cannot be repaired by repeatedly applying
    the same bytes.  Persisting the existing ``blocked`` result is therefore
    part of the final-apply boundary: ``step`` remains idle and the rolled-back
    main-root files are not captured as a new transaction baseline.  If an
    earlier process already began replacement, the same helper first restores
    its sealed backups.
    """

    transaction = state.get("final_apply_transaction")
    rollback_evidence: dict[str, Any] | None = None
    if isinstance(transaction, dict):
        transaction_status = str(transaction.get("status") or "")
        if transaction_status in {"backed-up", "completed"}:
            # A process can fail after replacing only the first formal target.
            # Once immutable backups are sealed, every later integrity blocker
            # must use them before stopping; merely consuming the action would
            # leave main root in a permanently half-applied state.
            try:
                main_root = Path(str(state["main_root"]))
                backup_root = fixed_path_under(
                    Path(str(state["report_root"])) / "final-check" / "backup",
                    main_root,
                    label="final-check backup directory",
                )
                rollback = _rollback(
                    state=state,
                    main_root=main_root,
                    backup_root=backup_root,
                )
                rollback_errors = [str(item) for item in rollback.get("errors", [])]
                rollback_evidence = {
                    "status": str(rollback.get("status") or "failed"),
                    "error_count": len(rollback_errors),
                    **({"first_error": rollback_errors[0]} if rollback_errors else {}),
                }
            except (KeyError, OSError, TypeError, ValueError, SystemExit) as exc:
                rollback_evidence = {
                    "status": "failed",
                    "error_count": 1,
                    "first_error": str(exc),
                }
            transaction["status"] = (
                "rolled-back"
                if rollback_evidence["status"] == "passed"
                else "rollback-failed"
            )
        elif transaction_status not in {"rolled-back", "rollback-failed"}:
            # ``prepared`` is durably saved before backups and before the first
            # formal replacement, so there is nothing to restore in that state.
            transaction["status"] = "blocked"
    final_apply_result: dict[str, Any] = {"status": "blocked", "reason": reason}
    if rollback_evidence is not None:
        blocker["rollback"] = rollback_evidence
        final_apply_result["rollback"] = rollback_evidence
    state["final_apply"] = final_apply_result
    state["current_blockers"] = [blocker]
    state["next_actions"] = []
    _append_event(
        run_root,
        state,
        event,
        failure_class=str(blocker.get("failure_class") or reason),
    )
    _save_state(run_root, state)
    print(json.dumps({"status": "blocked", "blocker": blocker}, indent=2))
    return 1


def _fixed_main_target(main_root: Path, relative: str) -> Path:
    """Return a formal destination without following repository links."""

    try:
        return fixed_path_under(
            Path(relative), main_root, label="final formal target path"
        )
    except SystemExit as exc:
        raise SystemExit(
            f"final target path uses a symlink or escapes main root: {relative}; {exc}"
        ) from exc


def _rollback_main_target(main_root: Path, relative: str) -> Path:
    """Validate a formal target parent while leaving its replaceable leaf lexical."""

    relative_path = Path(relative)
    if (
        relative_path.is_absolute()
        or ".." in relative_path.parts
        or not relative_path.name
    ):
        raise SystemExit(f"invalid final rollback target: {relative}")
    parent = fixed_path_under(
        main_root / relative_path.parent,
        main_root,
        label="final rollback target parent",
    )
    return parent / relative_path.name


def _nullable_sha256(value: Any, *, label: str) -> str | None:
    if value is None:
        return None
    if isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value):
        return value
    raise ValueError(f"{label} must be sha256 or null")


def _source_goal_generated_record(
    source_goal: dict[str, Any],
    *,
    role: str,
    relative_path: str,
) -> dict[str, Any]:
    raw_records = source_goal.get("generated_files")
    if not isinstance(raw_records, list):
        raise TypeError("source_goal_version generated_files is invalid")
    matches = [
        record
        for record in raw_records
        if isinstance(record, dict) and record.get("role") == role
    ]
    if len(matches) != 1:
        raise ValueError(
            f"source_goal_version requires exactly one generated record for {role}"
        )
    record = matches[0]
    if (
        set(record) != {"relative_path", "role", "state", "sha256"}
        or record.get("relative_path") != relative_path
        or record.get("state") not in {"present", "missing"}
    ):
        raise ValueError(f"source_goal_version generated record is invalid for {role}")
    digest = record.get("sha256")
    if record["state"] == "present":
        _nullable_sha256(digest, label=f"source_goal_version {role} digest")
        if digest is None:
            raise ValueError(f"present source_goal_version {role} has null digest")
    elif digest is not None:
        raise ValueError(f"missing source_goal_version {role} has a digest")
    return record


def _source_version_file_record(
    source_version: dict[str, Any],
    *,
    role: str,
    relative_path: str,
) -> dict[str, Any]:
    raw_records = source_version.get("files")
    if not isinstance(raw_records, list):
        raise TypeError("source_version files are invalid")
    matches = [
        record
        for record in raw_records
        if isinstance(record, dict)
        and record.get("relative_path") == relative_path
    ]
    if len(matches) != 1:
        raise ValueError(
            f"source_version requires exactly one file record for {relative_path}"
        )
    record = matches[0]
    if (
        set(record) != {"relative_path", "role", "state", "sha256"}
        or record.get("role") != role
        or record.get("state") not in {"present", "missing"}
    ):
        raise ValueError(f"source_version file record is invalid for {relative_path}")
    digest = record.get("sha256")
    if record["state"] == "present":
        _nullable_sha256(digest, label=f"source_version {role} digest")
        if digest is None:
            raise ValueError(f"present source_version {role} has null digest")
    elif digest is not None:
        raise ValueError(f"missing source_version {role} has a digest")
    return record


def _validated_base_seed_digests(
    base: Any,
    *,
    target_files: dict[str, Any],
    source_goal: dict[str, Any],
    source_version: dict[str, Any],
) -> tuple[str | None, str | None]:
    if not isinstance(base, dict) or set(base) != {
        "source_goal_version",
        "proof_manual",
        "formal_case_lib",
        "seed_sha256",
    }:
        raise ValueError("accepted base manifest fields are invalid")
    source_goal_digest = _nullable_sha256(
        source_goal.get("digest"), label="source_goal_version digest"
    )
    if (
        source_goal_digest is None
        or base.get("source_goal_version") != source_goal_digest
        or base.get("proof_manual") != target_files.get("proof_manual_file")
        or base.get("formal_case_lib") != target_files.get("formal_case_lib")
    ):
        raise ValueError("accepted base manifest provenance or target paths differ")
    seed = base.get("seed_sha256")
    if not isinstance(seed, dict) or set(seed) != {
        "proof_manual",
        "formal_case_lib",
    }:
        raise ValueError("accepted base manifest seed_sha256 is invalid")
    seed_manual_digest = _nullable_sha256(
        seed.get("proof_manual"), label="base manual seed digest"
    )
    seed_lib_digest = _nullable_sha256(
        seed.get("formal_case_lib"), label="base lib seed digest"
    )
    manual_record = _source_goal_generated_record(
        source_goal,
        role="proof_manual_file",
        relative_path=str(target_files["proof_manual_file"]),
    )
    lib_record = _source_version_file_record(
        source_version,
        role="formal-case-lib",
        relative_path=str(target_files["formal_case_lib"]),
    )
    if seed_manual_digest != manual_record.get("sha256"):
        raise ValueError(
            "accepted base manual seed differs from source_goal_version"
        )
    if seed_lib_digest != lib_record.get("sha256"):
        raise ValueError("accepted base lib seed differs from source_version")
    return seed_manual_digest, seed_lib_digest


def _optional_artifact_matches(path: Path, digest: str | None) -> bool:
    if digest is None:
        return not _lexists(path)
    try:
        return _regular_file_digest(path, label="optional final artifact") == digest
    except (OSError, ValueError):
        return False


def _accepted_group_artifact_paths(group: dict[str, Any]) -> dict[str, Path]:
    report_directory = Path(str(group.get("report_directory") or ""))
    paths = {
        "report": report_directory / "group_worker_report.json",
        "proof_manual": Path(str(group.get("proof_manual") or "")),
    }
    group_worker_lib = group.get("group_worker_lib")
    if isinstance(group_worker_lib, str) and group_worker_lib:
        paths["group_worker_lib"] = Path(group_worker_lib)
    return paths


def _accepted_proving_integrity_errors_unchecked(state: dict[str, Any]) -> list[str]:
    accepted = state.get("accepted_rounds", {}).get(VC_PROVING_PHASE, {})
    round_id = str(accepted.get("round") or "")
    proving = state.get("attempts", {}).get(round_id)
    if not round_id or not isinstance(proving, dict):
        return ["accepted vc-proving attempt is missing"]
    try:
        proving_paths = _validated_proving_attempt_paths(state, proving)
    except (OSError, ValueError) as exc:
        return [f"accepted vc-proving attempt path topology is invalid: {exc}"]
    errors = _proving_manifest_errors(state, proving)
    errors.extend(_public_helper_pool_errors(state))
    if accepted.get("attempt_id") != proving.get("attempt_id"):
        errors.append("accepted vc-proving pointer does not match its attempt")
    result_path = proving_paths["proving_merged_result"]
    expected_result_sha256 = str(proving.get("verified_result_sha256") or "")
    if accepted.get("result_sha256") != expected_result_sha256:
        errors.append("accepted vc-proving result seal does not match its attempt")
    if (
        not expected_result_sha256
        or not result_path.is_file()
        or _file_digest(result_path) != expected_result_sha256
    ):
        errors.append(
            "accepted proving_merged_result changed after parent verification"
        )
    else:
        try:
            merged_result = _json_load(result_path, {})
            merge_result_errors = validate_artifact_payload(
                "merge-result", merged_result
            )
            if merge_result_errors:
                raise ValueError(merge_result_errors[0])
            merged_candidate = (
                merged_result.get("candidate")
                if isinstance(merged_result, dict)
                else None
            )
            if (
                not isinstance(merged_result, dict)
                or merged_result.get("status") != "passed"
                or merged_result.get("source_goal_version")
                != state.get("source_goal_version", {}).get("digest")
                or not isinstance(merged_candidate, dict)
            ):
                raise ValueError("accepted proving_merged_result candidate is invalid")
            candidate_digests = {
                "proof_manual_file": _nullable_sha256(
                    merged_candidate.get("proof_manual_sha256"),
                    label="accepted merged manual digest",
                ),
                "formal_case_lib": _nullable_sha256(
                    merged_candidate.get("proving_merged_lib_sha256"),
                    label="accepted merged lib digest",
                ),
            }
            proving_directory = proving_paths["directory"]
            base_path = proving_paths["base_manifest"]
            seed_manual_digest, seed_lib_digest = _validated_base_seed_digests(
                _json_load(base_path, {}),
                target_files=state["target_files"],
                source_goal=state["source_goal_version"],
                source_version=state["source_version"],
            )
            if (candidate_digests["proof_manual_file"] is None) != (
                seed_manual_digest is None
            ) or (candidate_digests["formal_case_lib"] is None) != (
                seed_lib_digest is None
            ):
                raise ValueError(
                    "accepted merged candidate topology differs from its sealed base"
                )
            merged_directory = fixed_path_under(
                proving_directory / "proving_merged",
                proving_directory,
                label="accepted proving_merged directory",
            )
            expected_candidate_paths: set[Path] = set()
            for role, digest in candidate_digests.items():
                source = fixed_path_under(
                    merged_directory
                    / Path(str(state["target_files"][role])).name,
                    merged_directory,
                    label=f"accepted merged {role}",
                )
                if digest is None:
                    if _lexists(source):
                        errors.append(
                            f"absent accepted candidate has an unexpected file: {source}"
                        )
                else:
                    expected_candidate_paths.add(source)
                    if _regular_file_digest(
                        source, label=f"accepted merged {role}"
                    ) != digest:
                        errors.append(f"accepted merged candidate changed: {source}")
            actual_candidate_paths = set(merged_directory.iterdir())
            if actual_candidate_paths != expected_candidate_paths:
                unexpected = sorted(
                    actual_candidate_paths - expected_candidate_paths,
                    key=lambda path: path.name,
                )
                missing = sorted(
                    expected_candidate_paths - actual_candidate_paths,
                    key=lambda path: path.name,
                )
                errors.append(
                    "accepted proving_merged directory topology changed: "
                    + (
                        f"unexpected {unexpected[0]}"
                        if unexpected
                        else f"missing {missing[0]}"
                    )
                )
            final_candidate = state.get("final_candidate")
            if (
                not isinstance(final_candidate, dict)
                or set(final_candidate)
                != {
                    "round",
                    "proving_merged_result",
                    "result_sha256",
                    "proof_manual_sha256",
                    "proving_merged_lib_sha256",
                }
            ):
                errors.append("controller state final candidate is missing")
            elif (
                final_candidate.get("round") != round_id
                or final_candidate.get("round") != accepted.get("attempt_id")
                or final_candidate.get("proof_manual_sha256")
                != candidate_digests["proof_manual_file"]
                or final_candidate.get("proving_merged_lib_sha256")
                != candidate_digests["formal_case_lib"]
                or final_candidate.get("result_sha256") != expected_result_sha256
                or final_candidate.get("proving_merged_result") != str(result_path)
            ):
                errors.append(
                    "controller state final candidate differs from accepted merge result"
                )
        except (KeyError, OSError, TypeError, UnicodeError, ValueError, SystemExit) as exc:
            errors.append(f"accepted merged candidate could not be revalidated: {exc}")
    try:
        manifest = resolve_group_workers_manifest(
            proving_paths["group_workers_manifest"],
            main_root=Path(str(state["main_root"])),
            validate_current_seed=False,
            expected_run_root=Path(str(state["run_root"])),
            expected_round=str(proving["round"]),
        )
    except (OSError, TypeError, UnicodeError, ValueError, SystemExit):
        manifest = {}
    if (
        not isinstance(manifest, dict)
        or manifest.get("source_goal_version")
        != state.get("source_goal_version", {}).get("digest")
    ):
        errors.append("accepted group_workers_manifest is invalid or stale")
    else:
        manifest_groups = {
            str(group.get("id") or ""): group
            for group in manifest.get("groups", [])
            if isinstance(group, dict) and group.get("id")
        }
        accepted_groups = _accepted_group_ids(proving)
        if accepted_groups != set(manifest_groups):
            errors.append("accepted group set no longer covers the worker manifest")
        for group_id in sorted(accepted_groups & set(manifest_groups)):
            group = manifest_groups[group_id]
            group_state = proving.get("groups", {}).get(group_id, {})
            artifact_paths = _accepted_group_artifact_paths(group)
            artifact_seals = (
                group_state.get("accepted_artifact_sha256")
                if isinstance(group_state, dict)
                else None
            )
            if not isinstance(artifact_seals, dict) or set(artifact_seals) != set(
                artifact_paths
            ):
                errors.append(
                    f"accepted group `{group_id}`: artifact seal fields differ from topology"
                )
            group_errors = _artifact_integrity_errors(
                artifact_paths,
                artifact_seals,
                main_root=Path(str(state["main_root"])),
            )
            errors.extend(
                f"accepted group `{group_id}`: {error}" for error in group_errors
            )
    return errors


def _accepted_proving_integrity_errors(state: dict[str, Any]) -> list[str]:
    """Return integrity errors even when a sealed artifact is unreadable.

    These checks run after the accepted candidate may already be in main root.
    A malformed JSON file, invalid path, or read failure must therefore become
    rollback evidence rather than escape past final-check and strand the
    applied files behind a repeatedly failing command.
    """

    try:
        return _accepted_proving_integrity_errors_unchecked(state)
    except (KeyError, OSError, TypeError, UnicodeError, ValueError, SystemExit) as exc:
        return [f"accepted proving artifacts could not be revalidated: {exc}"]


def _lexists(path: Path) -> bool:
    return os.path.lexists(os.fspath(path))


def _regular_file_digest(path: Path, *, label: str) -> str:
    try:
        metadata = path.lstat()
    except FileNotFoundError as exc:
        raise ValueError(f"{label} is missing: {path}") from exc
    if path_is_link_like(path) or not stat.S_ISREG(metadata.st_mode):
        raise ValueError(f"{label} must be a fixed regular file: {path}")
    return _file_digest(path)


def _atomic_replace_formal_target(
    target: Path, payload: bytes, *, main_root: Path, label: str
) -> None:
    """Replace a formal leaf without opening/following the old leaf.

    Rollback may encounter a target leaf swapped to a symlink after apply.
    Validating the parent and replacing the directory entry is safe: the
    external symlink target is never opened, while the canonical formal path is
    restored to a regular file.
    """

    parent = fixed_path_under(target.parent, main_root, label=f"{label} parent")
    lexical_target = parent / target.name
    atomic_write_bytes(lexical_target, payload, suffix=".restore")


def _transaction_records(
    targets: list[tuple[Path, Path]],
    *,
    main_root: Path,
    backup_root: Path,
    transaction_id: str,
) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    transaction_backup_root = fixed_path_under(
        backup_root / transaction_id,
        backup_root,
        label="final-apply transaction backup directory",
    )
    for source, target in targets:
        source_sha256 = _regular_file_digest(source, label="final candidate")
        relative = target.relative_to(main_root)
        backup = fixed_path_under(
            transaction_backup_root / relative,
            transaction_backup_root,
            label="final-apply backup file",
        )
        if _lexists(target):
            before_sha256 = _regular_file_digest(target, label="formal target")
            existed = True
        else:
            before_sha256 = None
            existed = False
        records.append(
            {
                "source": str(source),
                "source_sha256": source_sha256,
                "target": str(target),
                "relative_path": relative.as_posix(),
                "existed": existed,
                "before_sha256": before_sha256,
                "backup": str(backup),
            }
        )
    return records


def _expected_transaction_records(
    state: dict[str, Any],
    *,
    main_root: Path,
    backup_root: Path,
    transaction_id: str,
) -> list[dict[str, Any]]:
    """Derive the only formal destinations a final transaction may name."""

    candidate = state.get("final_candidate")
    if not isinstance(candidate, dict) or set(candidate) != {
        "round",
        "proving_merged_result",
        "result_sha256",
        "proof_manual_sha256",
        "proving_merged_lib_sha256",
    }:
        raise ValueError("final candidate cannot authorize transaction targets")
    accepted = state.get("accepted_rounds", {}).get(VC_PROVING_PHASE, {})
    round_id = str(candidate.get("round") or "")
    if (
        not round_id
        or candidate.get("round") != accepted.get("round")
        or candidate.get("round") != accepted.get("attempt_id")
    ):
        raise ValueError("final candidate is not the accepted proving round")
    proving = state.get("attempts", {}).get(round_id)
    if not isinstance(proving, dict):
        raise ValueError("accepted proving attempt is missing")
    run_root = fixed_path_under(
        Path(str(state.get("run_root") or "")),
        main_root,
        label="final transaction run root",
    )
    accepted_directory = fixed_path_under(
        Path(str(proving.get("directory") or "")),
        run_root,
        label="final transaction accepted proving directory",
    )
    merged_directory = fixed_path_under(
        accepted_directory / "proving_merged",
        accepted_directory,
        label="final transaction proving_merged directory",
    )
    target_files = state.get("target_files")
    if not isinstance(target_files, dict):
        raise ValueError("controller target_files cannot authorize final transaction")
    source_goal = state.get("source_goal_version")
    source_version = state.get("source_version")
    if not isinstance(source_goal, dict) or not isinstance(source_version, dict):
        raise ValueError("accepted annotation versions cannot authorize rollback")
    manual_before = _source_goal_generated_record(
        source_goal,
        role="proof_manual_file",
        relative_path=str(target_files.get("proof_manual_file") or ""),
    )
    lib_before = _source_version_file_record(
        source_version,
        role="formal-case-lib",
        relative_path=str(target_files.get("formal_case_lib") or ""),
    )
    candidate_specs = (
        (
            str(target_files.get("proof_manual_file") or ""),
            _nullable_sha256(
                candidate.get("proof_manual_sha256"),
                label="final transaction manual digest",
            ),
            manual_before,
        ),
        (
            str(target_files.get("formal_case_lib") or ""),
            _nullable_sha256(
                candidate.get("proving_merged_lib_sha256"),
                label="final transaction lib digest",
            ),
            lib_before,
        ),
    )
    expected: list[dict[str, Any]] = []
    transaction_backup_root = fixed_path_under(
        backup_root / transaction_id,
        backup_root,
        label="final transaction backup directory",
    )
    for relative, digest, before_record in candidate_specs:
        before_digest = _nullable_sha256(
            before_record.get("sha256"),
            label="accepted pre-apply formal digest",
        )
        if digest is None:
            if before_record.get("state") != "missing" or before_digest is not None:
                raise ValueError(
                    "null final candidate differs from accepted annotation topology"
                )
            continue
        if before_record.get("state") != "present" or before_digest is None:
            raise ValueError(
                "present final candidate differs from accepted annotation topology"
            )
        # Transaction topology must remain recognizable even when an applied
        # leaf is later swapped to a symlink or another invalid entry.  Normal
        # apply/backup paths separately require a fixed regular target; the
        # rollback validator binds the safe parent plus the lexical leaf so it
        # can replace that entry without ever following its referent.
        target = _rollback_main_target(main_root, relative)
        source = fixed_path_under(
            merged_directory / Path(relative).name,
            merged_directory,
            label="final transaction candidate source",
        )
        backup = fixed_path_under(
            transaction_backup_root / relative,
            transaction_backup_root,
            label="final transaction backup file",
        )
        expected.append(
            {
                "source": str(source),
                "source_sha256": digest,
                "target": str(target),
                "relative_path": target.relative_to(main_root).as_posix(),
                "backup": str(backup),
                "existed": True,
                "before_sha256": before_digest,
            }
        )
    return expected


def _validated_final_apply_transaction(
    state: dict[str, Any],
    *,
    main_root: Path,
    backup_root: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Validate exact transaction schema/topology before any root mutation."""

    transaction = state.get("final_apply_transaction")
    if not isinstance(transaction, dict):
        raise ValueError("final-apply transaction is missing")
    base_fields = {
        "transaction_id",
        "status",
        "source_goal_version",
        "records",
        "prepared_at",
    }
    status = str(transaction.get("status") or "")
    expected_fields = set(base_fields)
    if status == "backed-up":
        expected_fields.add("backed_up_at")
    elif status == "completed":
        expected_fields.update({"backed_up_at", "completed_at"})
    elif status in {"rolled-back", "rollback-failed"}:
        expected_fields.add("backed_up_at")
        if "completed_at" in transaction:
            expected_fields.add("completed_at")
    elif status not in {"prepared", "blocked"}:
        raise ValueError("final-apply transaction status is invalid")
    if set(transaction) != expected_fields:
        raise ValueError("final-apply transaction has unsupported or missing fields")
    transaction_id = transaction.get("transaction_id")
    if not isinstance(transaction_id, str) or re.fullmatch(
        r"[0-9a-f]{32}", transaction_id
    ) is None:
        raise ValueError("final-apply transaction id is invalid")
    for timestamp_field in expected_fields & {
        "prepared_at",
        "backed_up_at",
        "completed_at",
    }:
        if not isinstance(transaction.get(timestamp_field), str) or not str(
            transaction[timestamp_field]
        ):
            raise ValueError(
                f"final-apply transaction {timestamp_field} is invalid"
            )
    source_goal_digest = str(
        (state.get("source_goal_version") or {}).get("digest") or ""
    )
    if (
        re.fullmatch(r"[0-9a-f]{64}", source_goal_digest) is None
        or transaction.get("source_goal_version") != source_goal_digest
    ):
        raise ValueError("final-apply transaction source_goal_version is stale")
    records = transaction.get("records")
    if not isinstance(records, list):
        raise ValueError("final-apply transaction records are invalid")
    expected_records = _expected_transaction_records(
        state,
        main_root=main_root,
        backup_root=backup_root,
        transaction_id=transaction_id,
    )
    if len(records) != len(expected_records):
        raise ValueError(
            "final-apply transaction record topology differs from the candidate"
        )
    backups_required = status in {
        "backed-up",
        "completed",
        "rolled-back",
        "rollback-failed",
    }
    record_fields = {
        "source",
        "source_sha256",
        "target",
        "relative_path",
        "existed",
        "before_sha256",
        "backup",
    }
    for index, (record, expected) in enumerate(
        zip(records, expected_records, strict=True)
    ):
        if not isinstance(record, dict) or set(record) != record_fields:
            raise ValueError(
                f"final-apply transaction record {index} has invalid fields"
            )
        for field, expected_value in expected.items():
            if record.get(field) != expected_value:
                raise ValueError(
                    "final-apply transaction record does not match the exact "
                    f"candidate topology: {field}"
                )
        if not isinstance(record.get("existed"), bool):
            raise ValueError("final-apply transaction existed flag is invalid")
        before_digest = _nullable_sha256(
            record.get("before_sha256"),
            label="final-apply transaction before digest",
        )
        if bool(record["existed"]) != (before_digest is not None):
            raise ValueError(
                "final-apply transaction before digest contradicts existed state"
            )
        backup = Path(expected["backup"])
        if record["existed"]:
            if _lexists(backup):
                if _regular_file_digest(
                    backup,
                    label="final-apply transaction backup",
                ) != before_digest:
                    raise ValueError("final-apply transaction backup digest changed")
            elif backups_required:
                raise ValueError("final-apply transaction backup is missing")
        elif _lexists(backup):
            raise ValueError(
                "final-apply transaction has a backup for an originally absent target"
            )
    return transaction, records


def _ensure_transaction_backups(
    records: list[dict[str, Any]], *, main_root: Path, backup_root: Path
) -> None:
    for record in records:
        target = _fixed_main_target(main_root, str(record["relative_path"]))
        backup = fixed_path_under(
            Path(str(record["backup"])),
            backup_root,
            label="final-apply backup file",
        )
        if not record.get("existed"):
            if _lexists(backup):
                raise ValueError(
                    f"unexpected backup exists for an originally absent target: {backup}"
                )
            continue
        expected = str(record.get("before_sha256") or "")
        if _lexists(backup):
            if _regular_file_digest(backup, label="final-apply backup") != expected:
                raise ValueError(f"final-apply backup digest changed: {backup}")
            continue
        if (
            _regular_file_digest(target, label="formal target before backup")
            != expected
        ):
            raise ValueError(
                f"formal target changed before its durable backup was created: {target}"
            )
        write_bytes(
            backup,
            target.read_bytes(),
            label="final-apply immutable backup",
        )
        if _regular_file_digest(backup, label="final-apply backup") != expected:
            raise ValueError(f"final-apply backup write was not exact: {backup}")


def _rollback(
    *,
    state: dict[str, Any],
    main_root: Path,
    backup_root: Path,
) -> dict[str, Any]:
    with nullcontext():
        _transaction, records = _validated_final_apply_transaction(
            state,
            main_root=main_root,
            backup_root=backup_root,
        )
        restored: list[str] = []
        errors: list[str] = []
        for record in records:
            target = Path(str(record.get("target") or "<unknown-final-target>"))
            try:
                relative_path = str(record["relative_path"])
                target = _rollback_main_target(main_root, relative_path)
                if record["existed"]:
                    backup = fixed_path_under(
                        Path(str(record["backup"])),
                        backup_root,
                        label="final-apply rollback backup",
                    )
                    expected = str(record["before_sha256"])
                    if (
                        _regular_file_digest(backup, label="rollback backup")
                        != expected
                    ):
                        raise ValueError(f"rollback backup digest changed: {backup}")
                    _atomic_replace_formal_target(
                        target,
                        backup.read_bytes(),
                        main_root=main_root,
                        label="formal rollback target",
                    )
                    if (
                        _regular_file_digest(target, label="restored formal target")
                        != expected
                    ):
                        raise ValueError(f"rollback target digest mismatch: {target}")
                elif _lexists(target):
                    # The validated exact leaf is removed directly; a symlink
                    # referent is never followed.
                    target.unlink()
                restored.append(str(target))
            except (OSError, ValueError, SystemExit) as exc:
                errors.append(f"{target}: {exc}")
    return {
        "status": "passed" if not errors else "failed",
        "restored": restored,
        "errors": errors,
    }


def final_apply(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    state = _load_state(run_root)
    if state.get("phase") != "final-candidate-apply":
        raise SystemExit(
            "final-apply requires the final-candidate-apply controller phase"
        )
    candidate = state.get("final_candidate")
    if not isinstance(candidate, dict):
        return _block_final_apply(
            run_root,
            state,
            reason="accepted-proving-integrity",
            blocker={
                "failure_class": "accepted-proving-integrity",
                "error_count": 1,
                "first_error": "final candidate is missing",
            },
            event="final-apply-accepted-proving-integrity-blocked",
        )
    existing_transaction = state.get("final_apply_transaction")
    annotation_findings = _accepted_annotation_source_findings(
        state,
        # Before the receipt exists, all six current files must still be the
        # accepted annotation originals.  On crash re-entry one or both formal
        # targets may already contain candidate bytes; the durable transaction
        # below validates those targets against its sealed before/source
        # digests, while this gate continues to protect C and goal/auto/check.
        require_preapply_state=not isinstance(existing_transaction, dict),
    )
    if annotation_findings:
        # The accepted annotation history is the provenance root for every
        # downstream proof.  A missing seal cannot be made trustworthy by
        # hashing mutable history at this late boundary.  Stop before creating
        # backups or replacing either main-root formal target.
        blocker = {
            "failure_class": "accepted-annotation-provenance",
            "finding_count": len(annotation_findings),
            "first_finding": annotation_findings[0],
        }
        return _block_final_apply(
            run_root,
            state,
            reason="accepted-annotation-provenance",
            blocker=blocker,
            event="final-apply-annotation-provenance-blocked",
        )
    integrity_errors = _accepted_proving_integrity_errors(state)
    if integrity_errors:
        parent_result_drift = any(
            "proving_merged_result changed after parent verification" in error
            for error in integrity_errors
        )
        blocker = {
            "failure_class": (
                "artifact-drift-after-parent-verification"
                if parent_result_drift
                else "accepted-proving-integrity"
            ),
            "error_count": len(integrity_errors),
            "first_error": integrity_errors[0],
        }
        accepted_round = str(
            state.get("accepted_rounds", {}).get(VC_PROVING_PHASE, {}).get("round")
            or ""
        )
        proving = state.get("attempts", {}).get(accepted_round)
        if parent_result_drift and isinstance(proving, dict):
            proving["parent_result_artifact_drift"] = blocker
        return _block_final_apply(
            run_root,
            state,
            reason="accepted-proving-integrity",
            blocker=blocker,
            event="final-apply-accepted-proving-integrity-blocked",
        )
    try:
        accepted = state.get("accepted_rounds", {}).get(VC_PROVING_PHASE, {})
        expected_candidate_fields = {
            "round",
            "proving_merged_result",
            "result_sha256",
            "proof_manual_sha256",
            "proving_merged_lib_sha256",
        }
        if set(candidate) != expected_candidate_fields:
            raise ValueError("final candidate has unsupported or missing fields")
        if (
            candidate.get("round") != accepted.get("round")
            or candidate.get("round") != accepted.get("attempt_id")
        ):
            raise ValueError("final candidate does not point to accepted vc-proving")
        proving = state.get("attempts", {}).get(str(candidate["round"]))
        if not isinstance(proving, dict):
            raise TypeError("accepted vc-proving attempt is missing")
        accepted_directory = fixed_path_under(
            Path(str(proving.get("directory", ""))),
            run_root,
            label="accepted vc-proving directory",
        )
        accepted_merged_directory = fixed_path_under(
            accepted_directory / "proving_merged",
            accepted_directory,
            label="accepted proving_merged directory",
        )
        target = state["target_files"]
        current_goal = str(state.get("source_goal_version", {}).get("digest") or "")
        if not current_goal or proving.get("source_goal_version") != current_goal:
            raise ValueError("final candidate source_goal_version is stale")
        if (
            candidate.get("proving_merged_result")
            != proving.get("proving_merged_result")
            or candidate.get("result_sha256") != accepted.get("result_sha256")
        ):
            raise ValueError("final candidate result pointer is not accepted")
        merge_result_path = fixed_path_under(
            Path(str(candidate.get("proving_merged_result", ""))),
            Path(str(state["report_root"])),
            label="accepted proving_merged result",
        )
        merge_result = _json_load(merge_result_path, {})
        merge_result_errors = validate_artifact_payload(
            "merge-result", merge_result
        )
        if merge_result_errors:
            raise ValueError(merge_result_errors[0])
        merged = merge_result if isinstance(merge_result, dict) else None
        merged_candidate = merged.get("candidate") if isinstance(merged, dict) else None
        merged_fields = {
            "status",
            "source_goal_version",
            "candidate",
            "group_count",
            "added_declarations",
        }
        if isinstance(merged, dict) and "proof_reuse" in merged:
            merged_fields.add("proof_reuse")
        if (
            not isinstance(merged, dict)
            or set(merged) != merged_fields
            or merged.get("status") != "passed"
            or merged.get("source_goal_version") != current_goal
            or not isinstance(merged_candidate, dict)
        ):
            raise ValueError("final candidate lacks an accepted proving_merged_result")
        if candidate.get("result_sha256") != _file_digest(merge_result_path):
            raise ValueError("final candidate result seal changed")
        if set(merged_candidate) != {
            "proof_manual_sha256",
            "proving_merged_lib_sha256",
        }:
            raise ValueError("proving_merged_result candidate fields are invalid")
        candidate_manual_digest = _nullable_sha256(
            candidate.get("proof_manual_sha256"),
            label="final manual digest",
        )
        candidate_lib_digest = _nullable_sha256(
            candidate.get("proving_merged_lib_sha256"),
            label="final lib digest",
        )
        merged_manual_digest = _nullable_sha256(
            merged_candidate.get("proof_manual_sha256"),
            label="merged manual digest",
        )
        merged_lib_digest = _nullable_sha256(
            merged_candidate.get("proving_merged_lib_sha256"),
            label="merged lib digest",
        )
        if candidate_manual_digest != merged_manual_digest:
            raise ValueError(
                "final manual digest is not pinned to proving_merged_result"
            )
        if candidate_lib_digest != merged_lib_digest:
            raise ValueError("final lib digest is not pinned to proving_merged_result")
        base_path = fixed_path_under(
            Path(str(proving.get("base_manifest") or "")),
            accepted_directory,
            label="accepted base manifest",
        )
        seed_manual_digest, seed_lib_digest = _validated_base_seed_digests(
            _json_load(base_path, {}),
            target_files=target,
            source_goal=state["source_goal_version"],
            source_version=state["source_version"],
        )
        if (seed_manual_digest is None) != (candidate_manual_digest is None):
            raise ValueError(
                "accepted manual topology differs between base and merged candidate"
            )
        if (seed_lib_digest is not None) != (candidate_lib_digest is not None):
            raise ValueError(
                "accepted formal_case_lib topology differs between base manifest and merged candidate"
            )

        candidate_specs = (
            (
                "proof manual",
                str(target["proof_manual_file"]),
                candidate_manual_digest,
            ),
            (
                "formal case library",
                str(target["formal_case_lib"]),
                candidate_lib_digest,
            ),
        )
        targets: list[tuple[Path, Path]] = []
        for label, relative, digest in candidate_specs:
            source = fixed_path_under(
                accepted_merged_directory / Path(relative).name,
                accepted_merged_directory,
                label=f"final candidate {label}",
            )
            destination = _fixed_main_target(main_root, relative)
            if digest is None:
                if _lexists(source):
                    raise ValueError(
                        f"absent {label} has an unexpected proving_merged file"
                    )
                if _lexists(destination):
                    raise ValueError(
                        f"absent {label} appeared before final apply: {destination}"
                    )
                continue
            if _regular_file_digest(source, label=f"final candidate {label}") != digest:
                raise ValueError(
                    f"final {label} digest does not match proving_merged_result"
                )
            if not _is_relative_to(source, accepted_merged_directory):
                raise ValueError(
                    f"final {label} candidate is outside proving_merged directory"
                )
            targets.append((source, destination))
        backup_root = fixed_path_under(
            Path(str(state["report_root"])) / "final-check" / "backup",
            main_root,
            label="final-check backup directory",
        )
    except (KeyError, OSError, TypeError, UnicodeError, ValueError, SystemExit) as exc:
        return _block_final_apply(
            run_root,
            state,
            reason="accepted-proving-integrity",
            blocker={
                "failure_class": "accepted-proving-integrity",
                "error_count": 1,
                "first_error": str(exc),
            },
            event="final-apply-accepted-proving-integrity-blocked",
        )

    transaction = existing_transaction
    if not isinstance(transaction, dict):
        try:
            transaction_id = uuid.uuid4().hex
            records = _transaction_records(
                targets,
                main_root=main_root,
                backup_root=backup_root,
                transaction_id=transaction_id,
            )
        except (OSError, TypeError, ValueError, SystemExit) as exc:
            return _block_final_apply(
                run_root,
                state,
                reason="accepted-proving-integrity",
                blocker={
                    "failure_class": "accepted-proving-integrity",
                    "error_count": 1,
                    "first_error": str(exc),
                },
                event="final-apply-accepted-proving-integrity-blocked",
            )
        transaction = {
            "transaction_id": transaction_id,
            "status": "prepared",
            "source_goal_version": current_goal,
            "records": records,
            "prepared_at": _utc(),
        }
        state["final_apply_transaction"] = transaction
        _append_event(
            run_root,
            state,
            "final-apply-transaction-prepared",
            transaction_id=transaction_id,
        )
        # No main-root target is touched before this recovery receipt is
        # durable. A crash after this commit can safely create or validate the
        # immutable backups on re-entry.
        _save_state(run_root, state)
    try:
        transaction, records = _validated_final_apply_transaction(
            state,
            main_root=main_root,
            backup_root=backup_root,
        )
        if transaction.get("status") not in {
            "prepared",
            "backed-up",
            "rolled-back",
        }:
            raise ValueError(
                "existing final-apply transaction is not in a re-applicable state"
            )
    except (OSError, TypeError, ValueError, SystemExit) as exc:
        return _block_final_apply(
            run_root,
            state,
            reason="accepted-proving-integrity",
            blocker={
                "failure_class": "accepted-proving-integrity",
                "error_count": 1,
                "first_error": str(exc),
            },
            event="final-apply-accepted-proving-integrity-blocked",
        )

    try:
        _ensure_transaction_backups(
            records,
            main_root=main_root,
            backup_root=backup_root,
        )
    except (OSError, ValueError, SystemExit) as exc:
        blocker = {
            "failure_class": "final-apply-backup-integrity",
            "message": str(exc),
            "transaction_id": str(transaction["transaction_id"]),
        }
        transaction["status"] = "blocked"
        state["final_apply"] = {
            "status": "blocked",
            "transaction_id": str(transaction["transaction_id"]),
        }
        state["current_blockers"] = [blocker]
        state["next_actions"] = []
        _append_event(run_root, state, "final-apply-backup-blocked", **blocker)
        _save_state(run_root, state)
        print(json.dumps({"status": "blocked", "blocker": blocker}, indent=2))
        return 1

    if transaction.get("status") != "backed-up":
        transaction.pop("completed_at", None)
        transaction["status"] = "backed-up"
        transaction["backed_up_at"] = _utc()
        _append_event(
            run_root,
            state,
            "final-apply-backups-sealed",
            transaction_id=str(transaction["transaction_id"]),
        )
        # This commit separates backup durability from the first formal-target
        # replacement.  Partial application can therefore always roll back to
        # the original digests recorded above.
        _save_state(run_root, state)

    copied: list[dict[str, Any]] = []
    try:
        for record, (source, target) in zip(records, targets, strict=True):
            source_sha256 = str(record["source_sha256"])
            current_sha256: str | None = None
            if _lexists(target):
                current_sha256 = _regular_file_digest(
                    target, label="formal target during final apply"
                )
            if current_sha256 == source_sha256:
                pass
            elif (
                record.get("existed") and current_sha256 == record.get("before_sha256")
            ) or (not record.get("existed") and current_sha256 is None):
                write_bytes(
                    target,
                    source.read_bytes(),
                    label="final formal candidate target",
                )
            else:
                raise ValueError(
                    f"formal target is neither the sealed original nor candidate: {target}"
                )
            if (
                _regular_file_digest(target, label="applied formal target")
                != source_sha256
            ):
                raise ValueError(f"final candidate copy digest mismatch: {target}")
            copied.append(
                {
                    "source": str(source),
                    "target": str(target),
                    "sha256": source_sha256,
                }
            )
    except (OSError, ValueError, SystemExit) as exc:
        try:
            rollback = _rollback(
                state=state,
                main_root=main_root,
                backup_root=backup_root,
            )
        except (KeyError, OSError, TypeError, ValueError, SystemExit) as rollback_exc:
            rollback = {
                "status": "failed",
                "restored": [],
                "errors": [str(rollback_exc)],
            }
        transaction["status"] = (
            "rolled-back" if rollback["status"] == "passed" else "rollback-failed"
        )
        rollback_errors = [str(item) for item in rollback.get("errors", [])]
        state["final_apply"] = {
            "status": transaction["status"],
            "transaction_id": str(transaction["transaction_id"]),
            "error_count": 1 + len(rollback_errors),
            "first_error": str(exc),
        }
        state["current_blockers"] = [
            {
                "failure_class": "final-apply-copy",
                "message": str(exc),
                "rollback_status": rollback["status"],
            }
        ]
        state["next_actions"] = (
            [
                {
                    "id": "final-candidate-apply",
                    "kind": "main-owned-action",
                    "action": "final-apply",
                }
            ]
            if rollback["status"] == "passed"
            else []
        )
        _append_event(run_root, state, "final-apply-failed", error=str(exc))
        _save_state(run_root, state)
        return 1
    transaction["status"] = "completed"
    transaction["completed_at"] = _utc()
    state["final_apply"] = {
        "status": "passed",
        "transaction_id": str(transaction["transaction_id"]),
        "applied_at": _utc(),
    }
    state["phase"] = "final-check"
    state["next_actions"] = [
        {"id": "final-check", "kind": "main-owned-action", "action": "final-check"}
    ]
    applied_relatives = [
        target_path.relative_to(main_root).as_posix()
        for _source_path, target_path in targets
    ]
    _append_event(run_root, state, "final-candidate-applied", files=applied_relatives)
    _save_state(run_root, state)
    print(json.dumps({"status": "passed", "files": applied_relatives}, indent=2))
    return 0


def _manual_structure_findings(
    manual: Path,
    source_goal: dict[str, Any],
    proof_routes: dict[str, dict[str, Any]],
    *,
    manual_relative: str,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    raw_witnesses = source_goal.get("target_witnesses")
    if not isinstance(raw_witnesses, list) or not all(
        isinstance(item, str) and item for item in raw_witnesses
    ):
        return [{"kind": "invalid-source-goal-witnesses"}]
    expected_witnesses = [str(item) for item in raw_witnesses]
    try:
        manual_record = _source_goal_generated_record(
            source_goal,
            role="proof_manual_file",
            relative_path=manual_relative,
        )
    except (TypeError, ValueError) as exc:
        return [{"kind": "invalid-manual-source-goal-record", "message": str(exc)}]
    if manual_record["state"] == "missing":
        if expected_witnesses:
            findings.append(
                {
                    "kind": "missing-manual-has-witnesses",
                    "witness_count": len(expected_witnesses),
                }
            )
        if _lexists(manual):
            findings.append({"kind": "unexpected-manual", "path": str(manual)})
        return findings
    if not manual.is_file():
        return [{"kind": "missing-manual", "path": str(manual)}]
    try:
        text = manual.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        return [
            {
                "kind": "manual-read-error",
                "path": str(manual),
                "message": str(exc),
            }
        ]
    expected_split_goals = {
        name: [
            str(item["name"])
            for item in source_goal.get("split_goals", {}).get(name, [])
        ]
        for name in expected_witnesses
    }
    expected_declarations = [
        declaration
        for name in expected_witnesses
        for declaration in [*expected_split_goals[name], name]
    ]
    command_witnesses = [
        str(command["name"])
        for command in top_level_commands(text)
        if str(command["kind"]) in PROOF_DECLARATION_KINDS
    ]
    if command_witnesses != expected_declarations:
        findings.append(
            {
                "kind": "top-level-witness-list-mismatch",
                "expected": expected_declarations,
                "actual": command_witnesses,
            }
        )
    for declaration in (
        unsafe_typing_commands(text)
        + rollback_control_commands(text)
        + unsafe_assumption_declarations(text)
        + forbidden_top_level_declarations(
            text,
            {
                "Definition",
                "Fixpoint",
                "CoFixpoint",
                "Inductive",
                "CoInductive",
                "Notation",
            },
        )
    ):
        kind = str(declaration["kind"])
        findings.append(
            {
                "kind": (
                    "unsafe-typing-control"
                    if declaration.get("unsafe_typing_control")
                    or declaration.get("bypass_checks")
                    else "rollback-control"
                    if kind in {"Fail", "Succeed"}
                    else "assumption-declaration"
                    if kind in ASSUMPTION_DECLARATION_KINDS
                    else "forbidden-top-level"
                ),
                "declaration": kind,
                "line": declaration["line"],
            }
        )
    try:
        _prelude, lemmas = parse_manual_file(text)
        names = [str(lemma["name"]) for lemma in lemmas]
        if names != expected_declarations:
            findings.append(
                {
                    "kind": "witness-list-mismatch",
                    "expected": expected_declarations,
                    "actual": names,
                }
            )
        witness_lemmas, split_goal_lemmas = partition_manual_lemmas(lemmas)
        actual_witnesses = [str(item["name"]) for item in witness_lemmas]
        actual_split_goals = {
            name: [str(item["name"]) for item in split_goal_lemmas.get(name, [])]
            for name in actual_witnesses
        }
        if (
            actual_witnesses != expected_witnesses
            or actual_split_goals != expected_split_goals
        ):
            findings.append(
                {
                    "kind": "vc-split-goal-mapping-mismatch",
                    "expected": expected_split_goals,
                    "actual": actual_split_goals,
                }
            )
        by_name = {str(lemma["name"]): lemma for lemma in lemmas}
        for lemma in lemmas:
            name = str(lemma["name"])
            commands = top_level_commands(str(lemma["block"]))
            if len(commands) != 1 or commands[0].get("name") != name:
                findings.append({"kind": "extra-top-level-command", "witness": name})
        for name in expected_witnesses:
            route = proof_routes.get(name)
            if not isinstance(route, dict):
                findings.append({"kind": "missing-proof-route", "witness": name})
                continue
            proof_mode = str(route.get("proof_mode") or "")
            split_names = expected_split_goals[name]
            witness = by_name.get(name)
            if witness is not None:
                for marker in incomplete_proof_markers(str(witness["block"])):
                    findings.append({**marker, "witness": name})
                for route_error in proof_mode_errors(
                    str(witness["block"]),
                    proof_mode,
                ):
                    findings.append(
                        {"kind": "proof-mode", "witness": name, "message": route_error}
                    )
            for split_name in split_names:
                split_goal = by_name.get(split_name)
                if split_goal is None:
                    continue
                for marker in incomplete_proof_markers(str(split_goal["block"])):
                    if (
                        marker["kind"] == "Abort"
                        and proof_mode == "LLM_pre_process"
                    ):
                        continue
                    findings.append({**marker, "witness": split_name})
    except ValueError as exc:
        findings.append({"kind": "manual-parse-error", "message": str(exc)})
    return findings


def _formal_case_lib_safety_findings(
    path: Path,
) -> list[dict[str, Any]]:
    if not path.is_file():
        return [{"kind": "missing-formal-case-lib", "path": str(path)}]
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        return [
            {
                "kind": "formal-case-lib-read-error",
                "path": str(path),
                "message": str(exc),
            }
        ]
    findings: list[dict[str, Any]] = incomplete_proof_markers(text)
    for command in unsafe_typing_commands(text):
        findings.append(
            {
                "kind": "unsafe-typing-control",
                "declaration": command["kind"],
                "control": command.get("unsafe_typing_control"),
                "bypass_checks": command.get("bypass_checks", []),
                "line": command["line"],
            }
        )
    for command in rollback_control_commands(text):
        findings.append(
            {
                "kind": "rollback-control",
                "declaration": command["kind"],
                "line": command["line"],
            }
        )
    for declaration in unsafe_assumption_declarations(text):
        findings.append(
            {
                "kind": "assumption-declaration",
                "declaration": declaration["kind"],
                "line": declaration["line"],
            }
        )
    return findings


def _formal_case_lib_closure_findings(
    audit: dict[str, Any],
    target_files: dict[str, Any],
    source_goal: dict[str, Any],
) -> list[dict[str, Any]]:
    if audit.get("status") == "passed":
        return []
    failure = audit.get("first_failure")
    if not isinstance(failure, dict):
        return [
            {
                "kind": "formal-case-lib-dependency-closure",
                "message": "formal_case_lib closure audit returned no failure",
            }
        ]
    if failure.get("kind") != "formal-case-lib-depends-on-generated-artifact":
        return [
            {
                "kind": "formal-case-lib-dependency-closure",
                "failure": failure,
            }
        ]
    evidence = failure.get("evidence")
    evidence = evidence if isinstance(evidence, dict) else {}
    relative = str(evidence.get("dependency") or "")
    matching_roles = [
        role
        for role in (
            "goal_file",
            "proof_auto_file",
            "proof_manual_file",
            "goal_check_file",
        )
        if str(target_files.get(role) or "") == relative
    ]
    finding: dict[str, Any] = {
        "kind": "formal-case-lib-depends-on-generated-artifact",
        "relative_path": relative,
        "source": str(evidence.get("source") or ""),
        "message": str(failure.get("message") or ""),
        "repair": str(failure.get("repair") or ""),
    }
    if len(matching_roles) != 1:
        finding["role_mapping_error"] = (
            "forbidden dependency does not match exactly one persisted generated role"
        )
        return [finding]
    role = matching_roles[0]
    finding["role"] = role
    try:
        record = _source_goal_generated_record(
            source_goal,
            role=role,
            relative_path=relative,
        )
        finding["source_state"] = record["state"]
    except (TypeError, ValueError) as exc:
        finding["source_state"] = "invalid"
        finding["source_record_error"] = str(exc)
    return [finding]


def _formal_case_lib_findings(
    path: Path,
    target_files: dict[str, Any],
    source_goal: dict[str, Any],
    *,
    main_root: Path,
    build_workspace: Path,
) -> list[dict[str, Any]]:
    """Combine local lib safety checks with an independent closure audit."""

    audit = audit_formal_case_lib_closure(
        workspace_root=main_root,
        build_workspace=build_workspace,
        formal_case_lib=Path(str(target_files["formal_case_lib"])),
        current_case_anchor=Path(str(target_files["proof_auto_file"])),
    )
    return [
        *_formal_case_lib_safety_findings(path),
        *_formal_case_lib_closure_findings(
            audit,
            target_files,
            source_goal,
        ),
    ]


def _forbidden_findings(paths: list[Path]) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file():
            continue
        try:
            masked = mask_coq_strings(
                strip_coq_comments(path.read_text(encoding="utf-8"))
            )
        except (OSError, UnicodeError, ValueError) as exc:
            findings.append(
                {
                    "kind": "artifact-read-error",
                    "path": str(path),
                    "message": str(exc),
                }
            )
            continue
        for line_number, line in enumerate(
            masked.splitlines(), start=1
        ):
            for lemma in FORBIDDEN_TOKENS:
                if re.search(
                    rf"(?<![A-Za-z0-9_']){re.escape(lemma)}(?![A-Za-z0-9_'])", line
                ):
                    findings.append(
                        {"path": str(path), "line": line_number, "lemma": lemma}
                    )
    return findings


def _accepted_annotation_source_findings_unchecked(
    state: dict[str, Any], *, require_preapply_state: bool = False
) -> list[dict[str, Any]]:
    """Revalidate accepted annotation provenance against current main root.

    Final-check has already replaced the manual and formal library, so it can
    compare only the target C and the three generated files that final-apply
    never writes.  Final-apply passes ``require_preapply_state`` and also
    compares the raw manual and annotation library with the immutable
    post-delivery history before those originals can enter a backup receipt.
    """

    target_c = str(state["target_files"]["c_file"])
    main_root = Path(str(state["main_root"]))
    source = (
        state.get("source_version")
        if isinstance(state.get("source_version"), dict)
        else {}
    )
    expected = next(
        (
            item
            for item in source.get("files", [])
            if isinstance(item, dict) and item.get("relative_path") == target_c
        ),
        None,
    )
    findings: list[dict[str, Any]] = []
    if (
        not isinstance(expected, dict)
        or expected.get("state") != "present"
        or not expected.get("sha256")
    ):
        findings.append(
            {"kind": "missing-accepted-target-c-digest", "relative_path": target_c}
        )
    else:
        try:
            current = fixed_path_under(
                Path(target_c), main_root, label="accepted annotation target C"
            )
            current_matches = _regular_file_digest(
                current, label="accepted annotation target C"
            ) == expected.get("sha256")
        except (OSError, ValueError, SystemExit):
            current_matches = False
        if not current_matches:
            findings.append(
                {
                    "kind": "target-c-changed-after-annotation",
                    "relative_path": target_c,
                }
            )
    accepted = state.get("accepted_rounds", {}).get("annotation", {})
    if accepted.get("source_version") != source.get("digest"):
        findings.append({"kind": "accepted-annotation-source-version-mismatch"})
    attempt_id = str(accepted.get("attempt_id") or "")
    attempt = state.get("attempts", {}).get(attempt_id)
    if not isinstance(attempt, dict):
        findings.append(
            {"kind": "missing-accepted-annotation-attempt", "attempt_id": attempt_id}
        )
    else:
        try:
            annotation_paths = _validated_annotation_attempt_paths(state, attempt)
            history_errors = _annotation_after_snapshot_errors(state, attempt)
        except (
            KeyError,
            OSError,
            TypeError,
            UnicodeError,
            ValueError,
            SystemExit,
        ) as exc:
            history_errors = [
                f"accepted annotation after-history could not be revalidated: {exc}"
            ]
        for error in history_errors:
            findings.append(
                {
                    "kind": "accepted-annotation-history-artifact-drift",
                    "attempt_id": attempt_id,
                    "message": error,
                }
            )
        if not history_errors:
            unchanged_keys = ["goal_file", "proof_auto_file", "goal_check_file"]
            if require_preapply_state:
                unchanged_keys.extend(["proof_manual_file", "formal_case_lib"])
            after_root = annotation_paths["after"]
            for key in unchanged_keys:
                relative = str(state["target_files"][key])
                try:
                    current_path = fixed_path_under(
                        Path(relative),
                        main_root,
                        label=f"current accepted annotation {key}",
                    )
                    archived_path = fixed_path_under(
                        after_root / relative,
                        after_root,
                        label=f"archived accepted annotation {key}",
                    )
                    current_exists = _lexists(current_path)
                    archived_exists = _lexists(archived_path)
                    if key in {"proof_manual_file", "formal_case_lib"} and not (
                        current_exists or archived_exists
                    ):
                        matches_history = True
                    elif current_exists != archived_exists:
                        matches_history = False
                    else:
                        matches_history = _regular_file_digest(
                            current_path, label=f"current accepted annotation {key}"
                        ) == _regular_file_digest(
                            archived_path,
                            label=f"archived accepted annotation {key}",
                        )
                    message = "current main-root bytes differ from accepted annotation after-history"
                except (KeyError, OSError, ValueError, SystemExit) as exc:
                    matches_history = False
                    message = str(exc)
                if not matches_history:
                    findings.append(
                        {
                            "kind": "current-version-drift",
                            "relative_path": relative,
                            "message": message,
                        }
                    )
    return findings


def _accepted_annotation_source_findings(
    state: dict[str, Any], *, require_preapply_state: bool = False
) -> list[dict[str, Any]]:
    """Make malformed accepted provenance a durable finding, never an escape."""

    try:
        return _accepted_annotation_source_findings_unchecked(
            state, require_preapply_state=require_preapply_state
        )
    except (KeyError, OSError, TypeError, UnicodeError, ValueError, SystemExit) as exc:
        return [
            {
                "kind": "current-version-drift",
                "message": f"accepted annotation provenance could not be revalidated: {exc}",
            }
        ]


def _freshness_evidence(state: dict[str, Any]) -> dict[str, Any]:
    main_root = Path(str(state["main_root"]))
    refresh = Path(str(state["report_root"])) / "final-check" / "symexec-refresh"
    evidence = clean_output_freshness(
        main_root=main_root,
        target_c_file=Path(str(state["target_files"]["c_file"])),
        target_files=state["target_files"],
        reference_root=main_root,
        refresh_root=refresh,
        manual_mode="proved",
        symexec_runner=run_symexec,
    )
    evidence["controller_entrypoint"] = "final-check"
    return evidence


def _coq_side_products(
    main_root: Path, run_root: Path, target_files: dict[str, Any]
) -> list[Path]:
    suffixes = {".vo", ".vos", ".vok", ".glob", ".aux"}
    findings: set[Path] = set()
    for key in (
        "formal_case_lib",
        "goal_file",
        "proof_auto_file",
        "proof_manual_file",
        "goal_check_file",
    ):
        source = main_root / str(target_files[key])
        for suffix in (".vo", ".vos", ".vok", ".glob", ".aux"):
            candidate = source.with_suffix(suffix)
            if _lexists(candidate):
                findings.add(candidate)
        hidden_aux = source.parent / f".{source.stem}.aux"
        if _lexists(hidden_aux):
            findings.add(hidden_aux)
    for path in run_root.rglob("*"):
        if (
            _lexists(path)
            and path.suffix in suffixes
            and not _is_relative_to(path, run_root / "_coq_builds")
        ):
            findings.add(path)
    return sorted(findings)


def _path_label(path: Path, main_root: Path) -> str:
    try:
        return path.relative_to(main_root).as_posix()
    except ValueError:
        return str(path)


def _remove_old_coq_side_products(
    main_root: Path,
    run_root: Path,
    target_files: dict[str, Any],
) -> dict[str, Any]:
    removed_count = 0
    error_count = 0
    first_error: str | None = None
    for path in _coq_side_products(main_root, run_root, target_files):
        try:
            path.unlink()
            removed_count += 1
        except OSError as exc:
            error_count += 1
            if first_error is None:
                first_error = f"{_path_label(path, main_root)}: {exc}"
    return {
        "removed_count": removed_count,
        "error_count": error_count,
        **({"first_error": first_error} if first_error is not None else {}),
    }


def _finish_cleanup_evidence(
    main_root: Path,
    run_root: Path,
    target_files: dict[str, Any],
    cleanup: dict[str, Any],
) -> dict[str, Any]:
    remaining = _coq_side_products(main_root, run_root, target_files)
    evidence = {
        **cleanup,
        "remaining_count": len(remaining),
        **(
            {"first_remaining": _path_label(remaining[0], main_root)}
            if remaining
            else {}
        ),
    }
    evidence["status"] = (
        "passed"
        if int(evidence.get("error_count", 0)) == 0
        and int(evidence["remaining_count"]) == 0
        else "failed"
    )
    return evidence


def _accepted_proof_routes(state: dict[str, Any]) -> dict[str, dict[str, Any]]:
    accepted = state.get("accepted_rounds", {}).get(VC_PROVING_PHASE, {})
    proving = state.get("attempts", {}).get(str(accepted.get("round") or ""), {})
    try:
        proving_paths = _validated_proving_attempt_paths(state, proving)
        manifest = resolve_group_workers_manifest(
            proving_paths["group_workers_manifest"],
            main_root=Path(str(state["main_root"])),
            validate_current_seed=False,
            expected_run_root=Path(str(state["run_root"])),
            expected_round=str(proving["round"]),
        )
    except (OSError, TypeError, UnicodeError, ValueError, SystemExit):
        # The integrity gate records a genuinely malformed accepted manifest.
        #
        # During final-check, however, the accepted candidate has already been
        # applied to the main-root manual/lib paths.  The compact manifest
        # resolver intentionally validates those paths against the original
        # proving seed, so it can reject an otherwise valid final-check state
        # with "formal seed changed".  Route checking only needs the accepted
        # proof modes, which are already sealed by the compact manifest's
        # group_plan path and digest.  Fall back to that sealed plan instead of
        # treating every witness as route-less.
        return _accepted_proof_routes_from_sealed_plan(state, proving)
    routes: dict[str, dict[str, Any]] = {}
    for group in manifest.get("groups", []) if isinstance(manifest, dict) else []:
        if not isinstance(group, dict):
            continue
        for witness in group.get("witnesses", []):
            if isinstance(witness, dict) and witness.get("name"):
                routes[str(witness["name"])] = witness
    return routes


def _accepted_proof_routes_from_sealed_plan(
    state: dict[str, Any],
    proving: Any,
) -> dict[str, dict[str, Any]]:
    if not isinstance(proving, dict):
        return {}
    try:
        report_root = Path(str(state["report_root"]))
        manifest_path = fixed_path_under(
            Path(str(proving.get("group_workers_manifest") or "")),
            report_root,
            label="accepted group workers manifest",
        )
        manifest_sha256 = str(proving.get("group_workers_manifest_sha256") or "")
        if (
            not manifest_path.is_file()
            or not manifest_sha256
            or _file_digest(manifest_path) != manifest_sha256
        ):
            return {}
        manifest = _json_load(manifest_path)
        if not isinstance(manifest, dict):
            return {}
        compact_groups = manifest.get("groups")
        if not isinstance(compact_groups, list) or not all(
            isinstance(item, dict) for item in compact_groups
        ):
            return {}
        compact_ids = [str(item.get("id") or "") for item in compact_groups]
        if any(not item for item in compact_ids):
            return {}
        plan_relative = Path(str(manifest.get("group_plan") or ""))
        if plan_relative.is_absolute() or ".." in plan_relative.parts:
            return {}
        plan_path = fixed_path_under(
            report_root / plan_relative,
            report_root,
            label="sealed accepted group plan",
        )
        plan_sha256 = str(manifest.get("group_plan_sha256") or "")
        if (
            not plan_path.is_file()
            or not plan_sha256
            or _file_digest(plan_path) != plan_sha256
        ):
            return {}
        plan = _json_load(plan_path)
        if not isinstance(plan, dict) or set(plan) != {"groups"}:
            return {}
        groups = plan.get("groups")
        if not isinstance(groups, list):
            return {}
        if [str(group.get("id") or "") for group in groups if isinstance(group, dict)] != compact_ids:
            return {}
        routes: dict[str, dict[str, Any]] = {}
        for group in groups:
            if not isinstance(group, dict):
                return {}
            witnesses = group.get("witnesses")
            if not isinstance(witnesses, list):
                return {}
            for witness in witnesses:
                if not isinstance(witness, dict) or not witness.get("name"):
                    return {}
                proof_mode = str(witness.get("proof_mode") or "")
                if proof_mode not in {"LLM_pre_process", "aggressive_pre_process"}:
                    return {}
                routes[str(witness["name"])] = {
                    "name": str(witness["name"]),
                    "proof_mode": proof_mode,
                }
        return routes
    except (OSError, TypeError, UnicodeError, ValueError, SystemExit):
        return {}


FINAL_CHECK_OPERATION_EXCEPTIONS = (
    KeyError,
    OSError,
    TypeError,
    UnicodeError,
    ValueError,
    SystemExit,
)


def _final_check_exception_finding(stage: str, exc: BaseException) -> dict[str, str]:
    return {
        "kind": "controller-stage-exception",
        "stage": stage,
        "exception_type": type(exc).__name__,
        "message": str(exc) or repr(exc),
    }


def _final_check_execution_stage(
    args: argparse.Namespace,
    run_root: Path,
    stage: str,
) -> dict[str, str] | None:
    """Retain stage call sites as simple diagnostic boundaries."""

    del args, run_root, stage
    return None


def final_check(args: argparse.Namespace) -> int:
    main_root = (
        Path(args.main_root).expanduser().resolve()
        if args.main_root
        else Path.cwd().resolve()
    )
    run_root = _run_root_from_id(main_root, args.run)
    operational_findings: list[dict[str, str]] = []
    if finding := _final_check_execution_stage(
        args, run_root, "validating-final-inputs"
    ):
        operational_findings.append(finding)
    state = _load_state(run_root)
    if state.get("phase") != "final-check":
        raise SystemExit("final-check requires the run to be in final-check phase")
    if state.get("final_apply", {}).get("status") != "passed":
        raise SystemExit("final-check requires a passed final-apply")
    target = state["target_files"]
    manual = main_root / target["proof_manual_file"]
    formal_case_lib = main_root / target["formal_case_lib"]
    source_goal = state["source_goal_version"]
    proving_integrity = _accepted_proving_integrity_errors(state)
    candidate = state.get("final_candidate")
    try:
        if not isinstance(candidate, dict):
            raise TypeError("controller state final candidate is missing")
        candidate_manual_digest = _nullable_sha256(
            candidate.get("proof_manual_sha256"),
            label="final manual digest",
        )
        candidate_lib_digest = _nullable_sha256(
            candidate.get("proving_merged_lib_sha256"),
            label="final lib digest",
        )
    except (TypeError, ValueError) as exc:
        proving_integrity.append(str(exc))
        candidate_manual_digest = None
        candidate_lib_digest = None
    proof_routes = {} if proving_integrity else _accepted_proof_routes(state)
    if finding := _final_check_execution_stage(args, run_root, "pre-check-cleanup"):
        operational_findings.append(finding)
    try:
        with nullcontext():
            cleanup = _remove_old_coq_side_products(main_root, run_root, target)
    except FINAL_CHECK_OPERATION_EXCEPTIONS as exc:
        cleanup = {
            "removed_count": 0,
            "error_count": 1,
            "first_error": _final_check_exception_finding(
                "pre-check-cleanup", exc
            ),
        }
    if finding := _final_check_execution_stage(
        args, run_root, "symbolic-execution-freshness"
    ):
        operational_findings.append(finding)
    try:
        freshness = _freshness_evidence(state)
    except FINAL_CHECK_OPERATION_EXCEPTIONS as exc:
        freshness = {
            "status": "failed",
            "mismatches": [
                _final_check_exception_finding("symbolic-execution-freshness", exc)
            ],
            "controller_entrypoint": "final-check",
        }
    if finding := _final_check_execution_stage(
        args, run_root, "fixed-main-path-coq-check"
    ):
        operational_findings.append(finding)
    try:
        coq = run_coqc_check(
            workspace_root=main_root,
            build_workspace=run_builds_root(run_root) / "final-check" / "src",
            target_file=Path(target["goal_check_file"]),
            target_kind="check",
            source_goal_version=str(state["source_goal_version"]["digest"]),
            current_case_anchor=Path(target["proof_auto_file"]),
        )
        coq["controller_entrypoint"] = "final-check"
    except FINAL_CHECK_OPERATION_EXCEPTIONS as exc:
        coq = {
            "status": "failed",
            "first_failure": _final_check_exception_finding(
                "fixed-main-path-coq-check", exc
            ),
            "controller_entrypoint": "final-check",
        }
    if finding := _final_check_execution_stage(
        args, run_root, "structure-lib-and-safety-checks"
    ):
        operational_findings.append(finding)
    applied_manual_matches = _optional_artifact_matches(
        manual, candidate_manual_digest
    )
    applied_lib_matches = _optional_artifact_matches(
        formal_case_lib, candidate_lib_digest
    )
    try:
        manual_findings = (
            _manual_structure_findings(
                manual,
                source_goal,
                proof_routes,
                manual_relative=str(target["proof_manual_file"]),
            )
            if applied_manual_matches
            else []
        )
    except FINAL_CHECK_OPERATION_EXCEPTIONS as exc:
        manual_findings = [
            _final_check_exception_finding("manual-structure", exc)
        ]
    try:
        if candidate_lib_digest is not None and applied_lib_matches:
            lib_findings = _formal_case_lib_findings(
                formal_case_lib,
                target,
                source_goal,
                main_root=main_root,
                build_workspace=(
                    run_builds_root(run_root) / "final-check" / "src"
                ),
            )
        elif candidate_lib_digest is None and _lexists(formal_case_lib):
            lib_findings = [
                {
                    "kind": "unexpected-formal-case-lib",
                    "path": str(formal_case_lib),
                }
            ]
        else:
            lib_findings = []
    except FINAL_CHECK_OPERATION_EXCEPTIONS as exc:
        lib_findings = [
            _final_check_exception_finding("formal-case-lib-contract", exc)
        ]
    try:
        forbidden = _forbidden_findings(
            [
                path
                for path, digest, matches in (
                    (manual, candidate_manual_digest, applied_manual_matches),
                    (formal_case_lib, candidate_lib_digest, applied_lib_matches),
                )
                if digest is not None and matches
            ]
        )
    except FINAL_CHECK_OPERATION_EXCEPTIONS as exc:
        forbidden = [
            _final_check_exception_finding("forbidden-lemma-scan", exc)
        ]
    accepted_source = _accepted_annotation_source_findings(state)
    try:
        with nullcontext():
            cleanup = _finish_cleanup_evidence(
                main_root,
                run_root,
                target,
                cleanup,
            )
    except FINAL_CHECK_OPERATION_EXCEPTIONS as exc:
        cleanup = {
            **cleanup,
            "status": "failed",
            "error_count": int(cleanup.get("error_count", 0)) + 1,
            **(
                {}
                if cleanup.get("first_error")
                else {
                    "first_error": _final_check_exception_finding(
                        "post-check-cleanup", exc
                    )
                }
            ),
            "remaining_count": int(cleanup.get("remaining_count", 0)),
        }
    blockers: list[dict[str, Any]] = []
    if freshness["status"] != "passed":
        mismatches = (
            freshness.get("mismatches")
            if isinstance(freshness.get("mismatches"), list)
            else []
        )
        blockers.append(
            {
                "failure_class": "symbolic-execution-freshness",
                "mismatch_count": len(mismatches),
                **({"first_mismatch": mismatches[0]} if mismatches else {}),
            }
        )
    if coq.get("status") != "passed":
        blockers.append(
            {
                "failure_class": "fixed-coqc-check",
                "failure": coq.get("first_failure"),
            }
        )
    if manual_findings or not applied_manual_matches:
        blockers.append(
            {
                "failure_class": "manual-structure",
                "finding_count": len(manual_findings),
                **(
                    {"first_finding": manual_findings[0]}
                    if manual_findings
                    else {}
                ),
                "matches_proving_merged_manual": applied_manual_matches,
            }
        )
    if lib_findings or not applied_lib_matches:
        blockers.append(
            {
                "failure_class": "formal-case-lib-contract",
                "finding_count": len(lib_findings),
                **({"first_finding": lib_findings[0]} if lib_findings else {}),
                "matches_proving_merged_lib": applied_lib_matches,
            }
        )
    if forbidden:
        blockers.append(
            {
                "failure_class": "forbidden-lemma",
                "finding_count": len(forbidden),
                "first_finding": forbidden[0],
            }
        )
    if accepted_source:
        blockers.append(
            {
                "failure_class": "accepted-annotation-source",
                "finding_count": len(accepted_source),
                "first_finding": accepted_source[0],
            }
        )
    if proving_integrity:
        blockers.append(
            {
                "failure_class": "accepted-proving-integrity",
                "finding_count": len(proving_integrity),
                "first_finding": proving_integrity[0],
            }
        )
    if cleanup["status"] != "passed":
        blockers.append(
            {
                "failure_class": "cleanup",
                **{
                    key: cleanup[key]
                    for key in (
                        "error_count",
                        "first_error",
                        "remaining_count",
                        "first_remaining",
                    )
                    if cleanup.get(key)
                },
            }
        )
    for finding in operational_findings:
        blockers.append(
            {
                "failure_class": "controller-stage-exception",
                "finding": finding,
            }
        )
    if finding := _final_check_execution_stage(
        args, run_root, "committing-final-result"
    ):
        blockers.append(
            {
                "failure_class": "controller-stage-exception",
                "finding": finding,
            }
        )
    status = "passed" if not blockers else "failed"
    if status == "failed":
        if finding := _final_check_execution_stage(
            args, run_root, "rolling-back-final-apply"
        ):
            blockers.append(
                {
                    "failure_class": "controller-stage-exception",
                    "finding": finding,
                }
            )
        transaction = state.get("final_apply_transaction")
        try:
            backup_root = fixed_path_under(
                Path(str(state["report_root"])) / "final-check" / "backup",
                main_root,
                label="final-check backup directory",
            )
            with nullcontext():
                rollback = _rollback(
                    state=state,
                    main_root=main_root,
                    backup_root=backup_root,
                )
        except FINAL_CHECK_OPERATION_EXCEPTIONS as exc:
            rollback = {
                "status": "failed",
                "restored": [],
                "errors": [
                    str(
                        _final_check_exception_finding(
                            "rolling-back-final-apply", exc
                        )
                    )
                ],
            }
        rollback_errors = [str(item) for item in rollback.get("errors", [])]
        state["final_apply"].update(
            {
                "rollback_error_count": len(rollback_errors),
                **(
                    {"rollback_first_error": rollback_errors[0]}
                    if rollback_errors
                    else {}
                ),
            }
        )
        state["final_apply"]["status"] = (
            "rolled-back" if rollback["status"] == "passed" else "rollback-failed"
        )
        if isinstance(transaction, dict):
            transaction["status"] = state["final_apply"]["status"]
        if rollback["status"] == "passed":
            # A retry must re-apply the pinned accepted candidate before the
            # next final check.  Returning to this phase lets `step` expose the
            # only legal recovery action.  That action repeats the accepted
            # annotation/proving seal checks before touching formal files, so
            # provenance drift becomes a persisted `blocked` final-apply
            # instead of a repeated exception or another final-check.
            state["phase"] = "final-candidate-apply"
        else:
            blockers.append(
                {
                    "failure_class": "final-apply-rollback",
                    "error_count": len(rollback_errors),
                    **(
                        {"first_error": rollback_errors[0]}
                        if rollback_errors
                        else {}
                    ),
                }
            )
    else:
        state["phase"] = "done"
    checked_at = _utc()
    final_result: dict[str, Any] = {
        "status": status,
        "checked_at": checked_at,
        "cleanup_removed_count": int(cleanup.get("removed_count", 0)),
    }
    if blockers:
        final_result.update(
            {
                "blocker_count": len(blockers),
                "first_blocker": blockers[0],
            }
        )
    state["final_check"] = final_result
    if status == "passed":
        state["finished_at"] = checked_at
    state["current_blockers"] = blockers[:1]
    state["next_actions"] = []
    _append_event(
        run_root,
        state,
        f"final-check-{status}",
        failure_classes=[str(item.get("failure_class")) for item in blockers],
    )
    _save_state(run_root, state)
    if status == "passed":
        print(json.dumps({"status": "passed", "phase": "done"}, indent=2))
    else:
        print(json.dumps(state["final_check"], indent=2))
    return 0 if status == "passed" else 1
