#!/usr/bin/env python3
"""Controller-owned append-only public-helper candidate pool.

The pool is a run-local catalogue, not a fourth active Rocq library.  Workers
may copy promising declarations into their own ``group_worker_lib``; the
existing group check remains the authority that the copied declarations and
their use actually compile.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

from atomic_file import atomic_write_bytes
from file_integrity import sha256_bytes as _sha256_bytes
from path_utils import fixed_path_under, write_bytes, write_text
from proof_manual_utils import (
    HELPER_DECL_KINDS,
    declaration_block_digest,
    is_official_library_import,
    lemma_statement_hash,
    lib_contract_errors,
    normalize_coq_text,
    parse_lib_declarations,
    required_rocq_modules,
)

PUBLIC_HELPER_LEMMA_LIB_NAME = "public_helper_lemma_lib.v"
ROUND_PUBLIC_HELPER_SNAPSHOT_NAME = "public_helper_snapshot.txt"
PUBLIC_HELPER_HEADER = (
    "(* Controller-owned append-only catalogue of proved helper candidates. *)\n"
    "(* It is never imported directly; copy candidates into a group_worker_lib and rerun group-check. *)\n"
)


def public_helper_lemma_lib_path(run_root: Path) -> Path:
    # Keep the durable pool on the lexical run path.  Calling ``resolve`` here
    # would silently turn a replaced pool symlink into an external write target.
    owner = fixed_path_under(run_root, run_root.parent, label="public helper run root")
    return fixed_path_under(
        owner / PUBLIC_HELPER_LEMMA_LIB_NAME,
        owner,
        label="public helper candidate pool",
    )


def round_public_helper_snapshot_path(run_root: Path, round_id: str) -> Path:
    owner = fixed_path_under(run_root, run_root.parent, label="public helper run root")
    return fixed_path_under(
        owner / round_id / ROUND_PUBLIC_HELPER_SNAPSHOT_NAME,
        owner,
        label="round public helper snapshot",
    )


def _fixed_public_artifact(path: Path, *, label: str) -> Path:
    """Reject a leaf or ancestor symlink before reading/replacing an artifact."""

    return fixed_path_under(path, path.parent, label=label)


def _declaration_record(declaration: dict[str, Any]) -> dict[str, Any]:
    block = str(declaration["block"])
    record: dict[str, Any] = {
        "name": str(declaration["name"]),
        "kind": str(declaration["kind"]),
        "block_sha256": declaration_block_digest(block),
        "start_line": int(declaration.get("start_line", 1)),
        "end_line": int(declaration.get("end_line", 1)),
    }
    if record["kind"] in HELPER_DECL_KINDS:
        record["statement_hash"] = lemma_statement_hash(block)
    return record


def ensure_public_helper_lemma_lib(run_root: Path) -> Path:
    path = public_helper_lemma_lib_path(run_root)
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists():
        write_text(path, PUBLIC_HELPER_HEADER)
    return path


def public_helper_pool_snapshot(
    path: Path, *, _raw: bytes | None = None
) -> dict[str, Any]:
    """Validate and summarize the current append-only candidate pool."""

    path = _fixed_public_artifact(path, label="public helper artifact")
    if not path.is_file():
        raise ValueError(f"public helper candidate pool is missing: {path}")
    raw = path.read_bytes() if _raw is None else _raw
    text = raw.decode("utf-8")
    # This catalogue is run-independent, so it intentionally has no
    # current-case module set to bind.  Its own dependency pass keeps the
    # stricter boundary of official Rocq imports only, including multiline and
    # Require Export forms that declaration extraction need not preserve.
    errors = lib_contract_errors(text, forbidden_modules=())
    try:
        dependencies = required_rocq_modules(
            text,
            source_label=str(path),
        )
    except ValueError as exc:
        errors.append(f"public helper dependency parsing failed: {exc}")
        dependencies = []
    for module in dependencies:
        if module != "Coq" and not module.startswith("Coq."):
            errors.append(
                "public helper candidate pool contains non-official dependency "
                f"`{module}`"
            )
    declarations = parse_lib_declarations(text)
    seen_names: dict[str, str] = {}
    records: list[dict[str, Any]] = []
    for declaration in declarations:
        kind = str(declaration["kind"])
        name = str(declaration["name"])
        if kind == "Import":
            if not is_official_library_import(name):
                errors.append(
                    f"public helper candidate pool contains non-official import `{name}`"
                )
        elif kind not in HELPER_DECL_KINDS:
            errors.append(
                f"public helper candidate pool contains forbidden declaration kind `{kind}`"
            )
        digest = declaration_block_digest(str(declaration["block"]))
        if name in seen_names and seen_names[name] != digest:
            errors.append(
                f"public helper candidate pool contains conflicting declaration `{name}`"
            )
        seen_names.setdefault(name, digest)
        records.append(_declaration_record(declaration))
    if errors:
        raise ValueError("; ".join(errors))
    helper_records = [
        item for item in records if str(item["kind"]) in HELPER_DECL_KINDS
    ]
    return {
        "path": str(path),
        "sha256": _sha256_bytes(raw),
        "declaration_count": len(records),
        "helper_count": len(helper_records),
        "declarations": records,
        "helpers": helper_records,
    }


def freeze_round_public_helper_snapshot(
    run_root: Path, round_id: str
) -> dict[str, Any]:
    """Freeze the pool seen by every worker in one vc-proving round.

    A retry of preparing the same round reuses the first snapshot instead of
    observing candidates promoted later by a sibling group.  Promotions remain
    useful to future rounds without making current group artifacts depend on
    dispatch or completion timing.
    """

    live_path = ensure_public_helper_lemma_lib(run_root)
    live_bytes = live_path.read_bytes()
    public_helper_pool_snapshot(live_path, _raw=live_bytes)
    snapshot_path = round_public_helper_snapshot_path(run_root, round_id)
    snapshot_path.parent.mkdir(parents=True, exist_ok=True)
    if not snapshot_path.exists():
        write_bytes(
            snapshot_path,
            live_bytes,
            label="round public helper snapshot",
        )
    return public_helper_pool_snapshot(snapshot_path)


def allowed_public_helper_blocks(path: Path) -> dict[str, set[str]]:
    """Return declaration/proof-token digests allowed for public reuse."""

    snapshot = public_helper_pool_snapshot(path)
    allowed: dict[str, set[str]] = {}
    for item in snapshot["helpers"]:
        allowed.setdefault(str(item["name"]), set()).add(str(item["block_sha256"]))
    return allowed


def plan_public_helper_declarations(
    path: Path,
    declarations: list[dict[str, Any]],
    *,
    source_round: str,
    source_group: str,
) -> dict[str, Any]:
    """Build, but do not install, one append-only helper-pool candidate.

    Exact duplicates and same-statement proof variants are already reusable and
    therefore skipped.  A same-name/different-statement declaration is reported
    as a conflict and is not appended; proof acceptance itself need not be
    weakened merely because the optional public catalogue cannot take it.

    ``candidate_bytes`` is intentionally an in-process field.  Controller state
    stores only the compact before/after receipt; after a crash the candidate is
    deterministically recomputed from the sealed group artifact.
    """

    path = _fixed_public_artifact(path, label="public helper candidate pool")
    old_bytes = path.read_bytes()
    before = public_helper_pool_snapshot(path, _raw=old_bytes)
    old_text = old_bytes.decode("utf-8")
    existing = parse_lib_declarations(old_text)
    imports = {str(item["name"]) for item in existing if str(item["kind"]) == "Import"}
    helpers = {
        str(item["name"]): item
        for item in existing
        if str(item["kind"]) in HELPER_DECL_KINDS
    }
    appended: list[str] = []
    skipped: list[str] = []
    conflicts: list[str] = []
    blocks: list[str] = []
    for declaration in declarations:
        kind = str(declaration.get("kind") or "")
        name = str(declaration.get("name") or "")
        block = str(declaration.get("block") or "").strip() + "\n"
        if kind == "Import":
            if not is_official_library_import(name):
                conflicts.append(name or "<unnamed-import>")
                continue
            if name in imports:
                skipped.append(name)
                continue
            imports.add(name)
        elif kind in HELPER_DECL_KINDS:
            current = helpers.get(name)
            if current is not None:
                current_block = str(current["block"])
                if normalize_coq_text(current_block) == normalize_coq_text(
                    block
                ) or lemma_statement_hash(current_block) == lemma_statement_hash(block):
                    skipped.append(name)
                else:
                    conflicts.append(name)
                continue
            helpers[name] = {"kind": kind, "name": name, "block": block}
        else:
            conflicts.append(name or f"<{kind or 'unknown-kind'}>")
            continue
        appended.append(name)
        blocks.append(block.rstrip())
    separator = "" if old_text.endswith("\n\n") else "\n"
    addition = separator + "\n\n".join(blocks) + "\n" if blocks else ""
    new_bytes = old_bytes + addition.encode("utf-8")
    if not new_bytes.startswith(old_bytes):
        raise ValueError("public helper update is not append-only")
    return {
        "status": "appended" if appended else "unchanged",
        "source_round": source_round,
        "source_group": source_group,
        "before_sha256": before["sha256"],
        "after_sha256": _sha256_bytes(new_bytes),
        "appended": appended,
        "skipped": skipped,
        "conflicts": conflicts,
        "helper_count": sum(
            1
            for item in parse_lib_declarations(new_bytes.decode("utf-8"))
            if str(item["kind"]) in HELPER_DECL_KINDS
        ),
        "candidate_bytes": new_bytes,
    }


def apply_public_helper_declaration_plan(
    path: Path, plan: dict[str, Any]
) -> dict[str, Any]:
    """Install a planned candidate after a last-moment before-digest check."""

    path = _fixed_public_artifact(path, label="public helper candidate pool")
    before_sha256 = str(plan.get("before_sha256") or "")
    after_sha256 = str(plan.get("after_sha256") or "")
    candidate = plan.get("candidate_bytes")
    if not isinstance(candidate, bytes):
        raise ValueError("public helper plan has no candidate bytes")
    current = public_helper_pool_snapshot(path)
    if current["sha256"] == after_sha256:
        return current
    if current["sha256"] != before_sha256:
        raise ValueError("public helper pool changed before planned append")
    def validate_prepared(temporary: Path) -> None:
        candidate_snapshot = public_helper_pool_snapshot(temporary)
        if candidate_snapshot["sha256"] != after_sha256:
            raise ValueError("public helper candidate digest does not match its plan")

    def validate_commit() -> None:
        # Validation can take non-zero time.  Recheck the live bytes immediately
        # before replacement so even an unexpected concurrent writer cannot be
        # silently overwritten.
        if public_helper_pool_snapshot(path)["sha256"] != before_sha256:
            raise ValueError("public helper pool changed during planned append")

    atomic_write_bytes(
        path,
        candidate,
        suffix=".candidate",
        validate_prepared=validate_prepared,
        validate_commit=validate_commit,
    )
    after = public_helper_pool_snapshot(path)
    if after["sha256"] != after_sha256:
        raise ValueError("public helper pool replacement did not install the plan")
    return after


def append_public_helper_declarations(
    path: Path,
    declarations: list[dict[str, Any]],
    *,
    source_round: str,
    source_group: str,
) -> dict[str, Any]:
    """Plan and atomically append declarations for non-controller callers."""

    plan = plan_public_helper_declarations(
        path,
        declarations,
        source_round=source_round,
        source_group=source_group,
    )
    if plan["after_sha256"] != plan["before_sha256"]:
        after = apply_public_helper_declaration_plan(path, plan)
    else:
        after = public_helper_pool_snapshot(path)
    result = {key: value for key, value in plan.items() if key != "candidate_bytes"}
    result["helper_count"] = after["helper_count"]
    return result
