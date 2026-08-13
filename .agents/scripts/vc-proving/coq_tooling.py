#!/usr/bin/env python3
"""Build-mode router for controller-owned Rocq tooling.

The selection rule is intentionally blunt and centralized: a repository root
with an ``_build`` directory uses the existing Dune implementation; every
other repository root uses the lock-free Makefile implementation.  Callers do
not construct backend-specific commands or import backend modules directly.
"""

from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path
from typing import Any

import coq_tooling_dune as _dune
import coq_tooling_makefile as _makefile
from build_mode import DUNE_BUILD_MODE, detect_build_mode

# Preserve the established utility/type surface for controller modules and
# external characterization tests.  The backend-specific operations below
# override the imported Dune names with dispatching wrappers.
from coq_tooling_dune import *  # noqa: F403
from coq_tooling_dune import _dependency_modules


DUNE_SNAPSHOT_FILE_NAME = _dune.DUNE_SNAPSHOT_FILE_NAME
MAKEFILE_SNAPSHOT_FILE_NAME = _makefile.MAKEFILE_SNAPSHOT_FILE_NAME


def _backend(workspace_root: Path) -> Any:
    return (
        _dune
        if detect_build_mode(workspace_root) == DUNE_BUILD_MODE
        else _makefile
    )


def dependency_snapshot_file_name(workspace_root: Path) -> str:
    """Return the selected backend's run-local snapshot filename."""

    backend = _backend(workspace_root)
    return (
        _dune.DUNE_SNAPSHOT_FILE_NAME
        if backend is _dune
        else _makefile.MAKEFILE_SNAPSHOT_FILE_NAME
    )


def prepare_dune_dependencies(
    *,
    workspace_root: Path,
    target_file: Path,
    current_case_anchor: Path,
    source_goal_version: str | None,
    snapshot_path: Path | None = None,
    timeout_seconds: int | float | None = _dune.DUNE_BUILD_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Prepare the exact dependency snapshot with the selected backend.

    The historical function name remains part of the controller API so the
    Dune path is unchanged.  Makefile receipts carry ``build_mode=makefile``.
    """

    return _backend(workspace_root).prepare_dune_dependencies(
        workspace_root=workspace_root,
        target_file=target_file,
        current_case_anchor=current_case_anchor,
        source_goal_version=source_goal_version,
        snapshot_path=snapshot_path,
        timeout_seconds=timeout_seconds,
    )


def compact_dune_preparation(evidence: Mapping[str, Any]) -> dict[str, Any]:
    backend = (
        _makefile
        if evidence.get("build_mode") == _makefile.MAKEFILE_BUILD_MODE
        else _dune
    )
    return backend.compact_dune_preparation(evidence)


def dune_preparation_receipt_errors(
    *,
    workspace_root: Path,
    receipt: Mapping[str, Any] | None,
    expected_source_goal_version: str | None = None,
) -> list[str]:
    return _backend(workspace_root).dune_preparation_receipt_errors(
        workspace_root=workspace_root,
        receipt=receipt,
        expected_source_goal_version=expected_source_goal_version,
    )


def dune_snapshot_for_preserved_build(
    *,
    workspace_root: Path,
    build_workspace: Path,
) -> dict[str, Any]:
    return _backend(workspace_root).dune_snapshot_for_preserved_build(
        workspace_root=workspace_root,
        build_workspace=build_workspace,
    )


def run_coqc_check(
    *,
    workspace_root: Path,
    build_workspace: Path,
    target_file: Path,
    target_kind: str,
    source_goal_version: str | None,
    timeout_seconds: int | float | None = _dune.COQ_COMMAND_TIMEOUT_SECONDS,
    group_check: dict[str, Any] | None = None,
    overlays: dict[Path, Path] | None = None,
    incremental: bool = False,
    current_case_anchor: Path | None = None,
    dune_preparation: Mapping[str, Any] | None = None,
    _reuse_dune_snapshot: dict[str, Any] | None = None,
) -> dict[str, Any]:
    return _backend(workspace_root).run_coqc_check(
        workspace_root=workspace_root,
        build_workspace=build_workspace,
        target_file=target_file,
        target_kind=target_kind,
        source_goal_version=source_goal_version,
        timeout_seconds=timeout_seconds,
        group_check=group_check,
        overlays=overlays,
        incremental=incremental,
        current_case_anchor=current_case_anchor,
        dune_preparation=dune_preparation,
        _reuse_dune_snapshot=_reuse_dune_snapshot,
    )


def run_coqtop_debug(
    *,
    workspace_root: Path,
    build_workspace: Path,
    debug_script: Path,
    source_goal_version: str | None,
    timeout_seconds: int | float | None = _dune.COQ_COMMAND_TIMEOUT_SECONDS,
    overlays: dict[Path, Path] | None = None,
    reuse_existing_build: bool = False,
    current_case_anchor: Path | None = None,
    _reuse_dune_snapshot: dict[str, Any] | None = None,
) -> dict[str, Any]:
    return _backend(workspace_root).run_coqtop_debug(
        workspace_root=workspace_root,
        build_workspace=build_workspace,
        debug_script=debug_script,
        source_goal_version=source_goal_version,
        timeout_seconds=timeout_seconds,
        overlays=overlays,
        reuse_existing_build=reuse_existing_build,
        current_case_anchor=current_case_anchor,
        _reuse_dune_snapshot=_reuse_dune_snapshot,
    )


def audit_formal_case_lib_closure(
    *,
    workspace_root: Path,
    build_workspace: Path,
    formal_case_lib: Path,
    current_case_anchor: Path,
) -> dict[str, Any]:
    return _backend(workspace_root).audit_formal_case_lib_closure(
        workspace_root=workspace_root,
        build_workspace=build_workspace,
        formal_case_lib=formal_case_lib,
        current_case_anchor=current_case_anchor,
    )


def __getattr__(name: str) -> Any:
    """Keep uncommon, mode-independent Dune helpers import-compatible."""

    return getattr(_dune, name)
