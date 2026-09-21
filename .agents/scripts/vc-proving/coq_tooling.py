"""Controller API for native dependencies and current-source Rocq checks."""

from __future__ import annotations

import json
import time
from collections.abc import Mapping
from pathlib import Path
from typing import Any

import coq_tooling_common as common
import coq_tooling_dune as dune
import coq_tooling_makefile as makefile
from atomic_file import atomic_write_text
from build_mode import DUNE_BUILD_MODE, detect_build_mode
from coq_tooling_common import _dependency_modules
from path_utils import fixed_path_under


def _backend(root: Path):
    return dune if detect_build_mode(root) == DUNE_BUILD_MODE else makefile


def dependency_snapshot_file_name(workspace_root: Path) -> str:
    return "dependency_plan.json"


def prepare_dune_dependencies(
    *, workspace_root: Path, target_file: Path, current_case_anchor: Path,
    snapshot_path: Path | None = None, timeout_seconds: int | float | None = None,
) -> dict[str, Any]:
    started = time.monotonic()
    try:
        root = fixed_path_under(workspace_root.expanduser().absolute(), workspace_root.expanduser().absolute(), label="workspace")
        backend = _backend(root)
        target = common._repository_relative(target_file, root, label="dependency target")
        anchor = common._repository_relative(current_case_anchor, root, label="case anchor")
        deadline = common.command_deadline(timeout_seconds)
        plan = common.prepare_plan(backend, root=root, target=target, anchor=anchor, deadline=deadline,
                                   all_current=not target.name.endswith("_lib.v"))
        receipt = common.preparation_receipt(plan, started, deadline)
        if snapshot_path is not None:
            path = fixed_path_under(snapshot_path, root, label="dependency plan")
            atomic_write_text(path, json.dumps(plan, indent=2, ensure_ascii=True) + "\n")
            receipt["snapshot"] = path.relative_to(root).as_posix()
        return receipt
    except (common.CoqBuildPlanError, OSError, UnicodeError, ValueError) as exc:
        return common.failure_result(exc, started)


def compact_dune_preparation(evidence: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in evidence.items() if not key.startswith("_")}


def dune_preparation_receipt_errors(*, workspace_root: Path, receipt: Mapping[str, Any] | None) -> list[str]:
    try:
        root = workspace_root.expanduser().absolute()
        common.load_plan(root, _backend(root), receipt)
        return []
    except (common.CoqBuildPlanError, OSError, UnicodeError, ValueError) as exc:
        return [str(exc)]


def run_coqc_check(*, workspace_root: Path, **kwargs: Any) -> dict[str, Any]:
    return common.run_coqc_check(_backend(workspace_root), workspace_root=workspace_root, **kwargs)


def run_coqtop_debug(*, workspace_root: Path, **kwargs: Any) -> dict[str, Any]:
    return common.run_coqtop_debug(_backend(workspace_root), workspace_root=workspace_root, **kwargs)


def audit_formal_case_lib_closure(*, workspace_root: Path, **kwargs: Any) -> dict[str, Any]:
    return common.audit_formal_case_lib_closure(_backend(workspace_root), workspace_root=workspace_root, **kwargs)
