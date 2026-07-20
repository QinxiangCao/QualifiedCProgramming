#!/usr/bin/env python3
"""Internal canonical symbolic-execution implementation used by controller.py.

The controller supplies the repository root, target C file, and output root.
This module selects the platform driver and constructs the required include,
SLP, logic, generated-file, input-file, and cwd arguments.
"""

# ruff: noqa: E402 -- this internal module resolves vc-proving path helpers at runtime.

from __future__ import annotations

import hashlib
import os
import platform
import subprocess
import sys
import time
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
VC_PROVING_SCRIPTS = SCRIPT_DIR.parents[1] / "vc-proving" / "scripts"
sys.path.insert(0, str(VC_PROVING_SCRIPTS))

from path_utils import target_files_for_c


CANONICAL_INCLUDE = "QCP_examples/QCP_demos_LLM/"
CANONICAL_SLP = ("QCP_examples/QCP_demos_LLM/", "SimpleC.EE.QCP_demos_LLM")


def _tail(text: str, limit: int = 8000) -> str:
    return text if len(text) <= limit else text[-limit:]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
    raise ValueError(f"output root must be the main root or be under main-root/verification_runs or main-root/reports: {output}")


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
        return main_root / "linux-binary" / "symexec"
    if platform_name == "darwin":
        if normalized_machine in {"arm64", "aarch64"}:
            return main_root / "mac-arm64-binary" / "symexec"
        if normalized_machine in {"x86_64", "amd64"}:
            return main_root / "mac-x86-64-binary" / "symexec"
        raise ValueError(f"unsupported macOS architecture for symexec: {machine or '<unknown>'}")
    raise ValueError(
        "unsupported platform for symexec: "
        f"os.name={os_name!r}, sys.platform={platform_name!r}, machine={machine!r}"
    )


def build_symexec_plan(
    *,
    main_root: Path,
    target_c_file: Path,
    output_root: Path,
) -> dict[str, Any]:
    main_root = main_root.expanduser().resolve()
    if not (main_root / "QCP_examples").is_dir() or not (main_root / "SeparationLogic").is_dir():
        raise ValueError(f"main root does not look like the QCP repository: {main_root}")
    target_rel = _relative_target(main_root, target_c_file)
    output_root = _validate_output_root(main_root, output_root)
    target_files = target_files_for_c(target_rel)
    formal_dir = output_root / target_files["formal_directory"]
    formal_dir.mkdir(parents=True, exist_ok=True)
    driver = _driver_for_platform(main_root)
    argv = [
        str(driver),
        f"--goal-file={output_root / target_files['goal_file']}",
        f"--proof-auto-file={output_root / target_files['proof_auto_file']}",
        f"--proof-manual-file={output_root / target_files['proof_manual_file']}",
        f"-I{CANONICAL_INCLUDE}",
        "-slp",
        *CANONICAL_SLP,
        f"--coq-logic-path={target_files['active_case_theory']}",
        f"--input-file={target_files['c_file']}",
        "--no-exec-info",
    ]
    return {
        "schema_version": "qcp-symexec-plan/v1",
        "helper": str(Path(__file__).resolve()),
        "driver": str(driver),
        "cwd": str(main_root),
        "main_root": str(main_root),
        "output_root": str(output_root),
        "target_c_file": target_files["c_file"],
        "target_files": target_files,
        "include_args": [CANONICAL_INCLUDE],
        "slp_args": list(CANONICAL_SLP),
        "argv": argv,
    }


def run_symexec(
    *,
    main_root: Path,
    target_c_file: Path,
    output_root: Path,
    timeout_seconds: int | None = None,
) -> dict[str, Any]:
    started = time.time()
    plan = build_symexec_plan(
        main_root=main_root,
        target_c_file=target_c_file,
        output_root=output_root,
    )
    driver = Path(plan["driver"])
    evidence: dict[str, Any] = {
        "schema_version": "qcp-canonical-symexec-result/v3",
        "target_c_file": plan["target_c_file"],
    }
    if not driver.is_file():
        return {
            **evidence,
            "status": "skipped",
            "reason": "canonical symexec driver not found",
            "returncode": None,
            "generated_files": [],
            "elapsed_seconds": round(time.time() - started, 3),
        }
    if os.name != "nt" and not os.access(driver, os.X_OK):
        return {
            **evidence,
            "status": "skipped",
            "reason": "canonical symexec driver is not executable",
            "returncode": None,
            "generated_files": [],
            "elapsed_seconds": round(time.time() - started, 3),
        }
    try:
        proc = subprocess.run(
            plan["argv"],
            cwd=plan["cwd"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
            check=False,
        )
        returncode = proc.returncode
        stdout = proc.stdout
        stderr = proc.stderr
    except subprocess.TimeoutExpired as exc:
        returncode = 124
        stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr = (exc.stderr if isinstance(exc.stderr, str) else "") + "\nsymexec timed out"
    output = Path(plan["output_root"])
    generated: list[dict[str, Any]] = []
    for key in ("goal_file", "proof_auto_file", "proof_manual_file", "goal_check_file"):
        relative = plan["target_files"][key]
        path = output / relative
        generated.append(
            {
                "role": key,
                "relative_path": relative,
                "state": "present" if path.is_file() else "missing",
                "sha256": _sha256(path) if path.is_file() else None,
            }
        )
    result = {
        **evidence,
        "status": "passed" if returncode == 0 else "failed",
        "returncode": returncode,
        "generated_files": generated,
        "elapsed_seconds": round(time.time() - started, 3),
    }
    if returncode != 0:
        result["stdout_tail"] = _tail(stdout)
        result["stderr_tail"] = _tail(stderr)
    return result
