"""Regression tests for the public build entry points."""
import os
from pathlib import Path
import shutil
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[2]
@pytest.mark.parametrize("retries", [0, 1])
def test_powershell_retry_count(tmp_path, retries):
    shell = shutil.which("powershell")
    if os.name != "nt" or not shell:
        pytest.skip("requires Windows PowerShell")
    calls = tmp_path / "calls.txt"
    lake = tmp_path / "lake.cmd"
    lake.write_text(f'@echo attempt>>"{calls}"\n@exit /b 7\n')
    result = subprocess.run([shell, "-NoProfile", "-File", str(ROOT / "Lean/scripts/build.ps1"),
                             "-Lake", str(lake), "-Retries", str(retries)],
                            capture_output=True, text=True, timeout=30)
    assert result.returncode != 0
    assert len(calls.read_text().splitlines()) == retries + 1


def make_command():
    command = shutil.which("make") or shutil.which("mingw32-make")
    if not command:
        pytest.skip("requires GNU Make")
    return command


def test_make_source_inventory_includes_shards(tmp_path):
    # An explicit dependency target avoids triggering compilation during inventory.
    extra = tmp_path / "inventory.mk"
    inventory = tmp_path / "sources.txt"
    extra.write_text(f"$(file >{inventory.as_posix()},$(EXAMPLE))\ndepend-examples: ;\n")
    result = subprocess.run([make_command(), "-f", "Makefile", "-f", str(extra),
                             "-n", "depend-examples"], cwd=ROOT / "Rocq",
                            capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stderr
    sources = set(inventory.read_text().split())
    assert all((ROOT / "Rocq" / source).is_file() for source in sources)
    codeforces = {p.relative_to(ROOT / "Rocq").as_posix()
                  for p in (ROOT / "Rocq/examples/LLM_bench/Codeforces").rglob("*.v")}
    assert codeforces and codeforces <= sources
    application_parts = {p.relative_to(ROOT / "Rocq").as_posix()
                         for p in (ROOT / "Rocq/examples/Applications_human").rglob("*_proof_manual_part*.v")}
    assert application_parts and application_parts <= sources
    qcp_strategy_checks = {p.relative_to(ROOT / "Rocq").as_posix()
                           for p in (ROOT / "Rocq/examples/QCP_demos_LLM").glob("*_strategy_goal_check.v")}
    # These two strategy families are explicitly excluded by the Dune theory.
    excluded = {f"examples/QCP_demos_LLM/{stem}_strategy_{suffix}.v"
                for stem in ("dll_data", "sll_data")
                for suffix in ("goal", "proof", "goal_check")}
    assert qcp_strategy_checks and qcp_strategy_checks - excluded <= sources
    assert {
        "examples/LLM_bench/Algorithms/decimal_digits/decimal_digits_lib.v",
        "examples/LLM_bench/Algorithms/kosaraju/TwoSAT.v",
    } <= sources


@pytest.mark.parametrize("timing", ["", "1"])
def test_posix_make_preserves_compiler_failure(tmp_path, timing):
    bash = shutil.which("bash")
    if os.name == "nt":
        bash = str(Path(os.environ.get("ProgramFiles", "C:/Program Files")) / "Git/bin/bash.exe")
    if not bash or not Path(bash).is_file():
        pytest.skip("requires Bash")
    shutil.copyfile(ROOT / "Rocq/Makefile", tmp_path / "Makefile")
    (tmp_path / "Base.v").write_text("Goal True. exact I. Qed.\n")
    result = subprocess.run([make_command(), "OS=Linux", f"SHELL={bash}", "COQDEP=true",
                             "COQC=false", "CORE_EXAMPLE=Base.v", "Unify_DEP_FILES=",
                             "CORE_PROJECT_EXAMPLE=Base.v", "FLOCQ_EXAMPLE=", f"TIMING={timing}", "core"],
                            cwd=tmp_path, capture_output=True, text=True, timeout=30)
    assert result.returncode != 0, result.stdout + result.stderr
    assert "Base.v" in result.stdout
    assert not (tmp_path / ".depend").exists()


def test_make_stops_on_dependency_failure(tmp_path):
    shutil.copyfile(ROOT / "Rocq/Makefile", tmp_path / "Makefile")
    (tmp_path / "Base.v").write_text("Goal True. exact I. Qed.\n")
    result = subprocess.run([make_command(), "COQDEP=missing-coqdep-command", "COQC=missing-coqc-command",
                             "CORE_EXAMPLE=Base.v", "Unify_DEP_FILES=", "core"],
                            cwd=tmp_path, capture_output=True, text=True, timeout=30)
    assert result.returncode != 0
    assert "COQC Base.v" not in result.stdout


def test_lean_generation_manifest_covers_tracked_goals():
    tracked = subprocess.check_output(["git", "ls-files", "Lean/examples"], cwd=ROOT, text=True).splitlines()
    goals = {name for name in tracked if name.endswith("_goal.lean")}
    generated = []
    for line in (ROOT / "scripts/lean-generation-inputs.txt").read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        tool, source, output, stem = line.split("|")
        assert tool in {"symexec", "StrategyCheck"}
        assert (ROOT / source).is_file(), source
        suffix = "_strategy" if tool == "StrategyCheck" else ""
        generated.append(f"Lean/examples/{output}/{stem}{suffix}_goal.lean")
    assert len(generated) == len(set(generated)), "Duplicate generation destinations"
    assert set(generated) == goals
