"""Regression tests for the public build entry points."""
import importlib.util
import os
from pathlib import Path
import re
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
    extra.write_text(f"$(file >{inventory.as_posix()},$(ALL_FILES))\ndepend-examples: ;\n")
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
    assert {
        f"examples/Applications_human/typeinfer_rc/typeinfer_rc_{suffix}.v"
        for suffix in ("lib", "goal", "proof_auto", "proof_manual", "goal_check",
                       "strategy_goal", "strategy_proof", "strategy_goal_check")
    } <= sources
    assert {
        "SeparationLogic/RCMap.v",
        "examples/Applications_human/typeinfer_rc/typeinfer_rc.v",
    } <= sources


def test_typeinfer_rc_is_not_excluded_from_dune():
    dune = (ROOT / "Rocq/examples/Applications_human/dune").read_text()
    assert "(include_subdirs qualified)" in dune
    assert not re.search(r"\(dirs[^)]*\\[^)]*\btypeinfer_rc\b", dune, re.S)


def test_typeinfer_rc_generation_entry():
    import sys
    sys.path.insert(0, str(ROOT / "scripts"))
    from generation_tasks import ProgramVC, command, discover_programs
    task = ProgramVC(Path("QCP_examples/Applications_human/typeinfer_rc/typeinfer_rc.c"))
    assert task in discover_programs()
    args, output = command(task)
    assert args[args.index("--coq-logic-path") + 1] == "SimpleC.EE.Applications_human.typeinfer_rc"
    assert output == Path("Rocq/examples/Applications_human/typeinfer_rc")
    assert "--no-exec-info" in args


def test_typeinfer_rc_post_transport_is_diagnostic_only(tmp_path, monkeypatch):
    spec = importlib.util.spec_from_file_location(
        "collect_and_analyze", ROOT / "scripts/collect_and_analyze.py")
    collector = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(collector)
    monkeypatch.setattr(collector, "OUT_LISTS_JSON", str(tmp_path / "lists.json"))
    monkeypatch.setattr(collector, "OUT_LISTS_PY", str(tmp_path / "lists.py"))
    fixture = "Applications_human/typeinfer_rc/post_transport.c"
    assert (ROOT / "QCP_examples" / fixture).is_file()
    examples, strategies = collector.collect_lists(str(ROOT / "QCP_examples"))
    assert fixture not in examples
    assert "Applications_human/typeinfer_rc/typeinfer_rc.c" in examples
    assert "Applications_human/typeinfer_rc/typeinfer_rc.strategies" in strategies




def test_typeinfer_rc_strategy_generation_entry():
    import sys
    sys.path.insert(0, str(ROOT / "scripts"))
    from generation_tasks import StrategyVC, command, discover_strategies
    task = StrategyVC(Path("QCP_examples/Applications_human/typeinfer_rc/typeinfer_rc.strategies"))
    assert task in discover_strategies()
    args, output = command(task)
    assert args[args.index("--coq-logic-path") + 1] == "SimpleC.EE.Applications_human.typeinfer_rc"
    assert output == Path("Rocq/examples/Applications_human/typeinfer_rc")
    assert "--no-exec-info" in args


@pytest.mark.parametrize("timing", ["", "1"])
def test_posix_make_preserves_compiler_failure(tmp_path, timing):
    bash = shutil.which("bash")
    if os.name == "nt":
        bash = str(Path(os.environ.get("ProgramFiles", "C:/Program Files")) / "Git/bin/bash.exe")
    if not bash or not Path(bash).is_file():
        pytest.skip("requires Bash")
    if os.name == "nt":
        import ctypes
        short = ctypes.create_unicode_buffer(32768)
        assert ctypes.windll.kernel32.GetShortPathNameW(bash, short, len(short))
        bash = short.value.replace("\\", "/")
    env = os.environ.copy()
    if os.name == "nt":
        # MinGW Make can directly launch simple commands such as printf/true.
        env["PATH"] = str(Path(bash).parents[1] / "usr/bin") + os.pathsep + env["PATH"]
    shutil.copyfile(ROOT / "Rocq/Makefile", tmp_path / "Makefile")
    (tmp_path / "Base.v").write_text("Goal True. exact I. Qed.\n")
    result = subprocess.run([make_command(), "MAKE_HOST=x86_64-pc-linux-gnu", ".SHELLFLAGS=-c", f"SHELL={bash}", "COQDEP=true",
                             "COQC=false", "CORE_FILES=Base.v", "EXAMPLE_FILES=", f"TIMING={timing}", "core"],
                            env=env, cwd=tmp_path, capture_output=True, text=True, timeout=30)
    assert result.returncode != 0, result.stdout + result.stderr
    assert "Base.v" in result.stdout
    assert (tmp_path / ".depend").is_file()


def test_make_stops_on_dependency_failure(tmp_path):
    shutil.copyfile(ROOT / "Rocq/Makefile", tmp_path / "Makefile")
    (tmp_path / "Base.v").write_text("Goal True. exact I. Qed.\n")
    result = subprocess.run([make_command(), "COQDEP=missing-coqdep-command", "COQC=missing-coqc-command",
                             "CORE_FILES=Base.v", "EXAMPLE_FILES=", "core"],
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
