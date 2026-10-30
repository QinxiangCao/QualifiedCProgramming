"""Consumers of a mutable case library must never reuse stale native artifacts."""
import shutil
import sys
import time
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(SCRIPTS / "vc-proving")]
import coq_tooling_common as common
import coq_tooling_dune as dune
import coq_tooling_makefile as makefile


def test_transitive_consumers_are_current_but_their_independent_dependencies_are_base():
    base, lib, strategy, bridge, goal = map(Path, ["Base.v", "case_lib.v", "strategy.v", "bridge.v", "case_goal.v"])
    graph = {base: (), lib: (base,), strategy: (lib,), bridge: (strategy, base), goal: (bridge,)}
    assert common.current_sources(graph, {lib, goal}) == {lib, strategy, bridge, goal}
    assert common.dependency_closure(graph, [goal]).index(lib) < common.dependency_closure(graph, [goal]).index(strategy)
    graph[lib] = (bridge,)
    with pytest.raises(ValueError, match="cycle"):
        common.dependency_closure(graph, [goal])


def test_library_audit_still_rejects_indirect_generated_artifact_dependency(tmp_path, monkeypatch):
    lib = Path("Rocq/examples/demo/case_lib.v")
    helper = Path("Rocq/examples/shared/helper.v")
    goal = Path("Rocq/examples/demo/case_goal.v")
    plan = {"dependencies": {lib.as_posix(): [helper.as_posix()], helper.as_posix(): [goal.as_posix()], goal.as_posix(): []}}
    monkeypatch.setattr(common, "prepare_plan", lambda *args, **kwargs: plan)
    result = common.audit_formal_case_lib_closure(dune, workspace_root=tmp_path,
             build_workspace=tmp_path / "unused", formal_case_lib=lib, current_case_anchor=lib)
    assert result["status"] == "failed" and "generated artifacts" in result["stderr_tail"]
    assert result["compiled"] is False


def _write(root, relative, text):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


@pytest.mark.parametrize("backend", [dune, makefile], ids=["dune", "make"])
def test_native_strategy_rebuild_with_library_overlay_and_cross_directory_import(tmp_path, backend):
    root = tmp_path / "source space (&)"
    root.mkdir()
    for tool in ("coqc", "coqtop", "dune" if backend is dune else "make"):
        executable = backend.configured_program(root, tool)
        if not Path(executable).is_file() and shutil.which(executable) is None:
            pytest.skip(f"requires native {tool}")
    if backend is makefile:
        executable = backend.configured_program(root, "coqdep")
        if not Path(executable).is_file() and shutil.which(executable) is None:
            pytest.skip("requires native coqdep")
    for _, physical, _ in common.FIXED_LOAD_PATH_MAPPINGS:
        (root / physical).mkdir(parents=True, exist_ok=True)
    case = Path("Rocq/examples/demo")
    lib = case / "case_lib.v"
    strategy = case / "case_strategy.v"
    bridge = Path("Rocq/examples/shared/bridge.v")
    base = Path("Rocq/sets/Base.v")
    target = case / "case_goal_check.v"
    texts = {
        base: "Definition base : nat := 0.\n",
        lib: "From SetsClass Require Import Base.\nDefinition n : nat := base.\n",
        bridge: "From SimpleC.EE.demo Require Import case_lib.\nLemma bridge_ok : n = 0. Proof. reflexivity. Qed.\n",
        strategy: "From SimpleC.EE.shared Require Export bridge.\n",
        case / "case_goal.v": "From SimpleC.EE.demo Require Export case_strategy.\n",
        case / "case_proof_auto.v": "From SimpleC.EE.demo Require Import case_goal.\n",
        case / "case_proof_manual_part1.v": "From SimpleC.EE.demo Require Import case_goal.\nLemma vc : True. Proof. exact I. Qed.\n",
        case / "case_proof_manual.v": "From SimpleC.EE.demo Require Export case_proof_manual_part1.\n",
        target: "From SimpleC.EE.demo Require Import case_proof_manual.\nCheck vc.\n",
    }
    for source, text in texts.items():
        _write(root, source, text)
    if backend is dune:
        _write(root, "dune-project", "(lang dune 3.16)\n(using coq 0.9)\n")
        _write(root, "Rocq/sets/dune", "(coq.theory (name SetsClass))\n")
        _write(root, "Rocq/examples/dune", "(coq.theory (name SimpleC.EE) (theories SetsClass))\n(include_subdirs qualified)\n")
    else:
        _write(root, "Rocq/Makefile", "# Native fixture\n")
    plan = common.prepare_plan(backend, root=root, target=target, anchor=target,
                               deadline=time.monotonic() + 120, all_current=True)
    assert common.validate_plan(root, backend, plan) == plan
    receipt = common.preparation_receipt(plan, time.monotonic(), time.monotonic() + 120)
    assert receipt["base_artifact_count"] == 1
    assert receipt["current_source_count"] == len(texts) - 1
    base_root = root / "_build/default" if backend is dune else root
    assert (base_root / base.with_suffix(".vo")).is_file()
    assert not (base_root / bridge.with_suffix(".vo")).exists()
    build = root / "verification_runs/case-20261016000000/_coq_builds/parent/src"
    kwargs = dict(workspace_root=root, build_workspace=build, target_file=target,
                  target_kind="parent", current_case_anchor=target, timeout_seconds=120)
    passed = common.run_coqc_check(backend, **kwargs)
    assert passed["status"] == "passed", passed.get("stderr_tail", passed)
    assert {strategy.as_posix(), bridge.as_posix(), lib.as_posix(),
            (case / "case_proof_manual_part1.v").as_posix()} <= set(passed["recompiled_target_files"])
    assert base.as_posix() not in passed["recompiled_target_files"]
    debug = common.run_coqtop_debug(backend, workspace_root=root, build_workspace=build,
                                   debug_script=case / "case_proof_manual.v", current_case_anchor=target,
                                   timeout_seconds=120)
    assert debug["status"] == "passed", debug.get("stderr_tail", debug)
    replacement = _write(root, "verification_runs/case-20261016000000/new_lib.v", "Definition n : nat := 1.\n")
    failed = common.run_coqc_check(backend, **kwargs, overlays={lib: replacement})
    assert failed["status"] == "failed" and "bridge.v" in str(failed), failed
    # Rebuilding a dependency does not grant permission to edit it via an overlay.
    denied = common.run_coqc_check(backend, **kwargs, overlays={bridge: replacement})
    assert denied["status"] == "failed" and "Overlay destinations" in str(denied), denied
    assert all((root / source).read_text(encoding="utf-8") == text for source, text in texts.items())
