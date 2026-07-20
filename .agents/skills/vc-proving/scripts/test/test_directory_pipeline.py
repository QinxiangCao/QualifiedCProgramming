from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

import coq_tooling
import prepare_group_workers
import verify_group_results
from group_plan_utils import group_entries_from_plan
from init_vc_proving_round import create_base_manifest
from path_utils import (
    ANNOTATION_ATTEMPTS_DIR_NAME,
    ANNOTATION_HISTORY_DIR_NAME,
    CONTROLLER_STATE_FILE_NAME,
    GROUP_WORKER_FILE_SET,
    REPORTS_DIR_NAME,
    RUN_BUILDS_DIR_NAME,
    VERIFICATION_RUNS_DIR_NAME,
    ensure_run_root,
    reports_root,
    target_files_for_c,
)
from proof_manual_utils import (
    ASSUMPTION_DECLARATION_KINDS,
    block_has_admitted,
    forbidden_top_level_declarations,
    helper_namespace_for_group_id,
    lib_contract_errors,
    merge_group_worker_libs,
    parse_manual_file,
    rollback_control_commands,
    split_manual_diagnostics,
    unsafe_assumption_declarations,
    unsafe_typing_commands,
)


def test_incomplete_proof_markers_allow_whitespace_and_ignore_comments() -> None:
    assert block_has_admitted("Lemma x : True. Proof. Admitted .")
    assert block_has_admitted("Lemma x : True. Proof. Admitted (* hidden *) .")
    assert block_has_admitted("Lemma x : True. Proof. Abort (* hidden *) .")
    assert any("Admitted" in error for error in lib_contract_errors("Lemma x : True. Proof. Admitted (* hidden *) ."))
    assert any("Abort" in error for error in lib_contract_errors("Lemma x : True. Proof. Abort (* hidden *) ."))
    assert any("Axiom" in error for error in lib_contract_errors("Axiom (* hidden *) shortcut : True."))
    assert any("Parameter" in error for error in lib_contract_errors("Parameter shortcut : False."))
    assert any("Conjecture" in error for error in lib_contract_errors("Conjecture shortcut : False."))
    assert any("Hypothesis" in error for error in lib_contract_errors("Hypothesis shortcut : False."))
    assert any("Variable" in error for error in lib_contract_errors("Variable shortcut : False."))
    assert any("Context" in error for error in lib_contract_errors("Context (shortcut : False)."))
    section_context = "Section Safe. Variable x : nat. Context (y : nat). End Safe."
    assert unsafe_assumption_declarations(section_context) == []
    assert lib_contract_errors(section_context) == []
    succeed_escape = "Succeed Section Phantom. Hypothesis escape : False."
    assert [item["kind"] for item in rollback_control_commands(succeed_escape)] == ["Succeed"]
    assert [item["kind"] for item in unsafe_assumption_declarations(succeed_escape)] == ["Hypothesis"]
    assert any("rollback control command Succeed" in error for error in lib_contract_errors(succeed_escape))
    fail_escape = "Fail Section Phantom. Variable escape : False."
    assert [item["kind"] for item in rollback_control_commands(fail_escape)] == ["Fail"]
    assert [item["kind"] for item in unsafe_assumption_declarations(fail_escape)] == ["Variable"]
    succeed_lemma = "Succeed Lemma dummy : True. Hypothesis escape : False."
    assert [item["kind"] for item in unsafe_assumption_declarations(succeed_lemma)] == ["Hypothesis"]
    timeout_escape = "Timeout 1 Hypothesis escape : False."
    redirect_escape = 'Redirect "feedback.log" Variable escape : False.'
    assert [item["kind"] for item in unsafe_assumption_declarations(timeout_escape)] == ["Hypothesis"]
    assert [item["kind"] for item in unsafe_assumption_declarations(redirect_escape)] == ["Variable"]
    instructions_escape = "Instructions Hypothesis escape : False."
    assert [item["kind"] for item in unsafe_assumption_declarations(instructions_escape)] == ["Hypothesis"]
    assert any("Hypothesis" in error for error in lib_contract_errors(instructions_escape))
    attributed_escape = "Time #[local] Hypothesis escape : False."
    assert [item["kind"] for item in unsafe_assumption_declarations(attributed_escape)] == ["Hypothesis"]
    for timeout in ("Timeout 1_0 Axiom escape : False.", "Timeout 0x1 Axiom escape : False."):
        assert [item["kind"] for item in unsafe_assumption_declarations(timeout)] == ["Axiom"]
        assert any("Axiom" in error for error in lib_contract_errors(timeout))
    quoted_bracket = '#[deprecated(note="]")] Axiom escape : False.'
    assert [item["kind"] for item in unsafe_assumption_declarations(quoted_bracket)] == ["Axiom"]
    assert any("Axiom" in error for error in lib_contract_errors(quoted_bracket))
    for unsafe in (
        "Unset Guard Checking. Fixpoint escape (n : nat) : False := escape n.",
        "Unset Positivity Checking.",
        "Unset Universe Checking.",
        "#[bypass_check(guard)] Fixpoint escape (n : nat) : False := escape n.",
        "#[bypass_check(positivity)] Inductive escape : Prop := make_escape.",
        "#[bypass_check(universes)] Definition escape : Type := Type.",
    ):
        assert unsafe_typing_commands(unsafe)
        assert any("unsafe typing control" in error for error in lib_contract_errors(unsafe))
    escaped = "Lemma x : True. Proof. exact I. Qed. Axiom escape : False. Definition hidden := 0."
    assert [item["kind"] for item in forbidden_top_level_declarations(escaped, {"Axiom", "Definition"})] == [
        "Axiom",
        "Definition",
    ]
    comment_separator = "Lemma x : True. Proof. exact I. Qed.(* separator *)Axiom escape : False."
    assert [item["kind"] for item in forbidden_top_level_declarations(comment_separator, {"Axiom"})] == ["Axiom"]
    assert forbidden_top_level_declarations("Lemma x : True. Proof. exact Foo.Definition. Qed.", {"Definition"}) == []
    assumption_escape = "Lemma x : True. Proof. exact I. Qed. Parameter escape : False."
    assert [
        item["kind"]
        for item in forbidden_top_level_declarations(assumption_escape, ASSUMPTION_DECLARATION_KINDS)
    ] == ["Parameter"]


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _repo(tmp_path: Path) -> tuple[Path, Path, Path, Path]:
    repo = tmp_path / "repo"
    (repo / "QCP_examples" / "LLM_bench" / "Algorithms" / "demo").mkdir(parents=True)
    formal = repo / "SeparationLogic" / "examples" / "LLM_bench" / "Algorithms" / "demo"
    formal.mkdir(parents=True)
    target = repo / "QCP_examples" / "LLM_bench" / "Algorithms" / "demo" / "demo.c"
    manual = formal / "demo_proof_manual.v"
    formal_lib = formal / "demo_lib.v"
    target.write_text("int demo(void) { return 0; }\n", encoding="utf-8")
    manual.write_text("Lemma w1 : True.\nProof. Admitted.\n", encoding="utf-8")
    formal_lib.write_text("Require Import Coq.Init.Logic.\n", encoding="utf-8")
    (formal / "demo_goal.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (formal / "demo_proof_auto.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (formal / "demo_goal_check.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (formal / "demo_proof_diagnostics.v").write_text("", encoding="utf-8")
    (formal / "diagnostics_snapshot.json").write_text("{}\n", encoding="utf-8")
    return repo, target, manual, formal_lib


def _verified_group_plan(path: Path) -> None:
    _write_json(
        path,
        {
            "schema_version": "qcp-vc-checking-group-plan/v3",
            "source_goal_version": "goal-v1",
            "verified": True,
            "groups": [
                {
                    "id": "core",
                    "witnesses": ["w1"],
                    "depends_on": [],
                    "strategy": "prove True directly",
                }
            ],
        },
    )


def test_target_files_use_formal_case_lib_terminology() -> None:
    files = target_files_for_c("QCP_examples/LLM_bench/Algorithms/demo/demo.c")
    assert files["formal_case_lib"] == "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_lib.v"
    assert "case_lib" not in files
    assert files["proof_manual_file"].endswith("demo_proof_manual.v")


def test_run_root_uses_fixed_directory_layout(tmp_path: Path) -> None:
    repo, _target, _manual, _formal_lib = _repo(tmp_path)
    run = ensure_run_root(repo, "demo", timestamp="20260714120000")
    report = reports_root(run)
    assert run == repo / VERIFICATION_RUNS_DIR_NAME / "demo-20260714120000"
    assert (run / RUN_BUILDS_DIR_NAME).is_dir()
    assert (run / ANNOTATION_HISTORY_DIR_NAME).is_dir()
    assert report == repo / REPORTS_DIR_NAME / "demo-20260714120000"
    assert CONTROLLER_STATE_FILE_NAME == "controller_state.json"
    assert ANNOTATION_ATTEMPTS_DIR_NAME == "annotation-attempts"


def test_coq_executable_uses_makefile_and_configure_path(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    separation_logic = repo / "SeparationLogic"
    separation_logic.mkdir(parents=True)
    (separation_logic / "Makefile").write_text(
        "COQBIN ?=\nSUF ?=\n-include CONFIGURE\nCOQC=$(COQBIN)coqc$(SUF)\n",
        encoding="utf-8",
    )
    (separation_logic / "CONFIGURE").write_text(
        "COQBIN = /configured/coq/bin/\nSUF = .opt\n",
        encoding="utf-8",
    )
    assert coq_tooling.configured_coq_executable(repo, "coqc") == "/configured/coq/bin/coqc.opt"
    assert coq_tooling.make_coqc_argv("demo.v", workspace_root=repo)[0] == "/configured/coq/bin/coqc.opt"


def test_full_make_base_vo_reuse_covers_all_load_roots_and_runs(tmp_path: Path) -> None:
    repo, _target, _manual, _formal_lib = _repo(tmp_path)
    artifacts = {
        repo / "SeparationLogic" / "tracelib" / "TraceLib.vo": b"trace base",
        repo / "SeparationLogic" / "coq-record-update" / "src" / "RecordUpdate.vo": b"record base",
        repo / "SeparationLogic" / "algorithms" / "MapLib.vo": b"algorithm base",
    }
    for path, content in artifacts.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
    runs = [
        ensure_run_root(repo, "demo", timestamp="20260714120001"),
        ensure_run_root(repo, "demo", timestamp="20260714120002"),
    ]

    for run in runs:
        build = run / RUN_BUILDS_DIR_NAME / "full-flow" / "src"
        reused = coq_tooling.reuse_base_vo_files(repo, build)
        for path, content in artifacts.items():
            relative = path.relative_to(repo)
            assert relative.as_posix() in reused
            assert (build / relative).read_bytes() == content

    flags = coq_tooling.fixed_flags()
    assert ["-R", "SeparationLogic/tracelib", "TraceLib"] == flags[-9:-6]
    assert ["-R", "SeparationLogic/coq-record-update/src", "RecordUpdate"] == flags[-6:-3]
    assert ["-Q", "SeparationLogic/algorithms", "Algorithms"] == flags[-3:]
    assert coq_tooling.logical_module_to_relative("TraceLib.TraceBasic") == Path(
        "SeparationLogic/tracelib/TraceBasic.v"
    )
    assert coq_tooling.logical_module_to_relative("RecordUpdate.RecordSet") == Path(
        "SeparationLogic/coq-record-update/src/RecordSet.v"
    )
    assert coq_tooling.logical_module_to_relative("Algorithms.BFS.BFS") == Path(
        "SeparationLogic/algorithms/BFS/BFS.v"
    )


def test_full_make_base_vo_is_reused_but_target_case_vo_is_removed(tmp_path: Path) -> None:
    repo, _target, _manual, formal_lib = _repo(tmp_path)
    run = ensure_run_root(repo, "demo", timestamp="20260714120001")
    build = run / RUN_BUILDS_DIR_NAME / "parent" / "src"
    base_source = repo / "SeparationLogic" / "auxlibs" / "Base.v"
    base_vo = base_source.with_suffix(".vo")
    base_source.parent.mkdir(parents=True, exist_ok=True)
    base_source.write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    base_vo.write_bytes(b"trusted full make artifact")
    goal_check = formal_lib.with_name("demo_goal_check.v")
    goal_check.write_text("From AUXLib Require Import Base.\n", encoding="utf-8")
    current_sources = coq_tooling.target_case_sources(goal_check.relative_to(repo))
    coq_tooling.mirror_sources(repo, build)
    stale_target_vo = build / formal_lib.relative_to(repo).with_suffix(".vo")
    stale_target_vo.parent.mkdir(parents=True, exist_ok=True)
    stale_target_vo.write_bytes(b"stale target artifact")

    removed = coq_tooling.remove_target_case_side_products(build, current_sources)
    reused = coq_tooling.reuse_base_vo_files(repo, build, excluded_sources=current_sources)

    assert formal_lib.relative_to(repo).with_suffix(".vo").as_posix() in removed
    assert not stale_target_vo.exists()
    assert base_vo.relative_to(repo).as_posix() in reused
    assert (build / base_vo.relative_to(repo)).read_bytes() == base_vo.read_bytes()
    assert formal_lib.relative_to(repo).with_suffix(".vo").as_posix() not in reused
    order, errors = coq_tooling._compile_order(
        build,
        goal_check.relative_to(repo),
        current_case_sources=current_sources,
    )
    assert errors == []
    assert base_source.relative_to(repo) not in order
    (build / base_vo.relative_to(repo)).unlink()
    _order, missing_errors = coq_tooling._compile_order(
        build,
        goal_check.relative_to(repo),
        current_case_sources=current_sources,
    )
    assert missing_errors == [
        "missing trusted base .vo from the prerequisite full make: " + base_vo.relative_to(repo).as_posix()
    ]


def test_coq_tooling_rejects_build_directory_outside_run(tmp_path: Path) -> None:
    repo, _target, _manual, formal_lib = _repo(tmp_path)
    error = coq_tooling.build_workspace_layout_error(repo, tmp_path / "outside")
    assert error is not None
    assert "verification_runs" in error
    result = coq_tooling.run_coqc_check(
        workspace_root=repo,
        build_workspace=tmp_path / "outside",
        target_file=formal_lib.relative_to(repo),
        target_kind="formal-case-lib",
        source_goal_version="goal-v1",
    )
    assert result["schema_version"] == "qcp-coqc-check-result/v3"
    assert result["status"] == "failed"
    assert "argv" not in result
    run = ensure_run_root(repo, "demo", timestamp="20260714120100")
    assert coq_tooling.build_workspace_layout_error(repo, run / "_coq_builds" / "group" / "src") is None


def test_coq_tooling_overlay_replaces_only_declared_sources(tmp_path: Path) -> None:
    repo, _target, manual, formal_lib = _repo(tmp_path)
    run = ensure_run_root(repo, "demo", timestamp="20260714120200")
    group = run / "demo-vc-proving-r1" / "groups" / "group_00__core"
    group.mkdir(parents=True)
    copied_manual = group / manual.name
    copied_lib = group / formal_lib.name
    copied_manual.write_text("Lemma w1 : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    copied_lib.write_text(formal_lib.read_text(encoding="utf-8"), encoding="utf-8")
    build = run / "_coq_builds" / "group" / "src"
    mirrored, overlaid = coq_tooling.mirror_sources(
        repo,
        build,
        overlays={
            Path("SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_proof_manual.v"): copied_manual,
            Path("SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_lib.v"): copied_lib,
        },
    )
    assert set(overlaid) == {
        "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_proof_manual.v",
        "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_lib.v",
    }
    assert set(overlaid) <= set(mirrored)
    assert "exact I" in (build / Path(overlaid[1] if overlaid[1].endswith("proof_manual.v") else overlaid[0])).read_text(encoding="utf-8")


def test_create_base_manifest_and_prepare_groups(tmp_path: Path) -> None:
    repo, _target, manual, formal_lib = _repo(tmp_path)
    run = ensure_run_root(repo, "demo", timestamp="20260714120300")
    round_id = "demo-vc-proving-r1"
    report_dir = reports_root(run) / "rounds" / round_id
    base_path = create_base_manifest(
        manual_file=manual,
        formal_case_lib=formal_lib,
        main_root=repo,
        run_root=run,
        round_report_directory=report_dir,
        vc_proving_round_id=round_id,
        source_goal_version="goal-v1",
    )
    plan = report_dir / "group_plan.json"
    _verified_group_plan(plan)
    groups = prepare_group_workers.prepare_group_workers(base_path, group_plan_path=plan)
    assert base_path == run / round_id / "base_manifest.json"
    assert len(groups) == 1
    group = groups[0]
    directory = Path(group["directory"])
    assert directory == run / round_id / "groups" / "group_00__core"
    assert {path.name for path in directory.iterdir()} == {manual.name, formal_lib.name}
    assert Path(group["proof_manual"]).read_text(encoding="utf-8") == manual.read_text(encoding="utf-8")
    assert Path(group["group_worker_lib"]).read_text(encoding="utf-8") == formal_lib.read_text(encoding="utf-8")
    manifest_path = report_dir / "group_workers_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest["schema_version"] == "qcp-vc-proving-group-workers-manifest/v3"
    assert manifest["base_manifest"] == str(base_path)
    handoff_dir = report_dir / "groups" / directory.name
    assert {path.name for path in handoff_dir.iterdir()} == set(GROUP_WORKER_FILE_SET)
    worker_input = (handoff_dir / "group_worker_input.md").read_text(encoding="utf-8")
    assert str(directory / formal_lib.name) in worker_input
    assert formal_lib.relative_to(repo).as_posix() in worker_input
    assert "controller.py" in worker_input
    assert "coq-check" in worker_input
    assert "--group core" in worker_input
    assert "--overlay" not in worker_input


def test_prepare_groups_rejects_unverified_plan(tmp_path: Path) -> None:
    repo, _target, manual, formal_lib = _repo(tmp_path)
    run = ensure_run_root(repo, "demo", timestamp="20260714120400")
    report_dir = reports_root(run) / "rounds" / "demo-vc-proving-r1"
    base = create_base_manifest(
        manual_file=manual,
        formal_case_lib=formal_lib,
        main_root=repo,
        run_root=run,
        round_report_directory=report_dir,
        vc_proving_round_id="demo-vc-proving-r1",
        source_goal_version="goal-v1",
    )
    plan = report_dir / "group_plan.json"
    _write_json(plan, {"groups": [{"id": "core", "witnesses": ["w1"]}]})
    with pytest.raises(SystemExit, match="controller-verified"):
        prepare_group_workers.prepare_group_workers(base, group_plan_path=plan)


def test_parent_verify_rejects_noncanonical_base_manifest_path(tmp_path: Path) -> None:
    repo, _target, manual, formal_lib = _repo(tmp_path)
    run = ensure_run_root(repo, "demo", timestamp="20260714120401")
    report_dir = reports_root(run) / "rounds" / "demo-vc-proving-r1"
    base = create_base_manifest(
        manual_file=manual,
        formal_case_lib=formal_lib,
        main_root=repo,
        run_root=run,
        round_report_directory=report_dir,
        vc_proving_round_id="demo-vc-proving-r1",
        source_goal_version="goal-v1",
    )
    plan = report_dir / "group_plan.json"
    _verified_group_plan(plan)
    prepare_group_workers.prepare_group_workers(base, group_plan_path=plan)
    alternate = base.with_name("alternate_base_manifest.json")
    alternate.write_text(base.read_text(encoding="utf-8"), encoding="utf-8")
    manifest_path = report_dir / "group_workers_manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["base_manifest"] = str(alternate)
    _write_json(manifest_path, manifest)
    with pytest.raises(SystemExit, match="fixed vc-proving path"):
        verify_group_results.verify_and_merge(manifest_path, main_root=repo)


def test_parent_verify_creates_proving_merged_without_touching_formal_files(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo, _target, manual, formal_lib = _repo(tmp_path)
    run = ensure_run_root(repo, "demo", timestamp="20260714120500")
    report_dir = reports_root(run) / "rounds" / "demo-vc-proving-r1"
    base = create_base_manifest(
        manual_file=manual,
        formal_case_lib=formal_lib,
        main_root=repo,
        run_root=run,
        round_report_directory=report_dir,
        vc_proving_round_id="demo-vc-proving-r1",
        source_goal_version="goal-v1",
    )
    plan = report_dir / "group_plan.json"
    _verified_group_plan(plan)
    [group] = prepare_group_workers.prepare_group_workers(base, group_plan_path=plan)
    group_manual = Path(group["proof_manual"])
    group_manual.write_text("Lemma w1 : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    report_path = Path(group["report_directory"]) / "group_worker_report.json"
    report = {
        "schema_version": "qcp-group-worker-report/v2",
        "status": "completed",
        "source_goal_version": "goal-v1",
        "blockers": [],
    }
    _write_json(report_path, report)
    original_manual = manual.read_text(encoding="utf-8")
    original_lib = formal_lib.read_text(encoding="utf-8")

    def passed_check(**kwargs: Any) -> dict[str, Any]:
        return {
            "status": "passed",
            "returncode": 0,
            "target_kind": kwargs["target_kind"],
            "source_goal_version": kwargs["source_goal_version"],
            "overlaid_sources": [path.as_posix() for path in kwargs["overlays"]],
        }

    monkeypatch.setattr(verify_group_results, "run_coqc_check", passed_check)
    merged_report = verify_group_results.verify_and_merge(report_dir / "group_workers_manifest.json", main_root=repo)
    merged = merged_report
    assert merged["status"] == "passed"
    assert "exact I" in Path(merged["candidate"]["proof_manual"]).read_text(encoding="utf-8")
    assert Path(merged["candidate"]["proving_merged_lib"]).parent == run / "demo-vc-proving-r1" / "proving_merged"
    assert manual.read_text(encoding="utf-8") == original_manual
    assert formal_lib.read_text(encoding="utf-8") == original_lib
    assert (report_dir / "proving_merged_result.json").is_file()


def test_parent_verify_rejects_extra_group_files(tmp_path: Path) -> None:
    repo, _target, manual, formal_lib = _repo(tmp_path)
    run = ensure_run_root(repo, "demo", timestamp="20260714120600")
    report_dir = reports_root(run) / "rounds" / "demo-vc-proving-r1"
    base = create_base_manifest(
        manual_file=manual,
        formal_case_lib=formal_lib,
        main_root=repo,
        run_root=run,
        round_report_directory=report_dir,
        vc_proving_round_id="demo-vc-proving-r1",
        source_goal_version="goal-v1",
    )
    plan = report_dir / "group_plan.json"
    _verified_group_plan(plan)
    [group] = prepare_group_workers.prepare_group_workers(base, group_plan_path=plan)
    (Path(group["directory"]) / "debug.v").write_text("Check True.\n", encoding="utf-8")
    report = verify_group_results.verify_and_merge(report_dir / "group_workers_manifest.json", main_root=repo)
    assert report["status"] == "failed"
    assert any("only manual and group_worker_lib" in error for error in report["errors"])


def test_group_plan_requires_exact_controller_verified_coverage() -> None:
    lemmas = [{"name": "w1"}, {"name": "w2"}]
    plan = {
        "schema_version": "qcp-vc-checking-group-plan/v3",
        "source_goal_version": "goal-v1",
        "groups": [{"id": "g1", "witnesses": ["w1", "w2"]}],
    }
    with pytest.raises(SystemExit, match="controller-verified"):
        group_entries_from_plan(
            lemmas,
            plan,
            require_controller_verified=True,
            source_goal_version="goal-v1",
        )
    plan["verified"] = True
    entries = group_entries_from_plan(lemmas, plan, require_controller_verified=True, source_goal_version="goal-v1")
    assert [entry["group_id"] for entry in entries] == ["g1"]


def test_lib_merge_enforces_group_suffix_and_preserves_seed() -> None:
    seed = "Require Import Coq.Init.Logic.\n\nLemma seed_ok : True.\nProof. exact I. Qed.\n"
    namespace = helper_namespace_for_group_id("g1")
    good = seed + "\nLemma helper__g1 : True.\nProof. exact I. Qed.\n"
    merged, added, errors = merge_group_worker_libs(seed, [("g1", good, namespace)])
    assert errors == []
    assert [item["name"] for item in added] == ["helper__g1"]
    assert "Lemma seed_ok" in merged
    bad = seed + "\nLemma helper : True.\nProof. exact I. Qed.\n"
    _merged, _added, errors = merge_group_worker_libs(seed, [("g1", bad, namespace)])
    assert any("must end with current suffix" in error for error in errors)
    hidden_definition = seed + "\nLemma helper__g1 : True. Proof. exact I. Qed. Definition escape := 0.\n"
    _merged, _added, errors = merge_group_worker_libs(seed, [("g1", hidden_definition, namespace)])
    assert any("forbidden kind `Definition`" in error for error in errors)
    hidden_assumption = seed + "\nLemma helper__g1 : True. Proof. exact I. Qed. Parameter escape : False.\n"
    _merged, _added, errors = merge_group_worker_libs(seed, [("g1", hidden_assumption, namespace)])
    assert any("assumption declaration Parameter" in error or "forbidden kind `Parameter`" in error for error in errors)
    hidden_helper = seed + "\nLemma helper__g1 : True. Proof. exact I. Qed. Lemma escape__g1 : True. Proof. exact I. Qed.\n"
    _merged, _added, errors = merge_group_worker_libs(seed, [("g1", hidden_helper, namespace)])
    assert any("not a standalone parseable block" in error for error in errors)


def test_manual_diagnostics_split_is_separate_from_target_witnesses() -> None:
    mixed = "From Coq Require Import Init.Logic.\nLemma proof_of_w1_split_goal_1 : w1_split_goal_1.\nProof. Abort.\nLemma w1 : True.\nProof. Admitted.\n"
    with pytest.raises(ValueError, match="diagnostic"):
        parse_manual_file(mixed)
    split = split_manual_diagnostics(mixed)
    assert "proof_of_w1_split_goal_1" not in split["proof_manual_text"]
    assert split["diagnostics_snapshot"]["manual_obligation_count"] == 1
