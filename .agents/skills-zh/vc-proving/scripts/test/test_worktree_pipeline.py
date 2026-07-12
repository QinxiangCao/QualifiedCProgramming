from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any

import pytest

import prepare_group_worktrees
import verify_group_results
from group_plan_utils import group_entries_from_plan
from coq_tooling import (
    FIXED_R_MAPPINGS,
    fixed_flags_hash,
    infer_case_config,
    make_coqc_argv,
    make_coqtop_argv,
    run_coqc_check,
    run_coqtop_debug,
)
from proof_manual_utils import (
    helper_namespace_for_group_id,
    merge_case_lib,
    parse_manual_file,
    split_manual_diagnostics,
    write_split_manual_artifacts,
)
from worktree_utils import (
    GROUP_WORKER_FILE_SET,
    REPORTS_DIR_NAME,
    RUN_BUILDS_DIR_NAME,
    WORKTREE_ROOT_NAME,
    coq_identifier_slug,
    default_round_workspace,
    group_worker_spawn_message,
    init_group_worker_files,
)


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _passed_coqc_evidence(
    argv: list[str],
    *,
    cwd: str,
    target_file: str = "case/demo_goal_check.v",
    source_goal_version: str = "goal-digest",
) -> dict[str, Any]:
    return {
        "schema_version": "qcp-coqc-check-evidence/v1",
        "status": "passed",
        "tool": "coqc",
        "kind": "coqc_check",
        "argv": argv,
        "cwd": cwd,
        "returncode": 0,
        "target_file": target_file,
        "target_kind": "check",
        "fixed_flags_hash": fixed_flags_hash(),
        "source_goal_version": source_goal_version,
        "stdout_tail": "",
        "stderr_tail": "",
        "first_diagnostic": None,
    }


def _grouping_policy(count: int, max_per_group: int = 4) -> dict[str, Any]:
    return {
        "schema_version": "qcp-grouping-policy/v1",
        "controller_policy": "bounded-witness-groups/v1",
        "controller_enforced": "yes",
        "target_witness_count": count,
        "max_witnesses_per_group": max_per_group,
        "single_group_allowed_only_if_target_witness_count_lte": max_per_group,
        "oversized_group_rejected": "yes",
    }


def test_coq_identifier_slug_replaces_hyphens() -> None:
    assert coq_identifier_slug("g01-quicksort-partition-core") == "g01_quicksort_partition_core"
    assert coq_identifier_slug("01-group") == "_01_group"


def test_default_round_workspace_uses_run_root_layout(tmp_path: Path) -> None:
    repo_root = tmp_path / "repo"
    manual_file = repo_root / "QCP_examples" / "case" / "demo_proof_manual.v"
    manual_file.parent.mkdir(parents=True)
    manual_file.write_text("Lemma w1 : True.\nProof. Admitted.\n", encoding="utf-8")

    workspace = default_round_workspace(repo_root, manual_file, timestamp="20260608120000")

    run_root = repo_root / WORKTREE_ROOT_NAME / "case-20260608120000"
    report_root = repo_root / REPORTS_DIR_NAME / "case-20260608120000"
    assert workspace == report_root / "rounds" / "repo"
    assert (run_root / RUN_BUILDS_DIR_NAME).is_dir()
    assert report_root.is_dir()


def test_group_worker_handoff_file_set(tmp_path: Path) -> None:
    group_worktree = tmp_path / "group"
    report_dir = tmp_path / "reports" / "groups" / "group"
    group_worktree.mkdir()
    coqc_argv = make_coqc_argv("case/demo_goal_check.v")
    coqtop_argv = make_coqtop_argv(".coq_debug/demo.v")
    init_group_worker_files(
        group_worktree=group_worktree,
        report_dir=report_dir,
        group_id="arith",
        assigned_witnesses=["w1"],
        group_workers_manifest=tmp_path / "group_workers_manifest.json",
        group_manifest={
            "source_goal_version": "goal-digest",
            "helper_namespace": helper_namespace_for_group_id("arith"),
            "tooling": {
                "coqc_check_argv": coqc_argv,
                "coqtop_debug_argv": coqtop_argv,
                "coq_build_workspace": str(tmp_path / "builds" / "g1" / "src"),
                "coqc_check_target_file": "case/demo_goal_check.v",
                "target_kind": "check",
                "fixed_flags_hash": fixed_flags_hash(),
            },
            "handoff": {"rendered_instructions_compact": group_worker_spawn_message("input", "report")},
        },
    )

    assert {path.name for path in report_dir.iterdir()} == set(GROUP_WORKER_FILE_SET)
    assert list(group_worktree.iterdir()) == []
    payload = json.loads((report_dir / "group_worker_input.json").read_text(encoding="utf-8"))
    assert payload["handoff"]["rendered_instructions_compact"].startswith("Read input.")
    assert "The goal is to complete the group-worker task assigned by group_worker_input.json" in payload["handoff"]["rendered_instructions_compact"]
    assert "is only the final report file recording the result" in payload["handoff"]["rendered_instructions_compact"]
    assert "No compromise operations" in payload["handoff"]["rendered_instructions_compact"]
    assert "Minimize respawns" in payload["zero_context_protocol"]["spawn_message"]
    assert "Do not stop for confirmation" in payload["zero_context_protocol"]["spawn_message"]
    zero_context_message = payload["zero_context_protocol"]["spawn_message"]
    assert zero_context_message.startswith("Read ")
    assert "The goal is to complete the group-worker task assigned by group_worker_input.json" in zero_context_message
    assert "is only the final report file recording the result" in zero_context_message
    assert "Before acting, read group_worker_input.json completely" in zero_context_message
    assert "No compromise operations" in zero_context_message
    assert "Task completion means the assigned group proof work is completed" in zero_context_message
    assert "Controller/parent verification acceptance is separate" in zero_context_message
    assert "previous output notes are non-authoritative" in zero_context_message
    assert "Compact-error is not your blocked judgment" in zero_context_message
    assert payload["helper_namespace"] == helper_namespace_for_group_id("arith")
    assert payload["single_spawn_policy"]["preferred"] == "yes"
    assert "failed tactic" in payload["single_spawn_policy"]["continue_without_confirmation"]
    assert payload["startup"]["method"] == "main-agent-worker-attempt"
    assert payload["startup"]["script_launch_allowed"] == "no"
    assert "resume_policy" not in payload["startup"]
    assert payload["attempt_control"]["on_compact_error"] == "main-agent-restarts-worker"
    assert payload["attempt_control"]["heartbeat_policy"] == "no-timeout-retry"
    assert payload["reports"] == {
        "input": str((report_dir / "group_worker_input.json").resolve()),
        "report": str((report_dir / "group_worker_report.json").resolve()),
        "output": str((report_dir / "group_worker_output.txt").resolve()),
    }
    assert payload["output_contract"]["kind"] == "non-authoritative-reuse-note"
    report = json.loads((report_dir / "group_worker_report.json").read_text(encoding="utf-8"))
    group = report["agent_result"]["vc_proving"]["group"]
    assert group["assigned_witnesses"] == ["w1"]
    assert group["helper_namespace"] == helper_namespace_for_group_id("arith")
    assert group["case_lib_added_declarations"] == []
    assert group["unsolved_witnesses"] == ["w1"]
    assert group["verification_result"]["coqc_check"]["status"] == "pending"
    assert group["verification_result"]["coqc_check"]["argv"] == coqc_argv
    assert group["verification_result"]["coqtop_debug"]["argv"] == coqtop_argv


def test_init_vc_proving_manifest_requires_controller_source_goal_version(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    round_worktree = repo / "worktrees" / "demo-20260608121212" / "demo-vc-proving-r1"
    case_dir = round_worktree / "SeparationLogic" / "examples" / "LLM_bench" / "Algorithms" / "demo"
    case_dir.mkdir(parents=True)
    manual = case_dir / "demo_proof_manual.v"
    case_lib = case_dir / "demo_lib.v"
    (repo / "reports" / "demo-20260608121212" / "rounds" / "demo-vc-proving-r1").mkdir(parents=True)
    (repo / "dune-project").write_text("(lang dune 3.0)\n", encoding="utf-8")
    manual.write_text("Lemma w1 : True.\nProof. Admitted.\n", encoding="utf-8")
    case_lib.write_text("Require Import Coq.Init.Logic.\n", encoding="utf-8")
    subprocess.run(["git", "init"], cwd=repo, check=True, stdout=subprocess.PIPE)
    subprocess.run(["git", "init"], cwd=round_worktree, check=True, stdout=subprocess.PIPE)
    script = Path(__file__).resolve().parents[1] / "init_vc_proving_round.py"

    missing = subprocess.run(
        ["python3", str(script), str(manual), "--case-lib", str(case_lib)],
        cwd=repo,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    ok = subprocess.run(
        [
            "python3",
            str(script),
            str(manual),
            "--case-lib",
            str(case_lib),
            "--source-goal-version",
            "controller-digest",
        ],
        cwd=repo,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )

    assert missing.returncode != 0
    assert ok.returncode == 0, ok.stderr
    manifest = next((repo / "reports").glob("*/rounds/*/group_workers_manifest.json"))
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    assert payload["source_goal_version"] == "controller-digest"


def test_case_lib_merge_rejects_seed_edit_and_name_conflict() -> None:
    seed = "Require Import Coq.Init.Logic.\n\nLemma seed_ok : True.\nProof. exact I. Qed.\n"
    edited_seed = "Require Import Coq.Init.Logic.\n\nLemma seed_ok : True.\nProof. trivial. Qed.\n"
    ns_g1 = helper_namespace_for_group_id("g1")
    ns_g2 = helper_namespace_for_group_id("g2")
    _merged, _added, errors = merge_case_lib(seed, [("g1", edited_seed, ns_g1)])
    assert any("modified seed case_lib declaration `seed_ok`" in error for error in errors)

    deleted_seed = "Require Import Coq.Init.Logic.\n"
    _merged, _added, errors = merge_case_lib(seed, [("g1", deleted_seed, ns_g1)])
    assert any("removed seed case_lib declaration `seed_ok`" in error for error in errors)

    group_a = seed + "\nLemma helper__g1 : True.\nProof. exact I. Qed.\n"
    group_b = seed + "\nLemma helper__g1 : True.\nProof. exact I. Qed.\n"
    _merged, _added, errors = merge_case_lib(seed, [("g1", group_a, ns_g1), ("g2", group_b, ns_g2)])
    assert any("foreign helper suffix" in error or "must end with current suffix" in error for error in errors)


def test_case_lib_merge_enforces_group_helper_suffixes() -> None:
    seed = "Require Import Coq.Init.Logic.\n"
    ns_g1 = helper_namespace_for_group_id("g1")
    ns_g2 = helper_namespace_for_group_id("g2")

    unsuffixed = seed + "\nLemma helper : True.\nProof. exact I. Qed.\n"
    _merged, _added, errors = merge_case_lib(seed, [("g1", unsuffixed, ns_g1)])
    assert any("must end with current suffix" in error for error in errors)

    foreign = seed + "\nLemma helper__g2 : True.\nProof. exact I. Qed.\n"
    _merged, _added, errors = merge_case_lib(seed, [("g1", foreign, ns_g1)])
    assert any("must end with current suffix" in error for error in errors)

    group_a = seed + "\nLemma helper__g1 : True.\nProof. exact I. Qed.\n"
    group_b = seed + "\nLemma helper__g2 : True.\nProof. exact I. Qed.\n"
    merged, added, errors = merge_case_lib(seed, [("g1", group_a, ns_g1), ("g2", group_b, ns_g2)])
    assert errors == []
    assert [decl["name"] for decl in added] == ["helper__g1", "helper__g2"]
    assert "Lemma helper__g1 : True." in merged
    assert "Lemma helper__g2 : True." in merged


def test_case_lib_merge_allows_official_rocq_imports_only() -> None:
    seed = "Require Import Coq.Init.Logic.\n"
    ns_g1 = helper_namespace_for_group_id("g1")

    group_with_official_imports = (
        seed
        + "\nRequire Import Coq.micromega.Psatz.\n"
        + "From Coq Require Import Lists.List.\n"
        + "Lemma helper__g1 : True.\nProof. exact I. Qed.\n"
    )
    merged, added, errors = merge_case_lib(seed, [("g1", group_with_official_imports, ns_g1)])
    assert errors == []
    assert [(decl["kind"], decl["name"]) for decl in added] == [
        ("Import", "Require Import Coq.micromega.Psatz."),
        ("Import", "From Coq Require Import Lists.List."),
        ("Lemma", "helper__g1"),
    ]
    assert "Require Import Coq.micromega.Psatz." in merged
    assert merged.index("Require Import Coq.micromega.Psatz.") < merged.index("Lemma helper__g1")

    group_with_project_import = seed + "\nRequire Import AUXLib.ListLib.\n"
    _merged, _added, errors = merge_case_lib(seed, [("g1", group_with_project_import, ns_g1)])
    assert any("not an allowed official Rocq import" in error for error in errors)


def test_manual_parser_rejects_diagnostics_and_splitter_separates_artifacts(tmp_path: Path) -> None:
    mixed = (
        "From Coq Require Import Init.Logic.\n"
        "Lemma proof_of_w1_split_goal_1 : w1_split_goal_1.\nProof. Abort.\n"
        "Lemma w1 : True.\nProof. Admitted.\n"
    )
    with pytest.raises(ValueError, match="diagnostic"):
        parse_manual_file(mixed)

    split = split_manual_diagnostics(mixed)
    assert "proof_of_w1_split_goal_1" not in split["proof_manual_text"]
    assert "Lemma w1 : True." in split["proof_manual_text"]
    assert "proof_of_w1_split_goal_1" in split["proof_diagnostics_text"]
    assert split["diagnostics_snapshot"]["manual_obligation_count"] == 1
    assert split["diagnostics_snapshot"]["diagnostic_count"] == 1

    manual_path = tmp_path / "demo_proof_manual.v"
    manual_path.write_text(mixed, encoding="utf-8")
    result = write_split_manual_artifacts(manual_path)
    assert Path(result["proof_diagnostics_file"]).name == "demo_proof_diagnostics.v"
    assert (tmp_path / "diagnostics_snapshot.json").is_file()
    assert "_split_goal_" not in manual_path.read_text(encoding="utf-8")


def test_group_plan_must_be_controller_verified_and_exact() -> None:
    lemmas = [{"name": "w1"}, {"name": "w2"}]
    plan = {
        "source_goal_version": "goal-v1",
        "proof_groups": [
            {
                "group_id": "g1",
                "witness_names": ["w1", "w2"],
                "per_witness_plan": {"w1": {"pure_plan": "split pures"}},
                "candidate_helper_declarations": [{"name": "helper_shape"}],
                "difficulty": "hard",
            }
        ],
    }
    with pytest.raises(SystemExit, match="controller-verified"):
        group_entries_from_plan(lemmas, plan, require_controller_verified=True, source_goal_version="goal-v1")

    verified = {**plan, "controller_verified": True, "target_witnesses": ["w1"], "grouping_policy": _grouping_policy(1)}
    with pytest.raises(SystemExit, match="target_witnesses"):
        group_entries_from_plan(lemmas, verified, require_controller_verified=True, source_goal_version="goal-v1")

    verified["target_witnesses"] = ["w1", "w2"]
    verified["grouping_policy"] = _grouping_policy(2)
    entries = group_entries_from_plan(lemmas, verified, require_controller_verified=True, source_goal_version="goal-v1")
    assert [entry["group_id"] for entry in entries] == ["g1"]
    assert entries[0]["per_witness_plan"]["w1"]["pure_plan"] == "split pures"
    assert entries[0]["candidate_helper_declarations"][0]["name"] == "helper_shape"
    assert entries[0]["difficulty"] == "hard"


def test_prepare_group_worktrees_rejects_build_root_outside_run_root(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    run_root = repo / "worktrees" / "demo-20260608123000"
    round_worktree = run_root / "demo-vc-proving-r1"
    work_dir = repo / "reports" / "demo-20260608123000" / "rounds" / "demo-vc-proving-r1"
    work_dir.mkdir(parents=True)
    round_worktree.mkdir(parents=True)
    manifest = work_dir / "group_workers_manifest.json"
    _write_json(
        manifest,
        {
            "schema_version": "qcp-vc-proving-group-workers-manifest/v1",
            "round_worktree": str(round_worktree),
            "work_dir": str(work_dir),
            "round_report_directory": str(work_dir),
            "run_root": str(run_root),
            "main_workspace_root": str(repo),
            "coq_builds_root": str(tmp_path / "outside-builds"),
            "proof_manual_file": "case/demo_proof_manual.v",
            "case_lib": "case/demo_lib.v",
            "source_goal_version": "goal-digest",
            "lemmas": [{"name": "w1"}],
        },
    )

    with pytest.raises(SystemExit, match="coq_builds_root"):
        prepare_group_worktrees.prepare_group_worktrees(manifest, group_plan_path=tmp_path / "missing-plan.json")


def test_coq_tooling_fixed_argv_and_source_mirror_loads_vo(tmp_path: Path) -> None:
    workspace = tmp_path / "formal"
    for physical, _logical in FIXED_R_MAPPINGS:
        (workspace / physical).mkdir(parents=True, exist_ok=True)
    target_rel = Path("SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_goal_check.v")
    target = workspace / target_rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("Lemma demo_ok : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    debug_rel = Path(".coq_debug/demo_debug.v")
    debug = workspace / debug_rel
    debug.parent.mkdir(parents=True, exist_ok=True)
    debug.write_text(
        "From SimpleC.EE.LLM_bench.Algorithms.demo Require Import demo_goal_check.\nCheck demo_ok.\n",
        encoding="utf-8",
    )
    build_workspace = tmp_path / "build" / "src"

    assert "-o" not in make_coqc_argv(target_rel)
    check = run_coqc_check(
        workspace_root=workspace,
        build_workspace=build_workspace,
        target_file=target_rel,
        target_kind="check",
        source_goal_version="goal-digest",
    )
    assert check["status"] == "passed", check
    assert (build_workspace / target_rel.with_suffix(".vo")).is_file()
    assert not target.with_suffix(".vo").exists()

    debug_evidence = run_coqtop_debug(
        workspace_root=workspace,
        build_workspace=build_workspace,
        debug_script=debug_rel,
        source_goal_version="goal-digest",
    )
    assert debug_evidence["status"] == "passed", debug_evidence
    assert debug_evidence["argv"] == make_coqtop_argv(build_workspace / debug_rel)


def test_coq_tooling_handles_unqualified_local_require_in_mirror(tmp_path: Path) -> None:
    workspace = tmp_path / "formal"
    for physical, _logical in FIXED_R_MAPPINGS:
        (workspace / physical).mkdir(parents=True, exist_ok=True)
    core = workspace / "SeparationLogic" / "SeparationLogic" / "LocalCore.v"
    user = workspace / "SeparationLogic" / "SeparationLogic" / "UseLocal.v"
    core.write_text("Lemma local_core_ok : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    user.write_text("Require Export LocalCore.\nCheck local_core_ok.\n", encoding="utf-8")
    build_workspace = tmp_path / "build" / "src"

    check = run_coqc_check(
        workspace_root=workspace,
        build_workspace=build_workspace,
        target_file=Path("SeparationLogic/SeparationLogic/UseLocal.v"),
        target_kind="check",
        source_goal_version="goal-digest",
    )

    assert check["status"] == "passed", check
    assert (build_workspace / "LocalCore.v").read_text(encoding="utf-8") == "Require Export SimpleC.SL.LocalCore.\n"
    assert not core.with_suffix(".vo").exists()


def test_coq_tooling_group_check_uses_build_workspace_wrapper(tmp_path: Path) -> None:
    workspace = tmp_path / "formal"
    for physical, _logical in FIXED_R_MAPPINGS:
        (workspace / physical).mkdir(parents=True, exist_ok=True)
    case_dir = workspace / "SeparationLogic" / "examples" / "LLM_bench" / "Algorithms" / "demo"
    case_dir.mkdir(parents=True, exist_ok=True)
    (case_dir / "demo_goal.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (case_dir / "demo_proof_auto.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (case_dir / "demo_proof_manual.v").write_text(
        "From Coq Require Import Init.Logic.\nLemma w1 : True.\nProof. exact I. Qed.\n",
        encoding="utf-8",
    )
    build_workspace = tmp_path / "build" / "src"
    target = Path(".coq_group_checks/demo_group_g1_check.v")

    check = run_coqc_check(
        workspace_root=workspace,
        build_workspace=build_workspace,
        target_file=target,
        target_kind="group-check",
        source_goal_version="goal-digest",
        group_check={
            "case_theory": "SimpleC.EE.LLM_bench.Algorithms.demo",
            "require_modules": ["demo_goal", "demo_proof_auto", "demo_proof_manual"],
            "assigned_witnesses": ["w1"],
        },
    )

    assert check["status"] == "passed", check
    assert check["target_file"] == target.as_posix()
    assert (build_workspace / target).is_file()
    assert not (workspace / target).exists()


def _write_case_fixture(tmp_path: Path, *, evidence_overrides: dict[str, Any] | None = None) -> Path:
    round_worktree = tmp_path / "round"
    group_worktree = tmp_path / "group"
    work_dir = tmp_path / "work"
    round_report_dir = tmp_path / "reports" / "rounds" / "round"
    group_report_dir = round_report_dir / "groups" / "g1"
    manual_rel = Path("case/demo_proof_manual.v")
    case_lib_rel = Path("case/demo_lib.v")
    generated = {
        Path("case/demo_goal.v"): "(* goal *)\n",
        Path("case/demo_proof_auto.v"): "(* auto *)\n",
        Path("case/demo_goal_check.v"): "From Coq Require Import Init.Logic.\nRequire Import demo_proof_manual.\n",
    }
    seed_manual = "From Coq Require Import Init.Logic.\nLemma w1 : True.\nProof. Admitted.\n"
    solved_manual = "From Coq Require Import Init.Logic.\nLemma w1 : True.\nProof. exact I. Qed.\n"
    seed_lib = "Require Import Coq.Init.Logic.\n"
    helper_namespace = helper_namespace_for_group_id("g1")
    group_lib = seed_lib + "\nLemma helper__g1 : True.\nProof. exact I. Qed.\n"
    for root, manual_text, lib_text in [
        (round_worktree, seed_manual, seed_lib),
        (group_worktree, solved_manual, group_lib),
    ]:
        (root / manual_rel).parent.mkdir(parents=True, exist_ok=True)
        (root / manual_rel).write_text(manual_text, encoding="utf-8")
        (root / case_lib_rel).write_text(lib_text, encoding="utf-8")
        for rel, text in generated.items():
            (root / rel).write_text(text, encoding="utf-8")

    coqc_argv = make_coqc_argv("case/demo_goal_check.v")
    build_workspace = tmp_path / "builds" / "g1" / "src"
    group_tooling = {
        "coq_tooling_only": "yes",
        "main_workspace_root": str(tmp_path),
        "coq_workspace_root": str(group_worktree),
        "coq_tooling_helper": str(tmp_path / ".agents" / "skills" / "vc-proving" / "scripts" / "coq_tooling.py"),
        "coqc_check_argv": coqc_argv,
        "coqtop_debug_argv": make_coqtop_argv(".coq_debug/g1.v"),
        "coqc_check_target_file": "case/demo_goal_check.v",
        "target_kind": "check",
        "coq_build_workspace": str(build_workspace),
        "source_goal_version_required": "yes",
        "fixed_flags_hash": fixed_flags_hash(),
    }
    evidence = _passed_coqc_evidence(coqc_argv, cwd=str(build_workspace))
    if evidence_overrides:
        evidence.update(evidence_overrides)
    _write_json(
        group_report_dir / "group_worker_report.json",
        {
            "schema_version": "qcp-group-worker-report/v1",
            "agent_result": {
                "vc_proving": {
                    "group": {
                        "status": "completed",
                        "group_id": "g1",
                        "assigned_witnesses": ["w1"],
                        "helper_namespace": helper_namespace,
                        "source_goal_version": "goal-digest",
                        "solved_witnesses": ["w1"],
                        "unsolved_witnesses": [],
                        "case_lib_added_declarations": [
                            {"name": "helper__g1", "kind": "Lemma", "statement_hash": "test-hash"}
                        ],
                        "blockers": [],
                        "errors": [],
                        "verification_result": {"coqc_check": evidence},
                    }
                }
            },
        },
    )
    _write_json(
        work_dir / "group_workers_manifest.json",
        {
            "round_worktree": str(round_worktree),
            "work_dir": str(work_dir),
            "round_report_directory": str(round_report_dir),
            "proof_manual_file": str(manual_rel),
            "case_lib": str(case_lib_rel),
            "main_workspace_root": str(tmp_path),
            "coq_builds_root": str(tmp_path / "builds"),
            "round_check_file": "case/demo_goal_check.v",
            "source_goal_version": "goal-digest",
            "target_witnesses": ["w1"],
            "groups": [
                {
                    "group_id": "g1",
                    "helper_namespace": helper_namespace,
                    "worktree_path": str(group_worktree),
                    "witness_names": ["w1"],
                    "tooling": group_tooling,
                    "handoff_files": {"report": str(group_report_dir / "group_worker_report.json")},
                }
            ],
        },
    )
    return work_dir / "group_workers_manifest.json"


def test_verify_group_results_writes_group_merged_result(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    manifest_path = _write_case_fixture(tmp_path)
    parent_evidence = _passed_coqc_evidence(
        make_coqc_argv("case/demo_goal_check.v"),
        cwd=str(tmp_path / "builds" / "round" / "parent" / "src"),
    )
    monkeypatch.setattr(verify_group_results, "run_coqc_check", lambda **_kwargs: parent_evidence)

    report = verify_group_results.verify_and_merge(manifest_path)
    vc = report["agent_result"]["vc_proving"]
    merged = vc["group_merged_result"]
    assert vc["merge_vc_ready"] == "yes"
    assert (tmp_path / "reports" / "rounds" / "round" / "group_merged_result.json").is_file()
    assert merged["solved_witnesses"] == ["w1"]
    assert merged["verification_result"]["coqc_check"]["status"] == "passed"
    assert "Lemma helper__g1 : True." in (tmp_path / "round" / "case" / "demo_lib.v").read_text(encoding="utf-8")
    assert "Proof. exact I. Qed." in (tmp_path / "round" / "case" / "demo_proof_manual.v").read_text(encoding="utf-8")


@pytest.mark.parametrize(
    "override, expected",
    [
        ({"argv": ["coqc", "-q", "wrong.v"]}, "coqc_check argv does not exactly match"),
        ({"cwd": "/tmp/not-the-group-build-workspace"}, "coqc_check cwd"),
        ({"source_goal_version": "stale"}, "coqc_check source_goal_version mismatch"),
        ({"status": "failed", "returncode": 1}, "coqc_check evidence is not passed"),
    ],
)
def test_verify_group_results_rejects_bad_group_coqc_evidence(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    override: dict[str, Any],
    expected: str,
) -> None:
    manifest_path = _write_case_fixture(tmp_path, evidence_overrides=override)
    monkeypatch.setattr(verify_group_results, "run_coqc_check", lambda **_kwargs: pytest.fail("parent check should not run"))

    report = verify_group_results.verify_and_merge(manifest_path)

    merged = report["agent_result"]["vc_proving"]["group_merged_result"]
    assert merged["merge_vc_ready"] == "no"
    assert any(expected in error for error in merged["errors"])


def test_verify_group_results_rejects_modified_generated_file(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    manifest_path = _write_case_fixture(tmp_path)
    (tmp_path / "group" / "case" / "demo_goal.v").write_text("(* modified *)\n", encoding="utf-8")
    monkeypatch.setattr(verify_group_results, "run_coqc_check", lambda **_kwargs: pytest.fail("parent check should not run"))

    report = verify_group_results.verify_and_merge(manifest_path)

    merged = report["agent_result"]["vc_proving"]["group_merged_result"]
    assert merged["merge_vc_ready"] == "no"
    assert any("generated file modified" in error for error in merged["errors"])


def test_verify_group_results_rolls_back_round_files_on_final_compile_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest_path = _write_case_fixture(tmp_path)
    seed_manual = (tmp_path / "round" / "case" / "demo_proof_manual.v").read_text(encoding="utf-8")
    seed_lib = (tmp_path / "round" / "case" / "demo_lib.v").read_text(encoding="utf-8")
    failed = _passed_coqc_evidence(make_coqc_argv("case/demo_goal_check.v"), cwd=str(tmp_path / "builds" / "round" / "parent" / "src"))
    failed["status"] = "failed"
    failed["returncode"] = 1
    monkeypatch.setattr(verify_group_results, "run_coqc_check", lambda **_kwargs: failed)

    report = verify_group_results.verify_and_merge(manifest_path)

    assert report["agent_result"]["vc_proving"]["merge_vc_ready"] == "no"
    assert (tmp_path / "reports" / "rounds" / "round" / "group_merged_result.json").is_file()
    assert (tmp_path / "round" / "case" / "demo_proof_manual.v").read_text(encoding="utf-8") == seed_manual
    assert (tmp_path / "round" / "case" / "demo_lib.v").read_text(encoding="utf-8") == seed_lib


def test_coq_config_infers_round_check_file_from_round_workspace(tmp_path: Path) -> None:
    workspace = tmp_path / "repo"
    round_workspace = workspace / "worktrees" / "run" / "vc-proving-r1"
    case_dir = (
        round_workspace
        / "SeparationLogic"
        / "examples"
        / "LLM_bench"
        / "Algorithms"
        / "choosing_inns"
    )
    case_dir.mkdir(parents=True)

    config = infer_case_config(round_workspace, case_dir)

    assert config["active_theory"] == "SimpleC.EE.LLM_bench.Algorithms.choosing_inns"
    assert config["check_file"] == "SeparationLogic/examples/LLM_bench/Algorithms/choosing_inns/choosing_inns_goal_check.v"
