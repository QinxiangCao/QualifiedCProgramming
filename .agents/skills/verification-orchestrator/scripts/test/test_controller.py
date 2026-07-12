from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any

import pytest

import controller


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _load_state(repo: Path, run_id: str) -> dict[str, Any]:
    return controller._load_state(repo / "worktrees" / run_id)


def _save_state(repo: Path, run_id: str, state: dict[str, Any]) -> None:
    controller._save_state(repo / "worktrees" / run_id, state)


def _run_log_records(repo: Path, run_id: str) -> list[dict[str, Any]]:
    path = repo / "reports" / run_id / "run_logs.json"
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def _timing_summary(repo: Path, run_id: str) -> dict[str, Any]:
    return json.loads((repo / "reports" / run_id / "timing_summary.json").read_text(encoding="utf-8"))


def _standard_output_note_text() -> str:
    return (
        "# Reuse Note\n\n"
        "Note kind: non-authoritative reuse note\n\n"
        "This file is not acceptance evidence. If it conflicts with JSON reports, handoff files, "
        "source versions, manifests, or current worktree files, ignore this file.\n\n"
        "## Result\n\nOwner status: completed\n"
    )


def _helper_namespace(group_id: str) -> dict[str, str]:
    sanitized = "".join(ch if ch.isalnum() or ch == "_" else "_" for ch in group_id).strip("_")
    return {
        "policy": "group-id-suffixed",
        "group_id": group_id,
        "suffix": "__" + sanitized,
        "required": "yes",
    }


def _controller_grouping_policy(count: int, max_per_group: int = 4) -> dict[str, Any]:
    return {
        "schema_version": "qcp-grouping-policy/v1",
        "controller_policy": "bounded-witness-groups/v1",
        "controller_enforced": "yes",
        "target_witness_count": count,
        "max_witnesses_per_group": max_per_group,
        "single_group_allowed_only_if_target_witness_count_lte": max_per_group,
        "oversized_group_rejected": "yes",
    }


def _natural_language_analysis(witnesses: list[str], group_id: str = "g1") -> dict[str, Any]:
    return {
        "witnesses": [
            {
                "witness_name": witness,
                "judgment": "proofable",
                "vc_shape": {
                    "pre_spatial": "True",
                    "pre_pure": "True",
                    "pre_exists": "none",
                    "post_spatial": "True",
                    "post_pure": "True",
                    "post_exists": "none",
                },
                "witness_instantiation": "none",
                "space_plan": "trivial frame",
                "pure_plan": "trivial proposition",
                "refinement_plan": "not applicable",
                "used_existing_lemmas": [],
                "candidate_helper_declarations": [],
                "premise_discharge": [],
                "recommended_next_phase": "vc-proving-preparing",
                "analysis_group_candidate": group_id,
                "grouping_reason": "same trivial proof pattern",
            }
            for witness in witnesses
        ],
        "analysis_groups": [
            {
                "group_id": group_id,
                "witness_names": witnesses,
                "representative_witness": witnesses[0],
                "shared_proof_pattern": "trivial",
                "shared_space_plan": "trivial frame",
                "shared_pure_plan": "trivial proposition",
                "shared_refinement_plan": "not applicable",
                "candidate_helper_declarations": [],
                "dependencies": [],
                "grouping_reason": "same trivial proof pattern",
                "proof_group_ready": True,
            }
        ],
    }


def _manifest_group_entry(
    *,
    state: dict[str, Any],
    vc_attempt: dict[str, Any],
    group_id: str,
    index: int,
    group_dir: Path,
    dependencies: list[str] | None = None,
) -> dict[str, Any]:
    run_root = Path(str(state["run_root"]))
    container = Path(str(vc_attempt["container_directory"]))
    group_worktree = container / f"group_{index:02d}__{group_id}"
    return {
        "group_id": group_id,
        "worktree_path": str(group_worktree),
        "dependencies": dependencies or [],
        "startup": {"owner": "main-agent", "script_launch_allowed": "no"},
        "tooling": {
            "coq_build_workspace": str(run_root / "_coq_builds" / str(vc_attempt["round"]) / f"group_{index:02d}__{group_id}" / "src"),
        },
        "handoff_files": {
            "input": str(group_dir / "group_worker_input.json"),
            "report": str(group_dir / "group_worker_report.json"),
        },
    }


def _manifest_base(state: dict[str, Any], vc_attempt: dict[str, Any]) -> dict[str, Any]:
    run_root = Path(str(state["run_root"]))
    return {
        "schema_version": "qcp-vc-proving-group-workers-manifest/v1",
        "run_root": str(run_root),
        "report_root": state["report_root"],
        "vc_proving_round_id": vc_attempt["round"],
        "vc_proving_container": vc_attempt["container_directory"],
        "round_worktree": vc_attempt["worktree"],
        "work_dir": vc_attempt["report_directory"],
        "round_report_directory": vc_attempt["report_directory"],
        "main_workspace_root": state["main_worktree"],
        "coq_builds_root": str(run_root / "_coq_builds"),
        "source_goal_version": state["source_goal_version"]["digest"],
    }


def _init_repo(tmp_path: Path) -> tuple[Path, Path]:
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init"], cwd=repo, check=True, stdout=subprocess.PIPE)
    subprocess.run(["git", "config", "user.email", "test@example.invalid"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=repo, check=True)
    target = repo / "QCP_examples" / "LLM_bench" / "Algorithms" / "demo" / "demo.c"
    formal = repo / "SeparationLogic" / "examples" / "LLM_bench" / "Algorithms" / "demo"
    target.parent.mkdir(parents=True)
    formal.mkdir(parents=True)
    target.write_text("int demo(void) { return 0; }\n", encoding="utf-8")
    (formal / "demo_lib.v").write_text("Require Import Coq.Init.Logic.\n", encoding="utf-8")
    (formal / "demo_goal.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (formal / "demo_proof_auto.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (formal / "demo_proof_manual.v").write_text("Lemma w1 : True.\nProof. Admitted.\n", encoding="utf-8")
    (formal / "demo_goal_check.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (formal / "demo_proof_diagnostics.v").write_text("", encoding="utf-8")
    (formal / "diagnostics_snapshot.json").write_text("{\"manual_obligation_count\":1}\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-m", "seed"], cwd=repo, check=True, stdout=subprocess.PIPE)
    return repo, target


def _bootstrap_to_vc_proving(repo: Path, target: Path, *, timestamp: str) -> str:
    run_id = f"demo-{timestamp}"
    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "init-run",
                "--case",
                "demo",
                "--target-c-file",
                str(target),
                "--timestamp",
                timestamp,
            ]
        )
        == 0
    )
    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    annotation_report = repo / "reports" / run_id / "rounds" / "demo-annotation-r1" / "agent_report.json"
    _write_json(
        annotation_report,
        {
            "schema_version": "qcp-agent-report/v1",
            "kind": "annotation",
            "status": "pending",
            "terminal": "no",
            "agent_result": {
                "annotation": {
                    "status": "completed",
                    "ready_for_annotation_check_round": True,
                    "self_reworkable_failures": [],
                    "self_repair_budget_exhausted": False,
                    "blockers": [],
                    "reference_policy_compliance": {"status": "passed"},
                    "file_access_summary": {"must_log_file_reads": "yes", "read_categories": [], "searches": []},
                }
            },
            "verification_result": {},
            "blockers": [],
        },
    )
    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "review-attempt",
            "--run",
            run_id,
            "--attempt",
            str(annotation_report.parent),
        ]
    ) == 0
    reviewed_report = json.loads(annotation_report.read_text(encoding="utf-8"))
    assert reviewed_report["verification_result"]["output_note_check"]["status"] == "warning"
    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "annotation-check-round",
            "--run",
            run_id,
            "--round",
            "demo-annotation-r1",
        ]
    ) == 0
    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    group_plan = repo / "reports" / run_id / "rounds" / "demo-vc-checking-r1" / "group_plan.json"
    _write_json(
        group_plan,
        {
            "proof_groups": [
                {"group_id": "g1", "witness_names": ["w1"], "dependencies": []},
            ]
        },
    )
    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "vc-checking-check-round",
            "--run",
            run_id,
            "--round",
            "demo-vc-checking-r1",
            "--group-plan",
            str(group_plan),
        ]
    ) == 0
    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    return run_id


def test_controller_step_is_idempotent_and_spawn_message_is_detailed(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "init-run",
                "--case",
                "demo",
                "--target-c-file",
                str(target),
                "--timestamp",
                "20260611120000",
            ]
        )
        == 0
    )
    run_id = "demo-20260611120000"

    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0

    state = _load_state(repo, run_id)
    assert len(state["attempts"]) == 1
    assert len(state["next_actions"]) == 1
    action_id = state["next_actions"][0]["id"]
    spawn = state["next_actions"][0]
    assert Path(spawn["input"]).is_file()
    assert Path(spawn["report"]).is_file()
    assert {path.name for path in Path(spawn["input"]).parent.iterdir()} == {
        "agent_input.json",
        "agent_report.json",
        "agent_output.txt",
    }

    # The printed instruction is still deterministic, but now carries strict workflow guardrails.
    controller.main(["--main-worktree-root", str(repo), "spawn-instructions", "--run", run_id, "--next-action", action_id])
    input_payload = json.loads(Path(spawn["input"]).read_text(encoding="utf-8"))
    spawn_message = input_payload["handoff"]["rendered_instructions_compact"]
    assert spawn_message.startswith("Read ")
    assert "The goal is to complete the workflow task assigned by the input JSON" in spawn_message
    assert "is only the final report file recording the result" in spawn_message
    assert "Before acting, read the input JSON completely" in spawn_message
    assert "No compromise operations" in spawn_message
    assert "Task completion means the assigned phase work is completed" in spawn_message
    assert "Controller acceptance is separate" in spawn_message
    assert "previous outputs are non-authoritative" in spawn_message
    assert "Minimize respawns" in spawn_message
    assert "Do not stop for confirmation" in spawn_message
    assert "Compact-error is not your blocked judgment" in spawn_message
    assert "write a blocked, stale, or compact-error result" in spawn_message
    assert input_payload["problem_context"]["source"] == "empty-user-input"
    assert input_payload["single_spawn_policy"]["preferred"] == "yes"
    assert input_payload["case_lib_seed_evidence"]["status"] == "existing"
    assert input_payload["annotation_contract"]["self_repair_budget"]["min_complete_cycles"] == 3
    assert "spec-quality" in input_payload["annotation_contract"]["self_reworkable_failure_classes"]
    assert input_payload["reference_policy"]["mode"] == "default"
    assert input_payload["previous_attempts"] == []
    assert input_payload["reports"] == {
        "input": spawn["input"],
        "report": spawn["report"],
        "output": str(Path(spawn["input"]).with_name("agent_output.txt")),
    }
    assert input_payload["attempt_control"]["heartbeat_policy"] == "no-timeout-retry"
    assert "heartbeat-timeout" not in input_payload["attempt_control"]["retry_reasons"]
    assert input_payload["output_contract"]["kind"] == "non-authoritative-reuse-note"
    assert input_payload["target_files"]["case_lib"] == "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_lib.v"
    assert input_payload["allowed_write_paths"][0] == "QCP_examples/LLM_bench/Algorithms/demo/demo.c"
    assert input_payload["qcp_driver"]["include_args"] == ["QCP_examples/QCP_demos_LLM/"]
    assert input_payload["coq_tooling"]["round_check_file"] == "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_goal_check.v"
    source_files = {entry["relative_path"]: entry for entry in input_payload["source_version"]["files"]}
    assert "QCP_examples/LLM_bench/Algorithms/demo/demo.c" in source_files
    assert "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_lib.v" in source_files
    assert source_files["SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_lib.v"]["state"] == "present"

    assert not (repo / "reports" / run_id / "run_status.json").exists()
    assert not (repo / "reports" / run_id / "run_events.json").exists()
    records = _run_log_records(repo, run_id)
    assert any(record["record_kind"] == "event" for record in records)
    assert any(record["record_kind"] == "state_snapshot" for record in records)
    assert all(record["schema_version"] == "qcp-controller-run-log/v1" for record in records)
    timing = _timing_summary(repo, run_id)
    timing_events = [node["event"] for node in timing["nodes"]]
    assert timing["schema_version"] == "qcp-timing-summary/v2"
    assert "run-start" in timing_events
    assert "phase-start" in timing_events
    assert "phase-end" in timing_events
    assert "controller-command-start" in timing_events
    assert "controller-command-end" in timing_events
    assert timing["phase_time"]["intake"]["count"] == 1
    assert timing["duration_summary"]["categories"]["controller_command"]["step"]["count"] == 2

    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "mark-attempt-started",
                "--run",
                run_id,
                "--attempt",
                "demo-annotation-r1-attempt-1",
            ]
        )
        == 0
    )
    state = _load_state(repo, run_id)
    assert state["attempts"]["demo-annotation-r1-attempt-1"]["status"] == "running"
    assert state["next_actions"] == []
    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "mark-attempt-returned",
                "--run",
                run_id,
                "--attempt",
                "demo-annotation-r1-attempt-1",
                "--result-status",
                "blocked",
            ]
        )
        == 0
    )
    state = _load_state(repo, run_id)
    assert state["attempts"]["demo-annotation-r1-attempt-1"]["status"] == "blocked"
    timing = _timing_summary(repo, run_id)
    attempt_nodes = [
        node
        for node in timing["nodes"]
        if node.get("timer_key") == "attempt:demo-annotation-r1-attempt-1"
    ]
    assert [node["event"] for node in attempt_nodes] == ["attempt-start", "attempt-end"]
    assert isinstance(attempt_nodes[-1]["duration_seconds"], float)
    assert attempt_nodes[-1]["duration_seconds"] >= 0
    assert timing["worker_time"]["demo-annotation-r1-attempt-1"]["count"] == 1


def test_init_run_records_problem_context(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120005",
            "--problem-statement",
            "Return the demo value.",
            "--target-function",
            "demo",
            "--expected-behavior",
            "returns zero",
            "--spec-hint",
            "postcondition should describe return value",
        ]
    ) == 0

    state = _load_state(repo, "demo-20260611120005")

    assert state["problem_context"]["source"] == "user-input"
    assert state["problem_context"]["problem_statement"] == "Return the demo value."
    assert state["problem_context"]["target_function"] == "demo"
    assert state["problem_context"]["spec_hint"] == ["postcondition should describe return value"]


def test_annotation_round_creates_minimal_case_lib_when_missing(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    case_lib = repo / "SeparationLogic" / "examples" / "LLM_bench" / "Algorithms" / "demo" / "demo_lib.v"
    subprocess.run(["git", "rm", str(case_lib.relative_to(repo))], cwd=repo, check=True, stdout=subprocess.PIPE)
    subprocess.run(["git", "commit", "-m", "remove lib"], cwd=repo, check=True, stdout=subprocess.PIPE)
    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120006",
        ]
    ) == 0
    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", "demo-20260611120006"]) == 0
    state = _load_state(repo, "demo-20260611120006")
    attempt = state["attempts"]["demo-annotation-r1-attempt-1"]
    input_payload = json.loads(Path(attempt["input"]).read_text(encoding="utf-8"))
    round_lib = Path(attempt["worktree"]) / input_payload["case_lib"]

    assert input_payload["case_lib_seed_evidence"]["status"] == "created"
    assert round_lib.is_file()
    assert "Require Import Coq.ZArith.ZArith." in round_lib.read_text(encoding="utf-8")


def test_source_version_digest_ignores_absolute_worktree_path(tmp_path: Path) -> None:
    rel = Path("QCP_examples/LLM_bench/Algorithms/demo/demo.c")
    root_a = tmp_path / "a"
    root_b = tmp_path / "b"
    (root_a / rel).parent.mkdir(parents=True)
    (root_b / rel).parent.mkdir(parents=True)
    (root_a / rel).write_text("int demo(void) { return 0; }\n", encoding="utf-8")
    (root_b / rel).write_text("int demo(void) { return 0; }\n", encoding="utf-8")

    version_a = controller._source_version(
        [root_a / rel],
        workspace_root=root_a,
        roles={rel.as_posix(): "target-c"},
    )
    version_b = controller._source_version(
        [root_b / rel],
        workspace_root=root_b,
        roles={rel.as_posix(): "target-c"},
    )

    assert version_a["digest"] == version_b["digest"]
    assert version_a["files"][0]["path"] != version_b["files"][0]["path"]
    assert version_a["files"][0]["relative_path"] == rel.as_posix()
    assert version_a["digest_input_policy"] == "relative_path+sha256+state+role only"


def test_legacy_run_status_can_still_load(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120010",
        ]
    )
    run_id = "demo-20260611120010"
    state = _load_state(repo, run_id)
    log_path = repo / "reports" / run_id / "run_logs.json"
    legacy_path = repo / "reports" / run_id / "run_status.json"
    legacy_path.write_text(json.dumps({**state, "phase": "legacy-loaded"}) + "\n", encoding="utf-8")
    log_path.unlink()

    loaded = _load_state(repo, run_id)

    assert loaded["phase"] == "legacy-loaded"


def test_output_note_check_is_warning_only(tmp_path: Path) -> None:
    report = tmp_path / "agent_report.json"
    input_path = tmp_path / "agent_input.json"
    output = tmp_path / "agent_output.txt"
    _write_json(input_path, {"round_worktree": str(tmp_path), "reports": {"output": str(output)}})
    _write_json(report, {"schema_version": "qcp-agent-report/v1", "agent_result": {}})

    missing = controller.check_output_note_payload(output_path=output, input_payload={}, report_path=report)
    output.write_text(_standard_output_note_text(), encoding="utf-8")
    passed = controller.check_output_note_payload(
        output_path=output,
        input_payload=json.loads(input_path.read_text(encoding="utf-8")),
        report_path=report,
    )

    assert missing["status"] == "warning"
    assert passed["status"] == "passed"


def test_retry_round_carries_previous_lessons_and_output_path(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = "demo-20260611120300"
    controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120300",
            "--reference-policy-mode",
            "deny-existing-examples",
        ]
    )
    controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id])
    r1_report = repo / "reports" / run_id / "rounds" / "demo-annotation-r1" / "agent_report.json"
    _write_json(
        r1_report,
        {
            "schema_version": "qcp-agent-report/v1",
            "kind": "annotation",
            "status": "pending",
            "terminal": "no",
            "agent_result": {
                "annotation": {
                    "status": "blocked",
                    "ready_for_annotation_check_round": False,
                    "self_reworkable_failures": [{"failure_class": "spec-quality"}],
                    "self_repair_budget_exhausted": True,
                    "blockers": [{"kind": "spec-quality", "message": "functional specs are missing"}],
                    "annotation_checking": {
                        "required_rework": ["add mathematical result semantics"],
                    },
                }
            },
            "verification_result": {},
            "blockers": [],
        },
    )

    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "retry-round",
                "--run",
                run_id,
                "--phase",
                "annotation",
                "--reason",
                "self-repair-budget-exhausted",
                "--previous-attempt",
                "demo-annotation-r1-attempt-1",
            ]
        )
        == 0
    )
    r2_input = repo / "reports" / run_id / "rounds" / "demo-annotation-r2" / "agent_input.json"
    payload = json.loads(r2_input.read_text(encoding="utf-8"))
    assert payload["reference_policy"]["mode"] == "deny-existing-examples"
    assert payload["previous_attempts"][0]["round"] == "demo-annotation-r1"
    assert payload["previous_attempts"][0]["report"] == str(r1_report)
    assert payload["previous_attempts"][0]["output"] == str(r1_report.with_name("agent_output.txt"))
    assert not any(key.startswith("report_") and key.endswith("sha256") for key in payload["previous_attempts"][0])
    lesson_text = " ".join(item["must_address"] for item in payload["required_lessons"])
    assert "functional specs are missing" in lesson_text
    assert "add mathematical result semantics" in lesson_text


def test_retry_round_from_vc_checking_uses_accepted_annotation_candidate(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = "demo-20260611120330"
    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "init-run",
                "--case",
                "demo",
                "--target-c-file",
                str(target),
                "--timestamp",
                "20260611120330",
                "--reference-policy-mode",
                "deny-existing-examples",
            ]
        )
        == 0
    )
    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    annotation_report = repo / "reports" / run_id / "rounds" / "demo-annotation-r1" / "agent_report.json"
    _write_json(
        annotation_report,
        {
            "schema_version": "qcp-agent-report/v1",
            "kind": "annotation",
            "status": "pending",
            "terminal": "no",
            "agent_result": {
                "annotation": {
                    "status": "completed",
                    "ready_for_annotation_check_round": True,
                    "self_reworkable_failures": [],
                    "self_repair_budget_exhausted": False,
                    "blockers": [],
                    "reference_policy_compliance": {"status": "passed"},
                    "file_access_summary": {"must_log_file_reads": "yes", "read_categories": [], "searches": []},
                }
            },
            "verification_result": {},
            "blockers": [],
        },
    )
    assert controller.main(["--main-worktree-root", str(repo), "review-attempt", "--run", run_id, "--attempt", str(annotation_report.parent)]) == 0
    assert controller.main(["--main-worktree-root", str(repo), "annotation-check-round", "--run", run_id, "--round", "demo-annotation-r1"]) == 0
    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    state = _load_state(repo, run_id)
    source_goal_digest = state["source_goal_version"]["digest"]
    accepted_source_digest = state["source_version"]["digest"]
    accepted_annotation_worktree = state["accepted_rounds"]["annotation"]["worktree"]

    vc_report = repo / "reports" / run_id / "rounds" / "demo-vc-checking-r1" / "agent_report.json"
    _write_json(
        vc_report,
        {
            "schema_version": "qcp-agent-report/v1",
            "kind": "vc-checking",
            "status": "pending",
            "terminal": "no",
            "agent_result": {
                "vc_checking": {
                    "status": "blocked",
                    "source_goal_version": source_goal_digest,
                    "blockers": [
                        {
                            "failure_class": "annotation-spec-insufficient",
                            "message": "false full-list permutation after overwrite",
                            "recommended_next_phase": "annotation",
                            "blocked_witnesses": [
                                {
                                    "witness_name": "proof_of_demo_wit_1",
                                    "target_symbol": "demo_wit_1",
                                    "reason": "postcondition preserves a full mutable list permutation",
                                    "counterexample": "src = [1;1;2], dest update produces [1;2;2]",
                                    "missing_or_wrong_fact": "track prefix values and leave suffix unconstrained",
                                    "recommended_next_phase": "annotation",
                                }
                            ],
                        }
                    ],
                    "errors": [],
                }
            },
            "verification_result": {},
            "blockers": [],
        },
    )
    assert controller.main(["--main-worktree-root", str(repo), "review-attempt", "--run", run_id, "--attempt", str(vc_report.parent)]) == 1
    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "retry-round",
                "--run",
                run_id,
                "--phase",
                "annotation",
                "--reason",
                "annotation-spec-insufficient",
                "--previous-attempt",
                "demo-vc-checking-r1-attempt-1",
            ]
        )
        == 0
    )

    r2_input = repo / "reports" / run_id / "rounds" / "demo-annotation-r2" / "agent_input.json"
    payload = json.loads(r2_input.read_text(encoding="utf-8"))
    assert payload["parent_worktree"] == accepted_annotation_worktree
    assert payload["source_version"]["digest"] == accepted_source_digest
    source_roles = {entry["relative_path"]: entry["role"] for entry in payload["source_version"]["files"]}
    assert source_roles["QCP_examples/LLM_bench/Algorithms/demo/demo.c"] == "target-c-annotated"
    case_lib = repo / "worktrees" / run_id / "demo-annotation-r2" / "SeparationLogic" / "examples" / "LLM_bench" / "Algorithms" / "demo" / "demo_lib.v"
    assert case_lib.is_file()
    lesson = payload["required_lessons"][0]
    assert lesson["witness_name"] == "proof_of_demo_wit_1"
    assert lesson["source_goal_version"] == source_goal_digest
    assert not any(key.startswith("report_") and key.endswith("sha256") for key in lesson)
    assert "counterexample" in lesson
    assert "prefix values" in lesson["must_address"]


def test_review_annotation_blocked_self_reworkable_is_terminal_after_spawn(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = "demo-20260611120400"
    controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120400",
        ]
    )
    controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id])
    report_dir = repo / "reports" / run_id / "rounds" / "demo-annotation-r1"
    _write_json(
        report_dir / "agent_report.json",
        {
            "schema_version": "qcp-agent-report/v1",
            "kind": "annotation",
            "status": "pending",
            "terminal": "no",
            "agent_result": {
                "annotation": {
                    "status": "blocked",
                    "ready_for_annotation_check_round": False,
                    "self_reworkable_failures": [{"failure_class": "qcp-symbolic-execution"}],
                    "self_repair_budget_exhausted": False,
                    "blockers": [{"kind": "qcp-symbolic-execution", "message": "call instantiation failed"}],
                }
            },
            "verification_result": {},
            "blockers": [],
        },
    )

    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "review-attempt",
                "--run",
                run_id,
                "--attempt",
                str(report_dir),
            ]
        )
        == 1
    )
    state = _load_state(repo, run_id)
    assert state["current_blockers"][0]["failure_class"] == "blocked"
    assert state["attempts"]["demo-annotation-r1-attempt-1"]["status"] == "blocked"


def test_review_vc_checking_compact_marker_overrides_agent_blocked_status() -> None:
    status, errors = controller._review_vc_checking(
        {
            "schema_version": "qcp-agent-report/v1",
            "agent_result": {
                "vc_checking": {
                    "status": "blocked",
                    "source_goal_version": "sgv-demo",
                    "blockers": [
                        {
                            "failure_class": "compact-error-with-no-progress",
                            "message": "context compacted before strict continuation could finish",
                        }
                    ],
                }
            },
        },
        expected_source_goal_version="sgv-demo",
    )

    assert status == "compact-error-with-no-progress"
    assert errors == ["compact error reported"]


def test_review_vc_checking_source_goal_mismatch_is_stale_not_blocked() -> None:
    status, errors = controller._review_vc_checking(
        {
            "schema_version": "qcp-agent-report/v1",
            "agent_result": {
                "vc_checking": {
                    "status": "blocked",
                    "source_goal_version": "old-sgv",
                    "blockers": [{"failure_class": "needs-helper"}],
                    "group_plan": {"proof_groups": [{"group_id": "g1", "witness_names": ["w1"]}]},
                }
            },
        },
        expected_source_goal_version="current-sgv",
    )

    assert status == "stale"
    assert errors == ["source_goal_version mismatch"]


def test_review_vc_checking_soft_blocker_with_group_plan_is_ready_for_main_check() -> None:
    status, errors = controller._review_vc_checking(
        {
            "schema_version": "qcp-agent-report/v1",
            "agent_result": {
                "vc_checking": {
                    "status": "blocked",
                    "source_goal_version": "sgv-demo",
                    "blockers": [{"failure_class": "needs-helper", "message": "helper not proved yet"}],
                    "group_plan": {"proof_groups": [{"group_id": "g1", "witness_names": ["w1"]}]},
                }
            },
        },
        expected_source_goal_version="sgv-demo",
    )

    assert status == "accepted-for-main-check"
    assert errors == []


def test_review_vc_checking_hard_blocker_stays_blocked_even_with_group_plan() -> None:
    status, errors = controller._review_vc_checking(
        {
            "schema_version": "qcp-agent-report/v1",
            "agent_result": {
                "vc_checking": {
                    "status": "blocked",
                    "source_goal_version": "sgv-demo",
                    "blockers": [{"failure_class": "annotation-bug", "message": "P does not imply Q"}],
                    "group_plan": {"proof_groups": [{"group_id": "g1", "witness_names": ["w1"]}]},
                }
            },
        },
        expected_source_goal_version="sgv-demo",
    )

    assert status == "blocked"
    assert "annotation-bug" in errors[0]


def test_materialize_inline_vc_checking_group_plan(tmp_path: Path) -> None:
    report_path = tmp_path / "round" / "agent_report.json"
    plan = {"proof_groups": [{"group_id": "g1", "witness_names": ["w1"]}]}
    report = {
        "schema_version": "qcp-agent-report/v1",
        "agent_result": {"vc_checking": {"status": "blocked", "group_plan": plan}},
        "verification_result": {},
    }
    _write_json(report_path, report)

    repair = controller._materialize_inline_vc_checking_group_plan(report, report_path)

    assert repair is not None
    assert json.loads((report_path.parent / "group_plan.json").read_text(encoding="utf-8")) == plan
    updated_report = json.loads(report_path.read_text(encoding="utf-8"))
    assert updated_report["verification_result"]["controller_simple_repairs"][0]["kind"] == "materialized-inline-group-plan"


def test_review_vc_proving_soft_blocker_with_manifest_is_ready_for_group_scheduling() -> None:
    status, errors = controller._review_vc_proving(
        {
            "schema_version": "qcp-agent-report/v1",
            "agent_result": {
                "vc_proving": {
                    "status": "blocked",
                    "source_goal_version": "sgv-demo",
                    "blockers": [{"failure_class": "worker-proof-risk"}],
                    "group_workers_manifest": "group_workers_manifest.json",
                }
            },
        },
        expected_source_goal_version="sgv-demo",
    )

    assert status == "accepted-for-main-check"
    assert errors == []


def test_review_vc_proving_source_goal_mismatch_is_stale_not_blocked() -> None:
    status, errors = controller._review_vc_proving(
        {
            "schema_version": "qcp-agent-report/v1",
            "agent_result": {
                "vc_proving": {
                    "status": "completed",
                    "source_goal_version": "old-sgv",
                    "blockers": [],
                    "group_workers_manifest": "group_workers_manifest.json",
                }
            },
        },
        expected_source_goal_version="current-sgv",
    )

    assert status == "stale"
    assert errors == ["source_goal_version mismatch"]


def test_review_group_source_goal_mismatch_is_stale_not_blocked() -> None:
    status, errors = controller._review_group(
        {
            "schema_version": "qcp-group-worker-report/v1",
            "group_id": "g1",
            "agent_result": {
                "vc_proving": {
                    "group": {
                        "group_id": "g1",
                        "status": "completed",
                        "source_goal_version": "old-sgv",
                        "helper_namespace": _helper_namespace("g1"),
                        "case_lib_added_declarations": [],
                        "verification_result": {
                            "coqc_check": {"status": "passed", "source_goal_version": "old-sgv"}
                        },
                    }
                }
            },
        },
        "current-sgv",
    )

    assert status == "stale"
    assert errors == ["source_goal_version mismatch"]


def test_review_attempt_compact_error_controller_marks_exhaustion_once(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = "demo-20260611120410"
    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120410",
            "--max-compact-attempts",
            "1",
        ]
    ) == 0
    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    report = repo / "reports" / run_id / "rounds" / "demo-annotation-r1" / "agent_report.json"
    _write_json(
        report,
        {
            "schema_version": "qcp-agent-report/v1",
            "kind": "annotation",
            "status": "pending",
            "terminal": "no",
            "agent_result": {
                "annotation": {
                    "status": "compact-error",
                    "compact_error": {
                        "message": "context compacted before strict continuation could finish",
                    },
                }
            },
            "verification_result": {},
            "blockers": [],
        },
    )

    assert controller.main(["--main-worktree-root", str(repo), "review-attempt", "--run", run_id, "--attempt", str(report.parent)]) == 1
    state = _load_state(repo, run_id)
    blocker = state["current_blockers"][0]
    assert blocker["failure_class"] == "compact-error-retry-exhausted"
    assert blocker["controller_judgment"] == "blocked"
    assert blocker["compact_attempt_count"] == 1
    assert state["attempts"]["demo-annotation-r1-attempt-1"]["status"] == "compact-error-retry-exhausted"

    assert controller.main(["--main-worktree-root", str(repo), "review-attempt", "--run", run_id, "--attempt", str(report.parent)]) == 1
    state = _load_state(repo, run_id)
    assert state["compact_counts"]["round:demo-annotation-r1"] == 1


def test_review_annotation_allows_reference_policy_denial_for_ready_candidate(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = "demo-20260611120430"
    controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120430",
            "--reference-policy-mode",
            "deny-existing-examples",
        ]
    )
    controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id])
    report_dir = repo / "reports" / run_id / "rounds" / "demo-annotation-r1"
    _write_json(
        report_dir / "agent_report.json",
        {
            "schema_version": "qcp-agent-report/v1",
            "kind": "annotation",
            "status": "pending",
            "terminal": "no",
            "agent_result": {
                "annotation": {
                    "status": "completed",
                    "ready_for_annotation_check_round": True,
                    "self_reworkable_failures": [],
                    "self_repair_budget_exhausted": False,
                    "blockers": [],
                    "reference_policy_compliance": {"status": "passed"},
                    "file_access_summary": {
                        "must_log_file_reads": "yes",
                        "read_categories": [
                            {
                                "category": "forbidden",
                                "paths": ["QCP_examples/QCP_demos_human/forbidden.c"],
                            }
                        ],
                        "searches": [],
                    },
                }
            },
            "verification_result": {},
            "blockers": [],
        },
    )

    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "review-attempt",
                "--run",
                run_id,
                "--attempt",
                str(report_dir),
            ]
        )
        == 0
    )
    state = _load_state(repo, run_id)
    assert state.get("current_blockers") == []
    assert state["attempts"]["demo-annotation-r1-attempt-1"]["status"] == "ready-for-main-check"


def test_reference_policy_allows_current_case_generated_context() -> None:
    policy = controller._default_reference_policy(
        "deny-existing-examples",
        "QCP_examples/LLM_bench/Algorithms/demo/demo.c",
    )
    current_generated = [
        "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_goal.v",
        "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_proof_auto.v",
        "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_proof_manual.v",
        "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_goal_check.v",
        "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_proof_diagnostics.v",
        "SeparationLogic/examples/LLM_bench/Algorithms/demo/diagnostics_snapshot.json",
    ]
    other_completed_case_lib = "SeparationLogic/examples/LLM_bench/Algorithms/other/other_lib.v"
    report = {
        "agent_result": {
            "annotation": {
                "status": "completed",
                "ready_for_annotation_check_round": True,
                "self_reworkable_failures": [],
                "self_repair_budget_exhausted": False,
                "blockers": [],
                "reference_policy_compliance": {"status": "passed"},
                "file_access_summary": {
                    "must_log_file_reads": "yes",
                    "read_categories": [
                        {"category": "current-generated", "paths": current_generated},
                        {"category": "other-case-lib", "paths": [other_completed_case_lib]},
                    ],
                    "searches": [],
                    "denied_globs_touched": current_generated,
                },
            }
        }
    }

    status, errors = controller._review_annotation(report, {"reference_policy": policy})

    assert status == "accepted-for-main-check"
    assert errors == []


def test_reference_policy_compliance_failed_does_not_block_ready_candidate() -> None:
    report = {
        "agent_result": {
            "annotation": {
                "status": "completed",
                "ready_for_annotation_check_round": True,
                "self_reworkable_failures": [],
                "self_repair_budget_exhausted": False,
                "blockers": [],
                "reference_policy_compliance": {"status": "failed", "reason": "discouraged reference read"},
                "file_access_summary": {
                    "must_log_file_reads": "yes",
                    "read_categories": [
                        {"category": "discouraged", "paths": ["QCP_examples/QCP_demos_human/forbidden.c"]}
                    ],
                    "searches": [],
                    "denied_globs_touched": ["QCP_examples/QCP_demos_human/forbidden.c"],
                },
            }
        }
    }
    input_payload = {
        "reference_policy": {
            "must_log_file_reads": "yes",
            "denied_globs": ["QCP_examples/QCP_demos_human/**"],
        }
    }

    status, errors = controller._review_annotation(report, input_payload)

    assert status == "accepted-for-main-check"
    assert errors == []


@pytest.mark.parametrize("summary", [None, []])
def test_review_annotation_file_access_summary_schema_does_not_block_ready_candidate(summary: Any) -> None:
    annotation = {
        "status": "completed",
        "ready_for_annotation_check_round": True,
        "self_reworkable_failures": [],
        "self_repair_budget_exhausted": False,
        "blockers": [],
        "reference_policy_compliance": {"status": "passed"},
    }
    if summary is not None:
        annotation["file_access_summary"] = summary
    report = {"agent_result": {"annotation": annotation}}
    input_payload = {"reference_policy": {"must_log_file_reads": "yes", "denied_globs": []}}

    status, errors = controller._review_annotation(report, input_payload)

    assert status == "accepted-for-main-check"
    assert errors == []


def test_annotation_check_round_accepts_round_and_spawns_vc_checking(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = "demo-20260611120445"
    controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120445",
        ]
    )
    controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id])
    report_dir = repo / "reports" / run_id / "rounds" / "demo-annotation-r1"
    round_manual = (
        repo
        / "worktrees"
        / run_id
        / "demo-annotation-r1"
        / "SeparationLogic"
        / "examples"
        / "LLM_bench"
        / "Algorithms"
        / "demo"
        / "demo_proof_manual.v"
    )
    round_manual.write_text(
        "From Coq Require Import Init.Logic.\n"
        "Lemma proof_of_w1_split_goal_1 : w1_split_goal_1.\nProof. Abort.\n"
        "Lemma w1 : True.\nProof. Admitted.\n",
        encoding="utf-8",
    )
    _write_json(
        report_dir / "agent_report.json",
        {
            "schema_version": "qcp-agent-report/v1",
            "kind": "annotation",
            "status": "pending",
            "terminal": "no",
            "agent_result": {
                "annotation": {
                    "status": "completed",
                    "ready_for_annotation_check_round": True,
                    "self_reworkable_failures": [],
                    "self_repair_budget_exhausted": False,
                    "blockers": [],
                    "reference_policy_compliance": {"status": "passed"},
                    "file_access_summary": {"must_log_file_reads": "yes", "read_categories": [], "searches": []},
                }
            },
            "verification_result": {},
            "blockers": [],
        },
    )
    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "review-attempt",
            "--run",
            run_id,
            "--attempt",
            str(report_dir),
        ]
    ) == 0
    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "annotation-check-round",
            "--run",
            run_id,
            "--round",
            "demo-annotation-r1",
        ]
    ) == 0

    state = _load_state(repo, run_id)
    assert state["phase"] == "vc-checking"
    assert state["attempts"]["demo-annotation-r1-attempt-1"]["status"] == "accepted"
    assert state["accepted_rounds"]["annotation"]["round"] == "demo-annotation-r1"
    assert state["source_goal_version"]["target_witnesses"] == ["w1"]
    assert "_split_goal_" not in round_manual.read_text(encoding="utf-8")
    diagnostics = round_manual.with_name("demo_proof_diagnostics.v").read_text(encoding="utf-8")
    assert "proof_of_w1_split_goal_1" in diagnostics

    report = json.loads((report_dir / "agent_report.json").read_text(encoding="utf-8"))
    assert report["status"] == "accepted"
    assert report["verification_result"]["annotation_check_round"]["status"] == "passed"
    assert report["verification_result"]["annotation_check_round"]["diagnostics_split"]["diagnostic_count"] == 1

    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    state = _load_state(repo, run_id)
    vc_attempt = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    assert vc_attempt["status"] == "pending"
    vc_input = json.loads(Path(vc_attempt["input"]).read_text(encoding="utf-8"))
    assert vc_input["allowed_write_paths"] == []
    assert vc_input["parent_worktree"].endswith("/demo-annotation-r1")
    assert vc_input["spawn"]["fork_context"] is False
    assert vc_input["context_policy"]["main_agent_transcript_allowed"] == "no"


def test_vc_checking_check_round_creates_vc_proving_preparing_container(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = _bootstrap_to_vc_proving(repo, target, timestamp="20260611120500")
    state = _load_state(repo, run_id)
    assert state["phase"] == "vc-proving-preparing"
    assert state["accepted_rounds"]["vc-checking"]["round"] == "demo-vc-checking-r1"
    vc_attempt = state["attempts"]["demo-vc-proving-r1-attempt-1"]
    assert vc_attempt["controller_owned"] == "yes"
    assert "input" not in vc_attempt
    assert "report" not in vc_attempt
    assert Path(vc_attempt["container_directory"]).is_dir()
    assert not (Path(vc_attempt["container_directory"]) / ".git").exists()
    assert vc_attempt["parallelism"]["max_parallel_group_workers"] == 4
    assert not (Path(vc_attempt["report_directory"]) / "agent_input.json").exists()
    assert not (Path(vc_attempt["report_directory"]) / "agent_report.json").exists()
    assert state["next_actions"][0]["action"] == "vc-proving-preparing"


def test_vc_proving_step_schedules_dependency_ready_group_workers(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = _bootstrap_to_vc_proving(repo, target, timestamp="20260611120530")
    state = _load_state(repo, run_id)
    vc_attempt = state["attempts"]["demo-vc-proving-r1-attempt-1"]
    vc_attempt["status"] = "ready-for-groups"
    state["next_actions"] = []
    _save_state(repo, run_id, state)
    report_dir = Path(vc_attempt["report_directory"])
    groups_root = report_dir / "groups"
    g1_dir = groups_root / "group_00__g1"
    g2_dir = groups_root / "group_01__g2"
    for group_dir in (g1_dir, g2_dir):
        group_dir.mkdir(parents=True, exist_ok=True)
        _write_json(group_dir / "group_worker_input.json", {"schema_version": "qcp-group-worker-input/v1"})
    _write_json(
        g1_dir / "group_worker_report.json",
        {
            "schema_version": "qcp-group-worker-report/v1",
            "group_id": "g1",
            "agent_result": {"vc_proving": {"group": {"status": "pending"}}},
        },
    )
    _write_json(
        g2_dir / "group_worker_report.json",
        {
            "schema_version": "qcp-group-worker-report/v1",
            "group_id": "g2",
            "agent_result": {"vc_proving": {"group": {"status": "pending"}}},
        },
    )
    _write_json(
        report_dir / "group_workers_manifest.json",
        {
            **_manifest_base(state, vc_attempt),
            "groups": [
                _manifest_group_entry(state=state, vc_attempt=vc_attempt, group_id="g1", index=0, group_dir=g1_dir),
                _manifest_group_entry(
                    state=state,
                    vc_attempt=vc_attempt,
                    group_id="g2",
                    index=1,
                    group_dir=g2_dir,
                    dependencies=["g1"],
                ),
            ],
        },
    )

    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    state = _load_state(repo, run_id)
    group_actions = [item for item in state["next_actions"] if item["kind"] == "spawn-group-worker"]
    assert [item["group_id"] for item in group_actions] == ["g1"]

    _write_json(
        g1_dir / "group_worker_report.json",
        {
            "schema_version": "qcp-group-worker-report/v1",
            "group_id": "g1",
            "agent_result": {
                "vc_proving": {
                    "group": {
                        "group_id": "g1",
                        "status": "completed",
                        "helper_namespace": _helper_namespace("g1"),
                        "source_goal_version": state["source_goal_version"]["digest"],
                        "solved_witnesses": ["w1"],
                        "unsolved_witnesses": [],
                        "case_lib_added_declarations": [],
                        "blockers": [],
                        "errors": [],
                        "verification_result": {
                            "coqc_check": {
                                "status": "passed",
                                "source_goal_version": state["source_goal_version"]["digest"],
                            }
                        },
                    }
                }
            },
        },
    )
    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "review-attempt",
            "--run",
            run_id,
            "--attempt",
            str(g1_dir),
        ]
    ) == 0
    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    state = _load_state(repo, run_id)
    group_actions = [item for item in state["next_actions"] if item["kind"] == "spawn-group-worker"]
    assert [item["group_id"] for item in group_actions] == ["g2"]


def test_step_prunes_stale_group_actions_before_scheduling_current_manifest(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = _bootstrap_to_vc_proving(repo, target, timestamp="20260611120540")
    state = _load_state(repo, run_id)
    vc_attempt = state["attempts"]["demo-vc-proving-r1-attempt-1"]
    vc_attempt["status"] = "ready-for-groups"
    report_dir = Path(vc_attempt["report_directory"])
    g1_dir = report_dir / "groups" / "group_00__g1"
    g1_dir.mkdir(parents=True, exist_ok=True)
    _write_json(g1_dir / "group_worker_input.json", {"schema_version": "qcp-group-worker-input/v1"})
    _write_json(
        g1_dir / "group_worker_report.json",
        {
            "schema_version": "qcp-group-worker-report/v1",
            "group_id": "g1",
            "agent_result": {"vc_proving": {"group": {"status": "pending"}}},
        },
    )
    _write_json(
        report_dir / "group_workers_manifest.json",
        {
            **_manifest_base(state, vc_attempt),
            "groups": [
                _manifest_group_entry(state=state, vc_attempt=vc_attempt, group_id="g1", index=0, group_dir=g1_dir),
            ],
        },
    )
    state["next_actions"] = [
        {
            "id": "spawn-demo-vc-proving-r0-g_old",
            "kind": "spawn-group-worker",
            "phase": "vc-proving-preparing",
            "round": "demo-vc-proving-r0",
            "group_id": "g_old",
            "input": str(g1_dir / "group_worker_input.json"),
            "report": str(g1_dir / "group_worker_report.json"),
        }
    ]
    _save_state(repo, run_id, state)

    assert controller.main(["--main-worktree-root", str(repo), "step", "--run", run_id]) == 0
    state = _load_state(repo, run_id)
    group_actions = [item for item in state["next_actions"] if item["kind"] == "spawn-group-worker"]
    assert [item["group_id"] for item in group_actions] == ["g1"]
    assert state["stale_actions"][0]["removed"][0]["action"]["round"] == "demo-vc-proving-r0"


def test_review_group_report_rejects_report_not_in_current_manifest(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = _bootstrap_to_vc_proving(repo, target, timestamp="20260611120550")
    state = _load_state(repo, run_id)
    vc_attempt = state["attempts"]["demo-vc-proving-r1-attempt-1"]
    vc_attempt["status"] = "ready-for-groups"
    report_dir = Path(vc_attempt["report_directory"])
    current_dir = report_dir / "groups" / "group_00__g1"
    current_dir.mkdir(parents=True, exist_ok=True)
    _write_json(current_dir / "group_worker_input.json", {"schema_version": "qcp-group-worker-input/v1"})
    _write_json(current_dir / "group_worker_report.json", {"schema_version": "qcp-group-worker-report/v1"})
    _write_json(
        report_dir / "group_workers_manifest.json",
        {
            **_manifest_base(state, vc_attempt),
            "groups": [
                _manifest_group_entry(state=state, vc_attempt=vc_attempt, group_id="g1", index=0, group_dir=current_dir),
            ],
        },
    )
    _save_state(repo, run_id, state)
    stale_dir = repo / "reports" / run_id / "rounds" / "demo-vc-proving-r0" / "groups" / "group_00__g1"
    stale_dir.mkdir(parents=True, exist_ok=True)
    _write_json(stale_dir / "group_worker_input.json", {"schema_version": "qcp-group-worker-input/v1"})
    _write_json(
        stale_dir / "group_worker_report.json",
        {
            "schema_version": "qcp-group-worker-report/v1",
            "group_id": "g1",
            "agent_result": {
                "vc_proving": {
                    "group": {
                        "group_id": "g1",
                        "status": "completed",
                        "helper_namespace": _helper_namespace("g1"),
                        "source_goal_version": state["source_goal_version"]["digest"],
                        "case_lib_added_declarations": [],
                        "verification_result": {
                            "coqc_check": {
                                "status": "passed",
                                "source_goal_version": state["source_goal_version"]["digest"],
                            }
                        },
                    }
                }
            },
        },
    )

    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "review-attempt",
                "--run",
                run_id,
                "--attempt",
                str(stale_dir),
            ]
        )
        == 1
    )
    state = _load_state(repo, run_id)
    assert state["group_acceptance"] == {}
    assert state["current_blockers"][0]["failure_class"] == "stale"


def test_review_group_compact_error_is_controller_retry_status() -> None:
    status, errors = controller._review_group(
        {
            "schema_version": "qcp-group-worker-report/v1",
            "group_id": "g1",
            "agent_result": {
                "vc_proving": {
                    "group": {
                        "group_id": "g1",
                        "status": "compact-error",
                        "source_goal_version": "sgv-demo",
                        "compact_error": {
                            "message": "context compacted before strict continuation could finish",
                            "reuse_evidence_pointer": "group_worker_output.txt",
                        },
                    }
                }
            },
        },
        "sgv-demo",
    )

    assert status == "compact-error-with-no-progress"
    assert errors == ["compact error reported"]


def test_vc_proving_verify_sets_final_candidate_and_final_check_action(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = _bootstrap_to_vc_proving(repo, target, timestamp="20260611120600")
    result_path = repo / "reports" / run_id / "rounds" / "demo-vc-proving-r1" / "group_merged_result.json"
    _write_json(
        result_path,
        {
            "schema_version": "qcp-vc-proving-parent-verify-result/v1",
            "agent_result": {
                "vc_proving": {
                    "status": "completed",
                    "group_merged_result": {
                        "status": "completed",
                        "merge_vc_ready": "yes",
                        "solved_witnesses": ["w1"],
                        "verification_result": {"coqc_check": {"status": "passed"}},
                    },
                }
            },
            "group_merged_result": {
                "status": "completed",
                "merge_vc_ready": "yes",
                "solved_witnesses": ["w1"],
                "verification_result": {"coqc_check": {"status": "passed"}},
            },
        },
    )

    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "vc-proving-verify",
            "--run",
            run_id,
            "--round",
            "demo-vc-proving-r1",
        ]
    ) == 0
    state = _load_state(repo, run_id)
    assert state["phase"] == "final-check"
    assert state["accepted_rounds"]["vc-proving-preparing"]["round"] == "demo-vc-proving-r1"
    assert state["final_candidate"]["files"][0]["target"] == "QCP_examples/LLM_bench/Algorithms/demo/demo.c"
    assert state["next_actions"][0]["action"] == "final-candidate-apply"


def test_vc_proving_verify_invokes_parent_helper_when_merged_result_missing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, target = _init_repo(tmp_path)
    run_id = _bootstrap_to_vc_proving(repo, target, timestamp="20260611120630")
    state = _load_state(repo, run_id)
    vc_attempt = state["attempts"]["demo-vc-proving-r1-attempt-1"]
    result_path = Path(vc_attempt["group_merged_result"])
    report_dir = Path(vc_attempt["report_directory"])
    g1_dir = report_dir / "groups" / "group_00__g1"
    g1_dir.mkdir(parents=True, exist_ok=True)
    _write_json(g1_dir / "group_worker_input.json", {"schema_version": "qcp-group-worker-input/v1"})
    _write_json(g1_dir / "group_worker_report.json", {"schema_version": "qcp-group-worker-report/v1"})
    manifest_path = report_dir / "group_workers_manifest.json"
    state["group_acceptance"] = {
        "g1": {
            "status": "accepted",
            "round": vc_attempt["round"],
            "attempt_id": vc_attempt["attempt_id"],
            "source_goal_version_digest": state["source_goal_version"]["digest"],
            "manifest": str(manifest_path.resolve()),
            "report": str((g1_dir / "group_worker_report.json").resolve()),
            "report_directory": str(g1_dir.resolve()),
        }
    }
    _save_state(repo, run_id, state)
    _write_json(
        manifest_path,
        {
            **_manifest_base(state, vc_attempt),
            "groups": [
                _manifest_group_entry(state=state, vc_attempt=vc_attempt, group_id="g1", index=0, group_dir=g1_dir),
            ],
        },
    )

    def fake_run(argv: list[str], **_kwargs: Any) -> subprocess.CompletedProcess[str]:
        assert "verify_group_results.py" in argv[1]
        _write_json(
            result_path,
            {
                "schema_version": "qcp-vc-proving-parent-verify-result/v1",
                "kind": "qcp-vc-proving-parent-verify-result",
                "agent_result": {
                    "vc_proving": {
                        "status": "completed",
                        "group_merged_result": {
                            "status": "completed",
                            "merge_vc_ready": "yes",
                            "solved_witnesses": ["w1"],
                            "blockers": [],
                            "errors": [],
                            "verification_result": {"coqc_check": {"status": "passed"}},
                        },
                    }
                },
                "group_merged_result": {
                    "status": "completed",
                    "merge_vc_ready": "yes",
                    "solved_witnesses": ["w1"],
                    "blockers": [],
                    "errors": [],
                    "verification_result": {"coqc_check": {"status": "passed"}},
                },
            },
        )
        return subprocess.CompletedProcess(argv, 0, "merged", "")

    monkeypatch.setattr(controller.subprocess, "run", fake_run)

    assert controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "vc-proving-verify",
            "--run",
            run_id,
            "--round",
            "demo-vc-proving-r1",
        ]
    ) == 0
    state = _load_state(repo, run_id)
    assert state["attempts"]["demo-vc-proving-r1-attempt-1"]["verification_result"]["parent_verify_command"]["returncode"] == 0


def test_annotation_preflight_requires_canonical_qcp_and_passed_coq(tmp_path: Path) -> None:
    qcp = tmp_path / "qcp.json"
    coq = tmp_path / "coq.json"
    _write_json(
        qcp,
        {
            "driver": "linux-binary/symexec",
            "cwd": "/repo",
            "include_args": ["QCP_examples/QCP_demos_LLM/"],
            "slp_args": ["QCP_examples/QCP_demos_LLM/", "SimpleC.EE.QCP_demos_LLM"],
        },
    )
    _write_json(coq, {"status": "failed", "target_kind": "check"})

    assert controller.main(["annotation-preflight", "--qcp-evidence", str(qcp), "--coq-evidence", str(coq)]) == 0

    _write_json(coq, {"status": "failed", "target_kind": "case_lib"})
    assert controller.main(["annotation-preflight", "--qcp-evidence", str(qcp), "--coq-evidence", str(coq)]) == 1


def test_verify_round_marks_group_plan_controller_verified(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120100",
        ]
    )
    manual = tmp_path / "demo_proof_manual.v"
    manual.write_text("Lemma w1 : True.\nProof. Admitted.\nLemma w2 : True.\nProof. Admitted.\n", encoding="utf-8")
    plan = tmp_path / "group_plan.json"
    _write_json(
        plan,
        {
            "proof_groups": [
                {"group_id": "g1", "witness_names": ["w1"], "dependencies": []},
                {"group_id": "g2", "witness_names": ["w2"], "dependencies": ["g1"]},
            ]
        },
    )

    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "verify-round",
                "--run",
                "demo-20260611120100",
                "--round",
                "vc-checking-r1",
                "--manual-file",
                str(manual),
                "--group-plan",
                str(plan),
                "--source-goal-version",
                "goal-v1",
            ]
        )
        == 0
    )
    verified = json.loads(plan.read_text(encoding="utf-8"))
    assert verified["controller_verified"] is True
    assert verified["target_witnesses"] == ["w1", "w2"]
    assert verified["grouping_policy"]["controller_policy"] == "bounded-witness-groups/v1"
    assert verified["grouping_policy"]["max_witnesses_per_group"] == 4


def test_verify_round_rejects_oversized_single_group(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120130",
        ]
    )
    manual = tmp_path / "demo_proof_manual.v"
    manual.write_text(
        "\n".join(f"Lemma w{i} : True.\nProof. Admitted." for i in range(1, 6)) + "\n",
        encoding="utf-8",
    )
    plan = tmp_path / "group_plan.json"
    _write_json(
        plan,
        {
            "proof_groups": [
                {"group_id": "g_all", "witness_names": [f"w{i}" for i in range(1, 6)], "dependencies": []},
            ]
        },
    )

    with pytest.raises(SystemExit, match="max_witnesses_per_group"):
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "verify-round",
                "--run",
                "demo-20260611120130",
                "--round",
                "vc-checking-r1",
                "--manual-file",
                str(manual),
                "--group-plan",
                str(plan),
                "--source-goal-version",
                "goal-v1",
            ]
        )


def test_review_attempt_rejects_invalid_report(tmp_path: Path) -> None:
    repo, target = _init_repo(tmp_path)
    controller.main(
        [
            "--main-worktree-root",
            str(repo),
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            "20260611120200",
        ]
    )
    report_dir = repo / "reports" / "demo-20260611120200" / "rounds" / "bad"
    report_dir.mkdir(parents=True)
    (report_dir / "agent_report.json").write_text("{bad json", encoding="utf-8")

    assert (
        controller.main(
            [
                "--main-worktree-root",
                str(repo),
                "review-attempt",
                "--run",
                "demo-20260611120200",
                "--attempt",
                str(report_dir),
            ]
        )
        == 1
    )
    state = _load_state(repo, "demo-20260611120200")
    assert state["current_blockers"][0]["failure_class"] == "invalid-report"
