from __future__ import annotations

import ast
import json
import re
from pathlib import Path
from typing import Any

import pytest

import controller
import controller_attempts
import controller_final
import controller_round_checks
import symexec_tooling
from controller_state import _source_version, _write_timing_summary
from path_utils import target_files_for_c


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _repo(tmp_path: Path) -> tuple[Path, Path]:
    repo = tmp_path / "repo"
    case = repo / "QCP_examples" / "LLM_bench" / "Algorithms" / "demo"
    formal = repo / "SeparationLogic" / "examples" / "LLM_bench" / "Algorithms" / "demo"
    case.mkdir(parents=True)
    formal.mkdir(parents=True)
    target = case / "demo.c"
    target.write_text("int demo(void) { return 0; }\n", encoding="utf-8")
    (formal / "demo_lib.v").write_text("Require Import Coq.Init.Logic.\n", encoding="utf-8")
    (formal / "demo_goal.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (formal / "demo_proof_auto.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (formal / "demo_proof_manual.v").write_text("Lemma w1 : True.\nProof. Admitted.\n", encoding="utf-8")
    (formal / "demo_goal_check.v").write_text("From Coq Require Import Init.Logic.\n", encoding="utf-8")
    (formal / "demo_proof_diagnostics.v").write_text("", encoding="utf-8")
    (formal / "diagnostics_snapshot.json").write_text("{}\n", encoding="utf-8")
    return repo, target


def _state(repo: Path, run_id: str) -> dict[str, Any]:
    return json.loads((repo / "reports" / run_id / "controller_state.json").read_text(encoding="utf-8"))


def _timing_summary(repo: Path, run_id: str) -> dict[str, Any]:
    return json.loads((repo / "reports" / run_id / "timing_summary.json").read_text(encoding="utf-8"))


def _call(repo: Path, *args: str) -> int:
    if args and args[0] == "mark-attempt-returned":
        run_id = args[args.index("--run") + 1]
        attempt_id = args[args.index("--attempt") + 1]
        state = _state(repo, run_id)
        if ":" in attempt_id:
            round_id, group_id = attempt_id.split(":", 1)
            started = state["attempts"][round_id]["groups"][group_id].get("started_at")
        else:
            started = state["attempts"][attempt_id].get("started_at")
        if not started:
            assert controller.main(
                ["--main-root", str(repo), "mark-attempt-started", "--run", run_id, "--attempt", attempt_id]
            ) == 0
    return controller.main(["--main-root", str(repo), *args])


@pytest.mark.parametrize(
    ("runtime_platform", "relative_driver"),
    [
        (("nt", "win32", "AMD64"), Path("win-binary/symexec.exe")),
        (("posix", "linux", "x86_64"), Path("linux-binary/symexec")),
        (("posix", "darwin", "arm64"), Path("mac-arm64-binary/symexec")),
        (("posix", "darwin", "x86_64"), Path("mac-x86-64-binary/symexec")),
    ],
)
def test_symexec_driver_matches_runtime_platform(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    runtime_platform: tuple[str, str, str],
    relative_driver: Path,
) -> None:
    monkeypatch.setattr(symexec_tooling, "_runtime_platform", lambda: runtime_platform)
    assert symexec_tooling._driver_for_platform(tmp_path) == tmp_path / relative_driver


def test_symexec_driver_rejects_unsupported_platform(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(symexec_tooling, "_runtime_platform", lambda: ("posix", "freebsd14", "amd64"))
    with pytest.raises(ValueError, match="unsupported platform"):
        symexec_tooling._driver_for_platform(tmp_path)


def _init(repo: Path, target: Path, timestamp: str = "20260714130000") -> str:
    assert (
        _call(
            repo,
            "init-run",
            "--case",
            "demo",
            "--target-c-file",
            str(target),
            "--timestamp",
            timestamp,
        )
        == 0
    )
    return f"demo-{timestamp}"


def _complete_annotation_report(attempt: dict[str, Any]) -> None:
    report = {
        "schema_version": "qcp-agent-report/v3",
        "status": "completed",
        "blockers": [],
        "changed_files": [],
        "checks": {
            "symexec": "passed",
            "formal_case_lib": "passed",
            "annotation_checking": "passed",
        },
    }
    _write_json(Path(attempt["report"]), report)


def _complete_vc_checking_report(attempt: dict[str, Any], source_goal_version: str) -> None:
    report = {
        "schema_version": "qcp-agent-report/v3",
        "status": "completed",
        "source_goal_version": source_goal_version,
        "blockers": [],
    }
    _write_json(Path(attempt["report"]), report)


def _fill_annotation_summary(attempt: dict[str, Any]) -> None:
    path = Path(attempt["input"])
    text = path.read_text(encoding="utf-8")
    replacement = (
        "The evidence identifies a concrete annotation-design failure. Repair the named specification, contract, "
        "invariant, assertion, or call instantiation while preserving the stated functional behavior, then rerun "
        "all exact checks and avoid repeating the previous local assumption."
    )
    text = re.sub(r"<!-- MAIN_AGENT:.*?-->", replacement, text, flags=re.DOTALL)
    path.write_text(text, encoding="utf-8")


def _ready_annotation_summary(repo: Path, run_id: str, attempt: dict[str, Any]) -> dict[str, Any]:
    _fill_annotation_summary(attempt)
    assert (
        _call(
            repo,
            "annotation-summary-ready",
            "--run",
            run_id,
            "--attempt",
            attempt["attempt_id"],
        )
        == 0
    )
    return _state(repo, run_id)


def _write_current_group_plan(path: Path, state: dict[str, Any]) -> None:
    _write_json(
        path,
        {
            "schema_version": "qcp-vc-checking-group-plan/v3",
            "source_goal_version": state["source_goal_version"]["digest"],
            "groups": [{"id": "core", "witnesses": ["w1"], "depends_on": []}],
        },
    )


def _passed_symexec() -> dict[str, Any]:
    return {
        "schema_version": "qcp-canonical-symexec-result/v3",
        "status": "passed",
        "returncode": 0,
        "generated_files": [],
        "elapsed_seconds": 0.25,
    }


def _passed_coq(**kwargs: Any) -> dict[str, Any]:
    return {
        "status": "passed",
        "returncode": 0,
        "target_kind": kwargs.get("target_kind"),
        "source_goal_version": kwargs.get("source_goal_version"),
        "elapsed_seconds": 0.125,
    }


def test_init_run_creates_controller_state_and_fixed_layout(tmp_path: Path) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target)
    state = _state(repo, run_id)
    assert state["schema_version"] == "qcp-controller-run-state/v5"
    assert state["main_root"] == str(repo)
    assert state["run_root"] == str(repo / "verification_runs" / run_id)
    assert state["report_root"] == str(repo / "reports" / run_id)
    assert state["target_files"]["formal_case_lib"].endswith("demo_lib.v")
    assert (repo / "verification_runs" / run_id / "_coq_builds").is_dir()
    assert (repo / "verification_runs" / run_id / "annotation_history").is_dir()
    assert (repo / "reports" / run_id / "controller_state.json").is_file()
    assert not (repo / "reports" / run_id / "run_status.json").exists()
    records = [json.loads(line) for line in (repo / "reports" / run_id / "run_logs.json").read_text().splitlines()]
    assert all(record["event"] for record in records)
    assert all(record["schema_version"] == "qcp-controller-run-log/v3" for record in records)


def test_annotation_attempt_uses_root_and_history_not_snapshot_directory(
    tmp_path: Path,
) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130001")
    assert _call(repo, "step", "--run", run_id) == 0
    state = _state(repo, run_id)
    attempt = state["attempts"]["demo-annotation-r1-attempt-1"]
    payload = Path(attempt["input"]).read_text(encoding="utf-8")
    assert Path(attempt["report_directory"]) == repo / "reports" / run_id / "annotation-attempts" / "annotation-attempt1"
    assert state["annotation_session"]["current_attempt"] == attempt["attempt_id"]
    assert set(state["annotation_session"]) == {"session_id", "status", "current_attempt", "iteration_count"}
    assert state["next_actions"][0]["kind"] == "spawn-annotation-agent"
    assert Path(attempt["annotation_history_directory"]) == repo / "verification_runs" / run_id / "annotation_history" / attempt["attempt_id"]
    assert (Path(attempt["annotation_history_directory"]) / "before" / "QCP_examples/LLM_bench/Algorithms/demo/demo.c").is_file()
    assert "demo_lib.v" in payload
    assert "controller.py" in payload
    assert " symexec " in payload
    assert " coq-check " in payload
    assert ".agents/skills/verification-orchestrator/docs/path-configuration.md" in payload


def test_annotation_return_archives_direct_root_result(tmp_path: Path) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130002")
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    attempt = state["attempts"]["demo-annotation-r1-attempt-1"]
    target.write_text("/*@ Assert emp; */\nint demo(void) { return 0; }\n", encoding="utf-8")
    _complete_annotation_report(attempt)
    assert (
        _call(
            repo,
            "mark-attempt-returned",
            "--run",
            run_id,
            "--attempt",
            attempt["attempt_id"],
            "--result-status",
            "completed",
        )
        == 0
    )
    state = _state(repo, run_id)
    attempt = state["attempts"][attempt["attempt_id"]]
    assert attempt["status"] == "completed"
    assert attempt["changed_files"] == ["QCP_examples/LLM_bench/Algorithms/demo/demo.c"]
    archived = Path(attempt["annotation_history_directory"]) / "after" / "QCP_examples/LLM_bench/Algorithms/demo/demo.c"
    assert "Assert emp" in archived.read_text(encoding="utf-8")
    assert Path(attempt["input"]).parent == repo / "reports" / run_id / "annotation-attempts" / "annotation-attempt1"
    assert Path(attempt["report"]).is_file()
    assert Path(attempt["output"]).is_file()
    assert set(path.name for path in Path(attempt["annotation_history_directory"]).iterdir()) == {"before", "after"}


def test_spawn_instruction_and_review_are_controller_owned(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130003")
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    action = state["next_actions"][0]
    assert _call(repo, "spawn-instructions", "--run", run_id, "--next-action", action["id"]) == 0
    output = capsys.readouterr().out
    assert "only annotation agent" in output
    assert "Do not close or replace" in output
    assert "controller acceptance is separate" in output
    attempt = state["attempts"][action["attempt_id"]]
    _complete_annotation_report(attempt)
    assert (
        _call(
            repo,
            "mark-attempt-returned",
            "--run",
            run_id,
            "--attempt",
            attempt["attempt_id"],
            "--result-status",
            "completed",
        )
        == 0
    )
    assert _call(repo, "review-attempt", "--run", run_id, "--attempt", attempt["attempt_id"]) == 0
    state = _state(repo, run_id)
    assert state["attempts"][attempt["attempt_id"]]["status"] == "ready-for-main-check"
    report = json.loads(Path(attempt["report"]).read_text(encoding="utf-8"))
    assert report["status"] == "completed"
    assert "controller_review" not in report


def test_annotation_check_accepts_only_after_scripted_checks(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130004")
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    attempt = state["attempts"]["demo-annotation-r1-attempt-1"]
    _complete_annotation_report(attempt)
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        attempt["attempt_id"],
        "--result-status",
        "completed",
    )
    _call(repo, "review-attempt", "--run", run_id, "--attempt", attempt["attempt_id"])
    monkeypatch.setattr(controller_round_checks, "run_symexec", lambda **_kwargs: _passed_symexec())
    monkeypatch.setattr(controller_round_checks, "run_coqc_check", _passed_coq)
    assert (
        _call(
            repo,
            "annotation-check-round",
            "--run",
            run_id,
            "--round",
            "demo-annotation-r1",
        )
        == 0
    )
    state = _state(repo, run_id)
    assert state["accepted_rounds"]["annotation"]["annotation_history_directory"] == attempt["annotation_history_directory"]
    assert state["source_goal_version"]["target_witnesses"] == ["w1"]
    report = json.loads(Path(attempt["report"]).read_text(encoding="utf-8"))
    assert report["status"] == "completed"


def test_timing_summary_tracks_annotation_attempt_and_important_stages(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130040")
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    attempt = state["attempts"]["demo-annotation-r1-attempt-1"]
    assert _call(repo, "mark-attempt-started", "--run", run_id, "--attempt", attempt["attempt_id"]) == 0
    assert (
        _call(
            repo,
            "timing-stage",
            "--run",
            run_id,
            "--round",
            attempt["round"],
            "--stage",
            "annotation-checking",
            "--event",
            "start",
        )
        == 0
    )
    assert (
        _call(
            repo,
            "timing-stage",
            "--run",
            run_id,
            "--round",
            attempt["round"],
            "--stage",
            "annotation-checking",
            "--event",
            "finish",
        )
        == 0
    )
    _complete_annotation_report(attempt)
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        attempt["attempt_id"],
        "--result-status",
        "completed",
    )
    _call(repo, "review-attempt", "--run", run_id, "--attempt", attempt["attempt_id"])
    monkeypatch.setattr(controller_round_checks, "run_symexec", lambda **_kwargs: _passed_symexec())
    monkeypatch.setattr(controller_round_checks, "run_coqc_check", _passed_coq)
    assert _call(repo, "annotation-check-round", "--run", run_id, "--round", attempt["round"]) == 0

    timing = _timing_summary(repo, run_id)
    assert timing["schema_version"] == "qcp-timing-summary/v4"
    assert "commands" not in timing
    assert timing["rounds"] == []
    [summary] = timing["annotation_attempts"]
    assert summary["attempt"] == "annotation-attempt1"
    assert summary["round"] == attempt["round"]
    assert summary["status"] == "accepted"
    assert summary["elapsed_seconds"] >= 0
    stages = {stage["name"]: stage for stage in summary["stages"]}
    assert {
        "annotation-work",
        "symexec",
        "formal-case-lib-coq-check",
        "annotation-checking",
        "controller-review",
        "controller-acceptance-check",
    } <= set(stages)
    assert stages["symexec"]["elapsed_seconds"] == 0.25
    assert stages["formal-case-lib-coq-check"]["elapsed_seconds"] == 0.125


def test_timing_summary_uses_whole_vc_round_intervals_not_per_witness_or_group(tmp_path: Path) -> None:
    report_root = tmp_path / "reports" / "demo-run"
    state = {
        "report_root": str(report_root),
        "attempts": {
            "demo-vc-checking-r1-attempt-1": {
                "round": "demo-vc-checking-r1",
                "phase": "vc-checking",
                "status": "accepted",
                "created_at": "2026-07-14T00:00:00.000000Z",
                "started_at": "2026-07-14T00:00:01.000000Z",
                "returned_at": "2026-07-14T00:00:11.000000Z",
                "finished_at": "2026-07-14T00:00:12.000000Z",
                "timing": {
                    "controller-plan-check": [
                        {
                            "started_at": "2026-07-14T00:00:11.000000Z",
                            "finished_at": "2026-07-14T00:00:12.000000Z",
                            "elapsed_seconds": 1.0,
                        }
                    ]
                },
            },
            "demo-vc-proving-r1": {
                "round": "demo-vc-proving-r1",
                "phase": "vc-proving-preparing",
                "status": "verified",
                "created_at": "2026-07-14T00:01:00.000000Z",
                "finished_at": "2026-07-14T00:01:20.000000Z",
                "groups": {
                    "core": {
                        "started_at": "2026-07-14T00:01:02.000000Z",
                        "returned_at": "2026-07-14T00:01:12.000000Z",
                    },
                    "tail": {
                        "started_at": "2026-07-14T00:01:03.000000Z",
                        "returned_at": "2026-07-14T00:01:08.000000Z",
                    },
                },
                "timing": {
                    "preparing": [
                        {
                            "started_at": "2026-07-14T00:01:00.000000Z",
                            "finished_at": "2026-07-14T00:01:01.000000Z",
                            "elapsed_seconds": 1.0,
                        }
                    ],
                    "parent-verify": [
                        {
                            "started_at": "2026-07-14T00:01:12.000000Z",
                            "finished_at": "2026-07-14T00:01:20.000000Z",
                            "elapsed_seconds": 8.0,
                        }
                    ],
                },
            },
        },
    }
    _write_timing_summary(state)
    timing = json.loads((report_root / "timing_summary.json").read_text(encoding="utf-8"))
    vc_checking, vc_proving = timing["rounds"]
    assert vc_checking["round"] == "demo-vc-checking-r1"
    assert vc_checking["stages"][0] == {
        "name": "witness-analysis",
        "started_at": "2026-07-14T00:00:01.000000Z",
        "finished_at": "2026-07-14T00:00:11.000000Z",
        "elapsed_seconds": 10.0,
    }
    assert vc_proving["round"] == "demo-vc-proving-r1"
    group_work = vc_proving["stages"][0]
    assert group_work["name"] == "group-work"
    assert group_work["elapsed_seconds"] == 10.0
    assert "groups" not in vc_proving and "witnesses" not in vc_checking


def test_annotation_check_rejects_unsafe_formal_case_lib(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130011")
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    attempt = state["attempts"]["demo-annotation-r1-attempt-1"]
    _complete_annotation_report(attempt)
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        attempt["attempt_id"],
        "--result-status",
        "completed",
    )
    _call(repo, "review-attempt", "--run", run_id, "--attempt", attempt["attempt_id"])
    state = _state(repo, run_id)
    formal_case_lib = repo / state["target_files"]["formal_case_lib"]
    formal_case_lib.write_text(
        "Unset Guard Checking.\nFixpoint escape (n : nat) : False := escape n.\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(controller_round_checks, "run_symexec", lambda **_kwargs: _passed_symexec())
    monkeypatch.setattr(controller_round_checks, "run_coqc_check", _passed_coq)
    assert _call(repo, "annotation-check-round", "--run", run_id, "--round", "demo-annotation-r1") == 1
    state = _state(repo, run_id)
    assert "annotation" not in state["accepted_rounds"]
    assert state["attempts"][attempt["attempt_id"]]["main_check"]["formal_case_lib_contract"]["status"] == "failed"
    queued = state["next_actions"][0]
    assert queued["action"] == "retry-round"
    assert queued["previous_attempt"] == attempt["attempt_id"]
    assert queued["reason"] == "annotation-main-check-formal-case-lib-contract"
    _call(
        repo,
        "retry-round",
        "--run",
        run_id,
        "--phase",
        queued["phase"],
        "--reason",
        queued["reason"],
        "--previous-attempt",
        queued["previous_attempt"],
    )
    state = _state(repo, run_id)
    repair = state["attempts"]["demo-annotation-r2-attempt-1"]
    assert "Controller main-check failure" in Path(repair["input"]).read_text(encoding="utf-8")


def _bootstrap_vc_checking(repo: Path, target: Path, run_id: str, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    annotation = state["attempts"]["demo-annotation-r1-attempt-1"]
    _complete_annotation_report(annotation)
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        annotation["attempt_id"],
        "--result-status",
        "completed",
    )
    _call(repo, "review-attempt", "--run", run_id, "--attempt", annotation["attempt_id"])
    monkeypatch.setattr(controller_round_checks, "run_symexec", lambda **_kwargs: _passed_symexec())
    monkeypatch.setattr(controller_round_checks, "run_coqc_check", _passed_coq)
    _call(repo, "annotation-check-round", "--run", run_id, "--round", "demo-annotation-r1")
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    _complete_vc_checking_report(vc, state["source_goal_version"]["digest"])
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        vc["attempt_id"],
        "--result-status",
        "completed",
    )
    _call(repo, "review-attempt", "--run", run_id, "--attempt", vc["attempt_id"])
    return _state(repo, run_id)


def test_vc_checking_reads_root_and_writes_verified_group_plan(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130005")
    state = _bootstrap_vc_checking(repo, target, run_id, monkeypatch)
    attempt = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    payload = Path(attempt["input"]).read_text(encoding="utf-8")
    assert str(repo) in payload
    assert "All formal files are read-only" in payload
    assert "Do not use unstated parent-chat context" in payload
    plan = Path(attempt["report_directory"]) / "group_plan.json"
    _write_current_group_plan(plan, state)
    assert (
        _call(
            repo,
            "vc-checking-check-round",
            "--run",
            run_id,
            "--round",
            "demo-vc-checking-r1",
            "--group-plan",
            str(plan),
        )
        == 0
    )
    verified = json.loads(plan.read_text(encoding="utf-8"))
    assert verified["verified"] is True
    assert verified["source_goal_version"] == state["source_goal_version"]["digest"]
    assert verified["groups"][0]["witnesses"] == ["w1"]


def test_vc_checking_acceptance_rejects_drift_after_owner_review(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130051")
    state = _bootstrap_vc_checking(repo, target, run_id, monkeypatch)
    attempt = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    plan = Path(attempt["report_directory"]) / "group_plan.json"
    _write_current_group_plan(plan, state)
    goal = repo / state["target_files"]["goal_file"]
    goal.write_text(goal.read_text(encoding="utf-8") + "(* drift *)\n", encoding="utf-8")
    with pytest.raises(SystemExit, match="acceptance requires current annotation files"):
        _call(
            repo,
            "vc-checking-check-round",
            "--run",
            run_id,
            "--round",
            attempt["round"],
            "--group-plan",
            str(plan),
        )
    assert "verified" not in json.loads(plan.read_text(encoding="utf-8"))


def test_vc_proving_preparing_creates_fixed_group_layout(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130006")
    state = _bootstrap_vc_checking(repo, target, run_id, monkeypatch)
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    plan = Path(vc["report_directory"]) / "group_plan.json"
    _write_current_group_plan(plan, state)
    _call(
        repo,
        "vc-checking-check-round",
        "--run",
        run_id,
        "--round",
        vc["round"],
        "--group-plan",
        str(plan),
    )
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    proving = state["attempts"]["demo-vc-proving-r1"]
    assert _call(repo, "vc-proving-preparing", "--run", run_id, "--round", proving["round"]) == 0
    state = _state(repo, run_id)
    proving = state["attempts"][proving["attempt_id"]]
    assert Path(proving["base_manifest"]) == repo / "verification_runs" / run_id / proving["round"] / "base_manifest.json"
    manifest = json.loads(Path(proving["group_workers_manifest"]).read_text(encoding="utf-8"))
    assert len(proving["base_manifest_sha256"]) == 64
    assert len(proving["group_workers_manifest_sha256"]) == 64
    group = manifest["groups"][0]
    directory = Path(group["directory"])
    assert directory.parent == repo / "verification_runs" / run_id / proving["round"] / "groups"
    assert {path.name for path in directory.iterdir()} == {
        "demo_proof_manual.v",
        "demo_lib.v",
    }
    assert state["next_actions"][0]["kind"] == "spawn-group-worker"


def test_vc_proving_preparing_rejects_current_root_version_drift(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130007")
    state = _bootstrap_vc_checking(repo, target, run_id, monkeypatch)
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    plan = Path(vc["report_directory"]) / "group_plan.json"
    _write_current_group_plan(plan, state)
    _call(repo, "vc-checking-check-round", "--run", run_id, "--round", vc["round"], "--group-plan", str(plan))
    _call(repo, "step", "--run", run_id)
    formal = repo / state["target_files"]["goal_file"]
    formal.write_text(formal.read_text(encoding="utf-8") + "(* drift *)\n", encoding="utf-8")
    with pytest.raises(SystemExit, match="current accepted annotation files"):
        _call(repo, "vc-proving-preparing", "--run", run_id, "--round", "demo-vc-proving-r1")


def test_group_review_rejects_admitted_before_group_acceptance(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130009")
    state = _bootstrap_vc_checking(repo, target, run_id, monkeypatch)
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    plan = Path(vc["report_directory"]) / "group_plan.json"
    _write_current_group_plan(plan, state)
    _call(repo, "vc-checking-check-round", "--run", run_id, "--round", vc["round"], "--group-plan", str(plan))
    _call(repo, "step", "--run", run_id)
    _call(repo, "vc-proving-preparing", "--run", run_id, "--round", "demo-vc-proving-r1")
    state = _state(repo, run_id)
    proving = state["attempts"]["demo-vc-proving-r1"]
    manifest = json.loads(Path(proving["group_workers_manifest"]).read_text(encoding="utf-8"))
    group = manifest["groups"][0]
    _write_json(
        Path(group["report_directory"]) / "group_worker_report.json",
        {
            "schema_version": "qcp-group-worker-report/v2",
            "status": "completed",
            "source_goal_version": state["source_goal_version"]["digest"],
            "blockers": [],
        },
    )
    identifier = "demo-vc-proving-r1:core"
    _call(repo, "mark-attempt-returned", "--run", run_id, "--attempt", identifier, "--result-status", "completed")
    monkeypatch.setattr(controller_attempts, "run_coqc_check", _passed_coq)
    assert _call(repo, "review-attempt", "--run", run_id, "--attempt", identifier) == 1
    state = _state(repo, run_id)
    assert state["attempts"]["demo-vc-proving-r1"]["groups"]["core"]["status"] == "invalid-report"
    assert state["accepted_groups"]["demo-vc-proving-r1"] == []


def test_group_review_rejects_manifest_assignment_tampering(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130010")
    state = _bootstrap_vc_checking(repo, target, run_id, monkeypatch)
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    plan = Path(vc["report_directory"]) / "group_plan.json"
    _write_current_group_plan(plan, state)
    _call(repo, "vc-checking-check-round", "--run", run_id, "--round", vc["round"], "--group-plan", str(plan))
    _call(repo, "step", "--run", run_id)
    _call(repo, "vc-proving-preparing", "--run", run_id, "--round", "demo-vc-proving-r1")
    state = _state(repo, run_id)
    proving = state["attempts"]["demo-vc-proving-r1"]
    manifest_path = Path(proving["group_workers_manifest"])
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    group = manifest["groups"][0]
    Path(group["proof_manual"]).write_text("Lemma w1 : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    _write_json(
        Path(group["report_directory"]) / "group_worker_report.json",
        {
            "schema_version": "qcp-group-worker-report/v2",
            "status": "completed",
            "source_goal_version": state["source_goal_version"]["digest"],
            "blockers": [],
        },
    )
    manifest["groups"][0]["witnesses"] = ["w1", "forged_assignment"]
    _write_json(manifest_path, manifest)
    identifier = "demo-vc-proving-r1:core"
    _call(repo, "mark-attempt-returned", "--run", run_id, "--attempt", identifier, "--result-status", "completed")
    monkeypatch.setattr(controller_attempts, "run_coqc_check", _passed_coq)
    assert _call(repo, "review-attempt", "--run", run_id, "--attempt", identifier) == 1
    state = _state(repo, run_id)
    errors = state["attempts"]["demo-vc-proving-r1"]["groups"]["core"]["review_errors"]
    assert "group_workers_manifest changed after vc-proving preparation" in errors


def test_final_candidate_destinations_are_pinned_to_current_target() -> None:
    state = {
        "target_files": {
            "proof_manual_file": "SeparationLogic/examples/demo/demo_proof_manual.v",
            "formal_case_lib": "SeparationLogic/examples/demo/demo_lib.v",
        }
    }
    candidate = {
        "formal_proof_manual_relative": "SeparationLogic/examples/other/other_proof_manual.v",
        "formal_case_lib_relative": "SeparationLogic/examples/demo/demo_lib.v",
    }
    assert controller_final._candidate_target_errors(state, candidate) == [
        "final candidate manual destination does not match current target"
    ]


def test_final_freshness_splits_raw_diagnostics_before_comparing_manual(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, _target = _repo(tmp_path)
    report_root = repo / "reports" / "demo-run"
    target_files = {
        "c_file": "QCP_examples/LLM_bench/Algorithms/demo/demo.c",
        "goal_file": "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_goal.v",
        "proof_auto_file": "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_proof_auto.v",
        "proof_manual_file": "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_proof_manual.v",
        "goal_check_file": "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_goal_check.v",
        "proof_diagnostics_file": "SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_proof_diagnostics.v",
        "diagnostics_snapshot": "SeparationLogic/examples/LLM_bench/Algorithms/demo/diagnostics_snapshot.json",
    }
    state = {
        "main_root": str(repo),
        "report_root": str(report_root),
        "target_files": target_files,
    }

    def fake_symexec(**kwargs: Any) -> dict[str, Any]:
        output_root = Path(kwargs["output_root"])
        for key in ("goal_file", "proof_auto_file", "goal_check_file"):
            relative = Path(target_files[key])
            destination = output_root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text((repo / relative).read_text(encoding="utf-8"), encoding="utf-8")
        fresh_manual = output_root / target_files["proof_manual_file"]
        fresh_manual.parent.mkdir(parents=True, exist_ok=True)
        fresh_manual.write_text(
            "Lemma proof_of_w1_split_goal_1 : w1_split_goal_1.\n"
            "Proof. Abort.\n\n"
            "Lemma w1 : True.\n"
            "Proof. Admitted.\n",
            encoding="utf-8",
        )
        return _passed_symexec()

    monkeypatch.setattr(controller_final, "run_symexec", fake_symexec)
    evidence = controller_final._freshness_evidence(state)
    assert evidence["status"] == "passed"
    refresh = report_root / "final-check" / "symexec-refresh"
    cleaned_manual = (refresh / target_files["proof_manual_file"]).read_text(encoding="utf-8")
    diagnostics = (refresh / target_files["proof_diagnostics_file"]).read_text(encoding="utf-8")
    snapshot = json.loads((refresh / target_files["diagnostics_snapshot"]).read_text(encoding="utf-8"))
    assert "_split_goal_" not in cleaned_manual
    assert "_split_goal_" in diagnostics
    assert snapshot["manual_obligation_count"] == 1
    assert snapshot["diagnostic_count"] == 1


def test_final_cleanup_removes_old_side_products_and_reports_new_ones_compactly(
    tmp_path: Path,
) -> None:
    repo, target = _repo(tmp_path)
    run_root = repo / "verification_runs" / "demo-run"
    target_files = target_files_for_c(target.relative_to(repo))
    current_lib_vo = (repo / target_files["formal_case_lib"]).with_suffix(".vo")
    trusted_base_vo = repo / "SeparationLogic" / "base.vo"
    stale = [
        current_lib_vo,
        run_root / "outside-build.aux",
    ]
    for path in stale:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("derived\n", encoding="utf-8")
    allowed = run_root / "_coq_builds" / "final-check" / "src" / "allowed.vok"
    allowed.parent.mkdir(parents=True, exist_ok=True)
    allowed.write_text("derived\n", encoding="utf-8")
    trusted_base_vo.write_text("trusted full-make output\n", encoding="utf-8")

    cleanup = controller_final._remove_old_coq_side_products(repo, run_root, target_files)
    assert cleanup == {"removed_count": 2, "error_count": 0}
    assert all(not path.exists() for path in stale)
    assert allowed.is_file()
    assert trusted_base_vo.is_file()

    new_artifact = (repo / target_files["goal_file"]).with_suffix(".vos")
    new_artifact.write_text("derived\n", encoding="utf-8")
    evidence = controller_final._finish_cleanup_evidence(repo, run_root, target_files, cleanup)
    assert evidence == {
        "removed_count": 2,
        "error_count": 0,
        "remaining_count": 1,
        "first_remaining": target_files["goal_file"].removesuffix(".v") + ".vos",
        "status": "failed",
    }


def test_final_check_failure_rolls_back_and_requeues_final_apply(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130011")
    state = _state(repo, run_id)
    manual = repo / state["target_files"]["proof_manual_file"]
    formal_case_lib = repo / state["target_files"]["formal_case_lib"]
    original_manual = manual.read_text(encoding="utf-8")
    original_lib = formal_case_lib.read_text(encoding="utf-8")
    manual.write_text("Lemma w1 : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    formal_case_lib.write_text("Require Import Coq.Init.Logic.\n", encoding="utf-8")

    backup_root = repo / "reports" / run_id / "final-check" / "backup"
    backup_manual = backup_root / state["target_files"]["proof_manual_file"]
    backup_lib = backup_root / state["target_files"]["formal_case_lib"]
    backup_manual.parent.mkdir(parents=True, exist_ok=True)
    backup_lib.parent.mkdir(parents=True, exist_ok=True)
    backup_manual.write_text(original_manual, encoding="utf-8")
    backup_lib.write_text(original_lib, encoding="utf-8")
    state["phase"] = "final-check"
    state["source_goal_version"] = {"digest": "goal-version", "target_witnesses": ["w1"]}
    state["final_candidate"] = {
        "proof_manual_sha256": controller_final._file_digest(manual),
        "proving_merged_lib_sha256": controller_final._file_digest(formal_case_lib),
    }
    state["final_apply"] = {
        "status": "passed",
        "backup": [
            {"target": str(manual), "existed": True, "backup": str(backup_manual)},
            {"target": str(formal_case_lib), "existed": True, "backup": str(backup_lib)},
        ],
    }
    _write_json(repo / "reports" / run_id / "controller_state.json", state)

    monkeypatch.setattr(
        controller_final,
        "_freshness_evidence",
        lambda _state: {
            "status": "failed",
            "symexec": {"status": "passed", "returncode": 0},
            "mismatches": [{"kind": "goal_file"}],
            "refresh_root": str(repo / "reports" / run_id / "final-check" / "symexec-refresh"),
        },
    )
    monkeypatch.setattr(controller_final, "run_coqc_check", _passed_coq)
    monkeypatch.setattr(controller_final, "_accepted_annotation_source_findings", lambda _state: [])
    monkeypatch.setattr(
        controller_final,
        "_finish_cleanup_evidence",
        lambda _main_root, _run_root, _target_files, cleanup: {
            **cleanup,
            "remaining_count": 2,
            "first_remaining": "SeparationLogic/new.vos",
            "status": "failed",
        },
    )
    assert _call(repo, "final-check", "--run", run_id) == 1

    state = _state(repo, run_id)
    assert state["phase"] == "final-candidate-apply"
    assert state["final_apply"]["status"] == "rolled-back"
    assert state["next_actions"] == []
    assert manual.read_text(encoding="utf-8") == original_manual
    assert formal_case_lib.read_text(encoding="utf-8") == original_lib
    cleanup_blocker = next(
        item for item in state["final_check"]["blockers"] if item["failure_class"] == "cleanup"
    )
    assert cleanup_blocker == {
        "failure_class": "cleanup",
        "remaining_count": 2,
        "first_remaining": "SeparationLogic/new.vos",
    }
    assert "unexpected_artifacts" not in state["final_check"]["evidence"]["cleanup"]
    assert _call(repo, "step", "--run", run_id) == 0
    state = _state(repo, run_id)
    assert state["next_actions"] == [
        {"id": "final-candidate-apply", "kind": "main-owned-action", "action": "final-apply"}
    ]


def test_step_stops_when_final_apply_rollback_failed(tmp_path: Path) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130012")
    state = _state(repo, run_id)
    state["phase"] = "final-check"
    state["final_apply"] = {"status": "rollback-failed"}
    state["next_actions"] = [{"id": "final-check", "kind": "main-owned-action", "action": "final-check"}]
    _write_json(repo / "reports" / run_id / "controller_state.json", state)

    assert _call(repo, "step", "--run", run_id) == 0
    state = _state(repo, run_id)
    assert state["phase"] == "final-check"
    assert state["next_actions"] == []


def test_final_check_detects_target_c_changed_after_annotation(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    target = repo / "QCP_examples/demo.c"
    target.parent.mkdir(parents=True)
    target.write_text("int demo(void) { return 0; }\n", encoding="utf-8")
    source = _source_version([target], main_root=repo, roles={"QCP_examples/demo.c": "target-c-annotated"})
    state = {
        "main_root": str(repo),
        "target_files": {"c_file": "QCP_examples/demo.c"},
        "source_version": source,
        "accepted_rounds": {"annotation": {"source_version": source["digest"]}},
    }
    assert controller_final._accepted_annotation_source_findings(state) == []
    target.write_text("int demo(void) { return 1; }\n", encoding="utf-8")
    assert controller_final._accepted_annotation_source_findings(state) == [
        {"kind": "target-c-changed-after-annotation", "relative_path": "QCP_examples/demo.c"}
    ]


def test_final_manual_structure_rejects_same_line_top_level_declarations(tmp_path: Path) -> None:
    manual = tmp_path / "demo_proof_manual.v"
    manual.write_text(
        "Lemma w1 : True. Proof. exact I. Qed. Axiom escape : False. Definition hidden := 0.\n",
        encoding="utf-8",
    )
    findings = controller_final._manual_structure_findings(manual, ["w1"])
    assert any(item["kind"] == "assumption-declaration" and item["declaration"] == "Axiom" for item in findings)
    assert any(item["kind"] == "forbidden-top-level" and item["declaration"] == "Definition" for item in findings)

    manual.write_text(
        "Lemma w1 : True. Proof. exact I. Qed. Parameter escape : False. "
        "Lemma hidden : True. Proof. exact I. Qed.\n",
        encoding="utf-8",
    )
    findings = controller_final._manual_structure_findings(manual, ["w1"])
    assert any(item["kind"] == "assumption-declaration" and item["declaration"] == "Parameter" for item in findings)
    assert any(item["kind"] == "extra-top-level-command" and item["witness"] == "w1" for item in findings)
    assert any(item["kind"] == "top-level-witness-list-mismatch" for item in findings)

    manual.write_text(
        "From Coq Require Import Init.Logic. Lemma hidden : True. Proof. exact I. Qed.\n"
        "Lemma w1 : True. Proof. exact I. Qed.\n",
        encoding="utf-8",
    )
    findings = controller_final._manual_structure_findings(manual, ["w1"])
    assert any(
        item["kind"] == "top-level-witness-list-mismatch" and item["actual"] == ["hidden", "w1"]
        for item in findings
    )

    manual.write_text(
        "Hypothesis escape : False.\nLemma w1 : False. Proof. exact escape. Qed.\n",
        encoding="utf-8",
    )
    findings = controller_final._manual_structure_findings(manual, ["w1"])
    assert any(
        item["kind"] == "assumption-declaration" and item["declaration"] == "Hypothesis"
        for item in findings
    )

    manual.write_text(
        "Succeed Section Phantom.\nHypothesis escape : False.\n"
        "Lemma w1 : False. Proof. exact escape. Qed.\n",
        encoding="utf-8",
    )
    findings = controller_final._manual_structure_findings(manual, ["w1"])
    assert any(item["kind"] == "rollback-control" and item["declaration"] == "Succeed" for item in findings)
    assert any(
        item["kind"] == "assumption-declaration" and item["declaration"] == "Hypothesis"
        for item in findings
    )


def test_group_compact_error_reuses_fixed_group_with_bounded_retry(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130008")
    state = _bootstrap_vc_checking(repo, target, run_id, monkeypatch)
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    plan = Path(vc["report_directory"]) / "group_plan.json"
    _write_current_group_plan(plan, state)
    _call(
        repo,
        "vc-checking-check-round",
        "--run",
        run_id,
        "--round",
        vc["round"],
        "--group-plan",
        str(plan),
    )
    _call(repo, "step", "--run", run_id)
    _call(repo, "vc-proving-preparing", "--run", run_id, "--round", "demo-vc-proving-r1")
    state = _state(repo, run_id)
    action = state["next_actions"][0]
    worker_report = Path(action["report"])
    payload = json.loads(worker_report.read_text(encoding="utf-8"))
    payload["status"] = "compact-error"
    _write_json(worker_report, payload)
    identifier = "demo-vc-proving-r1:core"
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        identifier,
        "--result-status",
        "compact-error",
    )
    assert _call(repo, "review-attempt", "--run", run_id, "--attempt", identifier) == 0
    state = _state(repo, run_id)
    group_state = state["attempts"]["demo-vc-proving-r1"]["groups"]["core"]
    assert group_state["attempt_index"] == 2
    assert group_state["status"] == "prepared"
    assert state["next_actions"][0]["attempt_id"] == identifier
    worker_input = Path(state["next_actions"][0]["input"]).read_text(encoding="utf-8")
    assert "Attempt: 2" in worker_input
    assert "Earlier compact attempts: 1" in worker_input


def test_group_blocker_sources_can_be_appended_to_persistent_annotation_agent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130014")
    state = _bootstrap_vc_checking(repo, target, run_id, monkeypatch)
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    plan = Path(vc["report_directory"]) / "group_plan.json"
    _write_current_group_plan(plan, state)
    _call(repo, "vc-checking-check-round", "--run", run_id, "--round", vc["round"], "--group-plan", str(plan))
    _call(repo, "step", "--run", run_id)
    _call(repo, "vc-proving-preparing", "--run", run_id, "--round", "demo-vc-proving-r1")
    state = _state(repo, run_id)
    proving = state["attempts"]["demo-vc-proving-r1"]
    manifest = json.loads(Path(proving["group_workers_manifest"]).read_text(encoding="utf-8"))
    group = manifest["groups"][0]
    report_path = Path(group["report_directory"]) / "group_worker_report.json"
    output_path = Path(group["report_directory"]) / "group_worker_output.md"
    _write_json(
        report_path,
        {
            "schema_version": "qcp-group-worker-report/v2",
            "status": "blocked",
            "source_goal_version": state["source_goal_version"]["digest"],
            "blockers": [{"failure_class": "missing-annotation-premise", "witness": "w1"}],
        },
    )
    output_path.write_text("# Worker notes\n\nThe VC lacks ownership required by w1.\n", encoding="utf-8")
    identifier = "demo-vc-proving-r1:core"
    _call(repo, "mark-attempt-returned", "--run", run_id, "--attempt", identifier, "--result-status", "blocked")
    assert _call(repo, "review-attempt", "--run", run_id, "--attempt", identifier) == 0
    queued = _state(repo, run_id)["next_actions"][0]
    assert queued["action"] == "retry-round"
    assert queued["previous_attempt"] == identifier
    assert (
        _call(
            repo,
            "retry-round",
            "--run",
            run_id,
            "--phase",
            "annotation",
            "--reason",
            "missing-annotation-premise",
            "--previous-attempt",
            identifier,
        )
        == 0
    )
    state = _state(repo, run_id)
    summary_action = state["next_actions"][0]
    assert summary_action["kind"] == "main-owned-action"
    assert summary_action["action"] == "annotation-summary-ready"
    repair = state["attempts"][summary_action["attempt_id"]]
    assert Path(repair["report_directory"]) == repo / "reports" / run_id / "annotation-attempts" / "annotation-attempt2"
    assert str(output_path) in Path(repair["input"]).read_text(encoding="utf-8")
    state = _ready_annotation_summary(repo, run_id, repair)
    action = state["next_actions"][0]
    assert action["kind"] == "append-annotation-agent"
    assert action["feedback_sources"] == [
        {
            "phase": "group-worker",
            "attempt_id": identifier,
            "markdown": str(output_path),
            "json": str(report_path),
        }
    ]
    assert state["attempts"]["demo-vc-proving-r1"]["status"] == "stale"


def test_retry_annotation_requires_main_summary_before_persistent_session_append(
    tmp_path: Path,
) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130007")
    _call(repo, "step", "--run", run_id)
    previous = _state(repo, run_id)["attempts"]["demo-annotation-r1-attempt-1"]
    report = json.loads(Path(previous["report"]).read_text(encoding="utf-8"))
    report.update(
        {
            "status": "blocked",
            "blockers": [{"failure_class": "scripted-tool-unavailable"}],
        }
    )
    _write_json(Path(previous["report"]), report)
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        previous["attempt_id"],
        "--result-status",
        "blocked",
    )
    _call(repo, "review-attempt", "--run", run_id, "--attempt", previous["attempt_id"])
    previous = _state(repo, run_id)["attempts"][previous["attempt_id"]]
    sealed_output = Path(previous["output"]).read_text(encoding="utf-8")
    Path(previous["output"]).write_text(sealed_output + "\nlate mutation\n", encoding="utf-8")
    with pytest.raises(SystemExit, match="feedback artifacts are not immutable"):
        _call(
            repo,
            "retry-round",
            "--run",
            run_id,
            "--phase",
            "annotation",
            "--reason",
            "invalid-report",
            "--previous-attempt",
            previous["attempt_id"],
        )
    Path(previous["output"]).write_text(sealed_output, encoding="utf-8")
    assert (
        _call(
            repo,
            "retry-round",
            "--run",
            run_id,
            "--phase",
            "annotation",
            "--reason",
            "invalid-report",
            "--previous-attempt",
            previous["attempt_id"],
        )
        == 0
    )
    state = _state(repo, run_id)
    current = state["attempts"]["demo-annotation-r2-attempt-1"]
    payload = Path(current["input"]).read_text(encoding="utf-8")
    assert previous["output"] in payload
    assert previous["report"] in payload
    assert "## Main-agent blocker conclusion" in payload
    assert "## Reflection on the previous annotation attempt" in payload
    assert "<!-- MAIN_AGENT:" in payload
    assert Path(current["report_directory"]) == repo / "reports" / run_id / "annotation-attempts" / "annotation-attempt2"
    assert state["attempts"][previous["attempt_id"]]["status"] == "superseded"
    assert state["annotation_session"]["iteration_count"] == 2
    assert current["status"] == "awaiting-main-summary"
    assert state["next_actions"][0]["action"] == "annotation-summary-ready"
    assert (
        _call(
            repo,
            "annotation-summary-ready",
            "--run",
            run_id,
            "--attempt",
            current["attempt_id"],
        )
        == 1
    )
    state = _ready_annotation_summary(repo, run_id, current)
    assert state["next_actions"][0]["kind"] == "append-annotation-agent"
    assert state["next_actions"][0]["session_id"] == "demo-annotation-agent"
    assert state["next_actions"][0]["feedback_sources"] == [
        {
            "phase": "annotation",
            "attempt_id": previous["attempt_id"],
            "markdown": previous["output"],
            "json": previous["report"],
        }
    ]
    assert "completely reload both annotation skills" in payload
    sealed_input = Path(current["input"]).read_text(encoding="utf-8")
    Path(current["input"]).write_text(sealed_input + "\nchanged after sealing\n", encoding="utf-8")
    with pytest.raises(SystemExit, match="changed after controller validation"):
        _call(
            repo,
            "spawn-instructions",
            "--run",
            run_id,
            "--next-action",
            state["next_actions"][0]["id"],
        )
    Path(current["input"]).write_text(sealed_input, encoding="utf-8")


def test_vc_blocker_is_appended_to_same_annotation_agent_and_later_repair_broadens(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130013")
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    annotation = state["attempts"]["demo-annotation-r1-attempt-1"]
    session_id = state["annotation_session"]["session_id"]
    _complete_annotation_report(annotation)
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        annotation["attempt_id"],
        "--result-status",
        "completed",
    )
    _call(repo, "review-attempt", "--run", run_id, "--attempt", annotation["attempt_id"])
    monkeypatch.setattr(controller_round_checks, "run_symexec", lambda **_kwargs: _passed_symexec())
    monkeypatch.setattr(controller_round_checks, "run_coqc_check", _passed_coq)
    _call(repo, "annotation-check-round", "--run", run_id, "--round", annotation["round"])
    _call(repo, "step", "--run", run_id)

    state = _state(repo, run_id)
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    vc_report = {
        "schema_version": "qcp-agent-report/v3",
        "status": "blocked",
        "source_goal_version": state["source_goal_version"]["digest"],
        "blockers": [{"failure_class": "annotation-bug", "witness": "w1"}],
    }
    _write_json(Path(vc["report"]), vc_report)
    Path(vc["output"]).write_text("# VC analysis\n\nThe invariant loses the required pure fact.\n", encoding="utf-8")
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        vc["attempt_id"],
        "--result-status",
        "blocked",
    )
    _call(repo, "review-attempt", "--run", run_id, "--attempt", vc["attempt_id"])
    queued = _state(repo, run_id)["next_actions"][0]
    assert queued == {
        "id": f"annotation-feedback-{vc['attempt_id']}",
        "kind": "main-owned-action",
        "action": "retry-round",
        "phase": "annotation",
        "reason": "vc-checking-blocked",
        "previous_attempt": vc["attempt_id"],
    }
    assert (
        _call(
            repo,
            "retry-round",
            "--run",
            run_id,
            "--phase",
            "annotation",
            "--reason",
            "annotation-bug",
            "--previous-attempt",
            vc["attempt_id"],
        )
        == 0
    )
    state = _state(repo, run_id)
    summary_action = state["next_actions"][0]
    assert state["annotation_session"]["session_id"] == session_id
    assert summary_action["action"] == "annotation-summary-ready"
    second = state["attempts"][summary_action["attempt_id"]]
    state = _ready_annotation_summary(repo, run_id, second)
    action = state["next_actions"][0]
    assert action["kind"] == "append-annotation-agent"
    assert action["feedback_sources"] == [
        {
            "phase": "vc-checking",
            "attempt_id": vc["attempt_id"],
            "markdown": vc["output"],
            "json": vc["report"],
        }
    ]
    assert action["consider_broader_refactor"] is False
    capsys.readouterr()
    _call(repo, "spawn-instructions", "--run", run_id, "--next-action", action["id"])
    append_message = capsys.readouterr().out
    assert "existing annotation agent session" in append_message
    assert "do not spawn a new agent" in append_message
    assert "reload .agents/skills/annotation-filling/SKILL.md" in append_message
    assert vc["report"] in append_message and vc["output"] in append_message

    second = state["attempts"][action["attempt_id"]]
    second_report = json.loads(Path(second["report"]).read_text(encoding="utf-8"))
    second_report.update(
        {
            "status": "blocked",
            "blockers": [{"failure_class": "annotation-redesign-needed"}],
        }
    )
    _write_json(Path(second["report"]), second_report)
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        second["attempt_id"],
        "--result-status",
        "blocked",
    )
    _call(repo, "review-attempt", "--run", run_id, "--attempt", second["attempt_id"])
    _call(
        repo,
        "retry-round",
        "--run",
        run_id,
        "--phase",
        "annotation",
        "--reason",
        "annotation-redesign-needed",
        "--previous-attempt",
        second["attempt_id"],
    )
    state = _state(repo, run_id)
    third_summary_action = state["next_actions"][0]
    third = state["attempts"][third_summary_action["attempt_id"]]
    assert state["annotation_session"]["iteration_count"] == 3
    assert third_summary_action["action"] == "annotation-summary-ready"
    third_input = Path(third["input"]).read_text(encoding="utf-8")
    assert "third or later annotation iteration" in third_input
    state = _ready_annotation_summary(repo, run_id, third)
    third_action = state["next_actions"][0]
    assert third_action["kind"] == "append-annotation-agent"
    assert third_action["consider_broader_refactor"] is True


def test_source_version_digest_ignores_absolute_root(tmp_path: Path) -> None:
    relative = Path("QCP_examples/demo.c")
    root_a = tmp_path / "a"
    root_b = tmp_path / "b"
    for root in (root_a, root_b):
        (root / relative).parent.mkdir(parents=True)
        (root / relative).write_text("int demo;\n", encoding="utf-8")
    a = _source_version([root_a / relative], main_root=root_a, roles={relative.as_posix(): "target-c"})
    b = _source_version([root_b / relative], main_root=root_b, roles={relative.as_posix(): "target-c"})
    assert a["digest"] == b["digest"]
    assert a["files"] == b["files"]


def test_validate_new_manifest_and_controller_state_schemas() -> None:
    assert (
        controller.validate_artifact_payload(
            "manifest",
            {
                "schema_version": "qcp-vc-proving-base-manifest/v2",
            },
        )
        == []
    )
    assert (
        controller.validate_artifact_payload(
            "manifest",
            {
                "schema_version": "qcp-vc-proving-group-workers-manifest/v3",
                "groups": [],
            },
        )
        == []
    )
    assert (
        controller.validate_artifact_payload(
            "controller-state",
            {"schema_version": "qcp-controller-run-state/v5"},
        )
        == []
    )


def test_only_controller_module_exposes_a_cli() -> None:
    scripts = Path(controller.__file__).resolve().parent
    internal = [path for path in scripts.glob("*.py") if path.name != "controller.py"]
    internal.extend((scripts.parents[1] / "vc-proving" / "scripts").glob("*.py"))
    for path in internal:
        tree = ast.parse(path.read_text(encoding="utf-8"))
        assert not any(isinstance(node, ast.FunctionDef) and node.name == "main" for node in tree.body), path
    commands = controller.build_parser()._subparsers._group_actions[0].choices
    assert {
        "symexec",
        "coq-check",
        "coq-debug",
        "timing-stage",
        "annotation-summary-ready",
        "vc-proving-preparing",
        "vc-proving-verify",
        "final-check",
    } <= set(commands)


def test_vc_checking_cannot_skip_owner_review(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130009")
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    annotation = state["attempts"]["demo-annotation-r1-attempt-1"]
    _complete_annotation_report(annotation)
    _call(
        repo,
        "mark-attempt-returned",
        "--run",
        run_id,
        "--attempt",
        annotation["attempt_id"],
        "--result-status",
        "completed",
    )
    _call(repo, "review-attempt", "--run", run_id, "--attempt", annotation["attempt_id"])
    monkeypatch.setattr(controller_round_checks, "run_symexec", lambda **_kwargs: _passed_symexec())
    monkeypatch.setattr(controller_round_checks, "run_coqc_check", _passed_coq)
    _call(repo, "annotation-check-round", "--run", run_id, "--round", annotation["round"])
    _call(repo, "step", "--run", run_id)
    state = _state(repo, run_id)
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    plan = Path(vc["report_directory"]) / "group_plan.json"
    _write_current_group_plan(plan, state)
    with pytest.raises(SystemExit, match="not ready"):
        _call(repo, "vc-checking-check-round", "--run", run_id, "--round", vc["round"])
    assert "vc-checking" not in _state(repo, run_id)["accepted_rounds"]


def test_rejected_group_plan_is_not_marked_controller_verified(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130010")
    state = _bootstrap_vc_checking(repo, target, run_id, monkeypatch)
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    plan = Path(vc["report_directory"]) / "group_plan.json"
    _write_json(
        plan,
        {
            "schema_version": "qcp-vc-checking-group-plan/v3",
            "source_goal_version": state["source_goal_version"]["digest"],
            "groups": [{"id": "core", "witnesses": ["wrong"], "depends_on": []}],
        },
    )
    with pytest.raises(SystemExit, match="assign every target witness"):
        _call(repo, "vc-checking-check-round", "--run", run_id, "--round", vc["round"])
    rejected = json.loads(plan.read_text(encoding="utf-8"))
    assert "verified" not in rejected


def test_annotation_retry_invalidates_all_downstream_state(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130011")
    state = _bootstrap_vc_checking(repo, target, run_id, monkeypatch)
    annotation = state["attempts"]["demo-annotation-r1-attempt-1"]
    vc = state["attempts"]["demo-vc-checking-r1-attempt-1"]
    assert (
        _call(
            repo,
            "retry-round",
            "--run",
            run_id,
            "--phase",
            "annotation",
            "--reason",
            "annotation-bug",
            "--previous-attempt",
            annotation["attempt_id"],
        )
        == 0
    )
    state = _state(repo, run_id)
    assert state["source_goal_version"] is None
    assert state["accepted_rounds"] == {}
    assert state["accepted_groups"] == {}
    assert state["attempts"][vc["attempt_id"]]["status"] == "stale"
    assert state["final_candidate"] is None
    assert state["next_actions"][0]["attempt_id"] == "demo-annotation-r2-attempt-1"
    assert state["next_actions"][0]["kind"] == "main-owned-action"
    assert state["next_actions"][0]["action"] == "annotation-summary-ready"


def test_controller_tooling_commands_derive_paths_from_round_state(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    repo, target = _repo(tmp_path)
    run_id = _init(repo, target, "20260714130012")
    _call(repo, "step", "--run", run_id)
    calls: dict[str, dict[str, Any]] = {}

    def passed_symexec(**kwargs: Any) -> dict[str, Any]:
        calls["symexec"] = kwargs
        return _passed_symexec()

    def passed_coq(**kwargs: Any) -> dict[str, Any]:
        calls["coq"] = kwargs
        return _passed_coq(**kwargs)

    monkeypatch.setattr(controller, "run_symexec", passed_symexec)
    monkeypatch.setattr(controller, "run_coqc_check", passed_coq)
    assert _call(repo, "symexec", "--run", run_id, "--round", "demo-annotation-r1") == 0
    assert (
        _call(
            repo,
            "coq-check",
            "--run",
            run_id,
            "--round",
            "demo-annotation-r1",
            "--target-kind",
            "formal-case-lib",
        )
        == 0
    )
    assert calls["symexec"]["main_root"] == repo
    assert calls["symexec"]["target_c_file"] == Path("QCP_examples/LLM_bench/Algorithms/demo/demo.c")
    assert calls["symexec"]["output_root"] == repo
    assert calls["coq"]["workspace_root"] == repo
    assert calls["coq"]["target_file"] == Path("SeparationLogic/examples/LLM_bench/Algorithms/demo/demo_lib.v")
    assert str(calls["coq"]["build_workspace"]).startswith(str(repo / "verification_runs" / run_id / "_coq_builds"))
