"""Run with uv run --frozen --python 3.12 python -m pytest .agents/scripts/tests."""

import argparse
import io
import json
import os
import shutil
import subprocess
import sys
import time
import ast
import tempfile
from contextlib import redirect_stdout, suppress
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(SCRIPTS / name) for name in ("verification-orchestrator", "vc-proving")]

import annotation_design
import annotation_refresh
import atomic_file
import controller
import controller_attempts
import controller_final
import controller_round_checks
import controller_rounds
import controller_state
import controller_tools
import controller_proving
import coq_tooling_dune
import coq_tooling_makefile
import coq_tooling_common
import witness_reuse
import spec_freeze
import symexec_tooling
from controller_artifacts import validate_artifact_payload
from group_plan_utils import group_entries_from_plan
from path_utils import target_files_for_c
from process_adapter import CONTROL_SIGNAL_ENV, ProcessCancelled, ProcessResult, run_bounded_process, tool_progress
from proof_manual_utils import manual_vc_index
from spec_freeze import extract_spec_surface


def _cli(root, *args):
    with redirect_stdout(io.StringIO()) as output:
        code = controller.main(["--main-root", str(root), *args])
    return code, json.loads(output.getvalue())


def _run_next_action(root, run, command):
    code, result = _cli(root, "step", "--run", run)
    assert code == 0, result
    action, = result["next_actions"]
    assert action["action"] == command
    invocation = action["invocation"]
    assert Path(invocation["cwd"]) == root.resolve()
    with redirect_stdout(io.StringIO()) as output:
        code = controller.main(invocation["argv"][2:])
    return code, json.loads(output.getvalue())


def _c_file(root):
    path = root / "QCP_examples/demo/case.c"
    path.parent.mkdir(parents=True)
    path.write_text(
        "int f(int x) /*@ Require x == 0 Ensure __return == 0 */ { return x; }\n",
        encoding="utf-8",
    )
    return path


@pytest.mark.parametrize("cancel", [False, True])
def test_tool_stop_preserves_output_and_progress(tmp_path, monkeypatch, cancel):
    signal = tmp_path / "control.json"
    signal.write_text('{"status": "active"}', encoding="utf-8")
    monkeypatch.setenv(CONTROL_SIGNAL_ENV, str(signal))
    progress = []

    def record(_elapsed, stdout, stderr):
        progress.append((stdout, stderr))
        if cancel and stdout and stderr:
            signal.write_text('{"status": "paused"}', encoding="utf-8")

    result = run_bounded_process(
        [sys.executable, "-X", "utf8", "-u", "-c",
         "import sys,time; print('输出'); print('diagnostic',file=sys.stderr); time.sleep(30)"],
        cwd=tmp_path, timeout_seconds=2, poll_interval_seconds=.05,
        timeout_message="TIMEOUT", detached_pipe_message="DETACHED",
        progress_callback=record, return_cancelled_result=True,
    )
    assert result.returncode == (130 if cancel else 124)
    assert result.cancelled is cancel
    assert result.stdout == "输出\n"
    assert "diagnostic\n" in result.stderr
    assert any(stdout == "输出\n" and stderr == "diagnostic\n" for stdout, stderr in progress)
    assert not result.cleanup_incomplete


def test_atomic_copy_closes_descriptor_when_source_open_fails(tmp_path, monkeypatch):
    descriptors = []
    mkstemp = atomic_file.tempfile.mkstemp

    def record_temporary(**kwargs):
        descriptor, name = mkstemp(**kwargs)
        descriptors.append(descriptor)
        return descriptor, name

    monkeypatch.setattr(atomic_file.tempfile, "mkstemp", record_temporary)
    destination = tmp_path / "destination"
    destination.write_bytes(b"keep original")
    with pytest.raises(FileNotFoundError):
        atomic_file.atomic_copy_file(tmp_path / "missing", destination)
    try:
        with pytest.raises(OSError):
            os.fstat(descriptors[0])
    finally:
        with suppress(OSError):
            os.close(descriptors[0])
    assert destination.read_bytes() == b"keep original"
    assert list(tmp_path.iterdir()) == [destination]
    source = tmp_path / "source"
    source.write_bytes(b"new payload")
    atomic_file.atomic_copy_file(source, destination)
    assert destination.read_bytes() == source.read_bytes()


@pytest.mark.parametrize("source, count", [
    ("// Don't change this loop\nwhile (x) { x--; }\n// It's required\n", 1),
    ('/* a " quote */ while (x) { x--; } /* another " quote */', 1),
    ('char *s = "while(x) /*"; /* for(;;) */ for (;;) {}', 1),
    ("do { while (x) {} } while (y);", 2),
])
def test_loop_count_ignores_comment_quotes(source, count):
    assert annotation_design._c_loop_count(source) == count


@pytest.mark.parametrize("bad", [[], {}, ["invalid"], {"value": "invalid"}])
def test_artifact_type_errors_return_diagnostics(bad):
    plan = {"version": 2, "status": "ready", "function_specs": [],
            "loop_invariants": [], "new_predicates": [], "vc_comparisons": []}
    witness = {"name": "vc", "proof_mode": bad, "strategy": "prove True"}
    helper = {"name": "helper__g", "visibility": bad, "strategy": "prove True"}
    group = {"id": "g", "estimated_difficulty": 1, "witnesses": [witness], "helpers": [helper]}
    comparison = {"source": {"attempt": "old", "name": "vc", "annotation_location": "f"},
                  "current": ["vc"], "old_gap": "premise", "change": "add premise", "result": bad}
    for kind, payload in [
        ("agent-report", {"status": bad}),
        ("group-worker-report", {"status": bad}),
        ("group-plan", {"groups": [group]}),
        ("merge-result", {"status": bad}),
        ("controller-state", {"formal_case_lib_policy": bad, "run_control": {"status": bad}}),
        ("annotation-plan", {**plan, "status": bad}),
        ("annotation-plan", {**plan, "vc_comparisons": [comparison]}),
    ]:
        assert validate_artifact_payload(kind, payload), (kind, payload)
    assert validate_artifact_payload("agent-report", {"status": "completed"}) == []
    assert validate_artifact_payload("annotation-plan", plan) == []


@pytest.mark.parametrize("same_group", [False, True])
def test_duplicate_vc_is_rejected_before_plan_acceptance(same_group):
    index = manual_vc_index("Lemma vc : True.\nProof. Abort.\n")
    witness = {"name": "vc", "proof_mode": "LLM_pre_process", "strategy": "prove True"}
    group = {"id": "g", "estimated_difficulty": 1, "witnesses": [witness]}
    assert len(group_entries_from_plan(index, {"groups": [group]})) == 1
    groups = ([{**group, "witnesses": [witness, witness]}] if same_group
              else [group, {**group, "id": "h"}])
    with pytest.raises(SystemExit, match="repeat"):
        group_entries_from_plan(index, {"groups": groups})


@pytest.mark.parametrize("invalid", ["freeze", "problem-file"])
def test_invalid_init_does_not_create_seed_or_run(tmp_path, invalid):
    c_file = _c_file(tmp_path)
    args = ["init-run", "--case", "case", "--target-c-file", str(c_file),
            "--formal-case-lib-policy", "create"]
    bad_args = (["--freeze-spec", "typo"] if invalid == "freeze"
                else ["--problem-statement-file", str(tmp_path / "missing")])
    with pytest.raises(SystemExit):
        _cli(tmp_path, *args, *bad_args)
    assert sorted(path.name for path in tmp_path.iterdir()) == ["QCP_examples"]
    code, result = _cli(tmp_path, *args, "--freeze-spec", "f")
    assert code == 0
    state = json.loads(Path(result["controller_state"]).read_text(encoding="utf-8"))
    assert state["spec_freeze"]["baseline"] == extract_spec_surface(
        c_file, tmp_path / state["target_files"]["formal_case_lib"])


def test_pause_rejects_blank_reason_and_valid_pause_resumes(tmp_path):
    _, result = _cli(tmp_path, "init-run", "--case", "case", "--target-c-file", str(_c_file(tmp_path)))
    run = result["run_id"]
    state_file = Path(result["controller_state"])
    before = state_file.read_bytes()
    with pytest.raises(SystemExit, match="reason"):
        _cli(tmp_path, "pause-run", "--run", run, "--reason", "   ")
    assert state_file.read_bytes() == before
    assert _cli(tmp_path, "pause-run", "--run", run, "--reason", "review")[0] == 0
    assert _cli(tmp_path, "resume-run", "--run", run)[0] == 0
    state = json.loads(state_file.read_text(encoding="utf-8"))
    assert state["run_control"]["status"] == "active"
    assert state["phase"] == "intake"


def test_non_object_annotation_report_stays_repairable(tmp_path):
    _, result = _cli(tmp_path, "init-run", "--case", "case", "--target-c-file", str(_c_file(tmp_path)))
    run = result["run_id"]
    _, step = _cli(tmp_path, "step", "--run", run)
    action = step["next_actions"][0]
    _cli(tmp_path, "claim-attempt", "--run", run, "--next-action", action["id"], "--owner", action["owner"])
    Path(action["report"]).write_text("[]", encoding="utf-8")
    code, delivery = _cli(tmp_path, "finalize-delivery", "--run", run,
                          "--attempt", action["attempt_id"], "--owner", action["owner"])
    assert code == 2
    assert delivery["status"] == "report-repair-required"
    state = json.loads(Path(result["controller_state"]).read_text(encoding="utf-8"))
    assert state["attempts"][action["attempt_id"]]["status"] == "running"


def test_expired_symexec_budget_returns_timeout_without_launch(tmp_path, monkeypatch):
    target = target_files_for_c("QCP_examples/demo/case.c", "case")
    plan = {"driver": sys.executable, "cwd": str(tmp_path), "output_root": str(tmp_path),
            "target_c_file": target["c_file"], "target_files": target, "argv": []}
    monkeypatch.setattr(symexec_tooling, "build_symexec_plan", lambda **kwargs: plan)

    def unexpected_launch(*args, **kwargs):
        pytest.fail("an expired budget must not launch a child")

    monkeypatch.setattr(symexec_tooling, "run_bounded_process", unexpected_launch)
    result = symexec_tooling._run_symexec_with_budget(
        main_root=tmp_path, target_c_file=Path(target["c_file"]), output_root=tmp_path,
        target_files=target, timeout_seconds=0,
    )
    assert result["returncode"] == 124
    assert result["first_failure"]["kind"] == "timeout"


def _accepted_annotation_state(root, *, frozen=False, lib_text=None):
    """Build accepted-state fixtures with real path and snapshot seals."""
    c_file = _c_file(root)
    if lib_text is not None:
        library = root / "Rocq/examples/demo/case_lib.v"
        library.parent.mkdir(parents=True)
        library.write_text(lib_text, encoding="utf-8")
    _, initialized = _cli(root, "init-run", "--case", "case", "--target-c-file", str(c_file),
                          *(["--freeze-spec", "f"] if frozen else []))
    run_root = Path(initialized["run_root"])
    _, step = _cli(root, "step", "--run", run_root.name)
    action = step["next_actions"][0]
    _cli(root, "claim-attempt", "--run", run_root.name, "--next-action", action["id"], "--owner", action["owner"])
    state = controller_state._load_state(run_root)
    attempt = state["attempts"][action["attempt_id"]]
    for key in controller_state.GENERATED_KEYS:
        (root / state["target_files"][key]).write_text(
            "Lemma vc : True.\nProof. Abort.\n" if key == "proof_manual_file" else "(* generated fixture *)\n",
            encoding="utf-8",
        )
    controller_state._archive_annotation_stage(state, attempt, "after")
    attempt["status"] = "accepted"
    state["accepted_rounds"]["annotation"] = {
        key: attempt[key] for key in ("round", "attempt_id", "annotation_history_directory")
    }
    state["annotation_session"]["status"] = "idle"
    state["next_actions"] = []
    state["waiting_for"] = []
    controller_state._save_state(run_root, state)
    return state, attempt


@pytest.mark.parametrize("before, after", [
    ("From Coq Require Import ZArith List.\nFrom Coq Require Import List.\n",
     "From Coq Require Import Bool List.\nFrom Coq Require Import List.\n"),
    ("Require Import List.\nOpen Scope Z_scope.\nRequire Import List.\nOpen Scope nat_scope.\n",
     "Require Import List.\nOpen Scope bool_scope.\nRequire Import List.\nOpen Scope nat_scope.\n"),
    ("From Coq Require Import\n ZArith List.\nFrom Coq Require Import\n Bool List.\n",
     "From Coq Require Import\n Lia List.\nFrom Coq Require Import\n Bool List.\n"),
])
def test_freeze_preserves_every_import_record(before, after):
    baseline = {"lib": spec_freeze.extract_lib(before)}
    assert spec_freeze.compare(baseline, {"lib": spec_freeze.extract_lib(after)}, None)
    formatted = before.replace("Require", "(* formatting *) Require  ").replace(".\n", " .\n\n")
    assert spec_freeze.compare(baseline, {"lib": spec_freeze.extract_lib(formatted)}, None) == []
    extended = before + "From Coq Require Import Arith.\n"
    assert spec_freeze.compare(baseline, {"lib": spec_freeze.extract_lib(extended)}, None) == []










@pytest.mark.parametrize("reason", [
    "vc-checking-stale", "vc-proving-preparing-stale", "vc-proving-parent-verify-stale",
    "group-worker-stale", "vc-checking-manual-refresh-failed", "vc-proving-parent-failed",
])
def test_downstream_controller_recovery_routes_to_annotation(tmp_path, reason):
    state, _ = _accepted_annotation_state(tmp_path)
    run_root = Path(state["run_root"])
    if reason.startswith("vc-checking"):
        source = controller_rounds._init_round_attempt(state, phase="vc-checking")
    else:
        source = controller_rounds._init_vc_proving_attempt(state)
    identifier = source["attempt_id"]
    if reason == "group-worker-stale":
        source["groups"]["g"] = {"status": "stale"}
        identifier += ":g"
    if reason.endswith("stale"):
        (tmp_path / state["target_files"]["goal_file"]).unlink()
        assert controller_attempts._transition_current_file_drift(
            state, source, action="fixture", feedback_attempt_id=identifier, retry_reason=reason)
    else:
        state["current_blockers"] = [{
            "failure_class": controller_attempts.CONTROLLER_ANNOTATION_RECOVERY_FAILURES[reason],
            "first_error": "fixture controller check failure",
        }]
        controller_attempts._queue_annotation_feedback(state, identifier, reason)
    controller_state._save_state(run_root, state)
    assert _cli(tmp_path, "retry-round", "--run", run_root.name, "--phase", "annotation",
                "--reason", reason, "--previous-attempt", identifier)[0] == 0
    recovered = controller_state._load_state(run_root)
    assert recovered["next_actions"][0]["kind"] == "append-annotation-agent"
    current = recovered["attempts"][recovered["annotation_session"]["current_attempt"]]
    assert current["failed_vcs"] == []
    assert recovered["attempts"][source["attempt_id"]]["status"] == "stale"


@pytest.mark.parametrize("backend", [coq_tooling_dune, coq_tooling_makefile])
def test_shared_rocq_helpers_preserve_paths_and_dependency_order(tmp_path, backend):
    target = Path("Rocq/examples/demo/case_goal.v")
    assert backend.relative_to_logical_module(target) == "SimpleC.EE.demo.case_goal"
    assert backend.logical_module_to_relative("SimpleC.EE.demo.case_goal") == target
    with pytest.raises(backend.CoqBuildPlanError):
        backend._repository_relative(Path("../outside.v"), tmp_path, label="target")
    graph = {"current_dependencies": [
        {"source": "goal.v", "requires": ["lib.v"]},
        {"source": "lib.v", "requires": []},
    ]}
    assert backend._topological_current_order(graph) == [Path("lib.v"), Path("goal.v")]
    graph["current_dependencies"][1]["requires"] = ["goal.v"]
    with pytest.raises(backend.CoqBuildPlanError):
        backend._topological_current_order(graph)


@pytest.mark.parametrize("report", [
    {}, {"status": []}, {"status": "completed", "extra": True},
    {"status": "blocked", "blocker": {"failure_class": []}},
    {"status": "completed"},
])
def test_public_and_delivery_report_contracts_agree(report):
    public_errors = validate_artifact_payload("agent-report", report)
    for context in ("annotation", "group"):
        assert bool(controller_attempts._minimal_owner_report_errors(report, context=context)) == bool(public_errors)


@pytest.mark.parametrize("backend", [coq_tooling_dune, coq_tooling_makefile])
def test_rocq_imports_keep_qualified_names_and_ignore_comments(backend):
    source = '''Require Import SimpleC.EE.demo.case_goal Coq.Lists.List.
From Coq Require Export ZArith.ZArith List.
Require (* formatting *) SimpleC.SL.Assertions.(* adjacent comment *)
(* Require Import Ignored.Module. *)
Definition message := "Require Import Also.Ignored.".
'''
    assert backend._dependency_modules(source, source_label=Path("case.v")) == [
        "SimpleC.EE.demo.case_goal", "Coq.Lists.List", "Coq.ZArith.ZArith",
        "Coq.List", "SimpleC.SL.Assertions",
    ]
    with pytest.raises(backend.CoqBuildPlanError):
        backend._dependency_modules('Load "other.v".', source_label=Path("case.v"))


@pytest.mark.parametrize("backend", [coq_tooling_dune, coq_tooling_makefile])
def test_auto_overlap_ignores_proof_words_in_comments_and_strings(tmp_path, backend):
    auto = Path("case_proof_auto.v")
    manual = Path("case_proof_manual.v")
    keep = "Lemma keep : True.\nProof. exact I. Qed.\n"
    (tmp_path / manual).write_text(
        "(*\n" + keep + "*)\nLemma vc : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    (tmp_path / auto).write_text(
        'Lemma vc : True.\nProof. (* Qed. *) idtac "Qed."; exact I. Qed.\n' + keep, encoding="utf-8")
    texts, changed = backend.stage_current_sources(
        workspace_root=tmp_path, build_workspace=tmp_path / "build",
        sources={relative: tmp_path / relative for relative in (auto, manual)})
    assert texts[auto] == keep
    assert (tmp_path / "build" / auto).read_text(encoding="utf-8") == keep


@pytest.mark.skipif(shutil.which("coqc") is None, reason="optional installed Rocq smoke")
@pytest.mark.parametrize("backend", [coq_tooling_dune, coq_tooling_makefile])
def test_staged_sources_and_group_wrapper_compile_with_rocq(tmp_path, backend):
    for _flag, physical, _logical in backend.FIXED_LOAD_PATH_MAPPINGS:
        (tmp_path / physical).mkdir(parents=True, exist_ok=True)
        (tmp_path / "_build/default" / physical).mkdir(parents=True, exist_ok=True)
    build = tmp_path / "verification_runs/case-20260101000000/_coq_builds/smoke/src"
    directory = Path("Rocq/examples/demo")
    (tmp_path / directory).mkdir(parents=True, exist_ok=True)
    auto = directory / "case_proof_auto.v"
    manual = directory / "case_proof_manual.v"
    (tmp_path / auto).write_text(
        "From Coq Require Import ZArith.ZArith.\nLemma vc : True.\nProof. (* Qed. *) exact I. Qed.\n"
        "Lemma retained : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    (tmp_path / manual).write_text(
        f"Require Import {(tmp_path / auto).with_suffix('')}.\nLemma vc : True.\nProof. exact I. Qed.\n",
        encoding="utf-8")
    backend.stage_current_sources(
        workspace_root=tmp_path, build_workspace=build,
        sources={relative: tmp_path / relative for relative in (auto, manual)})
    wrapper = directory / "group_check.v"
    backend._write_group_check_wrapper(build, wrapper, {
        "case_theory": "SimpleC.EE.demo", "require_modules": [auto.stem, manual.stem],
        "assigned_witnesses": ["vc", "retained"],
    })
    for relative in (auto, manual, wrapper):
        argv = backend.make_coqc_argv(
            relative, workspace_root=tmp_path, build_workspace=build, case_directory=directory)
        result = subprocess.run(argv, cwd=build, capture_output=True, text=True, timeout=30)
        assert result.returncode == 0, result.stdout + result.stderr
        assert (build / relative).with_suffix(".vo").is_file()


@pytest.mark.parametrize("backend", [coq_tooling_dune, coq_tooling_makefile])
def test_staging_normalizes_once_and_preserves_comments_strings_and_source(tmp_path, monkeypatch, backend):
    root = tmp_path / "中文 space (&)"
    directory = Path("Rocq/examples/demo")
    (root / directory).mkdir(parents=True)
    auto, manual = (directory / f"case_proof_{kind}.v" for kind in ("auto", "manual"))
    source = f"Require (* keep *) Import {(root / auto).with_suffix('')}.\r\n"
    comment = f"(* Require Import {(root / auto).with_suffix('')}. *)\n"
    message = f'Definition message := "Require Import {root / auto}.".\n'
    (root / auto).write_bytes(b"Lemma vc : True.\nProof. exact I. Qed.\n")
    (root / manual).write_bytes((source + comment + message + "Lemma vc : True.\nProof. Abort.\n").encode())
    original = (root / manual).read_bytes()
    (root / manual).chmod(0o444)
    build = root / "build"
    written = []
    real_write = coq_tooling_common.atomic_write_text

    def record_write(path, text, **kwargs):
        written.append(path)
        return real_write(path, text, **kwargs)

    monkeypatch.setattr(coq_tooling_common, "atomic_write_text", record_write)
    try:
        args = dict(workspace_root=root, build_workspace=build,
                    sources={relative: root / relative for relative in (auto, manual)})
        texts, changed = backend.stage_current_sources(**args)
        assert len(written) == len(changed) == 2
        assert texts[auto] == ""
        assert "Require (* keep *) Import SimpleC.EE.demo.case_proof_auto." in texts[manual]
        assert comment in texts[manual] and message in texts[manual]
        assert b"\r" not in (build / manual).read_bytes()
        written.clear()
        assert backend.stage_current_sources(**args) == (texts, [])
        assert written == []
        assert (root / manual).read_bytes() == original
        assert (build / manual).stat().st_mode & 0o200
        # Compare final bytes, even when length and timestamp are unchanged.
        destination = build / manual
        timestamp = destination.stat().st_mtime_ns
        destination.write_bytes(destination.read_bytes().replace(b"Abort", b"Admit"))
        os.utime(destination, ns=(timestamp, timestamp))
        assert backend.stage_current_sources(**args)[1] == [manual.as_posix()]
    finally:
        (root / manual).chmod(0o644)


def test_cleanup_prunes_builds_and_reports_scan_errors(tmp_path, monkeypatch):
    target = target_files_for_c("QCP_examples/demo/case.c", "case")
    run = tmp_path / "verification_runs/case-20260101000000"
    excluded = run / "_coq_builds/deep/tree"
    excluded.mkdir(parents=True)
    (excluded / "keep.vo").write_bytes(b"cache")
    group = run / "groups/g"
    group.mkdir(parents=True)
    stale = group / "case.vo"
    stale.write_bytes(b"old")
    visited = []
    real_scandir = os.scandir

    def scandir(path):
        visited.append(Path(path))
        return real_scandir(path)

    monkeypatch.setattr(os, "scandir", scandir)
    assert controller_final._coq_side_products(tmp_path, run, target) == [stale]
    assert not any(path.is_relative_to(run / "_coq_builds") for path in visited)

    def denied(path):
        if Path(path) == group:
            raise PermissionError("scan denied")
        return real_scandir(path)

    monkeypatch.setattr(os, "scandir", denied)
    result = controller_final._remove_old_coq_side_products(tmp_path, run, target)
    assert result["error_count"] == 1 and "scan denied" in result["first_error"]
    assert stale.read_bytes() == b"old"


def test_annotation_prose_is_diagnostic_but_comparison_identity_is_required():
    plan = {"version": 2, "status": "ready", "function_specs": [],
            "loop_invariants": [], "new_predicates": [], "vc_comparisons": []}
    source = "int f(int x) /*@ Require emp; Ensure emp; */ { while(x) x--; return x; }"
    assert annotation_design.annotation_plan_errors(plan, c_source=source) == []
    assert annotation_design.annotation_plan_diagnostics(plan, c_source=source)
    failed = [{"source_attempt": "old", "name": "vc", "parent": None,
               "annotation_location": "loop", "manual": "/sealed.v", "message": "missing premise"}]
    index = manual_vc_index("Lemma vc : True.\nProof. Abort.\n")
    assert annotation_design.annotation_plan_errors(plan, failed_vcs=failed, current_vcs=index)


def _backend_workspace(root, backend):
    for _flag, physical, _logical in backend.FIXED_LOAD_PATH_MAPPINGS:
        (root / physical).mkdir(parents=True, exist_ok=True)
    case = Path("Rocq/examples/demo")
    (root / case).mkdir(parents=True, exist_ok=True)
    texts = {
        Path("Rocq/sets/Base.v"): "Lemma base : True.\nProof. exact I. Qed.\n",
        case / "case_goal.v": "From SetsClass Require Import Base.\n",
        case / "case_proof_auto.v": "From SimpleC.EE.demo Require Import case_goal.\n",
        case / "case_proof_manual.v": "From SimpleC.EE.demo Require Import case_proof_auto.\nLemma vc : True.\nProof. exact I. Qed.\nLemma pending : True.\nProof. exact I. Qed.\n",
        case / "case_goal_check.v": "From SimpleC.EE.demo Require Import case_proof_manual.\nCheck vc.\nCheck pending.\n",
    }
    for relative, text in texts.items():
        (root / relative).write_text(text, encoding="utf-8")
    if backend is coq_tooling_dune:
        (root / "dune-project").write_text("(lang dune 3.16)\n(using coq 0.9)\n", encoding="utf-8")
        (root / "Rocq/sets/dune").write_text("(coq.theory (name SetsClass))\n", encoding="utf-8")
        (root / case / "dune").write_text("(coq.theory (name SimpleC.EE.demo) (theories SetsClass))\n", encoding="utf-8")
    else:
        (root / "Rocq/Makefile").write_text("# exact builds use the run Makefile\n", encoding="utf-8")
    return case / "case_goal_check.v"


@pytest.mark.parametrize("backend, programs", [
    (coq_tooling_dune, ("coqc", "dune")),
    (coq_tooling_makefile, ("coqc", "coqdep", "make")),
])
def test_actual_backend_checks_latest_sources_without_content_cache(tmp_path, monkeypatch, backend, programs):
    if any(shutil.which(program) is None for program in programs):
        pytest.skip("requires installed " + ", ".join(programs))
    target = _backend_workspace(tmp_path, backend)
    run = tmp_path / "verification_runs/case-20260101000000"
    run.mkdir(parents=True)
    snapshot_path = run / ("dune_dependency_snapshot.json" if backend is coq_tooling_dune else "makefile_dependency_snapshot.json")
    receipt = backend.prepare_dune_dependencies(
        workspace_root=tmp_path, target_file=target, current_case_anchor=target,
        snapshot_path=snapshot_path, timeout_seconds=60)
    assert receipt["status"] == "passed", receipt
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    for field in ("dependency_digest", "source_digest", "artifact_digest", "configuration_digest"):
        assert field not in snapshot and field not in receipt
    for field in ("dependency_metrics", "rebuilt_count", "current_source_count", "base_artifact_count", "current_cleanup"):
        receipt.pop(field, None)
    assert backend.dune_preparation_receipt_errors(workspace_root=tmp_path, receipt=receipt) == []
    if backend is coq_tooling_makefile:
        # Proof checks consume the snapshot, never execute the old run Makefile.
        (run / "Makefile").unlink()
    else:
        unrelated = tmp_path / "Rocq/examples/unrelated/dune"
        unrelated.parent.mkdir()
        unrelated.write_text("; unrelated configuration\n", encoding="utf-8")
    state_path = tmp_path / "reports" / run.name / "controller_state.json"
    state_path.parent.mkdir(parents=True)
    state_path.write_text(json.dumps({"dune_preparation": receipt}), encoding="utf-8")
    build = run / "_coq_builds/smoke/src"
    args = dict(workspace_root=tmp_path, build_workspace=build, target_file=target,
                target_kind="check", current_case_anchor=target, timeout_seconds=60)
    assert backend.run_coqc_check(**args)["status"] == "passed"
    written = []
    real_write = coq_tooling_common.atomic_write_text

    def record_write(path, text, **kwargs):
        written.append(path)
        return real_write(path, text, **kwargs)

    monkeypatch.setattr(coq_tooling_common, "atomic_write_text", record_write)
    warm = backend.run_coqc_check(**args)
    assert warm["status"] == "passed", warm
    assert set(warm["recompiled_target_files"]) == set(snapshot["current_sources"])
    assert written == []
    cache = run / "_coq_builds/current"
    cache.mkdir(parents=True, exist_ok=True)
    (cache / "obsolete.vo").write_bytes(b"corrupt former cache")
    final = backend.run_coqc_check(**args)
    assert final["status"] == "passed", final
    assert set(final["recompiled_target_files"]) == set(snapshot["current_sources"])
    manual_rel = target.with_name("case_proof_manual.v")
    partial = run / "partial.v"
    partial.write_text((tmp_path / manual_rel).read_text(encoding="utf-8").replace(
        "Lemma pending : True.\nProof. exact I. Qed.", "Lemma pending : True.\nProof. Abort."), encoding="utf-8")
    partial_args = {**args, "overlays": {manual_rel: partial}}
    group = backend.run_coqc_check(**{
        **partial_args, "target_file": Path(".coq_group_checks/g.v"), "target_kind": "group-check",
        "group_check": {"case_theory": "SimpleC.EE.demo",
                        "require_modules": ["case_goal", "case_proof_auto", "case_proof_manual"],
                        "assigned_witnesses": ["vc"]},
    })
    assert group["status"] == "passed", group
    assert target.as_posix() not in group["recompiled_target_files"]
    parent = backend.run_coqc_check(**partial_args)
    assert parent["status"] == "failed" and "pending" in str(parent)
    base = tmp_path / "Rocq/sets/Base.v"
    base.write_bytes(base.read_bytes().replace(b"True", b"False"))
    failure = backend.run_coqc_check(**args)
    assert failure["status"] == "failed" and "Base.v" in str(failure)


def test_new_run_contract_does_not_silently_migrate_old_state(tmp_path):
    _, initialized = _cli(tmp_path, "init-run", "--case", "case", "--target-c-file", str(_c_file(tmp_path)))
    path = Path(initialized["controller_state"])
    state = json.loads(path.read_text(encoding="utf-8"))
    state.pop("schema_version")
    path.write_text(json.dumps(state), encoding="utf-8")
    before = path.read_bytes()
    with pytest.raises(SystemExit, match="older controller"):
        _cli(tmp_path, "step", "--run", initialized["run_id"])
    assert path.read_bytes() == before


def test_vc_debug_copy_and_translated_report_need_no_regeneration(tmp_path, monkeypatch):
    state, _ = _accepted_annotation_state(tmp_path)
    run = Path(state["run_root"])
    attempt = controller_rounds._init_round_attempt(state, phase="vc-checking")
    controller_state._save_state(run, state)
    action = state["next_actions"][0]
    _cli(tmp_path, "claim-attempt", "--run", run.name, "--next-action", action["id"], "--owner", "vc-owner")
    paths = controller_state._validated_attempt_paths(state, attempt)
    manual = tmp_path / state["target_files"]["proof_manual_file"]
    raw = manual.read_bytes()
    assert paths["debug_manual"].read_bytes() == raw
    paths["debug_manual"].write_bytes(raw.replace(b"Proof.", b"Proof. Show."))
    seen = []

    def debug(**kwargs):
        seen.append(kwargs)
        authorized = str(kwargs["build_workspace"] / kwargs["debug_script"])
        return {"status": "passed", "debug_script_path": authorized, "load_argument": authorized,
                "resolved_script_path": authorized, "resolved_matches_authorized": True}

    args = argparse.Namespace(main_root=str(tmp_path), run=run.name, round=attempt["round"], group=None)
    with redirect_stdout(io.StringIO()):
        assert controller_tools.coq_debug(args, coq_debug_runner=debug) == 0
    assert seen[0]["overlays"] == {Path(state["target_files"]["proof_manual_file"]): paths["debug_manual"]}
    paths["group_plan"].write_text(json.dumps({"groups": [{"id": "g", "estimated_difficulty": 1,
        "witnesses": [{"name": "vc", "proof_mode": "LLM_pre_process", "strategy": "prove True"}]}]}), encoding="utf-8")
    paths["output"].write_text("结构检查通过；本组证明 True。", encoding="utf-8")
    paths["report"].write_text('{"status":"completed"}', encoding="utf-8")

    def unexpected_generation(**kwargs):
        pytest.fail("VC acceptance must not regenerate canonical outputs")

    monkeypatch.setattr(controller_round_checks, "run_symexec", unexpected_generation)
    assert _cli(tmp_path, "finalize-delivery", "--run", run.name,
                "--attempt", attempt["attempt_id"], "--owner", "vc-owner")[0] == 0
    assert _cli(tmp_path, "vc-checking-check-round", "--run", run.name, "--round", attempt["round"])[0] == 0
    loaded = controller_state._load_state(run)
    assert set(loaded["accepted_rounds"]["vc-checking"]) == {"round", "attempt_id", "group_plan"}
    assert manual.read_bytes() == raw
    manual.write_bytes(raw.replace(b"True", b"False"))
    assert controller_state._current_files_errors(loaded) == []


def _publication_fixture(root, *, manual=True):
    target = target_files_for_c("QCP_examples/demo/case.c", "case")
    output = root / "reports/generation"
    report = root / "reports/attempt"
    report.mkdir(parents=True)
    for role in symexec_tooling.GENERATED_FILE_KEYS:
        original = root / target[role]
        original.parent.mkdir(parents=True, exist_ok=True)
        original.write_bytes(b"(* original with CRLF *)\r\n")
        if role == "proof_manual_file" and not manual:
            continue
        generated = output / target[role]
        generated.parent.mkdir(parents=True, exist_ok=True)
        generated.write_text(
            "Lemma vc : True.\nProof. Abort.\n" if role == "proof_manual_file"
            else f"(* new output under {output} *)\n", encoding="utf-8")
    expected = annotation_refresh.generated_output_contents(root, target)
    return dict(main_root=root, target_files=target, output_root=output, report_directory=report, expected=expected)


@pytest.mark.parametrize("manual", [False, True])
def test_generated_publication_preserves_optional_absence_and_normalizes_paths(tmp_path, manual):
    args = _publication_fixture(tmp_path, manual=manual)
    assert annotation_refresh.publish_generated_output(**args)["status"] == "committed"
    for role, relative in args["target_files"].items():
        if role not in symexec_tooling.GENERATED_FILE_KEYS:
            continue
        target = tmp_path / relative
        if role == "proof_manual_file" and not manual:
            assert not target.exists()
        else:
            assert target.is_file() and str(args["output_root"]) not in target.read_text(encoding="utf-8")
    assert not annotation_refresh.transaction_root_for_attempt(args["report_directory"]).exists()


@pytest.mark.parametrize("failure", ["write", "crash", "external-conflict", "missing-backup", "record-injection"])
def test_generated_publication_recovers_or_preserves_conflict(tmp_path, monkeypatch, failure):
    args = _publication_fixture(tmp_path)
    target = args["target_files"]
    originals = {role: (tmp_path / target[role]).read_bytes() for role in symexec_tooling.GENERATED_FILE_KEYS}
    transaction = annotation_refresh.transaction_root_for_attempt(args["report_directory"])
    real_write = annotation_refresh.atomic_write_bytes
    count = 0

    class Crash(BaseException):
        pass

    def write(path, payload, **kwargs):
        nonlocal count
        if kwargs.get("suffix") == ".generated-publish":
            count += 1
            if count == 2:
                if failure == "write":
                    raise PermissionError("sharing violation fixture")
                raise Crash()
        return real_write(path, payload, **kwargs)

    monkeypatch.setattr(annotation_refresh, "atomic_write_bytes", write)
    with pytest.raises(annotation_refresh.AnnotationRefreshError if failure == "write" else Crash):
        annotation_refresh.publish_generated_output(**args)
    monkeypatch.setattr(annotation_refresh, "atomic_write_bytes", real_write)
    if failure == "write":
        assert not transaction.exists()
    else:
        assert transaction.is_dir()
        if failure == "external-conflict":
            (tmp_path / target["goal_file"]).write_bytes(b"external edit")
        elif failure == "missing-backup":
            (transaction / "goal_file.original").unlink()
        elif failure == "record-injection":
            path = transaction / "transaction.json"
            manifest = json.loads(path.read_text(encoding="utf-8"))
            manifest["files"]["goal_file"]["relative_path"] = "../sentinel"
            path.write_text(json.dumps(manifest), encoding="utf-8")
        recover_args = dict(main_root=tmp_path, target_files=target, transaction_root=transaction)
        if failure == "crash":
            assert annotation_refresh.recover_interrupted_refresh(**recover_args) == "rolled-back-interrupted"
        else:
            before = {role: (tmp_path / target[role]).read_bytes() for role in originals}
            with pytest.raises(annotation_refresh.AnnotationRefreshError):
                annotation_refresh.recover_interrupted_refresh(**recover_args)
            assert {role: (tmp_path / target[role]).read_bytes() for role in originals} == before
            assert transaction.exists()
            return
    assert {role: (tmp_path / target[role]).read_bytes() for role in originals} == originals


def _running_annotation(root):
    _, initialized = _cli(root, "init-run", "--case", "case", "--target-c-file", str(_c_file(root)))
    run = Path(initialized["run_root"])
    _, step = _cli(root, "step", "--run", run.name)
    action = step["next_actions"][0]
    _cli(root, "claim-attempt", "--run", run.name, "--next-action", action["id"], "--owner", action["owner"])
    state = controller_state._load_state(run)
    return state, state["attempts"][action["attempt_id"]]


@pytest.mark.parametrize("outcome", ["failed", "passed", "paused"])
def test_owner_generation_keeps_main_files_until_validated_publication(tmp_path, outcome):
    state, attempt = _running_annotation(tmp_path)
    target = state["target_files"]
    for role in symexec_tooling.GENERATED_FILE_KEYS:
        (tmp_path / target[role]).write_bytes(b"(* existing output *)\r\n")
    original = annotation_refresh.generated_output_contents(tmp_path, target)

    def generate(**kwargs):
        assert kwargs["output_root"] != tmp_path
        assert annotation_refresh.generated_output_contents(tmp_path, target) == original
        for role in symexec_tooling.GENERATED_FILE_KEYS:
            path = kwargs["output_root"] / target[role]
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("Lemma vc : True.\nProof. Abort.\n" if role == "proof_manual_file" else "(* generated *)\n", encoding="utf-8")
        if outcome == "paused":
            _cli(tmp_path, "pause-run", "--run", Path(state["run_root"]).name, "--reason", "pause during generation")
        return {"status": "failed" if outcome == "failed" else "passed", "returncode": 1 if outcome == "failed" else 0}

    args = argparse.Namespace(main_root=str(tmp_path), run=Path(state["run_root"]).name, round=attempt["round"])
    with redirect_stdout(io.StringIO()):
        code = controller_tools.symexec(args, symexec_runner=generate)
    assert code == (0 if outcome == "passed" else 1)
    if outcome != "passed":
        assert annotation_refresh.generated_output_contents(tmp_path, target) == original
    else:
        loaded = controller_state._load_state(Path(state["run_root"]))
        assert loaded["attempts"][attempt["attempt_id"]]["owner_symexec_invocations"][-1]["status"] == "passed"


def test_bundled_generator_can_publish_from_staging(tmp_path, monkeypatch):
    driver = symexec_tooling._driver_for_platform(SCRIPTS.parents[1])
    if not driver.is_file():
        pytest.skip("requires the platform's bundled symexec executable")
    monkeypatch.setattr(symexec_tooling, "_driver_for_platform", lambda _root: driver)
    state, attempt = _running_annotation(tmp_path)
    args = argparse.Namespace(main_root=str(tmp_path), run=Path(state["run_root"]).name, round=attempt["round"])
    with redirect_stdout(io.StringIO()) as output:
        code = controller_tools.symexec(args)
    assert code == 0, output.getvalue()
    for role in symexec_tooling.MANDATORY_GENERATED_FILE_KEYS:
        assert (tmp_path / state["target_files"][role]).stat().st_size > 0



def _reuse_fixture(root, *, current_name="fresh", statement="True", with_library=True):
    run = root / "verification_runs/case-20260101000000"
    previous = run / "case-vc-proving-r1"
    prior = previous / "groups/group_00__old"
    directory = run / "case-vc-proving-r2/groups/group_00__new"
    prior.mkdir(parents=True)
    directory.mkdir(parents=True)
    base = "Ltac LLM_pre_process tac := tac.\n"
    (prior / "case_lib.v").write_text(base +
        "Lemma h1__old : True.\nProof. exact I. Qed.\n"
        "Lemma h2__old : True.\nProof. exact h1__old. Qed.\n", encoding="utf-8")
    (prior / "case_proof_manual.v").write_text(
        "Require Import case_lib.\nLemma prior : True.\nProof. LLM_pre_process ltac:(exact h2__old). Qed.\n", encoding="utf-8")
    manual = directory / "case_proof_manual.v"
    manual.write_text(f"Require Import case_lib.\nLemma {current_name} : {statement}.\nProof. Abort.\n"
                      "Lemma untouched : True.\nProof. Abort.\n", encoding="utf-8")
    library = directory / "case_lib.v"
    if with_library:
        library.write_text(base, encoding="utf-8")
    report = root / "reports/case-20260101000000/rounds/case-vc-proving-r2/groups/group_00__new"
    group = {"id": "new", "directory": str(directory), "proof_manual": str(manual),
             "report_directory": str(report), "helper_namespace": {"policy": "group-id-suffixed", "group_id": "new", "suffix": "__new", "required": "yes"},
             "witnesses": [{"name": current_name, "proof_mode": "LLM_pre_process", "split_goals": []}],
             "proof_reuse": str(report / "proof_reuse.md")}
    if with_library:
        group["group_worker_lib"] = str(library)
    return previous, prior, group


def test_witness_reuse_renames_proofs_and_helper_closure_and_compiles(tmp_path):
    previous, prior, group = _reuse_fixture(tmp_path)
    before = {path: path.read_bytes() for path in prior.iterdir()}
    sources, diagnostics = witness_reuse.load_reuse_sources(previous.parent, Path("Rocq/examples/demo/case_proof_manual.v"), previous.name)
    result = witness_reuse.seed_witness_reuse(group, sources, diagnostics)
    assert result["seeded"] == ["fresh"] and result["helper_count"] == 2
    library = Path(group["group_worker_lib"]).read_text(encoding="utf-8")
    manual = Path(group["proof_manual"]).read_text(encoding="utf-8")
    assert "h1__new" in library and "exact h1__new" in library and "h2__old" not in manual
    assert "Lemma untouched : True.\nProof. Abort." in manual
    assert all(path.read_bytes() == payload for path, payload in before.items())
    saved = (manual, library)
    assert witness_reuse.seed_witness_reuse(group, sources, diagnostics)["seeded"] == []
    assert saved == (Path(group["proof_manual"]).read_text(encoding="utf-8"), Path(group["group_worker_lib"]).read_text(encoding="utf-8"))
    if shutil.which("coqc"):
        build = tmp_path / "compile"
        build.mkdir()
        (build / "case_lib.v").write_text(library, encoding="utf-8")
        (build / "case_proof_manual.v").write_text(manual, encoding="utf-8")
        (build / "check.v").write_text("Require Import case_proof_manual.\nCheck fresh.\n", encoding="utf-8")
        for name in ("case_lib.v", "case_proof_manual.v", "check.v"):
            checked = subprocess.run([shutil.which("coqc"), "-q", name], cwd=build, capture_output=True, text=True, timeout=30)
            assert checked.returncode == 0, checked.stdout + checked.stderr


def _compile_reused_group(group):
    if shutil.which("coqc") is None:
        pytest.skip("requires native Coq")
    directory = Path(group["directory"])
    for field in ("group_worker_lib", "proof_manual"):
        if not group.get(field):
            continue
        checked = subprocess.run([shutil.which("coqc"), "-q", Path(group[field]).name],
                                 cwd=directory, capture_output=True, text=True, timeout=30)
        assert checked.returncode == 0, checked.stdout + checked.stderr


@pytest.mark.parametrize("missing", ["helper", "witness"])
def test_reuse_falls_back_when_first_candidate_has_missing_dependencies(tmp_path, missing):
    previous, prior, group = _reuse_fixture(tmp_path)
    newer = previous.parent / "case-vc-proving-r2/groups/group_00__old"
    newer.mkdir(parents=True)
    for path in prior.iterdir():
        shutil.copyfile(path, newer / path.name)
    if missing == "helper":
        library = newer / "case_lib.v"
        library.write_text(library.read_text().replace("exact h1__old. Qed.", "Abort."), encoding="utf-8")
    else:
        (newer / "case_proof_manual.v").write_text(
            "Require Import case_lib.\nLemma outside : True /\\ True.\n"
            "Proof. LLM_pre_process ltac:(split; exact I). Qed.\n"
            "Lemma prior : True.\nProof. LLM_pre_process ltac:(exact (proj1 outside)). Qed.\n", encoding="utf-8")
    index, diagnostics = witness_reuse.load_reuse_sources(
        previous.parent, Path("Rocq/examples/demo/case_proof_manual.v"), "case-vc-proving-r2")
    result = witness_reuse.seed_witness_reuse(group, index, diagnostics)
    assert result["seeded"] == ["fresh"]
    _compile_reused_group(group)


def test_reuse_renames_identical_split_goals_by_parent_and_label(tmp_path):
    previous, prior, group = _reuse_fixture(tmp_path)
    base = ("Ltac LLM_pre_process tac := tac.\n"
            "Ltac aggressive_pre_process := split.\nLtac Goal_apply H := exact H.\n")
    Path(group["group_worker_lib"]).write_text(base, encoding="utf-8")
    (prior / "case_lib.v").write_text(base, encoding="utf-8")
    for directory, parent, complete in [(prior, "old", True), (Path(group["directory"]), "fresh", False)]:
        split_names = [f"{parent}_split_goal_{i}" for i in (1, 2)]
        text = "Require Import case_lib.\n"
        for name in split_names:
            proof = "LLM_pre_process ltac:(exact I). Qed." if complete else "Abort."
            text += f"Lemma {name} : True.\nProof. {proof}\n"
        proof = (f"aggressive_pre_process.\n- Goal_apply {split_names[0]}.\n"
                 f"- Goal_apply {split_names[1]}.\nQed." if complete else "Abort.")
        text += f"Lemma {parent} : True /\\ True.\nProof. {proof}\n"
        (directory / "case_proof_manual.v").write_text(text, encoding="utf-8")
    group["witnesses"] = [{"name": "fresh", "proof_mode": "aggressive_pre_process",
                           "split_goals": [{"name": f"fresh_split_goal_{i}"} for i in (1, 2)]}]
    index, diagnostics = witness_reuse.load_reuse_sources(previous.parent, Path("Rocq/examples/demo/case_proof_manual.v"), previous.name)
    result = witness_reuse.seed_witness_reuse(group, index, diagnostics)
    assert set(result["seeded"]) == {"fresh", "fresh_split_goal_1", "fresh_split_goal_2"}
    _compile_reused_group(group)


def test_reuse_helper_rename_does_not_capture_a_proof_local(tmp_path):
    previous, prior, group = _reuse_fixture(tmp_path, statement="forall h2__new : nat, True")
    (prior / "case_proof_manual.v").write_text(
        "Require Import case_lib.\nLemma prior : forall h2__new : nat, True.\n"
        "Proof. LLM_pre_process ltac:(intros h2__new; exact h2__old). Qed.\n", encoding="utf-8")
    index, diagnostics = witness_reuse.load_reuse_sources(previous.parent, Path("Rocq/examples/demo/case_proof_manual.v"), previous.name)
    assert witness_reuse.seed_witness_reuse(group, index, diagnostics)["seeded"] == ["fresh"]
    _compile_reused_group(group)


def test_reuse_shared_helper_reserves_locals_in_later_candidates(tmp_path):
    previous, prior, group = _reuse_fixture(tmp_path)
    (prior / "case_proof_manual.v").write_text(
        "Require Import case_lib.\nLemma first : True.\n"
        "Proof. LLM_pre_process ltac:(exact h2__old). Qed.\n"
        "Lemma second : True.\nProof. LLM_pre_process ltac:(pose (h2__new := 0); exact h2__old). Qed.\n", encoding="utf-8")
    Path(group["proof_manual"]).write_text(
        "Require Import case_lib.\nLemma first : True.\nProof. Abort.\n"
        "Lemma second : True.\nProof. Abort.\n", encoding="utf-8")
    group["witnesses"] = [{"name": name, "proof_mode": "LLM_pre_process", "split_goals": []}
                           for name in ("first", "second")]
    index, diagnostics = witness_reuse.load_reuse_sources(previous.parent, Path("Rocq/examples/demo/case_proof_manual.v"), previous.name)
    result = witness_reuse.seed_witness_reuse(group, index, diagnostics)
    assert result["seeded"] == ["first", "second"] and result["helper_count"] == 2
    _compile_reused_group(group)


def test_reuse_falls_back_when_witness_dependency_moves_after_consumer(tmp_path):
    previous, prior, group = _reuse_fixture(tmp_path)
    (prior / "case_proof_manual.v").write_text(
        "Require Import case_lib.\nLemma first : True.\nProof. LLM_pre_process ltac:(exact I). Qed.\n"
        "Lemma second : True /\\ True.\nProof. LLM_pre_process ltac:(exact (conj first first)). Qed.\n"
        "Lemma independent : True /\\ True.\nProof. LLM_pre_process ltac:(split; exact I). Qed.\n", encoding="utf-8")
    Path(group["proof_manual"]).write_text(
        "Require Import case_lib.\nLemma second : True /\\ True.\nProof. Abort.\n"
        "Lemma first : True.\nProof. Abort.\n", encoding="utf-8")
    group["witnesses"] = [{"name": name, "proof_mode": "LLM_pre_process", "split_goals": []}
                           for name in ("second", "first")]
    index, diagnostics = witness_reuse.load_reuse_sources(previous.parent, Path("Rocq/examples/demo/case_proof_manual.v"), previous.name)
    assert witness_reuse.seed_witness_reuse(group, index, diagnostics)["seeded"] == ["second", "first"]
    _compile_reused_group(group)


def test_reuse_copies_only_helper_proofs_and_standalone_imports(tmp_path):
    previous, prior, group = _reuse_fixture(tmp_path)
    library = prior / "case_lib.v"
    library.write_text("From Coq Require Import List.\nImport ListNotations.\n" + library.read_text()
                       + "Ltac unrelated_tactic := idtac.\n", encoding="utf-8")
    seed = Path(group["group_worker_lib"]).read_text()
    index, diagnostics = witness_reuse.load_reuse_sources(previous.parent, Path("Rocq/examples/demo/case_proof_manual.v"), previous.name)
    assert witness_reuse.seed_witness_reuse(group, index, diagnostics)["seeded"] == ["fresh"]
    from proof_manual_utils import merge_group_worker_libs
    current = Path(group["group_worker_lib"]).read_text()
    merged, additions, renames, errors = merge_group_worker_libs(seed, [("new", current, group["helper_namespace"])])
    assert not errors, errors
    assert "unrelated_tactic" not in current and "Import ListNotations." not in current
    _compile_reused_group(group)


@pytest.mark.parametrize("same_statement", [False, True])
def test_reuse_checks_existing_helper_statement_before_sharing(tmp_path, same_statement):
    previous, prior, group = _reuse_fixture(tmp_path)
    library = Path(group["group_worker_lib"])
    proposition = "True" if same_statement else "False -> True"
    library.write_text(library.read_text() + f"Lemma h2__old : {proposition}.\n"
                       "Proof. intros; exact I. Qed.\n", encoding="utf-8")
    index, diagnostics = witness_reuse.load_reuse_sources(previous.parent, Path("Rocq/examples/demo/case_proof_manual.v"), previous.name)
    result = witness_reuse.seed_witness_reuse(group, index, diagnostics)
    assert result["seeded"] == ["fresh"]
    assert result["helper_count"] == (0 if same_statement else 2)
    _compile_reused_group(group)


def test_witness_reuse_checked_magic_items_proofs():
    """Exercise all real VC routes and the trading-model helper closure in isolation."""
    from proof_manual_utils import (HELPER_DECL_KINDS, HELPER_NAMESPACE_SUFFIX_RE,
        helper_namespace_for_group_id, lemma_proof_parts, parse_lib_declarations,
        parse_manual_file, partition_manual_lemmas, proof_mode_errors, merge_group_worker_libs)

    root = SCRIPTS.parents[1]
    relative = Path("Rocq/examples/LLM_bench/Algorithms/magic_items")
    manual_relative = relative / "magic_items_proof_manual.v"
    library_relative = relative / "magic_items_lib.v"
    if not (root / manual_relative).is_file() or not (root / library_relative).is_file():
        pytest.skip("requires the checked magic_items artifacts")
    if any(shutil.which(tool) is None for tool in ("coqc", "dune")):
        pytest.skip("requires native Coq/Dune")
    original = {path: (root / path).read_bytes() for path in (manual_relative, library_relative)}
    old_manual = original[manual_relative].decode("utf-8")
    old_library = original[library_relative].decode("utf-8")
    prelude, lemmas = parse_manual_file(old_manual)
    top, splits = partition_manual_lemmas(lemmas)
    witnesses = []
    for lemma in top:
        modes = [mode for mode in ("LLM_pre_process", "aggressive_pre_process")
                 if not proof_mode_errors(lemma["block"], mode)]
        assert len(modes) == 1, lemma["name"]
        witnesses.append({"name": lemma["name"], "proof_mode": modes[0],
                          "split_goals": splits[lemma["name"]]})
    raw = prelude + "".join(before + "Proof. Abort." + after
                             for before, _proof, after in map(lemma_proof_parts, lemmas))
    first_helper = min(item["start_offset"] for item in parse_lib_declarations(old_library)
                       if item["kind"] in HELPER_DECL_KINDS and HELPER_NAMESPACE_SUFFIX_RE.search(item["name"]))
    seed_library = old_library[:first_helper]
    runs = root / "verification_runs"
    runs.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="witness-reuse-test-", suffix="-20260101000000", dir=runs) as temporary:
        run = Path(temporary)
        previous = run / "magic_items-vc-proving-r1/groups/group_00__history"
        current = run / "magic_items-vc-proving-r2/groups/group_00__reused"
        previous.mkdir(parents=True)
        current.mkdir(parents=True)
        for directory, manual, library in [(previous, old_manual, old_library), (current, raw, seed_library)]:
            (directory / manual_relative.name).write_text(manual, encoding="utf-8")
            (directory / library_relative.name).write_text(library, encoding="utf-8")
        group = {"id": "reused", "directory": str(current),
                 "proof_manual": str(current / manual_relative.name),
                 "group_worker_lib": str(current / library_relative.name),
                 "proof_reuse": str(current / "proof_reuse.md"),
                 "helper_namespace": helper_namespace_for_group_id("reused"), "witnesses": witnesses}
        index, diagnostics = witness_reuse.load_reuse_sources(run, manual_relative, "magic_items-vc-proving-r1")
        result = witness_reuse.seed_witness_reuse(group, index, diagnostics)
        expected = {item["name"] for item in top} | {
            split["name"] for item in witnesses if item["proof_mode"] == "aggressive_pre_process"
            for split in item["split_goals"]}
        assert set(result["seeded"]) == expected and result["helper_count"] > 0, result
        _merged, _additions, _renames, errors = merge_group_worker_libs(
            seed_library, [("reused", (current / library_relative.name).read_text(), group["helper_namespace"])])
        assert not errors, errors
        target = relative / "magic_items_goal_check.v"
        receipt = coq_tooling_dune.prepare_dune_dependencies(
            workspace_root=root, target_file=target, current_case_anchor=manual_relative)
        assert receipt["status"] == "passed", receipt
        check = coq_tooling_dune.run_coqc_check(
            workspace_root=root, build_workspace=run / "_coq_builds/reuse/src", target_file=target,
            target_kind="check", current_case_anchor=manual_relative, dune_preparation=receipt,
            overlays={manual_relative: current / manual_relative.name, library_relative: current / library_relative.name})
        assert check["status"] == "passed", json.dumps(check, indent=2)
    assert all((root / path).read_bytes() == content for path, content in original.items())


@pytest.mark.parametrize("problem", ["changed-statement", "incomplete-helper", "unsafe-proof", "wrong-mode", "no-library"])
def test_witness_reuse_never_accepts_incompatible_or_incomplete_history(tmp_path, problem):
    previous, prior, group = _reuse_fixture(tmp_path, current_name="prior",
        statement="False" if problem == "changed-statement" else "True", with_library=problem != "no-library")
    if problem == "incomplete-helper":
        path = prior / "case_lib.v"
        path.write_text(path.read_text().replace("exact h1__old. Qed.", "Abort."), encoding="utf-8")
    elif problem in {"unsafe-proof", "wrong-mode"}:
        path = prior / "case_proof_manual.v"
        text = path.read_text().replace("Qed.", "Admitted.") if problem == "unsafe-proof" else path.read_text().replace("LLM_pre_process", "aggressive_pre_process")
        path.write_text(text, encoding="utf-8")
    before = Path(group["proof_manual"]).read_bytes()
    index, diagnostics = witness_reuse.load_reuse_sources(previous.parent, Path("Rocq/examples/demo/case_proof_manual.v"), previous.name)
    result = witness_reuse.seed_witness_reuse(group, index, diagnostics)
    assert result["seeded"] == []
    assert Path(group["proof_manual"]).read_bytes() == before
    assert Path(group["proof_reuse"]).is_file()


def test_current_input_edits_and_historical_notes_do_not_create_version_gates(tmp_path):
    state, attempt = _accepted_annotation_state(tmp_path)
    target = tmp_path / state["target_files"]["c_file"]
    target.write_text(target.read_text().replace("return x;", "return 0;"), encoding="utf-8")
    (Path(attempt["annotation_history_directory"]) / "after" / state["target_files"]["c_file"]).write_text("old history edited", encoding="utf-8")
    assert controller_state._current_files_errors(state) == []
    _, output = _cli(tmp_path, "step", "--run", Path(state["run_root"]).name)
    assert output["next_actions"][0]["action"] == "dune-build"
    assert len(controller_state._load_state(Path(state["run_root"]))["attempts"]) == 1


def test_production_scripts_have_no_digest_primitives_or_metadata():
    for path in SCRIPTS.rglob("*.py"):
        if "tests" in path.parts:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                assert "hashlib" not in ast.unparse(node), path
            if isinstance(node, ast.Dict):
                for key in node.keys:
                    if isinstance(key, ast.Constant) and isinstance(key.value, str):
                        assert not any(word in key.value for word in ("sha256", "digest", "fingerprint")), (path, key.value)



@pytest.mark.parametrize("backend", [coq_tooling_dune, coq_tooling_makefile])
@pytest.mark.parametrize("reuse_history", [False, True])
def test_controller_groups_parent_apply_and_final_use_current_files(tmp_path, monkeypatch, backend, reuse_history):
    if any(shutil.which(tool) is None for tool in ("coqc", "coqdep", "dune" if backend is coq_tooling_dune else "make")):
        pytest.skip("requires the selected native Coq/build tools")
    tmp_path = tmp_path / "源码 space (&)"
    tmp_path.mkdir()
    if backend is coq_tooling_dune:
        (tmp_path / "_build").mkdir()
    state, _ = _accepted_annotation_state(tmp_path, lib_text="Ltac LLM_pre_process tac := tac.\n")
    target = _backend_workspace(tmp_path, backend)
    target_files = state["target_files"]
    goal = tmp_path / target_files["goal_file"]
    goal.write_text(goal.read_text() + "From SimpleC.EE.demo Require Import case_lib.\n", encoding="utf-8")
    manual = tmp_path / target_files["proof_manual_file"]
    raw = "From SimpleC.EE.demo Require Import case_lib.\n" + manual.read_text().replace("exact I. Qed.", "Abort.")
    manual.write_text(raw, encoding="utf-8")
    run = Path(state["run_root"])
    if reuse_history:
        history = run / "annotation_history/annotation-attempt1/before" / manual.relative_to(tmp_path).parent
        history.mkdir(parents=True, exist_ok=True)
        (history / manual.name).write_text(
            raw.replace("Proof. Abort.", "Proof. LLM_pre_process ltac:(exact reused__history). Qed."), encoding="utf-8")
        (history / "case_lib.v").write_text("Ltac LLM_pre_process tac := tac.\n"
            "Lemma reused__history : True.\nProof. exact I. Qed.\n", encoding="utf-8")
    assert _cli(tmp_path, "dune-build", "--run", run.name)[0] == 0
    _, step = _cli(tmp_path, "step", "--run", run.name)
    action = step["next_actions"][0]
    _cli(tmp_path, "claim-attempt", "--run", run.name, "--next-action", action["id"], "--owner", "analysis")
    report = Path(action["report"])
    plan = {"groups": [{"id": name, "estimated_difficulty": 1,
                       "witnesses": [{"name": name, "proof_mode": "LLM_pre_process", "strategy": "prove True"}]}
                      for name in ("vc", "pending")]}
    (report.parent / "group_plan.json").write_text(json.dumps(plan), encoding="utf-8")
    report.write_text('{"status":"completed"}', encoding="utf-8")
    assert _cli(tmp_path, "finalize-delivery", "--run", run.name, "--attempt", action["attempt_id"], "--owner", "analysis")[0] == 0
    state = controller_state._load_state(run)
    vc_round = state["attempts"][action["attempt_id"]]["round"]
    assert _cli(tmp_path, "vc-checking-check-round", "--run", run.name, "--round", vc_round)[0] == 0
    _, step = _cli(tmp_path, "step", "--run", run.name)
    proving_round = step["next_actions"][0]["round"]
    assert _cli(tmp_path, "vc-proving-preparing", "--run", run.name, "--round", proving_round)[0] == 0
    for name in ("vc", "pending"):
        _, step = _cli(tmp_path, "step", "--run", run.name)
        action = next(item for item in step["next_actions"] if item.get("group_id") == name)
        _cli(tmp_path, "claim-attempt", "--run", run.name, "--next-action", action["id"], "--owner", name)
        state = controller_state._load_state(run)
        manifest = controller_attempts._resolved_proving_manifest(state, state["attempts"][proving_round])
        group = next(item for item in manifest["groups"] if item["id"] == name)
        copied = Path(group["proof_manual"])
        if reuse_history:
            assert f"exact reused__{name}" in copied.read_text()
            assert "seeded from" in Path(group["proof_reuse"]).read_text()
            before_check = Path(state["report_root"], "controller_state.json").read_bytes()
            assert _cli(tmp_path, "coq-check", "--run", run.name, "--round", proving_round,
                        "--group", name, "--target-kind", "group-check")[0] == 0
            assert Path(state["report_root"], "controller_state.json").read_bytes() == before_check
        else:
            copied.write_text(copied.read_text().replace(f"Lemma {name} : True.\nProof. Abort.",
                              f"Lemma {name} : True.\nProof. LLM_pre_process ltac:(exact I). Qed."), encoding="utf-8")
        Path(action["report"]).write_text('{"status":"completed"}', encoding="utf-8")
        code, result = _cli(tmp_path, "finalize-delivery", "--run", run.name, "--attempt", action["attempt_id"], "--owner", name)
        assert code == 0, result
        assert controller_state._load_state(run)["attempts"][proving_round]["groups"][name]["status"] == "accepted"
        if name == "vc":
            original_proof = f"ltac:(exact reused__{name})" if reuse_history else "ltac:(exact I)"
            copied.write_text(copied.read_text().replace(original_proof, "ltac:(constructor)"), encoding="utf-8")
            assert _cli(tmp_path, "finalize-delivery", "--run", run.name, "--attempt", action["attempt_id"], "--owner", name)[0] == 0
            assert controller_state._load_state(run)["attempts"][proving_round]["groups"][name]["status"] == "accepted"
    assert _run_next_action(tmp_path, run.name, "vc-proving-verify")[0] == 0
    candidate = run / proving_round / "proving_merged" / manual.name
    candidate.write_text(candidate.read_text() + "(* latest candidate edit *)\n", encoding="utf-8")
    assert _run_next_action(tmp_path, run.name, "final-apply")[0] == 0
    assert manual.read_text().endswith("(* latest candidate edit *)\n")
    refresh = tmp_path / "reports" / run.name / "final-check/symexec-refresh"
    (refresh / target_files["proof_manual_file"]).parent.mkdir(parents=True)
    (refresh / target_files["proof_manual_file"]).write_text(raw, encoding="utf-8")
    refresh_status = "failed"

    def freshness(current):
        # Older scheduler states can retain this wait even with an applied
        # candidate. Final success and rollback must both consume it.
        current["waiting_for"] = [{"phase": "final-check", "status": "awaiting-step"}]
        return {"status": refresh_status, "refresh_root": str(refresh)}

    monkeypatch.setattr(controller_final, "_freshness_evidence", freshness)
    assert _run_next_action(tmp_path, run.name, "final-check")[0] == 1
    assert manual.read_text() == raw
    rolled_back = controller_state._load_state(run)
    assert rolled_back["phase"] == "final-candidate-apply" and rolled_back["waiting_for"] == []
    assert _run_next_action(tmp_path, run.name, "final-apply")[0] == 0
    refresh_status = "passed"
    code, result = _run_next_action(tmp_path, run.name, "final-check")
    assert code == 0, result
    finished = controller_state._load_state(run)
    assert finished["phase"] == "done" and finished["waiting_for"] == [] and finished["next_actions"] == []



@pytest.mark.parametrize("backend", [coq_tooling_dune, coq_tooling_makefile])
def test_unreferenced_current_library_is_still_compiled(tmp_path, backend):
    if any(shutil.which(tool) is None for tool in ("coqc", "coqdep", "dune" if backend is coq_tooling_dune else "make")):
        pytest.skip("requires native Coq/build tools")
    target = _backend_workspace(tmp_path, backend)
    receipt = backend.prepare_dune_dependencies(workspace_root=tmp_path, target_file=target, current_case_anchor=target)
    assert receipt["status"] == "passed", receipt
    library = tmp_path / target.with_name("case_lib.v")
    library.write_text("Lemma bad : False.\nProof. exact I. Qed.\n", encoding="utf-8")
    build = tmp_path / "verification_runs/case-20260101000000/_coq_builds/unused/src"
    result = backend.run_coqc_check(workspace_root=tmp_path, build_workspace=build, target_file=target,
                                    target_kind="check", current_case_anchor=target, dune_preparation=receipt)
    assert result["status"] == "failed" and "case_lib.v" in str(result)


def test_timing_records_do_not_rewrite_business_state(tmp_path):
    state, attempt = _accepted_annotation_state(tmp_path)
    run = Path(state["run_root"])
    path = Path(state["report_root"]) / "controller_state.json"
    before = path.read_bytes()
    controller_state._record_timing(run, "annotation-check-round", started_at=attempt["created_at"],
                                    elapsed_seconds=1, round_id=attempt["round"])
    assert path.read_bytes() == before
    summary = json.loads((Path(state["report_root"]) / "timing_summary.json").read_text(encoding="utf-8"))
    assert summary["annotation_attempts"]


@pytest.mark.skipif(os.name != "nt", reason="requires native Windows file sharing")
def test_windows_publication_recovers_after_sharing_violation(tmp_path):
    import ctypes
    from ctypes import wintypes

    args = _publication_fixture(tmp_path)
    target = args["target_files"]
    original = annotation_refresh.generated_output_contents(tmp_path, target)
    kernel = ctypes.WinDLL("kernel32", use_last_error=True)
    create = kernel.CreateFileW
    create.argtypes = (wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, wintypes.LPVOID,
                       wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE)
    create.restype = wintypes.HANDLE
    close = kernel.CloseHandle
    close.argtypes, close.restype = (wintypes.HANDLE,), wintypes.BOOL
    handle = create(str(tmp_path / target["proof_auto_file"]), 0x80000000, 3, None, 3, 0x80, None)
    assert handle != ctypes.c_void_p(-1).value, ctypes.get_last_error()
    try:
        with pytest.raises(annotation_refresh.AnnotationRefreshError):
            annotation_refresh.publish_generated_output(**args)
        assert annotation_refresh.generated_output_contents(tmp_path, target) == original
    finally:
        close(handle)
    assert annotation_refresh.publish_generated_output(**args)["status"] == "committed"


@pytest.mark.skipif(os.name != "nt", reason="requires native Windows junctions")
def test_windows_cleanup_does_not_follow_junction(tmp_path):
    root = tmp_path / "workspace"
    run = root / "verification_runs/case-20260101000000"
    outside = tmp_path / "outside"
    run.mkdir(parents=True)
    outside.mkdir()
    sentinel = outside / "keep.vo"
    sentinel.write_bytes(b"outside")
    junction = run / "redirect"
    created = subprocess.run(["cmd", "/d", "/c", "mklink", "/J", str(junction), str(outside)], capture_output=True, text=True)
    if created.returncode:
        pytest.skip("junction creation unavailable: " + created.stderr)
    try:
        result = controller_final._remove_old_coq_side_products(root, run, target_files_for_c("QCP_examples/demo/case.c", "case"))
        assert result["error_count"] == 1
        assert sentinel.read_bytes() == b"outside"
    finally:
        junction.rmdir()



def test_windows_path_projection_uses_current_layout_without_creating_directories(tmp_path):
    root = tmp_path / "not-created"
    target = target_files_for_c("QCP_examples/demo/deep/case.c", "case")
    diagnostic = controller_state._windows_path_length_error(
        main_root=root, projected_run_name="case-20260101000000", target_files=target, file_limit=1, directory_limit=1)
    assert diagnostic and "0" * 32 not in diagnostic
    assert not root.exists()



@pytest.mark.parametrize("manual_present, library_present", [(False, False), (True, False), (False, True), (True, True)])
def test_zero_vc_publication_supports_zero_one_or_two_current_files(tmp_path, monkeypatch, manual_present, library_present):
    if any(shutil.which(tool) is None for tool in ("coqc", "coqdep", "make")):
        pytest.skip("requires native Coq/Make tools")
    c = _c_file(tmp_path)
    _, initial = _cli(tmp_path, "init-run", "--case", "case", "--target-c-file", str(c),
                      "--formal-case-lib-policy", "create" if library_present else "absent")
    run = Path(initial["run_root"])
    _, step = _cli(tmp_path, "step", "--run", run.name)
    action = step["next_actions"][0]
    _cli(tmp_path, "claim-attempt", "--run", run.name, "--next-action", action["id"], "--owner", action["owner"])
    state = controller_state._load_state(run)
    target = state["target_files"]
    directory = tmp_path / target["formal_directory"]
    directory.mkdir(parents=True, exist_ok=True)
    for role in ("goal_file", "proof_auto_file", "goal_check_file"):
        (tmp_path / target[role]).write_text("From Coq Require Import Bool.\n", encoding="utf-8")
    if manual_present:
        (tmp_path / target["proof_manual_file"]).write_text("From Coq Require Import Bool.\n", encoding="utf-8")
    (tmp_path / "Rocq/Makefile").write_text("# native exact build\n", encoding="utf-8")
    for _flag, physical, _logical in coq_tooling_makefile.FIXED_LOAD_PATH_MAPPINGS:
        (tmp_path / physical).mkdir(parents=True, exist_ok=True)
    attempt = state["attempts"][action["attempt_id"]]
    controller_state._archive_annotation_stage(state, attempt, "after")
    attempt["status"] = "accepted"
    state["accepted_rounds"]["annotation"] = {key: attempt[key] for key in ("round", "attempt_id", "annotation_history_directory")}
    state["annotation_session"]["status"] = "idle"
    state["next_actions"] = []
    controller_state._save_state(run, state)
    assert _cli(tmp_path, "dune-build", "--run", run.name)[0] == 0
    _, step = _cli(tmp_path, "step", "--run", run.name)
    proving = step["next_actions"][0]["round"]
    assert _cli(tmp_path, "vc-proving-preparing", "--run", run.name, "--round", proving)[0] == 0
    assert _run_next_action(tmp_path, run.name, "vc-proving-verify")[0] == 0
    code, result = _run_next_action(tmp_path, run.name, "final-apply")
    assert code == 0, result
    assert len(result["files"]) == int(manual_present) + int(library_present)
    refresh = tmp_path / "reports" / run.name / "final-check/symexec-refresh"
    (refresh / target["formal_directory"]).mkdir(parents=True)
    if manual_present:
        (refresh / target["proof_manual_file"]).write_text("From Coq Require Import Bool.\n", encoding="utf-8")
    monkeypatch.setattr(controller_final, "_freshness_evidence", lambda _state: {"status": "passed", "refresh_root": str(refresh)})
    code, result = _run_next_action(tmp_path, run.name, "final-check")
    assert code == 0, result
    assert (tmp_path / target["proof_manual_file"]).exists() is manual_present
    assert (tmp_path / target["formal_case_lib"]).exists() is library_present



def test_annotation_retry_uses_current_gap_report_and_keeps_owner(tmp_path):
    state, original = _accepted_annotation_state(tmp_path)
    run = Path(state["run_root"])
    owner = state["annotation_session"]["owner"]
    attempt = controller_rounds._init_round_attempt(state, phase="vc-checking")
    controller_state._save_state(run, state)
    action = state["next_actions"][0]
    _cli(tmp_path, "claim-attempt", "--run", run.name, "--next-action", action["id"], "--owner", "checker")
    paths = controller_state._validated_attempt_paths(state, attempt)
    report = {"status": "blocked", "blocker": {"failure_class": "annotation-gap", "kind": "missing-annotation-premise",
              "vcs": [{"name": "vc", "parent": None, "annotation_location": "f/entry"}],
              "message": "old explanation", "repair_boundary": "C annotation"}}
    paths["report"].write_text(json.dumps(report), encoding="utf-8")
    paths["output"].write_text("缺失 premise 的说明", encoding="utf-8")
    assert _cli(tmp_path, "finalize-delivery", "--run", run.name,
                "--attempt", attempt["attempt_id"], "--owner", "checker")[0] == 0
    report["blocker"]["message"] = "updated explanation"
    paths["report"].write_text(json.dumps(report), encoding="utf-8")
    state = controller_state._load_state(run)
    retry = state["next_actions"][0]
    args = ("retry-round", "--run", run.name, "--phase", "annotation", "--reason", retry["reason"],
            "--previous-attempt", retry["previous_attempt"])
    assert _cli(tmp_path, *args)[0] == 0
    state = controller_state._load_state(run)
    current = state["attempts"][state["annotation_session"]["current_attempt"]]
    assert current["failed_vcs"][0]["name"] == "vc"
    assert current["failed_vcs"][0]["message"] == "updated explanation"
    assert state["annotation_session"]["owner"] == owner
    assert state["next_actions"][0]["kind"] == "append-annotation-agent"
    assert _cli(tmp_path, *args)[1]["status"] == "already-retried"



def _prepared_group_state(tmp_path):
    state, _ = _accepted_annotation_state(tmp_path)
    run = Path(state["run_root"])
    vc = controller_rounds._init_round_attempt(state, phase="vc-checking")
    paths = controller_state._validated_attempt_paths(state, vc)
    paths["group_plan"].write_text(json.dumps({"groups": [{"id": "g", "estimated_difficulty": 1,
        "witnesses": [{"name": "vc", "proof_mode": "LLM_pre_process", "strategy": "prove current goal"}]}]}), encoding="utf-8")
    vc["status"] = "accepted"
    state["accepted_rounds"]["vc-checking"] = {"round": vc["round"], "attempt_id": vc["attempt_id"], "group_plan": str(paths["group_plan"])}
    proving = controller_rounds._init_vc_proving_attempt(state)
    controller_state._save_state(run, state)
    assert _cli(tmp_path, "vc-proving-preparing", "--run", run.name, "--round", proving["round"])[0] == 0
    state = controller_state._load_state(run)
    proving = state["attempts"][proving["round"]]
    group = controller_attempts._resolved_proving_manifest(state, proving)["groups"][0]
    return state, proving, group


def test_group_gap_aggregation_reads_latest_reports_without_seals(tmp_path):
    state, proving, group = _prepared_group_state(tmp_path)
    blocker = {"failure_class": "annotation-gap", "kind": "missing-annotation-premise",
               "vcs": [{"name": "vc", "parent": None, "annotation_location": "f/entry"}],
               "message": "first explanation", "repair_boundary": "C annotation"}
    proving["groups"]["g"].update(status="blocked", blockers=[blocker])
    report = Path(group["report_directory"]) / "group_worker_report.json"
    report.write_text(json.dumps({"status": "blocked", "blocker": {**blocker, "message": "current explanation"}}), encoding="utf-8")
    (report.parent / "group_worker_output.md").write_text("current explanation", encoding="utf-8")
    controller_rounds._sync_group_actions(state, proving)
    sources, payloads, records, failures = controller_attempts._feedback_sources_for_retry(state, proving["round"])
    assert sources and payloads and records
    assert records[0]["message"] == failures[0]["message"] == "current explanation"



def test_first_round_reuses_existing_pre_generation_proofs(tmp_path):
    previous, prior, group = _reuse_fixture(tmp_path)
    relative = Path("Rocq/examples/demo/case_proof_manual.v")
    before = previous.parent / "annotation_history/annotation-attempt1/before" / relative.parent
    before.mkdir(parents=True)
    for source in prior.iterdir():
        (before / source.name).write_bytes(source.read_bytes())
    index, diagnostics = witness_reuse.load_reuse_sources(previous.parent, relative)
    assert index["source_count"] == 1
    result = witness_reuse.seed_witness_reuse(group, index, diagnostics)
    assert result["seeded"] == ["fresh"]
    assert "annotation-attempt1/before" in Path(group["proof_reuse"]).read_text(encoding="utf-8")


def test_wrong_owner_cannot_finalize_current_delivery(tmp_path):
    state, attempt = _running_annotation(tmp_path)
    report = Path(attempt["report"])
    report.write_text('{"status":"completed"}', encoding="utf-8")
    state_path = Path(state["report_root"]) / "controller_state.json"
    before = state_path.read_bytes()
    with pytest.raises(SystemExit, match="owner"):
        _cli(tmp_path, "finalize-delivery", "--run", Path(state["run_root"]).name,
             "--attempt", attempt["attempt_id"], "--owner", "another-owner")
    assert state_path.read_bytes() == before


def test_step_reports_stalled_state_and_preserves_running_wait(tmp_path):
    state, attempt = _running_annotation(tmp_path)
    run = Path(state["run_root"])
    _, result = _cli(tmp_path, "step", "--run", run.name)
    assert result["waiting_for"] and not result.get("current_blockers")
    state = controller_state._load_state(run)
    state["attempts"][attempt["attempt_id"]]["status"] = "prepared"
    state["next_actions"] = []
    controller_state._save_state(run, state)
    for _ in range(2):
        _, result = _cli(tmp_path, "step", "--run", run.name)
        assert result["waiting_for"][0]["status"] == "blocked"
        assert result["current_blockers"][0]["kind"] == "controller-no-progress"
    state = controller_state._load_state(run)
    state["attempts"][attempt["attempt_id"]]["status"] = "running"
    controller_state._save_state(run, state)
    _, result = _cli(tmp_path, "step", "--run", run.name)
    assert result["waiting_for"] and not result.get("current_blockers")


@pytest.mark.parametrize("command", ["coq-check", "coq-debug"])
@pytest.mark.parametrize("outcome", ["passed", "failed", "interrupted"])
def test_group_tool_logs_survive_errors_without_state_writes(tmp_path, monkeypatch, command, outcome):
    state, proving, group = _prepared_group_state(tmp_path)
    run = Path(state["run_root"])
    action = state["next_actions"][0]
    _cli(tmp_path, "claim-attempt", "--run", run.name, "--next-action", action["id"], "--owner", "worker")
    state_path = Path(state["report_root"]) / "controller_state.json"
    before = state_path.read_bytes()

    def check(*args, **kwargs):
        if outcome == "interrupted":
            raise KeyboardInterrupt()
        result = {"status": outcome, "returncode": 0 if outcome == "passed" else 124}
        if outcome == "failed":
            result["first_failure"] = {"category": "tooling", "kind": "dune-lock-timeout", "message": "wait expired"}
        if command == "coq-debug":
            script = str(kwargs["build_workspace"] / kwargs["debug_script"])
            result.update(debug_script_path=script, load_argument=script,
                          resolved_script_path=script, resolved_matches_authorized=True)
        return result

    monkeypatch.setattr(controller_tools, "_execute_group_check", check)
    monkeypatch.setattr(controller, "run_coqtop_debug", check)
    args = [command, "--run", run.name, "--round", proving["round"], "--group", group["id"]]
    if command == "coq-check":
        args += ["--target-kind", "group-development"]
    if outcome == "interrupted":
        with pytest.raises(KeyboardInterrupt):
            _cli(tmp_path, *args)
    else:
        assert _cli(tmp_path, *args)[0] == (0 if outcome == "passed" else 1)
    assert state_path.read_bytes() == before
    records = [json.loads(line) for line in (Path(group["report_directory"]) / "tool_calls.jsonl").read_text().splitlines()]
    start, finish = records
    assert start["event"] == "started" and finish["event"] == "finished"
    assert start["call_id"] == finish["call_id"]
    assert finish["command"] == command and finish["group"] == group["id"]
    assert finish["exit_code"] == {"passed": 0, "failed": 1, "interrupted": 130}[outcome]
    assert finish["elapsed_seconds"] >= 0
    if outcome == "failed":
        assert finish["returncode"] == 124 and finish["first_failure"]["kind"] == "dune-lock-timeout"


def test_dune_lock_waits_across_processes_and_releases_on_exit(tmp_path):
    lock = coq_tooling_dune._acquire_dune_lock(tmp_path, time.monotonic() + 5)
    script = (
        f"import sys,time; from pathlib import Path; sys.path.insert(0, {str(SCRIPTS / 'vc-proving')!r}); "
        "from coq_tooling_dune import _acquire_dune_lock; "
        f"handle = _acquire_dune_lock(Path({str(tmp_path)!r}), time.monotonic()+5); "
        "print('acquired',flush=True); time.sleep(30)"
    )
    child = subprocess.Popen([sys.executable, "-c", script], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    try:
        with pytest.raises(subprocess.TimeoutExpired) as waiting:
            child.communicate(timeout=.5)
        assert b"acquired" not in (waiting.value.output or b"")
        lock.close()
        with pytest.raises(subprocess.TimeoutExpired) as acquired:
            child.communicate(timeout=1)
        assert b"acquired" in (acquired.value.output or b"")
        assert b"waiting for Dune dependency lock" in (acquired.value.stderr or b"")
    finally:
        lock.close()
        child.kill()
        child.communicate(timeout=5)
    # Abrupt owner exit releases the OS lock without deleting the lock file.
    coq_tooling_dune._acquire_dune_lock(tmp_path, time.monotonic() + 1).close()


def test_dune_lock_wait_honors_deadline_and_cancellation(tmp_path, monkeypatch):
    target = _backend_workspace(tmp_path, coq_tooling_dune)
    monkeypatch.setattr(coq_tooling_dune, "run_bounded_process", lambda *a, **kw: pytest.fail("lock wait must not start Dune"))
    lock = coq_tooling_dune._acquire_dune_lock(tmp_path, time.monotonic() + 1)
    try:
        result = coq_tooling_dune.prepare_dune_dependencies(
            workspace_root=tmp_path, target_file=target, current_case_anchor=target, timeout_seconds=.05)
        assert result["returncode"] == 124
        assert result["first_failure"]["kind"] == "dune-lock-timeout"
        signal = tmp_path / "control.json"
        signal.write_text('{"status":"paused"}', encoding="utf-8")
        monkeypatch.setenv(CONTROL_SIGNAL_ENV, str(signal))
        with pytest.raises(ProcessCancelled):
            coq_tooling_dune.prepare_dune_dependencies(
                workspace_root=tmp_path, target_file=target, current_case_anchor=target, timeout_seconds=1)
    finally:
        lock.close()
    monkeypatch.delenv(CONTROL_SIGNAL_ENV)
    coq_tooling_dune._acquire_dune_lock(tmp_path, time.monotonic() + 1).close()


@pytest.mark.parametrize("code, diagnostic, kind", [
    (124, "Request forwarded to running Dune instance\nDune base build timed out", "dune-build-timeout"),
    (1, "Error: A running dune instance has locked the build directory", "dune-lock-conflict"),
    (1, 'File "Base.v", line 1, characters 0-10:\nError: proof failed', "dune-base-build-failed"),
    (130, "interrupted", "dune-build-interrupted"),
])
def test_dune_failures_distinguish_waiting_from_source_errors(code, diagnostic, kind):
    result = coq_tooling_dune._dune_process_failure(
        ProcessResult(code, "", diagnostic), target=Path("case.v"), started=time.monotonic(),
        stage="base-build", argv=["dune", "build"])
    assert result["first_failure"]["kind"] == kind
    assert result["returncode"] == code and result["stage"] == "base-build"
    assert result["stderr_tail"] == diagnostic
    if kind in {"dune-build-timeout", "dune-lock-conflict"}:
        assert "Repair" not in result["first_failure"]["repair"]


def test_build_progress_identifies_stage_without_polluting_json(capsys):
    progress = tool_progress("Dune base build for case.v")
    progress(29, "", "")
    assert capsys.readouterr().err == ""
    progress(30, "", "Request forwarded to Dune instance 42")
    output = capsys.readouterr()
    assert output.out == ""
    assert "Dune base build for case.v" in output.err and "instance 42" in output.err
