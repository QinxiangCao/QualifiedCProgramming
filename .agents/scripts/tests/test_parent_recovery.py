"""Infrastructure recovery must never imply proof acceptance."""
import argparse
import copy
import sys
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(SCRIPTS / name) for name in ("verification-orchestrator", "vc-proving")]

import controller_proving
import coq_tooling_common


def recovery_state():
    parent = {"attempt_id": "p", "phase": "vc-proving", "status": "blocked",
              "source_annotation": "a", "groups": {"one": {"status": "accepted"}},
              "blocker": {"failure_class": "parent-check", "message": "timeout"}}
    review = {"attempt_id": "v", "phase": "vc-checking", "status": "blocked",
              "owner": "reviewer",
              "retry_reason": "parent-check-failed", "retry_previous_attempt": "p",
              "blocker": {"failure_class": "infrastructure"}}
    return {"phase": "vc-checking", "run_control": {"status": "active"},
            "run_root": "/unused", "main_root": "/unused", "run_id": "example",
            "current_blockers": [review["blocker"]],
            "current": {"annotation": "a", "vc-checking": "v", "vc-proving": None},
            "attempts": {"a": {"attempt_id": "a", "status": "accepted", "phase": "annotation"}, "p": parent, "v": review}}


@pytest.mark.parametrize("unsafe", [None, "semantic", "group", "paused", "drift", "published", "annotation", "running"])
def test_parent_recovery_keeps_evidence_and_requires_new_full_check(monkeypatch, unsafe):
    state = recovery_state()
    if unsafe == "semantic":
        state["attempts"]["v"]["blocker"]["failure_class"] = "annotation-gap"
    elif unsafe == "group":
        state["attempts"]["p"]["groups"]["one"]["status"] = "blocked"
    elif unsafe == "paused":
        state["run_control"]["status"] = "paused"
    elif unsafe == "published":
        state["final_apply"] = {"status": "applied"}
    elif unsafe == "annotation":
        state["attempts"]["p"]["source_annotation"] = "older"
    elif unsafe == "running":
        state["attempts"]["v"]["status"] = "running"
    original = copy.deepcopy(state)
    saved = []
    monkeypatch.setattr(controller_proving, "load_run", lambda args: state)
    monkeypatch.setattr(controller_proving, "_current_files_errors", lambda s: ["changed"] if unsafe == "drift" else [])
    monkeypatch.setattr(controller_proving, "_save_state", lambda root, s: saved.append(copy.deepcopy(s)))
    monkeypatch.setattr(controller_proving, "_respond", lambda s, result: 0)
    args = argparse.Namespace(round="p", reason="User increased the command budget to 30 minutes")
    if unsafe:
        with pytest.raises(SystemExit):
            controller_proving.retry_parent(args)
        assert not saved and state == original
        return
    assert controller_proving.retry_parent(args) == 0
    assert len(saved) == 1
    assert state["phase"] == "vc-proving" and state["current"]["vc-proving"] == "p"
    assert state["attempts"]["p"]["status"] == "running"
    assert state["attempts"]["p"]["groups"] == original["attempts"]["p"]["groups"]
    assert state["attempts"]["v"] == original["attempts"]["v"]
    assert state["attempts"]["p"]["parent_retries"][0]["previous_blocker"] == original["attempts"]["p"]["blocker"]
    assert not state.get("final_candidate") and not state.get("final_apply")


def test_thirty_minute_budget_preserves_shorter_requested_deadlines(monkeypatch):
    monkeypatch.setattr(coq_tooling_common.time, "monotonic", lambda: 100)
    monkeypatch.delenv("QCP_COQ_TIMEOUT_SECONDS", raising=False)
    assert coq_tooling_common.command_deadline(None) == 1900
    assert coq_tooling_common.command_deadline(3600) == 1900
    assert coq_tooling_common.command_deadline(60) == 160
