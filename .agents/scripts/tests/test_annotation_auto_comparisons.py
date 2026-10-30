"""A repaired manual obligation can move to the generator's auto module."""
from pathlib import Path
import sys

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(SCRIPTS / name) for name in ("verification-orchestrator", "vc-proving")]

from annotation_design import annotation_plan_errors
from controller_round_checks import _annotation_obligations
from controller_state import _manual_obligations


def state(tmp_path, auto=True):
    (tmp_path / "manual.v").write_text("Lemma manual_vc : True. Proof. Abort.\n", encoding="utf-8")
    if auto:
        (tmp_path / "auto.v").write_text("Lemma repaired_vc : True. Proof. exact I. Qed.\n", encoding="utf-8")
    return {"main_root": str(tmp_path), "target_files": {
        "proof_manual_file": "manual.v", "proof_auto_file": "auto.v"}}


def comparison(name):
    failed = [{"source_attempt": "old", "name": "old_vc", "parent": None,
               "annotation_location": "return", "manual": "/old.v", "message": "range lost"}]
    plan = {"version": 2, "status": "ready", "function_specs": [],
            "loop_invariants": [], "new_predicates": [], "vc_comparisons": [{
                "source": {"attempt": "old", "name": "old_vc", "annotation_location": "return"},
                "current": [name], "old_gap": "range lost", "change": "restore typed cell", "result": "resolved"}]}
    return failed, plan


def test_repaired_auto_identity_is_accepted_without_adding_manual_work(tmp_path):
    current = state(tmp_path)
    failed, plan = comparison("repaired_vc")
    assert not annotation_plan_errors(plan, failed_vcs=failed, current_vcs=_annotation_obligations(current))
    assert set(_manual_obligations(current)["by_name"]) == {"manual_vc"}


def test_unknown_identity_still_rejected(tmp_path):
    failed, plan = comparison("missing_vc")
    errors = annotation_plan_errors(plan, failed_vcs=failed, current_vcs=_annotation_obligations(state(tmp_path)))
    assert any("current VC does not exist: missing_vc" in error for error in errors)


def test_absent_auto_does_not_allow_unknown_identity(tmp_path):
    current = state(tmp_path, auto=False)
    assert _annotation_obligations(current) == _manual_obligations(current)


def test_manual_overlap_keeps_manual_identity(tmp_path):
    current = state(tmp_path)
    (tmp_path / "auto.v").write_text("Lemma manual_vc : False. Proof. Abort.\n", encoding="utf-8")
    assert _annotation_obligations(current)["by_name"]["manual_vc"] == _manual_obligations(current)["by_name"]["manual_vc"]
