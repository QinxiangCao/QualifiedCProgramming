"""Publication retries must preserve backup ownership and external edits."""
import sys
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(SCRIPTS / name) for name in ("verification-orchestrator", "vc-proving")]

import annotation_refresh as refresh
import controller_final as final
from controller_rounds import derive_actions


@pytest.fixture
def state(tmp_path):
    (tmp_path / "manual.v").write_bytes(b"original")
    return {"main_root": str(tmp_path), "report_root": str(tmp_path / "reports"), "run_root": str(tmp_path / "run"),
            "run_id": "fixture", "phase": "final-apply", "run_control": {"status": "active"},
            "current_blockers": [], "target_files": {"proof_manual_file": "manual.v"},
            "final_apply_transaction": {"roles": ["proof_manual_file"], "status": "preparing"}}


def publish(state):
    backup, files = final._publication(state)
    return refresh.publish_file_contents(main_root=Path(state["main_root"]), target_files=files,
        payloads={"proof_manual_file": b"candidate"}, expected={"proof_manual_file": b"original"},
        transaction=backup, keep_backup=True)


def denial(winerror=5):
    error = PermissionError("rename denied fixture")
    error.winerror = winerror
    return error


@pytest.mark.parametrize("winerror", [5, 32, 33])
def test_transient_backup_rename_retry(state, monkeypatch, winerror):
    replace = refresh.os.replace
    attempts = []
    sleeps = []
    def flaky(source, destination):
        if Path(source).name == "transaction":
            attempts.append(source)
            assert (Path(state["main_root"]) / "manual.v").read_bytes() == b"original"
            if len(attempts) < 3:
                raise denial(winerror)
        return replace(source, destination)
    monkeypatch.setattr(refresh.os, "replace", flaky)
    monkeypatch.setattr(refresh.time, "sleep", sleeps.append)
    assert publish(state)["status"] == "committed"
    assert len(attempts) == 3 and sleeps == [0.05, 0.1]
    assert (Path(state["main_root"]) / "manual.v").read_bytes() == b"candidate"


@pytest.mark.parametrize("winerror, expected_attempts", [(5, 5), (87, 1), (None, 1)])
def test_failed_backup_creation_never_writes_canonical(state, monkeypatch, winerror, expected_attempts):
    replace = refresh.os.replace
    attempts = []
    def fail(source, destination):
        if Path(source).name == "transaction":
            attempts.append(source)
            raise denial(winerror)
        return replace(source, destination)
    monkeypatch.setattr(refresh.os, "replace", fail)
    monkeypatch.setattr(refresh.time, "sleep", lambda _: None)
    with pytest.raises(refresh.AnnotationRefreshError):
        publish(state)
    assert len(attempts) == expected_attempts
    assert (Path(state["main_root"]) / "manual.v").read_bytes() == b"original"
    assert not final._publication(state)[0].exists()
    assert final._rollback(state) is None
    assert final._rollback(state) is None


def test_backup_appearing_during_retry_is_not_recovered_or_deleted(state, monkeypatch):
    replace = refresh.os.replace
    backup, _ = final._publication(state)
    def fail(source, destination):
        if Path(source).name == "transaction":
            raise denial()
        return replace(source, destination)
    def external_backup(_):
        backup.mkdir()
        (backup / "external").write_bytes(b"do not remove")
    monkeypatch.setattr(refresh.os, "replace", fail)
    monkeypatch.setattr(refresh.time, "sleep", external_backup)
    with pytest.raises(refresh.AnnotationRefreshError, match="appeared during preparation"):
        publish(state)
    assert (backup / "external").read_bytes() == b"do not remove"
    assert (Path(state["main_root"]) / "manual.v").read_bytes() == b"original"


def test_real_rollback_is_idempotent_and_refuses_external_edits(state):
    publish(state)
    state["final_apply_transaction"]["status"] = "applied"
    assert final._rollback(state) is None
    assert final._rollback(state) is None
    canonical = Path(state["main_root"]) / "manual.v"
    assert canonical.read_bytes() == b"original"
    canonical.write_bytes(b"external edit")
    assert "external edit" in final._rollback(state)
    assert canonical.read_bytes() == b"external edit"
    assert final._publication(state)[0].exists()


def test_partial_publication_failure_restores_exact_originals(state, monkeypatch):
    root = Path(state["main_root"])
    (root / "lib.v").write_bytes(b"original library")
    files = {"proof_manual_file": "manual.v", "formal_case_lib": "lib.v"}
    backup, _ = final._publication(state)
    write = refresh.atomic_write_bytes
    def fail_second_target(destination, payload, **kwargs):
        if destination == root / "lib.v" and kwargs.get("suffix") == ".generated-publish":
            assert (root / "manual.v").read_bytes() == b"candidate"
            assert backup.is_dir()
            raise PermissionError("target write denied")
        return write(destination, payload, **kwargs)
    monkeypatch.setattr(refresh, "atomic_write_bytes", fail_second_target)
    with pytest.raises(refresh.AnnotationRefreshError, match="target write denied"):
        refresh.publish_file_contents(main_root=root, target_files=files, transaction=backup,
            payloads={"proof_manual_file": b"candidate", "formal_case_lib": b"new library"}, keep_backup=True)
    assert (root / "manual.v").read_bytes() == b"original"
    assert (root / "lib.v").read_bytes() == b"original library"
    assert not backup.exists()


def test_existing_backup_is_never_replaced(state):
    publish(state)
    backup, _ = final._publication(state)
    manifest = (backup / "transaction.json").read_bytes()
    with pytest.raises(refresh.AnnotationRefreshError, match="Recover the existing publication"):
        publish(state)
    assert (backup / "transaction.json").read_bytes() == manifest
    assert (Path(state["main_root"]) / "manual.v").read_bytes() == b"candidate"


@pytest.mark.parametrize("status", ["applied", "invalid"])
def test_missing_backup_does_not_hide_unrecoverable_state(state, status):
    state["final_apply_transaction"]["status"] = status
    assert final._rollback(state) is not None
    assert state["final_apply_transaction"]["status"] == status


def legacy_conflict(state):
    state["final_apply_transaction"]["status"] = "rolled-back"
    state["current_blockers"] = [{"failure_class": "publication-conflict",
                                  "message": "final publication backup is missing"}]


def test_legacy_false_conflict_offers_normal_final_apply(state):
    legacy_conflict(state)
    actions = derive_actions(state)
    assert [action["action"] for action in actions] == ["final-apply"]
    assert "--run" in actions[0]["invocation"]["argv"]
    assert final._rollback(state) is None


@pytest.mark.parametrize("condition", ["applied", "backup", "malformed", "other", "paused", "final-check"])
def test_recovery_does_not_reopen_other_blockers(state, condition):
    legacy_conflict(state)
    if condition == "applied":
        state["final_apply_transaction"]["status"] = "applied"
    elif condition == "backup":
        final._publication(state)[0].mkdir(parents=True)
    elif condition == "malformed":
        state["final_apply_transaction"]["roles"] = ["unexpected"]
    elif condition == "other":
        state["current_blockers"][0]["message"] = "external edit"
    elif condition == "paused":
        state["run_control"]["status"] = "paused"
    else:
        state["phase"] = "final-check"
    assert derive_actions(state) == []


def test_retry_clears_only_resolved_conflict_before_compiling(state, monkeypatch):
    legacy_conflict(state)
    monkeypatch.setattr(final, "load_run", lambda _: state)
    saved = []
    monkeypatch.setattr(final, "_save_state", lambda *_: saved.append(dict(state)))
    class ReachedCandidate(Exception):
        pass
    def context(current):
        assert current["current_blockers"] == []
        assert "final_apply_transaction" not in current
        assert derive_actions(current)[0]["action"] == "final-apply"
        raise ReachedCandidate()
    monkeypatch.setattr(final, "_context", context)
    with pytest.raises(ReachedCandidate):
        final.final_apply(None)
    assert len(saved) == 1
    assert (Path(state["main_root"]) / "manual.v").read_bytes() == b"original"
