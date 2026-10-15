"""Generation must keep long case identifiers out of native staging paths."""
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(SCRIPTS / name) for name in ("verification-orchestrator", "vc-proving")]

import controller_tools


def test_failed_generation_uses_short_staging_and_preserves_canonical(tmp_path, monkeypatch):
    root = tmp_path / "repo"
    report = root / "reports" / ("long_case_" * 8) / "annotation-attempts/annotation-attempt1"
    report.mkdir(parents=True)
    canonical = root / "manual.v"
    canonical.write_bytes(b"existing proof\n")
    target = {"c_file": "case.c", "formal_case_lib": "lib.v"}
    state = {"main_root": str(root), "run_root": str(root / "run"), "target_files": target}
    monkeypatch.setattr(controller_tools, "attempt_paths", lambda *_: {"directory": report})
    monkeypatch.setattr(controller_tools, "recover_interrupted_refresh", lambda **_: None)
    monkeypatch.setattr(controller_tools, "generated_output_contents", lambda *_: {"manual": canonical.read_bytes()})
    monkeypatch.setattr(controller_tools, "file_contents", lambda *_: {})
    monkeypatch.setattr(controller_tools, "symexec_profile_for_state", lambda _: {
        "name": "standard", "timeout_seconds": 900, "heartbeat_seconds": 30, "poll_interval_seconds": 1})
    seen = []

    def generate(**kwargs):
        output = kwargs["output_root"]
        assert output.parent == root / "reports"
        assert len(str(output)) < len(str(report))
        (output / "incomplete.v").write_text("incomplete output", encoding="utf-8")
        seen.append(output)
        return {"status": "failed", "returncode": 1}

    monkeypatch.setattr(controller_tools, "run_symexec", generate)
    result = controller_tools.refresh_annotation(state, {})
    assert result["status"] == "failed"
    assert canonical.read_bytes() == b"existing proof\n"
    assert len(seen) == 1 and not seen[0].exists()
