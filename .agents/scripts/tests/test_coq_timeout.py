"""Long checks may extend the shared budget without losing explicit limits."""
import sys
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(SCRIPTS / name) for name in ("verification-orchestrator", "vc-proving")]

import coq_tooling_common


def test_shared_deadline_default_and_override(monkeypatch):
    monkeypatch.setattr(coq_tooling_common.time, "monotonic", lambda: 100)
    monkeypatch.delenv("QCP_COQ_TIMEOUT_SECONDS", raising=False)
    assert coq_tooling_common.command_deadline(None) == 1900
    assert coq_tooling_common.command_deadline(7200) == 1900
    monkeypatch.setenv("QCP_COQ_TIMEOUT_SECONDS", "3600")
    assert coq_tooling_common.command_deadline(None) == 3700
    assert coq_tooling_common.command_deadline(7200) == 3700
    assert coq_tooling_common.command_deadline(30) == 130


@pytest.mark.parametrize("value", ["invalid", "nan", "inf", "-1", "0"])
def test_invalid_shared_budget_is_rejected(monkeypatch, value):
    monkeypatch.setenv("QCP_COQ_TIMEOUT_SECONDS", value)
    with pytest.raises(ValueError, match="QCP_COQ_TIMEOUT_SECONDS"):
        coq_tooling_common.command_deadline(None)
