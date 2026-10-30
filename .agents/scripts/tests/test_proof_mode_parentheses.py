"""Keep valid historical Coq tactic parentheses without relaxing route checks."""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "vc-proving"))
from proof_manual_utils import proof_mode_errors


@pytest.mark.parametrize("mode,opening", [
    ("LLM_pre_process", "LLM_pre_process ltac:(int_auto)."),
    ("LLM_pre_process", "left.\n LLM_pre_process ltac:(int_auto)."),
    ("LLM_pre_process", "left.\n (LLM_pre_process ltac:(int_auto))."),
    ("LLM_pre_process", "(LLM_pre_process ltac:(int_auto)); Exists 0."),
    ("LLM_pre_process", "((LLM_pre_process ltac:(int_auto))); Exists 0."),
    ("LLM_pre_process", "( (* original tactic *) LLM_pre_process ltac:(int_auto))."),
    ("aggressive_pre_process", "aggressive_pre_process."),
    ("aggressive_pre_process", "(aggressive_pre_process); Goal_apply old_split."),
])
def test_parenthesized_opening_preserves_original_route(mode, opening):
    block = f"Lemma p : True.\nProof.\n  {opening}\nQed.\n"
    assert proof_mode_errors(block, mode) == []


@pytest.mark.parametrize("opening", [
    "idtac; LLM_pre_process ltac:(int_auto).",
    "right. LLM_pre_process ltac:(int_auto).",
    "left. left. LLM_pre_process ltac:(int_auto).",
    "left; LLM_pre_process ltac:(int_auto).",
    "try (LLM_pre_process ltac:(int_auto)).",
    "(* LLM_pre_process *) exact I.",
    'idtac "LLM_pre_process"; exact I.',
    "(aggressive_pre_process).",
    "(LLM_pre_process ltac:(int_auto)); aggressive_pre_process.",
])
def test_parentheses_cannot_hide_wrong_opening_or_mixed_route(opening):
    block = f"Lemma p : True.\nProof.\n  {opening}\nQed.\n"
    assert proof_mode_errors(block, "LLM_pre_process")


def test_left_prefix_does_not_expand_aggressive_route():
    block = "Lemma p : True.\nProof.\nleft. aggressive_pre_process.\nQed.\n"
    assert proof_mode_errors(block, "aggressive_pre_process")
