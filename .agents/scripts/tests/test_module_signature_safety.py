"""Module signature fields are obligations, not global admitted implementations."""

import sys
from pathlib import Path

import pytest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(SCRIPTS / name) for name in ("verification-orchestrator", "vc-proving")]

from proof_manual_utils import (
    lib_contract_errors,
    top_level_commands,
    unsafe_assumption_declarations,
    unsafe_commands,
)


def findings(source):
    return unsafe_commands(top_level_commands(source, include_proof_commands=True))


@pytest.mark.parametrize("source", [
    "Module Type S. Parameter t : Type. Parameters x y : t. End S.",
    "Module Type S. Section T. Variable A : Type. Parameter x : A. End T. End S.",
    "Module Type S. Module Type T. Parameter t : Type. End T. Parameter x : nat. End S.",
    "Module Outer. Module Type S. Parameter t : Type. End S. End Outer.",
    "Module Type P. Parameter t : Type. End P. "
    "Module Type S (X : P). Parameter t : X.t. End S.",
    "Time Module Type S. #[local] Parameter t : Type. End S.",
    "Module Type (* nested (* comment *) *) S. Parameter t : Type. End S.",
    "Section S. Variable A : Type. Module M. End M. End S.",
    "Module Type S. Parameter t : Type. End S. Module M <: S. Definition t := nat. End M.",
    "Module Type S. Definition text := \"Module Type Fake. End S.\". Parameter x : nat. End S.",
    "Module Type P. Parameter t : Type. End P. "
    "Module Type S (X : P with Definition t := nat). Parameter y : nat. End S.",
    "Module Type S. Module Type Alias := Other. Parameter x : nat. End S.",
])
def test_signature_parameters_are_implementation_obligations(source):
    assert findings(source) == []
    assert unsafe_assumption_declarations(source) == []
    assert lib_contract_errors(source) == []


@pytest.mark.parametrize("source", [
    "Parameter bad : False.",
    "Section S. Parameter bad : False. End S.",
    "Module M. Parameter bad : False. End M.",
    "Module Import M. Parameter bad : False. End M.",
    "Module Export M. Parameter bad : False. End M.",
    "Module M (X : S). Parameter bad : False. End M.",
    "Module Type S. Parameter t : Type. End S. Parameter bad : False.",
    "Module Type S := Existing. Parameter bad : False.",
    "Module M := F X. Parameter bad : False.",
    "Module Type S. Module M. Parameter bad : False. End M. End S.",
    "Module M. Module Type S. Parameter t : Type. End S. Parameter bad : False. End M.",
    "Module Type S. Lemma demo : True. Proof. Parameter bad : False. exact I. Qed. End S.",
    "(* Module Type S. *) Parameter bad : False.",
    'Definition text := "Module Type S.". Parameter bad : False.',
    "Module Type S. End Wrong. Parameter bad : False.",
])
def test_no_parameter_exemption_leaks_to_implementations(source):
    assert any(item["kind"] == "Parameter" for item in findings(source))
    assert any(item["kind"] == "Parameter" for item in unsafe_assumption_declarations(source))
    assert any("assumption declaration Parameter" in error for error in lib_contract_errors(source))


@pytest.mark.parametrize("unsafe", [
    "Axiom bad : False.",
    "Axioms bad : False.",
    "Conjecture bad : False.",
    "Declare Module M : S.",
    "Declare Module Type T.",
    "Unset Guard Checking.",
    "#[bypass_check(guard)] Definition bad := 0.",
    "Fail Parameter bad : False.",
    "Succeed Parameter bad : False.",
    "Lemma demo : True. Proof. Admitted.",
])
def test_signature_scope_does_not_disable_other_safety_checks(unsafe):
    assert lib_contract_errors(f"Module Type S. {unsafe} End S.")


def test_abstract_module_cannot_turn_signature_obligations_into_global_axioms():
    source = "Module Type S. Parameter bad : False. End S. Declare Module M : S."
    assert any(item.get("abstract_module") for item in findings(source))
    assert any(item.get("abstract_module") for item in unsafe_assumption_declarations(source))


def test_nested_same_name_section_does_not_end_module_signature():
    source = "Module Type S. Section S. End S. Parameter good : Type. End S. Parameter bad : False."
    assert [(x["kind"], x["name"]) for x in findings(source)] == [("Parameter", "bad")]


def test_mismatched_end_fails_closed():
    assert any("mismatched scope" in error for error in lib_contract_errors("Module Type S. End X."))


def test_complete_stream_and_preparsed_lib_checks_agree():
    source = "Module Type S. Parameter t : Type. End S. Module M <: S. Parameter t : Type. End M."
    commands = top_level_commands(source, include_proof_commands=True)
    assert lib_contract_errors(source) == lib_contract_errors(source, commands=commands)


def test_bypass_attributes_on_scope_headers_are_not_swallowed():
    assert lib_contract_errors("#[bypass_check(guard)] Module Type S. Parameter t : Type. End S.")
