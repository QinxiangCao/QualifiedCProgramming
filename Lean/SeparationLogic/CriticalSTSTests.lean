import SimpleC.SL.CriticalSTS
import Lean.Util.CollectAxioms

namespace CriticalSTSTests

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.ConAssertion
open SimpleC.SL.CriticalSTS

open Lean Elab Command

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env <- getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "CriticalSTS API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkCriticalSTSContract)
  "#check_critical_sts_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_critical_sts_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "CriticalSTS API type hash changed: expected {expected}, got {actual}"
      let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "CriticalSTS declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"CriticalSTS API contract verified for {names.size} declarations"

#check critical_STS
#check critical_STS.critical_STS_state
#check critical_STS.critical_STS_transition
#check critical_state
#check inside_state
#check outside_state
#check critical_transition
#check CT_enter_critical
#check CT_exit_critical
#check critical_STS_to_STS
#check critical_STS_def
#check critical_STS_def.c_sts
#check critical_STS_to_STS_def
#check critical_STS_to_STS_def.canonical
#check critical_STS_to_STS_def.sts
#check critical_STS_to_STS_def.toSTSDef
#check critical_STS_to_STS_def.RTrans
#check critical_STS_to_STS_def.GTrans
#check CriticalCSL
#check CriticalCSL.canonical
#check CriticalCSL.InsideCritical
#check CriticalCSL.OutsideCritical

#check_critical_sts_contract [
  critical_STS,
  critical_STS.critical_STS_state,
  critical_STS.critical_STS_transition,
  critical_state,
  inside_state,
  outside_state,
  critical_transition,
  CT_enter_critical,
  CT_exit_critical,
  critical_STS_to_STS,
  critical_STS_def,
  critical_STS_def.c_sts,
  critical_STS_to_STS_def,
  critical_STS_to_STS_def.canonical,
  critical_STS_to_STS_def.sts,
  critical_STS_to_STS_def.toSTSDef,
  critical_STS_to_STS_def.RTrans,
  critical_STS_to_STS_def.GTrans,
  CriticalCSL,
  CriticalCSL.canonical,
  CriticalCSL.InsideCritical,
  CriticalCSL.OutsideCritical
] => 7379886619862721357

abbrev CounterSTS : critical_STS where
  critical_STS_state := Nat
  critical_STS_transition := fun s1 s2 => s2 = s1 + 1

section TypeclassIdentity

local instance : critical_STS := CounterSTS

example : critical_STS := inferInstance
example : (inferInstance : critical_STS).critical_STS_state = Nat := rfl

end TypeclassIdentity

example : CounterSTS.critical_STS_state = Nat := rfl
example (s1 s2 : Nat) :
    CounterSTS.critical_STS_transition s1 s2 = (s2 = s1 + 1) := rfl

example : critical_state (C := CounterSTS) :=
  inside_state (C := CounterSTS) (0 : Nat)
example : critical_state (C := CounterSTS) :=
  outside_state (C := CounterSTS) (0 : Nat)

example : @critical_transition CounterSTS
    (outside_state (C := CounterSTS) (3 : Nat)) Sets.empty
    (inside_state (C := CounterSTS) (3 : Nat)) Sets.full :=
  @CT_enter_critical CounterSTS (3 : Nat)

example : @critical_transition CounterSTS
    (inside_state (C := CounterSTS) (3 : Nat)) Sets.full
    (outside_state (C := CounterSTS) (4 : Nat)) Sets.empty :=
  @CT_exit_critical CounterSTS (3 : Nat) (4 : Nat) rfl

example : (critical_STS_to_STS CounterSTS).token = Unit := rfl
example : (critical_STS_to_STS CounterSTS).STS_state =
    critical_state (C := CounterSTS) := rfl
example : (critical_STS_to_STS CounterSTS).Transition
    (outside_state (C := CounterSTS) (3 : Nat), Sets.empty)
    (inside_state (C := CounterSTS) (3 : Nat), Sets.full) :=
  @CT_enter_critical CounterSTS (3 : Nat)
example : (critical_STS_to_STS CounterSTS).InvownedToken
    (inside_state (C := CounterSTS) (3 : Nat)) =
    Sets.empty := rfl
example : (critical_STS_to_STS CounterSTS).InvownedToken
    (outside_state (C := CounterSTS) (3 : Nat)) =
    Sets.full := rfl

abbrev CounterDef : critical_STS_def := ⟨CounterSTS⟩
abbrev CounterFacade : critical_STS_to_STS_def CounterDef :=
  critical_STS_to_STS_def.canonical CounterDef

example : CounterFacade.sts = critical_STS_to_STS CounterSTS := rfl
example : CounterFacade.toSTSDef.sts = critical_STS_to_STS CounterSTS := rfl
example (s1 s2 : Nat) : CounterFacade.RTrans s1 s2 = (s2 = s1 + 1) := rfl
example (s1 s2 : Nat) : CounterFacade.GTrans s1 s2 = (s2 = s1 + 1) := rfl

def CounterLogic : CSL CounterFacade.toSTSDef :=
  CSL.canonical CounterFacade.toSTSDef
def CounterDerived : DerivedPredSig CounterLogic.toSeparationLogicSig :=
  DerivedPredSig.canonical CounterLogic.toSeparationLogicSig
def CounterCritical : CriticalCSL CounterDef CounterFacade CounterLogic CounterDerived :=
  CriticalCSL.canonical CounterDef CounterFacade CounterLogic CounterDerived

example (s : Nat) : CounterCritical.InsideCritical s =
    CounterLogic.sepcon
      (CounterLogic.at_states
        (Sets.singleton (inside_state (C := CounterSTS) s)))
      (CounterLogic.has_tokens Sets.full) := rfl

example (s : Nat) : CounterCritical.OutsideCritical s =
    CounterLogic.exp Nat fun s' =>
      CounterLogic.andp (CounterLogic.coq_prop (s' = s + 1))
        (CounterLogic.at_states fun cs =>
          exists s'',
            cs = outside_state (C := CounterSTS) s'' ∧ s'' = s' + 1) := rfl

#print axioms SimpleC.SL.CriticalSTS.critical_STS_to_STS
#print axioms SimpleC.SL.CriticalSTS.CriticalCSL.InsideCritical
#print axioms SimpleC.SL.CriticalSTS.CriticalCSL.OutsideCritical

end CriticalSTSTests
