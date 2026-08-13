import SimpleC.SL.NestedCriticalSTS
import Lean.Util.CollectAxioms

namespace NestedCriticalSTSTests

open SimpleC.SL.CommonAssertion
open SimpleC.SL.ConAssertion
open SimpleC.SL.CriticalSTS
open SimpleC.SL.NestedCriticalSTS
open Lean Elab Command

private def resolveApiDecls (ids : Array Syntax) : CommandElabM (Array Name) :=
  ids.mapM fun id => liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def apiTypeHash (names : Array Name) : CommandElabM UInt64 := do
  let env <- getEnv
  let mut result := hash names.size
  for name in names do
    let some info := env.find? name
      | throwError "NestedCriticalSTS API declaration '{name}' is missing"
    result := mixHash result (mixHash (hash name) (hash info.type))
  pure result

syntax (name := checkNestedCriticalSTSContract)
  "#check_nested_critical_sts_contract " "[" ident,* "]" " => " num : command

elab_rules : command
  | `(#check_nested_critical_sts_contract [$ids:ident,*] => $expected:num) => do
      let names <- resolveApiDecls ids
      let some expected := expected.raw.isNatLit?
        | throwErrorAt expected "expected a natural-number API type hash"
      let actual <- apiTypeHash names
      unless actual = expected.toUInt64 do
        throwError "NestedCriticalSTS API type hash changed: expected {expected}, got {actual}"
      let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
      for name in names do
        for axiomName in (← collectAxioms name) do
          unless allowedAxioms.contains axiomName do
            throwError "NestedCriticalSTS declaration '{name}' depends on disallowed axiom '{axiomName}'"
      logInfo m!"NestedCriticalSTS API contract verified for {names.size} declarations"

#check nested_critical_state
#check Build_nested_critical_state
#check nested_critical_state.handlers_of_NCS
#check nested_critical_state.state_of_NCS
#check nested_critical_transition
#check NCT_enter_critical
#check NCT_exit_critical
#check nested_critical_STS_to_STS
#check nested_critical_STS_def
#check nested_critical_STS_def.nc_sts
#check nested_critical_STS_to_STS_def
#check nested_critical_STS_to_STS_def.canonical
#check nested_critical_STS_to_STS_def.sts
#check nested_critical_STS_to_STS_def.toSTSDef
#check nested_critical_STS_to_STS_def.RTrans
#check nested_critical_STS_to_STS_def.GTrans
#check NestedCriticalCSL
#check NestedCriticalCSL.canonical
#check NestedCriticalCSL.Critical

#check_nested_critical_sts_contract [
  nested_critical_state,
  Build_nested_critical_state,
  nested_critical_state.handlers_of_NCS,
  nested_critical_state.state_of_NCS,
  nested_critical_transition,
  NCT_enter_critical,
  NCT_exit_critical,
  nested_critical_STS_to_STS,
  nested_critical_STS_def,
  nested_critical_STS_def.nc_sts,
  nested_critical_STS_to_STS_def,
  nested_critical_STS_to_STS_def.canonical,
  nested_critical_STS_to_STS_def.sts,
  nested_critical_STS_to_STS_def.toSTSDef,
  nested_critical_STS_to_STS_def.RTrans,
  nested_critical_STS_to_STS_def.GTrans,
  NestedCriticalCSL,
  NestedCriticalCSL.canonical,
  NestedCriticalCSL.Critical
] => 12796742306923022250

abbrev CounterSTS : critical_STS where
  critical_STS_state := Nat
  critical_STS_transition := fun s1 s2 => s2 = s1 + 1

example : nested_critical_state (C := CounterSTS) :=
  Build_nested_critical_state [10, 20] (3 : Nat)

example : @nested_critical_transition CounterSTS
    (Build_nested_critical_state [10, 20] (3 : Nat)) Sets.empty
    (Build_nested_critical_state [7, 10, 20] (3 : Nat))
    (Sets.union Sets.empty (Sets.singleton 2)) := by
  apply NCT_enter_critical
  intro n _ hn
  exact hn.elim

example : @nested_critical_transition CounterSTS
    (Build_nested_critical_state [7, 10, 20] (3 : Nat))
    (Sets.union Sets.empty (Sets.singleton 2))
    (Build_nested_critical_state [10, 20] (4 : Nat)) Sets.empty := by
  apply NCT_exit_critical
  · intro n _ hn
    exact hn.elim
  · rfl

example : ¬(forall n, n >= [10, 20].length ->
    ¬Sets.singleton 2 n) := by
  intro h
  exact h 2 (by decide) rfl

example : (nested_critical_STS_to_STS CounterSTS).token = Nat := rfl
example : (nested_critical_STS_to_STS CounterSTS).STS_state =
    nested_critical_state (C := CounterSTS) := rfl
example : ¬(nested_critical_STS_to_STS CounterSTS).InvownedToken
    (Build_nested_critical_state [10, 20] (3 : Nat)) (1 : Nat) := by
  change ¬(1 >= 2)
  omega
example : (nested_critical_STS_to_STS CounterSTS).InvownedToken
    (Build_nested_critical_state [10, 20] (3 : Nat)) (2 : Nat) := by
  change 2 >= 2
  omega

abbrev CounterDef : nested_critical_STS_def := ⟨CounterSTS⟩
abbrev CounterFacade : nested_critical_STS_to_STS_def CounterDef :=
  nested_critical_STS_to_STS_def.canonical CounterDef

example : CounterFacade.sts = nested_critical_STS_to_STS CounterSTS := rfl
example : CounterFacade.toSTSDef.sts = nested_critical_STS_to_STS CounterSTS := rfl
example (s1 s2 : Nat) : CounterFacade.RTrans s1 s2 = (s2 = s1 + 1) := rfl
example (s1 s2 : Nat) : CounterFacade.GTrans s1 s2 = (s2 = s1 + 1) := rfl

def CounterLogic : CSL CounterFacade.toSTSDef :=
  CSL.canonical CounterFacade.toSTSDef
def CounterDerived : DerivedPredSig CounterLogic.toSeparationLogicSig :=
  DerivedPredSig.canonical CounterLogic.toSeparationLogicSig
def CounterNested :
    NestedCriticalCSL CounterDef CounterFacade CounterLogic CounterDerived :=
  NestedCriticalCSL.canonical CounterDef CounterFacade CounterLogic CounterDerived

example (s : Nat) : CounterNested.Critical [] s =
    CounterLogic.andp (CounterLogic.coq_prop ([] = ([] : List Int)))
      (CounterLogic.orp
        (CounterLogic.exp Nat fun s' =>
          CounterLogic.sepcon
            (CounterLogic.at_states fun cs =>
              exists s'',
                cs = Build_nested_critical_state [] s'' ∧ s'' = s' + 1)
            (CounterLogic.has_tokens Sets.empty))
        (CounterLogic.andp (CounterLogic.coq_prop (([] : List Int) ≠ []))
          (CounterLogic.sepcon
            (CounterLogic.at_states fun cs =>
              exists hs', cs = Build_nested_critical_state (hs' ++ []) s)
            (CounterLogic.has_tokens fun (n : Nat) => n < (0 : Nat))))) := rfl

example (s : Nat) (hs : List Int) : CounterNested.Critical hs s =
    CounterLogic.andp (CounterLogic.coq_prop (hs = []))
      (CounterLogic.orp
        (CounterLogic.exp Nat fun s' =>
          CounterLogic.sepcon
            (CounterLogic.at_states fun cs =>
              exists s'',
                cs = Build_nested_critical_state [] s'' ∧ s'' = s' + 1)
            (CounterLogic.has_tokens Sets.empty))
        (CounterLogic.andp (CounterLogic.coq_prop (hs ≠ []))
          (CounterLogic.sepcon
            (CounterLogic.at_states fun cs =>
              exists hs', cs = Build_nested_critical_state (hs' ++ hs) s)
            (CounterLogic.has_tokens fun (n : Nat) => n < hs.length)))) := rfl

-- Reproduce the module assembly used by examples/nested_critical_sll_lib.v.
abbrev sll_CS : critical_STS where
  critical_STS_state := List Int
  critical_STS_transition := fun _ _ => (1 : Int) = 1

abbrev NC_STS_sll : nested_critical_STS_def := ⟨sll_CS⟩
abbrev NC_STS_sll_facade : nested_critical_STS_to_STS_def NC_STS_sll :=
  nested_critical_STS_to_STS_def.canonical NC_STS_sll
def sll_NC_CSL : CSL NC_STS_sll_facade.toSTSDef :=
  CSL.canonical NC_STS_sll_facade.toSTSDef
abbrev sll_NC_Rules : SeparationLogicSig :=
  sll_NC_CSL.toSeparationLogicSig
def sll_NC_Derived : DerivedPredSig sll_NC_Rules :=
  DerivedPredSig.canonical sll_NC_Rules
def sll_NC_Nested :
    NestedCriticalCSL NC_STS_sll NC_STS_sll_facade sll_NC_CSL sll_NC_Derived :=
  NestedCriticalCSL.canonical
    NC_STS_sll NC_STS_sll_facade sll_NC_CSL sll_NC_Derived

namespace sll_NC_Rules

abbrev nc_sts : critical_STS := NC_STS_sll.nc_sts
abbrev sts : STS := NC_STS_sll_facade.sts
abbrev RTrans := NC_STS_sll_facade.RTrans
abbrev GTrans := NC_STS_sll_facade.GTrans
abbrev Critical := sll_NC_Nested.Critical

end sll_NC_Rules

#check sll_NC_Rules.nc_sts
#check sll_NC_Rules.sts
#check sll_NC_Rules.RTrans
#check sll_NC_Rules.GTrans
#check sll_NC_Rules.Critical
#check sll_NC_Rules.store_int
#check sll_NC_Rules.IntArray

example : sll_NC_Rules.sts = nested_critical_STS_to_STS sll_CS := rfl
example (l1 l2 : List Int) : sll_NC_Rules.RTrans l1 l2 := rfl
example (l1 l2 : List Int) : sll_NC_Rules.GTrans l1 l2 := rfl
example (p v : Int) :
    sll_NC_Rules.store_int p v =
      DerivedPredSig.store_int sll_NC_Rules p v := rfl
example : sll_NC_Rules.IntArray.elementStore =
    SimpleC.SL.ArrayLib.StoreIntAsElement
      sll_NC_Rules sll_NC_Rules.derivedPredSig sll_NC_Rules.storeLibSig := rfl
example (hs s : List Int) :
    sll_NC_Rules.Critical hs s = sll_NC_Nested.Critical hs s := rfl

abbrev ProductSTS : critical_STS where
  critical_STS_state := Int × List Int
  critical_STS_transition := Eq

abbrev TripleShapeSTS : critical_STS where
  critical_STS_state := List Int × (Int × List Int)
  critical_STS_transition := Eq

example : nested_critical_state (C := ProductSTS) :=
  Build_nested_critical_state [1] (0, [])
example : nested_critical_state (C := TripleShapeSTS) :=
  Build_nested_critical_state [1, 2] ([], 0, [])

#print axioms SimpleC.SL.NestedCriticalSTS.nested_critical_STS_to_STS
#print axioms SimpleC.SL.NestedCriticalSTS.NestedCriticalCSL.Critical

end NestedCriticalSTSTests
