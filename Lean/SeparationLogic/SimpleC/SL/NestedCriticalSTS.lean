import SimpleC.SL.SeparationLogic

namespace SimpleC.SL.NestedCriticalSTS

open SimpleC.SL.CommonAssertion
open SimpleC.SL.ConAssertion
open SimpleC.SL.CriticalSTS

structure nested_critical_state {C : critical_STS} : Type where
  Build_nested_critical_state ::
  handlers_of_NCS : List Int
  state_of_NCS : @critical_STS.critical_STS_state C

export nested_critical_state (Build_nested_critical_state)

inductive nested_critical_transition {C : critical_STS} :
    nested_critical_state (C := C) -> (Nat -> Prop) ->
    nested_critical_state (C := C) -> (Nat -> Prop) -> Prop
  | NCT_enter_critical
      (h : Int) (l : List Int)
      (s : @critical_STS.critical_STS_state C) (t : Nat -> Prop)
      (hfree : forall n, n >= l.length -> ¬t n) :
      nested_critical_transition
        (Build_nested_critical_state l s) t
        (Build_nested_critical_state (h :: l) s)
        (Sets.union t (Sets.singleton l.length))
  | NCT_exit_critical
      (h : Int) (l : List Int)
      (s1 s2 : @critical_STS.critical_STS_state C) (t : Nat -> Prop)
      (hfree : forall n, n >= l.length -> ¬t n)
      (htransition : @critical_STS.critical_STS_transition C s1 s2) :
      nested_critical_transition
        (Build_nested_critical_state (h :: l) s1)
        (Sets.union t (Sets.singleton l.length))
        (Build_nested_critical_state l s2) t

export nested_critical_transition (NCT_enter_critical NCT_exit_critical)

def nested_critical_STS_to_STS (C : critical_STS) : ConAssertion.STS where
  token := Nat
  STS_state := nested_critical_state (C := C)
  Transition := fun s1 s2 =>
    nested_critical_transition s1.1 s1.2 s2.1 s2.2
  InvownedToken := fun s n => n >= s.handlers_of_NCS.length

structure nested_critical_STS_def : Type 1 where
  nc_sts : critical_STS

structure nested_critical_STS_to_STS_def
    (_NC : nested_critical_STS_def) : Type where
  mk ::

namespace nested_critical_STS_to_STS_def

def canonical (NC : nested_critical_STS_def) :
    nested_critical_STS_to_STS_def NC := .mk

def sts {NC : nested_critical_STS_def}
    (_self : nested_critical_STS_to_STS_def NC) : ConAssertion.STS :=
  nested_critical_STS_to_STS NC.nc_sts

def toSTSDef {NC : nested_critical_STS_def}
    (self : nested_critical_STS_to_STS_def NC) : ConAssertion.STS_def :=
  ⟨self.sts⟩

def RTrans {NC : nested_critical_STS_def}
    (_self : nested_critical_STS_to_STS_def NC)
    (s1 s2 : @critical_STS.critical_STS_state NC.nc_sts) : Prop :=
  @critical_STS.critical_STS_transition NC.nc_sts s1 s2

def GTrans {NC : nested_critical_STS_def}
    (_self : nested_critical_STS_to_STS_def NC)
    (s1 s2 : @critical_STS.critical_STS_state NC.nc_sts) : Prop :=
  @critical_STS.critical_STS_transition NC.nc_sts s1 s2

end nested_critical_STS_to_STS_def

structure NestedCriticalCSL
    (NC : nested_critical_STS_def)
    (S : nested_critical_STS_to_STS_def NC)
    (_R1 : ConAssertion.CSL S.toSTSDef)
    (_R2 : DerivedPredSig _R1.toSeparationLogicSig) : Type where
  mk ::

namespace NestedCriticalCSL

def canonical (NC : nested_critical_STS_def)
    (S : nested_critical_STS_to_STS_def NC)
    (R1 : ConAssertion.CSL S.toSTSDef)
    (R2 : DerivedPredSig R1.toSeparationLogicSig) :
    NestedCriticalCSL NC S R1 R2 := .mk

def Critical {NC : nested_critical_STS_def}
    {S : nested_critical_STS_to_STS_def NC}
    {R1 : ConAssertion.CSL S.toSTSDef}
    {R2 : DerivedPredSig R1.toSeparationLogicSig}
    (_self : NestedCriticalCSL NC S R1 R2)
    (hs : List Int)
    (s : @critical_STS.critical_STS_state NC.nc_sts) : R1.expr :=
  R1.andp (R1.coq_prop (hs = []))
    (R1.orp
      (R1.exp (@critical_STS.critical_STS_state NC.nc_sts) fun s' =>
        R1.sepcon
          (R1.at_states fun cs =>
            exists s'',
              cs = Build_nested_critical_state [] s'' ∧
                @critical_STS.critical_STS_transition NC.nc_sts s' s'')
          (R1.has_tokens Sets.empty))
      (R1.andp (R1.coq_prop (hs ≠ []))
        (R1.sepcon
          (R1.at_states fun cs =>
            exists hs', cs = Build_nested_critical_state (hs' ++ hs) s)
          (R1.has_tokens fun (n : Nat) => n < hs.length))))

end NestedCriticalCSL

end SimpleC.SL.NestedCriticalSTS
