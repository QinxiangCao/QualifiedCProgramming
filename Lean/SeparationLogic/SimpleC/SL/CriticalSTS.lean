import SimpleC.SL.IntLib
import SimpleC.SL.ArrayLib
import SimpleC.SL.ConAssertion

namespace SimpleC.SL.CriticalSTS

open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.ConAssertion

class critical_STS : Type 1 where
  critical_STS_state : Type
  critical_STS_transition : critical_STS_state -> critical_STS_state -> Prop

inductive critical_state {C : critical_STS} : Type
  | inside_state (s : @critical_STS.critical_STS_state C)
  | outside_state (s : @critical_STS.critical_STS_state C)

export critical_state (inside_state outside_state)

inductive critical_transition {C : critical_STS} :
    critical_state (C := C) -> (Unit -> Prop) ->
    critical_state (C := C) -> (Unit -> Prop) -> Prop
  | CT_enter_critical (s : @critical_STS.critical_STS_state C) :
      critical_transition (outside_state s) Sets.empty
        (inside_state s) Sets.full
  | CT_exit_critical (s1 s2 : @critical_STS.critical_STS_state C)
      (htransition : @critical_STS.critical_STS_transition C s1 s2) :
      critical_transition (inside_state s1) Sets.full
        (outside_state s2) Sets.empty

export critical_transition (CT_enter_critical CT_exit_critical)

def critical_STS_to_STS (C : critical_STS) : ConAssertion.STS where
  token := Unit
  STS_state := critical_state (C := C)
  Transition := fun s1 s2 =>
    critical_transition s1.1 s1.2 s2.1 s2.2
  InvownedToken := fun s =>
    match s with
    | inside_state _ => Sets.empty
    | outside_state _ => Sets.full

structure critical_STS_def : Type 1 where
  c_sts : critical_STS

/-- The source module type contains only definitions, so its Lean facade has no
replaceable data. -/
structure critical_STS_to_STS_def (_C : critical_STS_def) : Type where
  mk ::

namespace critical_STS_to_STS_def

def canonical (C : critical_STS_def) : critical_STS_to_STS_def C := .mk

def sts {C : critical_STS_def} (_self : critical_STS_to_STS_def C) :
    ConAssertion.STS :=
  critical_STS_to_STS C.c_sts

def toSTSDef {C : critical_STS_def} (self : critical_STS_to_STS_def C) :
    ConAssertion.STS_def :=
  ⟨self.sts⟩

def RTrans {C : critical_STS_def} (_self : critical_STS_to_STS_def C)
    (s1 s2 : @critical_STS.critical_STS_state C.c_sts) : Prop :=
  @critical_STS.critical_STS_transition C.c_sts s1 s2

def GTrans {C : critical_STS_def} (_self : critical_STS_to_STS_def C)
    (s1 s2 : @critical_STS.critical_STS_state C.c_sts) : Prop :=
  @critical_STS.critical_STS_transition C.c_sts s1 s2

end critical_STS_to_STS_def

structure CriticalCSL
    (C : critical_STS_def)
    (S : critical_STS_to_STS_def C)
    (_R1 : ConAssertion.CSL S.toSTSDef)
    (_R2 : DerivedPredSig _R1.toSeparationLogicSig) : Type where
  mk ::

namespace CriticalCSL

def canonical (C : critical_STS_def)
    (S : critical_STS_to_STS_def C)
    (R1 : ConAssertion.CSL S.toSTSDef)
    (R2 : DerivedPredSig R1.toSeparationLogicSig) :
    CriticalCSL C S R1 R2 := .mk

def InsideCritical {C : critical_STS_def}
    {S : critical_STS_to_STS_def C}
    {R1 : ConAssertion.CSL S.toSTSDef}
    {R2 : DerivedPredSig R1.toSeparationLogicSig}
    (_self : CriticalCSL C S R1 R2)
    (s : @critical_STS.critical_STS_state C.c_sts) : R1.expr :=
  R1.sepcon
    (R1.at_states (Sets.singleton (inside_state s)))
    (R1.has_tokens Sets.full)

def OutsideCritical {C : critical_STS_def}
    {S : critical_STS_to_STS_def C}
    {R1 : ConAssertion.CSL S.toSTSDef}
    {R2 : DerivedPredSig R1.toSeparationLogicSig}
    (_self : CriticalCSL C S R1 R2)
    (s : @critical_STS.critical_STS_state C.c_sts) : R1.expr :=
  R1.exp (@critical_STS.critical_STS_state C.c_sts) fun s' =>
    R1.andp
      (R1.coq_prop (@critical_STS.critical_STS_transition C.c_sts s s'))
      (R1.at_states fun cs =>
        exists s'',
          cs = outside_state s'' ∧
            @critical_STS.critical_STS_transition C.c_sts s' s'')

end CriticalCSL

end SimpleC.SL.CriticalSTS
