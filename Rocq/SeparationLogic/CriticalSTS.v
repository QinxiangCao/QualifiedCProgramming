Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import String.
Require Import Permutation.

From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From compcert.lib Require Import Integers.

From SimpleC.SL Require Import Mem.
From SimpleC.SL Require Export IntLib ArrayLib.
From AUXLib Require Export ListLib.
From SimpleC.SL Require Export CommonAssertion.
From SimpleC.SL Require Assertion ConAssertion.

Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.

Class critical_STS : Type := {
  critical_STS_state : Type;
  critical_STS_transition : critical_STS_state -> critical_STS_state -> Prop;
}.

Inductive critical_state {C: critical_STS}: Type :=
| inside_state (s: critical_STS_state)
| outside_state (s: critical_STS_state).

Inductive critical_transition {C: critical_STS}:
  critical_state -> (unit -> Prop) ->
  critical_state -> (unit -> Prop) -> Prop :=
| CT_enter_critical: forall s,
    critical_transition
      (outside_state s) Sets.empty
      (inside_state s) Sets.full
| CT_exit_critical: forall s1 s2,
    critical_STS_transition s1 s2 ->
    critical_transition
      (inside_state s1) Sets.full
      (outside_state s2) Sets.empty.

Definition critical_STS_to_STS (C: critical_STS): ConAssertion.STS :=
    {|
        ConAssertion.token := unit;
        ConAssertion.STS_state := critical_state;
        ConAssertion.Transition := fun s1 s2 =>
          critical_transition (fst s1) (snd s1) (fst s2) (snd s2);
        ConAssertion.InvownedToken := fun s =>
          match s with
          | inside_state _ => Sets.empty
          | outside_state _ => Sets.full
          end;
    |}.

Module Type critical_STS_def.
  Parameter c_sts : critical_STS.
End critical_STS_def.

Module Type critical_STS_to_STS_def (C: critical_STS_def) <: ConAssertion.STS_def.

Definition sts: ConAssertion.STS := critical_STS_to_STS C.c_sts.

Definition RTrans (s1 s2: @critical_STS_state C.c_sts): Prop :=
  @critical_STS_transition C.c_sts s1 s2.

Definition GTrans (s1 s2: @critical_STS_state C.c_sts): Prop :=
  @critical_STS_transition C.c_sts s1 s2.

End critical_STS_to_STS_def.

Module Type CriticalCSL
              (C: critical_STS_def)
              (S: critical_STS_to_STS_def C)
              (R1: ConAssertion.CSL S)
              (Arch : CArchSig)
              (Endian : CEndianSig)
              (R2: DerivedPredSig Arch Endian R1).
Import R1 R2.
Local Open Scope sac.

Definition InsideCritical (s: @critical_STS_state C.c_sts): expr :=
  at_states (Sets.singleton (inside_state s)) **
  has_tokens Sets.full.

Definition OutsideCritical (s: @critical_STS_state C.c_sts): expr :=
  EX s',
    “ critical_STS_transition s s' ” &&
    at_states (fun cs => exists s'',
                 cs = outside_state s'' /\
                 critical_STS_transition s' s'').

End CriticalCSL.
