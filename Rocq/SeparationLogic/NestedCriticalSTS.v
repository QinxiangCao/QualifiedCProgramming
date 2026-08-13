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
From SimpleC.SL Require Import CriticalSTS.

Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.

Record nested_critical_state {C: critical_STS}: Type :=
  {
    handlers_of_NCS: list Z;
    state_of_NCS: critical_STS_state
  }.

Inductive nested_critical_transition {C: critical_STS}:
  nested_critical_state -> (nat -> Prop) ->
  nested_critical_state -> (nat -> Prop) -> Prop :=
| NCT_enter_critical: forall h l s t,
    (forall n, n >= List.length l -> ~ n ∈ t)%nat ->
    nested_critical_transition
      (Build_nested_critical_state _ l s) t
      (Build_nested_critical_state _ (cons h l) s) (t ∪ [List.length l])
| NCT_exit_critical: forall h l s1 s2 t,
    (forall n, n >= List.length l -> ~ n ∈ t)%nat ->
    critical_STS_transition s1 s2 ->
    nested_critical_transition
      (Build_nested_critical_state _ (cons h l) s1) (t ∪ [List.length l])
      (Build_nested_critical_state _ l s2) t.

Definition nested_critical_STS_to_STS (C: critical_STS): ConAssertion.STS :=
    {|
        ConAssertion.token := nat;
        ConAssertion.STS_state := nested_critical_state;
        ConAssertion.Transition := fun s1 s2 =>
          nested_critical_transition (fst s1) (snd s1) (fst s2) (snd s2);
        ConAssertion.InvownedToken := fun s (n: nat) => (n >= List.length (handlers_of_NCS s))%nat;
    |}.

Module Type nested_critical_STS_def.
  Parameter nc_sts : critical_STS.
End nested_critical_STS_def.

Module Type nested_critical_STS_to_STS_def (NC: nested_critical_STS_def) <: ConAssertion.STS_def.

Definition sts: ConAssertion.STS := nested_critical_STS_to_STS NC.nc_sts.

Definition RTrans (s1 s2: @critical_STS_state NC.nc_sts): Prop :=
  @critical_STS_transition NC.nc_sts s1 s2.

Definition GTrans (s1 s2: @critical_STS_state NC.nc_sts): Prop :=
  @critical_STS_transition NC.nc_sts s1 s2.

End nested_critical_STS_to_STS_def.

Module Type NestedCriticalCSL
              (NC: nested_critical_STS_def)
              (S: nested_critical_STS_to_STS_def NC)
              (R1: ConAssertion.CSL S)
              (Arch : CArchSig)
              (Endian : CEndianSig)
              (R2: DerivedPredSig Arch Endian R1).
Import R1 R2.
Local Open Scope sac.

Definition Critical (hs: list Z) (s: @critical_STS_state NC.nc_sts): expr :=
  “ hs = nil ” &&
    EX s',
    at_states (fun cs => exists s'',
                 cs = Build_nested_critical_state _ nil s'' /\
                 critical_STS_transition s' s'') **
    has_tokens Sets.empty ||
  “ hs <> nil ” &&
    at_states (fun cs => exists hs',
                 cs = Build_nested_critical_state _ (hs' ++ hs) s) **
    has_tokens (fun n => n < List.length hs)%nat.

End NestedCriticalCSL.
