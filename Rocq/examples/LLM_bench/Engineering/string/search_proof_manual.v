Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Engineering.string Require Import search_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Lemma proof_of_memchr_entail_wit_1 : memchr_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_memchr_return_wit_1 : memchr_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
  unfold memchr_result.
  right.
  split; [| reflexivity].
  intros k Hk.
  match goal with
  | Hprev : forall k : Z, 0 <= k < i -> Znth k bytes 0 <> c_pre |- _ =>
      apply Hprev; lia
  end.
Qed. 

Lemma proof_of_memchr_return_wit_2 : memchr_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
  unfold memchr_result.
  left.
  exists i.
  repeat split; try lia; auto.
  rewrite sizeof_char.
  lia.
Qed. 

Lemma proof_of_strchr_entail_wit_1 : strchr_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
  apply string_length_nonneg.
Qed. 

Lemma proof_of_strchr_entail_wit_2 : strchr_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_lt : i < SimpleC.StdLib.string_lib.string_length str).
  { eapply SimpleC.StdLib.string_lib.c_string_nonzero_index_lt; eauto. }
  assert (Hi_neq : Znth i str 0 <> c_pre).
  { pose proof (c_string_Znth_inside str i 0 (conj PreH7 Hi_lt)) as Hinside.
    rewrite <- Hinside.
    exact PreH1. }
  unfold store_string.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    intros k Hk.
    destruct (Z.eq_dec k i) as [-> | Hki].
    + exact Hi_neq.
    + apply PreH9; lia.
Qed. 

Lemma proof_of_strchr_return_wit_1 : strchr_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_eq : i = string_length str).
  { eapply c_string_zero_index_eq_length; eauto. }
  subst i.
  unfold store_string.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
  unfold strchr_result.
  right.
  split.
  + intros k Hk.
    apply PreH9; lia.
  + right.
    split; auto.
Qed. 

Lemma proof_of_strchr_return_wit_2 : strchr_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_eq : i = string_length str).
  { eapply c_string_zero_index_eq_length; eauto. }
  subst i.
  unfold store_string.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
  unfold strchr_result.
  right.
  split.
  + intros k Hk.
    apply PreH9; lia.
  + left.
    split; auto.
    rewrite sizeof_char.
    lia.
Qed. 

Lemma proof_of_strchr_return_wit_3 : strchr_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hi_lt : i < string_length str).
  { eapply c_string_nonzero_index_lt; eauto. }
  assert (Hi_eq : Znth i str 0 = c_pre).
  { rewrite <- (c_string_Znth_inside str i 0) by lia.
    exact PreH1. }
  unfold store_string.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
  unfold strchr_result.
  left.
  exists i.
  repeat split; try lia; auto.
  rewrite sizeof_char.
  lia.
Qed. 
