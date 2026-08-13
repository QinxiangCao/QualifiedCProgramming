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
From SimpleC.EE.Applications_human.minigmp Require Import gmp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minigmp Require Import GmpAux GmpNumber.
Import Aux.
Local Open Scope sac.

Lemma proof_of_mpz_clear_return_wit_2_split_goal_spatial :
  mpz_clear_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst cap_2.
  assert (Hsize_abs: Zabs size_2 = 0) by lia.
  rewrite Hsize_abs.
  rewrite UIntArray.undef_seg_empty.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros data.
  assert (data = nil).
  { apply Zlength_nil_inv. lia. }
  subst data.
  rewrite UIntArray.full_empty.
  cancel.
  normalize.
  cancel.
  Intros_p Hlen_nil.
  cancel.
Qed.

Lemma proof_of_mpz_clear_return_wit_2 : mpz_clear_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_clear_return_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1_split_goal_spatial :
  mpz_realloc_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hold_zero: old = 0) by lia.
  subst old.
  change (Zabs 0) with 0 in *.
  rewrite PreH3.
  sep_apply (UIntArray.undef_full_to_undef_seg retval); try lia.
  unfold mpd_store_Z_compact, mpd_store_list.
  Intros l.
  assert (l = nil).
  { apply Zlength_nil_inv. lia. }
  subst l.
  destruct H as [Hval [Hlast Hbound]].
  simpl in Hval.
  assert (Hn_abs_zero: Zabs n = 0) by lia.
  rewrite Hn_abs_zero in *.
  rewrite UIntArray.full_empty.
  rewrite PreH10.
  rewrite UIntArray.undef_seg_empty.
  Exists (@nil Z).
  rewrite UIntArray.full_empty.
  try rewrite UIntArray.undef_seg_empty.
  split_pure_spatial.
  - cancel.
    normalize.
    Intros.
    cancel.
  - repeat split_pures; dump_pre_spatial; simpl; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_realloc_return_wit_1 : mpz_realloc_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_realloc_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_realloc_return_wit_3 : mpz_realloc_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_return_wit_4 : mpz_realloc_return_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_2_pure : mpz_realloc_partial_solve_wit_2_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_3_pure : mpz_realloc_partial_solve_wit_3_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_4_pure : mpz_realloc_partial_solve_wit_4_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_realloc_partial_solve_wit_5_pure : mpz_realloc_partial_solve_wit_5_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_split_goal_1 :
  mrz_realloc_if_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_split_goal_2 :
  mrz_realloc_if_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1_split_goal_spatial :
  mrz_realloc_if_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (Z.max (Z.max n_pre 1) cap) with cap by lia.
  cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_1 : mrz_realloc_if_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_1_split_goal_1.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_split_goal_1 :
  mrz_realloc_if_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_split_goal_2 :
  mrz_realloc_if_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2_split_goal_spatial :
  mrz_realloc_if_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  replace (Z.max (Z.max n_pre 1) cap) with (Z.max n_pre 1) by lia.
  cancel.
Qed.

Lemma proof_of_mrz_realloc_if_return_wit_2 : mrz_realloc_if_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_2_split_goal_1.
  - Goal_apply proof_of_mrz_realloc_if_return_wit_2_split_goal_2.
Qed.

Lemma proof_of_mpz_sgn_return_wit_1_split_goal_1 :
  mpz_sgn_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold same_sign in PreH3.
  destruct PreH3 as [[_ Hsize_nonneg] | [Hn_neg _]]; [lia | exact Hn_neg].
Qed.

Lemma proof_of_mpz_sgn_return_wit_1 : mpz_sgn_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_sgn_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpz_sgn_return_wit_2 : mpz_sgn_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z.
  Exists ptr size cap.
  replace (Zabs size) with size by lia.
  subst size.
  prop_apply (mpd_store_Z_compact_zero); try lia.
  Intros.
  assert (n = 0) by lia.
  replace (Zabs n) with n by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_mpz_sgn_return_wit_3 : mpz_sgn_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_Z.
  Exists ptr size cap.
  replace (Zabs size) with size by lia.
  prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr
    (Zabs n) size ltac:(lia)).
  Intros.
  assert (Hn_pos: n > 0).
  { unfold same_sign in PreH3.
    match goal with
    | [ Habs_pos : Zabs n > 0 |- _ ] =>
        destruct PreH3 as [[Hn_nonneg _] | [_ Hsize_neg]]; lia
    end. }
  replace (Zabs n) with n by lia.
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.
