Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma gmp_strategy20_correctness : gmp_strategy20.
Proof.
  unfold gmp_strategy20.
  pre_process_default.
  rewrite <- logic_equiv_coq_prop_or.
  LLM_pre_process ltac:(lia).
  destruct H as [Hpq | Hqp]; subst.
  -
    split_pure_spatial.
    + Intros_r l2.
      apply_sepcon_adjoint.
      Intros_p Hl.
      subst l2.
      cancel.
    + dump_pre_spatial; left; reflexivity.
  -
    split_pure_spatial.
    + Intros_r l2.
      apply_sepcon_adjoint.
      Intros_p Hl.
      subst l2.
      cancel.
    + dump_pre_spatial; left; reflexivity.
Qed.

Lemma gmp_strategy1_correctness : gmp_strategy1.
Proof.
  pre_process_default.
  unfold mpd_store_Z_compact, mpd_store_Z, is_compact_Z.
  Intros data.
  LLM_pre_process ltac:(lia).
  split_pure_spatial.
  - Intros_r v.
    apply_sepcon_adjoint.
    Intros_p Hv.
    subst v.
    Exists data.
    split_pure_spatial.
    + cancel.
    + split_pures.
      * dump_pre_spatial.
        destruct H0 as [Hval [_ Hbound]].
        split; assumption.
      * dump_pre_spatial.
        rewrite <- H.
        exact H1.
  - dump_pre_spatial.
    refine (ex_intro _ data _).
    destruct H0 as [? [? ?]].
    split; [assumption | split; [symmetry; assumption | tauto]].
Qed.

Lemma gmp_strategy2_correctness : gmp_strategy2.
Proof.
  pre_process_default.
  unfold store_Z.
  Intros ptr size cap.
  Exists ptr size cap.
  LLM_pre_process ltac:(lia).
  split_pure_spatial.
  - cancel (&( x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size).
    cancel (&( x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap).
    cancel (&( x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr).
    cancel (mpd_store_Z_compact UINT_MOD ptr (Zabs n) (Zabs size)).
    cancel (UIntArray.undef_seg ptr (Zabs size) cap).
    Intros_r y.
    apply_sepcon_adjoint.
    normalize.
    Split.
    + Split.
      * Left; Left.
        cancel.
      * Left; Right.
        cancel.
    + Right.
      cancel.
  - split_pures.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
Qed.

Lemma gmp_strategy3_correctness : gmp_strategy3.
Proof.
  pre_process_default.
  cancel.
  Intros_r size n cap ptr.
  apply_sepcon_adjoint.
  Intros_p Hz.
  Intros_p Hsign.
  unfold store_Z.
  Exists ptr size cap.
  LLM_pre_process ltac:(lia).
Qed.

Lemma gmp_strategy4_correctness : gmp_strategy4.
Proof.
  pre_process_default.
  unfold store_Z_remain_size.
  Intros ptr old_size cap.
  Exists ptr old_size cap.
  LLM_pre_process ltac:(lia).
  split_pure_spatial.
  - cancel (&( x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> old_size).
    cancel (&( x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap).
    cancel (&( x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr).
    cancel (mpd_store_Z_compact UINT_MOD ptr (Zabs n) (Zabs size)).
    cancel (UIntArray.undef_seg ptr (Zabs size) cap).
    Intros_r y.
    apply_sepcon_adjoint.
    normalize.
    Split.
    + Split.
      * Left; Left.
        cancel.
      * Left; Right.
        cancel.
    + Right.
      cancel.
  - split_pures.
    + dump_pre_spatial; assumption.
    + dump_pre_spatial; assumption.
Qed.

Lemma gmp_strategy21_correctness : gmp_strategy21.
Proof.
  unfold gmp_strategy21.
  pre_process_default.
  prop_apply (UIntArray.seg_Zlength p 0%Z n l).
  Intros_p Hlen.
  prop_apply (UIntArray_seg_list_within_bound p 0%Z n l).
  Intros_p Hbound.
  sep_apply_l_atomic (UIntArray.seg_to_full p 0%Z n l).
  replace (p + 0 * sizeof(UINT)) with p by lia.
  replace (n - 0) with n by lia.
  Intros_r v.
  apply_sepcon_adjoint.
  Intros_p Hv.
  subst v.
  sep_apply_l_atomic
    (UIntArray_full_to_mpd_store_Z_exact p n l (list_to_Z UINT_MOD l)).
  - LLM_pre_process ltac:(lia).
  - LLM_pre_process ltac:(lia).
  - LLM_pre_process ltac:(lia).
  - cancel.
Qed.
