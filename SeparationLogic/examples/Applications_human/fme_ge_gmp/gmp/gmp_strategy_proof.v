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
  entailer!.
  destruct H as [Hpq | Hqp]; subst.
  -
    Intros_r l2.
    entailer!.
    apply_sepcon_adjoint.
    Intros_p Hl.
    subst l2.
    cancel.
  -
    Intros_r l2.
    entailer!.
    apply_sepcon_adjoint.
    Intros_p Hl.
    subst l2.
    cancel.
Qed.

Lemma gmp_strategy1_correctness : gmp_strategy1.
Proof.
  pre_process_default.
  unfold mpd_store_Z_compact, mpd_store_Z, is_compact_Z.
  Intros data.
  entailer!.
  - Intros_r v.
    apply_sepcon_adjoint.
    Intros_p Hv.
    subst v.
    Exists data.
    entailer!.
  - refine (ex_intro _ data _).
    destruct H0 as [? [? ?]].
    split; [assumption | split; [symmetry; assumption | tauto]].
Qed.

Lemma gmp_strategy2_correctness : gmp_strategy2.
Proof.
  pre_process_default.
  unfold store_Z.
  Intros ptr size cap.
  Exists ptr size cap.
  entailer!.
  Intros_r y.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
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
  entailer!.
Qed.

Lemma gmp_strategy4_correctness : gmp_strategy4.
Proof.
  pre_process_default.
  unfold store_Z_remain_size.
  Intros ptr old_size cap.
  Exists ptr old_size cap.
  entailer!.
  Intros_r y.
  apply_sepcon_adjoint.
  elim_emp.
  cancel.
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
  - entailer!.
  - entailer!.
  - entailer!.
  - cancel.
Qed.
