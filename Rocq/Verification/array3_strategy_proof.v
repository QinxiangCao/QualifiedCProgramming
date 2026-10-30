From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.Verification Require Import array3_strategy_goal.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string.

Lemma array3_strategy1_correctness : array3_strategy1.
Proof.
  pre_process_default.
  subst am. subst ak.
  rewrite !Z.mul_assoc.
  prop_apply (IntArray3.full_Zlength p n m k cubes). Intros.
  sep_apply (IntArray3.full_split_to_missing_i p i n m k cubes) ; try lia.
  cancel (IntArray3.missing_i p i 0 n m k cubes).
  change (IntArray3.PlaneArray.full (IntArray3.plane_addr p m k i) m k
    (Znth i cubes nil)) with
    (IntArray2.full (p + i * m * k * sizeof (INT)) m k
      (Znth i cubes nil)).
  Intros_r plane __default_app1_app1_Z.
  apply_sepcon_adjoint.
  Intros.
  subst plane.
  rewrite (Znth_indep cubes i __default_app1_app1_Z nil) by lia.
  cancel.
Qed.

Lemma array3_strategy2_correctness : array3_strategy2.
Proof.
  pre_process_default.
  cbn [poly_store poly_undef_store].
  subst am. subst ak. subst ak2.
  rewrite !Z.mul_assoc.
  prop_apply (IntArray3.full_Zlength p n m k cubes). Intros.
  sep_apply (IntArray3.full_split_to_missing_i p i n m k cubes) ; try lia.
  cancel (IntArray3.missing_i p i 0 n m k cubes).
  rewrite (Znth_indep cubes i __default_app1_app1_Z nil) by lia.
  change (IntArray3.PlaneArray.full (IntArray3.plane_addr p m k i) m k
    (Znth i cubes nil)) with
    (IntArray2.full (p + i * m * k * sizeof (INT)) m k
      (Znth i cubes nil)).
  cancel (IntArray2.full (p + i * m * k * sizeof (INT)) m k
    (Znth i cubes nil)).
  Intros_r v.
  apply_sepcon_adjoint.
  LLM_pre_process ltac:(lia).
Qed.

Lemma array3_strategy6_correctness : array3_strategy6.
Proof.
  pre_process_default.
  subst am. subst ak. subst ak2.
  rewrite !Z.mul_assoc, Z.mul_0_l, Z.add_0_r.
  prop_apply (IntArray3.full_Zlength p n m k cubes). Intros.
  sep_apply (IntArray3.full_split_to_missing_i p i n m k cubes) ; try lia.
  cancel (IntArray3.missing_i p i 0 n m k cubes).
  change (IntArray3.PlaneArray.full (IntArray3.plane_addr p m k i) m k
    (Znth i cubes nil)) with
    (IntArray2.full (p + i * m * k * sizeof (INT)) m k
      (Znth i cubes nil)).
  Intros_r plane __default_app1_app1_Z.
  apply_sepcon_adjoint.
  Intros.
  subst plane.
  rewrite (Znth_indep cubes i __default_app1_app1_Z nil) by lia.
  cancel.
Qed.

Lemma array3_strategy4_correctness : array3_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst cubes2.
  cancel.
Qed.

Lemma array3_strategy5_correctness : array3_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma array3_strategy3_correctness : array3_strategy3.
Proof.
  pre_process_default.
  subst am. subst ak.
  rewrite !Z.mul_assoc.
  prop_apply (IntArray3.missing_i_Zlength p i 0 n m k cubes).
  Intros.
  pose proof (IntArray3.missing_i_merge_to_full
        p i n m k cubes (Znth i cubes __default_app1_app1_Z)) as Hmerge.
  change (IntArray3.PlaneArray.full (IntArray3.plane_addr p m k i) m k
    (Znth i cubes __default_app1_app1_Z)) with
    (IntArray2.full (p + i * m * k * sizeof (INT)) m k
      (Znth i cubes __default_app1_app1_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma array3_strategy7_correctness : array3_strategy7.
Proof.
  pre_process_default.
  subst am. subst ak. subst ak2.
  rewrite !Z.mul_assoc, Z.mul_0_l, Z.add_0_r.
  prop_apply (IntArray3.missing_i_Zlength p i 0 n m k cubes).
  Intros.
  pose proof (IntArray3.missing_i_merge_to_full
        p i n m k cubes (Znth i cubes __default_app1_app1_Z)) as Hmerge.
  change (IntArray3.PlaneArray.full (IntArray3.plane_addr p m k i) m k
    (Znth i cubes __default_app1_app1_Z)) with
    (IntArray2.full (p + i * m * k * sizeof (INT)) m k
      (Znth i cubes __default_app1_app1_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
