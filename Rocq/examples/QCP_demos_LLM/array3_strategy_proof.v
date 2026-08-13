Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import array3_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma array3_strategy1_correctness : array3_strategy1.
Proof.
  pre_process_default.
  subst am. subst ak.
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
  replace (p + i * (sizeof (INT) * k * m))
    with (p + i * m * k * sizeof (INT)) by (rewrite sizeof_int; lia).
  rewrite (Znth_indep cubes i nil __default_app1_app1_Z) by lia.
  cancel.
Qed.

Lemma array3_strategy2_correctness : array3_strategy2.
Proof.
  pre_process_default.
  subst am. subst ak. subst ak2.
  prop_apply (IntArray3.full_Zlength p n m k cubes). Intros.
  sep_apply (IntArray3.full_split_to_missing_i p i n m k cubes) ; try lia.
  cancel (IntArray3.missing_i p i 0 n m k cubes).
  replace (Znth i cubes nil) with (Znth i cubes __default_app1_app1_Z).
  change (IntArray3.PlaneArray.full (IntArray3.plane_addr p m k i) m k
    (Znth i cubes __default_app1_app1_Z)) with
    (IntArray2.full (p + i * m * k * sizeof (INT)) m k
      (Znth i cubes __default_app1_app1_Z)).
  replace (p + i * ((4 * k) * m))
    with (p + i * m * k * sizeof (INT)) by (rewrite sizeof_int; lia).
  replace (p + i * (sizeof (INT) * k * m))
    with (p + i * m * k * sizeof (INT)) by (rewrite sizeof_int; lia).
  replace (p + i * (
    match k with
    | 0 => 0
    | Z.pos y => Z.pos (xO (xO y))
    | Z.neg y => Z.neg (xO (xO y))
    end * m)) with (p + i * m * k * sizeof (INT))
    by (rewrite sizeof_int; destruct k; lia).
  cancel (IntArray2.full (p + i * m * k * sizeof (INT)) m k
    (Znth i cubes __default_app1_app1_Z)).
  Intros_r v.
  apply_sepcon_adjoint.
  replace (p + i * (
    match k with
    | 0 => 0
    | Z.pos y => Z.pos (xO (xO y))
    | Z.neg y => Z.neg (xO (xO y))
    end * m) + j *
    match k with
    | 0 => 0
    | Z.pos y => Z.pos (xO (xO y))
    | Z.neg y => Z.neg (xO (xO y))
    end + l * 4)
    with (p + i * m * k * sizeof (INT) + j * (sizeof (INT) * k) + l * sizeof (INT))
    by (rewrite sizeof_int; destruct k; lia).
  LLM_pre_process ltac:(lia).
  apply Znth_indep; try lia.
Qed.

Lemma array3_strategy6_correctness : array3_strategy6.
Proof.
  pre_process_default.
  subst am. subst ak. subst ak2.
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
  replace (p + i * (sizeof (INT) * k * m) + 0 * (sizeof (INT) * k))
    with (p + i * m * k * sizeof (INT)) by (rewrite sizeof_int; lia).
  rewrite (Znth_indep cubes i nil __default_app1_app1_Z) by lia.
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
  prop_apply (IntArray3.missing_i_Zlength p i 0 n m k cubes).
  Intros.
  pose proof (IntArray3.missing_i_merge_to_full
        p i n m k cubes (Znth i cubes __default_app1_app1_Z)) as Hmerge.
  change (IntArray3.PlaneArray.full (IntArray3.plane_addr p m k i) m k
    (Znth i cubes __default_app1_app1_Z)) with
    (IntArray2.full (p + i * m * k * sizeof (INT)) m k
      (Znth i cubes __default_app1_app1_Z)) in Hmerge.
  replace (p + i * ((4 * k) * m))
    with (p + i * m * k * sizeof (INT)) by (rewrite sizeof_int; lia).
  replace (p + i * (sizeof (INT) * k * m))
    with (p + i * m * k * sizeof (INT)) by (rewrite sizeof_int; lia).
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma array3_strategy7_correctness : array3_strategy7.
Proof.
  pre_process_default.
  subst am. subst ak. subst ak2.
  prop_apply (IntArray3.missing_i_Zlength p i 0 n m k cubes).
  Intros.
  pose proof (IntArray3.missing_i_merge_to_full
        p i n m k cubes (Znth i cubes __default_app1_app1_Z)) as Hmerge.
  change (IntArray3.PlaneArray.full (IntArray3.plane_addr p m k i) m k
    (Znth i cubes __default_app1_app1_Z)) with
    (IntArray2.full (p + i * m * k * sizeof (INT)) m k
      (Znth i cubes __default_app1_app1_Z)) in Hmerge.
  replace (p + i * ((4 * k) * m) + 0 * (4 * k))
    with (p + i * m * k * sizeof (INT)) by (rewrite sizeof_int; lia).
  replace (p + i * (sizeof (INT) * k * m) + 0 * (sizeof (INT) * k))
    with (p + i * m * k * sizeof (INT)) by (rewrite sizeof_int; lia).
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
