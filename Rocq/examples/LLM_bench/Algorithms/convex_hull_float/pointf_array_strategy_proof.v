Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.convex_hull_float Require Import pointf_array_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.convex_hull_float.convex_hull_float_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Ltac normalize_pointf_size :=
  repeat rewrite sizeof_PointF.

Lemma pointf_array_strategy20_correctness : pointf_array_strategy20.
Proof.
  pre_process_default; normalize_pointf_size.
  cancel (store_pointf (p + i * 8) a).
  Intros_r vx. Intros_r vy.
  pre_process_default; normalize_pointf_size.
 Defined.

Lemma pointf_array_strategy25_correctness : pointf_array_strategy25.
Proof.
  pre_process_default; normalize_pointf_size.
  assert (Heta :
    pointf_mk (pointf_get_x (Znth i l __default_PointF))
             (pointf_get_y (Znth i l __default_PointF)) =
    Znth i l __default_PointF).
  { destruct (Znth i l __default_PointF); reflexivity. }
  rewrite Heta.
  sep_apply (pointf_missing_i_merge_to_full p i n
    (Znth i l __default_PointF) l) ; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma pointf_array_strategy26_correctness : pointf_array_strategy26.
Proof.
  pre_process_default; normalize_pointf_size.
  assert (Heta :
    pointf_mk (pointf_get_x (Znth (i - x) l __default_PointF))
             (pointf_get_y (Znth (i - x) l __default_PointF)) =
    Znth (i - x) l __default_PointF).
  { destruct (Znth (i - x) l __default_PointF); reflexivity. }
  rewrite Heta.
  sep_apply (pointf_missing_i_merge_to_seg p x i y
    (Znth (i - x) l __default_PointF) l) ; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma pointf_array_strategy19_correctness : pointf_array_strategy19.
Proof.
  pre_process_default; normalize_pointf_size.
Qed.

Lemma pointf_array_strategy1_correctness : pointf_array_strategy1.
Proof.
  pre_process_default; normalize_pointf_size.
  prop_apply (PointFArray.full_Zlength p n l).
  Intros_p Hlen.
  sep_apply_l_atomic (pointf_full_split_to_missing_i p i n l default_pointf).
  - dump_pre_spatial.
    lia.
  - cancel (PointFArray.missing_i p i 0 n l).
    Intros_r v.
    Intros_r __default_PointF.
    apply_sepcon_adjoint.
    Intros_p Hv.
    subst v.
    assert (Hi : 0 <= i < Zlength l) by (rewrite Hlen; lia).
    rewrite (Znth_indep l i default_pointf __default_PointF Hi).
    cancel.
Qed.

Lemma pointf_array_strategy4_correctness : pointf_array_strategy4.
Proof.
  pre_process_default; normalize_pointf_size.
  Intros_p Hl2.
  subst l2.
  cancel.
Qed.

Lemma pointf_array_strategy5_correctness : pointf_array_strategy5.
Proof.
  pre_process_default; normalize_pointf_size.
Qed.

Lemma pointf_array_strategy6_correctness : pointf_array_strategy6.
Proof.
  pre_process_default; normalize_pointf_size.
  Intros_p Hl2.
  subst l2.
  cancel.
Qed.

Lemma pointf_array_strategy7_correctness : pointf_array_strategy7.
Proof.
  pre_process_default; normalize_pointf_size.
  prop_apply (PointFArray.seg_Zlength p x y l).
  Intros_p Hlen.
  sep_apply_l_atomic (pointf_seg_split_to_missing_i p x i y l default_pointf).
  - dump_pre_spatial.
    lia.
  - cancel (PointFArray.missing_i p i x y l).
    Intros_r v.
    Intros_r __default_PointF.
    apply_sepcon_adjoint.
    Intros_p Hv.
    subst v.
    assert (Hi : 0 <= i - x < Zlength l) by (rewrite Hlen; lia).
    rewrite (Znth_indep l (i - x) default_pointf __default_PointF Hi).
    cancel.
Qed.

Lemma pointf_array_strategy8_correctness : pointf_array_strategy8.
Proof.
  pre_process_default; normalize_pointf_size.
  Intros_p Hl3.
  subst l3.
  sep_apply_l_atomic (PointFArray.seg_merge_to_seg p x y z l1 l2).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma pointf_array_strategy9_correctness : pointf_array_strategy9.
Proof.
  pre_process_default; normalize_pointf_size.
  Intros_p Heq.
  Intros_p Hlen.
  subst l3.
  prop_apply (PointFArray.seg_Zlength p x z (l1 ++ l2)).
  Intros.
  assert (Hz2 : Zlength l2 = z - y) by (rewrite Zlength_app in H1; lia).
  sep_apply_l_atomic (PointFArray.seg_split_to_seg p x y z (l1 ++ l2)).
  - dump_pre_spatial.
    lia.
  - rewrite <- Hlen.
    rewrite sublist_app_exact1.
    rewrite (sublist_split_app_r (Zlength l1) (z - x) (Zlength l1) l1 l2) by lia.
    replace (Zlength l1 - Zlength l1) with 0 by lia.
    replace (z - x - Zlength l1) with (z - y) by lia.
    rewrite sublist_self by exact (eq_sym Hz2).
    cancel.
Qed.

Lemma pointf_array_strategy10_correctness : pointf_array_strategy10.
Proof.
  pre_process_default; normalize_pointf_size.
  Intros_p Hsize.
  subst l.
  rewrite PointFArray.seg_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma pointf_array_strategy13_correctness : pointf_array_strategy13.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (PointFArray.undef_full_split_to_undef_missing_i p 0 n).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (PointFArray.undef_missing_i_to_undef_seg_head p 0 n).
    + dump_pre_spatial.
      lia.
    + cancel (PointFArray.undef_seg p 1 n).
      apply_sepcon_adjoint.
      cancel.
      unfold StorePointFAsElement.undefstoreA, undef_pointf.
      simpl.
      rewrite sepcon_emp_equiv.
      cancel.
Qed.

Lemma pointf_array_strategy15_correctness : pointf_array_strategy15.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (PointFArray.undef_seg_split_to_undef_missing_i p x x y).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (PointFArray.undef_missing_i_to_undef_seg_head p x y).
    + dump_pre_spatial.
      lia.
    + unfold StorePointFAsElement.undefstoreA, undef_pointf.
      change StorePointFAsElement.sizeA with
        (sizeof_front_end_type (FET_alias "PointF")).
      cancel.
      apply_sepcon_adjoint.
      cancel.
      cancel.
      replace (p + x * 8)
        with (p + x * sizeof_front_end_type (FET_alias "PointF"))
        by (rewrite sizeof_PointF; lia).
      change (sizeof ("PointF")) with (sizeof_alias_type "PointF").
      rewrite sepcon_emp_equiv.
      cancel.
Qed.

Lemma pointf_array_strategy29_correctness : pointf_array_strategy29.
Proof.
  pre_process_default; normalize_pointf_size.
  Intros_p Hstore.
  subst b.
  cancel.
Qed.

Lemma pointf_array_strategy34_correctness : pointf_array_strategy34.
Proof.
  pre_process_default; normalize_pointf_size.
Qed.

Lemma pointf_array_strategy35_correctness : pointf_array_strategy35.
Proof.
  pre_process_default; normalize_pointf_size.
  unfold store_pointf.
  simpl.
  cancel.
Qed.

Lemma pointf_array_strategy30_correctness : pointf_array_strategy30.
Proof.
  pre_process_default; normalize_pointf_size.
  unfold store_pointf, pointf_get_x, pointf_get_y.
  cancel ((&((p) # "PointF" ->ₛ "y") # Float |-> pointf_y a)).
  Intros_r vx0.
  apply_sepcon_adjoint.
  Intros_p Hx.
  subst vx0.
  cancel.
Qed.

Lemma pointf_array_strategy31_correctness : pointf_array_strategy31.
Proof.
  pre_process_default; normalize_pointf_size.
  unfold store_pointf, pointf_get_x, pointf_get_y.
  cancel ((&((p) # "PointF" ->ₛ "x") # Float |-> pointf_x a)).
  Intros_r vy0.
  apply_sepcon_adjoint.
  Intros_p Hy.
  subst vy0.
  cancel.
Qed.

Lemma pointf_array_strategy28_correctness : pointf_array_strategy28.
Proof.
  pre_process_default; normalize_pointf_size.
  subst m.
  cancel.
Qed.

Lemma pointf_array_strategy2_correctness : pointf_array_strategy2.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (pointf_missing_i_merge_to_full p i n
    (Znth i l __default_PointF) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma pointf_array_strategy11_correctness : pointf_array_strategy11.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (pointf_missing_i_merge_to_seg p x i y
    (Znth (i - x) l __default_PointF) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma pointf_array_strategy17_correctness : pointf_array_strategy17.
Proof.
  pre_process_default; normalize_pointf_size.
  subst y.
  sep_apply_l_atomic (pointf_array_store_undef_tail_to_undef_seg p x z a).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma pointf_array_strategy18_correctness : pointf_array_strategy18.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (pointf_array_seg_snoc_store p x y l a).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma pointf_array_strategy14_correctness : pointf_array_strategy14.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (PointFArray.undef_full_split_to_undef_missing_i p 0 n).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (PointFArray.undef_missing_i_to_undef_seg_head p 0 n).
    + dump_pre_spatial.
      lia.
    + unfold StorePointFAsElement.undefstoreA, undef_pointf.
      simpl.
      unfold StorePointFAsElement.sizeA.
      cancel.
      apply derivable1_wand_sepcon_adjoint.
      cancel.
      rewrite sepcon_emp_equiv.
      reflexivity.
Qed.

Lemma pointf_array_strategy16_correctness : pointf_array_strategy16.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (PointFArray.undef_seg_split_to_undef_missing_i p x x y).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (PointFArray.undef_missing_i_to_undef_seg_head p x y).
    + dump_pre_spatial.
      lia.
    + unfold StorePointFAsElement.undefstoreA, undef_pointf.
      simpl.
      unfold StorePointFAsElement.sizeA.
      rewrite sizeof_PointF.
      replace (p + x * 8)
        with (p + x * sizeof_front_end_type (FET_alias "PointF"))
        by (rewrite sizeof_PointF; lia).
      change (sizeof ("PointF")) with (sizeof_alias_type "PointF").
      cancel.
      apply derivable1_wand_sepcon_adjoint.
      cancel.
      apply derivable1_wand_sepcon_adjoint.
      cancel.
      cancel.
      all: try (apply derivable1_wand_sepcon_adjoint; cancel;
                rewrite sepcon_emp_equiv; reflexivity).
Qed.

Lemma pointf_array_strategy21_correctness : pointf_array_strategy21.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (pointf_full_split_to_missing_i p i n l __default_PointF).
  - dump_pre_spatial.
    lia.
  - unfold StorePointFAsElement.storeA, store_pointf, pointf_get_x, pointf_get_y.
    cancel (PointFArray.missing_i p i 0 n l).
    cancel (((&(((Z.add p (Z.mul i 8))) # "PointF" ->ₛ "y")) # Float |-> pointf_y (Znth i l __default_PointF))).
    Intros_r vx0.
    apply_sepcon_adjoint.
    Intros_p Hvx.
    subst vx0.
    cancel.
Qed.

Lemma pointf_array_strategy22_correctness : pointf_array_strategy22.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (pointf_full_split_to_missing_i p i n l __default_PointF).
  - dump_pre_spatial.
    lia.
  - unfold StorePointFAsElement.storeA, store_pointf, pointf_get_x, pointf_get_y.
    cancel (PointFArray.missing_i p i 0 n l).
    cancel (((&(((Z.add p (Z.mul i 8))) # "PointF" ->ₛ "x")) # Float |-> pointf_x (Znth i l __default_PointF))).
    Intros_r vy0.
    apply_sepcon_adjoint.
    Intros_p Hvy.
    subst vy0.
    cancel.
Qed.

Lemma pointf_array_strategy23_correctness : pointf_array_strategy23.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (pointf_seg_split_to_missing_i p x i y l __default_PointF).
  - dump_pre_spatial.
    lia.
  - unfold StorePointFAsElement.storeA, store_pointf, pointf_get_x, pointf_get_y.
    cancel (PointFArray.missing_i p i x y l).
    cancel (((&(((Z.add p (Z.mul i 8))) # "PointF" ->ₛ "y")) # Float |-> pointf_y (Znth (i - x) l __default_PointF))).
    Intros_r vx0.
    apply_sepcon_adjoint.
    Intros_p Hvx.
    subst vx0.
    cancel.
Qed.

Lemma pointf_array_strategy24_correctness : pointf_array_strategy24.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (pointf_seg_split_to_missing_i p x i y l __default_PointF).
  - dump_pre_spatial.
    lia.
  - unfold StorePointFAsElement.storeA, store_pointf, pointf_get_x, pointf_get_y.
    cancel (PointFArray.missing_i p i x y l).
    cancel (((&(((Z.add p (Z.mul i 8))) # "PointF" ->ₛ "x")) # Float |-> pointf_x (Znth (i - x) l __default_PointF))).
    Intros_r vy0.
    apply_sepcon_adjoint.
    Intros_p Hvy.
    subst vy0.
    cancel.
Qed.

Lemma pointf_array_strategy3_correctness : pointf_array_strategy3.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (pointf_missing_i_merge_to_full p i n v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma pointf_array_strategy12_correctness : pointf_array_strategy12.
Proof.
  pre_process_default; normalize_pointf_size.
  sep_apply_l_atomic (pointf_missing_i_merge_to_seg p x i y v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.
