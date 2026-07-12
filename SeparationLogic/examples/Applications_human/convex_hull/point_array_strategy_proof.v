Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human.convex_hull Require Import point_array_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.convex_hull.convex_hull_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Ltac normalize_point_size :=
  repeat rewrite sizeof_front_end_type_Point.

Lemma point_array_strategy20_correctness : point_array_strategy20.
Proof.
  pre_process_default; normalize_point_size.
  entailer!.
  Intros_r vx vy.
  pre_process_default; normalize_point_size.
Qed.

Lemma point_array_strategy25_correctness : point_array_strategy25.
Proof.
  pre_process_default; normalize_point_size.
  assert (Heta :
    point_mk (point_x (Znth i l __default_Point))
             (point_y (Znth i l __default_Point)) =
    Znth i l __default_Point).
  { destruct (Znth i l __default_Point); reflexivity. }
  rewrite Heta.
  sep_apply (PointArray.missing_i_merge_to_full p i n) ; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma point_array_strategy26_correctness : point_array_strategy26.
Proof.
  pre_process_default; normalize_point_size.
  assert (Heta :
    point_mk (point_x (Znth (i - x) l __default_Point))
             (point_y (Znth (i - x) l __default_Point)) =
    Znth (i - x) l __default_Point).
  { destruct (Znth (i - x) l __default_Point); reflexivity. }
  rewrite Heta.
  sep_apply (PointArray.missing_i_merge_to_seg p x i y) ; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

Lemma point_array_strategy19_correctness : point_array_strategy19.
Proof.
  pre_process_default; normalize_point_size.
Qed.

Lemma point_array_strategy1_correctness : point_array_strategy1.
Proof.
  pre_process_default; normalize_point_size.
  prop_apply (PointArray.full_Zlength p n l).
  Intros_p Hlen.
  sep_apply_l_atomic (PointArray.full_split_to_missing_i p i n l default_point).
  - dump_pre_spatial.
    lia.
  - cancel (PointArray.missing_i p i 0 n l).
    Intros_r v.
    Intros_r __default_Point.
    apply_sepcon_adjoint.
    Intros_p Hv.
    subst v.
    assert (Hi : 0 <= i < Zlength l) by (rewrite Hlen; lia).
    rewrite (Znth_indep l i default_point __default_Point Hi).
    cancel.
Qed.

Lemma point_array_strategy4_correctness : point_array_strategy4.
Proof.
  pre_process_default; normalize_point_size.
  Intros_p Hl2.
  subst l2.
  cancel.
Qed.

Lemma point_array_strategy5_correctness : point_array_strategy5.
Proof.
  pre_process_default; normalize_point_size.
Qed.

Lemma point_array_strategy6_correctness : point_array_strategy6.
Proof.
  pre_process_default; normalize_point_size.
  Intros_p Hl2.
  subst l2.
  cancel.
Qed.

Lemma point_array_strategy7_correctness : point_array_strategy7.
Proof.
  pre_process_default; normalize_point_size.
  prop_apply (PointArray.seg_Zlength p x y l).
  Intros_p Hlen.
  sep_apply_l_atomic (PointArray.seg_split_to_missing_i p x i y l default_point).
  - dump_pre_spatial.
    lia.
  - cancel (PointArray.missing_i p i x y l).
    Intros_r v.
    Intros_r __default_Point.
    apply_sepcon_adjoint.
    Intros_p Hv.
    subst v.
    assert (Hi : 0 <= i - x < Zlength l) by (rewrite Hlen; lia).
    rewrite (Znth_indep l (i - x) default_point __default_Point Hi).
    cancel.
Qed.

Lemma point_array_strategy8_correctness : point_array_strategy8.
Proof.
  pre_process_default; normalize_point_size.
  Intros_p Hl3.
  subst l3.
  sep_apply_l_atomic (PointArray.seg_merge_to_seg p x y z l1 l2).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma point_array_strategy9_correctness : point_array_strategy9.
Proof.
  pre_process_default; normalize_point_size.
  Intros_p Heq.
  Intros_p Hlen.
  subst l3.
  prop_apply (PointArray.seg_Zlength p x z (l1 ++ l2)).
  Intros.
  assert (Hz2 : Zlength l2 = z - y) by (rewrite Zlength_app in H1; lia).
  sep_apply_l_atomic (PointArray.seg_split_to_seg p x y z (l1 ++ l2)).
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

Lemma point_array_strategy10_correctness : point_array_strategy10.
Proof.
  pre_process_default; normalize_point_size.
  Intros_p Hsize.
  subst l.
  rewrite PointArray.seg_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma point_array_strategy13_correctness : point_array_strategy13.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.undef_full_split_to_undef_missing_i p 0 n).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (PointArray.undef_missing_i_to_undef_seg_head p 0 n).
    + dump_pre_spatial.
      lia.
    + cancel (PointArray.undef_seg p 1 n).
      apply_sepcon_adjoint.
      elim_emp.
      unfold StorePointAsElement.undefstoreA, undef_point.
      simpl.
      cancel.
Qed.

Lemma point_array_strategy15_correctness : point_array_strategy15.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.undef_seg_split_to_undef_missing_i p x x y).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (PointArray.undef_missing_i_to_undef_seg_head p x y).
    + dump_pre_spatial.
      lia.
    + cancel (PointArray.undef_seg p (x + 1) y).
      apply_sepcon_adjoint.
      elim_emp.
      unfold StorePointAsElement.undefstoreA, undef_point.
      cancel.
Qed.

Lemma point_array_strategy29_correctness : point_array_strategy29.
Proof.
  pre_process_default; normalize_point_size.
  Intros_p Hstore.
  subst b.
  cancel.
Qed.

Lemma point_array_strategy27_correctness : point_array_strategy27.
Proof.
  pre_process_default; normalize_point_size.
Qed.

Lemma point_array_strategy28_correctness : point_array_strategy28.
Proof.
  pre_process_default; normalize_point_size.
  subst m.
  cancel.
Qed.

Lemma point_array_strategy2_correctness : point_array_strategy2.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.missing_i_merge_to_full p i n
    (Znth i l __default_Point) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma point_array_strategy11_correctness : point_array_strategy11.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.missing_i_merge_to_seg p x i y
    (Znth (i - x) l __default_Point) l).
  - dump_pre_spatial.
    lia.
  - rewrite replace_Znth_Znth by lia.
    cancel.
Qed.

Lemma point_array_strategy17_correctness : point_array_strategy17.
Proof.
  pre_process_default; normalize_point_size.
  subst y.
  sep_apply_l_atomic (point_array_store_undef_tail_to_undef_seg p x z a).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma point_array_strategy18_correctness : point_array_strategy18.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (point_array_seg_snoc_store p x y l a).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma point_array_strategy14_correctness : point_array_strategy14.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.undef_full_split_to_undef_missing_i p 0 n).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (PointArray.undef_missing_i_to_undef_seg_head p 0 n).
    + dump_pre_spatial.
      lia.
    + unfold StorePointAsElement.undefstoreA, undef_point.
      simpl.
      eapply derivable1_trans.
      * apply derivable1_sepcon_assoc1.
      * eapply derivable1_trans.
        -- apply derivable1_sepcon_comm.
        -- apply derivable1_sepcon_mono.
           ++ apply derivable1_refl.
           ++ apply derivable1_sepcon_mono.
              ** apply derivable1_refl.
              ** apply_sepcon_adjoint.
                 elim_emp.
                 cancel.
Qed.

Lemma point_array_strategy16_correctness : point_array_strategy16.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.undef_seg_split_to_undef_missing_i p x x y).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (PointArray.undef_missing_i_to_undef_seg_head p x y).
    + dump_pre_spatial.
      lia.
    + unfold StorePointAsElement.undefstoreA, undef_point.
      eapply derivable1_trans.
      * apply derivable1_sepcon_assoc1.
      * eapply derivable1_trans.
        -- apply derivable1_sepcon_comm.
        -- apply derivable1_sepcon_mono.
           ++ apply derivable1_refl.
           ++ apply derivable1_sepcon_mono.
              ** apply derivable1_refl.
              ** apply_sepcon_adjoint.
                 elim_emp.
                 cancel.
Qed.

Lemma point_array_strategy21_correctness : point_array_strategy21.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.full_split_to_missing_i p i n l __default_Point).
  - dump_pre_spatial.
    lia.
  - unfold StorePointAsElement.storeA, store_point.
    cancel (PointArray.missing_i p i 0 n l).
    cancel (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |-> point_y (Znth i l __default_Point))).
    Intros_r vx.
    apply_sepcon_adjoint.
    Intros_p Hvx.
    subst vx.
    elim_emp.
    cancel.
Qed.

Lemma point_array_strategy22_correctness : point_array_strategy22.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.full_split_to_missing_i p i n l __default_Point).
  - dump_pre_spatial.
    lia.
  - unfold StorePointAsElement.storeA, store_point.
    cancel (PointArray.missing_i p i 0 n l).
    cancel (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |-> point_x (Znth i l __default_Point))).
    Intros_r vy.
    apply_sepcon_adjoint.
    Intros_p Hvy.
    subst vy.
    elim_emp.
    cancel.
Qed.

Lemma point_array_strategy23_correctness : point_array_strategy23.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.seg_split_to_missing_i p x i y l __default_Point).
  - dump_pre_spatial.
    lia.
  - unfold StorePointAsElement.storeA, store_point.
    cancel (PointArray.missing_i p i x y l).
    cancel (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |-> point_y (Znth (i - x) l __default_Point))).
    Intros_r vx.
    apply_sepcon_adjoint.
    Intros_p Hvx.
    subst vx.
    elim_emp.
    cancel.
Qed.

Lemma point_array_strategy24_correctness : point_array_strategy24.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.seg_split_to_missing_i p x i y l __default_Point).
  - dump_pre_spatial.
    lia.
  - unfold StorePointAsElement.storeA, store_point.
    cancel (PointArray.missing_i p i x y l).
    cancel (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |-> point_x (Znth (i - x) l __default_Point))).
    Intros_r vy.
    apply_sepcon_adjoint.
    Intros_p Hvy.
    subst vy.
    elim_emp.
    cancel.
Qed.

Lemma point_array_strategy3_correctness : point_array_strategy3.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.missing_i_merge_to_full p i n v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma point_array_strategy12_correctness : point_array_strategy12.
Proof.
  pre_process_default; normalize_point_size.
  sep_apply_l_atomic (PointArray.missing_i_merge_to_seg p x i y v l).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.
