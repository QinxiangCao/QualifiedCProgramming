Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.paint_house_ii Require Import paint_house_ii_goal.
From SimpleC.EE.LLM_bench.Algorithms.paint_house_ii Require Import paint_house_ii_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.paint_house_ii.paint_house_ii_lib.
Local Open Scope sac.

Lemma proof_of_paint_house_ii_entail_wit_1 : paint_house_ii_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  entailer!.
  unfold PaintHouseIIDPState; auto.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_2 : paint_house_ii_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    costs_pre i n_pre costs_l).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    entailer!.
    all: unfold PaintHouseIIInnerState, PaintHouseIIInf.
    all: repeat split; auto; try lia.
    all: rewrite sizeof_ptr.
    all: rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
    all: change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i costs_l __default__List_Z))
      (Znth i costs_l __default__List_Z)) with
      (IntArray.full row_ptr
        (Zlength (Znth i costs_l __default__List_Z))
        (Znth i costs_l __default__List_Z)).
    all: fold_arch.
    all: cancel.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_3 : paint_house_ii_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists row_ptr_2.
  entailer!.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_4_1 : paint_house_ii_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists row_ptr_2.
  entailer!.
  - unfold PaintHouseIIPrevSelection.
    subst c. destruct (Z.eq_dec min1_color min1_color);
      [reflexivity | contradiction].
  - assert (Hcost_bound: forall r col,
        0 <= r < n_pre ->
        0 <= col < k_pre ->
        0 <= PaintCostAt costs_l r col <= 10000).
    { intros r col Hr Hcol. unfold PaintCostAt.
      rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
      apply PreH10; repeat split; lia. }
    pose proof (PaintHouseIIDPState_values_bound__loop_core
                  costs_l n_pre k_pre i min1 min2 min1_color
                  PreH4 Hcost_bound PreH28) as [_ Hmin2_bound].
    pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)).
    lia.
  - pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)). lia.
  - pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)). lia.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_4_2 : paint_house_ii_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists row_ptr_2.
  entailer!.
  - unfold PaintHouseIIPrevSelection.
    destruct (Z.eq_dec c min1_color); [contradiction | reflexivity].
  - assert (Hcost_bound: forall r col,
        0 <= r < n_pre ->
        0 <= col < k_pre ->
        0 <= PaintCostAt costs_l r col <= 10000).
    { intros r col Hr Hcol. unfold PaintCostAt.
      rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
      apply PreH10; repeat split; lia. }
    pose proof (PaintHouseIIDPState_values_bound__loop_core
                  costs_l n_pre k_pre i min1 min2 min1_color
                  PreH4 Hcost_bound PreH28) as [Hmin1_bound _].
    pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)).
    lia.
  - pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)). lia.
  - pose proof (PreH10 i c) as Hcurrent_cost.
    specialize (Hcurrent_cost ltac:(intuition lia)). lia.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_5_1 : paint_house_ii_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    costs_pre i n_pre costs_l).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    entailer!.
    + rewrite sizeof_ptr.
      rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
      change (IntPtrArray2.ElemArray.full row_ptr
        (Zlength (Znth i costs_l __default__List_Z))
        (Znth i costs_l __default__List_Z)) with
        (IntArray.full row_ptr
          (Zlength (Znth i costs_l __default__List_Z))
          (Znth i costs_l __default__List_Z)).
      fold_arch. cancel.
    + eapply PaintHouseIIInnerState_update_best__loop_core
        with (prev := prev);
        [ lia
        | exact PreH1
        | exact PreH20
        | unfold PaintCostAt;
          rewrite (Znth_indep costs_l i nil __default__List_Z) by lia;
          reflexivity
        | exact PreH22 ].
    + assert (Hcost_bound: forall r col,
        0 <= r < n_pre ->
        0 <= col < k_pre ->
        0 <= PaintCostAt costs_l r col <= 10000).
    { intros r col Hr Hcol. unfold PaintCostAt.
      rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
      apply PreH9; repeat split; lia. }
    pose proof (PaintHouseIIInnerState_values_bound__loop_core
                  costs_l n_pre k_pre i c min1 min2 min1_color
                  new_min1 new_min2 new_min1_color
                  PreH3 Hcost_bound PreH22)
      as [Hnew1_bound _].
    lia.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_5_2 : paint_house_ii_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcost_bound: forall r col,
      0 <= r < n_pre ->
      0 <= col < k_pre ->
      0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply PreH10; repeat split; lia. }
  pose proof (PaintHouseIIInnerState_values_bound__loop_core
                costs_l n_pre k_pre i c min1 min2 min1_color
                new_min1 new_min2 new_min1_color
                PreH4 Hcost_bound PreH23)
    as [Hnew1_bound [_ Hnew_color_bound]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    costs_pre i n_pre costs_l).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    entailer!.
    + rewrite sizeof_ptr.
      rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
      change (IntPtrArray2.ElemArray.full row_ptr
        (Zlength (Znth i costs_l __default__List_Z))
        (Znth i costs_l __default__List_Z)) with
        (IntArray.full row_ptr
          (Zlength (Znth i costs_l __default__List_Z))
          (Znth i costs_l __default__List_Z)).
      fold_arch. cancel.
    + eapply PaintHouseIIInnerState_update_second__loop_core
        with (prev := prev);
        [ lia
        | apply Z.ge_le; exact PreH2
        | exact PreH1
        | exact PreH21
        | unfold PaintCostAt;
          rewrite (Znth_indep costs_l i nil __default__List_Z) by lia;
          reflexivity
        | exact PreH23 ].
Qed.

Lemma proof_of_paint_house_ii_entail_wit_5_3 : paint_house_ii_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcost_bound: forall r col,
          0 <= r < n_pre ->
          0 <= col < k_pre ->
          0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply PreH10; repeat split; lia. }
  pose proof (PaintHouseIIInnerState_values_bound__loop_core
                costs_l n_pre k_pre i c min1 min2 min1_color
                new_min1 new_min2 new_min1_color
                PreH4 Hcost_bound PreH23)
    as [Hnew1_bound [Hnew2_bound Hnew_color_bound]].
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    costs_pre i n_pre costs_l).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    entailer!.
    + rewrite sizeof_ptr.
      rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
      change (IntPtrArray2.ElemArray.full row_ptr
        (Zlength (Znth i costs_l __default__List_Z))
        (Znth i costs_l __default__List_Z)) with
        (IntArray.full row_ptr
          (Zlength (Znth i costs_l __default__List_Z))
          (Znth i costs_l __default__List_Z)).
      fold_arch. cancel.
    + eapply PaintHouseIIInnerState_keep__loop_core
        with (prev := prev) (total := prev + PaintCostAt costs_l i c).
      * lia.
      * replace (PaintCostAt costs_l i c)
          with (Znth c (Znth i costs_l __default__List_Z) 0).
        -- apply Z.ge_le. exact PreH2.
        -- unfold PaintCostAt.
           rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
           reflexivity.
      * replace (PaintCostAt costs_l i c)
          with (Znth c (Znth i costs_l __default__List_Z) 0).
        -- apply Z.ge_le. exact PreH1.
        -- unfold PaintCostAt.
           rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
           reflexivity.
      * pose proof (PaintHouseIIDPState_values_bound__loop_core
                      costs_l n_pre k_pre i min1 min2 min1_color
                      PreH4 Hcost_bound PreH22)
          as [Hmin1_bound Hmin2_bound].
        assert (Hi_cost_bound : i * 10000 <= 99990000) by lia.
        assert (Hpaint_cost_bound : PaintCostAt costs_l i c <= 10000).
        { unfold PaintCostAt.
          rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
          lia. }
        unfold PaintHouseIIPrevSelection in PreH21.
        destruct (Z.eq_dec c min1_color); subst prev;
          unfold PaintHouseIIInf; nia.
      * exact PreH21.
      * unfold PaintCostAt.
        rewrite (Znth_indep costs_l i nil __default__List_Z) by lia.
        reflexivity.
      * exact PreH23.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_6 : paint_house_ii_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcost_bound: forall r col,
      0 <= r < n_pre ->
      0 <= col < k_pre ->
      0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply PreH8; repeat split; lia. }
  pose proof (PaintHouseIIDPState_values_bound__loop_core
                costs_l n_pre k_pre i min1 min2 min1_color
                PreH2 Hcost_bound PreH26)
    as [Hmin1_bound Hmin2_bound].
  assert (Hcolor_bound: -1 <= min1_color < k_pre).
  { pose proof PreH26 as Hdp_shape.
    unfold PaintHouseIIDPState in Hdp_shape.
    destruct Hdp_shape as [[_ [_ [_ Hcolor]]] | [_ [Hcolor _]]];
      subst; lia. }
  Exists row_ptr_2.
  entailer!.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_7 : paint_house_ii_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  entailer!.
  - pose proof (IntPtrArray2.missing_i_merge_to_full
      costs_pre i n_pre row_ptr costs_l
      (Znth i costs_l __default__List_Z)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    rewrite sizeof_ptr.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i costs_l __default__List_Z))
      (Znth i costs_l __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth i costs_l __default__List_Z))
        (Znth i costs_l __default__List_Z)) in Hmerge.
    rewrite replace_Znth_Znth in Hmerge by lia.
    eapply derivable1_trans.
    + apply derivable1_sepcon_comm.
    + apply Hmerge; lia.
  - assert (c_3 = k_pre) by lia.
    subst c_3.
    eapply PaintHouseIIInnerState_completed_row__loop_core; eauto; lia.
  - assert (c_3 = k_pre) by lia.
    subst c_3.
    exact PreH28.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_8 : paint_house_ii_entail_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hcost_bound: forall r col,
      0 <= r < n_pre ->
      0 <= col < k_pre ->
      0 <= PaintCostAt costs_l r col <= 10000).
  { intros r col Hr Hcol. unfold PaintCostAt.
    rewrite (Znth_indep costs_l r nil __default__List_Z) by lia.
    apply PreH8; repeat split; lia. }
  pose proof (PaintHouseIIInnerState_values_bound__loop_core
                costs_l n_pre k_pre i k_pre min1 min2 min1_color
                new_min1 new_min2 new_min1_color
                PreH2 Hcost_bound PreH12)
    as [Hnew1_bound [Hnew2_bound _]].
  pose proof (proj2 PreH13) as Hdp_next.
  assert (Hnew_color_bound: 0 <= new_min1_color < k_pre).
  { pose proof Hdp_next as Hdp_shape.
    unfold PaintHouseIIDPState in Hdp_shape.
    destruct Hdp_shape as [[Hrow _] | [_ [Hcolor _]]]; lia. }
  entailer!.
Qed.

Lemma proof_of_paint_house_ii_entail_wit_9 : paint_house_ii_entail_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_paint_house_ii_return_wit_1 : paint_house_ii_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      assert (i = n_pre) by lia.
      subst i.
      eapply PaintHouseIIDPState_answer__answer; eauto; lia.
    + dump_pre_spatial; lia.
    + dump_pre_spatial; lia.
Qed. 
