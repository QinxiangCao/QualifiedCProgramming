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
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_multi_merge_rel_goal.
From SimpleC.EE.LLM_bench.Engineering.glibc_slist.glibc_slist_rel Require Import glibc_slist_multi_merge_rel_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From MonadLib Require Export MonadLib.
From MonadLib.MonadErr Require Export StateRelMonadErr.
Export MonadNotation.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
Require Import glibc_slist_lib.
Require Import glibc_slist_multi_merge_rel_lib.
Local Open Scope sac.

Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_1_1 : glibc_slist_clean_multi_merge_entail_wit_1_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_left (sll_zero x_pre l1_low_level_spec PreH2).
  subst_eqs.
  sep_apply_left (sll_not_zero y_pre l2_low_level_spec PreH1).
  Intros y x l0.
  subst_eqs.
  Exists nil. Exists (x :: l0). Exists nil. Exists l3_low_level_spec.
  split_pure_spatial.
  - unfold sllseg, sll.
    Exists y.
    split_pure_spatial.
    + cancel (&( y_pre # "list" ->ₛ"data") # Int |-> x).
      cancel (&( y_pre # "list" ->ₛ"next") # Ptr |-> y).
      cancel.
    + split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M in PreH3 at 1.
      prog_nf in PreH3.
      unfold glibc_slist_clean_multi_merge_M_loop_before in PreH3 at 1.
      prog_nf in PreH3.
      unfold glibc_slist_clean_multi_merge_M_loop.
      prog_nf.
      exact PreH3.
    + dump_pre_spatial; auto.
    + dump_pre_spatial; auto.
    + dump_pre_spatial; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_1_2 : glibc_slist_clean_multi_merge_entail_wit_1_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_not_zero x_pre l1_low_level_spec PreH1).
  Intros y x l0.
  subst_eqs.
  Exists nil. Exists (x :: l0). Exists l2_low_level_spec. Exists l3_low_level_spec.
  split_pure_spatial.
  - cancel.
    unfold sllseg, sll.
    Exists y.
    split_pure_spatial.
    + cancel (&( x_pre # "list" ->ₛ"data") # Int |-> x).
      cancel (&( x_pre # "list" ->ₛ"next") # Ptr |-> y).
      cancel.
    + split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M in PreH3 at 1.
      prog_nf in PreH3.
      unfold glibc_slist_clean_multi_merge_M_loop_before in PreH3 at 1.
      prog_nf in PreH3.
      unfold glibc_slist_clean_multi_merge_M_loop.
      prog_nf.
      exact PreH3.
    + dump_pre_spatial; auto.
    + dump_pre_spatial; auto.
    + dump_pre_spatial; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_1 : glibc_slist_clean_multi_merge_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  sep_apply_left (sll_zero z l4_3 PreH5).
  Intros.
  subst_eqs.
  destruct l0_2 as [| l0_2_head l0_2_tail].
  - unfold sll.
    Intros.
    contradiction.
  -
    Exists (l1_3 ++ x_3 :: x_2 :: nil). Exists (l0_2_head :: l0_2_tail). Exists l0. Exists nil.
    split_pure_spatial.
    + sep_apply_left (sllseg_len1 cursor x_3 y_3 PreH9).
    sep_apply_left (sllseg_len1 y_3 x_2 y_2 PreH7).
    sep_apply_left (sllseg_sllseg x cursor y_3 l1_3 (x_3 :: nil)).
    sep_apply_left (sllseg_sllseg x y_3 y_2 (l1_3 ++ x_3 :: nil) (x_2 :: nil)).
    replace ((l1_3 ++ x_3 :: nil) ++ x_2 :: nil)
      with (l1_3 ++ x_3 :: x_2 :: nil).
    2: { rewrite <- app_assoc. reflexivity. }
    unfold sll at 2.
    cancel.
    sep_apply_left (store_ptr_undef_store_ptr (&("node")) y_3).
    unfold sll at 2.
    split_pure_spatial.
    * fold sll.
      cancel.
    * split_pures; dump_pre_spatial; try unfold NULL in *; auto.
    + split_pures.
      * dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
      prog_nf in PreH8.
      unfold_loop in PreH8.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
      prog_nf in PreH8.
      safe_choice_r PreH8.
      { prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_l PreH8.
        - prog_nf in PreH8.
           prog_nf in PreH8.
           unfold continue in PreH8 at 1.
           prog_nf in PreH8.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH8.
        - intro Hnil; discriminate Hnil. }
      { unfold glibc_slist_clean_multi_merge_guardP; simpl.
        left; intro Hnil; discriminate Hnil. }
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_2 : glibc_slist_clean_multi_merge_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l0_2 as [| l0_2_head l0_2_tail].
  - unfold sll.
    Intros.
    contradiction.
  -
    Exists (l1_3 ++ x_3 :: x_2 :: nil).
    Exists (l0_2_head :: l0_2_tail).
    Exists l0.
    Exists l4_3.
    split_pure_spatial.
    + sep_apply_left (sllseg_len1 cursor x_3 y_3 PreH9).
      sep_apply_left (sllseg_len1 y_3 x_2 y_2 PreH7).
      sep_apply_left (sllseg_sllseg x cursor y_3 l1_3 (x_3 :: nil)).
      sep_apply_left (sllseg_sllseg x y_3 y_2 (l1_3 ++ x_3 :: nil) (x_2 :: nil)).
      replace ((l1_3 ++ x_3 :: nil) ++ x_2 :: nil)
        with (l1_3 ++ x_3 :: x_2 :: nil).
      2: { rewrite <- app_assoc. reflexivity. }
      cancel.
      sep_apply_left (store_ptr_undef_store_ptr (&("node")) y_3).
    fold sll.
    cancel.
    + split_pures.
      * dump_pre_spatial.
        unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
        prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
        prog_nf in PreH8.
        unfold_loop in PreH8.
        prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_r PreH8.
        { prog_nf in PreH8.
          unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
          prog_nf in PreH8.
          safe_choice_l PreH8.
          - prog_nf in PreH8.
            prog_nf in PreH8.
            unfold continue in PreH8 at 1.
            prog_nf in PreH8.
            unfold glibc_slist_clean_multi_merge_M_loop.
            prog_nf.
            unfold glibc_slist_clean_multi_merge_M_loop_aux.
            prog_nf.
            exact PreH8.
          - intro Hnil; discriminate Hnil. }
        { unfold glibc_slist_clean_multi_merge_guardP; simpl.
          left; intro Hnil; discriminate Hnil. }
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_3 : glibc_slist_clean_multi_merge_entail_wit_2_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l0_2 as [| l0_2_head l0_2_tail].
  - unfold sll.
    Intros.
    contradiction.
  -
    Exists (l1_3 ++ x_3 :: x_2 :: nil).
    Exists (l0_2_head :: l0_2_tail).
    Exists l3_3.
    Exists l0.
    split_pure_spatial.
    + sep_apply_left (sllseg_len1 cursor x_3 z PreH11).
      sep_apply_left (sllseg_len1 z x_2 y_3 PreH8).
      sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
      sep_apply_left (sllseg_sllseg x z y_3 (l1_3 ++ x_3 :: nil) (x_2 :: nil)).
      replace ((l1_3 ++ x_3 :: nil) ++ x_2 :: nil)
        with (l1_3 ++ x_3 :: x_2 :: nil).
      2: { rewrite <- app_assoc. reflexivity. }
    cancel.
      sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    cancel.
    + split_pures.
      * dump_pre_spatial.
        unfold glibc_slist_clean_multi_merge_M_loop in PreH10 at 1.
        prog_nf in PreH10.
        unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH10 at 1.
        prog_nf in PreH10.
        unfold_loop in PreH10.
        prog_nf in PreH10.
        unfold glibc_slist_clean_multi_merge_M_loop_body in PreH10 at 1.
        prog_nf in PreH10.
        safe_choice_r PreH10.
        { prog_nf in PreH10.
          unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH10 at 1.
          prog_nf in PreH10.
          safe_choice_r PreH10.
          - prog_nf in PreH10.
            prog_nf in PreH10.
            unfold continue in PreH10 at 1.
            prog_nf in PreH10.
            unfold glibc_slist_clean_multi_merge_M_loop.
            prog_nf.
            unfold glibc_slist_clean_multi_merge_M_loop_aux.
            prog_nf.
            exact PreH10.
          - intro Hnil; discriminate Hnil. }
        { unfold glibc_slist_clean_multi_merge_guardP; simpl.
          right; intro Hnil; discriminate Hnil. }
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_4 : glibc_slist_clean_multi_merge_entail_wit_2_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l0_2 as [| l0_2_head l0_2_tail].
  - unfold sll.
    Intros.
    contradiction.
  -
    Exists (l1_3 ++ x_3 :: x_2 :: nil).
    Exists (l0_2_head :: l0_2_tail).
    Exists l3_3.
    Exists l0.
    split_pure_spatial.
    + sep_apply_left (sllseg_len1 cursor x_3 z PreH11).
      sep_apply_left (sllseg_len1 z x_2 y_3 PreH8).
      sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
      sep_apply_left (sllseg_sllseg x z y_3 (l1_3 ++ x_3 :: nil) (x_2 :: nil)).
      replace ((l1_3 ++ x_3 :: nil) ++ x_2 :: nil)
        with (l1_3 ++ x_3 :: x_2 :: nil).
      2: { rewrite <- app_assoc. reflexivity. }
    cancel.
      sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    cancel.
    + split_pures.
      * dump_pre_spatial.
        unfold glibc_slist_clean_multi_merge_M_loop in PreH10 at 1.
        prog_nf in PreH10.
        unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH10 at 1.
        prog_nf in PreH10.
        unfold_loop in PreH10.
        prog_nf in PreH10.
        unfold glibc_slist_clean_multi_merge_M_loop_body in PreH10 at 1.
        prog_nf in PreH10.
        safe_choice_r PreH10.
        { prog_nf in PreH10.
          unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH10 at 1.
          prog_nf in PreH10.
          safe_choice_r PreH10.
          - prog_nf in PreH10.
            prog_nf in PreH10.
            unfold continue in PreH10 at 1.
            prog_nf in PreH10.
            unfold glibc_slist_clean_multi_merge_M_loop.
            prog_nf.
            unfold glibc_slist_clean_multi_merge_M_loop_aux.
            prog_nf.
            exact PreH10.
          - intro Hnil; discriminate Hnil. }
        { unfold glibc_slist_clean_multi_merge_guardP; simpl.
          right; intro Hnil; discriminate Hnil. }
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_5 : glibc_slist_clean_multi_merge_entail_wit_2_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l0_2 as [| l0_2_head l0_2_tail].
  - unfold sll.
    Intros.
    contradiction.
  -
    Exists (l1_3 ++ x_3 :: x_2 :: nil).
    Exists (l0_2_head :: l0_2_tail).
    Exists l3_3.
    Exists l0.
    split_pure_spatial.
    + sep_apply_left (sllseg_len1 cursor x_3 z PreH9).
      sep_apply_left (sllseg_len1 z x_2 y_3 PreH5).
      sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
      sep_apply_left (sllseg_sllseg x z y_3 (l1_3 ++ x_3 :: nil) (x_2 :: nil)).
      replace ((l1_3 ++ x_3 :: nil) ++ x_2 :: nil)
        with (l1_3 ++ x_3 :: x_2 :: nil).
      2: { rewrite <- app_assoc. reflexivity. }
    cancel.
      sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    cancel.
    + split_pures.
      * dump_pre_spatial.
        unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
        prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
        prog_nf in PreH8.
        unfold_loop in PreH8.
        prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_r PreH8.
        { prog_nf in PreH8.
          unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
          prog_nf in PreH8.
          safe_choice_r PreH8.
          - prog_nf in PreH8.
            prog_nf in PreH8.
            unfold continue in PreH8 at 1.
            prog_nf in PreH8.
            unfold glibc_slist_clean_multi_merge_M_loop.
            prog_nf.
            unfold glibc_slist_clean_multi_merge_M_loop_aux.
            prog_nf.
            exact PreH8.
          - intro Hnil; discriminate Hnil. }
        { unfold glibc_slist_clean_multi_merge_guardP; simpl.
          right; intro Hnil; discriminate Hnil. }
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_6 : glibc_slist_clean_multi_merge_entail_wit_2_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l0_2 as [| l0_2_head l0_2_tail].
  - unfold sll.
    Intros.
    contradiction.
  -
    Exists (l1_3 ++ x_3 :: x_2 :: nil).
    Exists (l0_2_head :: l0_2_tail).
    Exists l3_3.
    Exists l0.
    split_pure_spatial.
    + sep_apply_left (sllseg_len1 cursor x_3 z PreH9).
      sep_apply_left (sllseg_len1 z x_2 y_3 PreH5).
      sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
      sep_apply_left (sllseg_sllseg x z y_3 (l1_3 ++ x_3 :: nil) (x_2 :: nil)).
      replace ((l1_3 ++ x_3 :: nil) ++ x_2 :: nil)
        with (l1_3 ++ x_3 :: x_2 :: nil).
      2: { rewrite <- app_assoc. reflexivity. }
    cancel.
      sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    cancel.
    + split_pures.
      * dump_pre_spatial.
        unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
        prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
        prog_nf in PreH8.
        unfold_loop in PreH8.
        prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_r PreH8.
        { prog_nf in PreH8.
          unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
          prog_nf in PreH8.
          safe_choice_r PreH8.
          - prog_nf in PreH8.
            prog_nf in PreH8.
            unfold continue in PreH8 at 1.
            prog_nf in PreH8.
            unfold glibc_slist_clean_multi_merge_M_loop.
            prog_nf.
            unfold glibc_slist_clean_multi_merge_M_loop_aux.
            prog_nf.
            exact PreH8.
          - intro Hnil; discriminate Hnil. }
        { unfold glibc_slist_clean_multi_merge_guardP; simpl.
          right; intro Hnil; discriminate Hnil. }
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_7 : glibc_slist_clean_multi_merge_entail_wit_2_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l0_2 as [| l0_2_head l0_2_tail].
  - unfold sll.
    Intros.
    contradiction.
  -
    Exists (l1_3 ++ x_3 :: x_2 :: nil).
    Exists (l0_2_head :: l0_2_tail).
    Exists l3_3.
    Exists l0.
    split_pure_spatial.
    + sep_apply_left (sllseg_len1 cursor x_3 z PreH10).
      sep_apply_left (sllseg_len1 z x_2 y_3 PreH7).
      sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
      sep_apply_left (sllseg_sllseg x z y_3 (l1_3 ++ x_3 :: nil) (x_2 :: nil)).
      replace ((l1_3 ++ x_3 :: nil) ++ x_2 :: nil)
        with (l1_3 ++ x_3 :: x_2 :: nil).
      2: { rewrite <- app_assoc. reflexivity. }
    cancel.
      sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    cancel.
    + split_pures.
      * dump_pre_spatial.
        unfold glibc_slist_clean_multi_merge_M_loop in PreH9 at 1.
        prog_nf in PreH9.
        unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH9 at 1.
        prog_nf in PreH9.
        unfold_loop in PreH9.
        prog_nf in PreH9.
        unfold glibc_slist_clean_multi_merge_M_loop_body in PreH9 at 1.
        prog_nf in PreH9.
        safe_choice_r PreH9.
        { prog_nf in PreH9.
          unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH9 at 1.
          prog_nf in PreH9.
          safe_choice_r PreH9.
          - prog_nf in PreH9.
            prog_nf in PreH9.
            unfold continue in PreH9 at 1.
            prog_nf in PreH9.
            unfold glibc_slist_clean_multi_merge_M_loop.
            prog_nf.
            unfold glibc_slist_clean_multi_merge_M_loop_aux.
            prog_nf.
            exact PreH9.
          - intro Hnil; discriminate Hnil. }
        { unfold glibc_slist_clean_multi_merge_guardP; simpl.
          right; intro Hnil; discriminate Hnil. }
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_8 : glibc_slist_clean_multi_merge_entail_wit_2_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l0_2 as [| l0_2_head l0_2_tail].
  - unfold sll.
    Intros.
    contradiction.
  -
    Exists (l1_3 ++ x_3 :: x_2 :: nil).
    Exists (l0_2_head :: l0_2_tail).
    Exists l3_3.
    Exists l0.
    split_pure_spatial.
    + sep_apply_left (sllseg_len1 cursor x_3 z PreH10).
      sep_apply_left (sllseg_len1 z x_2 y_3 PreH7).
      sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
      sep_apply_left (sllseg_sllseg x z y_3 (l1_3 ++ x_3 :: nil) (x_2 :: nil)).
      replace ((l1_3 ++ x_3 :: nil) ++ x_2 :: nil)
        with (l1_3 ++ x_3 :: x_2 :: nil).
      2: { rewrite <- app_assoc. reflexivity. }
    cancel.
      sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    cancel.
    + split_pures.
      * dump_pre_spatial.
        unfold glibc_slist_clean_multi_merge_M_loop in PreH9 at 1.
        prog_nf in PreH9.
        unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH9 at 1.
        prog_nf in PreH9.
        unfold_loop in PreH9.
        prog_nf in PreH9.
        unfold glibc_slist_clean_multi_merge_M_loop_body in PreH9 at 1.
        prog_nf in PreH9.
        safe_choice_r PreH9.
        { prog_nf in PreH9.
          unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH9 at 1.
          prog_nf in PreH9.
          safe_choice_r PreH9.
          - prog_nf in PreH9.
            prog_nf in PreH9.
            unfold continue in PreH9 at 1.
            prog_nf in PreH9.
            unfold glibc_slist_clean_multi_merge_M_loop.
            prog_nf.
            unfold glibc_slist_clean_multi_merge_M_loop_aux.
            prog_nf.
            exact PreH9.
          - intro Hnil; discriminate Hnil. }
        { unfold glibc_slist_clean_multi_merge_guardP; simpl.
          right; intro Hnil; discriminate Hnil. }
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_9 : glibc_slist_clean_multi_merge_entail_wit_2_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l0_2 as [| l0_2_head l0_2_tail].
  - unfold sll.
    Intros.
    contradiction.
  -
    Exists (l1_3 ++ x_3 :: x_2 :: nil).
    Exists (l0_2_head :: l0_2_tail).
    Exists l0.
    Exists l4_3.
    split_pure_spatial.
    + sep_apply_left (sllseg_len1 cursor x_3 y_3 PreH9).
      sep_apply_left (sllseg_len1 y_3 x_2 y_2 PreH7).
      sep_apply_left (sllseg_sllseg x cursor y_3 l1_3 (x_3 :: nil)).
      sep_apply_left (sllseg_sllseg x y_3 y_2 (l1_3 ++ x_3 :: nil) (x_2 :: nil)).
      replace ((l1_3 ++ x_3 :: nil) ++ x_2 :: nil)
        with (l1_3 ++ x_3 :: x_2 :: nil).
      2: { rewrite <- app_assoc. reflexivity. }
    cancel.
      sep_apply_left (store_ptr_undef_store_ptr (&("node")) y_3).
    fold sll.
    cancel.
    + split_pures.
      * dump_pre_spatial.
        unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
        prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
        prog_nf in PreH8.
        unfold_loop in PreH8.
        prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_r PreH8.
        { prog_nf in PreH8.
          unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
          prog_nf in PreH8.
          safe_choice_l PreH8.
          - prog_nf in PreH8.
            prog_nf in PreH8.
            unfold continue in PreH8 at 1.
            prog_nf in PreH8.
            unfold glibc_slist_clean_multi_merge_M_loop.
            prog_nf.
            unfold glibc_slist_clean_multi_merge_M_loop_aux.
            prog_nf.
            exact PreH8.
          - intro Hnil; discriminate Hnil. }
        { unfold glibc_slist_clean_multi_merge_guardP; simpl.
          left; intro Hnil; discriminate Hnil. }
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_10 : glibc_slist_clean_multi_merge_entail_wit_2_10.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  destruct l0_2 as [| l0_2_head l0_2_tail].
  - unfold sll.
    Intros.
    contradiction.
  -
    Exists (l1_3 ++ x_3 :: x_2 :: nil).
    Exists (l0_2_head :: l0_2_tail).
    Exists l0.
    Exists l4_3.
    split_pure_spatial.
    + sep_apply_left (sllseg_len1 cursor x_3 y_3 PreH9).
      sep_apply_left (sllseg_len1 y_3 x_2 y_2 PreH7).
      sep_apply_left (sllseg_sllseg x cursor y_3 l1_3 (x_3 :: nil)).
      sep_apply_left (sllseg_sllseg x y_3 y_2 (l1_3 ++ x_3 :: nil) (x_2 :: nil)).
      replace ((l1_3 ++ x_3 :: nil) ++ x_2 :: nil)
        with (l1_3 ++ x_3 :: x_2 :: nil).
      2: { rewrite <- app_assoc. reflexivity. }
    cancel.
      sep_apply_left (store_ptr_undef_store_ptr (&("node")) y_3).
    fold sll.
    cancel.
    + split_pures.
      * dump_pre_spatial.
        unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
        prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
        prog_nf in PreH8.
        unfold_loop in PreH8.
        prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_r PreH8.
        { prog_nf in PreH8.
          unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
          prog_nf in PreH8.
          safe_choice_l PreH8.
          - prog_nf in PreH8.
            prog_nf in PreH8.
            unfold continue in PreH8 at 1.
            prog_nf in PreH8.
            unfold glibc_slist_clean_multi_merge_M_loop.
            prog_nf.
            unfold glibc_slist_clean_multi_merge_M_loop_aux.
            prog_nf.
            exact PreH8.
          - intro Hnil; discriminate Hnil. }
        { unfold glibc_slist_clean_multi_merge_guardP; simpl.
          left; intro Hnil; discriminate Hnil. }
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
      * dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_11 : glibc_slist_clean_multi_merge_entail_wit_2_11.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l0_2 eq_refl).
  Intros.
  subst l0_2.
  Exists (l1_3 ++ x_3 :: nil). Exists (x_2 :: nil). Exists l0. Exists l4_3.
  split_pure_spatial.
  - sep_apply_left (sllseg_len1 cursor x_3 y PreH9).
    sep_apply_left (sllseg_sllseg x cursor y l1_3 (x_3 :: nil)).
    unfold sll.
    Exists 0.
    cancel.
    sep_apply_left (store_ptr_undef_store_ptr (&("node")) y).
    fold sll.
    split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
      prog_nf in PreH8.
      unfold_loop in PreH8.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
      prog_nf in PreH8.
      safe_choice_r PreH8.
      * prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_l PreH8.
        -- prog_nf in PreH8.
           unfold continue in PreH8 at 1.
           prog_nf in PreH8.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH8.
        -- intro Hnil; discriminate Hnil.
      * unfold glibc_slist_clean_multi_merge_guardP; simpl.
        left; intro Hnil; discriminate Hnil.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_12 : glibc_slist_clean_multi_merge_entail_wit_2_12.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l0_2 eq_refl).
  Intros.
  subst l0_2.
  Exists (l1_3 ++ x_3 :: nil). Exists (x_2 :: nil). Exists l0. Exists l4_3.
  split_pure_spatial.
  - sep_apply_left (sllseg_len1 cursor x_3 y PreH9).
    sep_apply_left (sllseg_sllseg x cursor y l1_3 (x_3 :: nil)).
    unfold sll.
    Exists 0.
    cancel.
sep_apply_left (store_ptr_undef_store_ptr (&("node")) y).
    fold sll.
    split_pure_spatial.
+ cancel.
+ split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
      prog_nf in PreH8.
      unfold_loop in PreH8.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
      prog_nf in PreH8.
      safe_choice_r PreH8.
      * prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_l PreH8.
        -- prog_nf in PreH8.
           unfold continue in PreH8 at 1.
           prog_nf in PreH8.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH8.
        -- intro Hnil; discriminate Hnil.
      * unfold glibc_slist_clean_multi_merge_guardP; simpl.
        left; intro Hnil; discriminate Hnil.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_13 : glibc_slist_clean_multi_merge_entail_wit_2_13.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l0_2 eq_refl).
  Intros.
  subst l0_2.
  Exists (l1_3 ++ x_3 :: nil).
  Exists (x_2 :: nil).
  Exists l3_3.
  Exists l0.
  split_pure_spatial.
  - sep_apply_left (sllseg_len1 cursor x_3 z PreH11).
    sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
    unfold sll.
    Exists 0.
    cancel.
sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    split_pure_spatial.
+ cancel.
+ split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH10 at 1.
      prog_nf in PreH10.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH10 at 1.
      prog_nf in PreH10.
      unfold_loop in PreH10.
      prog_nf in PreH10.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH10 at 1.
      prog_nf in PreH10.
      safe_choice_r PreH10.
      * prog_nf in PreH10.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH10 at 1.
        prog_nf in PreH10.
        safe_choice_r PreH10.
        -- prog_nf in PreH10.
           unfold continue in PreH10 at 1.
           prog_nf in PreH10.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH10.
        -- intro Hnil; discriminate Hnil.
      * unfold glibc_slist_clean_multi_merge_guardP; simpl.
        right; intro Hnil; discriminate Hnil.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_14 : glibc_slist_clean_multi_merge_entail_wit_2_14.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l0_2 eq_refl).
  Intros.
  subst l0_2.
  Exists (l1_3 ++ x_3 :: nil).
  Exists (x_2 :: nil).
  Exists l3_3.
  Exists l0.
  split_pure_spatial.
  - sep_apply_left (sllseg_len1 cursor x_3 z PreH11).
    sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
    unfold sll.
    Exists 0.
    cancel.
sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    split_pure_spatial.
+ cancel.
+ split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH10 at 1.
      prog_nf in PreH10.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH10 at 1.
      prog_nf in PreH10.
      unfold_loop in PreH10.
      prog_nf in PreH10.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH10 at 1.
      prog_nf in PreH10.
      safe_choice_r PreH10.
      * prog_nf in PreH10.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH10 at 1.
        prog_nf in PreH10.
        safe_choice_r PreH10.
        -- prog_nf in PreH10.
           unfold continue in PreH10 at 1.
           prog_nf in PreH10.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH10.
        -- intro Hnil; discriminate Hnil.
      * unfold glibc_slist_clean_multi_merge_guardP; simpl.
        right; intro Hnil; discriminate Hnil.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_15 : glibc_slist_clean_multi_merge_entail_wit_2_15.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l0_2 eq_refl).
  Intros.
  subst l0_2.
  Exists (l1_3 ++ x_3 :: nil).
  Exists (x_2 :: nil).
  Exists l3_3.
  Exists l0.
  split_pure_spatial.
  - sep_apply_left (sllseg_len1 cursor x_3 z PreH9).
    sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
    unfold sll.
    Exists 0.
    cancel.
sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    split_pure_spatial.
+ cancel.
+ split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
      prog_nf in PreH8.
      unfold_loop in PreH8.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
      prog_nf in PreH8.
      safe_choice_r PreH8.
      * prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_r PreH8.
        -- prog_nf in PreH8.
           unfold continue in PreH8 at 1.
           prog_nf in PreH8.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH8.
        -- intro Hnil; discriminate Hnil.
      * unfold glibc_slist_clean_multi_merge_guardP; simpl.
        right; intro Hnil; discriminate Hnil.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_16 : glibc_slist_clean_multi_merge_entail_wit_2_16.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l0_2 eq_refl).
  Intros.
  subst l0_2.
  Exists (l1_3 ++ x_3 :: nil).
  Exists (x_2 :: nil).
  Exists l3_3.
  Exists l0.
  split_pure_spatial.
  - sep_apply_left (sllseg_len1 cursor x_3 z PreH9).
    sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
    unfold sll.
    Exists 0.
    cancel.
sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    split_pure_spatial.
+ cancel.
+ split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
      prog_nf in PreH8.
      unfold_loop in PreH8.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
      prog_nf in PreH8.
      safe_choice_r PreH8.
      * prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_r PreH8.
        -- prog_nf in PreH8.
           unfold continue in PreH8 at 1.
           prog_nf in PreH8.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH8.
        -- intro Hnil; discriminate Hnil.
      * unfold glibc_slist_clean_multi_merge_guardP; simpl.
        right; intro Hnil; discriminate Hnil.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_17 : glibc_slist_clean_multi_merge_entail_wit_2_17.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l0_2 eq_refl).
  Intros.
  subst l0_2.
  Exists (l1_3 ++ x_3 :: nil).
  Exists (x_2 :: nil).
  Exists l3_3.
  Exists l0.
  split_pure_spatial.
  - sep_apply_left (sllseg_len1 cursor x_3 z PreH10).
    sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
    unfold sll.
    Exists 0.
    cancel.
sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    split_pure_spatial.
+ cancel.
+ split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH9 at 1.
      prog_nf in PreH9.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH9 at 1.
      prog_nf in PreH9.
      unfold_loop in PreH9.
      prog_nf in PreH9.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH9 at 1.
      prog_nf in PreH9.
      safe_choice_r PreH9.
      * prog_nf in PreH9.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH9 at 1.
        prog_nf in PreH9.
        safe_choice_r PreH9.
        -- prog_nf in PreH9.
           unfold continue in PreH9 at 1.
           prog_nf in PreH9.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH9.
        -- intro Hnil; discriminate Hnil.
      * unfold glibc_slist_clean_multi_merge_guardP; simpl.
        right; intro Hnil; discriminate Hnil.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_18 : glibc_slist_clean_multi_merge_entail_wit_2_18.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l0_2 eq_refl).
  Intros.
  subst l0_2.
  Exists (l1_3 ++ x_3 :: nil).
  Exists (x_2 :: nil).
  Exists l3_3.
  Exists l0.
  split_pure_spatial.
  - sep_apply_left (sllseg_len1 cursor x_3 z PreH10).
    sep_apply_left (sllseg_sllseg x cursor z l1_3 (x_3 :: nil)).
    unfold sll.
    Exists 0.
    cancel.
sep_apply_left (store_ptr_undef_store_ptr (&("node")) z).
    fold sll.
    split_pure_spatial.
+ cancel.
+ split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH9 at 1.
      prog_nf in PreH9.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH9 at 1.
      prog_nf in PreH9.
      unfold_loop in PreH9.
      prog_nf in PreH9.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH9 at 1.
      prog_nf in PreH9.
      safe_choice_r PreH9.
      * prog_nf in PreH9.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH9 at 1.
        prog_nf in PreH9.
        safe_choice_r PreH9.
        -- prog_nf in PreH9.
           unfold continue in PreH9 at 1.
           prog_nf in PreH9.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH9.
        -- intro Hnil; discriminate Hnil.
      * unfold glibc_slist_clean_multi_merge_guardP; simpl.
        right; intro Hnil; discriminate Hnil.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_19 : glibc_slist_clean_multi_merge_entail_wit_2_19.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l0_2 eq_refl).
  Intros.
  subst l0_2.
  Exists (l1_3 ++ x_3 :: nil).
  Exists (x_2 :: nil).
  Exists l0.
  Exists l4_3.
  split_pure_spatial.
  - sep_apply_left (sllseg_len1 cursor x_3 y PreH9).
    sep_apply_left (sllseg_sllseg x cursor y l1_3 (x_3 :: nil)).
    unfold sll.
    Exists 0.
    cancel.
sep_apply_left (store_ptr_undef_store_ptr (&("node")) y).
    fold sll.
    split_pure_spatial.
+ cancel.
+ split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
      prog_nf in PreH8.
      unfold_loop in PreH8.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
      prog_nf in PreH8.
      safe_choice_r PreH8.
      * prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_l PreH8.
        -- prog_nf in PreH8.
           unfold continue in PreH8 at 1.
           prog_nf in PreH8.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH8.
        -- intro Hnil; discriminate Hnil.
      * unfold glibc_slist_clean_multi_merge_guardP; simpl.
        left; intro Hnil; discriminate Hnil.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_entail_wit_2_20 : glibc_slist_clean_multi_merge_entail_wit_2_20.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  sep_apply_left (sll_zero 0 l0_2 eq_refl).
  Intros.
  subst l0_2.
  Exists (l1_3 ++ x_3 :: nil).
  Exists (x_2 :: nil).
  Exists l0.
  Exists l4_3.
  split_pure_spatial.
  - sep_apply_left (sllseg_len1 cursor x_3 y PreH9).
    sep_apply_left (sllseg_sllseg x cursor y l1_3 (x_3 :: nil)).
    unfold sll.
    Exists 0.
    cancel.
sep_apply_left (store_ptr_undef_store_ptr (&("node")) y).
    fold sll.
    split_pure_spatial.
+ cancel.
+ split_pures; dump_pre_spatial; try unfold NULL in *; auto.
  - split_pures.
    + dump_pre_spatial.
      unfold glibc_slist_clean_multi_merge_M_loop in PreH8 at 1.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH8 at 1.
      prog_nf in PreH8.
      unfold_loop in PreH8.
      prog_nf in PreH8.
      unfold glibc_slist_clean_multi_merge_M_loop_body in PreH8 at 1.
      prog_nf in PreH8.
      safe_choice_r PreH8.
      * prog_nf in PreH8.
        unfold glibc_slist_clean_multi_merge_M_loop_M2 in PreH8 at 1.
        prog_nf in PreH8.
        safe_choice_l PreH8.
        -- prog_nf in PreH8.
           unfold continue in PreH8 at 1.
           prog_nf in PreH8.
           unfold glibc_slist_clean_multi_merge_M_loop.
           prog_nf.
           unfold glibc_slist_clean_multi_merge_M_loop_aux.
           prog_nf.
           exact PreH8.
        -- intro Hnil; discriminate Hnil.
      * unfold glibc_slist_clean_multi_merge_guardP; simpl.
        left; intro Hnil; discriminate Hnil.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
    + dump_pre_spatial; try unfold NULL in *; auto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_return_wit_1 : glibc_slist_clean_multi_merge_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (l1 ++ l2).
  split_pure_spatial.
  - sep_apply_left (sll_zero 0 l3 eq_refl). Intros.
    sep_apply_left (sll_zero 0 l4_2 eq_refl). Intros.
    sep_apply_left (sll_zero 0 l1_low_level_spec eq_refl). Intros.
    subst l3. subst l4_2. subst l1_low_level_spec.
    sep_apply_left (sllseg_sll x cursor l1 l2).
    cancel.
  - sep_apply_left (sll_zero 0 l3 eq_refl). Intros.
    sep_apply_left (sll_zero 0 l4_2 eq_refl). Intros.
    sep_apply_left (sll_zero 0 l1_low_level_spec eq_refl). Intros.
    subst l3. subst l4_2. subst l1_low_level_spec.
    split_pure_and_solve.
    unfold glibc_slist_clean_multi_merge_M_loop in PreH3 at 1. prog_nf in PreH3.
    unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH3 at 1. prog_nf in PreH3.
    unfold_loop in PreH3. prog_nf in PreH3.
    unfold glibc_slist_clean_multi_merge_M_loop_body in PreH3 at 1. prog_nf in PreH3.
    safe_choice_l PreH3.
    + unfold glibc_slist_clean_multi_merge_M_loop_M1 in PreH3 at 1. prog_nf in PreH3.
      unfold break in PreH3 at 1. prog_nf in PreH3.
      dump_pre_spatial. exact PreH3.
    + unfold glibc_slist_clean_multi_merge_guardP. simpl.
      tauto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_return_wit_2 : glibc_slist_clean_multi_merge_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists (l1 ++ l2).
  split_pure_spatial.
  - sep_apply_left (sll_zero 0 l3 eq_refl). Intros.
    sep_apply_left (sll_zero 0 l4_2 eq_refl). Intros.
    subst l3. subst l4_2.
    sep_apply_left (sllseg_sll x cursor l1 l2).
    cancel.
  - sep_apply_left (sll_zero 0 l3 eq_refl). Intros.
    sep_apply_left (sll_zero 0 l4_2 eq_refl). Intros.
    subst l3. subst l4_2.
    split_pure_and_solve.
    unfold glibc_slist_clean_multi_merge_M_loop in PreH3 at 1. prog_nf in PreH3.
    unfold glibc_slist_clean_multi_merge_M_loop_aux in PreH3 at 1. prog_nf in PreH3.
    unfold_loop in PreH3. prog_nf in PreH3.
    unfold glibc_slist_clean_multi_merge_M_loop_body in PreH3 at 1. prog_nf in PreH3.
    safe_choice_l PreH3.
    + unfold glibc_slist_clean_multi_merge_M_loop_M1 in PreH3 at 1. prog_nf in PreH3.
      unfold break in PreH3 at 1. prog_nf in PreH3.
      dump_pre_spatial. exact PreH3.
    + unfold glibc_slist_clean_multi_merge_guardP. simpl.
      tauto.
Qed. 
Lemma proof_of_glibc_slist_clean_multi_merge_return_wit_3 : glibc_slist_clean_multi_merge_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  subst_eqs.
  Exists l3_low_level_spec.
  split_pure_spatial.
  - sep_apply_left (sll_zero 0 l1_low_level_spec eq_refl). Intros.
    sep_apply_left (sll_zero 0 l2_low_level_spec eq_refl). Intros.
    subst l1_low_level_spec. subst l2_low_level_spec.
    cancel.
  - sep_apply_left (sll_zero 0 l1_low_level_spec eq_refl). Intros.
    sep_apply_left (sll_zero 0 l2_low_level_spec eq_refl). Intros.
    subst l1_low_level_spec. subst l2_low_level_spec.
    split_pure_and_solve.
    unfold glibc_slist_clean_multi_merge_M in PreH3 at 1. prog_nf in PreH3.
    unfold glibc_slist_clean_multi_merge_M_loop_before in PreH3 at 1. prog_nf in PreH3.
    dump_pre_spatial. exact PreH3.
Qed. 

Lemma proof_of_glibc_slist_clean_multi_merge_derive_high_level_spec_by_low_level_spec : glibc_slist_clean_multi_merge_derive_high_level_spec_by_low_level_spec.
Proof.
  LLM_pre_process ltac:(int_auto).
  Exists (MonadErr.nrm
    (glibc_slist_clean_multi_merge_M
      l1_high_level_spec l2_high_level_spec l3_high_level_spec) tt).
  Exists l1_high_level_spec.
  Exists l2_high_level_spec.
  Exists l3_high_level_spec.
  split_pure_spatial.
  - cancel (sll x_pre l1_high_level_spec).
    cancel (sll y_pre l2_high_level_spec).
    cancel (sll z_pre l3_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros l4.
    Intros retval_2.
    Exists l4.
    Exists retval_2.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial.
    destruct (@Hoare_safeexec_compose unit (list Z)
                ATrue
                (glibc_slist_clean_multi_merge_M
                  l1_high_level_spec l2_high_level_spec l3_high_level_spec)
                (fun r _ =>
                  Permutation r
                    (app (app l1_high_level_spec l2_high_level_spec)
                      l3_high_level_spec))
                (glibc_slist_clean_multi_merge_M_Hoare
                  l1_high_level_spec l2_high_level_spec
                  l3_high_level_spec)
                ATrue l4 tt H I) as [sigma' [Hperm _]].
    exact Hperm.
  - dump_pre_spatial.
    apply safeExec_monad_Atrue_finnal.
    destruct (glibc_slist_clean_multi_merge_M_Hoare
      l1_high_level_spec l2_high_level_spec l3_high_level_spec) as [_ Herr].
    intro Herr0.
    eapply Herr; [exact I | exact Herr0].
Qed.
