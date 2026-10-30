From SimpleC.Verification Require Import StrategyPrelude.
From SimpleC.EE.QCP_demos_LLM Require Import int_ptr_array2_strategy_goal.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope string.

Lemma int_ptr_array2_strategy1_correctness : int_ptr_array2_strategy1.
Proof.
  pre_process_default.
  prop_apply (IntPtrArray2.full_Zlength p n rows).
  Intros.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i p i n rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
    change (IntPtrArray2.ElemArray.full row_ptr (Zlength (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)) with (IntArray.full row_ptr (Zlength (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)).
    normalize.
    cancel (IntPtrArray2.missing_i p n i row_ptr rows).
    cancel (IntArray.full row_ptr (Zlength (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros.
    subst v.
    entailer!.
Qed.

Lemma int_ptr_array2_strategy4_correctness : int_ptr_array2_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst rows2.
  cancel.
Qed.

Lemma int_ptr_array2_strategy5_correctness : int_ptr_array2_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma int_ptr_array2_strategy2_correctness : int_ptr_array2_strategy2.
Proof.
  pre_process_default.
  pose proof (IntPtrArray2.missing_i_merge_to_full p i n row_ptr rows (Znth i rows __default_app1_Z) ltac:(lia)) as Hmerge.
  rewrite replace_Znth_Znth in Hmerge.
  sep_apply_r_atomic Hmerge.
  entailer!.
  sep_apply (derivable1_sepcon_comm (IntArray.full row_ptr (Zlength (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)) (poly_store FET_ptr (p + i * sizeof(PTR)) row_ptr)).
  reflexivity.
Qed.
