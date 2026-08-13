Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma ptr_array2_strategy1_correctness : ptr_array2_strategy1.
Proof.
  pre_process_default.
  prop_apply (CharPtrArray2.full_Zlength p n rows).
  Intros.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i p i n rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows i nil __default_app1_Z) by lia.
    unfold StorePtrAsElement.storeA.
    fold_arch.
     change (CharPtrArray2.ElemArray.full row_ptr (Zlength (Znth i rows
__default_app1_Z)) (Znth i rows __default_app1_Z)) with (CharArray.full row_ptr (Zlength (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)).
    normalize.
    cancel (CharPtrArray2.missing_i p n i row_ptr rows).
    cancel (CharArray.full row_ptr (Zlength (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)).
    Intros_r v.
    apply_sepcon_adjoint.
    Intros.
    subst v.
    cancel.
Qed.

Lemma ptr_array2_strategy4_correctness : ptr_array2_strategy4.
Proof.
  pre_process_default.
  Intros_p H.
  subst rows2.
  cancel.
Qed.

Lemma ptr_array2_strategy5_correctness : ptr_array2_strategy5.
Proof.
  pre_process_default.
Qed.

Lemma ptr_array2_strategy2_correctness : ptr_array2_strategy2.
Proof.
  pre_process_default.
  pose proof (CharPtrArray2.missing_i_merge_to_full
        p i n row_ptr rows (Znth i rows __default_app1_Z)).
  unfold StorePtrAsElement.storeA in H1.
  fold_arch.
  change (CharPtrArray2.ElemArray.full row_ptr
(Zlength (Znth i rows __default_app1_Z))
(Znth i rows __default_app1_Z)) with (CharArray.full row_ptr (Zlength (Znth i rows __default_app1_Z)) (Znth i rows __default_app1_Z)) in H1.
  sep_apply H1 ; try lia.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
