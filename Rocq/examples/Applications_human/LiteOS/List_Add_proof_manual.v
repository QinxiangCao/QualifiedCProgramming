Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.LiteOS Require Import List_Add_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_LOS_ListAdd_return_wit_1_split_goal_spatial :
  LOS_ListAdd_return_wit_1_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    unfold dllseg_shift.
    Exists node_pre.
    split_pure_spatial.
    - simpl.
      cancel (storeA_low_level_spec node_pre a_low_level_spec).
      cancel (&( node_pre # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> list_pre).
      cancel (&( list_pre # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> node_pre).
    - split_pures.
      + dump_pre_spatial.
        reflexivity.
      + dump_pre_spatial.
        reflexivity.
Qed.

Lemma proof_of_LOS_ListAdd_return_wit_1 : LOS_ListAdd_return_wit_1.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_LOS_ListAdd_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_LOS_ListTailInsert_return_wit_1 : LOS_ListTailInsert_return_wit_1.
Proof. 
    LLM_pre_process ltac:(int_auto).
    intros.
    unfold store_dll.
    sep_apply(dllseg_shift_concat storeA list_pre list_pstPrev node_pre).
    sep_apply(dllseg_shift_to_dllseg storeA).
    Intros x.
    Exists x node_pre.
    cancel.
Qed. 


Lemma proof_of_LOS_ListTailInsert_which_implies_wit_1 : LOS_ListTailInsert_which_implies_wit_1.
Proof. 
    LLM_pre_process ltac:(int_auto).
    intros.
    unfold store_dll.
    Intros h pt.
    pose proof dllseg_to_dllseg_shift storeA h list list pt.
    sep_apply H.
    Exists pt.
    cancel.
    cancel (&( pt # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> list).
Qed. 

Lemma proof_of_LOS_ListAdd_derive_high_level_spec_by_low_level_spec : LOS_ListAdd_derive_high_level_spec_by_low_level_spec.
Proof. 
    LLM_pre_process ltac:(int_auto).
    Intros un pu.
    Exists A storeA1_high_level_spec a_high_level_spec.
    unfold store_dll at 1.
    Intros h pt.
    Exists h un pu.
    sep_apply(dllseg_to_dllseg_shift_rev storeA1_high_level_spec).
    cancel.
    rewrite <- derivable1_wand_sepcon_adjoint.
    unfold store_dll.
    sep_apply(dllseg_shift_to_dllseg_shift_rev storeA1_high_level_spec).
    Intros x.
    sep_apply (dllseg_shift_rev_concat storeA1_high_level_spec).
    assert(H:(({| data := a_high_level_spec; ptr := node_pre |} :: nil) ++ l_high_level_spec)=({| data := a_high_level_spec; ptr := node_pre |} :: l_high_level_spec)) by (auto).
    rewrite H.
    sep_apply (dllseg_shift_rev_to_dllseg storeA1_high_level_spec x list_pre list_pre ).
    Intros py.
    Exists x py.
    cancel.
Qed. 
