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
From SimpleC.EE.Applications_human.LiteOS Require Import LOS_ListDelInit_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_LOS_ListDelInit_return_wit_1_split_goal_spatial :
  LOS_ListDelInit_return_wit_1_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_LOS_ListDelInit_return_wit_1 : LOS_ListDelInit_return_wit_1.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_LOS_ListDelInit_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_LOS_ListDelete_derive_mid_level_spec_by_low_level_spec : LOS_ListDelete_derive_mid_level_spec_by_low_level_spec.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_dll. Intros h pt.
    sep_apply (@dllseg_split A). simpl.
    Intros y py z. subst.
    sep_apply (@dllseg_to_dllseg_shift_rev A).
    sep_apply (@dllseg_to_dllseg_shift A).
    Exists A storeA1_mid_level_spec a_mid_level_spec py z.
    cancel (&( node_pre # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z).
    cancel (&( z # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> node_pre).
    Exists node_pre.
    split_pure_spatial.
    - cancel (storeA1_mid_level_spec node_pre a_mid_level_spec).
      cancel (&( node_pre # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py).
      cancel (&( py # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> node_pre).
      rewrite <- derivable1_wand_sepcon_adjoint.
      sep_apply (@dllseg_shift_to_dllseg A). Intros x.
      sep_apply (@dllseg_shift_rev_to_dllseg A). Intros py0.
      sep_apply (dllseg_concat storeA1_mid_level_spec x).
      Exists x py0.
      cancel (&( p_mid_level_spec # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py0).
      cancel (&( p_mid_level_spec # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> x).
      cancel (dllseg storeA1_mid_level_spec x p_mid_level_spec p_mid_level_spec py0
        (l1_mid_level_spec ++ l2_mid_level_spec)).
      cancel (&( node_pre # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |->_).
      cancel (&( node_pre # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |->_).
      cancel (storeA1_mid_level_spec node_pre a_mid_level_spec).
    - split_pures; dump_pre_spatial; auto.
Qed.
