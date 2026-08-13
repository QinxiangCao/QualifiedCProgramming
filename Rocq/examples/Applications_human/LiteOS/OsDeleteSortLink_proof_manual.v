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
From SimpleC.EE.Applications_human.LiteOS Require Import OsDeleteSortLink_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.glob_vars_and_defs.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.Los_Verify_State_def.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.sortlink.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.dll.
Require Import SimpleC.EE.Applications_human.LiteOS.lib.tick_backup.
Local Open Scope sac.

Lemma storesortedLinkNode_split : 
    forall (A : Type) (storeA : Z -> A -> Assertion) (y y0 : Z) (a : A) (t : Z),
    y = &( y0 # "SortLinkList" ->ₛ "sortLinkNode") ->
    storeA y (sl_data {| sl_data := a; responseTime := t |}) **
    &( y0 # "SortLinkList" ->ₛ "responseTime") # UInt64 |-> responseTime {| sl_data := a; responseTime := t |}|--
    storesortedLinkNode storeA y {| sl_data := a; responseTime := t |}.
Proof.
    intros.
    simpl.
    unfold storesortedLinkNode.
    Exists y0.
    split_pure_spatial.
    - change (sl_data {| sl_data := a; responseTime := t |}) with a.
      change (responseTime {| sl_data := a; responseTime := t |}) with t.
      cancel.
    - dump_pre_spatial.
      assumption.
Qed.


Lemma dllseg_head_insert:
  forall (A: Type) (storeA: Z -> A -> Assertion) 
         (py y z x pt: Z) (a: A) (l: list (DL_Node A)),
    dllseg storeA z y x pt l **
    storeA y a **
    &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py **
    &(y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z |--
    dllseg storeA y py x pt ((Build_DL_Node a y) :: l).
Proof.
    intros.
    simpl.
    Exists z.
    split_pure_spatial.
    - cancel (storeA y a).
      cancel (&( y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py).
      cancel (&( y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z).
      cancel.
    - dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_OsDeleteSortLink_return_wit_3_split_goal_spatial :
  OsDeleteSortLink_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold store_sorted_dll.
  split_pure_spatial.
  - unfold store_dll.
    pose proof dllseg_shift_rev_to_dllseg
      (storesortedLinkNode storeA) v_5 v_pstPrev x (map sortedLinkNodeMapping l2)
      as Hshift_rev.
    sep_apply Hshift_rev.
    Intros py.
    pose proof dllseg_shift_to_dllseg
      (storesortedLinkNode storeA) x v_6 v_pstNext (map sortedLinkNodeMapping l1)
      as Hshift.
    sep_apply Hshift.
    Intros x0.
    Exists x0 py.
    pose proof storesortedLinkNode_split A storeA
      &( node_pre # "SortLinkList" ->ₛ "sortLinkNode") node_pre a t
      as Hnode.
    simpl in Hnode.
    sep_apply Hnode.
    pose proof dllseg_head_insert
      (sortedLinkNode A) (storesortedLinkNode storeA)
      v_6 v_pstPrev v_5 x py (mksortedLinkNode a t)
      (map sortedLinkNodeMapping l2) as Hinsert.
    rewrite PreH5 in Hinsert.
    rewrite PreH5.
    + revert Hinsert.
      csimpl.
      intros Hinsert.
      sep_apply Hinsert.
      pose proof dllseg_concat
        (storesortedLinkNode storeA) x0 x v_pstNext v_6 x py
        (map sortedLinkNodeMapping l1)
        ({|
          data := {| sl_data := a; responseTime := t |};
          ptr := &( node_pre # "SortLinkList" ->ₛ "sortLinkNode")
        |} :: map sortedLinkNodeMapping l2) as Hconcat.
      rewrite PreH4 in Hconcat.
      rewrite PreH4.
      sep_apply Hconcat.
      rewrite map_app.
      rewrite map_cons.
      unfold sortedLinkNodeMapping.
      simpl.
      cancel.
    + lia.
  - dump_pre_spatial.
    exact PreH6.
Qed.

Lemma proof_of_OsDeleteSortLink_return_wit_3 : OsDeleteSortLink_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_OsDeleteSortLink_return_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_OsDeleteSortLink_which_implies_wit_1_split_goal_1 :
    OsDeleteSortLink_which_implies_wit_1_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_sorted_dll.
    unfold increasingSortedNode.
    Intros_p Hincreasing.
    dump_pre_spatial.
    exact Hincreasing.
Qed.

Lemma proof_of_OsDeleteSortLink_which_implies_wit_1_split_goal_spatial :
    OsDeleteSortLink_which_implies_wit_1_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_sorted_dll.
    Intros_p Hincreasing.
    rewrite map_app.
    rewrite map_cons.
    unfold sortedLinkNodeMapping at 2.
    simpl.
    cancel.
Qed.

Lemma proof_of_OsDeleteSortLink_which_implies_wit_1 : OsDeleteSortLink_which_implies_wit_1.
Proof.
    aggressive_pre_process.
    + Goal_apply proof_of_OsDeleteSortLink_which_implies_wit_1_split_goal_spatial.
    + Goal_apply proof_of_OsDeleteSortLink_which_implies_wit_1_split_goal_1.
Qed.

Lemma proof_of_OsDeleteSortLink_which_implies_wit_2 : OsDeleteSortLink_which_implies_wit_2.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold store_dll.
    Intros h pt.
    sep_apply(dllseg_split (storesortedLinkNode(storeA)) h x x pt).
    Intros x0 py.
    simpl dllseg.
    Intros z.
    subst.
    pose proof dllseg_to_dllseg_shift_rev (storesortedLinkNode storeA) z &(node#"SortLinkList"->ₛ "sortLinkNode") x pt (map sortedLinkNodeMapping l2).
    sep_apply (H).
    pose proof dllseg_to_dllseg_shift (storesortedLinkNode storeA) h x &( node # "SortLinkList" ->ₛ "sortLinkNode") py (map sortedLinkNodeMapping l1).
    sep_apply (H0).

    Exists &( node # "SortLinkList" ->ₛ "sortLinkNode") z &( node # "SortLinkList" ->ₛ "sortLinkNode") py.
    split_pure_spatial.
    - csimpl.
      cancel (&( &( node # "SortLinkList" ->ₛ "sortLinkNode") ->ₛ "pstPrev") # Ptr |-> py).
      cancel (&( py # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |->
        &( node # "SortLinkList" ->ₛ "sortLinkNode")).
      cancel (&( &( node # "SortLinkList" ->ₛ "sortLinkNode") ->ₛ "pstNext") # Ptr |-> z).
      cancel (&( z # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |->
        &( node # "SortLinkList" ->ₛ "sortLinkNode")).
      cancel (dllseg_shift_rev (storesortedLinkNode storeA) z x
        (map sortedLinkNodeMapping l2)).
      cancel (dllseg_shift (storesortedLinkNode storeA) x py
        (map sortedLinkNodeMapping l1)).
      cancel.
    - split_pures; dump_pre_spatial; reflexivity.
Qed. 

Lemma proof_of_OsDeleteSortLink_which_implies_wit_3_split_goal_spatial :
    OsDeleteSortLink_which_implies_wit_3_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold storesortedLinkNode.
    Intros y.
    simpl.
    apply addr_of_arrow_field_inv in H.
    rewrite H.
    cancel.
Qed.

Lemma proof_of_OsDeleteSortLink_which_implies_wit_3 : OsDeleteSortLink_which_implies_wit_3.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsDeleteSortLink_which_implies_wit_3_split_goal_spatial.
Qed.

Lemma proof_of_OsDeleteSortLink_which_implies_wit_4_split_goal_spatial :
    OsDeleteSortLink_which_implies_wit_4_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_sorted_dll.
    split_pure_spatial.
    - unfold store_dll.
      pose proof dllseg_shift_rev_to_dllseg (storesortedLinkNode storeA) v_2 v_pstPrev x (map sortedLinkNodeMapping l2) as Hshift_rev.
      sep_apply(Hshift_rev).
      Intros py.
      pose proof dllseg_shift_to_dllseg (storesortedLinkNode storeA) x v v_pstNext (map sortedLinkNodeMapping l1) as Hshift.
      sep_apply(Hshift).
      Intros x0.
      Exists x0 py.
      pose proof storesortedLinkNode_split A storeA &( node # "SortLinkList" ->ₛ "sortLinkNode") node a t.
      simpl in H.
      sep_apply(H).
      pose proof dllseg_head_insert (sortedLinkNode A) (storesortedLinkNode storeA) v v_pstPrev v_2 x py (mksortedLinkNode a t) (map sortedLinkNodeMapping l2) as Hinsert.
      rewrite PreH5 in Hinsert.
      rewrite PreH5.
      + revert Hinsert.
        csimpl.
        intros Hinsert.
        sep_apply(Hinsert).
        pose proof dllseg_concat (storesortedLinkNode storeA) x0 x v_pstNext v x py (map sortedLinkNodeMapping l1) ({|
          data := {| sl_data := a; responseTime := t |};
          ptr := &( node # "SortLinkList" ->ₛ "sortLinkNode")
        |} :: map sortedLinkNodeMapping l2) as Hconcat.
        rewrite PreH4 in Hconcat.
        rewrite PreH4.
        sep_apply(Hconcat).
        rewrite map_app.
        rewrite map_cons.
        unfold sortedLinkNodeMapping.
        simpl.
        cancel.
      + lia.
    - dump_pre_spatial.
      exact PreH3.
Qed.

Lemma proof_of_OsDeleteSortLink_which_implies_wit_4 : OsDeleteSortLink_which_implies_wit_4.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsDeleteSortLink_which_implies_wit_4_split_goal_spatial.
Qed.
