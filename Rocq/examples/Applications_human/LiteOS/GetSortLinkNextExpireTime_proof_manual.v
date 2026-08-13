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
From SimpleC.EE.Applications_human.LiteOS Require Import GetSortLinkNextExpireTime_goal.
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
      cancel (&(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py).
      cancel (&(y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z).
      cancel (dllseg storeA z y x pt l).
    - dump_pre_spatial.
      reflexivity.
Qed.


Lemma dllseg_head_split:
  forall (A: Type) (storeA: Z -> A -> Assertion) 
         (y py x pt: Z) (a: A) (l: list (DL_Node A)),
    dllseg storeA y py x pt ((Build_DL_Node a y) :: l) |--
    EX z,
    dllseg storeA z y x pt l **
    storeA y a **
    &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py **
    &(y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z.
Proof.
    intros.
    simpl.
    Intros z.
    Exists z.
    cancel (dllseg storeA z y x pt l).
    cancel (storeA y a).
    cancel (&(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py).
    cancel (&(y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z).
Qed.

Lemma head_trans:
forall (A: Type) (storeA: Z -> A -> Assertion) 
    (y py x pt az: Z) (a: A) (l: list (DL_Node A)),
  dllseg storeA y py x pt ((Build_DL_Node a az) :: l) |--
“ az = y ”.
Proof.
    intros.
    simpl.
    unfold store_dll.
    Intros z.
    rewrite H.
    dump_pre_spatial.
    reflexivity.
Qed.

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
    - cancel.
      simpl.
      cancel.
    - dump_pre_spatial.
      assumption.
Qed.

Lemma store_dll_shift_rev_unfold:
forall {A: Type} (storeA: addr -> A -> Assertion)(x: addr) (l: list (DL_Node A)),
  store_dll storeA x l |--
  EX xn: addr ,
  &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> xn **
  &(xn # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> x **
  dllseg_shift_rev storeA xn x l.
Proof.
  intros.
  unfold store_dll.
  Intros h pt.
  sep_apply (dllseg_to_dllseg_shift_rev storeA h x x pt l).
  Exists h.
  cancel.
Qed.

Lemma map_sortedLinkNodeMapping_not_nil : forall [A B : Type]  (f : A -> B) (l : list A),
  map f l <> nil -> l <> nil.
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    csimpl.
    destruct l.
    +
    contradiction.
    +
    congruence.
Qed.

Lemma map_sortedLinkNodeMapping : forall [A: Type](d a: DL_Node (sortedLinkNode A)) (l1 l: list (DL_Node (sortedLinkNode A))),
  map sortedLinkNodeMapping (d::l) = a::l1 ->  d.(dll_data) = a.(dll_data).
Proof.
    LLM_pre_process ltac:(int_auto).
    intros.
    csimpl.
    simpl in H.
    destruct d.
    destruct a.
    simpl in H.
    unfold sortedLinkNodeMapping in H.
    simpl in H.
    inversion H.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_entail_wit_1 : GetSortLinkNextExpireTime_entail_wit_1.
Proof. 
    unfold GetSortLinkNextExpireTime_entail_wit_1.
    LLM_pre_process ltac:(int_auto).
    intros.
    Intros.
    destruct l.
    +
    unfold obtian_first_pointer.
    simpl.
    Intros_p Hnil.
    destruct Hnil as [Hh Hpt].
    rewrite Hh.
    split_pure_spatial.
    - cancel.
    - repeat split_pures; dump_pre_spatial;
        try reflexivity; try assumption; try (split; [reflexivity | exact Hpt]).
    +
    unfold obtian_first_pointer.
    simpl.
    Intros z.
    Exists z.
    rewrite H.
    split_pure_spatial.
    - cancel.
      cancel.
      cancel.
      cancel.
      cancel.
    - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity.
Qed. 


Lemma proof_of_GetSortLinkNextExpireTime_return_wit_3_split_goal_1 :
  GetSortLinkNextExpireTime_return_wit_3_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold getFirstNodeExpireTime.
    destruct l.
    +
    unfold MaxTime.
    pose proof (unsigned_last_nbits_eq (ULLONG_MAX - tickPrecision_pre) 64).
    assert (0 <= ULLONG_MAX - tickPrecision_pre).
    lia. 
    assert ( ULLONG_MAX - tickPrecision_pre < 2 ^ 64).
    lia.
    dump_pre_spatial.
    reflexivity.
    +
    simpl in PreH1.
    discriminate PreH1.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_3_split_goal_spatial :
  GetSortLinkNextExpireTime_return_wit_3_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_sorted_dll.
    split_pure_spatial.
    - cancel.
    - split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_3 :
  GetSortLinkNextExpireTime_return_wit_3.
Proof.
    aggressive_pre_process.
    + Goal_apply proof_of_GetSortLinkNextExpireTime_return_wit_3_split_goal_spatial.
    + Goal_apply proof_of_GetSortLinkNextExpireTime_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_2_split_goal_spatial :
  GetSortLinkNextExpireTime_return_wit_2_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_sorted_dll.
    destruct a as [[adata atime] aptr]; simpl in *.
    split_pure_spatial.
    - unfold store_dll.
      rewrite PreH7.
      unfold obtian_first_pointer in PreH4.
      simpl in PreH7.
      rewrite PreH7 in PreH4.
      Exists &( retval_2 # "SortLinkList" ->ₛ "sortLinkNode") pt.
      simpl.
      Exists pl.
      split_pure_spatial.
      + pose proof storesortedLinkNode_split A storeA
          (&( retval_2 # "SortLinkList" ->ₛ "sortLinkNode")) retval_2
          adata atime as HsplitNode.
        sep_apply HsplitNode; try auto.
        csimpl.
        cancel.
      + dump_pre_spatial.
        exact PreH4.
    - dump_pre_spatial.
      unfold increasingSortedNode in PreH8.
      unfold increasing.
      exact PreH8.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_2_split_goal_1 :
  GetSortLinkNextExpireTime_return_wit_2_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold getFirstNodeExpireTime.
    pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l.
    assert (l <> nil) by auto.
    destruct l.
    - contradiction.
    - unfold getNodeExpireTime.
      pose proof (map_sortedLinkNodeMapping d a l1 l PreH7) as HmapDataEq.
      assert (Hunsigned:
        unsigned_last_nbits (startTime_pre + tickPrecision_pre) 64 =
        startTime_pre + tickPrecision_pre).
      {
        pose proof (unsigned_last_nbits_eq
          (startTime_pre + tickPrecision_pre) 64).
        assert (0 <= startTime_pre + tickPrecision_pre) by lia.
        assert (startTime_pre + tickPrecision_pre < 2 ^ 64) by lia.
        lia.
      }
      rewrite Hunsigned in PreH3.
      rewrite Hunsigned.
      rewrite HmapDataEq.
      destruct (responseTime a.(dll_data) <=?
        startTime_pre + tickPrecision_pre)%Z eqn: En.
      + dump_pre_spatial.
        reflexivity.
      + apply Z.leb_gt in En; lia.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_2 :
  GetSortLinkNextExpireTime_return_wit_2.
Proof.
    aggressive_pre_process.
    + Goal_apply proof_of_GetSortLinkNextExpireTime_return_wit_2_split_goal_spatial.
    + Goal_apply proof_of_GetSortLinkNextExpireTime_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_1_split_goal_spatial :
  GetSortLinkNextExpireTime_return_wit_1_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_sorted_dll.
    destruct a as [[adata atime] aptr]; simpl in *.
    split_pure_spatial.
    - unfold store_dll.
      rewrite PreH7.
      unfold obtian_first_pointer in PreH4.
      simpl in PreH7.
      rewrite PreH7 in PreH4.
      Exists &( retval_2 # "SortLinkList" ->ₛ "sortLinkNode") pt.
      simpl.
      Exists pl.
      split_pure_spatial.
      + pose proof storesortedLinkNode_split A storeA
          (&( retval_2 # "SortLinkList" ->ₛ "sortLinkNode")) retval_2
          adata atime as HsplitNode.
        sep_apply HsplitNode; try auto.
        csimpl.
        cancel.
      + dump_pre_spatial.
        exact PreH4.
    - dump_pre_spatial.
      unfold increasingSortedNode in PreH8.
      unfold increasing.
      exact PreH8.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_1_split_goal_1 :
  GetSortLinkNextExpireTime_return_wit_1_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold getFirstNodeExpireTime.
    pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l.
    assert (l <> nil) by auto.
    destruct l.
    - contradiction.
    - unfold getNodeExpireTime.
      pose proof (map_sortedLinkNodeMapping d a l1 l PreH7) as HmapDataEq.
      assert (Hunsigned:
        unsigned_last_nbits (startTime_pre + tickPrecision_pre) 64 =
        startTime_pre + tickPrecision_pre).
      {
        pose proof (unsigned_last_nbits_eq
          (startTime_pre + tickPrecision_pre) 64).
        assert (0 <= startTime_pre + tickPrecision_pre) by lia.
        assert (startTime_pre + tickPrecision_pre < 2 ^ 64) by lia.
        lia.
      }
      rewrite Hunsigned in PreH3.
      rewrite HmapDataEq.
      destruct (responseTime a.(dll_data) <=?
        startTime_pre + tickPrecision_pre)%Z eqn: En.
      + apply Z.leb_le in En; lia.
      + dump_pre_spatial.
        reflexivity.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_1 :
  GetSortLinkNextExpireTime_return_wit_1.
Proof.
    aggressive_pre_process.
    + Goal_apply proof_of_GetSortLinkNextExpireTime_return_wit_1_split_goal_spatial.
    + Goal_apply proof_of_GetSortLinkNextExpireTime_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_1 : GetSortLinkNextExpireTime_which_implies_wit_1.
Proof. 
    unfold GetSortLinkNextExpireTime_which_implies_wit_1.
    LLM_pre_process ltac:(int_auto).
    intros.
    csimpl.
    unfold store_sorted_dll.
    unfold store_dll.
    Intros h pt.
    Exists pt h.
    csimpl.
    split_pure_spatial.
    - cancel (&( &( sortHead # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstNext") # Ptr |-> h).
      cancel (&( &( sortHead # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstPrev") # Ptr |-> pt).
      cancel (dllseg (storesortedLinkNode storeA) h
        &( sortHead # "SortLinkAttribute" ->ₛ "sortLink")
        &( sortHead # "SortLinkAttribute" ->ₛ "sortLink") pt
        (map sortedLinkNodeMapping l)).
    - dump_pre_spatial.
      unfold increasing, increasingSortedNode in *.
      assumption.
Qed. 


Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_2_split_goal_spatial :
  GetSortLinkNextExpireTime_which_implies_wit_2_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    csimpl.
    unfold store_dll.
    Exists h pt.
    csimpl.
    cancel (&( &( sortHead # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstPrev") # Ptr |-> pt).
    cancel (&( &( sortHead # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstNext") # Ptr |-> h).
    cancel (dllseg (storesortedLinkNode storeA) h
      &( sortHead # "SortLinkAttribute" ->ₛ "sortLink")
      &( sortHead # "SortLinkAttribute" ->ₛ "sortLink") pt
      (map sortedLinkNodeMapping l)).
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_2 :
  GetSortLinkNextExpireTime_which_implies_wit_2.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_GetSortLinkNextExpireTime_which_implies_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_3 : GetSortLinkNextExpireTime_which_implies_wit_3.
Proof. 
    unfold GetSortLinkNextExpireTime_which_implies_wit_3.
    LLM_pre_process ltac:(int_auto).
    intros.
    unfold store_dll.
    Intros h pt.
    simpl.
    Intros pl.
    subst h.
    Exists pt pl.
    simpl.
    csimpl.
    cancel (&( &( listSorted # "SortLinkList" ->ₛ "sortLinkNode") ->ₛ "pstNext") # Ptr |-> pl).
    cancel (&( &( listSorted # "SortLinkList" ->ₛ "sortLinkNode") ->ₛ "pstPrev")
      # Ptr |-> &( sortHead # "SortLinkAttribute" ->ₛ "sortLink")).
    cancel (&( &( sortHead # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstNext")
      # Ptr |-> &( listSorted # "SortLinkList" ->ₛ "sortLinkNode")).
    cancel (&( &( sortHead # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstPrev") # Ptr |-> pt).
    cancel (dllseg (storesortedLinkNode storeA) pl
      &( listSorted # "SortLinkList" ->ₛ "sortLinkNode")
      &( sortHead # "SortLinkAttribute" ->ₛ "sortLink") pt l1).
    cancel (storesortedLinkNode storeA
      &( listSorted # "SortLinkList" ->ₛ "sortLinkNode")
      {| sl_data := al; responseTime := t |}).
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_4_split_goal_spatial :
  GetSortLinkNextExpireTime_which_implies_wit_4_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold storesortedLinkNode.
    csimpl.
    Intros y.
    apply addr_of_arrow_field_inv in H.
    rewrite H.
    simpl.
    cancel.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_4 :
  GetSortLinkNextExpireTime_which_implies_wit_4.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_GetSortLinkNextExpireTime_which_implies_wit_4_split_goal_spatial.
Qed.

Lemma proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.
Proof. 
    LLM_pre_process ltac:(int_auto).
    Exists A storeA_getfirstSpec l_getfirstSpec.
    cancel (store_dll storeA_getfirstSpec node_pre l_getfirstSpec).
    apply derivable1_wand_sepcon_adjoint.
    normalize.
    Split.
    - Intros retval_2.
      unfold store_dll.
      Intros h pt.
      unfold dllseg.
      destruct l_getfirstSpec.
      + Intros Hnil.
        contradiction.
      + Intros z.
        Right.
        Exists d l_getfirstSpec retval_2.
        Exists h pt.
        Exists z.
        split_pure_spatial.
        * fold (dllseg storeA_getfirstSpec z h node_pre pt l_getfirstSpec).
          cancel (storeA_getfirstSpec h d.(dll_data)).
          cancel (&( h # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> node_pre).
          cancel (&( h # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z).
          cancel (dllseg storeA_getfirstSpec z h node_pre pt l_getfirstSpec).
          cancel (&( node_pre # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> pt).
          cancel (&( node_pre # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> h).
        * repeat split_pures; dump_pre_spatial;
            try assumption; try reflexivity; try congruence.
    - Intros retval_2.
      Left.
      Exists retval_2.
      split_pure_spatial.
      + cancel.
      + repeat split_pures; dump_pre_spatial;
          try assumption; try reflexivity; try congruence.
Qed.


Lemma proof_of_GetSortLinkNextExpireTime_partial_solve_wit_5_pure_split_goal_1 :
  GetSortLinkNextExpireTime_partial_solve_wit_5_pure_split_goal_1.
Proof.
    LLM_pre_process ltac:(int_auto).
    dump_pre_spatial.
    unfold obtian_first_pointer.
    unfold obtian_first_pointer in PreH5.
    rewrite PreH8 in PreH5.
    exact PreH5.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_partial_solve_wit_5_pure :
  GetSortLinkNextExpireTime_partial_solve_wit_5_pure.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_GetSortLinkNextExpireTime_partial_solve_wit_5_pure_split_goal_1.
Qed.
