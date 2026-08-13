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
From SimpleC.EE.Applications_human.LiteOS Require Import OsSortLinkGetNextExpireTime_goal.
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


Lemma next_trans:
forall {A: Type}(storeA: Z -> sortedLinkNode A -> Assertion) 
    (x h pt: Z)(l: list (DL_Node (sortedLinkNode A))),
dllseg storeA h x x pt l **
&(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> pt **
&(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> h  |--
“ h = obtian_first_pointer x l ”.
Proof.
    intros.
    simpl.
    destruct l.
    +
    unfold obtian_first_pointer.
    unfold dllseg.
    Intros_p Hnil.
    split_pures.
    dump_pre_spatial.
    destruct Hnil as [Hh _].
    exact Hh.
    +
    unfold obtian_first_pointer.
    unfold dllseg.
    Intros z.
    split_pures.
    dump_pre_spatial.
    exact H.
Qed.

Lemma dllseg_shift_rev_to_dllseg:
forall {A: Type} (storeA: addr -> A -> Assertion) (x px y: addr) (l: list (DL_Node A)),
  dllseg_shift_rev storeA x y l **
  &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px
  |--
  EX py,
  dllseg storeA x px y py l **
  &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py.
Proof.
  intros.
  revert x px.
  induction l;intros;simpl.
  + Exists px.
    Intros_p Hxy.
    split_pure_spatial.
    - rewrite <- Hxy.
      cancel.
    - dump_pre_spatial.
      split; [assumption | reflexivity].
  + Intros z.
    sep_apply (IHl z x).
    Intros py.
    Exists py z.
    split_pure_spatial.
    - cancel (storeA x a.(dll_data)).
      cancel (&( x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px).
      cancel (&( x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z).
      cancel (dllseg storeA z x y py l).
      cancel.
    - repeat split_pures; dump_pre_spatial; try assumption; try congruence.
Qed.

Lemma proof_of_OsSortLinkGetNextExpireTime_entail_wit_1 : OsSortLinkGetNextExpireTime_entail_wit_1.
Proof. 
    unfold OsSortLinkGetNextExpireTime_entail_wit_1.
    LLM_pre_process ltac:(int_auto).
    intros.
    Intros.
    destruct l.
    +
    unfold obtian_first_pointer.
    simpl.
    Intros_p Hnil.
    split_pure_spatial.
    - destruct Hnil as [Hh _].
      rewrite Hh.
      cancel.
    - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity.
    +
    unfold obtian_first_pointer.
    simpl.
    Intros z.
    Exists z.
    split_pure_spatial.
    - rewrite H.
      cancel (storesortedLinkNode storeA
        &( ((d.(ptr))) # "SortLinkList" ->ₛ "sortLinkNode") d.(dll_data)).
      cancel (&( "SysTick") # Ptr |-> SysTick).
      cancel (storeTick &( "g_archTickTimer") SysTick ts att).
      cancel.
    - repeat split_pures; dump_pre_spatial; try assumption; try reflexivity.
Qed. 

Lemma proof_of_OsSortLinkGetNextExpireTime_return_wit_3 : OsSortLinkGetNextExpireTime_return_wit_3.
Proof. 
    LLM_pre_process ltac:(int_auto).
    intros.
    Right.
    pose proof map_eq_nil sortedLinkNodeMapping l as Hmap_nil.
    assert (l = nil).
    apply Hmap_nil.
    auto.
    Exists SysTick_4.
    split_pure_spatial.
    - unfold store_sorted_dll.
      split_pure_spatial.
      + cancel (&( "SysTick") # Ptr |-> SysTick_4).
        cancel (store_dll (storesortedLinkNode storeA)
          &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink")
          (map sortedLinkNodeMapping l)).
        cancel.
      + dump_pre_spatial.
        assumption.
    - repeat split_pures; dump_pre_spatial; try assumption; try congruence.
Qed. 

Lemma proof_of_OsSortLinkGetNextExpireTime_return_wit_1 : OsSortLinkGetNextExpireTime_return_wit_1.
Proof. 
    LLM_pre_process ltac:(int_auto).
    Left.
    assert (Hl: l <> nil).
    {
      pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l as Hmap_not_nil.
      apply Hmap_not_nil.
      exact PreH9.
    }
    assert (Hresp:
      getFirstNodeResponseTime l =
      getFirstNodeResponseTime (map sortedLinkNodeMapping l)).
    {
      unfold getFirstNodeResponseTime.
      destruct l; simpl; lia.
    }
    assert (Htime: getFirstNodeResponseTime l <= tick_getcycle_ret ts).
    {
      rewrite Hresp.
      rewrite <- PreH6.
      exact PreH1.
    }
    Exists SysTick_5.
    unfold store_sorted_dll.
    split_pure_spatial.
    - assert (h = &( retval_3 # "SortLinkList" ->ₛ "sortLinkNode")) as Hhead by lia.
      rewrite <- Hhead.
      pose proof dllseg_shift_rev_to_dllseg (storesortedLinkNode storeA) h
        (&( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink"))
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink")
        (map sortedLinkNodeMapping l) as Hdll.
      sep_apply Hdll.
      Intros py.
      unfold store_dll.
      Exists h py.
      csimpl.
      simpl.
      assert (x_lSpec_pstNext = h) as Hnext by lia.
      rewrite Hnext.
      cancel (&(
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstPrev")
        # Ptr |-> py).
      cancel (&(
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstNext")
        # Ptr |-> h).
      cancel (dllseg (storesortedLinkNode storeA) h
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink")
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") py
        (map sortedLinkNodeMapping l)).
      cancel.
    - repeat split_pures; dump_pre_spatial; try assumption; try lia.
      all: try (pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l as Hmap_not_nil;
                apply Hmap_not_nil; exact PreH9).
      all: try (rewrite Hresp; rewrite <- PreH6; exact PreH1).
      all: try (rewrite Hresp; rewrite <- PreH6; exact PreH2).
Qed. 

(* These split goals are no longer generated; keep the original lemma names
   here as debugging references and prove the current return witness directly.
Lemma proof_of_OsSortLinkGetNextExpireTime_return_wit_2_split_goal_1 :
  OsSortLinkGetNextExpireTime_return_wit_2_split_goal_1.
Proof. 
    LLM_pre_process ltac:(int_auto).
    assert (getFirstNodeResponseTime l =
      getFirstNodeResponseTime (map sortedLinkNodeMapping l)) as Hresp.
    {
      unfold getFirstNodeResponseTime.
      destruct l; simpl; lia.
    }
    rewrite Hresp.
    rewrite <- PreH6.
    dump_pre_spatial.
    exact PreH2.
Qed.

Lemma proof_of_OsSortLinkGetNextExpireTime_return_wit_2_split_goal_2 :
  OsSortLinkGetNextExpireTime_return_wit_2_split_goal_2.
Proof.
    LLM_pre_process ltac:(int_auto).
    assert (getFirstNodeResponseTime l =
      getFirstNodeResponseTime (map sortedLinkNodeMapping l)) as Hresp.
    {
      unfold getFirstNodeResponseTime.
      destruct l; simpl; lia.
    }
    rewrite Hresp.
    rewrite <- PreH6.
    dump_pre_spatial.
    exact PreH1.
Qed.

Lemma proof_of_OsSortLinkGetNextExpireTime_return_wit_2_split_goal_3 :
  OsSortLinkGetNextExpireTime_return_wit_2_split_goal_3.
Proof.
    LLM_pre_process ltac:(int_auto).
    pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l as Hmap_not_nil.
    dump_pre_spatial.
    apply Hmap_not_nil.
    exact PreH9.
Qed.

Lemma proof_of_OsSortLinkGetNextExpireTime_return_wit_2_split_goal_spatial :
  OsSortLinkGetNextExpireTime_return_wit_2_split_goal_spatial.
Proof.
    LLM_pre_process ltac:(int_auto).
    unfold store_sorted_dll.
    assert (h = &( retval_3 # "SortLinkList" ->ₛ "sortLinkNode")) as Hhead by lia.
    rewrite <- Hhead.
    pose proof dllseg_shift_rev_to_dllseg (storesortedLinkNode storeA) h (&( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") (map sortedLinkNodeMapping l) as Hdll.
    sep_apply Hdll.
    Intros py.
    unfold store_dll.
    Exists h py.
    csimpl.
    simpl.
    assert (x_lSpec_pstNext = h) as Hnext by lia.
    rewrite Hnext.
    split_pure_spatial.
    - cancel (&(
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstPrev")
        # Ptr |-> py).
      cancel (&(
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstNext")
        # Ptr |-> h).
      cancel (dllseg (storesortedLinkNode storeA) h
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink")
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") py
        (map sortedLinkNodeMapping l)).
      cancel.
    - dump_pre_spatial.
      exact PreH12.
Qed.
*)

Lemma proof_of_OsSortLinkGetNextExpireTime_return_wit_2 : OsSortLinkGetNextExpireTime_return_wit_2.
Proof.
    LLM_pre_process ltac:(int_auto).
    Left.
    Left.
    Exists SysTick_5.
    assert (Hresp: getFirstNodeResponseTime l =
      getFirstNodeResponseTime (map sortedLinkNodeMapping l)).
    {
      unfold getFirstNodeResponseTime.
      destruct l; simpl; lia.
    }
    assert (Hincr: increasing l).
    {
      unfold increasing, increasingSortedNode in *.
      destruct l; auto.
    }
    unfold store_sorted_dll.
    assert (h = &( retval_3 # "SortLinkList" ->ₛ "sortLinkNode")) as Hhead by lia.
    rewrite <- Hhead.
    pose proof dllseg_shift_rev_to_dllseg (storesortedLinkNode storeA) h
      (&( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink"))
      &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink")
      (map sortedLinkNodeMapping l) as Hdll.
    sep_apply Hdll.
    Intros py.
    unfold store_dll.
    Exists h py.
    csimpl.
    simpl.
    assert (x_lSpec_pstNext = h) as Hnext by lia.
    rewrite Hnext.
    split_pure_spatial.
    - cancel (&(
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstPrev")
        # Ptr |-> py).
      cancel (&(
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstNext")
        # Ptr |-> h).
      cancel (dllseg (storesortedLinkNode storeA) h
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink")
        &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") py
        (map sortedLinkNodeMapping l)).
      cancel.
    - repeat split_pures; dump_pre_spatial; try assumption; try lia.
      all: try exact Hincr.
      all: try (pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l as Hmap_not_nil;
                apply Hmap_not_nil; exact PreH9).
      all: try (rewrite Hresp; rewrite <- PreH6; exact PreH1).
      all: try (rewrite Hresp; rewrite <- PreH6; exact PreH2).
Qed. 


Lemma proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_1 : OsSortLinkGetNextExpireTime_which_implies_wit_1.
Proof. 
    unfold OsSortLinkGetNextExpireTime_which_implies_wit_1.
    LLM_pre_process ltac:(int_auto).
    intros.
    unfold store_sorted_dll.
    unfold store_dll.
    Intros h pt.
    Exists pt h.
    csimpl.
    split_pure_spatial.
    - cancel (&( &( sortLinkHead # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstNext")
        # Ptr |-> h).
      cancel (&( &( sortLinkHead # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstPrev")
        # Ptr |-> pt).
      cancel (dllseg (storesortedLinkNode storeA) h
        &( sortLinkHead # "SortLinkAttribute" ->ₛ "sortLink")
        &( sortLinkHead # "SortLinkAttribute" ->ₛ "sortLink") pt
        (map sortedLinkNodeMapping l)).
    - dump_pre_spatial.
      exact H.
Qed. 

Lemma proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_2_split_goal_spatial :
  OsSortLinkGetNextExpireTime_which_implies_wit_2_split_goal_spatial.
Proof. 
    LLM_pre_process ltac:(int_auto).
    unfold store_dll.
    Exists h pt.
    csimpl.
    cancel (&( &( sortLinkHead # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstPrev")
      # Ptr |-> pt).
    cancel (&( &( sortLinkHead # "SortLinkAttribute" ->ₛ "sortLink") ->ₛ "pstNext")
      # Ptr |-> h).
    cancel.
Qed. 

Lemma proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_2 : OsSortLinkGetNextExpireTime_which_implies_wit_2.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_3_split_goal_spatial :
  OsSortLinkGetNextExpireTime_which_implies_wit_3_split_goal_spatial.
Proof.  
    LLM_pre_process ltac:(int_auto).
    unfold store_dll.
    Intros h pt.
    csimpl.
    simpl. 
    pose proof dllseg_to_dllseg_shift_rev (storesortedLinkNode storeA) h &( sortLinkHead # "SortLinkAttribute" ->ₛ "sortLink") &( sortLinkHead # "SortLinkAttribute" ->ₛ "sortLink") pt (map sortedLinkNodeMapping l).
    revert H.
    csimpl.
    intros.
    sep_apply H.
    destruct l.
    +
    unfold obtian_first_pointer.
    simpl.
    Intros_p Hh.
    rewrite Hh.
    split_pure_spatial.
    - cancel.
    - dump_pre_spatial.
      reflexivity.
    +
    unfold obtian_first_pointer.
    simpl.
    Intros z.
    Exists z.
    rewrite H0.
    split_pure_spatial.
    - cancel.
      cancel.
      cancel.
      cancel.
    - dump_pre_spatial.
      reflexivity.
Qed.

Lemma proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_3 : OsSortLinkGetNextExpireTime_which_implies_wit_3.
Proof.
    aggressive_pre_process.
    Goal_apply proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_3_split_goal_spatial.
Qed.

Theorem dllseg_shift_rev_split_a:
forall 
    {A : Type} (storeA : addr -> sortedLinkNode A -> Assertion)
    (x z: addr) (l: list (DL_Node (sortedLinkNode A))),
  l <> nil -> dllseg_shift_rev storeA z x l |--
  EX a t y l1,
  “ l = ((Build_DL_Node (mksortedLinkNode a t) z) :: l1) ” &&
  storeA z (mksortedLinkNode a t) **
  &(z # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> y **
  &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> z **
  dllseg_shift_rev storeA y x l1.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  unfold dllseg_shift_rev at 1.
  simpl.
  csimpl.
  destruct l.
  +
  congruence.
  +
  Intros z0.
  simpl.
  csimpl.
  Exists (sl_data d.(dll_data)) (responseTime d.(dll_data)) z0 l.
  unfold dllseg_shift_rev.
  csimpl.
  simpl.
  split_pure_spatial.
  - destruct (d.(dll_data)).
    csimpl.
    simpl.
    cancel.
    cancel.
    cancel.
  - rewrite H0.
    csimpl.
    simpl.
    destruct d.
    destruct data0.
    csimpl.
    simpl.
    congruence.
Qed.


Theorem dllseg_shift_rev_concat_a:
forall 
    {A : Type} (storeA : addr -> sortedLinkNode A -> Assertion)
    (x y z: addr) (a: A) (t : Z) (l l1: list (DL_Node (sortedLinkNode A))),
  l <> nil -> 
  &(z # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> y **
  &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> z **
  dllseg_shift_rev storeA y x l1  **
  storeA z (mksortedLinkNode a t) |--
  dllseg_shift_rev storeA z x ((Build_DL_Node (mksortedLinkNode a t) z) :: l1).
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  unfold dllseg_shift_rev at 1.
  simpl.
  csimpl.
  destruct l.
  +
  congruence.
  +
  simpl.
  csimpl.
  Exists y.
  unfold dllseg_shift_rev.
  simpl.
  csimpl.
  split_pure_spatial.
  - cancel.
    cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma proof_of_OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec : OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec.
Proof. 
    LLM_pre_process ltac:(int_auto).
    intros.
    Intros x_pstNext.
    Exists A storeA_lSpec.
    rewrite <- H.
    pose proof dllseg_shift_rev_split_a (storesortedLinkNode storeA_lSpec) x_lSpec x_pstNext l_lSpec.
    sep_apply H1.
    Intros a t y l1.
    Exists a t.
    cancel (storesortedLinkNode storeA_lSpec
      x_pstNext
      (mksortedLinkNode a t)).
    rewrite <- derivable1_wand_sepcon_adjoint.
    Split.
    - Intros x0.
      Right.
      Exists x_pstNext x0.
      split_pure_spatial.
      + rewrite H3.
        pose proof dllseg_shift_rev_concat_a (storesortedLinkNode storeA_lSpec)
          x_lSpec y x_pstNext a t l_lSpec l1.
        sep_apply H6.
        cancel.
        exact H0.
      + repeat split_pures.
        * dump_pre_spatial.
          unfold getFirstNodeResponseTime.
          simpl.
          csimpl.
          destruct l_lSpec.
          -- congruence.
          -- assert (Hrt: responseTime d.(dll_data) = t).
             { inversion H3. simpl. csimpl. lia. }
             rewrite Hrt.
             apply Z.lt_gt.
             exact H4.
        * dump_pre_spatial.
          unfold getFirstNodeResponseTime.
          simpl.
          csimpl.
          destruct l_lSpec.
          -- congruence.
          -- assert (Hrt: responseTime d.(dll_data) = t).
             { inversion H3. simpl. csimpl. lia. }
             rewrite Hrt.
             exact H5.
        * dump_pre_spatial.
          reflexivity.
    - Intros py0.
      Left.
      Exists x_pstNext py0.
      split_pure_spatial.
      + rewrite H3.
        pose proof dllseg_shift_rev_concat_a (storesortedLinkNode storeA_lSpec)
          x_lSpec y x_pstNext a t l_lSpec l1.
        sep_apply H6.
        cancel.
        exact H0.
      + repeat split_pures.
        * dump_pre_spatial.
          unfold getFirstNodeResponseTime.
          simpl.
          csimpl.
          destruct l_lSpec.
          -- congruence.
          -- assert (Hrt: responseTime d.(dll_data) = t).
             { inversion H3. simpl. csimpl. lia. }
             rewrite Hrt.
             lia.
        * dump_pre_spatial.
          exact H5.
        * dump_pre_spatial.
          reflexivity.
    - exact H0.
Qed. 

Lemma proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.
Proof. 
    LLM_pre_process ltac:(int_auto).
    Exists A storeA_getfirstSpec l_getfirstSpec.
    cancel (store_dll storeA_getfirstSpec node_pre l_getfirstSpec).
    apply derivable1_wand_sepcon_adjoint.
    Split.
    - Intros retval_2.
      destruct l_getfirstSpec.
      + exfalso.
        contradiction.
      + Right.
        Exists d l_getfirstSpec retval_2.
        split_pure_spatial.
        * cancel.
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
