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
    pre_process.
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
    entailer!.
    +
    unfold obtian_first_pointer.
    unfold dllseg.
    Intros z.
    entailer!.
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
    entailer!.
    subst;reflexivity.
  + Intros z.
    sep_apply (IHl z x).
    Intros py.
    Exists py z.
    entailer!.
Qed.

Lemma proof_of_OsSortLinkGetNextExpireTime_entail_wit_1 : OsSortLinkGetNextExpireTime_entail_wit_1.
Proof. 
    unfold OsSortLinkGetNextExpireTime_entail_wit_1.
    pre_process.
    intros.
    Intros.
    destruct l.
    +
    unfold obtian_first_pointer.
    simpl.
    entailer!.
    destruct H as [Hh _].
    rewrite Hh.
    entailer!.
    +
    unfold obtian_first_pointer.
    simpl.
    Intros z.
    Exists z.
    entailer!.
    rewrite H.
    entailer!.
Qed. 

Lemma proof_of_OsSortLinkGetNextExpireTime_return_wit_3 : OsSortLinkGetNextExpireTime_return_wit_3.
Proof. 
    pre_process.
    intros.
    Right.
    pose proof map_eq_nil sortedLinkNodeMapping l as Hmap_nil.
    assert (l = nil).
    apply Hmap_nil.
    auto.
    Exists SysTick_4.
    entailer!.
    unfold store_sorted_dll.
    entailer!.
Qed. 

Lemma proof_of_OsSortLinkGetNextExpireTime_return_wit_1 : OsSortLinkGetNextExpireTime_return_wit_1.
Proof. 
    pre_process.
    intros.
    Left.
    Exists SysTick_5.
    unfold store_sorted_dll.
    entailer!.
    assert (h = &( retval_3 # "SortLinkList" ->ₛ "sortLinkNode")) as Hhead by lia.
    rewrite <- Hhead.
    pose proof dllseg_shift_rev_to_dllseg (storesortedLinkNode storeA) h (&( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") (map sortedLinkNodeMapping l) as Hdll.
    sep_apply Hdll.
    Intros py.
    unfold store_dll.
    Exists h py.
    entailer!.
    csimpl.
    simpl.
    assert (x_lSpec_pstNext = h) as Hnext by lia.
    rewrite Hnext.
    entailer!.
    assert (l <> nil).
    pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l as Hmap_not_nil.
    apply Hmap_not_nil.
    auto.
    assert (getFirstNodeResponseTime l = getFirstNodeResponseTime (map sortedLinkNodeMapping l)) as Hresp.
    unfold getFirstNodeResponseTime.
    destruct l.
    simpl.
    lia.
    simpl.
    lia.
    try rewrite Hresp.
    try rewrite <- PreH6.
    apply PreH1.
    pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l as Hmap_not_nil.
    apply Hmap_not_nil.
    auto.
Qed. 

Lemma proof_of_OsSortLinkGetNextExpireTime_return_wit_2 : OsSortLinkGetNextExpireTime_return_wit_2.
Proof. 
    pre_process.
    intros.
    Exists SysTick_5.
    unfold store_sorted_dll.
    entailer!.
    assert (h = &( retval_3 # "SortLinkList" ->ₛ "sortLinkNode")) as Hhead by lia.
    rewrite <- Hhead.
    pose proof dllseg_shift_rev_to_dllseg (storesortedLinkNode storeA) h (&( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) &( sortLinkHead_pre # "SortLinkAttribute" ->ₛ "sortLink") (map sortedLinkNodeMapping l) as Hdll.
    sep_apply Hdll.
    Intros py.
    unfold store_dll.
    Exists h py.
    entailer!.
    csimpl.
    simpl.
    assert (x_lSpec_pstNext = h) as Hnext by lia.
    rewrite Hnext.
    entailer!.
    assert (l <> nil).
    pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l as Hmap_not_nil.
    apply Hmap_not_nil.
    auto.
    assert (getFirstNodeResponseTime l = getFirstNodeResponseTime (map sortedLinkNodeMapping l)) as Hresp.
    unfold getFirstNodeResponseTime.
    destruct l.
    +
    simpl.
    lia.
    +
    simpl.
    lia.
    +
    try rewrite Hresp.
    try rewrite <- PreH6.
    apply PreH2.
    +
    assert (getFirstNodeResponseTime l = getFirstNodeResponseTime (map sortedLinkNodeMapping l)) as Hresp.
    unfold getFirstNodeResponseTime.
    destruct l.
    simpl.
    lia.
    simpl.
    lia.
    rewrite Hresp.
    rewrite <- PreH6.
    apply PreH1.
    +
    pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l as Hmap_not_nil.
    apply Hmap_not_nil.
    auto.
Qed. 


Lemma proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_1 : OsSortLinkGetNextExpireTime_which_implies_wit_1.
Proof. 
    unfold OsSortLinkGetNextExpireTime_which_implies_wit_1.
    pre_process.
    intros.
    unfold store_sorted_dll.
    unfold store_dll.
    Intros h pt.
    Exists pt h.
    csimpl.
    entailer!.
Qed. 

Lemma proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_2 : OsSortLinkGetNextExpireTime_which_implies_wit_2.
Proof. 
    unfold OsSortLinkGetNextExpireTime_which_implies_wit_2.
    pre_process.
    intros.
    unfold store_dll.
    Exists h pt.
    csimpl.
    entailer!.
Qed. 

Lemma proof_of_OsSortLinkGetNextExpireTime_which_implies_wit_3 : OsSortLinkGetNextExpireTime_which_implies_wit_3.
Proof.  
    unfold OsSortLinkGetNextExpireTime_which_implies_wit_3.
    pre_process.
    intros.
    entailer!.
    unfold store_dll.
    Intros h pt.
    csimpl.
    simpl. 
    Exists h.
    pose proof dllseg_to_dllseg_shift_rev (storesortedLinkNode storeA) h &( sortLinkHead # "SortLinkAttribute" ->ₛ "sortLink") &( sortLinkHead # "SortLinkAttribute" ->ₛ "sortLink") pt (map sortedLinkNodeMapping l).
    revert H.
    csimpl.
    intros.
    sep_apply H.
    destruct l.
    +
    unfold obtian_first_pointer.
    simpl.
    entailer!.  
    +
    unfold obtian_first_pointer.
    simpl.
    Intros z.
    Exists z.
    entailer!.
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
  pre_process.
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
  entailer!.
  destruct (d.(dll_data)).
  entailer!.
  rewrite H0.
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
  pre_process.
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
  entailer!.
  Exists y.
  unfold dllseg_shift_rev.
  simpl.
  csimpl.
  entailer!.
Qed.

Lemma proof_of_OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec : OsSortLinkGetTargetExpireTime_derive_lSpec_by_highSpec.
Proof. 
    pre_process.
    intros.
    Intros x_pstNext.
    Exists A storeA_lSpec.
    rewrite <- H.
    pose proof dllseg_shift_rev_split_a (storesortedLinkNode storeA_lSpec) x_lSpec x_pstNext l_lSpec.
    sep_apply H1.
    Intros a t y l1.
    Exists a t.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    entailer!.
    rewrite orp_sepcon_right.
    rewrite orp_sepcon_right.
    rewrite orp_sepcon_right.
    rewrite orp_sepcon_right.
    apply derivable1_orp_elim.
    entailer!.
    Intros x0.
    Right.
    Exists x_pstNext x0.
    entailer!.
    rewrite H3.
    pose proof dllseg_shift_rev_concat_a (storesortedLinkNode storeA_lSpec) x_lSpec y x_pstNext a t l_lSpec l1.
    sep_apply H6.
    entailer!.
    apply H2.
    unfold getFirstNodeResponseTime.
    simpl.
    csimpl.
    destruct l_lSpec.
    congruence.
    assert (Hrt: responseTime d.(dll_data) = t).
    inversion H3.
    simpl.
    csimpl.
    lia.
    rewrite Hrt.
    exact H5.
    entailer!.
    unfold getFirstNodeResponseTime.
    simpl.
    csimpl.
    destruct l_lSpec.
    congruence.
    assert (Hrt: responseTime d.(dll_data) = t).
    inversion H3.
    simpl.
    csimpl.
    lia.
    rewrite Hrt.
    apply Z.lt_gt.
    exact H4.
    Intros py0.
    Left.
    Exists x_pstNext py0.
    entailer!.
    rewrite H3.
    pose proof dllseg_shift_rev_concat_a (storesortedLinkNode storeA_lSpec) x_lSpec y x_pstNext a t l_lSpec l1.
    sep_apply H6.
    entailer!.
    apply H2.
    unfold getFirstNodeResponseTime.
    simpl.
    csimpl.
    destruct l_lSpec.
    congruence.
    assert (Hrt: responseTime d.(dll_data) = t).
    inversion H3.
    simpl.
    csimpl.
    lia.
    rewrite Hrt.
    lia.
    apply H0.
Qed. 

Lemma proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.
Proof. 
    pre_process.
    Exists A storeA_getfirstSpec l_getfirstSpec.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    entailer!.
    apply derivable1_orp_elim.
    - Intros retval_2.
    unfold store_dll.
    Intros h pt.
    unfold dllseg.
    destruct l_getfirstSpec.
    + entailer!.
    + Intros z.
    Right.
    Exists d l_getfirstSpec retval_2.
    Exists h pt.
    Exists z.
    entailer!.
    - Intros retval_2.
    Left.
    Exists retval_2.
    entailer!.
Qed.
