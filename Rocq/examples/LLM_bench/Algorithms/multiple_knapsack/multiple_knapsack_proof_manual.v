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
From SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack Require Import multiple_knapsack_goal.
From SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack Require Import multiple_knapsack_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.

From AUXLib Require Import MonotonicList.

(* Convert the public Forall/sublist form to the indexed form used by the
   existing queue helper proofs. This does not add assumptions. *)
Lemma MK_Forall_slice (P : Z -> Prop) l lo hi :
  0 <= lo <= hi -> hi <= Zlength l ->
  (Forall P (sublist lo hi l) <->
   forall p, lo <= p < hi -> P (Znth p l 0)).
Proof.
  intros Hlo Hhi. rewrite (Forall_Znth P 0).
  rewrite Zlength_sublist by lia.
  split; intros H p Hp.
  - specialize (H (p - lo) ltac:(lia)).
    rewrite Znth_sublist in H by lia.
    replace (p - lo + lo) with p in H by lia. exact H.
  - rewrite Znth_sublist by lia. apply H. lia.
Qed.

Ltac mk_lengths := repeat rewrite ?Zlength_replace_Znth, ?Zlength_app,
  ?Zlength_cons, ?Zlength_nil in *.
Ltac mk_forall :=
  repeat match goal with
  | H : Forall ?P (sublist ?lo ?hi ?l) |- _ =>
      rewrite (MK_Forall_slice P l lo hi ltac:(lia) ltac:(lia)) in H
  | H : Forall ?P ?l |- _ => rewrite (Forall_Znth P 0 l) in H
  end.
Ltac mk_at idx :=
  repeat match goal with
  | H : forall z : Z, 0 <= z < Zlength ?l -> _ |- _ =>
      specialize (H idx ltac:(lia))
  | H : forall z : Z, ?lo <= z < ?hi -> _ |- _ =>
      specialize (H idx ltac:(lia))
  end.
Ltac mk_numeric :=
  lazymatch goal with
  | |- _ <= _ => idtac | |- _ < _ => idtac
  | |- _ >= _ => idtac | |- _ > _ => idtac
  | |- @eq Z _ _ => idtac | |- _ /\ _ => idtac
  | _ => fail
  end;
  mk_lengths; mk_forall;
  first [lia |
    match goal with |- context [Znth ?idx ?l 0] => mk_at idx; nia end | nia].
Ltac mk_slice :=
  lazymatch goal with |- Forall ?P (sublist ?lo ?hi ?l) =>
    apply (proj2 (MK_Forall_slice P l lo hi ltac:(lia) ltac:(lia)))
  end.
Ltac mk_simple := first [assumption | reflexivity | constructor; fail |
  solve [intros; eauto] |
  solve [mk_numeric] |
  solve [apply Forall_app; split; [assumption | repeat constructor]] |
  solve [mk_slice;
         intros idx Hidx; mk_numeric] |
  solve [apply (proj2 (Forall_Znth _ 0 _)); intros idx Hidx; mk_numeric]].


(* Reconstruct proof-only interfaces from explicit annotation facts. *)
Ltac mk_table := unfold MKDPTable, MKDPTableSafety, MKDPTableSemantics in *;
  repeat split; try assumption; try lia.
Ltac mk_copy := unfold MKCopyPrefix, MKCopyPrefixSemantics in *;
  repeat split; try assumption; try lia.
Ltac mk_item_bounds := intros idx Hidx; mk_forall; mk_at idx; lia.
Ltac mk_queue_bound := unfold MKQueueResultValueBound;
  intros idx Hidx; mk_forall; mk_at idx; lia.
Ltac mk_transition_bound := unfold MKTransitionValueBound;
  intros p a Hp Htrans; unfold MKTransitionValue in Htrans;
  destruct Htrans as (_ & _ & _ & _ & Htrans);
  match goal with H : forall p a : Z, _ -> _ |- _ =>
    eapply H; split; [exact Hp | exact Htrans] end.

Ltac mk_drop_state cap :=
  lazymatch goal with
  | H : MKQueueDropSemantics ?old ?qi ?qv ?h ?t ?r ?w ?v ?cnt ?k |- _ =>
    let Hb := fresh "Hqueue_bound" in
    assert (Hb : MKQueueResultValueBound qv h t v (k - 1)) by mk_queue_bound;
    let Hs := fresh "Hdrop" in
    assert (Hs : MKQueueDropLoopState old qi qv h t r w v cnt k cap)
      by (unfold MKQueueDropLoopState, MKQueueDropSemantics in *; intuition lia)
  end.
Ltac mk_pending_state cap :=
  lazymatch goal with
  | H : MKQueuePendingSemantics ?old ?qi ?qv ?h ?t ?r ?w ?v ?cnt ?k ?cur |- _ =>
    let Hb := fresh "Hqueue_bound" in
    assert (Hb : MKQueueResultValueBound qv h t v k) by mk_queue_bound;
    let Hs := fresh "Hpending" in
    assert (Hs : MKQueuePendingState old qi qv h t r w v cnt k cap cur)
      by (unfold MKQueuePendingState, MKQueuePendingSemantics in *; intuition lia)
  end.
Ltac mk_read_bound H :=
  unfold MKQueueResultValueBound in H;
  match goal with
  | |- Forall ?P (sublist ?lo ?hi ?l) =>
    apply (proj2 (MK_Forall_slice P l lo hi ltac:(mk_lengths; lia) ltac:(mk_lengths; lia)));
    intros idx Hidx; specialize (H idx Hidx); lia
  end.
Ltac mk_after_drop cap cur pos :=
  mk_drop_state cap;
  lazymatch goal with
  | H : MKQueueDropLoopState ?old ?qi ?qv ?h ?t ?r ?w ?v ?cnt ?k cap |- _ =>
    let Hb := fresh "Htransition_bound" in
    assert (Hb : MKTransitionValueBound old w v cnt cap) by mk_transition_bound;
    let Ha := fresh "Hafter" in
    pose proof (MKQueueDropLoopState_nonempty_exit_to_MKQueueAfterDrop
      old qi qv h t r w v cnt k cap cur pos
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb H) as Ha
  end.
Ltac mk_push cap :=
  mk_pending_state cap;
  lazymatch goal with
  | H : MKQueuePendingState ?old ?qi ?qv ?h ?t ?r ?w ?v ?cnt ?k cap ?cur |- _ =>
    let Hq := fresh "Hresult" in
    pose proof (MKQueuePendingState_push_to_MKQueueState
      old qi qv h t r w v cnt k cap cur H
      ltac:(match goal with E : ?p = r + k * w |- _ => rewrite <- E; assumption end)
      ltac:(nia) ltac:(lia) ltac:(lia) ltac:(intros; lia)) as Hq
  end.




























































































































































































Lemma proof_of_multipleKnapsack_safety_wit_15_split_goal_1 : multipleKnapsack_safety_wit_15_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial. mk_numeric.
Qed.

Lemma proof_of_multipleKnapsack_safety_wit_15_split_goal_2 : multipleKnapsack_safety_wit_15_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto). dump_pre_spatial. mk_numeric.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1_split_goal_1 : multipleKnapsack_entail_wit_1_split_goal_1.
Proof. LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple]. Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1_split_goal_2 : multipleKnapsack_entail_wit_1_split_goal_2.
Proof. LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple]. Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1_split_goal_3 : multipleKnapsack_entail_wit_1_split_goal_3.
Proof. LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple]. Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1_split_goal_4 : multipleKnapsack_entail_wit_1_split_goal_4.
Proof. LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple]. Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1_split_goal_5 : multipleKnapsack_entail_wit_1_split_goal_5.
Proof. LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple]. Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2_split_goal_1 : multipleKnapsack_entail_wit_2_split_goal_1.
Proof. LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple]. Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2_split_goal_2 : multipleKnapsack_entail_wit_2_split_goal_2.
Proof. LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple]. Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2_split_goal_3 : multipleKnapsack_entail_wit_2_split_goal_3.
Proof. LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple]. Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2_split_goal_4 : multipleKnapsack_entail_wit_2_split_goal_4.
Proof. LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple]. Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2_split_goal_5 : multipleKnapsack_entail_wit_2_split_goal_5.
Proof. LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple]. Qed.

Lemma proof_of_multipleKnapsack_entail_wit_4_split_goal_1 : multipleKnapsack_entail_wit_4_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto). unfold MKCopyPrefixSemantics. intros; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_5_split_goal_1 : multipleKnapsack_entail_wit_5_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold MKCopyPrefixSemantics in *. intros cap Hcap.
destruct (Z.eq_dec cap j) as [-> | Hneq].
- rewrite Znth_replace_Znth_Same by lia. reflexivity.
- rewrite Znth_replace_Znth_Diff by lia. apply PreH18; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_5_split_goal_2 : multipleKnapsack_entail_wit_5_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_1 : multipleKnapsack_entail_wit_6_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold MKItemResidueProgressSemantics. split.
- intros rem k pos Hpos Hrem. lia.
- intros rem k pos Hpos Hrem Hk Hp.
  symmetry. apply PreH18. lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_2 : multipleKnapsack_entail_wit_6_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (Htable : MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2) by mk_table.
assert (Hcopy : MKCopyPrefix dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre).
{ replace (capacity_pre + 1) with j by lia. mk_copy. }
assert (Hbound : MKTransitionValueBound old_l_2 (Znth i weights_l 0)
  (Znth i values_l 0) (Znth i counts_l 0) capacity_pre).
{ eapply MKDPTable_implies_MKTransitionValueBound_for_current_item;
    try eassumption; try lia; try reflexivity.
  all: try solve [mk_numeric | split; mk_numeric].
  all: mk_item_bounds. }
destruct H as [[Hp0 Hpcap] Hsem]. apply Hbound with (pos := p); [lia |].
unfold MKTransitionValue.
split; [mk_numeric |]. split; [mk_numeric |].
split; [lia |]. split; [lia | exact Hsem].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_3 : multipleKnapsack_entail_wit_6_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (Htable : MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2) by mk_table.
assert (Hcopy : MKCopyPrefix dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre).
{ replace (capacity_pre + 1) with j by lia. mk_copy. }
assert (Hbound : MKDPValueBound old_l_2 capacity_pre).
{ eapply MKDPTable_copy_implies_MKDPValueBound_under_global_item_bounds;
    try eassumption; try lia. mk_item_bounds. }
unfold MKDPValueBound in Hbound. destruct Hbound as [_ Hbound].
apply (proj2 (Forall_Znth _ 0 _)). intros idx Hidx.
specialize (Hbound idx ltac:(lia)). lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_4 : multipleKnapsack_entail_wit_6_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (Htable : MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2) by mk_table.
assert (Hcopy : MKCopyPrefix dp_l_2 old_l_2 (capacity_pre + 1) capacity_pre).
{ replace (capacity_pre + 1) with j by lia. mk_copy. }
assert (Hbound : MKDPValueBound old_l_2 capacity_pre).
{ eapply MKDPTable_copy_implies_MKDPValueBound_under_global_item_bounds;
    try eassumption; try lia. mk_item_bounds. }
unfold MKDPValueBound in Hbound. destruct Hbound as [_ Hbound].
apply (proj2 (Forall_Znth _ 0 _)). intros idx Hidx.
specialize (Hbound idx ltac:(lia)). lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_5 : multipleKnapsack_entail_wit_6_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold MKDPTableSemantics, MKCopyPrefixSemantics in *.
intros cap Hcap. rewrite (PreH18 cap ltac:(lia)). apply PreH17. lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_6 : multipleKnapsack_entail_wit_6_split_goal_6.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_7 : multipleKnapsack_entail_wit_6_split_goal_7.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_8 : multipleKnapsack_entail_wit_6_split_goal_8.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_9 : multipleKnapsack_entail_wit_6_split_goal_9.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_10 : multipleKnapsack_entail_wit_6_split_goal_10.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_11 : multipleKnapsack_entail_wit_6_split_goal_11.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6_split_goal_12 : multipleKnapsack_entail_wit_6_split_goal_12.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_1 : multipleKnapsack_entail_wit_7_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_2 : multipleKnapsack_entail_wit_7_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_3 : multipleKnapsack_entail_wit_7_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold MKQueueResultSemantics, MKQueueEntriesValidForResult,
 MKQueueIndexIncreasing, MKQueueValueDecreasing, MKQueueCoversResultWindow.
repeat split; intros; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_4 : multipleKnapsack_entail_wit_7_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold MKItemResiduePrefixSemantics.
match goal with H : MKItemResidueProgressSemantics _ _ _ _ _ _ _ |- _ =>
  destruct H as [Hdone Hsame] end.
split; [intros; lia |]. intros pos Hp. split.
- intros. eapply Hdone; eauto.
- intros rem t Heq Hrem Ht Hcase. eapply Hsame; eauto. lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7_split_goal_5 : multipleKnapsack_entail_wit_7_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_8_split_goal_1 : multipleKnapsack_entail_wit_8_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold MKQueueDropSemantics.
match goal with H : MKQueueResultSemantics _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  destruct H as (Hvalid & Hinc & Hdec & Hcover & _) end.
split; [exact Hvalid |]. split; [exact Hinc |]. split; [exact Hdec |].
unfold MKQueueCoversWindow, MKQueueCoversResultWindow in *.
intros. apply Hcover; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_8_split_goal_2 : multipleKnapsack_entail_wit_8_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_8_split_goal_3 : multipleKnapsack_entail_wit_8_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_8_split_goal_4 : multipleKnapsack_entail_wit_8_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_8_split_goal_5 : multipleKnapsack_entail_wit_8_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_8_split_goal_6 : multipleKnapsack_entail_wit_8_split_goal_6.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_9_split_goal_1 : multipleKnapsack_entail_wit_9_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_9_split_goal_2 : multipleKnapsack_entail_wit_9_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_9_split_goal_3 : multipleKnapsack_entail_wit_9_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_drop_state capacity_pre.
pose proof (MKQueueDropLoopState_pop_expired_preserves_predrop
 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre ltac:(lia) ltac:(lia) Hdrop) as Hnext.
unfold MKQueueDropLoopState, MKQueueDropSemantics in *. tauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_1_split_goal_1 : multipleKnapsack_entail_wit_10_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (head = tail) by lia. subst head.
mk_slice. intros; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_1_split_goal_2 : multipleKnapsack_entail_wit_10_1_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (head = tail) by lia. subst head.
mk_slice. intros; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_1_split_goal_3 : multipleKnapsack_entail_wit_10_1_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (head = tail) by lia. subst head.
unfold MKQueuePendingSemantics, MKQueueEntriesValidAfterDrop,
 MKQueueIndexIncreasing, MKQueueValueDecreasing, MKQueueCoversWithPending.
match goal with H : MKQueueDropSemantics _ _ _ _ _ _ _ _ _ _ |- _ =>
  destruct H as (_ & _ & _ & Hcover) end.
repeat split; intros; try lia.
left. apply Hcover; assumption.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_1_split_goal_4 : multipleKnapsack_entail_wit_10_1_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_2_split_goal_1 : multipleKnapsack_entail_wit_10_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_after_drop capacity_pre current pos.
unfold MKQueueAfterDrop in Hafter.
destruct Hafter as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb).
mk_read_bound Hb.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_2_split_goal_2 : multipleKnapsack_entail_wit_10_2_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_after_drop capacity_pre current pos.
unfold MKQueueAfterDrop in Hafter.
destruct Hafter as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb).
mk_read_bound Hb.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_2_split_goal_3 : multipleKnapsack_entail_wit_10_2_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_after_drop capacity_pre current pos.
pose proof (MKQueueAfterDrop_to_MKQueuePendingState_current
 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current
 Hafter ltac:(lia)) as Hp.
unfold MKQueuePendingState, MKQueuePendingSemantics in *. tauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_2_split_goal_4 : multipleKnapsack_entail_wit_10_2_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_11_split_goal_1 : multipleKnapsack_entail_wit_11_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_11_split_goal_2 : multipleKnapsack_entail_wit_11_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_11_split_goal_3 : multipleKnapsack_entail_wit_11_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_pending_state capacity_pre.
pose proof (MKQueuePendingState_pop_dominated_tail_preserves
 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current
 Hpending ltac:(lia) ltac:(lia)) as Hnext.
unfold MKQueuePendingState, MKQueuePendingSemantics in *. tauto.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_1_split_goal_1 : multipleKnapsack_entail_wit_12_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_push capacity_pre.
unfold MKQueueState in Hresult.
destruct Hresult as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
mk_read_bound Hb.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_1_split_goal_2 : multipleKnapsack_entail_wit_12_1_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_push capacity_pre.
unfold MKQueueState in Hresult.
destruct Hresult as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
mk_read_bound Hb.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_1_split_goal_3 : multipleKnapsack_entail_wit_12_1_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_push capacity_pre.
unfold MKQueueState, MKQueueResultSemantics, MKTransitionValue in *.
intuition.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_1_split_goal_5 : multipleKnapsack_entail_wit_12_1_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_1_split_goal_7 : multipleKnapsack_entail_wit_12_1_split_goal_7.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_1_split_goal_8 : multipleKnapsack_entail_wit_12_1_split_goal_8.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_2_split_goal_1 : multipleKnapsack_entail_wit_12_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_push capacity_pre.
unfold MKQueueState in Hresult.
destruct Hresult as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
mk_read_bound Hb.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_2_split_goal_2 : multipleKnapsack_entail_wit_12_2_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_push capacity_pre.
unfold MKQueueState in Hresult.
destruct Hresult as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
mk_read_bound Hb.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_2_split_goal_3 : multipleKnapsack_entail_wit_12_2_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
mk_push capacity_pre.
unfold MKQueueState, MKQueueResultSemantics, MKTransitionValue in *.
intuition.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_2_split_goal_5 : multipleKnapsack_entail_wit_12_2_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_2_split_goal_7 : multipleKnapsack_entail_wit_12_2_split_goal_7.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_2_split_goal_8 : multipleKnapsack_entail_wit_12_2_split_goal_8.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_13_split_goal_1 : multipleKnapsack_entail_wit_13_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
eapply MKItemResidueProgressSemantics_next_residue__g09; eauto; lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_13_split_goal_2 : multipleKnapsack_entail_wit_13_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto). all: try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_14_split_goal_1 : multipleKnapsack_entail_wit_14_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (Htable : MKDPTable weights_l values_l counts_l i capacity_pre old_l_2) by mk_table.
assert (Hprogress : MKItemResidueProgress old_l_2 dp_l_2 r w v cnt capacity_pre).
{ apply MKItemResidueProgress_from_safety_semantics__g10; [|assumption].
  unfold MKItemResidueProgressSafety. repeat split; lia. }
pose proof (MKItemResidueProgress_complete_implies_MKDPTable_next_item
 weights_l values_l counts_l i capacity_pre old_l_2 dp_l_2 r w v cnt
 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(assumption) ltac:(assumption)
 ltac:(assumption) ltac:(mk_item_bounds) ltac:(lia) Htable Hprogress) as Hnext.
unfold MKDPTable, MKDPTableSemantics in *. tauto.
Qed.

Lemma proof_of_multipleKnapsack_safety_wit_15 : multipleKnapsack_safety_wit_15.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_safety_wit_15_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_safety_wit_15_split_goal_2.
Qed.

Lemma proof_of_multipleKnapsack_safety_wit_24 : multipleKnapsack_safety_wit_24.
Proof.
  unfold multipleKnapsack_safety_wit_24; left; intros.
  mk_push capacity_pre.
  pose proof (MKQueueState_head_bound _ _ _ _ _ _ _ _ _ _ _ Hresult ltac:(lia)) as Hb.
  replace (k + 1 - 1) with k in Hb by lia.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_multipleKnapsack_safety_wit_26 : multipleKnapsack_safety_wit_26.
Proof.
  unfold multipleKnapsack_safety_wit_26; left; intros.
  mk_push capacity_pre.
  pose proof (MKQueueState_head_bound _ _ _ _ _ _ _ _ _ _ _ Hresult ltac:(lia)) as Hb.
  replace (k + 1 - 1) with k in Hb by lia.
  split_pures; dump_pre_spatial; try change INT_MAX with 2147483647; try change INT_MIN with (-2147483648); lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_1 : multipleKnapsack_entail_wit_1.
Proof. aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_1_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_1_split_goal_5.
- Goal_apply proof_of_multipleKnapsack_entail_wit_1_split_goal_3.
- Goal_apply proof_of_multipleKnapsack_entail_wit_1_split_goal_4.
- Goal_apply proof_of_multipleKnapsack_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_2 : multipleKnapsack_entail_wit_2.
Proof. aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_2_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_2_split_goal_2.
- Goal_apply proof_of_multipleKnapsack_entail_wit_2_split_goal_3.
- Goal_apply proof_of_multipleKnapsack_entail_wit_2_split_goal_4.
- Goal_apply proof_of_multipleKnapsack_entail_wit_2_split_goal_5.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_3 : multipleKnapsack_entail_wit_3.
Proof.
aggressive_pre_process.
assert (Hj : j = capacity_pre + 1) by lia. subst j.
Exists qval0 qidx0 old0 dp_l_2.
split_pure_spatial.
- replace (Zlength dp_l_2) with (capacity_pre + 1) by lia.
  sep_apply (IntArray.seg_to_full (&( "dp" )) 0 (capacity_pre + 1) dp_l_2).
  sep_apply (IntArray.seg_to_full (&( "old" )) 0 (capacity_pre + 1) old0).
  sep_apply (IntArray.seg_to_full (&( "q_idx" )) 0 (capacity_pre + 1) qidx0).
  sep_apply (IntArray.seg_to_full (&( "q_val" )) 0 (capacity_pre + 1) qval0).
  simpl. rewrite !Z.add_0_r, !Z.sub_0_r. cancel.
- split_pures; dump_pre_spatial; try assumption; try lia.
  unfold MKDPTableSemantics. intros cap Hcap.
  pose proof (proj1 (Forall_Znth (eq 0) 0 dp_l_2) PreH15 cap ltac:(lia)) as Hz.
  rewrite <- Hz. apply MultipleKnapsackPrefixAnswer_zero_items. lia.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_4 : multipleKnapsack_entail_wit_4.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_5 : multipleKnapsack_entail_wit_5.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_5_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_6 : multipleKnapsack_entail_wit_6.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_2.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_3.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_4.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_5.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_6.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_7.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_8.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_9.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_10.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_11.
- Goal_apply proof_of_multipleKnapsack_entail_wit_6_split_goal_12.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_7 : multipleKnapsack_entail_wit_7.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_2.
- Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_3.
- Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_4.
- Goal_apply proof_of_multipleKnapsack_entail_wit_7_split_goal_5.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_8 : multipleKnapsack_entail_wit_8.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_8_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_8_split_goal_2.
- Goal_apply proof_of_multipleKnapsack_entail_wit_8_split_goal_3.
- Goal_apply proof_of_multipleKnapsack_entail_wit_8_split_goal_4.
- Goal_apply proof_of_multipleKnapsack_entail_wit_8_split_goal_5.
- Goal_apply proof_of_multipleKnapsack_entail_wit_8_split_goal_6.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_9 : multipleKnapsack_entail_wit_9.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_9_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_9_split_goal_2.
- Goal_apply proof_of_multipleKnapsack_entail_wit_9_split_goal_3.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_1 : multipleKnapsack_entail_wit_10_1.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_10_1_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_10_1_split_goal_2.
- Goal_apply proof_of_multipleKnapsack_entail_wit_10_1_split_goal_3.
- Goal_apply proof_of_multipleKnapsack_entail_wit_10_1_split_goal_4.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_10_2 : multipleKnapsack_entail_wit_10_2.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_10_2_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_10_2_split_goal_2.
- Goal_apply proof_of_multipleKnapsack_entail_wit_10_2_split_goal_3.
- Goal_apply proof_of_multipleKnapsack_entail_wit_10_2_split_goal_4.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_11 : multipleKnapsack_entail_wit_11.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_11_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_11_split_goal_2.
- Goal_apply proof_of_multipleKnapsack_entail_wit_11_split_goal_3.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_1 : multipleKnapsack_entail_wit_12_1.
Proof.
  unfold multipleKnapsack_entail_wit_12_1; right; intros.
  mk_push capacity_pre.
  pose proof (MKQueueState_head_transition _ _ _ _ _ _ _ _ _ _ _ Hresult ltac:(lia)) as Htrans.
  replace (k + 1 - 1) with k in Htrans by lia.
  unfold MKTransitionValue in Htrans.
  destruct Htrans as (_ & _ & _ & _ & Htrans).
  assert (Hprefix : MKItemResiduePrefixSemantics old_l_2
    (replace_Znth (r+k*w) (Znth head (replace_Znth tail current qval_l_2) 0+k*v) dp_l_2)
    r w v cnt (k+1) capacity_pre).
  { eapply MKItemResiduePrefixSemantics_after_dp_write__g09 with (pos := r+k*w); try eassumption; try reflexivity; try lia. }
  assert (Hsemantic : MKQueueResultSemantics old_l_2 (replace_Znth tail k qidx_l_2)
    (replace_Znth tail current qval_l_2) head (tail+1) r w v cnt (k+1) capacity_pre).
  { pose proof Hresult as Hstate. clear - Hstate.
    unfold MKQueueState, MKQueueResultSemantics, MKTransitionValue in Hstate |- *. tauto. }
  pose proof Hresult as Hbound.
  unfold MKQueueState in Hbound.
  destruct Hbound as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try assumption; try solve [mk_read_bound Hb]; try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_12_2 : multipleKnapsack_entail_wit_12_2.
Proof.
  unfold multipleKnapsack_entail_wit_12_2; right; intros.
  mk_push capacity_pre.
  pose proof (MKQueueState_head_transition _ _ _ _ _ _ _ _ _ _ _ Hresult ltac:(lia)) as Htrans.
  replace (k + 1 - 1) with k in Htrans by lia.
  unfold MKTransitionValue in Htrans.
  destruct Htrans as (_ & _ & _ & _ & Htrans).
  assert (Hprefix : MKItemResiduePrefixSemantics old_l_2
    (replace_Znth (r+k*w) (Znth head (replace_Znth tail current qval_l_2) 0+k*v) dp_l_2)
    r w v cnt (k+1) capacity_pre).
  { eapply MKItemResiduePrefixSemantics_after_dp_write__g09 with (pos := r+k*w); try eassumption; try reflexivity; try lia. }
  assert (Hsemantic : MKQueueResultSemantics old_l_2 (replace_Znth tail k qidx_l_2)
    (replace_Znth tail current qval_l_2) head (tail+1) r w v cnt (k+1) capacity_pre).
  { pose proof Hresult as Hstate. clear - Hstate.
    unfold MKQueueState, MKQueueResultSemantics, MKTransitionValue in Hstate |- *. tauto. }
  pose proof Hresult as Hbound.
  unfold MKQueueState in Hbound.
  destruct Hbound as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  split_pure_spatial; [entailer! |].
  split_pures; dump_pre_spatial; try assumption; try solve [mk_read_bound Hb]; try solve [mk_simple].
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_13 : multipleKnapsack_entail_wit_13.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_13_split_goal_1.
- Goal_apply proof_of_multipleKnapsack_entail_wit_13_split_goal_2.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_14 : multipleKnapsack_entail_wit_14.
Proof.
aggressive_pre_process.
- Goal_apply proof_of_multipleKnapsack_entail_wit_14_split_goal_1.
Qed.

Lemma proof_of_multipleKnapsack_entail_wit_15 : multipleKnapsack_entail_wit_15.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pure_spatial.
  - sep_apply (IntArray.full_to_undef_full (&( "dp" )) (capacity_pre + 1) dp_l).
    sep_apply (IntArray.undef_full_to_undef_seg (&( "dp" )) (capacity_pre + 1)).
    sep_apply (IntArray.undef_seg_merge_to_undef_full (&( "dp" )) 0 (capacity_pre + 1) 1001 ltac:(lia)).
    sep_apply (IntArray.full_to_undef_full (&( "old" )) (capacity_pre + 1) old_l).
    sep_apply (IntArray.undef_full_to_undef_seg (&( "old" )) (capacity_pre + 1)).
    sep_apply (IntArray.undef_seg_merge_to_undef_full (&( "old" )) 0 (capacity_pre + 1) 1001 ltac:(lia)).
    sep_apply (IntArray.full_to_undef_full (&( "q_idx" )) (capacity_pre + 1) qidx_l).
    sep_apply (IntArray.undef_full_to_undef_seg (&( "q_idx" )) (capacity_pre + 1)).
    sep_apply (IntArray.undef_seg_merge_to_undef_full (&( "q_idx" )) 0 (capacity_pre + 1) 1001 ltac:(lia)).
    sep_apply (IntArray.full_to_undef_full (&( "q_val" )) (capacity_pre + 1) qval_l).
    sep_apply (IntArray.undef_full_to_undef_seg (&( "q_val" )) (capacity_pre + 1)).
    sep_apply (IntArray.undef_seg_merge_to_undef_full (&( "q_val" )) 0 (capacity_pre + 1) 1001 ltac:(lia)).
    simpl. rewrite !Z.add_0_r. cancel.
  - dump_pre_spatial.
    assert (i = n_pre) by lia. subst i.
    eapply MKDPTable_final_capacity_implies_MultipleKnapsackAnswer;
      try eassumption; try lia; try mk_table.
Qed.
