From SimpleC.SL Require Import Mem.
From AUXLib Require Import Decision.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import SetsClass.SetsClass.
Import SetsNotation.

Local Open Scope Z.
Local Open Scope sets.

Module ZInterval.

(* [Ico lo hi] is the left-closed, right-open integer interval [lo, hi). *)
Definition Ico (lo hi : Z) : Z -> Prop :=
  fun p => lo <= p < hi.

Lemma Ico_union_Ico :
  forall lo mid hi,
    lo <= mid <= hi ->
    Ico lo mid ∪ Ico mid hi == Ico lo hi.
Proof.
  intros lo mid hi Hrange p.
  unfold Ico.
  sets_unfold.
  lia.
Qed.

Lemma Ico_singleton :
  forall lo,
    Ico lo (lo + 1) == [lo].
Proof. unfold Ico. sets_unfold. lia. Qed.

Lemma Ico_empty :
  forall lo hi,
    hi <= lo ->
    Ico lo hi == ∅.
Proof. unfold Ico. sets_unfold. lia. Qed.

Definition Ico_dec lo hi p : Decision (p ∈ Ico lo hi).
Proof.
  unfold Ico.
  destruct (Z_le_dec lo p) as [Hlo | Hlo];
    destruct (Z_lt_dec p hi) as [Hhi | Hhi].
  - left. split; assumption.
  - right. intros [_ H]. lia.
  - right. intros [H _]. lia.
  - right. intros [H _]. lia.
Defined.

End ZInterval.

Definition mem_dom (m : Mem.mem) : Mem.addr -> Prop :=
  fun p => m p <> Mem.Noperm.

Definition mem_pred_dom (P : Mem.mem -> Prop) (D : Mem.addr -> Prop) : Prop :=
  forall m, P m -> mem_dom m == D.

Definition mem_overwrite_on
    (D : Mem.addr -> Prop) (f : Mem.mem -> Mem.mem) : Prop :=
  (forall m p, ~ p ∈ D -> f m p = m p) /\
  (forall m1 m2 p, p ∈ D -> f m1 p = f m2 p).

#[export] Instance mem_pred_dom_congr :
  Proper (Sets.equiv ==> Sets.equiv ==> iff) mem_pred_dom.
Proof.
  unfold mem_pred_dom.
  intros P1 P2 HP D1 D2 HD.
  split; intros H m HPm; specialize (H m).
  - rewrite H; [rewrite HD; reflexivity | apply HP, HPm].
  - rewrite H; [rewrite HD; reflexivity | apply HP, HPm].
Qed.

#[export] Instance mem_overwrite_on_congr :
  Proper (Sets.equiv ==> eq ==> iff) mem_overwrite_on.
Proof.
  unfold mem_overwrite_on.
  intros D1 D2 HD f ? <-. sets_unfold. sets_unfold in HD. firstorder.
Qed.

Lemma in_mem_dom :
  forall m p,
    p ∈ mem_dom m <-> m p <> Mem.Noperm.
Proof.
  intros m p.
  split.
  - intros H. hnf in H.
    destruct (m p) eqn:Hp; congruence.
  - intros H H'. congruence.
Qed.

Lemma notin_mem_dom :
  forall m p,
    ~ p ∈ mem_dom m <-> m p = Mem.Noperm.
Proof.
  unfold mem_dom.
  intros m p.
  split.
  - intros H. sets_unfold in H.
    destruct (m p); try reflexivity; exfalso; apply H; discriminate.
  - intros H Hnon. exact (Hnon H).
Qed.

Lemma mem_join_dom :
  forall m1 m2 m,
    Mem.mem_join m1 m2 m ->
    mem_dom m == mem_dom m1 ∪ mem_dom m2.
Proof.
  intros m1 m2 m Hjoin p.
  rewrite mem_join_iff in Hjoin.
  specialize (Hjoin p).
  unfold mem_dom.
  sets_unfold.
  destruct (m1 p), (m2 p); try contradiction;
    destruct (m p); try contradiction; try subst; tauto.
Qed.

Lemma mem_join_dom_disjoint :
  forall m1 m2 m,
    Mem.mem_join m1 m2 m ->
    mem_dom m1 ∩ mem_dom m2 == ∅.
Proof.
  intros m1 m2 m Hjoin p.
  rewrite mem_join_iff in Hjoin.
  specialize (Hjoin p).
  unfold mem_dom.
  sets_unfold.
  destruct (m1 p), (m2 p); try contradiction; tauto.
Qed.

Lemma mem_overwrite_on_emptyset :
  forall f,
    mem_overwrite_on ∅ f <->
    (forall m p, f m p = m p).
Proof.
  intros f.
  unfold mem_overwrite_on. sets_unfold. firstorder.
Qed.

Lemma mem_overwrite_ext D f m1 m2
    (D_dec : forall p, Decision (p ∈ D)) :
    mem_overwrite_on D f ->
    (forall p, ~ p ∈ D -> m1 p = m2 p) ->
    f m1 = f m2.
Proof.
  intros [Houtside Hinside] Heq.
  apply functional_extensionality. intros p.
  destruct (D_dec p) as [Hin | Hout].
  - apply Hinside. exact Hin.
  - rewrite !Houtside by exact Hout.
    apply Heq. exact Hout.
Qed.

Lemma mem_overwrite_empty_ext D f m
    (D_dec : forall p, Decision (p ∈ D)) :
    mem_overwrite_on D f ->
    mem_dom m ⊆ D ->
    f m = f Mem.empty_mem.
Proof.
  intros Hoverwrite Hdom.
  eapply mem_overwrite_ext; eauto.
  intros p Hout.
  apply notin_mem_dom.
  intros Hin.
  apply Hout, Hdom, Hin.
Qed.

Lemma mem_join_overwrite_left D f m1 m2 m
    (D_dec : forall p, Decision (p ∈ D)) :
    mem_overwrite_on D f ->
    D ⊆ mem_dom m1 ->
    Mem.mem_join m1 m2 m ->
    Mem.mem_join (f m1) m2 (f m).
Proof.
  intros [Houtside Hinside] Hdom Hjoin.
  pose proof (proj1 (Mem.mem_join_iff m1 m2 m) Hjoin) as Hjoin_point.
  apply Mem.mem_join_iff. intros p.
  destruct (D_dec p) as [Hin | Hout].
  - assert (Hframe : m2 p = Mem.Noperm).
    {
      apply notin_mem_dom.
      intros Hm2.
      pose proof (mem_join_dom_disjoint m1 m2 m Hjoin p) as Hdisjoint.
      sets_unfold in Hdisjoint.
      apply (proj1 Hdisjoint).
      split; [apply Hdom, Hin | exact Hm2].
    }
    rewrite Hframe.
    rewrite (Hinside m1 m p Hin).
    destruct (f m p); simpl; auto.
  - rewrite !Houtside by exact Hout.
    apply Hjoin_point.
Qed.

Lemma mem_join_overwrite_right D f m1 m2 m
    (D_dec : forall p, Decision (p ∈ D)) :
    mem_overwrite_on D f ->
    D ⊆ mem_dom m2 ->
    Mem.mem_join m1 m2 m ->
    Mem.mem_join m1 (f m2) (f m).
Proof.
  intros Hoverwrite Hdom Hjoin.
  apply Mem.mem_join_comm.
  eapply mem_join_overwrite_left; eauto.
  apply Mem.mem_join_comm. exact Hjoin.
Qed.

Lemma mem_join_overwrite_Ico_left lo hi f m1 m2 m :
    mem_overwrite_on (ZInterval.Ico lo hi) f ->
    ZInterval.Ico lo hi ⊆ mem_dom m1 ->
    Mem.mem_join m1 m2 m ->
    Mem.mem_join (f m1) m2 (f m).
Proof.
  apply (mem_join_overwrite_left
    (ZInterval.Ico lo hi) f m1 m2 m (ZInterval.Ico_dec lo hi)).
Qed.

Lemma mem_join_overwrite_Ico_right lo hi f m1 m2 m :
    mem_overwrite_on (ZInterval.Ico lo hi) f ->
    ZInterval.Ico lo hi ⊆ mem_dom m2 ->
    Mem.mem_join m1 m2 m ->
    Mem.mem_join m1 (f m2) (f m).
Proof.
  apply (mem_join_overwrite_right
    (ZInterval.Ico lo hi) f m1 m2 m (ZInterval.Ico_dec lo hi)).
Qed.

Lemma mem_pred_dom_includes :
  forall P D m,
    mem_pred_dom P D ->
    P m ->
    D ⊆ mem_dom m.
Proof.
  intros P D m Hdom HP p Hp.
  unfold mem_pred_dom in Hdom.
  apply (Hdom m HP p).
  exact Hp.
Qed.

Lemma in_mem_pred_dom :
  forall P D m p,
    mem_pred_dom P D ->
    P m ->
    p ∈ D ->
    m p <> Mem.Noperm.
Proof.
  intros P D m p Hdom HP HD.
  unfold mem_pred_dom in Hdom.
  specialize (Hdom m HP p).
  apply Hdom.
  exact HD.
Qed.

Lemma notin_mem_pred_dom :
  forall P D m p,
    mem_pred_dom P D ->
    P m ->
    ~ p ∈ D ->
    m p = Mem.Noperm.
Proof.
  intros P D m p Hdom HP Hnot.
  apply notin_mem_dom.
  intros Hmem.
  apply Hnot.
  specialize (Hdom m HP p).
  apply Hdom.
  exact Hmem.
Qed.

Lemma mem_domain_eq_iff_dom :
  forall m1 m2,
    Mem.mem_domain_eq m1 m2 <->
    mem_dom m1 == mem_dom m2.
Proof.
  intros m1 m2.
  rewrite Mem.mem_domain_eq_iff.
  split; intros H p.
  - split; intros Hnon Hnoperm; apply Hnon, H, Hnoperm.
  - rewrite <- !notin_mem_dom, H. reflexivity.
Qed.

Lemma mem_pred_dom_domain_eq :
  forall P D m1 m2,
    mem_pred_dom P D ->
    P m1 ->
    P m2 ->
    Mem.mem_domain_eq m1 m2.
Proof.
  intros P D m1 m2 Hdom HP1 HP2.
  apply mem_domain_eq_iff_dom.
  unfold mem_pred_dom in Hdom.
  apply Hdom in HP1, HP2.
  rewrite HP1, HP2. reflexivity.
Qed.
