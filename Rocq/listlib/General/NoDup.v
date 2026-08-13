Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import Permutation.

Lemma Nodup_exists_repetition: forall {A: Type} (l: list A),
  ~ NoDup l -> 
  exists x l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3.
Proof.
  intros A l.
  induction l as [|a l IH].
  - intro H; exfalso; apply H; constructor.
  - intros; rewrite NoDup_cons_iff in H. 
    assert (In a l \/ ~ NoDup l) by tauto; clear H. 
    destruct H0.
    + apply in_split in H. destruct H as [l1 [l2 H]].
      exists a, nil, l1, l2. 
      simpl; rewrite H; auto.
    + apply IH in H. destruct H as [x [l1 [l2 [l3 H]]]].
      exists x, (a :: l1), l2, l3.
      simpl; rewrite H; auto.
Qed.

Lemma Nodup_split_constructors :
  forall {A: Type} (p1 p2 : list A) (e : A),
    NoDup (p1 ++ e :: p2) ->
    ~ In e p1 /\ ~ In e p2.
Proof.
  intros. 
  apply NoDup_remove_2 in H. 
  rewrite in_app_iff in H. 
  tauto.
Qed.

Lemma Nodup_app_comm: forall {A: Type} (l1 l2: list A),
  NoDup (l1 ++ l2) ->
  NoDup (l2 ++ l1).
Proof.
  intros A l1 l2 H.
  eapply Permutation_NoDup; [ | exact H].
  apply Permutation_app_comm.
Qed.

(* 对于一个没有重复元素的集合，我们能够把它的所有可能子集无遗漏地收集到一个列表里面 *)
Lemma Nodup_all_sublists {A: Type} (l: list A):
  NoDup l -> exists ll : list (list A),
    (forall x, In x ll -> NoDup x /\ incl x l) /\
    (forall y, NoDup y -> incl y l -> exists x, In x ll /\ Permutation x y).
Proof.
  induction l as [|a l IH]; intros Hnd.
  - exists (nil :: nil); split.
    + intros x H; destruct H as [H | []]; subst.
      split; [constructor|intros ? []].
    + intros y Hnodup Hincl.
      destruct y as [|b y]; [|exfalso; destruct (Hincl b); left; auto].
      exists nil; split; [simpl; auto|constructor].
  - inversion Hnd as [|? ? Hnotin Hnd_tail]; subst.
    destruct (IH Hnd_tail) as [ll [Hsound Hcomplete]].
    exists (ll ++ map (cons a) ll). split.
    + intros x H.
      apply in_app_iff in H as [H | H].
      * apply Hsound in H as [Hnodup Hincl].
        split; auto. 
        intros z Hz; right; apply Hincl; auto.
      * apply in_map_iff in H as [y [Hx Hy]]; subst x.
        apply Hsound in Hy as [Hnodup Hincl].
        split; [constructor; auto|].
        intros b Hb; destruct Hb as [Hb | Hb]; subst; [left|right]; auto.
    + intros y Hnodup Hincl.
      destruct (classic (In a y)) as [Ha | Ha].
      * apply in_split in Ha as [y1 [y2 Hy]]; subst y.
        assert (Hnodup' : NoDup (y1 ++ y2)) by (apply NoDup_remove in Hnodup as []; auto).
        assert (Hincl' : incl (y1 ++ y2) l).
        {
          intros b Hb.
          assert (b <> a) by (intro Heq; subst b; apply NoDup_remove_2 in Hnodup; contradiction).
          assert (Hborig : In b (y1 ++ a :: y2)) by (rewrite !in_app_iff in *; simpl in *; tauto).
          apply Hincl in Hborig as [Hb' | Hb']; subst; [contradiction|auto].
        }
        destruct (Hcomplete (y1 ++ y2) Hnodup' Hincl') as [x [Hin_ll Hperm_tail]].
        exists (a :: x); split.
        ** apply in_app_iff; right; apply in_map_iff.
           exists x; split; auto.
        ** eapply Permutation_trans;
           [constructor; exact Hperm_tail
           |rewrite Permutation_middle; reflexivity].
      * assert (Hincl' : incl y l) by (intros b Hb; specialize (Hincl b Hb) as [|]; subst; auto; contradiction).
        destruct (Hcomplete y Hnodup Hincl') as [x [Hin_ll Hperm]].
        exists x; split; [apply in_app_iff; left; auto|auto]. 
Qed.