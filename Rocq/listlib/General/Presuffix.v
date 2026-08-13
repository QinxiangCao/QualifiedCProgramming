Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import ListLib.Base.Inductive.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
Import ListNotations.

Definition is_prefix {A: Type} (l1 l2: list A): Prop := 
  exists l3, l2 = l1 ++ l3. 

Definition is_suffix {A: Type} (l1 l2: list A): Prop := 
  exists l3, l2 = l3 ++ l1. 

Definition is_sublist {A: Type} (l1 l2: list A): Prop := 
  exists l3 l4, l2 = l3 ++ l1 ++ l4. 

Notation "l1 'is_a_prefix_of' l2" := (is_prefix l1 l2) (at level 70).
Notation "l1 'is_a_suffix_of' l2" := (is_suffix l1 l2) (at level 70).
Notation "l1 'is_a_sublist_of' l2" := (is_sublist l1 l2) (at level 70).

Definition presuffix {A: Type} (l1 l2: list A): Prop :=
  l1 is_a_prefix_of l2 /\
  l1 is_a_suffix_of l2.

Definition partial_match_res {A: Type} (patn text res: list A): Prop :=
  res is_a_suffix_of text /\
  res is_a_prefix_of patn.

Definition partial_bound_res {A: Type} (patn text bound: list A): Prop :=
  (forall res, partial_match_res patn text res -> length res <= length bound).

Definition proper_presuffix {A: Type} (l1 l2: list A): Prop :=
  presuffix l1 l2 /\ length l1 < length l2.

Definition presuffix_bound {A: Type} (l1 l2: list A): Prop :=
  (forall l3, proper_presuffix l3 l2 -> presuffix l3 l1).

Definition max_proper_presuffix {A: Type} (l1 l2: list A): Prop :=
  proper_presuffix l1 l2 /\ presuffix_bound l1 l2.


Theorem prefix_ind_iff_positional {A: Type}: forall (l1 l2: list A),
  l1 is_a_prefix_of l2 <-> exists hi, l1 = firstn hi l2.
Proof.
  intros.
  split; intros.
  - destruct H as [l3 ?]; exists (length l1); subst.
    rewrite firstn_app.
    rewrite Nat.sub_diag; simpl.
    rewrite firstn_all.
    rewrite app_nil_r.
    reflexivity.
  - destruct H as [hi ?].
    exists (skipn hi l2); subst.
    rewrite firstn_skipn.
    reflexivity. 
Qed.

Theorem suffix_ind_iff_positional {A: Type}: forall (l1 l2: list A),
  l1 is_a_suffix_of l2 <-> exists lo, l1 = skipn lo l2.
Proof.
  intros.
  split; intros.
  - destruct H as [l3 ?]; exists (length l3); subst.
    rewrite skipn_app.
    rewrite Nat.sub_diag; simpl.
    rewrite skipn_all.
    reflexivity.
  - destruct H as [lo ?].
    exists (firstn lo l2); subst.
    rewrite firstn_skipn.
    reflexivity.
Qed.

Theorem sublist_ind_iff_positional {A: Type}: forall (l1 l2: list A),
  l1 is_a_sublist_of l2 <-> exists lo hi, l1 = skipn lo (firstn hi l2).
Proof.
  intros.
  split; intros.
  - destruct H as [p [q]]. 
    exists (length p), (length p + length l1); subst. 
    rewrite! firstn_app.
    replace (length p + length l1 - length p) with (length l1) by lia.
    rewrite Nat.sub_diag; simpl. 
    rewrite app_nil_r. 
    rewrite firstn_all. 
    rewrite firstn_all2 by lia.
    rewrite skipn_app. 
    rewrite Nat.sub_diag; simpl. 
    rewrite skipn_all. 
    reflexivity. 
  - destruct H as [lo [hi Heq]].
    exists (firstn lo (firstn hi l2)), (skipn hi l2); subst.
    rewrite app_assoc.
    rewrite! firstn_skipn.
    reflexivity.
Qed.

Section Presuffix.

Lemma prefix_snoc: forall {A: Type} (l0 l: list A) (a: A),
  l0 is_a_prefix_of (l ++ a :: nil) <-> l0 is_a_prefix_of l \/ l ++ a :: nil = l0.
Proof.
  intros.
  split; intros.
  + destruct H as [l' ?].
    assert (l' = nil \/ l' <> nil) by (destruct l'; [left; reflexivity | right; congruence]). 
    destruct H0; [subst; right|left]. 
    rewrite app_nil_r in H; auto. 
    apply exists_last in H0 as [? []]; subst. 
    rewrite app_assoc in H.
    apply app_inj_tail in H as []. 
    exists x; auto.
  + destruct H as [? | ?]. 
    * destruct H. 
      exists (x ++ [a]); subst. 
      rewrite app_assoc; auto. 
    * exists [].
      rewrite app_nil_r; auto.
Qed.

Lemma sublist_snor: forall {A: Type} (l0 l: list A) (a: A),
  l0 is_a_sublist_of (l ++ a :: nil) <-> l0 is_a_sublist_of l \/ l0 is_a_suffix_of (l ++ a :: nil).
Proof.
  intros.
  split; intros.
  + destruct H as [l1 [l2 ?]].
    assert (l2 = nil \/ l2 <> nil) by (destruct l2; [left; reflexivity | right; congruence]). 
    destruct H0. 
    * subst. right. 
      rewrite app_nil_r in H; auto. 
      exists l1; auto. 
    * left.
      apply exists_last in H0 as [? []]; subst. 
      rewrite! app_assoc in H. 
      apply app_inj_tail in H as []; subst. 
      exists l1, x; rewrite app_assoc; reflexivity. 
  + destruct H as [? | ?].
    * destruct H as [l1 [l2 ?]].
      exists l1, (l2 ++ [a]); subst.
      rewrite! app_assoc; auto.
    * destruct H as [l1 ?].
      exists l1, []; rewrite app_nil_r; auto.
Qed.

Lemma prefix_of_nil_inv {A: Type}: forall (l: list A),
  l is_a_prefix_of nil -> l = nil.
Proof.
  intros l [l' ?].
  destruct l.
  + reflexivity.
  + discriminate H.
Qed.

Lemma sublist_of_nil_inv {A: Type}: forall (l: list A),
  l is_a_sublist_of nil -> l = nil.
Proof.
  intros l [l' [l'' ?]].
  destruct l'.
  + eapply prefix_of_nil_inv.
    exists l''.
    symmetry in H. 
    apply app_eq_nil in H as [_ ?].
    auto.
  + discriminate H.
Qed. 

Lemma is_suffix_snoc_snoc_iff: forall {A: Type} (l1 l2: list A) a1 a2,
  (l1 ++ [a1]) is_a_suffix_of (l2 ++ [a2]) <->
  l1 is_a_suffix_of l2 /\ a1 = a2.
Proof.
  intros.
  split; intros.
  + destruct H as [l ?].
    rewrite app_assoc in H.
    apply app_inj_tail in H.
    destruct H.
    split; [eexists; eauto | congruence].
  + destruct H as [ [l ?] ?].
    exists l.
    subst.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma prefix_length: forall {A: Type} (l1 l2: list A),
  l1 is_a_prefix_of l2 ->
  length l1 <= length l2.
Proof.
  intros.
  destruct H as [? ?].
  subst.
  rewrite length_app.
  lia.
Qed.

Lemma suffix_length: forall {A: Type} (l1 l2: list A),
  l1 is_a_suffix_of l2 ->
  length l1 <= length l2.
Proof.
  intros.
  destruct H as [? ?].
  subst.
  rewrite length_app.
  lia.
Qed.

Lemma presuffix_length: forall {A: Type} (l1 l2: list A),
  presuffix l1 l2 ->
  length l1 <= length l2.
Proof.
  unfold presuffix; intros.
  apply prefix_length; tauto.
Qed.

Lemma prefix_iff: forall {A: Type} (default: A) (l1 l2: list A),
  l1 is_a_prefix_of l2 <->
  (length l1 <= length l2 /\
   forall i, 0 <= i < length l1 -> nth i l1 default = nth i l2 default)%nat.
Proof.
  intros.
  split; intros.
  + pose proof prefix_length _ _ H.
    destruct H as [? ?].
    split; [tauto |].
    intros.
    subst.
    rewrite app_nth1 by lia.
    reflexivity.
  + destruct H.
    exists (Nsublist (length l1) (length l2) l2).
    eapply (nth_ext _ _ default default).
    - rewrite length_app.
      rewrite length_sublist by lia.
      lia.
    - intros.
      destruct (le_gt_dec (length l1) n).
      * rewrite app_nth2 by lia.
        rewrite nth_sublist by lia.
        f_equal; lia.
      * rewrite app_nth1 by lia.
        symmetry; apply H0; lia.  
Qed.

Lemma prefix_iff': forall {A: Type} (l1 l2: list A),
  l1 is_a_prefix_of l2 <->
  (length l1 <= length l2 /\
   forall default i, 0 <= i < length l1 ->
                     nth i l1 default = nth i l2 default)%nat.
Proof.
  intros.
  split; intros.
  + pose proof prefix_length _ _ H.
    split; [tauto |].
    intros d.
    rewrite (prefix_iff d) in H.
    tauto.
  + destruct H.
    destruct l1.
    - exists l2.
      reflexivity.
    - specialize (H0 a).
      rewrite (prefix_iff a).
      tauto.
Qed.

Lemma suffix_iff: forall {A: Type} (default: A) (l1 l2: list A),
  l1 is_a_suffix_of l2 <->
  (length l1 <= length l2 /\
   forall i, 0 <= i < length l1 ->
             nth (length l1 - 1 - i) l1 default =
             nth (length l2 - 1 - i) l2 default)%nat.
Proof.
  intros.
  split; intros.
  + pose proof suffix_length _ _ H.
    destruct H as [? ?].
    split; [tauto |].
    intros.
    subst.
    rewrite length_app.
    rewrite app_nth2 by lia.
    f_equal. lia.
  + destruct H.
    exists (Nsublist 0 (length l2 - length l1) l2).
    eapply (nth_ext _ _ default default).
    - rewrite length_app.
      rewrite length_sublist by lia.
      lia.  
    - intros.
      destruct (le_gt_dec (length l2 - length l1) n).
      * rewrite app_nth2 by (rewrite length_sublist by lia; lia).
        rewrite length_sublist by lia.
        replace (n - (length l2 - length l1 - 0)) with
                (length l1 - 1 - (length l2 - 1 - n)) by lia.
        rewrite H0 by lia.
        f_equal; lia.
      * rewrite app_nth1 by (rewrite length_sublist by lia; lia).
        rewrite nth_sublist by lia.
        f_equal; lia.
  Qed.

Lemma suffix_iff': forall {A: Type} (l1 l2: list A),
  l1 is_a_suffix_of l2 <->
  (length l1 <= length l2 /\
   forall default i, 0 <= i < length l1 ->
             nth (length l1 - 1 - i) l1 default =
             nth (length l2 - 1 - i) l2 default)%nat.
Proof.
  intros.
  split; intros.
  + pose proof suffix_length _ _ H.
    split; [tauto |].
    intros d.
    rewrite (suffix_iff d) in H.
    tauto.
  + destruct H.
    destruct l1.
    - exists l2.
      rewrite app_nil_r.
      reflexivity.
    - specialize (H0 a).
      rewrite (suffix_iff a).
      tauto.
Qed.

Lemma is_prefix_snoc_iff: forall {A: Type} default (l1 l2: list A) a,
  (l1 ++ [a]) is_a_prefix_of l2 <->
  (length l1 < length l2 /\
   l1 is_a_prefix_of l2 /\
   a = nth (length l1) l2 default).
Proof.
  intros.
  rewrite !(prefix_iff default).
  rewrite length_app; simpl.
  split; intros.
  + destruct H.
    split; [| split; [split |]].
    - lia.
    - lia.
    - intros.
      specialize (H0 i ltac:(lia)).
      rewrite <- H0.
      rewrite app_nth1 by lia.
      reflexivity.
    - specialize (H0 (length l1) ltac:(lia)).
      rewrite <- H0.
      rewrite app_nth2 by lia.
      replace (length l1 - length l1) with 0 by lia.
      simpl.
      reflexivity.
  + destruct H as [? [[_ ?] ?]].
    split; [lia |].
    intros.
    destruct (le_gt_dec (length l1) i).
    - rewrite app_nth2 by lia.
      replace (i - length l1) with 0 by lia.
      simpl.
      rewrite H1; f_equal; lia.
    - rewrite app_nth1 by lia.
      apply H0; lia.
Qed.

Lemma prefix_trans: forall {A: Type} (l1 l2 l3: list A),
  l1 is_a_prefix_of l2 ->
  l2 is_a_prefix_of l3 ->
  l1 is_a_prefix_of l3.
Proof.
  intros.
  destruct H as [? ?], H0 as [? ?].
  exists (x ++ x0).
  subst.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma suffix_trans: forall {A: Type} (l1 l2 l3: list A),
  l1 is_a_suffix_of l2 ->
  l2 is_a_suffix_of l3 ->
  l1 is_a_suffix_of l3.
Proof.
  intros.
  destruct H as [? ?], H0 as [? ?].
  exists (x0 ++ x).
  subst.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma presuffix_trans: forall {A: Type} (l1 l2 l3: list A),
  presuffix l1 l2 ->
  presuffix l2 l3 ->
  presuffix l1 l3.
Proof.
  unfold presuffix; intros; split.
  - apply (prefix_trans _ l2); tauto.
  - apply (suffix_trans _ l2); tauto.
Qed.

Lemma prefix_total_order:
  forall {A: Type} (l1 l2 l: list A),
    l1 is_a_prefix_of l ->
    l2 is_a_prefix_of l ->
    length l1 <= length l2 ->
    l1 is_a_prefix_of l2.
Proof.
  intros ? ? ? ?.
  rewrite !prefix_iff'.
  intros [? ?] [? ?] ?.
  split; [lia |].
  intros.
  rewrite H0, H2 by lia.
  reflexivity.
Qed.

Lemma suffix_total_order:
  forall {A: Type} (l1 l2 l: list A),
    l1 is_a_suffix_of l ->
    l2 is_a_suffix_of l ->
    length l1 <= length l2 ->
    l1 is_a_suffix_of l2.
Proof.
  intros ? ? ? ?.
  rewrite !suffix_iff'.
  intros [? ?] [? ?] ?.
  split; [lia |].
  intros.
  rewrite H0, H2 by lia.
  reflexivity.
Qed.

Lemma partial_match_total_order:
  forall {A: Type} (l1 l2 patn text: list A),
    partial_match_res patn text l1 ->
    partial_match_res patn text l2 ->
    length l1 <= length l2 ->
    presuffix l1 l2.
Proof.
  intros.
  destruct H, H0.
  pose proof prefix_total_order _ _ _ H2 H3 H1.
  pose proof suffix_total_order _ _ _ H H0 H1.
  split; tauto.
Qed.

Lemma partial_match_iff:
  forall {A: Type} (res0 patn text: list A),
    partial_match_res patn text res0 ->
    partial_bound_res patn text res0 ->
    forall res,
      partial_match_res patn text res <->
      presuffix res res0.
Proof.
  intros.
  split; intros.
  + specialize (H0 _ H1).
    pose proof partial_match_total_order _ _ _ _ H1 H H0.
    tauto.
  + clear H0.
    destruct H as [? ?].
    destruct H1.
    pose proof prefix_trans _ _ _ H1 H0.
    pose proof suffix_trans _ _ _ H2 H.
    split; tauto.
Qed.

Lemma partial_match_snoc_iff:
  forall {A: Type} default (res patn text: list A) ch,
    partial_match_res patn (text ++ [ch]) res <->
    res = [] \/
    exists res',
      res = res' ++ [ch] /\
      length res' < length patn /\
      nth (length res') patn default = ch /\
      partial_match_res patn text res'.
Proof.
  intros.
  split; intros.
  + destruct (list_snoc_destruct res) as [? | [ch0 [res' ?] ] ]; subst res.
    - left.
      tauto.
    - right.
      exists res'.
      destruct H.
      apply is_suffix_snoc_snoc_iff in H.
      destruct H; subst ch0.
      split; [auto | ].
      split; [| split].
      * apply prefix_length in H0.
        rewrite length_app in H0; simpl in H0.
        lia.
      * destruct H0.
        subst patn.
        rewrite <- app_assoc.
        rewrite app_nth2 by lia.
        replace (length res' - length res') with 0 by lia.
        simpl app.
        reflexivity.
      * split; auto.
        eapply prefix_trans; [ | apply H0].
        exists [ch]; reflexivity.
  + destruct H as [? | [? [? ?] ] ].
    - subst.
      split.
      * exists (text ++ [ch]).
        rewrite app_nil_r.
        reflexivity.
      * exists patn.
        reflexivity.
    - destruct H0 as [? [? [? ?] ]].
      subst.
      split; auto.
      * apply is_suffix_snoc_snoc_iff.
        tauto.
      * rewrite (is_prefix_snoc_iff default).
        tauto.
Qed.

Lemma prefix_iff_sublist {A: Type}:
  forall (l1 l2: list A),
    l1 is_a_prefix_of l2 <->
    (exists j, j = length l1 /\ l1 = Nsublist 0 j l2).
Proof.
  split; intros.
  - unfold is_prefix in H.
    destruct H as [l3 H].
    exists (length l1).
    pose proof length_app l1 l3.
    subst; split; try lia.
    rewrite Nsublist_split_app_l; try lia.
    rewrite Nsublist_self; easy.
  - destruct H as [j [? ?]].
    pose proof (f_equal (@length A) H0).
    rewrite length_sublist' in H1.
    unfold is_prefix.
    exists (Nsublist j (length l2) l2).
    rewrite <- Nsublist_self at 1 by eauto.
    rewrite (Nsublist_split 0 (length l2) j); try lia.
    rewrite H0; auto.
Qed.

Lemma suffix_iff_sublist {A: Type}:
  forall (l1 l2: list A),
    l1 is_a_suffix_of l2 <->
    (exists i, i = length l2 - length l1 /\ l1 = Nsublist i (length l2) l2).
Proof.
  split; intros.
  - unfold is_suffix in H.
    destruct H as [l3 H].
    exists (length l3).
    pose proof length_app l3 l1.
    subst; split; try lia.
    rewrite Nsublist_split_app_r with (len:= length l3); try lia.
    rewrite H0.
    replace (length l3 - length l3) with 0 by lia.
    replace (length l3 + length l1 - length l3) with (length l1) by lia.
    rewrite Nsublist_self; easy.
  - destruct H as [i [? ?]].
    pose proof (f_equal (@length A) H0).
    rewrite length_sublist in H1 by lia.
    unfold is_suffix.
    exists (Nsublist 0 i l2).
    rewrite <- Nsublist_self at 1 by eauto.
    rewrite (Nsublist_split 0 (length l2) i); try lia.
    rewrite H0; easy.
Qed.

Lemma nil_prefix {A: Type}:
  forall (l: list A), [] is_a_prefix_of l.
Proof.
  intros; unfold is_prefix.
  exists l; easy.
Qed.

Lemma nil_suffix {A: Type}:
  forall (l: list A), [] is_a_suffix_of l.
Proof.
  intros; unfold is_suffix.
  exists l. rewrite app_nil_r; easy.
Qed.

Lemma nil_presuffix {A: Type}:
  forall (l: list A), presuffix [] l.
Proof. 
  intros; unfold presuffix.
  split; [apply nil_prefix | apply nil_suffix].
Qed.

Lemma presuffix_nil_iff {A: Type}:
  forall (l:list A), presuffix l [] <-> l = [].
Proof.
  intros; split; intros.
  - unfold presuffix in H.
    pose proof prefix_length _ _ (proj1 H).
    simpl in H0.
    apply length_zero_iff_nil; lia.
  - subst; apply nil_presuffix.
Qed.

Lemma partial_match_nil {A: Type}:
  forall (patn text: list A),
    partial_match_res patn text [].
Proof.
  intros; unfold partial_match_res.
  split; [apply nil_suffix | apply nil_prefix].
Qed.

Lemma presuffix_partial_match {A: Type} (p t l0 l1: list A):
  partial_match_res p t l0 ->
  presuffix l1 l0 ->
  partial_match_res p t l1.
Proof.
  unfold partial_match_res, presuffix; intros.
  destruct H; destruct H0.
  split.
  - eapply suffix_trans; eauto.
  - eapply prefix_trans; eauto.
Qed.

Lemma prefix_app_iff {A: Type}:
  forall (l1 l2 l3: list A),
    l1 is_a_prefix_of l2 <->
    length l1 <= length l2 /\ l1 is_a_prefix_of (l2 ++ l3).
Proof.
  split; intros.
  - split. apply prefix_length, H.
    unfold is_prefix in *.
    destruct H. exists (x ++ l3).
    rewrite H. rewrite app_assoc; auto.
  - destruct H as [H0 H1].
    rewrite prefix_iff' in *.
    destruct H1 as [_ H1]; split; try easy.
    intros. specialize (H1 default i H).
    rewrite app_nth1 in H1 by lia; auto.
Qed.

Lemma suffix_app_iff {A: Type}:
  forall (l1 l2 l3: list A),
    l1 is_a_suffix_of l2 <->
    length l1 <= length l2 /\ l1 is_a_suffix_of (l3 ++ l2) .
Proof.
  split; intros.
  - split. apply suffix_length, H.
    unfold is_suffix in *.
    destruct H. exists (l3 ++ x).
    rewrite H. rewrite app_assoc; auto.
  - destruct H as [H0 H1].
    rewrite suffix_iff' in *.
    destruct H1 as [_ H1]; split; try easy.
    intros. specialize (H1 default i H).
    rewrite length_app in H1.
    rewrite app_nth2 in H1 by lia.
    replace (length l3 + length l2 - 1 - i - length l3) 
      with (length l2 - 1 - i) in H1 by lia; auto.
Qed.

Lemma prefix_sublist_iff {A: Type}:
  forall (l0 l: list A) i,
    0 <= i <= length l ->
    l0 is_a_prefix_of (Nsublist 0 i l) <->
    length l0 <= i /\ l0 is_a_prefix_of l.
Proof.
  intros.
  rewrite <- (Nsublist_self l) at 2; eauto.
  rewrite (Nsublist_split 0 (length l) i); try lia.
  pose proof length_sublist 0 i l ltac:(lia).
  replace (i - 0) with i in H0 by lia.
  rewrite <- H0 at 2.
  apply prefix_app_iff.
Qed.

Lemma suffix_sublist_cons_iff {A: Type}:
  forall (l0 l: list A) i,
    1 <= i <= length l ->
    l0 is_a_suffix_of (Nsublist 1 i l) <->
    length l0 <= i - 1 /\ l0 is_a_suffix_of (Nsublist 0 i l).
Proof.
  intros.
  rewrite (Nsublist_split 0 i 1); try lia.
  pose proof length_sublist 1 i l ltac:(lia).
  rewrite <- H0.
  apply suffix_app_iff.
Qed.

End Presuffix.