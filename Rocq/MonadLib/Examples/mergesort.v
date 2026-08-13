Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From SetsClass Require Import SetsClass.
From FP Require Import SetsFixedpoints.
Require Import MonadLib.StateRelMonad.StateRelMonad.


Local Open Scope Z_scope.
Import SetsNotation.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

Export MonadNotation.
Local Open Scope monad.




Section  merge_monad.

Definition merge_body:
  list Z * list Z * list Z ->
  MONAD (CntOrBrk  (list Z * list Z * list Z) (list Z)) :=
  fun '(l1, l2, l3) =>
    match l1, l2 with 
    | nil, _ => return (by_break (l3 ++ l2))
    | _, nil => return (by_break (l3 ++ l1))
    | x :: l1', y :: l2' =>
        choice
          (test' (x <= y);; return (by_continue (l1', l2, l3 ++ x :: nil)))
          (test' (y <= x);; return (by_continue (l1, l2', l3 ++ y :: nil)))
  end.

  Definition merge_rel l l0 :=
    repeat_break merge_body (l, l0, nil).

  Definition merge_from_mid_rel l1 l2 l3 := 
    repeat_break merge_body (l1, l2, l3).

End  merge_monad.


Section split_rec_rel_monad.

  Definition reversepair : ((list Z) * (list Z)) -> MONAD ((list Z) * (list Z)) :=
    fun '(p,q) => return (q,p).

  Definition split_rec_rel_f  (W : ((list Z) * (list Z) * (list Z)) ->  MONAD ((list Z) * (list Z))) 
                          : ((list Z) * (list Z) * (list Z)) -> MONAD ((list Z) * (list Z)) :=
    fun '(x, p, q) => match x with 
                      | nil => return (p, q)
                      | xh :: x' => x <- W (x', q,  xh::p) ;;
                                    reversepair x
                      end.

  Definition split_rec_rel' : ((list Z) * (list Z) * (list Z)) -> MONAD ((list Z) * (list Z)) := 
    Lfix split_rec_rel_f.

  Definition split_rec_rel l1 l2 l3: MONAD ((list Z) * (list Z)) := 
    split_rec_rel' (l1, l2, l3).

  Definition split_rel x :=
    split_rec_rel' (x, nil, nil).

  Lemma split_rec_rel_unfold: split_rec_rel' == split_rec_rel_f split_rec_rel'.
  Proof.
    intros.
    unfold split_rec_rel'.
    apply Lfix_fixpoint'.
    unfold split_rec_rel_f.
    mono_cont_auto.
  Qed. 


  Lemma split_rec_rel_eval_xnil: forall p q P, 
    P -@ (split_rec_rel' (nil, p, q)) -⥅ 
    P ♯ (p, q).
  Proof.
    intros.
    erewrite (program_para_equiv (split_rec_rel_unfold)).
    unfold split_rec_rel_f.
    apply  highret_eval2.
  Qed.


  Lemma split_rel_eval_xnotnil: forall z x p q,
    forall P X, safeExec P (split_rec_rel' (z::x, p, q)) X ->
                safeExec P (x <- split_rec_rel' (x, q, z::p) ;; reversepair x ) X.
  Proof. 
    unfold split_rel, reversepair. intros.
    erewrite (program_para_equiv (split_rec_rel_unfold)) in H.
    unfold split_rec_rel_f in H.
    apply H.
  Qed.

  Lemma bind_2_reversepair_equiv_Id: 
    (fun p => z <- reversepair p ;; reversepair z) == ret.
  Proof.
    intros [x y].
    unfold reversepair;sets_unfold.
    intros s [u v] s'.
    split;intros.
    - destruct H as ([x' y'] & s'' & ? & ? ).
      unfold_monad in H. destruct H.
      unfold_monad in H0. destruct H0.
      inversion H; inversion H0. subst.
      unfold_monad. auto.
    - unfold_monad in H. destruct H.
      inversion H;subst.
      do 3 eexists.
      split;eauto.
      cbn. sets_unfold. unfold_monad. auto.
  Qed.

End split_rec_rel_monad.


Section mergesort_monad.
  Definition mergesortrec_f  (W :  (list Z) -> MONAD (list Z) ) 
                        : ((list Z) -> MONAD (list Z)) :=
    fun x => '(p1, q1) <- split_rel x ;; 
                      match q1 with 
                      | nil => return p1
                      | _ :: _  =>  p2 <- W (p1) ;; 
                                    q2 <- W (q1) ;; 
                                    merge_rel p2 q2
                      end.

  Definition mergesortrec := Lfix (mergesortrec_f).

  Definition mergesortrec_loc0: ((list Z) * (list Z)) -> MONAD (list Z) :=
    fun x => match x with
             | (p1, q1) =>
                      match q1 with 
                      | nil => return p1
                      | _ :: _  =>  p2 <- mergesortrec p1 ;; 
                                    q2 <- mergesortrec q1 ;; 
                                    merge_rel p2 q2
                      end
             end.

  Definition mergesortrec_loc1 q1: list Z -> MONAD (list Z) :=
    fun p2 => q2 <- mergesortrec q1 ;; 
              merge_rel p2 q2.

  Definition mergesortrec_loc2 p2: list Z -> MONAD (list Z) :=
    fun q2 => merge_rel p2 q2.

  Lemma mergesortrec_unfold: mergesortrec == mergesortrec_f mergesortrec.
  Proof.
    intros.
    unfold mergesortrec.
    apply Lfix_fixpoint'.
    unfold mergesortrec_f.
    mono_cont_auto.
  Qed.

End mergesort_monad.

Fixpoint incr_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ incr_aux l0 y
  end.

Definition incr (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => incr_aux l0 x
  end.

Section general_mergesort_monad.

  Definition ext_sort (l: list Z): MONAD (list Z) :=
    fun _ l' _ => Permutation l l' /\ incr l'.

  Definition ext_split (l: list Z): MONAD (list Z * list Z) :=
    fun _ '(l0, l1) _ =>   Permutation l (l0 ++ l1).

  Definition gmergesortrec_f  (W :  (list Z) -> MONAD (list Z) ) 
                        : ((list Z) -> MONAD (list Z)) :=
    fun x => 
      choice
        (ext_sort x)
        (test'(Zlength x >= 2)%Z;;
         '(p1, q1) <- ext_split x ;; 
         p2 <- W (p1) ;; 
         q2 <- W (q1) ;; 
         merge_rel p2 q2).

  Definition gmergesortrec := Lfix (gmergesortrec_f).

  Definition gmergesortrec_loc0: ((list Z) * (list Z)) -> MONAD (list Z) :=
    fun x => match x with
             | (p1, q1) =>
                 p2 <- gmergesortrec p1 ;; 
                 q2 <- gmergesortrec q1 ;; 
                 merge_rel p2 q2
             end.

  Definition gmergesortrec_loc1 q1: list Z -> MONAD (list Z) :=
    fun p2 => q2 <- gmergesortrec q1 ;; 
              merge_rel p2 q2.

  Lemma gmergesortrec_unfold: gmergesortrec == gmergesortrec_f gmergesortrec.
  Proof.
    intros.
    unfold gmergesortrec.
    apply Lfix_fixpoint'.
    unfold gmergesortrec_f.
    mono_cont_auto.
  Qed.

End general_mergesort_monad.


Section mergesort_algorithm_correctness.



Theorem merge_perm:
  forall l1 l2,
    Hoare (fun _ => True) 
          (merge_rel l1 l2) 
          (fun r _  => Permutation (l1 ++ l2) r).
Proof.
  intros.
  unfold merge_rel.
  eapply Hoare_conseq_pre.
  2: 
  apply (Hoare_repeat_break _
           (fun '(l1', l2', l3') _ =>
              Permutation (l1 ++ l2) (l1' ++ l2' ++ l3'))).
  { intros. simpl. rewrite app_nil_r. reflexivity. } 

  intros [[l1' l2'] l3'].
  unfold merge_body.
  destruct l1' as [ | x l1']; [| destruct l2' as [| y l2']].
  + hoare_auto.
    rewrite H; simpl.
    apply Permutation_app_comm.
  + hoare_auto.
    rewrite H.
    rewrite Permutation_app_comm.
    reflexivity.
  + hoare_auto. 
    - rewrite H0.
      rewrite ! app_assoc.
      rewrite (Permutation_app_comm _ [x]).
      reflexivity.
    - rewrite H0.
      apply Permutation_app; [reflexivity |].
      rewrite ! app_assoc.
      rewrite (Permutation_app_comm _ [y]).
      reflexivity.
Qed.

Lemma incr_app_cons: forall l1 x l2,
  incr (l1 ++ [x]) ->
  incr (x :: l2) ->
  incr (l1 ++ x :: l2).
Proof.
  intros.
  simpl in H0.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv1: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (l1 ++ [x]).
Proof.
  intros.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv2: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (x :: l2).
Proof.
  intros.
  simpl.
  induction l1; simpl in *.
  + tauto.
  + apply IHl1.
    destruct l1; simpl in *; tauto.
Qed.

Theorem merge_incr:
  forall l1 l2,
    incr l1 ->
    incr l2 ->
    Hoare (fun _ => True) (merge_rel l1 l2) (fun r _ => incr r).
Proof.
  intros.
  unfold merge_rel.
  eapply Hoare_conseq_pre.
  2:
  apply (Hoare_repeat_break _
           (fun '(l1', l2', l3') _ => 
              incr (l3' ++ l1') /\
              incr (l3' ++ l2'))).
  1: {
    tauto.
  }
  clear l1 l2 H H0.
  intros [[l1 l2] l3].
  unfold merge_body.
  destruct l1 as [ | x l1]; [| destruct l2 as [| y l2]].
  + hoare_auto. tauto.
  + hoare_auto. tauto.
  + hoare_auto.
    - split.
      * rewrite <- app_assoc.
        tauto.
      * rewrite <- app_assoc.
        simpl.
        destruct H0.
        apply incr_app_cons_inv1 in H0.
        apply incr_app_cons_inv2 in H1.
        apply incr_app_cons; simpl in *; tauto.
    - split.
      * rewrite <- app_assoc.
        simpl.
        destruct H0.
        apply incr_app_cons_inv1 in H1.
        apply incr_app_cons_inv2 in H0.
        apply incr_app_cons; simpl in *; tauto.
      * rewrite <- app_assoc.
        tauto.
Qed.

Theorem functional_correctness_merge:
  forall l1 l2,
    incr l1 ->
    incr l2 ->
    Hoare (fun _ => True)
          (merge_rel l1 l2)
          (fun l3 _ => Permutation (l1 ++ l2) l3 /\ incr l3).
Proof.
  intros.
  apply Hoare_conj.
  + apply merge_perm.
  + apply merge_incr; tauto.
Qed.


Theorem functional_correctness_split:
  forall l,
    Hoare (fun _ => True)
          (split_rel l)
          (fun '(l1, l2) _ => Permutation l (l1 ++ l2) /\ (0 <= length l1 - length l2 <= 1)%nat).
Proof.
  intros.
  unfold split_rel, split_rec_rel'.
  apply Hoare_conseq_post with (Q2 := fun '(l1, l2) _ => 
  Permutation ((fst (fst (l, @nil Z, @nil Z))) ++ (snd (fst (l, [], @nil Z))) ++ (snd (l, @nil Z, []))) (l1 ++ l2) /\ 
  (@length Z (snd (fst (l, [], @nil Z))) <= length l1 /\
   @length Z (snd (l, @nil Z, [])) <= length l2 /\
   length l2 - @length Z (snd (l, @nil Z, [])) <= length l1 - @length Z (snd (fst (l, [], @nil Z))) <= S (length l2 - @length Z (snd (l, @nil Z, []))))%nat).
  { simpl. rewrite app_nil_r. 
    intros [l1  l2];intros.
    split; try tauto.
    lia. }
  hoare_fix_nolv_auto ((list Z * list Z)%type * list Z)%type.
  simpl;intros * H [[l0 l1] l2]. simpl.
  destruct l0.
  - hoare_auto. split;auto. lia.
  - eapply Hoare_bind;[apply H |].
    simpl.
    intros [? ?].
    unfold reversepair.
    hoare_auto.
    split.
    + rewrite (Permutation_app_comm l1 l2).
      rewrite !Permutation_middle.
      destruct H0 as [H0 _].
      rewrite H0.
      apply Permutation_app_comm.
    + lia. 
Qed.

Lemma split_rel_refine_ext_split : 
forall l, 
  split_rel l ⊆ ext_split l.
Proof.
  intros.
  intros x (l1,l2) x' H.
  unfold ext_split.
  pose proof functional_correctness_split l x (l1,l2) x'.
  simpl in H0.
  apply H0;auto.
Qed.

Theorem functional_correctness_mergesort:
  forall l,
    Hoare ATrue (mergesortrec l) (fun l0 _ => Permutation l l0 /\ incr l0).
Proof.
  intros.
  unfold mergesortrec, ATrue.
  hoare_fix_nolv_auto (list Z).
  simpl.
  intros.
  unfold mergesortrec_f.
  eapply Hoare_bind;[apply functional_correctness_split | ].
  intros [l1 l2].
  destruct l2.
  - hoare_auto. 
    rewrite app_nil_r in H0. destruct H0.  split;auto.
    simpl in H1.
    destruct l1;[cbn;auto | ].
    destruct l1;[ | simpl in H1; lia].
    cbn. auto.
  - apply Hoare_stateless;intros.
    eapply Hoare_bind;[apply H| ].
    intros lp;simpl.
    apply Hoare_stateless;intros.
    eapply Hoare_bind;[apply H| ].
    intros lq;simpl.
    apply Hoare_stateless;intros.
    eapply Hoare_conseq_post.
    2: { apply functional_correctness_merge;try tauto. }
    destruct H0.
    destruct H1. destruct H2.
    intros lr ? [? ?].
    rewrite H0.
    rewrite H1, H2.
    tauto.
Qed.

End mergesort_algorithm_correctness.



Section gmergesort_algorithm_correctness.




Lemma ext_sort_fact:
  forall l,
    Hoare (ATrue) (ext_sort l) (fun l0 _ => Permutation l l0 /\ incr l0).
Proof.
  unfold Hoare, ext_sort; sets_unfold.
  intros.
  tauto.
Qed.

Lemma ext_split_fact:
  forall l,
    Hoare (ATrue) (ext_split l) (fun '(l1, l2) _ => Permutation l (l1 ++ l2)).
Proof.
  unfold Hoare, ext_split; sets_unfold.
  intros.
  tauto.
Qed.

Theorem functional_correctness_gmergesort:
  forall l,
    Hoare ATrue (gmergesortrec l) (fun l0 _ => Permutation l l0 /\ incr l0).
Proof.
  intros.
  unfold gmergesortrec, ATrue.
  hoare_fix_nolv_auto (list Z).
  simpl.
  intros.
  unfold gmergesortrec_f.
  hoare_auto.
  - apply ext_sort_fact.
  - eapply Hoare_bind.
    eapply ext_split_fact.
    intros [l1 l2].
    apply Hoare_stateless;intros.
    eapply Hoare_bind;[ apply H |].
    intros lp;simpl.
    apply Hoare_stateless;intros.
    eapply Hoare_bind;[ apply H |].
    intros lq;simpl.
    apply Hoare_stateless;intros.
    eapply Hoare_conseq_post.
    2: { apply functional_correctness_merge;try tauto. }
    destruct H2. destruct H3.
    intros lr ? [? ?].
    rewrite H1.
    rewrite H2, H3.
    tauto.
Qed.

End gmergesort_algorithm_correctness.