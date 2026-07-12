Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid. 
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare.

Import Monad MonadNotation SetsNotation.
Local Open Scope sets.
Local Open Scope order_scope.
Import MonadErr.

Definition safe  {Σ A: Type} (σ : Σ) (c:  program Σ A) (X: A -> Σ -> Prop) :=
  σ ∈ (weakestpre c X).

Definition safeExec {Σ: Type} {A: Type} (P: Σ -> Prop) (c: program Σ A) (X: A -> Σ -> Prop) :=
  exists σₕ, P σₕ /\ safe σₕ c X.

Definition result_state {Σ A: Type} (P: Σ -> Prop) (c: program Σ A): A -> Σ -> Prop :=
  fun a s1 => exists s0, P s0 /\  c.(nrm) s0 a s1.   

(* angelic reduction with return value a *)
Definition hs_eval {Σ: Type}  {A: Type} (c : program Σ A) (P : Σ -> Prop) (P' : (Σ -> Prop)) (a : A) := 
  forall (σₕ : Σ), P σₕ -> exists (σₕ' : Σ), c.(nrm) σₕ a σₕ' /\ P' σₕ'.

(* ⥅  rightarrowplus *)
Notation " P '-@' s '-⥅' P' '♯' a " := (hs_eval s P P' a) (at level 70, no associativity).

Notation " P '-@' s '-→' P' " := (exists a,  hs_eval s P P' a) (at level 70, no associativity).


Import MonadNotation.
Local Open Scope monad.
(**********************************************************************************)
(*    safe exec  rules                                                            *)
(**********************************************************************************)
Ltac splits :=
  match goal with 
  | |- _ /\ _ => split;splits
  | |- _ => idtac end.

Local Ltac my_destruct Σ H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | Σ => let σ := fresh "σₕ" in destruct H as [σ H];my_destruct Σ H
              | program Σ ?A => let c := fresh "c" in destruct H as [c H];my_destruct Σ H
              | _ => destruct H as [? H];my_destruct Σ H
              end
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              my_destruct Σ H;
              my_destruct Σ H0
  | _ \/ _ => destruct H as [H | H];
              my_destruct Σ H
  | _ => (discriminate || contradiction  || idtac)
  end.

Section  hs_eval_rules.
  Context {Σ: Type}.

  Definition asrt : Type :=  Σ -> Prop.

  Ltac destructs H := my_destruct Σ H.

  Lemma hs_eval_equiv_angelic_triple: forall {A : Type} (c1: program Σ A)  (P  : Σ -> Prop) a Q, 
    P -@ c1 -⥅ Q ♯ a <->
    valid_angelic_triple P c1 (fun r σ => r = a /\ Q σ).
  Proof.
    intros.
    unfold hs_eval, valid_angelic_triple. unfold_monad.
    split;intros.
    - specialize (H _ H0) as (? & ? & ?).
      sets_unfold. eexists. splits;eauto.
    - specialize (H _ H0) as (? & ? & ? & ? & ?). subst.
      sets_unfold. sets_unfold in H.
      eexists. splits;eauto.
  Qed. 

  Lemma ret_eq : forall {A : Type} (s: Σ) s0 (a a0: A),
    (ret a).(nrm) s a0 s0 <-> s0 = s /\ a0 = a.
  Proof.
    unfold_monad. intros; tauto.
  Qed.


  Lemma highstependret_derive : forall  {A : Type} (c1: program Σ A)  (P  : Σ -> Prop) a P',
  P -@ c1 -⥅ (P' a) ♯ a ->
  (forall X, safeExec P (c1) X ->  safeExec (P' a) (ret a) X).
  Proof.
    intros.
    unfold hs_eval, safeExec, safe in *.
    destructs H0. 
    simpl in *.
    specialize (H _ H0) as [σₕ' [? ?]].
    exists σₕ'.
    splits;auto.
    rewrite wp_ret.
    eapply wp_spec;eauto.
  Qed.


  Lemma highstepend_derive : forall  (c1: program Σ unit)  (P  : Σ -> Prop) P',
  P -@ c1 -→ P' ->
  (forall X, safeExec P (c1) X ->  safeExec P' (ret tt) X).
  Proof.
    intros.
    destruct H.
    destruct x.
    pose proof (highstependret_derive c1  P tt ((fun _ => P')) H).
    eapply H1;eauto.
  Qed.

  
  Lemma highstepbind_derive : forall  {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) a P',
  P -@ c1 -⥅ (P') ♯ a ->
  (forall X, safeExec P (x <- c1;; c2 x) X ->  safeExec (P') (c2 a) X).
  Proof.
    intros.
    unfold hs_eval, safeExec, safe in *. 
    destructs H0.
    rewrite wp_bind in H1.
    specialize (H _ H0) as [σₕ' [? ?]].
    eexists.
    split;eauto.
    eapply wp_spec with (Q:= (fun a : A => weakestpre (c2 a) X)); [ apply H | ].
    auto.
  Qed.


  Lemma highstepseq_derive : forall  {A B: Type} (c1: program Σ A) (c2:  program Σ B) (P P': Σ -> Prop),
    P -@ c1 -→ P'  ->
    (forall X, safeExec P (c1 ;; c2) X ->  safeExec P' c2 X).
  Proof.
    intros.
    destruct H.
    unfold seq in H0.
    pose proof (highstepbind_derive c1 (fun _ => c2) P x (P') H).
    eapply H1;eauto.
  Qed. 


  Lemma highret_eval1 : forall {A: Type}  (P  : Σ -> Prop) (a: A), 
    P -@ (ret a) -→ P.
  Proof.
    intros. cbv. intros.
    eexists. splits;eauto.
  Qed.

  Lemma highret_eval2 : forall {A: Type}  (P  : Σ -> Prop) (a: A), 
    P -@ (ret a) -⥅ P ♯ a.
  Proof.
    intros. cbv. intros.
    eexists. splits;eauto.
  Qed.

  Lemma hsevalbind_derive : forall  {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) P' a Q b,
  P -@ c1 -⥅ (P' a) ♯ a ->  (P' a) -@ (c2 a) -⥅ (Q b) ♯ b ->
  P -@ (x  <- c1 ;; c2 x) -⥅ (Q b) ♯ b.
  Proof.
    unfold hs_eval. intros.
    specialize (H _ H1).
    destructs H.
    specialize (H0 _ H2).
    destructs H0.
    eexists.
    splits;eauto.
    do 2 eexists.
    split;eauto.
  Qed.

  Lemma hsevalbind_derive' : forall  {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) P' a Q b,
  P -@ c1 -⥅ P' ♯ a ->  P' -@ (c2 a) -⥅ Q ♯ b ->
  P -@ (x  <- c1 ;; c2 x) -⥅ Q ♯ b.
  Proof.
    unfold hs_eval. intros.
    specialize (H _ H1).
    destructs H.
    specialize (H0 _ H2).
    destructs H0.
    eexists.
    splits;eauto.
    do 2 eexists.
    split;eauto.
  Qed.

  Lemma hsevalchoice_left_derive:
    forall {A: Type} (c1 c2: program Σ A) (P  : Σ -> Prop) Q a,
      P -@ c1 -⥅ Q ♯ a ->
      P -@ (choice c1 c2) -⥅ Q ♯ a.
  Proof.
    intros.
    unfold hs_eval.
    intros.
    specialize (H _ H0) as [? [? ?]].
    eexists.
    split; [left; apply H | apply H1].
  Qed.

  Lemma hsevalchoice_right_derive:
    forall {A: Type} (c1 c2: program Σ A) (P: Σ -> Prop) Q a,
      P -@ c2 -⥅ Q ♯ a ->
      P -@ (choice c1 c2) -⥅ Q ♯ a.
  Proof.
    intros.
    unfold hs_eval.
    intros.
    specialize (H _ H0) as [? [? ?]].
    eexists.
    split; [right; apply H | apply H1].
  Qed.

  Lemma hsevaltestpure_derive:
    forall (P: Σ -> Prop) (Q: Prop) a,
      Q -> P -@ (testPure Q) -⥅ P ♯ a.
  Proof.
    intros.
    unfold hs_eval, testPure. simpl.
    intros.
    eauto.
  Qed.

  Lemma hsevalassert_derive:
    forall (P: Σ -> Prop) (Q: Prop) a,
      Q -> P -@ (assert Q) -⥅ P ♯ a.
  Proof.
    intros.
    unfold hs_eval, assert. simpl.
    intros.
    eauto.
  Qed.
  
  Lemma hs_eval_proequiv: forall {A : Type} (c1 c2: program Σ A)  (P  Q: Σ -> Prop) a,
  c1 == c2 ->
  P -@ c1 -⥅ Q ♯ a ->
  P -@ c2 -⥅ Q ♯ a.
  Proof.
    unfold hs_eval. intros.
    specialize (H0 _ H1).
    destructs H0.
    eexists.
    split;eauto.
    eapply H;eauto.
  Qed.

End hs_eval_rules.

Section exec_rules.

  Context {Σ: Type}.

  Ltac destructs H := my_destruct Σ H.


  Lemma safeExec_ex : forall {A B: Type} (P: A -> Σ -> Prop) (c:  program Σ B) X,
  (exists a, safeExec (P a) (c) X) <->  safeExec (fun σ => exists a, P a σ) (c) X.
  Proof.
    unfold safeExec;intros;split;intros.
    - destruct H as (? & ? & ? & ?).
      eexists.
      split;eauto.
    - destruct H as (? & (? & ?) & ?).
      do 2 eexists.
      split;eauto.
  Qed.

  Lemma safeExec_coqprop : forall {A: Type} (B: Prop) (P: Σ -> Prop) (c:  program Σ A) X,
  (safeExec (fun s => B /\ P s) (c) X) <->  B /\ safeExec P (c) X.
  Proof.
    unfold safeExec;intros;split;intros.
    - destruct H as (? & ? & ?).
      split;[tauto | ].
      exists x.
      tauto.
    - destruct H as (? & ? & ?).
      exists x.
      tauto.
  Qed.
  
  Lemma safeExec_pre {A: Type} (c: program Σ A) (P1 P2: Σ -> Prop) X:
    (forall st, P1 st -> P2 st) ->
    safeExec P1 c X ->
    safeExec P2 c X.
  Proof.
    unfold safeExec, safe; intros Hx [s [H1 H2]].
    exists s; split; auto.
  Qed.

  Lemma safeExec_X_subset {A: Type} (c: program Σ A) (P: Σ -> Prop) X1 X2:
    X1 ⊆ X2 ->
    safeExec P c X1 ->
    safeExec P c X2.
  Proof.
    unfold safeExec, safe; intros Hx [s [H1 H2]].
    exists s; split; auto.
    eapply wp_conseq;eauto.
  Qed.


  Lemma safeExec_proequiv: forall {A : Type} (c1 c2: program Σ A)  (P  : Σ -> Prop) X,
  c1 == c2 ->
  safeExec P c1 X -> safeExec P c2 X.
  Proof.
    unfold safeExec. intros.
    destructs H0.
    eexists.
    split;eauto.
    unfold safe in *.
    intros.
    rewrite wp_progequiv;eauto.
  Qed.

  Lemma safeExec_choice_l {A: Type}:
    forall (c0 c1: program Σ A) X (s: Σ -> Prop),
      safeExec s (choice c0 c1) X -> safeExec s c0 X.
  Proof.
    unfold safeExec,  safe.
    intros.
    destruct H as [σ [? ?]].
    exists σ.
    split; [tauto |].
    rewrite wp_choice in H0.
    rewrite Sets_intersect_included1 in H0.
    auto.
  Qed.
  
  Lemma safeExec_choice_r {A: Type}:
    forall (c0 c1: program Σ A) X (s: Σ -> Prop),
      safeExec s (choice c0 c1) X -> safeExec s c1 X.
  Proof.
    unfold safeExec,  safe.
    intros.
    destruct H as [σ [? ?]].
    exists σ.
    split; [tauto |].
    rewrite wp_choice in H0.
    rewrite Sets_intersect_included2 in H0.
    auto.
  Qed.

  Lemma safeExec_test: forall (Q: Prop) P (X: unit -> Σ -> Prop),
    Q ->
    safeExec P (assume!! Q) X -> safeExec P (ret tt) X.
  Proof.
    unfold safeExec, safe. intros.
    destructs H0.
    eexists.
    split;eauto.
    rewrite wp_assume_coqprop in H1;auto.
    rewrite wp_ret.
    auto.
  Qed.

  Lemma safeExec_testst: forall (Q: Σ -> Prop) (P: Σ -> Prop) (X: unit -> Σ -> Prop),
    (forall st, P st -> Q st) ->
    safeExec P (assume Q) X -> safeExec P (ret tt) X.
  Proof.
    unfold safeExec, safe. intros.
    destructs H0.
    eexists.
    split;eauto.
    rewrite wp_assume in H1.
    rewrite wp_ret.
    apply H1.
    auto.
  Qed.

  Lemma safeExec_any: forall (Q: Type) P (X: Q -> Σ -> Prop) q,
    safeExec P (any Q) X -> safeExec P (ret q) X.
  Proof.
    unfold safeExec, safe. intros.
    destructs H.
    eexists.
    split;eauto.
    rewrite wp_any in H0.
    sets_unfold in H0.
    rewrite wp_ret.
    apply H0.
  Qed.

  Lemma safeExec_get: forall {A: Type} (Pa: Σ -> A -> Prop) (P: Σ -> Prop) (X: A -> Σ -> Prop) a, 
  (forall s, P s -> Pa s a) ->
    safeExec P (get Pa) X -> safeExec P (ret a) X.
  Proof. 
    unfold safeExec, safe. intros.
    destructs H0.
    eexists.
    split;eauto.
    rewrite wp_get in H1.
    sets_unfold in H1.
    rewrite wp_ret.
    apply H1;auto.
  Qed.

  Lemma safeExec_get': forall {A: Type} (f: Σ -> A) (P: Σ -> Prop) (X: A -> Σ -> Prop) a, 
    (forall s, P s -> a = f s) ->
    safeExec P (get' f) X -> safeExec P (ret a) X.
  Proof. 
    unfold safeExec, safe. intros.
    destructs H0.
    eexists.
    split;eauto.
    rewrite wp_get' in H1.
    sets_unfold in H1.
    rewrite wp_ret.
    apply H1;auto.
  Qed.

  Lemma safeExec_update' : forall (f: Σ -> Σ) (P: Σ -> Prop) (X: unit -> Σ -> Prop),
    safeExec P (update' f) X -> safeExec (fun s => exists s0, s = f s0 /\ P s0) (ret tt) X.
  Proof.
    unfold safeExec, safe. intros.
    destructs H.
    exists (f σₕ).
    split;eauto.
    rewrite wp_update' in H0.
    sets_unfold in H0.
    rewrite wp_ret.
    apply H0;auto.
  Qed.

  Lemma safeExec_update : forall (R: Σ -> Σ -> Prop) (P: Σ -> Prop) (X: unit -> Σ -> Prop),
    (forall s, P s -> exists s', R s s') ->
    safeExec P (update R) X -> safeExec (fun s => exists s0, R s0 s /\ P s0) (ret tt) X.
  Proof.
    unfold safeExec, safe. intros R P X Hex H.
    destructs H.
    destruct (Hex σₕ H) as [σₕ' HR].
    exists σₕ'.
    split; [ exists σₕ; auto | ].
    rewrite wp_update in H0.
    sets_unfold in H0.
    rewrite wp_ret.
    apply H0; auto.
  Qed.

  Lemma safeExec_assert_aux: forall (Q: Prop) P (X: unit -> Σ -> Prop),
    safeExec P (assert Q) X -> safeExec (fun s => Q /\ P s) (ret tt) X.
  Proof.
    unfold safeExec, safe. intros.
    destructs H.
    rewrite wp_assert in H0.
    sets_unfold in H0.
    exists σₕ.
    split;[tauto | ].
    rewrite wp_ret.
    sets_unfold.
    tauto.
  Qed.

  Lemma safeExec_assert: forall (Q: Prop) P (X: unit -> Σ -> Prop),
    safeExec P (assert Q) X -> Q /\ safeExec P (ret tt) X.
  Proof.
    intros.
    apply safeExec_coqprop.
    apply safeExec_assert_aux;auto.
  Qed.

  Lemma safeExec_assertS: forall (Q: Σ -> Prop) P (X: unit -> Σ -> Prop),
    safeExec P (assertS Q) X -> safeExec (fun s => Q s /\ P s) (ret tt) X.
  Proof.
    unfold safeExec, safe. intros.
    destructs H.
    rewrite wp_assertS in H0.
    sets_unfold in H0.
    exists σₕ.
    split;[tauto | ].
    rewrite wp_ret.
    sets_unfold.
    tauto.
  Qed.

  (* primitive rule *)
  Lemma safeExec_bind_reta  : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P : Σ -> Prop) P' a,
    (forall X, safeExec P c1 X ->  safeExec (P') (ret a) X) ->
    (forall X, safeExec P (x <- c1 ;; c2 x) X -> safeExec (P') (c2 a) X).
  Proof.
    intros.
    unfold safeExec, safe in *.
    destructs H0.
    rewrite wp_bind in H1.
    specialize (H (fun a : A => weakestpre (c2 a) X) (ltac:(exists σₕ; auto))).
    destructs H.
    exists σₕ0.
    split;eauto.
    rewrite wp_ret in H2.
    auto. 
  Qed.

  Lemma safeExec_bind_reta_target: forall {A B : Type}
    (c1 : program Σ  A) (c2 : A -> program Σ B)
    (P P' : Σ  -> Prop) (a : A) (c : program Σ  B),
  (forall X, safeExec P c1 X -> safeExec P' (return a) X) ->
  forall X,
    safeExec P (x <- c1 ;; c2 x) X ->
    c = c2 a ->
    safeExec P' c X.
  Proof.
    intros * Hret X Hbind Heq.
    subst c.
    eapply safeExec_bind_reta.
    - exact Hret.
    - exact Hbind.
  Qed.

  Lemma safeExec_bind_partial_target: forall {A B : Type}
    (c1 c1': program Σ  A) (c2 : A -> program Σ B)
    (P P' : Σ  -> Prop) (c : program Σ  B),
  (forall X, safeExec P c1 X -> safeExec P' c1' X) ->
  forall X,
    safeExec P (x <- c1 ;; c2 x) X ->
    c = (x <- c1' ;; c2 x) ->
    safeExec P' c X.
  Proof.
    intros * Hret X Hbind Heq.
    subst c.
    unfold safeExec, safe in *.
    destructs Hbind.
    rewrite wp_bind in H.
    specialize (Hret (fun a : A => weakestpre (c2 a) X) (ltac:(eexists;eauto))) as [? [? ?]]. 
    eexists;split;eauto.
    rewrite wp_bind.
    auto.
  Qed.

  Lemma safeExec_bind'  : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P : Σ -> Prop) P',
    (forall X, safeExec P c1 X -> exists a, safeExec (P')  (ret a) X) ->
    (forall X, safeExec P (x <- c1 ;; c2 x) X -> exists a, safeExec (P') (c2 a) X).
  Proof.
    intros.
    unfold safeExec, safe in *.
    destructs H0.
    rewrite wp_bind in H1.
    specialize (H (fun a : A => weakestpre (c2 a) X) (ltac:(exists σₕ; auto))).
    destructs H.
    exists x , σₕ0.
    split;eauto.
    rewrite wp_ret in H2.
    auto. 
  Qed.

  Lemma safeExec_bind : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P : Σ -> Prop) ,
    forall X, safeExec P (x <- c1 ;; c2 x) X ->
    exists X', safeExec P c1 X' /\
    (forall P' a, safeExec P'  (ret a) X' -> 
              safeExec P' (c2 a) X).
  Proof.
    intros.
    unfold safeExec in H.
    destructs H.
    unfold safe in H0.
    exists (fun (r : A) (x : Σ) => c1.(nrm) σₕ r x).
    unfold safeExec.
    splits;eauto.
    { eexists.
      split;eauto.
      unfold safe.
      apply wp_self.
      rewrite wp_bind in H0.
      eapply wp_spec_err;eauto.
    }
    intros.
    destructs H1.
    eexists.
    split;eauto.
    unfold safe in *.
    rewrite wp_ret in H2.
    rewrite wp_bind in H0.
    sets_unfold in H2.
    simple eapply wp_spec in H2;eauto.
    auto. 
  Qed. 


  Lemma safeExec_conseq: forall {A: Type} (P' P: Σ -> Prop) (c: program Σ A)  X,
    safeExec P c X ->
    (forall s, P s -> P' s) ->
    safeExec P' c X.
  Proof.
    unfold safeExec, safe; intros.
    destruct H as [hs [Ps Hc]].
    exists hs; split; auto.
  Qed.
  

  Lemma safeExec_test_bind: forall {A: Type} (Q: Prop) (c: program Σ A) P X,
    Q ->
    safeExec P (assume!! Q;; c) X ->
    safeExec P c X.
  Proof.
    intros * H.
    eapply safeExec_bind_reta with (a:= tt).
    intros *.
    apply safeExec_test;auto.
  Qed.

  Lemma safeExec_testst_bind: forall {A: Type} (Q: Σ -> Prop) (c: program Σ A) (P: Σ -> Prop) X,
    (forall st, P st -> Q st) ->
    safeExec P (assume Q;; c) X ->
    safeExec P c X.
  Proof.
    intros * H.
    eapply safeExec_bind_reta with (a:= tt).
    intros *.
    apply safeExec_testst;auto.
  Qed.

  Lemma safeExec_any_bind: forall {A: Type} (Q: Type) (c: Q -> program Σ A) (P: Σ -> Prop) X a,
    safeExec P (a <- any Q;; c a) X ->
    safeExec P (c a) X.
  Proof.
    intros * H.
    eapply safeExec_bind_reta with (a:= a);auto.
    intros *.
    apply safeExec_any;auto.
    auto.
  Qed.

  Lemma safeExec_get_bind {A B: Type} (a: A) (Pa: Σ -> A -> Prop) (P: Σ -> Prop) (c: A -> program Σ B) X:
    (forall s, P s -> Pa s a) ->
    safeExec P (a0 <- get Pa;; c a0) X -> safeExec P (c a) X.
  Proof.
    intros * H.
    eapply safeExec_bind_reta with (a:= a);auto.
    intros *.
    apply safeExec_get;auto.
  Qed.

  Lemma safeExec_get'_bind {A B: Type} (f: Σ -> A) (a: A) (P: Σ -> Prop) (c: A -> program Σ B) X:
    (forall s, P s -> a = f s) ->
    safeExec P (a0 <- get' f;; c a0) X -> safeExec P (c a) X.
  Proof.
    intros * H.
    eapply safeExec_bind_reta with (a:= a); auto.
    intros *.
    apply safeExec_get'; auto.
  Qed.

  Lemma safeExec_update'_bind {B: Type} (f: Σ -> Σ) (P: Σ -> Prop) (c:program Σ B) X:
    safeExec P (update' f;; c) X ->
    safeExec (fun s => exists s0, s = f s0 /\ P s0) c X.
  Proof.
    intros * H.
    eapply safeExec_bind_reta  with (a:= tt) in H.
    exact H.
    intros *.
    apply safeExec_update';auto.
  Qed.

  Lemma safeExec_update_bind {B: Type} (R: Σ -> Σ -> Prop) (P: Σ -> Prop) (c: program Σ B) X:
    (forall s, P s -> exists s', R s s') ->
    safeExec P (update R;; c) X ->
    safeExec (fun s => exists s0, R s0 s /\ P s0) c X.
  Proof.
    intros * Hex H.
    eapply safeExec_bind_reta with (a:= tt) in H.
    exact H.
    intros *.
    apply safeExec_update; auto.
  Qed.


  Lemma safeExec_assert_seq : forall {A: Type}  (B : Prop) (c: program Σ A) (P : Σ -> Prop) ,
    forall X, safeExec P (assert B ;; c) X ->
    B /\ safeExec P c X.
  Proof.
    intros * H.
    apply safeExec_coqprop.
    eapply safeExec_bind_reta  with (a:= tt) in H.
    exact H.
    intros *.
    apply safeExec_assert_aux;auto.
  Qed.

  Lemma safeExec_assertS_seq : forall {A: Type}  (B : Σ -> Prop) (c: program Σ A) (P : Σ -> Prop) ,
    forall X, safeExec P (assertS B ;; c) X ->
    safeExec (fun s => B s /\ P s) c X.
  Proof.
    intros * H.
    eapply safeExec_bind_reta  with (a:= tt) in H.
    exact H.
    intros *.
    apply safeExec_assertS;auto.
  Qed.

  Lemma safeExec_monad_Atrue_finnal: forall  {A: Type} (m: program unit A),
    ~ m.(err) tt ->
    safeExec ATrue m (fun r x => m.(nrm) tt r x).
  Proof.
    intros.
    unfold safeExec, ATrue, safe.
    exists tt.
    splits;auto.
    apply wp_self;auto.
  Qed.

  Lemma safeExec_ret_Atrue_finnal: forall  {A: Type}  (m: program Σ A) (l : A) (σ: Σ) ,
    safeExec ATrue (ret l) (fun r x => m.(nrm) σ r x) ->
    exists σ', m.(nrm) σ l σ'.
  Proof.
    unfold safeExec,safe; unfold_monad.
    intros.
    destructs H. 
    eapply wp_spec with (a:= l) (s2:= σₕ)  in H0;[ | auto].
    exists σₕ.
    auto.
    simpl. auto.
  Qed.

End  exec_rules.

#[export] Instance safeExec_X_subset_impl_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (eq ==> Sets.included ==> Basics.impl) (@safeExec Σ A P).
Proof.
  unfold Proper, respectful.
  intros; subst.
  hnf; apply safeExec_X_subset; auto.
Qed.

#[export] Instance safeExec_programequiv_iff_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (equiv ==> eq ==>  iff) (@safeExec Σ A P).
Proof.
  unfold Proper, respectful.
  intros. subst y0. split. 
  apply safeExec_proequiv. auto.
  apply safeExec_proequiv. symmetry. auto.
Qed.


#[export] Instance hseval_programequiv_Proper
  {Σ: Type} {A: Type}:
  Proper (equiv ==> eq ==> eq ==> eq ==> iff ) (@hs_eval Σ A).
Proof.
  unfold Proper, respectful.
  intros. subst y0 y1 y2. split.
  apply hs_eval_proequiv. auto.
  apply hs_eval_proequiv. symmetry. auto.
Qed.

Lemma  program_para_equiv {Σ: Type} {A B: Type}: forall 
  (f1 f2: A -> program Σ B),
  f1 == f2 -> forall x, f1 x == f2 x.
Proof.
  intros.
  apply H.
Qed.

Arguments program_para_equiv {Σ} {A B}%_type_scope [f1] [f2].

Ltac __prove_by_one_abs_step x :=
  match goal with
  | H: safeExec ?P1 (bind ?c11 ?c12) ?X |- safeExec ?P2 ?c2 ?X =>
      unify (c12 x) c2; 
      refine (highstepbind_derive _ _ _ x P2 _ X H);
      clear H
  end.

Tactic Notation "prove_by_one_abs_step" uconstr(x) :=
  __prove_by_one_abs_step x.

Ltac abs_choice_left :=
  match goal with 
  | |- ?P -@ (choice ?c1 ?c2) -⥅ ?Q ♯ ?a => apply hsevalchoice_left_derive
  | |- _ => fail 1 "choice_left error, expected hseval/choice"
  end.

Ltac abs_choice_right :=
  match goal with 
  | |- ?P -@ (choice ?c1 ?c2) -⥅ ?Q ♯ ?a => apply hsevalchoice_right_derive
  | |- _ => fail 1 "choice_right error, expected hseval/choice"
  end.

Ltac abs_test_step :=
  match goal with
  | |- hs_eval (testPure _) _ _ _ => apply hsevaltestpure_derive
  | |- hs_eval (bind (testPure _) _) ?P ?Q ?a =>
         refine (hsevalbind_derive' _ _ _
                   P tt Q a _ _);
          [ apply hsevaltestpure_derive | ]
  | |- hs_eval ((testPure _) ;; _) ?P ?Q ?a =>
         refine (hsevalbind_derive' _ _ _
                   P tt Q a _ _);
          [ apply hsevaltestpure_derive | ]
  | |- _ => fail 1 "test error, expected hseval/assume!!"
  end.

Ltac abs_assert_step :=
  match goal with
  | |- hs_eval (assert _) _ _ _ => apply hsevalassert_derive
  | |- hs_eval (bind (assert _) _) _ _ _ =>
          refine (hsevalbind_derive _ _ _
                    (fun _ => ATrue) tt (fun _ => ATrue) _ _ _);
          [ apply hsevalassert_derive | ]
  | |- hs_eval ((assert _) ;; _) _ _ _ =>
          refine (hsevalbind_derive _ _ _
                    (fun _ => ATrue) tt (fun _ => ATrue) _ _ _);
          [ apply hsevalassert_derive | ]
  | |- _ => fail 1 "test error, expected hseval/assert"
  end.

Ltac abs_ret_step :=
  apply highret_eval2.

Ltac safe_step H := prog_nf in H;
  match type of H with
  | safeExec _ ((assert _) ;;  _) _ =>
      apply safeExec_assert_seq in H; destruct H as [? H]; prog_nf in H; try safe_step H
  | safeExec _ ((assume!! _ ) ;;  _) _ =>
      apply safeExec_test_bind in H; [prog_nf in H; try safe_step H | auto]
  | safeExec _ ((assume _ ) ;; _) _ =>
      apply safeExec_testst_bind in H; [prog_nf in H; try safe_step H | auto]
  | _ => fail 1 "no pattern in hypothesis, expected safeExec/assume or safeExec/assert"
  end.

Ltac safe_choice_l H :=
  prog_nf in H;
  match type of H with
  | safeExec _ (choice _ _) _ =>
      apply safeExec_choice_l in H; prog_nf in H; try safe_step H
  | _ => fail 1 "no pattern in hypothesis, expected safeExec/choice"
  end.

Ltac safe_choice_r H :=
  prog_nf in H;
  match type of H with
  | safeExec _ (choice _ _) _ =>
      apply safeExec_choice_r in H; prog_nf in H; try safe_step H
  | _ => fail 1 "no pattern in hypothesis, expected safeExec/choice"
  end.

Ltac safe_equiv :=
  match goal with
  | H: safeExec ?P ?c1 ?X 
    |-  safeExec ?P ?c2 ?X => eapply (safeExec_proequiv c1 c2 P X); eauto
  | |- _ =>  fail 1 "expected safeExec/safeExec"
  end.  


Section  safeexec_Hoare_composition_rules.
  
  Context {Σ: Type}.

  Ltac destructs H := my_destruct Σ H.

  Lemma safeExec_result_state {A: Type} (P: Σ -> Prop) (c: program Σ A):
    (exists s, P s /\ ~ err c s) ->
    safeExec P c (result_state P c).
  Proof.
    unfold safeExec, result_state, safe.
    intros [s [HP ?]].
    exists s; splits; auto.
    sets_unfold. split;auto. intros a s' ?.
    exists s; tauto.
  Qed.

  Lemma Hoare_result_state {A: Type} (P: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop):
    Hoare P c Q ->
    result_state P c ⊆ Q.
  Proof.
    unfold Hoare, result_state; sets_unfold; intros.
    destruct H0 as [s0 [? ?]].
    eapply H; eauto.
  Qed.

  Lemma Hoare_safeexec_compose {A: Type} (P1 : Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop):
    Hoare P1 c Q ->
    forall (P2: Σ -> Prop) (a: A) (σ : Σ),
    safeExec P2 (return a) (c.(nrm) σ) -> 
    σ ∈ P1 ->
    (exists σ', Q a σ' /\ P2 σ').
  Proof.
    unfold Hoare, safeExec, safe.
    intros. 
    destructs H0.
    eapply wp_spec with (a:= a) (s2:= σₕ) in H2.
    destruct H.
    specialize (H a σ _ H1 H2).
    eexists. eauto.
    unfold_monad;auto.
  Qed.
  
End  safeexec_Hoare_composition_rules.
