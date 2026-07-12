Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
From SetsClass Require Import SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare.

Import Monad SetsNotation MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Definition safe  {Σ A: Type} (σ : Σ) (c:  program Σ A) (X: A -> Σ -> Prop) :=
  σ ∈ (weakestpre c X).

Definition safeExec {Σ: Type} {A: Type} (P: Σ -> Prop) (c: program Σ A) (X: A -> Σ -> Prop) :=
  exists σₕ, P σₕ /\ safe σₕ c X.

Definition result_state {Σ A: Type} (P: Σ -> Prop) (c: program Σ A): A -> Σ -> Prop :=
  fun a s1 => exists s0, P s0 /\ c s0 a s1. 

(* angelic reduction with return value a *)
Definition hs_eval {Σ: Type}  {A: Type} (c : program Σ A) (P : Σ -> Prop) (P' : (Σ -> Prop)) (a : A) := 
  forall (σₕ : Σ), P σₕ -> exists (σₕ' : Σ), c σₕ a σₕ' /\ P' σₕ'.

(* ⥅  rightarrowplus *)
Notation " P '-@' s '-⥅' P' '♯' a " := (hs_eval s P P' a) (at level 70, no associativity).

Notation " P '-@' s '-→' P' " := (exists a,  hs_eval s P P' a) (at level 70, no associativity).


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
      sets_unfold in H. eexists. splits;eauto.
  Qed. 
  
  Lemma highstepbind_derive : forall {A B: Type} (c1: program Σ A) (c2: A -> program Σ B) (P  : Σ -> Prop) a P',
    P -@ c1 -⥅ (P') ♯ a ->
    (forall X, safeExec P (x <- c1 ;; c2 x) X -> safeExec P' (c2 a) X).
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
    (forall X, safeExec P (c1 ;; c2) X -> safeExec P' c2 X).
  Proof.
    intros.
    destruct H.
    unfold_monad in H0.
    pose proof (highstepbind_derive c1 (fun _ => c2) P x ((P')) H).
    eapply H1;eauto.
  Qed.
  
  Lemma hseval_stateless_ret: forall  {A: Type}  (m: program unit A) (a : A),
    m tt a tt ->
    ATrue -@ m -⥅ ATrue ♯ a.
  Proof.
    intros. hnf. 
    exists tt.
    destruct σₕ.
    easy.
  Qed.


  Lemma ret_eq : forall {A : Type} (s: Σ) s0 (a a0: A),
    (ret a) s a0 s0 <-> s = s0 /\ a0 = a.
  Proof.
    unfold_monad; tauto.
  Qed.

  Lemma highstependret_derive : forall  {A : Type} (c1: program Σ A)  (P  : Σ -> Prop) a P',
  P -@ c1 -⥅ (P' a) ♯ a ->
  (forall X, safeExec P (c1) X ->  safeExec (P' a) (ret a) X).
  Proof.
    intros.
    unfold hs_eval, safeExec, safe in *.
    destructs H0. 
    specialize (H _ H0) as [σₕ' [? ?]].
    exists σₕ'.
    splits;auto.
    rewrite wp_ret.
    eapply wp_spec;eauto.
  Qed.


  Lemma highstepend_derive : forall  (c1: program Σ unit)  (P  : Σ -> Prop) P',
  P -@ c1 -→ P' ->
  (forall X, safeExec P  c1 X  -> safeExec P' (return tt) X).
  Proof.
    intros.
    destruct H.
    destruct x.
    pose proof (highstependret_derive c1  P tt ((fun _ => P')) H).
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
    unfold_monad.
    sets_unfold.
    eexists.
    splits;eauto.
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
    unfold_monad.
    sets_unfold.
    eexists.
    splits;eauto.
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

  Lemma hsevaltest_derive:
    forall (P: Σ -> Prop) (Q: Prop) a,
      Q -> P -@ (assume!! Q ) -⥅ P ♯ a.
  Proof.
    intros.
    unfold hs_eval, test'.
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


  Lemma safeExec_prorefine: forall {A : Type} (c1 c2: program Σ A)  (P  : Σ -> Prop) X,
  c2 ⊆ c1 ->
  safeExec P c1 X -> safeExec P  c2  X.
  Proof.
    unfold safeExec. intros.
    destructs H0.
    eexists.
    split;eauto.
    unfold safe in *.
    eapply wp_progrefine;eauto.
  Qed.

  Lemma safeExec_X_subset {A: Type} (c: program Σ A) (P: Σ -> Prop) X1 X2:
    X1 ⊆ X2 ->
    safeExec P c X1 -> safeExec P c X2.
  Proof.
    unfold safeExec, safe; intros Hx [s [H1 H2]].
    exists s; split; auto.
    eapply wp_conseq;eauto.
  Qed.

  Lemma safeExec_proequiv: forall {A : Type} (c1 c2: program Σ A)  (P  : Σ -> Prop) X,
  c1 == c2 ->
  safeExec P c1 X  -> safeExec P c2 X.
  Proof.
    unfold safeExec. intros.
    destructs H0.
    eexists.
    split;eauto.
    unfold safe in *.
    intros.
    rewrite wp_progequiv;eauto.
  Qed.

  Lemma safeExec_choice_l: forall {A: Type} (c1 c2: program Σ A) P X,
    safeExec P (choice c1 c2) X -> safeExec P c1  X.
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

  Lemma safeExec_choice_r: forall {A: Type} (c1 c2: program Σ A) P X,
    safeExec P (choice c1 c2) X -> safeExec P c2 X.
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

  Lemma safeExec_test': forall (Q: Prop) P (X: unit -> Σ -> Prop),
    Q ->
    safeExec P (assume!! Q) X -> safeExec P (skip) X.
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
    safeExec P (assume Q) X -> safeExec P (skip) X.
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
    safeExec P (update' f) X -> safeExec (fun s => exists s0, s = f s0 /\ P s0) (skip) X.
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
    safeExec P (update R) X -> safeExec (fun s => exists s0, R s0 s /\ P s0) (skip) X.
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
    exists (fun (r : A) (x : Σ) => c1 σₕ r x).
    unfold safeExec.
    splits;eauto.
    { eexists.
      split;eauto.
      unfold safe.
      apply wp_self.
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

  (* this can be replaced by highstependret_derive*)
  Lemma safeExec_bind_high {A B: Type}: forall a (Q: A -> Σ -> Prop) (P : Σ -> Prop) (c1: program Σ A) (c2: A -> program Σ B) X,
    safeExec P (x <- c1;; c2 x) X ->
    (forall s1, P s1 -> exists s2, c1 s1 a s2 /\ Q a s2) ->
    safeExec (Q a) (c2 a) X.
  Proof.
    unfold safeExec, safe; unfold_monad; sets_unfold; intros.
    destruct H as [s [HP Hs]].
    specialize (H0 s HP); destruct H0 as [s1 [Hc1 Qs2]].
    exists s1; split; auto.
    intros b s2 Hc2.
    apply Hs.
    exists a, s1; tauto.
  Qed.

  Lemma safeExec_bind_unit {B: Type}: forall (Q: Σ -> Prop) (P : Σ -> Prop) (c1: program Σ unit) (c2:program Σ B) X,
    safeExec P (c1;; c2) X ->
    (forall s1, P s1 -> exists s2, c1 s1 tt s2 /\ Q s2) ->
    safeExec Q c2 X.
  Proof.
    unfold safeExec, safe; unfold_monad; sets_unfold; intros.
    destruct H as [s [HP Hs]].
    specialize (H0 s HP); destruct H0 as [s1 [Hc1 Qs2]].
    exists s1; split; auto.
    intros b s2 Hc2.
    apply Hs.
    exists tt, s1; tauto.
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


  (* corollaries with bind *)

  Lemma safeExec_test_bind: forall {A: Type} (Q: Prop) (c: program Σ A) P X,
    Q ->
    safeExec P (assume!! Q ;; c) X  -> safeExec P c X.
  Proof.
    intros * H.
    eapply safeExec_bind_reta with (a:= tt).
    intros *.
    apply safeExec_test';auto.
  Qed.

  Lemma safeExec_testst_bind: forall {A: Type} (Q: Σ -> Prop) (c: program Σ A) (P: Σ -> Prop) X,
    (forall st, P st -> Q st) ->
    safeExec P (assume Q ;; c) X  -> safeExec P c X.
  Proof.
    intros * H.
    eapply safeExec_bind_reta with (a:= tt).
    intros *.
    apply safeExec_testst;auto.
  Qed.

  Lemma safeExec_any_bind: forall {A: Type} (Q: Type) (c: Q -> program Σ A) (P: Σ -> Prop) X a,
    safeExec P (a <- any Q;; c a) X -> safeExec P (c a) X.
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


  Lemma safeExec_monad_Atrue_finnal: forall  {A: Type} (m: program unit A) ,
    safeExec ATrue m (fun r x => m tt r x).
  Proof.
    intros.
    unfold safeExec, ATrue, safe.
    exists tt.
    splits;auto.
    apply wp_self.
  Qed.

  Lemma safeExec_ret_Atrue_finnal: forall  {A: Type}  (m: program Σ A) (l : A) (σ: Σ) ,
    safeExec ATrue (ret l) (fun r x => m σ r x) ->
    exists σ', m σ l σ'.
  Proof.
    unfold safeExec,safe; unfold_monad.
    intros.
    destructs H.
    eapply wp_spec with (a:= l) (s2:= σₕ)  in H0;[ | auto].
    exists σₕ.
    auto.
  Qed.

  
  Lemma safeExec_ret {A: Type} a (P: Σ -> Prop) (X: A -> Σ -> Prop):
    safeExec P (ret a) X ->
    exists s, P s /\ (a, s) ∈ X.
  Proof.
    unfold safeExec, safe.
    intros [s [? ?]].
    rewrite wp_ret in H0.
    exists s; tauto.
  Qed.

  Lemma safeExec_ret_tt (P: Σ -> Prop) (X: Σ -> Prop):
    safeExec P (ret tt) (fun _ => X) ->
    exists s, P s /\  X s.
  Proof.
    intros; apply safeExec_ret in H.
    sets_unfold in H; auto.
  Qed.

End  exec_rules.

#[export] Instance safeExec_programrefine_impl_Proper
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (Sets.included ==> eq ==> (Basics.flip Basics.impl)) (@safeExec Σ A P).
Proof.
  unfold Proper, respectful.
  intros. subst y0.
  hnf.
  apply safeExec_prorefine;eauto.
Qed.

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
  Proper (Sets.equiv ==> eq ==>  iff) (@safeExec Σ A P).
Proof.
  unfold Proper, respectful.
  intros. subst y0. split. 
  apply safeExec_proequiv. auto.
  apply safeExec_proequiv. symmetry. auto.
Qed.

#[export] Instance safeExec_programequiv_iff_Proper'
  {Σ: Type} {A: Type} (P: Σ -> Prop):
  Proper (Sets.equiv ==> eq ==>  iff) (@safeExec Σ A P).
Proof.
  unfold Proper, respectful.
  intros. subst y0. split. 
  apply safeExec_proequiv. auto.
  apply safeExec_proequiv. symmetry. auto.
Qed.

#[export] Instance hseval_programequiv_Proper
  {Σ: Type} {A: Type}:
  Proper (Sets.equiv ==> eq ==> eq ==> eq ==> iff ) (@hs_eval Σ A).
Proof.
  unfold Proper, respectful.
  intros. subst y0 y1 y2. split.
  apply hs_eval_proequiv. auto.
  apply hs_eval_proequiv. symmetry. auto.
Qed.

#[export] Instance hseval_programequiv_Proper'
  {Σ: Type} {A: Type}:
  Proper (Sets.equiv ==> eq ==> eq ==> eq ==> iff ) (@hs_eval Σ A).
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
  prog_nf;
  match goal with 
  | |- ?P -@ (choice ?c1 ?c2) -⥅ ?Q ♯ ?a => apply hsevalchoice_left_derive
  | |- _ => fail 1 "choice_left error, expected hseval/choice"
  end.

Ltac abs_choice_right :=
  prog_nf;
  match goal with 
  | |- ?P -@ (choice ?c1 ?c2) -⥅ ?Q ♯ ?a => apply hsevalchoice_right_derive
  | |- _ => fail 1 "choice_right error, expected hseval/choice"
  end.


Ltac abs_test_step :=
  match goal with
  | |- hs_eval (test' _) _ _ _ => apply hsevaltest_derive
  | |- hs_eval (bind (test' _) _) ?P ?Q ?a =>
         refine (hsevalbind_derive' _ _ _
                   P tt Q a _ _);
          [ apply hsevaltest_derive | ]
  | |- hs_eval ((test' _) ;; _) ?P ?Q ?a =>
         refine (hsevalbind_derive' _ _ _
                   P tt Q a _ _);
          [ apply hsevaltest_derive | ]
  | |- _ => fail 1 "test error, expected hseval/assume!!"
  end.

Ltac abs_ret_step :=
  apply highret_eval2.

Ltac safe_step H := prog_nf in H;
  match type of H with
  | safeExec _ ((assume!! _ ) ;; _) _ =>
      apply safeExec_test_bind in H; [prog_nf in H; try safe_step H | auto]
  | safeExec _ ((assume _ ) ;; _) _ =>
      apply safeExec_testst_bind in H; [prog_nf in H; try safe_step H | auto]
  | _ => fail 1 "no pattern in hypothesis, expected safeExec/assume"
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
    (exists s, P s) ->
    safeExec P c (result_state P c).
  Proof.
    unfold safeExec, result_state, safe.
    intros [s HP].
    exists s; split; auto.
    sets_unfold; intros a s' ?.
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
    safeExec P2 (return a) (c σ) -> 
    σ ∈ P1 ->
    (exists σ', Q a σ' /\ P2 σ').
  Proof.
    unfold Hoare, safeExec, safe.
    intros. 
    destructs H0.
    sets_unfold.
    specialize (H2 a σₕ (ltac:(unfold_monad;auto))).
    specialize (H σ _ _ H1 H2).
    eexists. eauto.
  Qed.

End  safeexec_Hoare_composition_rules.
