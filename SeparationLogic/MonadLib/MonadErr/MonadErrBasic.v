Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Lia.
From SetsClass Require Import SetsClass.
From FP Require Import PartialOrder_Setoid BourbakiWitt. 
From MonadLib Require Export Monad.
Export PO_lift.
Import Monad MonadNotation SetsNotation.
Local Open Scope sets.
Local Open Scope monad.



(*************************************************************************************************************)
(**********************************      state relation monad with error     *********************************)
(**********************************                 program Σ A              *********************************)
(**********************************    Setting                               *********************************)
(**********************************         nrm : Σ -> A -> Σ -> Prop        *********************************)
(**********************************         err : Σ -> Prop                  *********************************)
(*************************************************************************************************************)

Module MonadErr.

Section monaderr.
  Context {Σ: Type}.

  Record M (A: Type): Type := {
    nrm: Σ -> A -> Σ -> Prop;
    err: Σ -> Prop
  }.

  Arguments nrm {A}%_type_scope m.
  Arguments err {A}%_type_scope m.


  Definition ret {A: Type}(a: A): M A := {|
    nrm := fun s1 r s2 => r = a /\ s2 = s1;
    err := ∅
  |}.

  (* program order  *)
  
  Definition nrm_err {A : Type} (f: Σ -> A -> Σ -> Prop) (g:  A -> Σ -> Prop) : Σ -> Prop := 
    fun s1 => exists a s0, f s1 a s0 /\ g a s0. 
  Definition nrm_nrm {A B: Type} (f: Σ -> A -> Σ -> Prop) (g:  A -> Σ -> B -> Σ -> Prop) : Σ -> B -> Σ -> Prop := 
    fun s1 b s2 => exists a s0, f s1 a s0 /\ g a s0 b s2.

  Definition bind {A B: Type}(m: M A)(f: A -> M B): M B := {|
    nrm := nrm_nrm m.(nrm) (fun a => (f a).(nrm)) ;
    err := m.(err) ∪ (nrm_err m.(nrm) (fun a => (f a).(err)));
  |}. 
  
End monaderr.
End MonadErr.

Arguments MonadErr.M Σ%_type_scope A%_type_scope: clear implicits.
Arguments MonadErr.nrm {Σ}%_type_scope [A]%_type_scope m.
Arguments MonadErr.err {Σ}%_type_scope [A]%_type_scope m.

#[export] Instance state_rel_monad (Σ: Type): Monad (MonadErr.M Σ) :=
{|
  bind := @MonadErr.bind Σ;
  ret := @MonadErr.ret Σ;
|}.

Notation program := MonadErr.M.
Notation MONAD := (program unit).

(** A backend-independent name for recursive constructions.  The error
    monad keeps [BW_fix] as its implementation. *)
Definition Rec {X: Type} {oLubX: OmegaLub X} {BotX: Bot X}
  (F: X -> X): X :=
  BW_fix F.

Arguments Rec: simpl never.

Hint Unfold MonadErr.bind MonadErr.ret : monad_unfold.



Section monadop.
Import MonadErr.
Context {Σ: Type}.

  Definition step : Type := Σ -> Σ -> Prop.
  Coercion step_to_program (m: step): program Σ unit := {|
    nrm := fun s1 a s2 => a = tt /\ m s1 s2;
    err := ∅
  |}.
  
  Definition choice {A: Type}
    (f g: program Σ A): program Σ A := {|
    nrm := f.(nrm) ∪ g.(nrm);
    err := f.(err) ∪ g.(err);
  |}.

  Definition testPure (P: Prop): program Σ unit :={|
    nrm := fun s1 _ s2 => s1 = s2 /\ P;
    err := ∅;
  |}.

  Definition test (P: Σ -> Prop): program Σ unit :={|
    nrm := fun s1 _ s2 => s1 = s2 /\ P s1;
    err := ∅;
  |}.
  
  Definition assert (P: Prop): program Σ unit :={|
    nrm := fun s1 _ s2 => s1 = s2 /\ P;
    err := fun _ => ~ P;
  |}.

  Definition assertS (P: Σ -> Prop): program Σ unit :={|
    nrm := fun s1 _ s2 => s1 = s2 /\ P s1;
    err := fun s1 => ~ P s1;
  |}.


  (* do not ret anything, encoded by reting the dummy constant tt. *)
  Definition put (s: Σ) : program Σ unit :={|
    nrm := fun s1 a s2 => a = tt /\ s2 = s;
    err := ∅;
  |}.

  Definition any (A: Type): program Σ A :=
  {|
    nrm := fun s1 _ s2 => s1 = s2 ;
    err := ∅;
  |}. 

  Definition get {A: Type} (P: Σ -> A -> Prop): program Σ A :=
  {|
    nrm := fun s1 a s2 => P s1 a /\ s1 = s2 ;
    err := ∅;
  |}. 

  Definition get' {A: Type} (f: Σ -> A): program Σ A :=
    get (fun s a => a = f s).

  Definition update (P: Σ -> Σ -> Prop): program Σ unit :=
  {|
    nrm := fun s1 _ s2 => P s1 s2;
    err := ∅;
  |}. 
  
  Definition update' (f: Σ -> Σ): program Σ unit :=
    update (fun s s' => s' = f s).
  
  Definition read : program Σ Σ :=
  {|
    nrm := fun s1 a s2 =>  a = s1 /\ s1 = s2 ;
    err := ∅;
  |}.

  Definition If (cond: Σ -> Prop) (c: program Σ unit): program Σ unit :=
    choice
      (test cond;; c)
      (test (fun s => ~ cond s)).

  Definition if_else {A: Type} (cond: Σ -> Prop)
                     (c1 c2: program Σ A): program Σ A :=
    choice
      (test cond;; c1)
      (test (fun s => ~ cond s);; c2).

End monadop.

Notation "'skip'" := (ret tt) (at level 50).
Notation "'assume!!' P" := (testPure P) (at level 50).
Notation "'assume' P" := (test P) (at level 50).


(*************************************************************************************************************)
(*****************************************    monad program CPO      *****************************************)
(*************************************************************************************************************)

Module ProgramPO.
  Import MonadErr.

  Section program_rels.
  Context {Σ : Type}.
  Context {A: Type}.

  Definition full : program Σ A := {|
    nrm := Sets.full;
    err := Sets.full;
  |}.

  Definition bot : program Σ A := {|
    nrm := ∅;
    err := ∅;
  |}.

  Definition intersect (x1 x2: program Σ A) : program Σ A := {|
    nrm := x1.(nrm) ∩ x2.(nrm);
    err := x1.(err) ∩ x2.(err);
  |}.

  Definition union (x1 x2: program Σ A) : program Σ A := {|
    nrm := x1.(nrm) ∪ x2.(nrm);
    err := x1.(err) ∪ x2.(err);
  |}.

  Definition indexed_intersect {I} (x: I -> program Σ A): program Σ A := {|
    nrm := ⋂ (fun i => (x i).(nrm));
    err := ⋂ (fun i => (x i).(err));
  |}.

  Definition indexed_union {I} (x: I -> program Σ A): program Σ A := {|
    nrm := ⋃ (fun i => (x i).(nrm));
    err := ⋃ (fun i => (x i).(err));
  |}.

  Record equiv  (p1 p2 : program Σ A) : Prop := {
    nrmequiv : p1.(nrm) == p2.(nrm);
    errequiv : p1.(err) == p2.(err);
  }.

  Record order (p1 p2 : program Σ A) : Prop := {
    nrmle : p1.(nrm) ⊆ p2.(nrm);
    errle : p1.(err) ⊆ p2.(err);
  }.

  End program_rels.
End ProgramPO.

#[export] Instance program_equiv {Σ A: Type} : Equiv (MonadErr.M Σ A) :=  ProgramPO.equiv.
#[export] Instance Equivalence_program {Σ A: Type} : Equivalence (@equiv (MonadErr.M Σ A) _).
Proof.
  split.
  - unfold Reflexive, equiv, program_equiv. 
    intros [? ?].  constructor. reflexivity. reflexivity.
  - unfold Symmetric, equiv.
    intros [? ?] [? ?] [? ?]. constructor; symmetry;auto.  
  - unfold Transitive, equiv.
    intros [? ?] [? ?] [? ?] [? ?] [? ?].
    constructor; etransitivity;eauto. 
Qed.

#[export] Instance program_order {Σ A: Type} : Order(MonadErr.M Σ A) :=  ProgramPO.order.
#[export] Instance Transitive_program {Σ A: Type} : Transitive (@order_rel (MonadErr.M Σ A) _).
Proof.
  unfold Transitive, order_rel.
  intros [? ?] [? ?] [? ?] [? ?] [? ?].
  constructor; etransitivity;eauto. 
Qed.

#[export] Instance Reflexive_program {Σ A: Type}  : Reflexive (@order_rel (MonadErr.M Σ A) _).
Proof.
  unfold Reflexive, order_rel.
  intros [? ?].
  constructor;simpl;reflexivity.
Qed.


#[export] Instance program_PO {Σ A: Type} : PartialOrder_Setoid (MonadErr.M Σ A).
Proof.
  split.
  + unfold AntiSymmetric_Setoid.
    unfold equiv, order_rel, program_equiv, program_order; simpl.
    intros. 
    destruct a as [nrm1 err1]. destruct b as [nrm2 err2].
    destruct H as [H H1]. destruct H0 as [H0 H2]. 
    constructor;simpl in *.
    sets_unfold. sets_unfold in H; sets_unfold in H0. split;intros. apply H;auto. apply H0. auto.
    sets_unfold. sets_unfold in H1; sets_unfold in H2. split;intros.  apply H1. auto. apply H2. auto. 
  + unfold equiv, order_rel, program_equiv, program_order; simpl.
    intros.
    destruct x as [nrm1 err1]. destruct y as [nrm2 err2].
    destruct H.
    simpl in *.
    constructor;simpl.
    sets_unfold. sets_unfold in nrmequiv. intros. apply nrmequiv. auto.
    sets_unfold. sets_unfold in errequiv. intros. apply errequiv. auto.
  + apply Transitive_program.
Qed.

Section monad_equiv_lemmas.

  Context {Σ: Type}.
  Import MonadNotation.
  Local Open Scope monad_scope.
  Local Open Scope order_scope.

  Lemma bind_equiv {A B: Type}: forall (c1 c1': program Σ A) (c2 c2': A -> program Σ B), 
    c1 == c1' -> c2 == c2'  ->
    bind c1 c2  == bind c1' c2'.
  Proof.
    intros.
    constructor;simpl.
    * unfold MonadErr.nrm_nrm. 
      split; intros.
      + destruct H1 as (? & ? & ? & ?).
        do 2 eexists.
        split.
        apply H;eauto.
        apply H0;eauto.
      + destruct H1 as (? & ? & ? & ?).
        do 2 eexists.
        split.
        apply H;eauto.
        apply H0;eauto.
    * unfold MonadErr.nrm_err. 
      split; intros.
      + destruct H1.
        left. apply H;auto.
        destruct H1 as (? & ? & ? & ?).
        right.
        do 2 eexists.
        split.
        apply H;eauto.
        apply H0;eauto.
      + destruct H1.
        left. apply H;auto.
        destruct H1 as (? & ? & ? & ?).
        right.
        do 2 eexists.
        split.
        apply H;eauto.
        apply H0;eauto. 
  Qed.


  Lemma bindpat_equiv {A B: Type}: forall (c1 c1': program Σ A) (c2 c2': A -> program Σ B), 
    c1 == c1' -> c2 == c2'  ->
    ' pat <- c1 ;; (c2 pat) == ' pat <- c1' ;; (c2' pat).
  Proof.
    intros.
    apply bind_equiv. auto.
    auto.
  Qed.

  Lemma assume_equiv {A: Type}: 
    forall (P: Prop) (c: program Σ A),
      P -> (assume!! (P);; c) == c.
  Proof.
    intros; constructor; simpl.
    - unfold MonadErr.nrm_nrm; sets_unfold.
      split; intros.
      + destruct H0 as [_ [s [[H0 _] H1]]].
        subst; tauto.
      + exists tt; exists a; tauto.
    - rewrite Sets_empty_union.
      unfold MonadErr.nrm_err; sets_unfold.
      split; intros.
      + destruct H0 as [_ [s [[H0 _] H1]]].
        subst; tauto.
      + exists tt; exists a; tauto.
  Qed. 

  Lemma assert_equiv {A: Type}: 
    forall (P: Prop) (c: program Σ A),
      P -> (assert (P);; c) == c.
  Proof.
    intros; constructor; simpl.
    - unfold MonadErr.nrm_nrm; sets_unfold.
      split; intros.
      + destruct H0 as [_ [s [[H0 _] H1]]].
        subst; tauto.
      + exists tt; exists a; tauto.
    - unfold MonadErr.nrm_err; sets_unfold.
      split; intros.
      + destruct H0; try tauto.
        destruct H0 as [_ [s [[H0 _] H1]]].
        subst; tauto.
      + right; exists tt; exists a; tauto.
  Qed.  
  

  Lemma bind_assoc {A B C: Type}: 
    forall (c0: program Σ A) (c1: A -> program Σ B) (c2: B -> program Σ C),
      x <- (y <- c0;; c1 y);; c2 x == y <- c0;; x <- c1 y;; c2 x.
  Proof.
    intros; constructor; simpl.
    - unfold MonadErr.nrm_nrm; sets_unfold; split; intros.
      + destruct H as [a2 [s0 [H H0]]].
        destruct H as [a3 [s1 [H1 H2]]].
        exists a3; exists s1; split; auto.
        exists a2; exists s0; tauto.
      + destruct H as [a2 [s0 [H0 H]]].
        destruct H as [a3 [s1 [H1 H2]]].
        exists a3; exists s1; split; auto.
        exists a2; exists s0; tauto.
    - unfold MonadErr.nrm_err; sets_unfold; split; intros.
      + destruct H.
        * destruct H; try tauto.
          destruct H as [a0 [s0 [? ?]]].
          right; exists a0; exists s0; tauto.
        * unfold MonadErr.nrm_nrm in H.
          destruct H as [a0 [s0 [? ?]]].
          destruct H as [a1 [s1 [? ?]]].
          right; exists a1; exists s1.
          split; try tauto.
          right; exists a0; exists s0; tauto.
      + destruct H; try tauto.
        destruct H as [a0 [s0 [H0 H]]].
        destruct H.
        * left; right.
          exists a0; exists s0; tauto.
        * right; unfold MonadErr.nrm_nrm.
          destruct H as [a1 [s1 [? ?]]].
          exists a1; exists s1.
          split; try tauto.
          exists a0; exists s0; tauto. 
  Qed.

  Lemma bind_choice_equiv {A B: Type}: 
    forall (c0 c1: program Σ A) (c2: A -> program Σ B),
      x <- (choice c0 c1);; c2 x == choice (x <- c0;; c2 x) (x <- c1;; c2 x).
  Proof.
    intros; constructor; simpl.
    - unfold MonadErr.nrm_nrm; sets_unfold; split; intros.
      + destruct H as [a2 [s0 [H H0]]].
        destruct H.
        * left; do 2 eexists.
          split; eauto.
        * right; do 2 eexists.
          split; eauto.
      + destruct H; destruct H as [a2 [s0 [? ?]]];
        exists a2; exists s0; tauto.
    - unfold MonadErr.nrm_err; sets_unfold; split; intros.
      + destruct H; try tauto.
        destruct H as [a0 [s0 [H H0]]].
        destruct H.
        * left; right.
          do 2 eexists; split; eauto.
        * right; right.
          do 2 eexists; split; eauto.
      + do 2 destruct H; try tauto.
        * destruct H as [a0 [s0 [? ?]]]; right.
          exists a0; exists s0; tauto.
        * destruct H as [a0 [s0 [? ?]]]; right.
          exists a0; exists s0; tauto.
  Qed.

  Lemma choice_comm {A: Type}:
    forall (c0 c1: program Σ A),
      choice c0 c1 == choice c1 c0.
  Proof.
    intros; unfold choice.
    constructor; simpl; apply Sets_union_comm.
  Qed.

  Lemma choice_case_equiv {A: Type}:
    forall (c0 c1 c2 c3: program Σ A),
      c0 == c2 ->
      c1 == c3 ->
      choice c0 c1 == choice c2 c3.
  Proof.
    intros.
    inversion H as [E0 E1].
    inversion H0 as [E2 E3].
    unfold choice; constructor; simpl.
    - rewrite E0; rewrite E2; easy.
    - rewrite E1; rewrite E3; easy.
  Qed.

  Lemma bind_ret_l{A B: Type}: 
    forall (a: A) (c: A -> program Σ B),
      x <- ret a;; c x == c a.
  Proof.
    intros; constructor; simpl.
    - unfold MonadErr.nrm_nrm; sets_unfold. 
      unfold ret; split; intros.
      + destruct H as [? [? [[? ?] ?]]].
        subst; tauto.
      + exists a; exists a0; tauto.
    - rewrite Sets_empty_union.
      unfold MonadErr.nrm_err, ret; sets_unfold; split; intros.
      + destruct H as [? [? [[? ?] ?]]].
        subst; tauto.
      + exists a; exists a0; tauto.
  Qed.

  Lemma bind_ret_r {A: Type}: 
    forall (c: program Σ A),
      a <- c;; ret a == c.
  Proof.
    intros; constructor; simpl.
    - unfold MonadErr.nrm_nrm; sets_unfold. 
      unfold_monad; split; intros.
      + destruct H as (? & ? & ? & ? & ?).
        subst; tauto.
      + exists a0; exists a1; tauto.
    - unfold MonadErr.nrm_err; unfold_monad; sets_unfold; split; intros.
      + destruct H; auto.
        destruct H as (? & ? & ? & ?); tauto.
      + left; auto.
  Qed.

  Lemma bind_ret_l' {A B C: Type}: 
    forall (f: A -> B) (c: A -> B -> program Σ C),
       (fun k => x <- ret (f k);; c k x) == (fun k => c  k (f k)).
  Proof.
    intros; constructor; simpl.
    - unfold MonadErr.nrm_nrm; sets_unfold. 
      unfold ret; split; intros.
      + destruct H as [? [? [[? ?] ?]]].
        subst; tauto.
      + exists (f a); exists a0; tauto.
    - rewrite Sets_empty_union.
      unfold MonadErr.nrm_err, ret; sets_unfold; split; intros.
      + destruct H as [? [? [[? ?] ?]]].
        subst; tauto.
      + exists (f a); exists a0; tauto.
  Qed.

  Lemma common_step_equiv {A B: Type}:
    forall (c0: program Σ A) (c1 c2: A -> program Σ B),
      (forall a, c1 a == c2 a) ->
      x <- c0;; c1 x == x <- c0;; c2 x.
  Proof.
    intros.
    constructor; unfold bind; simpl; sets_unfold; intros. 
    - unfold MonadErr.nrm_nrm; split; intros.
      + destruct H0 as [a2 [s0 ?]].
        specialize (H a2).
        inversion H.
        sets_unfold in nrmequiv.
        specialize (nrmequiv s0 a0 a1).
        exists a2; exists s0; tauto.
      + destruct H0 as [a2 [s0 ?]].
        specialize (H a2).
        inversion H.
        sets_unfold in nrmequiv.
        specialize (nrmequiv s0 a0 a1).
        exists a2; exists s0; tauto.
    - unfold MonadErr.nrm_err; split; intros; 
      destruct H0; try tauto; right.
      + destruct H0 as [a2 [s0 ?]].
        specialize (H a2).
        inversion H.
        sets_unfold in errequiv.
        specialize (errequiv s0).
        exists a2; exists s0; tauto.
      + destruct H0 as [a2 [s0 ?]].
        specialize (H a2).
        inversion H.
        sets_unfold in errequiv.
        specialize (errequiv s0).
        exists a2; exists s0; tauto.
  Qed.
  
  Lemma choice_l_equiv {A: Type}:
    forall (c0 c1: program Σ A),
      c1 == ProgramPO.bot -> choice c0 c1 == c0.
  Proof.
    intros.
    inversion H; clear H.
    rename nrmequiv into He, errequiv into Hn.
    simpl in He, Hn; sets_unfold in He; sets_unfold in Hn.
    constructor; simpl; sets_unfold; intros.
    - specialize (He a a0 a1).
      rewrite He; tauto.
    - specialize (Hn a).
      rewrite Hn; tauto.
  Qed.

  Lemma choice_r_equiv {A: Type}:
    forall (c0 c1: program Σ A),
      c0 == ProgramPO.bot -> choice c0 c1 == c1.
  Proof.
    intros.
    rewrite choice_comm.
    apply choice_l_equiv; auto.
  Qed.

  Lemma choice_idem_equiv {A: Type}:
    forall (c: program Σ A),
      choice c c == c.
  Proof.
    intros.
    constructor; simpl; sets_unfold; intros; tauto.
  Qed.

  Lemma assume_false_equiv {A: Type}:
    forall P (c: program Σ A),
      ~ P -> assume!! P;; c == ProgramPO.bot.
  Proof.
    intros.
    constructor; simpl; sets_unfold; intros.
    - unfold MonadErr.nrm_nrm; split; intros; try tauto.
      destruct H0 as [_ [? [ [_  ?] _ ]]]; tauto.
    - unfold MonadErr.nrm_err; split; intros; try tauto.
      destruct H0; auto.
      destruct H0 as [_ [? [ [_  ?] _ ]]]; tauto.
  Qed.
    

End monad_equiv_lemmas.



Section  monad_nrm_err_lemmas.
  Context {Σ A B : Type}.
  Import MonadErr.
  Import MonadNotation.

  Lemma bind_err_iff (c1: program Σ A) (c2: A -> program Σ B) σ :
    (x <- c1 ;; c2 x).(err) σ <-> c1.(err) σ \/ exists a σ', c1.(nrm) σ a σ' /\ (c2 a).(err) σ'.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_noerr_iff (c1: program Σ A) (c2: A -> program Σ B) σ :
    ~ (x <- c1 ;; c2 x).(err) σ <-> ~ c1.(err) σ /\ forall a σ', c1.(nrm) σ a σ' ->  ~ (c2 a).(err) σ'.
  Proof.
    rewrite bind_err_iff.
    split; intros.
    - split.
      + contradict H. tauto.
      + intros. contradict H. right. eexists. eexists. split; eauto.
    - destruct H as [Herr Hnrm].
      intros Hfalse.
      destruct Hfalse as [Herr' | Hnrm']; auto.
      destruct Hnrm' as (a & σ' & ? & ?).
      eapply Hnrm; eauto.
  Qed.

  Lemma bind_err_left (c1: program Σ A) (c2: A -> program Σ B) σ :
    c1.(err) σ -> (x <- c1 ;; c2 x).(err) σ.
  Proof.
    intros. rewrite bind_err_iff. left; auto.
  Qed.

  Lemma bind_noerr_left (c1: program Σ A) (c2: A -> program Σ B) σ :
    ~ (x <- c1 ;; c2 x).(err) σ -> ~ c1.(err) σ.
  Proof.
    intros H. apply bind_noerr_iff in H as [H _]. auto.
  Qed.

  Lemma bind_err_right (c1: program Σ A) (c2: A -> program Σ B) σ a σ' :
    c1.(nrm) σ a σ' -> (c2 a).(err) σ' -> (x <- c1 ;; c2 x).(err) σ.
  Proof.
    intros. rewrite bind_err_iff. right. eexists. eexists. split; eauto.
  Qed.

  Lemma bind_noerr_right (c1: program Σ A) (c2: A -> program Σ B) σ :
    ~ (x <- c1 ;; c2 x).(err) σ ->
    forall a σ', c1.(nrm) σ a σ' ->  ~ (c2 a).(err) σ'.
  Proof.
    intros H. apply bind_noerr_iff in H as [? H]. intros; auto.
  Qed.

  Lemma bind_nrm_iff (c1: program Σ A) (c2: A -> program Σ B) σ1 b σ2 :
    (x <- c1 ;; c2 x).(nrm) σ1 b σ2 <->
    exists a σ', c1.(nrm) σ1 a σ' /\ (c2 a).(nrm) σ' b σ2.
  Proof.
    reflexivity.
  Qed.

End  monad_nrm_err_lemmas.


#[export] Instance programbind_Proper
  {Σ: Type} {A B: Type}:
  Proper (equiv ==> equiv ==> equiv ) (@MonadErr.bind Σ A B).
Proof.
  unfold Proper, respectful.
  intros.
  apply bind_equiv; auto.
Qed.


#[export] Instance programbindpat_Proper
  {Σ: Type}  {A B: Type}:
  Proper (equiv ==> equiv ==> equiv )  (fun c1 c2 => (@MonadErr.bind Σ A B  c1 (fun x => match x with pat => c2 end))).
Proof.
  unfold Proper, respectful.
  intros.
  apply bindpat_equiv; auto.
  hnf.
  intros.
  apply H0.
Qed.

#[export] Instance programbind_included_Proper
  {Σ: Type} {A B: Type}:
  Proper (order_rel ==> order_rel ==> order_rel ) (@MonadErr.bind Σ A B).
Proof.
  unfold Proper, respectful.
  intros.
  unfold MonadErr.bind.
  constructor;simpl.
  * unfold  MonadErr.nrm_nrm;simpl.
    sets_unfold.
    intros s b s0.
    intros.
    destruct H1 as (a & s1 & ? & ?).
    exists a, s1.
    split;[apply H | apply H0];auto.
  * unfold  MonadErr.nrm_err;simpl.
    sets_unfold.
    intros s.
    intros.
    destruct H1.
    left;apply H;auto.
    destruct H1 as (a & s1 & ? & ?).
    right.
    exists a, s1.
    split;[apply H | apply H0];auto.
Qed.

#[export] Instance choice_equiv_Proper {Σ A: Type}:
  Proper ( equiv ==> equiv  ==> equiv) (@choice Σ A).
Proof.
  unfold Proper, respectful; intros.
  apply choice_case_equiv; auto.
Qed.

Definition ATrue {Σ: Type} : Σ -> Prop := fun _ => True.

Ltac prog_nf :=
  repeat 
  (rewrite bind_assoc ||
   rewrite bind_choice_equiv ||
   rewrite bind_ret_l || 
   rewrite bind_ret_l' ||
   rewrite bind_ret_r).

Ltac prog_nf_in H :=
  repeat 
  (rewrite bind_assoc in H ||
   rewrite bind_choice_equiv in H ||
   rewrite bind_ret_l in H || 
   rewrite bind_ret_l' in H ||
   rewrite bind_ret_r in H).

Tactic Notation "prog_nf" "in" hyp(H) :=
  prog_nf_in H.
