Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import SetsClass.SetsClass.
From MonadLib Require Export Monad.
Import SetsNotation.
From FP Require Import SetsFixedpoints PartialOrder_Setoid.
Export SetsFixedpoints.
Import Monad MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Module StateRelMonad.

Definition M (Σ A: Type): Type :=
  Σ -> A -> Σ -> Prop.

Definition bind {Σ A B: Type} (f: M Σ A) (g: A -> M Σ B): M Σ B :=
  fun (s1: Σ) (b: B) (s3: Σ) =>
    exists (a: A) (s2: Σ),
      (s1, a, s2) ∈ f /\ (s2, b, s3) ∈ g a.

Definition ret {Σ A: Type} (a0: A): M Σ A :=
  fun (s1: Σ) (a: A) (s2: Σ) => a = a0 /\ s1 = s2.

End StateRelMonad.

#[export] Instance state_rel_monad (Σ: Type): Monad (StateRelMonad.M Σ) :=
{|
  bind := @StateRelMonad.bind Σ;
  ret := @StateRelMonad.ret Σ;
|}.

Notation program := StateRelMonad.M.
Notation MONAD := (program unit).

(** A backend-independent name for recursive constructions.  The state
    relation monad keeps [Lfix] as its implementation. *)
Definition Rec {X: Type} {_SETS_X: Sets.SETS X} (F: X -> X): X :=
  Lfix F.

Arguments Rec: simpl never.

Hint Unfold StateRelMonad.bind StateRelMonad.ret : monad_unfold.

Section state_rel.
  Context {Σ: Type}.

  Definition test (P: Σ -> Prop): program Σ unit :=
  fun s1 _ s2 => P s1 /\ s1 = s2.

  Definition test' (P: Prop): program Σ unit :=
    fun s1 _ s2 => P /\ s1 = s2.
  
  Definition choice {Σ A: Type} (f g: program Σ A): program Σ A :=
    f ∪ g.

  Definition any (A: Type): program Σ A :=
    fun s1 _ s2 => s1 = s2.

  Definition get {A: Type} (P: Σ -> A -> Prop): program Σ A :=
    fun s1 a s2 => P s1 a /\ s1 = s2.
  
  Definition get' {A: Type} (f: Σ -> A): program Σ A :=
    get (fun s a => a = f s).
  
  Definition update (P: Σ -> Σ -> Prop): program Σ unit :=
    fun s1 _ s2 => P s1 s2.
  
  Definition update' (f: Σ -> Σ): program Σ unit :=
    update (fun s s' => s' = f s).
  
  Definition If (cond: Σ -> Prop) (c: program Σ unit): program Σ unit :=
    choice
      (test cond;; c)
      (test (fun s => ~ cond s)).
  
  Definition if_else {A: Type} (cond: Σ -> Prop) 
                     (c1 c2: program Σ A): program Σ A :=
    choice
      (test cond;; c1)
      (test (fun s => ~ cond s);; c2).

End  state_rel.

Notation "'skip'" := (ret tt) (at level 50).
Notation "'assume' P" := (test P) (at level 50).
Notation "'assume!!' P " := (test' P) (at level 50).

Section  loop_monad.
  
  Context {Σ: Type}.

Definition while_f (cond: (program Σ bool))  (body : (program Σ unit)) 
                     (W : (program Σ unit)) 
                        : (program Σ unit) :=
  (x <- cond ;; (match x with 
  | true => body;; W
  | false => ret tt
  end)).

  Definition while (cond: (program Σ bool)) (body : program Σ unit)  := Rec (while_f cond body).

  Definition whileret_f {A: Type}  (cond: A -> (program Σ bool)) (body : A -> (program Σ A)) 
                     (W :  A -> program Σ A) 
                        : A -> program Σ A :=
  fun a => (x <- (cond a) ;; match x with 
  | true =>  bind (body a) W
  | false => (ret a)
  end).

  Definition whileret {A: Type}  (cond: (A -> (program Σ bool))) (body : A -> (program Σ A))  := Rec (whileret_f cond body).
  
  Definition whileP_f (cond: Σ -> Prop)  (body : (program Σ unit)) 
                     (W : program Σ unit) 
                        : program Σ unit :=
  choice (assume cond;; body;; W) 
         (assume (fun s => ~ cond s);; ret tt).
  
  Definition whileP (cond: Σ -> Prop) (body : program Σ unit)  := Rec (whileP_f cond body).

  Definition whileretP_f {A: Type}  (cond: A -> Σ -> Prop) (body : A -> (program Σ A)) 
                     (W :  A -> program Σ A) 
                        : A -> program Σ A :=
  fun a => 
    choice (assume (fun s => cond a s);; a' <- body a;; W a') 
           (assume (fun s => ~ cond a s);; ret a).

  Definition whileretP {A: Type}  (cond: A -> Σ -> Prop) (body : A -> (program Σ A))  := Rec (whileretP_f cond body).

  Definition Repeat_f  (body : (program Σ unit)) 
                      (W : program Σ unit) 
                          :program Σ unit :=
    body;; W.

  Definition Repeat (body : (program Σ unit))  := Rec (Repeat_f body).

  Definition repeat_break_f
              {Σ A B: Type}
              (body: A -> program Σ (CntOrBrk A B))
              (W: A -> program Σ B)
              (a: A): program Σ B :=
    x <- body a;;
    match x with
    | by_continue a' => W a'
    | by_break b => ret b
    end.

  Definition repeat_break
              {Σ A B: Type}
              (body: A -> program Σ (CntOrBrk A B)):
    A -> program Σ B :=
    Rec (repeat_break_f body).

  Definition repeat_break_f_noinput
              {Σ B: Type}
              (body: program Σ (CntOrBrk unit B))
              (W: program Σ B): program Σ B :=
    x <- body;;
    match x with
    | by_continue _ => W
    | by_break b => ret b
    end.

  Definition repeat_break_noin
              {Σ B: Type}
              (body: program Σ (CntOrBrk unit B)): program Σ B :=
    Rec (repeat_break_f_noinput body).

  Definition continue {Σ A B: Type} (a: A):
    program Σ (CntOrBrk A B) :=
    ret (by_continue a).

  Definition break {Σ A B: Type} (b: B):
    program Σ (CntOrBrk A B) :=
    ret (by_break b).

  Definition range_iter_f {Σ A: Type}
              (hi: Z)
              (body: Z -> A -> program Σ A)
              (W: Z * A -> program Σ A): Z * A -> program Σ A :=
    fun '(lo, a0) =>
      choice
        (assume!! (lo < hi)%Z;;
         a1 <- body lo a0;;
         W ((lo + 1)%Z, a1))
        (assume!! (lo >= hi)%Z;;
         ret a0).

  Definition range_iter {Σ A: Type}
              (lo hi: Z)
              (body: Z -> A -> program Σ A): A -> program Σ A :=
    fun a => Rec (range_iter_f hi body) (lo, a).

  Definition range_iter_break_f {Σ A B: Type}
              (hi: Z)
              (body: Z -> A -> program Σ (CntOrBrk A B))
              (W: Z * A -> program Σ (CntOrBrk A B)):
    Z * A -> program Σ (CntOrBrk A B) :=
    fun '(lo, a0) =>
      choice
        (assume!! (lo < hi)%Z;;
         ab <- body lo a0;;
         match ab with
         | by_continue a1 => W ((lo + 1)%Z, a1)
         | by_break b => break b
         end)
        (assume!! (lo >= hi)%Z;;
         continue a0).

  Definition range_iter_break {Σ A B: Type}
              (lo hi: Z)
              (body: Z -> A -> program Σ (CntOrBrk A B)):
    A -> program Σ (CntOrBrk A B) :=
    fun a => Rec (range_iter_break_f hi body) (lo, a).

  Definition forset_f {Σ A: Type}
    (body: A -> program Σ unit)
    (W: (A -> Prop) -> program Σ unit) (universe: A -> Prop): program Σ unit :=
    choice (a <- get (fun _ a => a ∈ universe);; 
            body a;;
            W (fun x => x ∈ universe /\ x <> a))
           (assume!! (universe == ∅) ;;
            ret tt).
  
  Definition forset {Σ A: Type}
    (universe: A -> Prop)
    (body: A -> program Σ unit): program Σ unit :=
    Rec (forset_f body) universe.

  Fixpoint list_iter {Σ A B: Type}
    (body: A -> B -> program Σ B)
    (universe : list A) (b: B)
    : program Σ B :=
    match universe with 
      | nil => ret b
      | cons a universe' =>
          b0 <- body a b;;
          list_iter body universe' b0
    end.

End  loop_monad.

Arguments program Σ%_type_scope A%_type_scope: clear implicits.

(*************************************************************************************************************)
(*****    Pseudocode notation: write a whole abstract program inline, no auxiliary definitions      ******)
(*************************************************************************************************************)
(*                                                                                                          *)
(*  Open this scope ([Local Open Scope prog_scope]) to write state-relation programs the way you would      *)
(*  sketch them on a whiteboard.  Every block is a self-delimiting keyword form, so blocks nest and chain    *)
(*  with [;;] without extra parentheses or intermediate [Definition]s:                                       *)
(*                                                                                                          *)
(*      UPDATE s := f s ;;                     -- state update  (update' (fun s => f s))                     *)
(*      WHILE s , P s DO ... END ;;            -- pre-tested loop   (whileP)                                 *)
(*      IF s , P s THEN c1 ELSE c2 FI          -- two-armed choice  (if_else)                                *)
(*      WHEN s , P s THEN c END                -- one-armed guard   (If)                                     *)
(*      FOR i FROM lo TO hi DO c END           -- counted loop over [lo, hi)   (range_iter)                  *)
(*      LOOP ... BREAK v ... CONTINUE ... END  -- break/continue loop   (repeat_break_noin)                  *)
(*      CHOOSE { c1 | c2 | c3 }                -- nondeterministic choice, one branch per | (choice)         *)
(*                                                                                                          *)
(*  Every construct that inspects the state binds it under the fixed name [s]: a guard is written [s , P]    *)
(*  and expands to the predicate [fun s => P : Σ -> Prop].  (Coq cannot supply a truly invisible binder, so  *)
(*  the state is named once, right after the keyword.)  The loop index [i] of FOR is a [Z] bound in the body.*)
(*                                                                                                          *)

Declare Scope prog_scope.
Delimit Scope prog_scope with prog.

Notation "'UPDATE' s ':=' e" :=
  (update' (fun s => e))
  (at level 50, s ident,
   format "'UPDATE'  s  ':='  e") : prog_scope.

(* Multi-branch nondeterministic choice, one branch per [|] inside braces -- readable even when
   the branches are long.  Each arity expands directly to nested [choice] (no auxiliary function,
   no trailing empty program): [CHOOSE { a | b | c }] *is* [choice a (choice b c)].
   Supported for 2..6 branches; nest [CHOOSE]s for more. *)
Notation "'CHOOSE' '{' c1 '|' c2 '}'" :=
  (choice c1 c2)
  (at level 0, c1 at level 200, c2 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '}' ']'") : prog_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '}'" :=
  (choice c1 (choice c2 c3))
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '}' ']'") : prog_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '|' c4 '}'" :=
  (choice c1 (choice c2 (choice c3 c4)))
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200, c4 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '|'  c4 '//' '}' ']'") : prog_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '|' c4 '|' c5 '}'" :=
  (choice c1 (choice c2 (choice c3 (choice c4 c5))))
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200, c4 at level 200, c5 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '|'  c4 '//' '|'  c5 '//' '}' ']'") : prog_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '|' c4 '|' c5 '|' c6 '}'" :=
  (choice c1 (choice c2 (choice c3 (choice c4 (choice c5 c6)))))
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200, c4 at level 200, c5 at level 200, c6 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '|'  c4 '//' '|'  c5 '//' '|'  c6 '//' '}' ']'") : prog_scope.

Notation "'IF' s ',' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (if_else (fun s => b) c1 c2)
  (at level 0, s ident, b at level 99, c1 at level 200, c2 at level 200,
   format "'[v' 'IF'  s ','  b  'THEN' '//' c1 '//' 'ELSE' '//' c2 '//' 'FI' ']'") : prog_scope.

Notation "'WHEN' s ',' b 'THEN' c 'END'" :=
  (If (fun s => b) c)
  (at level 0, s ident, b at level 99, c at level 200,
   format "'[v' 'WHEN'  s ','  b  'THEN' '//' c '//' 'END' ']'") : prog_scope.

Notation "'WHILE' s ',' b 'DO' c 'END'" :=
  (whileP (fun s => b) c)
  (at level 0, s ident, b at level 99, c at level 200,
   format "'[v' 'WHILE'  s ','  b  'DO' '//' c '//' 'END' ']'") : prog_scope.

Notation "'FOR' i 'FROM' lo 'TO' hi 'DO' c 'END'" :=
  (range_iter lo hi (fun i _ => c) tt)
  (at level 0, i ident, lo at level 99, hi at level 99, c at level 200,
   format "'[v' 'FOR'  i  'FROM'  lo  'TO'  hi  'DO' '//' c '//' 'END' ']'") : prog_scope.

Notation "'LOOP' c 'END'" :=
  (repeat_break_noin c)
  (at level 0, c at level 200,
   format "'[v' 'LOOP' '//' c '//' 'END' ']'") : prog_scope.

(* Accumulator-carrying loop: [p] is the loop variable, [a0] its initial value; the body
   ends each round with [NEXT a'] to loop with [a'] or [BREAK b] to exit with result [b].
   This is the way to loop when there is no state to carry the iteration in (e.g. [MONAD R]). *)
Notation "'REPEAT' ' p 'FROM' a0 'DO' c 'END'" :=
  (repeat_break (fun p => c) a0)
  (at level 0, p strict pattern, a0 at level 99, c at level 200,
   format "'[v' 'REPEAT'  ' p  'FROM'  a0  'DO' '//' c '//' 'END' ']'") : prog_scope.

Notation "'BREAK' e" := (break e) (at level 50) : prog_scope.
Notation "'NEXT' a" := (continue a) (at level 50) : prog_scope.
Notation "'CONTINUE'" := (continue tt) (at level 0) : prog_scope.

Section monad_equiv_lemmas.
  Context {Σ: Type}.

  Lemma bind_equiv {A B: Type}: forall (c1 c1': program Σ A) (c2 c2': A -> program Σ B), 
    c1 == c1' -> c2 == c2'  ->
    bind c1 c2  == bind c1' c2'.
  Proof.
    intros.
    unfold_monad.
    constructor; sets_unfold; intros.
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
  Qed.


  Lemma bindpat_equiv {A B: Type}: forall (c1 c1': program Σ A) (c2 c2': A -> program Σ B), 
    c1 == c1' -> c2 == c2'  ->
    ' pat <- c1 ;; (c2 pat) == ' pat <- c1' ;; (c2' pat).
  Proof.
    intros.
    apply bind_equiv. auto.
    auto.
  Qed.

  Lemma bind_ret_left : forall {A B : Type} x (m : A -> program Σ B),
    bind (ret x) m == m x.
  Proof.
    intros.
    unfold bind, ret; simpl.
    unfold StateRelMonad.bind, StateRelMonad.ret.
    sets_unfold.
    intros s b s'.
    split; intros.
    - destruct H as [? [? [[? ?] ?]]].
      subst; tauto.
    - do 2 eexists. eauto.
  Qed.

  Lemma bind_ret_right : forall {A: Type} (m: program Σ A),
    bind m ret == m.
  Proof.
    intros.
    unfold bind, ret; simpl.
    unfold StateRelMonad.bind, StateRelMonad.ret.
    sets_unfold.
    intros s a s'.
    split; intros.
    - destruct H as (? & ? & ? & ? & ?).
      subst; tauto.
    - do 2 eexists. eauto.
  Qed.

  
  Lemma bind_assoc {A B C: Type}: 
    forall (c0: program Σ A) (c1: A -> program Σ B) (c2: B -> program Σ C),
      bind (bind c0 c1) c2 == bind c0 (fun x => bind (c1 x) c2).
  Proof.
    intros; simpl.
    sets_unfold; split; intros.
    + destruct H as [a2 [s0 [H H0]]].
      destruct H as [a3 [s1 [H1 H2]]].
      exists a3; exists s1; split; auto.
      exists a2; exists s0; tauto.
    + destruct H as [a2 [s0 [H0 H]]].
      destruct H as [a3 [s1 [H1 H2]]].
      exists a3; exists s1; split; auto.
      exists a2; exists s0; tauto.
  Qed.

  Lemma bind_fun_seq_equiv {B C D: Type}: 
    forall (c0: D -> program Σ unit) (c1: program Σ B) (c2: B -> program Σ C),
      (fun d => x <- (c0 d;; c1);; c2 x) == (fun d => ((c0 d);; x <- c1;; c2 x)).
  Proof.
    intros.
    sets_unfold. intro d. split; intros.
      + destruct H as [a2 [s0 [H H0]]].
        destruct H as [a3 [s1 [H1 H2]]].
        exists a3; exists s1; split; auto.
        exists a2; exists s0; tauto.
      + destruct H as [a2 [s0 [H0 H]]].
        destruct H as [a3 [s1 [H1 H2]]].
        exists a3; exists s1; split; auto.
        exists a2; exists s0; tauto.
  Qed.

  Lemma bind_choice_equiv {A B: Type}: 
    forall (c0 c1: program Σ A) (c2: A -> program Σ B),
      x <- (choice c0 c1);; c2 x == choice (x <- c0;; c2 x) (x <- c1;; c2 x).
  Proof.
    intros.
    unfold choice, bind; simpl.
    unfold StateRelMonad.bind; sets_unfold; split; intros.
      + destruct H as [a2 [s0 [H H0]]].
        destruct H.
        * left; do 2 eexists.
          split; eauto.
        * right; do 2 eexists.
          split; eauto.
      + destruct H; destruct H as [a2 [s0 [? ?]]];
        exists a2; exists s0; tauto.
  Qed.

  Lemma choice_case_equiv {A: Type}:
    forall (c0 c1 c2 c3: program Σ A),
      c0 == c2 ->
      c1 == c3 ->
      choice c0 c1 == choice c2 c3.
  Proof.
    sets_unfold.
    intros.
    specialize (H a a0 a1).
    specialize (H0 a a0 a1).
    unfold choice; constructor; sets_unfold; simpl; tauto.
  Qed.

  Lemma choice_comm {A: Type}:
    forall (c0 c1: program Σ A),
      choice c0 c1 == choice c1 c0.
  Proof.
    intros; unfold choice.
    simpl; apply Sets_union_comm.
  Qed.

  Lemma ret_equiv {A B: Type}: 
    forall (a: A) (c: A -> program Σ B),
      x <- ret a;; c x == c a.
  Proof.
    intros; simpl.
    unfold_monad. sets_unfold. 
      unfold ret; split; intros.
      + destruct H as [? [? [[? ?] ?]]].
        subst; tauto.
      + exists a; exists a0; tauto.
  Qed.

  Lemma ret_equiv' {A B C: Type}: 
    forall (f: A -> B) (c: A -> B -> program Σ C),
       (fun k => x <- ret (f k);; c k x) == (fun k => c  k (f k)).
  Proof.
    intros; simpl.
    unfold_monad; sets_unfold. 
    split; intros.
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
    unfold_monad; sets_unfold. 
    split; intros.
      + destruct H0 as [a2 [s0 ?]].
        specialize (H a2).
        destruct H0.
        specialize (H s0 a0 a1).
        apply H in H1.
        exists a2; exists s0;tauto.
      + destruct H0 as [a2 [s0 ?]].
        specialize (H a2).
        destruct H0.
        specialize (H s0 a0 a1).
        apply H in H1.
        exists a2; exists s0; tauto.
  Qed.
  
  Lemma choice_l_equiv {A: Type}:
    forall (c0 c1: program Σ A),
      c1 == ∅ -> choice c0 c1 == c0.
  Proof.
    intros. unfold choice; simpl; sets_unfold; split;  intros.
    - sets_unfold in H.
      destruct H0;auto.
      apply H in H0.
      contradiction.
    - auto. 
  Qed.

  Lemma choice_r_equiv {A: Type}:
    forall (c0 c1: program Σ A),
      c0 == ∅ -> choice c0 c1 == c1.
  Proof.
    intros. unfold choice; simpl; sets_unfold; split;  intros;auto.
      sets_unfold in H.
      destruct H0;auto.
      apply H in H0.
      contradiction.
  Qed.

  Lemma choice_idem_equiv {A: Type}:
    forall (c: program Σ A),
      choice c c == c.
  Proof.
    unfold choice. sets_unfold. intros. tauto.
  Qed.
End monad_equiv_lemmas.



Section Program_trans.
  Context {Σ₁ Σ₂: Type}.

  Definition programcall  {A : Type} (f: Σ₁ -> Σ₂) (g : Σ₂ -> Σ₁) 
                          (c: program Σ₂ A) : program Σ₁ A :=
    fun s1 a s2 => exists s0, c (f s1) a s0 /\ s2 = (g s0).
  
End Program_trans.



#[export] Instance bind_congr
  {Σ: Type} {A B: Type}:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) (@StateRelMonad.bind Σ A B).
Proof.
  unfold Proper, respectful.
  intros.
  apply bind_equiv; auto.
Qed.

#[export] Instance programbindpat_Proper
  {Σ: Type}  {A B: Type}:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv)  (fun c1 c2 => (@StateRelMonad.bind Σ A B  c1 (fun x => match x with pat => c2 end))).
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
  Proper (Sets.included ==> Sets.included ==> Sets.included) (@StateRelMonad.bind Σ A B).
Proof.
  unfold Proper, respectful.
  unfold_monad; sets_unfold.
  intros.
  destruct H1 as ( a2 & s2 & H2 & H3).
  exists a2, s2.
  split; [apply H | apply H0]; auto.
Qed.

#[export] Instance choice_equiv_Proper {Σ A: Type}:
  Proper (Sets.equiv ==> Sets.equiv  ==> Sets.equiv) (@choice Σ A).
Proof.
  unfold Proper, respectful; intros.
  apply choice_case_equiv; auto.
Qed.

Definition ATrue {Σ: Type} : Σ -> Prop := fun _ => True.

Ltac prog_nf :=
  repeat 
  (rewrite bind_assoc ||
   rewrite bind_choice_equiv ||
   rewrite ret_equiv || 
   rewrite ret_equiv').

Ltac prog_nf_in H :=
  repeat 
  (rewrite bind_assoc in H ||
   rewrite bind_choice_equiv in H ||
   rewrite ret_equiv in H || 
   rewrite ret_equiv' in H).

Tactic Notation "prog_nf" "in" hyp(H) :=
  prog_nf_in H.
