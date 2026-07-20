Require Import SetsClass.SetsClass.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
From FP Require Import SetsFixedpoints.
Import SetsNotation.
Local Open Scope sets.
From MonadLib.SetMonad Require Import SetBasic.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope sets.

(** * Hoare Logic for the SetMonad *)

(** In the set monad, the Hoare triple degenerates to a Hoare pair. *)

Definition Hoare {A: Type} (c: program A) (P: A -> Prop): Prop :=
  forall a, a ∈ c -> P a.

Theorem Hoare_bind {A B: Type}:
  forall (f: program A)
         (g: A -> program B)
         (P: A -> Prop)
         (Q: B -> Prop),
    Hoare f P ->
    (forall a, P a -> Hoare (g a) Q) ->
    Hoare (bind f g) Q.
Proof.
  intros.
  unfold Hoare; sets_unfold;
  unfold bind, set_monad, SetMonad.bind.
  intros b [a [? ?]].
  specialize (H _ H1).
  specialize (H0 _ H _ H2).
  tauto.
Qed.

Theorem Hoare_ret {A: Type}:
  forall (a: A) (P: A -> Prop),
    P a -> Hoare (ret a) P.
Proof.
  intros.
  unfold Hoare, ret, set_monad, SetMonad.ret; sets_unfold.
  intros.
  rewrite <- H0; tauto.
Qed.

Theorem Hoare_conseq {A: Type}:
  forall (f: program A) (P Q: A -> Prop),
    (forall a, P a -> Q a) ->
    Hoare f P ->
    Hoare f Q.
Proof.
  unfold Hoare; intros.
  specialize (H a).
  specialize (H0 a).
  tauto.
Qed.

Theorem Hoare_conj {A: Type}:
  forall (f: program A) (P Q: A -> Prop),
    Hoare f P ->
    Hoare f Q ->
    Hoare f (fun a => P a /\ Q a).
Proof.
  unfold Hoare; intros.
  specialize (H a).
  specialize (H0 a).
  tauto.
Qed.

Theorem Hoare_choice {A: Type}:
  forall (f g: program A)
         (P: A -> Prop),
    Hoare f P ->
    Hoare g P ->
    Hoare (choice f g) P.
Proof.
  intros.
  unfold Hoare; sets_unfold; unfold choice; Sets_unfold.
  intros.
  destruct H1; [apply H | apply H0]; tauto.
Qed.

Theorem Hoare_assume {Σ: Type}:
  forall (Q: Prop),
    Hoare (assume Q) (fun _ => Q).
Proof.
  intros.
  unfold Hoare, test; sets_unfold.
  intros; tauto.
Qed.

Theorem Hoare_assume_bind {A: Type}:
  forall (P: Prop)
         (f: program A)
         (Q: A -> Prop),
    (P -> Hoare f Q) ->
    (Hoare (assume P;; f) Q).
Proof.
  intros.
  apply (Hoare_bind _ _ (fun _ => P)).
  + unfold Hoare, test; sets_unfold.
    tauto.
  + tauto.
Qed.

Theorem Hoare_any:
  forall (A: Type),
    Hoare (any A) (fun _ => True).
Proof.
  intros.
  unfold Hoare, any; sets_unfold.
  intros; tauto.
Qed.

Theorem Hoare_any_bind {A B: Type}:
  forall (f: A -> program B)
         (P: B -> Prop),
    (forall a, Hoare (f a) P) ->
    Hoare (x <- any A;; f x) P.
Proof.
  intros.
  eapply Hoare_bind; [apply Hoare_any |].
  simpl.
  intros; auto.
Qed.

Definition continue_case {A B: Type} : CntOrBrk A B -> program A :=
  fun x =>
    match x with
    | by_continue a => ret a
    | by_break _ => ∅
    end.

Definition break_case {A B: Type} : CntOrBrk A B -> program B :=
  fun x =>
    match x with
    | by_continue _ => ∅
    | by_break b => ret b
    end.
  
Lemma Hoare_sum {A B: Type}:
  forall (c: program (CntOrBrk A B)) (Q: A ->Prop) (R: B -> Prop),
    Hoare (x <- c;; continue_case x) Q ->
    Hoare (x <- c;; break_case x) R ->
    Hoare c (fun x => match x with
                        | by_continue a => Q a
                        | by_break b => R b
                        end).
Proof.
  unfold Hoare in *; intros.
  destruct a.
  - specialize (H a).
    apply H; clear H.
    unfold bind; simpl.
    unfold SetMonad.bind; sets_unfold.
    exists (by_continue a).
    simpl; unfold ret; simpl; unfold SetMonad.ret; simpl.
    sets_unfold in H1; easy.
  - specialize (H0 b).
    apply H0; clear H.
    unfold bind; simpl.
    unfold SetMonad.bind; sets_unfold.
    exists (by_break b).
    simpl; unfold ret; simpl; unfold SetMonad.ret; simpl.
    sets_unfold in H1; easy.
Qed.

Lemma Hoare_empty {A: Type}:
  forall (P: A -> Prop),
    Hoare ∅ P.
Proof.
  unfold Hoare; sets_unfold; tauto.
Qed.

#[export] Instance Hoare_equiv_iff_Proper {A: Type}:
  Proper (Sets.equiv ==> eq ==> iff) (@Hoare A).
Proof.
  unfold Proper, respectful; intros.
  unfold Hoare; sets_unfold in H.
  subst; split; intros; apply H0; apply H; auto.
Qed.

Lemma Hoare_equiv_iff {A: Type}:
  forall (f g: program A) (P: A -> Prop),
    f == g ->
    Hoare f P <-> Hoare g P.
Proof.
  intros; rewrite H; easy.
Qed.


(** Tactics *)
Tactic Notation "hoare_bind" uconstr(H) :=
  eapply Hoare_bind; [apply H |]; intros.

Ltac hoare_conj :=
  match goal with
    | |- Hoare _ (fun _ => _ /\ _) => apply Hoare_conj; [| try hoare_conj]
  end.

Ltac hoare_step := 
  unfold continue, break, continue_case, break_case;
  match goal with
    | |- Hoare (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_step
    | |- Hoare (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_step
    | |- Hoare (bind (ret _) _) _ => rewrite bind_ret_l
    | |- Hoare (bind (any _) _) _ => apply Hoare_any_bind; intros
    | |- Hoare (assume _ ;; _) _ => apply Hoare_assume_bind; intros
    | |- Hoare (choice _ _) _ => apply Hoare_choice
    | |- Hoare (ret _) _ => apply Hoare_ret; intros
    | |- Hoare (match ?a with _ => _ end) _ => destruct a; hoare_step
    | |- Hoare ∅ _ => apply Hoare_empty
  end; auto.

Ltac hoare_auto :=
  unfold continue, break, continue_case, break_case;
  match goal with
    | |- Hoare (bind (bind _ _) _) _ => rewrite bind_assoc; try hoare_auto
    | |- Hoare (bind (choice _ _) _) _ => rewrite bind_choice_equiv; try hoare_auto
    | |- Hoare (bind (ret _) _) _ => rewrite bind_ret_l; try hoare_auto
    | |- Hoare (bind (any _) _) _ => apply Hoare_any_bind; intros; try hoare_auto
    | |- Hoare (assume _ ;; _) _ => apply Hoare_assume_bind; intros; try hoare_auto
    | |- Hoare (choice _ _) _ => apply Hoare_choice; try hoare_auto
    | |- Hoare (ret _) _ => apply Hoare_ret; intros
    | |- Hoare (match ?a with _ => _ end) _ => destruct a; try hoare_auto
    | |- Hoare ∅ _ => apply Hoare_empty
  end; auto.

Ltac monad_law :=
  repeat (rewrite bind_assoc ||
          rewrite bind_ret_l ||
          rewrite bind_ret_r).

Ltac intro_bound :=
  unfold Sets.equiv; simpl; unfold Sets.lift_equiv; intros.

Ltac monad_equiv :=
  unfold continue, break, continue_case, break_case;
  repeat (monad_law; try easy;
          apply bind_congr; try easy;
          intro_bound).

Tactic Notation "hoare_apply" uconstr(H) :=
  eapply Hoare_equiv_iff;
  [ | apply H; try tauto];
  monad_equiv.

(** Hoare Logic for Loops *)
Theorem Hoare_fix {A B: Type}:
  forall (P: A -> Prop) (Q: A -> B -> Prop) (f: (A -> program B) -> A -> program B) (a: A), 
  (forall W: A -> program B,
    (forall a, P a -> Hoare (W a) (Q a)) -> (forall a, P a -> Hoare (f W a) (Q a))) ->
  P a -> Hoare (Lfix f a) (Q a).
Proof.
  unfold Lfix; unfold Hoare.
  sets_unfold; intros.
  rename a0 into b; destruct H1 as [i Hi].
  revert H0 Hi; revert a b.
  induction i; intros.
  - simpl in Hi; tauto.
  - simpl in Hi.
    apply H with (W:=(Nat.iter i f (fun (_ : A) (_ : B) => False))) (a:=a); auto.
Qed.

Theorem Hoare_fix' {A B: Type}:
  forall (P: A -> Prop) (Q: B -> Prop) (f: (A -> program B) -> A -> program B) (a: A), 
  (forall W: A -> program B,
    (forall a, P a -> Hoare (W a) Q) -> (forall a, P a -> Hoare (f W a) Q)) ->
  P a -> Hoare (Lfix f a) Q.
Proof.
  intros; revert H0.
  apply Hoare_fix with (Q:=fun _ => Q); auto.
Qed.

(** Backend-independent recursion rule. *)
Theorem Hoare_Rec {A B: Type}:
  forall (P: A -> Prop)
         (Q: A -> B -> Prop)
         (F: (A -> program B) -> A -> program B)
         (a: A),
    (forall W: A -> program B,
      (forall a, P a -> Hoare (W a) (Q a)) ->
      forall a, P a -> Hoare (F W a) (Q a)) ->
    P a -> Hoare (Rec F a) (Q a).
Proof.
  intros. unfold Rec. eapply Hoare_fix; eauto.
Qed.

Tactic Notation "hoare_rec" uconstr(P) uconstr(Q) :=
  lazymatch goal with
  | |- Hoare (Rec ?F ?a) _ => eapply (@Hoare_Rec _ _ P Q F a)
  | |- ?G => fail 1 "hoare_rec: expected a Hoare goal headed by Rec" G
  end.

Theorem Hoare_repeat_break' {A B: Type}:
  forall (body: A -> program (CntOrBrk A B))
         (P: A -> Prop)
         (Q: B -> Prop),
    (forall a, P a ->
               Hoare (body a) (fun x => match x with
                                        | by_continue a => P a
                                        | by_break b => Q b
                                        end)) ->
    (forall a, P a -> Hoare (repeat_break body a) Q).
Proof.
  intros.
  unfold repeat_break.
  apply (Hoare_fix P (fun _ => Q)); auto.
  intros.
  unfold repeat_break_f.
  eapply Hoare_bind. 
  apply H; auto.
  intros; simpl in H3.
  destruct a1.
  - apply H1; auto.
  - apply Hoare_ret; auto.
Qed.

Theorem Hoare_range_iter {A: Type}:
  forall (f: nat -> A -> program A)
         (P: nat -> A -> Prop)
         (lo hi: nat),
    lo <= hi ->
    (forall i, lo <= i < hi -> forall a,
       P i a ->
       Hoare (f i a) (fun a' => P (i+1) a')) ->
    (forall a,
       P lo a ->
       Hoare (range_iter lo hi f a)
             (fun a' => P hi a')).
Proof.
  intros.
  unfold range_iter.
  apply (Hoare_fix 
    (fun '(n, a) => P n a /\ lo <= n <= hi) 
    (fun _ a' => P hi a')); auto.
  intros.
  unfold range_iter_f.
  destruct a0.
  hoare_auto.
  2:{
    assert (n = hi) by lia.
    subst; tauto.
  }
  specialize (H0 n (ltac:(lia)) a0 (ltac:(tauto))).
  hoare_bind H0.
  apply H2; split; [tauto | lia].
Qed.

Theorem Hoare_range_iter_break' {A B: Type}:
  forall (f: nat -> A -> program (CntOrBrk A B))
         (P: nat -> A -> Prop)
         (Q: B -> Prop) (lo hi: nat),
    lo <= hi ->
    (forall i, lo <= i < hi -> forall a,
       P i a ->
       Hoare (f i a) (fun res => match res with
                                 | by_continue a => P (i+1) a
                                 | by_break b => Q b
                                 end)) -> 
    (forall a,
       P lo a ->
       Hoare (range_iter_break lo hi f a)
             (fun res => match res with
                          | by_continue a => P hi a
                         | by_break b => Q b                              
                         end)).
Proof.
  intros.
  unfold range_iter_break.
  match goal with
  | |- Hoare (Rec _ _) ?X => set (K := X)
  end.
  eapply Hoare_Rec with (P:= fun '(i, a) => P i a /\ lo <= i <= hi)(Q :=fun _ => K); auto.
  unfold K; clear K.
  intros; unfold range_iter_break_f.
  hoare_auto.
  2:{
    assert (n = hi) by lia.
    subst; tauto.
  }
  specialize (H0 n (ltac:(lia)) a0 (ltac:(tauto))).
  hoare_bind H0.
  hoare_auto.
  apply H2; split; [tauto | lia]. 
Qed.

Theorem Hoare_repeat_break {A B: Type}:
  forall (body: A -> program (CntOrBrk A B))
         (P: A-> Prop) (Q: B -> Prop),
    (forall a, P a -> Hoare (x <- body a;; continue_case x) P) ->
    (forall a, P a -> Hoare (x <- body a;; break_case x) Q) -> 
    (forall a, P a -> Hoare (repeat_break body a) Q).
Proof.
  intros.
  apply (Hoare_repeat_break' _ P); auto.
  intros; apply Hoare_sum; auto.
Qed.

Theorem Hoare_range_iter_break {A B: Type}:
  forall (f: nat -> A -> program (CntOrBrk A B))
         (P: nat -> A -> Prop)
         (Q: B -> Prop) (lo hi: nat),
    lo <= hi ->
    (forall i, lo <= i < hi -> forall a,
       P i a ->
       Hoare (x <- f i a;; continue_case x) (fun a => P (i+1) a)) -> 
    (forall i, lo <= i < hi -> forall a,
       P i a ->
       Hoare (x <- f i a;; break_case x) Q) ->
    (forall a,
       P lo a ->
       Hoare (range_iter_break lo hi f a)
             (fun res => match res with
                          | by_continue a => P hi a
                          | by_break b => Q b                              
                          end)).
Proof.
  intros.
  apply (Hoare_range_iter_break' _ P); auto.
  intros; apply Hoare_sum; auto.
Qed.

Lemma Hoare_list_iter {A B} (f : A -> B -> program B) (P : list A -> B -> Prop) :
  (forall b l' a, P l' b -> Hoare (f a b) (P (l' ++ a :: nil))) ->
  forall b l, 
    P nil b -> 
    Hoare (list_iter f l b) (P l). 
Proof.
  intros ? ?.
  assert (H_gen: forall l b prefix, 
            P prefix b -> 
            Hoare (list_iter f l b) (P (prefix ++ l))).
  {
    induction l; intros.
    - simpl.
      rewrite app_nil_r. 
      apply Hoare_ret.
      auto.
    - simpl.
      apply (Hoare_bind _ _ (P (prefix ++ cons a nil))).
      + auto. 
      + intros b' H_mid.
        specialize (IHl b' (prefix ++ cons a nil) H_mid).
        rewrite <- app_assoc in IHl.
        auto. 
  }
  intros.  
  specialize (H_gen l b nil H0).
  simpl in H_gen.
  apply H_gen.
Qed.
