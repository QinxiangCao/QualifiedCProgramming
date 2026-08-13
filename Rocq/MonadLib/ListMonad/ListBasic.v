(** Monadic operations on Lists. *)
(* Reference: https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/stdpp/list_monad.v *)

From MonadLib Require Import Monad.
From MonadLib.OptionMonad Require Import OptionMonad.
Import MonadNotation. Local Open Scope monad_scope.

Require Import Coq.Unicode.Utf8.

Require Import Coq.Lists.List. Import ListNotations.

#[export] Instance list_monad: Monad list := {
  bind := fun A B mx f =>
    (fix go (l : list A) := match l with [] => [] | x :: l => f x ++ go l end) mx;
  ret := fun A x => [x];
}.
Arguments Monad.bind _ _ _ _ !mx / f.
Arguments Monad.ret _ _ _ !x /.

#[export] Instance list_fmap : FMap list := λ A B f,
  fix go (l : list A) := match l with [] => [] | x :: l => f x :: go l end.

Definition mapM {M} `{Monad M} {A B} (f : A → M B) : list A → M (list B) :=
  fix go l :=
  match l with
  | [] => return []
  | x :: l => y <- f x;; k <- go l;; return (y :: k)
  end.

From Coq Require Import ssreflect ssrfun ssrbool.

Section mapM.
  Context {A B : Type} (f : A → option B).

  Lemma mapM_ext (g : A → option B) l : (∀ x, f x = g x) → mapM f l = mapM g l.
  Proof. intros Hfg. by induction l as [|?? IHl]; simpl; rewrite ?Hfg ?IHl. Qed.

  Lemma Forall2_mapM_ext (g : A → option B) l k :
    Forall2 (λ x y, f x = g y) l k → mapM f l = mapM g k.
  Proof. induction 1 as [|???? Hfg ? IH]; simpl; [done|]. by rewrite Hfg IH. Qed.
  Lemma Forall_mapM_ext (g : A → option B) l :
    Forall (λ x, f x = g x) l → mapM f l = mapM g l.
  Proof. induction 1 as [|?? Hfg ? IH]; simpl; [done|]. by rewrite Hfg IH. Qed.

  Lemma mapM_Some_1 l k : mapM f l = Some k → Forall2 (λ x y, f x = Some y) l k.
  Proof.
    revert k. induction l as [|x l]; intros [|y k]; simpl; try done.
    - destruct (f x); simpl; [|discriminate]. by destruct (mapM f l).
    - intros. constructor. 2: apply IHl.
      all: destruct (f x), (mapM f l); simpl in *; congruence.
  Qed.
  Lemma mapM_Some_2 l k : Forall2 (λ x y, f x = Some y) l k → mapM f l = Some k.
  Proof.
    induction 1 as [|???? Hf ? IH]; simpl; [done |].
    rewrite Hf. simpl. by rewrite IH.
  Qed.
  Lemma mapM_Some l k : mapM f l = Some k ↔ Forall2 (λ x y, f x = Some y) l k.
  Proof. split; auto using mapM_Some_1, mapM_Some_2. Qed.
  (* Lemma length_mapM l k : mapM f l = Some k → length l = length k.
  Proof. intros. by eapply Forall2_length, mapM_Some_1. Qed. *)
  Lemma mapM_None_1 l : mapM f l = None → Exists (λ x, f x = None) l.
  Proof.
    induction l as [|x l IH]; simpl; [done|].
    destruct (f x) eqn:?; simpl; eauto. by destruct (mapM f l); eauto.
  Qed.
  Lemma mapM_None_2 l : Exists (λ x, f x = None) l → mapM f l = None.
  Proof.
    induction 1 as [x l Hx|x l ? IH]; simpl; [by rewrite Hx|].
    by destruct (f x); simpl; rewrite ?IH.
  Qed.
  Lemma mapM_None l : mapM f l = None ↔ Exists (λ x, f x = None) l.
  Proof. split; auto using mapM_None_1, mapM_None_2. Qed.
  (* Lemma mapM_is_Some_1 l : is_Some (mapM f l) → Forall (is_Some ∘ f) l.
  Proof.
    unfold compose. setoid_rewrite <-not_eq_None_Some.
    rewrite mapM_None. apply (not_Exists_Forall _).
  Qed.
  Lemma mapM_is_Some_2 l : Forall (is_Some ∘ f) l → is_Some (mapM f l).
  Proof.
    unfold compose. setoid_rewrite <-not_eq_None_Some.
    rewrite mapM_None. apply (Forall_not_Exists _).
  Qed.
  Lemma mapM_is_Some l : is_Some (mapM f l) ↔ Forall (is_Some ∘ f) l.
  Proof. split; auto using mapM_is_Some_1, mapM_is_Some_2. Qed. *)

  (* Lemma mapM_fmap_Forall_Some (g : B → A) (l : list B) :
    Forall (λ x, f (g x) = Some x) l → mapM f (g <$> l) = Some l.
  Proof. by induction 1; simpl; simplify_option_eq. Qed.
  Lemma mapM_fmap_Some (g : B → A) (l : list B) :
    (∀ x, f (g x) = Some x) → mapM f (g <$> l) = Some l.
  Proof. intros. by apply mapM_fmap_Forall_Some, Forall_true. Qed. *)

  (* Lemma mapM_fmap_Forall2_Some_inv (g : B → A) (l : list A) (k : list B) :
    mapM f l = Some k → Forall2 (λ x y, f x = Some y → g y = x) l k → g <$> k = l.
  Proof. induction 2; simplify_option_eq; naive_solver. Qed.
  Lemma mapM_fmap_Some_inv (g : B → A) (l : list A) (k : list B) :
    mapM f l = Some k → (∀ x y, f x = Some y → g y = x) → g <$> k = l.
  Proof. eauto using mapM_fmap_Forall2_Some_inv, Forall2_true, length_mapM. Qed. *)

  Lemma mapM_app l1 l2 :
    mapM f (l1 ++ l2) =
    l1' <- mapM f l1;; l2' <- mapM f l2;; return (l1' ++ l2').
  Proof.
    induction l1 as [|hd l1']; simpl.
    - destruct (mapM f l2); [reflexivity|done].
    - rewrite IHl1'. destruct (f hd); simpl; auto.
      destruct (mapM f l1'); simpl; auto.
      destruct (mapM f l2); simpl; auto.
  Qed.

End mapM.

(*************************************************************************************************************)
(*****    Pseudocode notation for the list monad -- thin sugar over existing operations              ******)
(*************************************************************************************************************)
(*                                                                                                          *)
(*  The list monad models *nondeterministic search*: a program is the list of all its possible results.     *)
(*  Per the "notation over existing only" choice, both new forms desugar to operations that already exist:   *)
(*                                                                                                          *)
(*      CHOOSE { c1 | c2 | ... }                  == c1 ++ c2 ++ ...      -- either branch's results (app)    *)
(*      MAP e FOR x IN l                          == fmap (fun x => e) l  -- transform every result          *)
(*                                                                                                          *)
(*  Multi-result search still uses the existing do-block: [x <- l1;; y <- l2;; return (x, y)] enumerates      *)
(*  the cartesian product.                                                                                   *)
(*                                                                                                          *)

Declare Scope listprog_scope.
Delimit Scope listprog_scope with listprog.

(* Nondeterministic choice, one branch per [|] inside braces; expands directly to list append.
   2..6 branches; nest [CHOOSE]s for more. *)
Notation "'CHOOSE' '{' c1 '|' c2 '}'" :=
  (c1 ++ c2)
  (at level 0, c1 at level 200, c2 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '}' ']'") : listprog_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '}'" :=
  (c1 ++ c2 ++ c3)
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '}' ']'") : listprog_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '|' c4 '}'" :=
  (c1 ++ c2 ++ c3 ++ c4)
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200, c4 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '|'  c4 '//' '}' ']'") : listprog_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '|' c4 '|' c5 '}'" :=
  (c1 ++ c2 ++ c3 ++ c4 ++ c5)
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200, c4 at level 200, c5 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '|'  c4 '//' '|'  c5 '//' '}' ']'") : listprog_scope.
Notation "'CHOOSE' '{' c1 '|' c2 '|' c3 '|' c4 '|' c5 '|' c6 '}'" :=
  (c1 ++ c2 ++ c3 ++ c4 ++ c5 ++ c6)
  (at level 0, c1 at level 200, c2 at level 200, c3 at level 200, c4 at level 200, c5 at level 200, c6 at level 200,
   format "'[v' 'CHOOSE'  '{' '//' c1 '//' '|'  c2 '//' '|'  c3 '//' '|'  c4 '//' '|'  c5 '//' '|'  c6 '//' '}' ']'") : listprog_scope.

Notation "'MAP' e 'FOR' x 'IN' l" :=
  (fmap (fun x => e) l)
  (at level 0, e at level 99, x ident, l at level 99,
   format "'[v' 'MAP'  e  'FOR'  x  'IN'  l ']'") : listprog_scope.
