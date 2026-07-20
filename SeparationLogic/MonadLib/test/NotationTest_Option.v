(** * Notation test: writing option-monad (partial) programs as inline pseudocode.

    The option monad has only [bind]/[ret]/[fmap], so -- per the "notation over
    existing only" choice -- the pseudocode layer is thin: the existing do-block
    already reads like imperative code and short-circuits on [None], and the one
    new form [MAP e FOR x IN mx] (defined at the end of [OptionBasic.v]) is sugar
    for [fmap].

    Each example is checked both concretely (by computation) and as pure sugar
    (definitionally equal to the underlying combinator term). *)

Require Import Coq.ZArith.ZArith.
From MonadLib Require Import Monad.
From MonadLib.OptionMonad Require Import OptionBasic.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope optprog_scope.

(** ** Example 1 — a partial computation written as a do-block (existing notation).
    The chain fails to [None] as soon as any bound step is [None]. *)
Definition add_opt (mx my: option Z) : option Z :=
  x <- mx ;;
  y <- my ;;
  return (x + y).

(** It behaves like the imperative reading -- short-circuiting on the first [None]. *)
Goal add_opt (Some 2) (Some 3) = Some 5.
Proof. reflexivity. Qed.
Goal add_opt None (Some 3) = None.
Proof. reflexivity. Qed.
Goal add_opt (Some 2) None = None.
Proof. reflexivity. Qed.

(** ...and it is exactly the desugared [bind] term. *)
Goal forall mx my,
  add_opt mx my = (x <- mx;; y <- my;; ret (x + y)).
Proof. intros; reflexivity. Qed.

(** ** Example 2 — the [MAP] comprehension is sugar for [fmap]. *)
Definition incr_opt (mx: option Z) : option Z :=
  MAP x + 1 FOR x IN mx.

Goal incr_opt (Some 4) = Some 5.
Proof. reflexivity. Qed.
Goal incr_opt None = None.
Proof. reflexivity. Qed.

Goal forall mx,
  incr_opt mx = fmap (fun x => x + 1) mx.
Proof. intros; reflexivity. Qed.
