(** * Notation test: writing list-monad (nondeterministic search) programs inline.

    The list monad enumerates all possible results of a nondeterministic
    computation.  Per the "notation over existing only" choice, the pseudocode
    layer (defined at the end of [ListBasic.v]) is sugar over operations that
    already exist: [CHOOSE] over list append [++], and [MAP] over [fmap].
    Cartesian-product search uses the existing do-block.

    Each example is checked both concretely (by computation) and as pure sugar. *)

Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith.
From MonadLib Require Import Monad.
From MonadLib.ListMonad Require Import ListBasic.
Import MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope listprog_scope.

(** ** Example 1 — nondeterministic choice, written whole ([CHOOSE] = append). *)
Definition pick_small : list Z :=
  CHOOSE {
    ret 0
  | ret 1
  | ret 2
  }.

Goal pick_small = [0; 1; 2].
Proof. reflexivity. Qed.

Goal pick_small = (ret 0 ++ ret 1 ++ ret 2).
Proof. reflexivity. Qed.

(** ** Example 2 — [MAP] transforms every result ([MAP] = fmap). *)
Definition doubles (l: list Z) : list Z :=
  MAP x + x FOR x IN l.

Goal doubles [1; 2; 3] = [2; 4; 6].
Proof. reflexivity. Qed.

Goal forall l,
  doubles l = fmap (fun x => x + x) l.
Proof. intros; reflexivity. Qed.

(** ** Example 3 — cartesian-product search via the existing do-block. *)
Definition pairs (l1 l2: list Z) : list (Z * Z) :=
  x <- l1 ;;
  y <- l2 ;;
  return (x, y).

Goal pairs [1; 2] [3; 4] = [(1,3); (1,4); (2,3); (2,4)].
Proof. reflexivity. Qed.

Goal forall l1 l2,
  pairs l1 l2 = (x <- l1;; y <- l2;; ret (x, y)).
Proof. intros; reflexivity. Qed.
