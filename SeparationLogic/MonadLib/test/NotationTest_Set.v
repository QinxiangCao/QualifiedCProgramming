(** * Notation test: writing set-monad (nondeterministic) programs as inline pseudocode.

    Everything below uses the [setprog_scope] notation layer defined at the end of
    [SetBasic.v].  The set monad has no state, so this is the *nondeterministic*
    subset of StateRelMonad's pseudocode: [CHOOSE] for choice, [REPEAT]/[FOR] for
    loops, [NEXT]/[BREAK]/[CONTINUE] for loop-body control, and the pre-existing
    [assume] guard.

    As in [StateRelMonad/PseudocodeDemo.v], the notation is pure surface syntax:
    each example is proved *definitionally equal* (by [reflexivity]) to the
    underlying combinator term. *)

Require Import SetsClass.SetsClass.
From MonadLib.SetMonad Require Import SetBasic.
Import Monad MonadNotation SetsNotation.
Local Open Scope nat.
Local Open Scope monad_scope.
Local Open Scope setprog_scope.

(** ** Example 1 — a two-way nondeterministic choice, written whole.
    [CHOOSE { c1 | c2 }] puts one branch per [|] inside braces. *)
Definition pick_bit : program nat :=
  CHOOSE {
    ret 0
  | ret 1
  }.

Goal pick_bit = choice (ret 0) (ret 1).
Proof. reflexivity. Qed.

(** ** Example 2 — the same notation scales to any number of branches. *)
Definition pick_small : program nat :=
  CHOOSE {
    ret 0
  | ret 1
  | ret 2
  }.

Goal pick_small = choice (ret 0) (choice (ret 1) (ret 2)).
Proof. reflexivity. Qed.

(** ** Example 3 — an accumulator loop with [REPEAT] + guarded [CHOOSE].

    With no state to carry the iteration, the loop variable rides in
    [repeat_break]'s accumulator ([REPEAT '(k, acc) FROM (0,0) DO ... END]).
    Each round either loops on with [NEXT a'] or exits with [BREAK b]; the
    [assume] guards pick which branch of the nondeterministic [CHOOSE] can fire. *)
Definition sum_upto (n: nat) : program nat :=
  REPEAT '(k, acc) FROM (0, 0) DO
    CHOOSE {
      assume (k <= n) ;; NEXT (k + 1, acc + k)
    | assume (k > n)  ;; BREAK acc
    }
  END.

Goal forall n,
  sum_upto n =
    repeat_break
      (fun '(k, acc) =>
         choice (assume (k <= n);; continue (k + 1, acc + k))
                (assume (k > n) ;; break acc))
      (0, 0).
Proof. intros; reflexivity. Qed.

(** ** Example 4 — a counted [FOR] loop over [0, n) threading an accumulator.
    ([FOR] here carries its own accumulator [acc] since the set monad has no
    state; the loop index [i] is a [nat] bound in the body.) *)
Definition sum_for (n: nat) : program nat :=
  FOR i FROM 0 TO n WITH 'acc := 0 DO
    ret (acc + i)
  END.

Goal forall n,
  sum_for n = range_iter 0 n (fun i acc => ret (acc + i)) 0.
Proof. intros; reflexivity. Qed.

(** Print any of them to see the pseudocode round-trip on display: *)
(* Print sum_upto. *)
(* Print sum_for. *)
