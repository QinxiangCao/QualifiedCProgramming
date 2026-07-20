(** * Demo: writing abstract state-relation programs as inline pseudocode.

    Everything below uses the [prog_scope] notation layer defined at the end of
    [StateRelBasic.v].  The point of the demo is that a whole abstract program
    can be written in one [Definition], the way you would sketch it on paper,
    without introducing auxiliary [Definition]s for each loop/branch body and
    stitching them together by hand with [bind].

    The notation is pure surface syntax: each example is proved to be
    *definitionally equal* (by [reflexivity]) to the underlying combinator term. *)

Require Import Coq.ZArith.ZArith.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic.
Import Monad MonadNotation SetsNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope prog_scope.

(** A toy state: a loop counter [i] and a running [sum]. *)
Record st := { i : Z ; sum : Z }.

Definition seti   (s: st) (v: Z) : st := {| i := v ;      sum := s.(sum) |}.
Definition setsum (s: st) (v: Z) : st := {| i := s.(i) ;  sum := v       |}.

(** ** Example 1 — a [WHILE] loop, written whole. *)
Definition sum_upto (n: Z) : program st unit :=
  UPDATE s := seti s 0 ;;
  UPDATE s := setsum s 0 ;;
  WHILE s, s.(i) < n DO
    UPDATE s := setsum s (s.(sum) + s.(i)) ;;
    UPDATE s := seti s (s.(i) + 1)
  END.

(** It is exactly the desugared combinator term — the notation adds no content. *)
Goal forall n,
  sum_upto n =
    (update' (fun s => seti s 0);;
     update' (fun s => setsum s 0);;
     whileP (fun s => s.(i) < n)
            (update' (fun s => setsum s (s.(sum) + s.(i)));;
             update' (fun s => seti s (s.(i) + 1)))).
Proof. intros; reflexivity. Qed.

(** ** Example 2 — a counted [FOR] loop with a one-armed guard inside. *)
Definition sum_evens (n: Z) : program st unit :=
  UPDATE s := setsum s 0 ;;
  FOR k FROM 0 TO n DO
    WHEN s, Z.even k = true THEN
      UPDATE s := setsum s (s.(sum) + k)
    END
  END.

(** ** Example 3 — a [LOOP] with [BREAK]/[CONTINUE] and a two-armed [IF]. *)
Definition first_i_reaching_10 : program st Z :=
  LOOP
    IF s, s.(i) >= 10 THEN
      r <- get' (fun s => s.(sum)) ;;
      BREAK r
    ELSE
      UPDATE s := setsum s (s.(sum) + s.(i)) ;;
      UPDATE s := seti s (s.(i) + 1) ;;
      CONTINUE
    FI
  END.

(** ** Example 4 — nondeterministic choice between whole branches.
    [CHOOSE { .. | .. | .. }] puts one branch per [|] inside braces, so long
    branches stay readable.  The same notation covers any number of branches
    (here just two). *)
Definition guess_bit : program st unit :=
  CHOOSE {
    UPDATE s := seti s 0
  | UPDATE s := seti s 1
  }.

(** ** Example 5 — a *stateless* program: [MONAD R] (the state is [unit]).

    With no state to carry the iteration, the loop variable rides in
    [repeat_break]'s accumulator ([REPEAT '(k, acc) FROM (0,0) DO ... END]).
    Control flow uses [assume!!] guards + nondeterministic choice [CHOOSE] instead
    of [IF] -- each round either loops on with [NEXT a'] or exits with [BREAK b]. *)
Definition sum_upto_pure (n: Z) : MONAD Z :=
  REPEAT '(k, acc) FROM (0, 0) DO
    CHOOSE {
      assume!! (k <= n) ;; NEXT (k + 1, acc + k)
    | assume!! (k > n)  ;; BREAK acc
    }
  END.

(** Same claim as the others: the notation is pure sugar for the combinators.
    [CHOOSE { a | b }] computes to exactly [choice a b] -- no trailing empty program. *)
Goal forall n,
  sum_upto_pure n =
    repeat_break
      (fun '(k, acc) =>
         choice (assume!! (k <= n);; continue (k + 1, acc + k))
                (assume!! (k > n) ;; break acc))
      (0, 0).
Proof. intros; reflexivity. Qed.

(** Print any of them to see the pseudocode round-trip on display: *)
(* Print sum_upto. *)
(* Print sum_upto_pure. *)
(* Print first_i_reaching_10. *)
