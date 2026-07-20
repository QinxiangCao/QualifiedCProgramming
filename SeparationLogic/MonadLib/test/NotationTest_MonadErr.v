(** * Notation test: writing error-monad programs as inline pseudocode.

    This is the [progerr_scope] twin of [StateRelMonad/PseudocodeDemo.v]: the
    same imperative pseudocode ([UPDATE], [WHILE], [IF], [WHEN], [FOR], [LOOP],
    [CHOOSE], [REPEAT], [BREAK]/[NEXT]/[CONTINUE]) but over the error monad
    [MonadErr.M] (a state monad that can also fault).  The notation layer is
    defined at the end of [MonadErrLoop.v].

    As before, the notation is pure surface syntax: each example is proved
    *definitionally equal* (by [reflexivity]) to the underlying combinator term. *)

Require Import Coq.ZArith.ZArith.
Require Import SetsClass.SetsClass.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrLoop.
Import Monad MonadNotation SetsNotation.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
Local Open Scope progerr_scope.

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

(** ** Example 4 — nondeterministic choice between whole branches. *)
Definition guess_bit : program st unit :=
  CHOOSE {
    UPDATE s := seti s 0
  | UPDATE s := seti s 1
  }.

Goal guess_bit =
  choice (update' (fun s => seti s 0)) (update' (fun s => seti s 1)).
Proof. reflexivity. Qed.

(** ** Example 5 — a *stateless* program ([program unit R]).

    With no meaningful state, the loop variable rides in [repeat_break]'s
    accumulator, and control flow uses [assume!!] guards + [CHOOSE] instead of
    [IF] -- each round either loops on with [NEXT a'] or exits with [BREAK b]. *)
Definition sum_upto_pure (n: Z) : program unit Z :=
  REPEAT '(k, acc) FROM (0, 0) DO
    CHOOSE {
      assume!! (k <= n) ;; NEXT (k + 1, acc + k)
    | assume!! (k > n)  ;; BREAK acc
    }
  END.

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
