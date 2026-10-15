Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(n : Z) -> Z, the one digit that is left at the end.
   Alice swaps two digits standing at different positions, Bob then deletes the
   last digit, and the game stops when a single digit remains.  Only Alice
   chooses, so the answer is the smallest digit reachable by some play.

   [DecimalDigits x ds] says that [ds] is the decimal representation of the
   positive integer [x], most significant digit first; see the note in P001 on
   why the relation is restated here instead of shared. *)
Definition DecimalDigits (x : Z) (ds : list Z) : Prop :=
  1 <= Zlength ds /\
  Forall (fun d => 0 <= d <= 9) ds /\
  Znth 0 ds 0 <> 0 /\
  fold_left (fun acc d => acc * 10 + d) ds 0 = x.

Definition SwapStep (t t' : list Z) : Prop :=
  exists p q, 0 <= p < Zlength t /\ 0 <= q < Zlength t /\ p <> q /\
    t' = replace_Znth p (Znth q t 0) (replace_Znth q (Znth p t 0) t).

Definition DropLastStep (t t' : list Z) : Prop :=
  1 <= Zlength t /\ t' = sublist 0 (Zlength t - 1) t.

(* One round is a swap by Alice followed by a deletion by Bob, and the digit
   list loses one position per round until a single digit is left. *)
Definition ReachableDigit (ds : list Z) (d : Z) : Prop :=
  exists states : list (list Z),
    Zlength states = 2 * (Zlength ds - 1) + 1 /\
    Znth 0 states nil = ds /\
    (forall r, 0 <= r < Zlength ds - 1 ->
       SwapStep (Znth (2 * r) states nil) (Znth (2 * r + 1) states nil) /\
       DropLastStep (Znth (2 * r + 1) states nil)
                    (Znth (2 * r + 2) states nil)) /\
    Znth (2 * (Zlength ds - 1)) states nil = cons d nil.

Definition Pre (n : Z) : Prop :=
  (* Every clause below is stated explicitly in the P004 solver Require, whose
     ghost digit list carries the same conditions, so the Pre(...) call is
     omitted there:
       10 <= n <= 1000000000 /\
       exists ds, DecimalDigits n ds /\ Forall (fun d => d <> 0) ds. *)
  True.

Definition Spec (n out : Z) : Prop :=
  exists ds, DecimalDigits n ds /\
    min_value_of_subset Z.le (ReachableDigit ds) (fun x => x) out.

(* Representation bridge: the solver receives the number as its decimal string,
   every digit written as its character code, '0' = 48. *)
Definition DigitsAsChars (ds : list Z) : list Z :=
  map (fun d => d + 48) ds.
