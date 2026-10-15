Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(n : Z) -> Z, with 1 = "YES" and 0 = "NO".
   A number is nearly lucky when the amount of its lucky digits (4 and 7) is
   itself a lucky number, i.e. a positive integer written with 4s and 7s only.

   [DecimalDigits x ds] says that [ds] is the decimal representation of the
   positive integer [x], most significant digit first.  No repository facility
   states the decimal expansion of a [Z]; the same relation is therefore
   restated in P004 and P007, which need the statement's own notion of the
   digits of the given number.  The three specs must stay standalone, so the
   relation cannot be shared through a module. *)
Definition DecimalDigits (x : Z) (ds : list Z) : Prop :=
  1 <= Zlength ds /\
  Forall (fun d => 0 <= d <= 9) ds /\
  Znth 0 ds 0 <> 0 /\
  fold_left (fun acc d => acc * 10 + d) ds 0 = x.

Definition LuckyNumber (x : Z) : Prop :=
  exists ds, DecimalDigits x ds /\ Forall (fun d => d = 4 \/ d = 7) ds.

Definition NearlyLucky (n : Z) : Prop :=
  exists ds, DecimalDigits n ds /\
    LuckyNumber
      (#(fun i : Z => 0 <= i < Zlength ds /\
                      (Znth i ds 0 = 4 \/ Znth i ds 0 = 7))).

Definition Pre (n : Z) : Prop :=
  (* Every clause below is stated explicitly in the P001 solver Require, which
     therefore omits the Pre(...) call:
       1 <= n <= 1000000000000000000. *)
  True.

Definition Spec (n out : Z) : Prop :=
  (out = 1 /\ NearlyLucky n) \/ (out = 0 /\ ~ NearlyLucky n).

(* Representation bridge: the solver receives the number as its decimal string,
   every digit written as its character code, '0' = 48. *)
Definition DigitsAsChars (ds : list Z) : list Z :=
  map (fun d => d + 48) ds.
