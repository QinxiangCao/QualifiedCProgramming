Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import Coq.ZArith.Znumtheory.

Local Open Scope Z_scope.

(* Signature: solve_case(n:Z)->Z. Output counts integers with exactly two
   distinct prime divisors. *)
Definition Pre (n : Z) : Prop :=
  (* Stated explicitly in the P008 solver Require, which therefore omits the
     Pre(...) call: 1 <= n <= 3000. *)
  True.
Definition AlmostPrime (x : Z) : Prop :=
  exists p q, prime p /\ prime q /\ p <> q /\ (p | x) /\ (q | x) /\
    forall r, prime r -> (r | x) -> r = p \/ r = q.
Definition Spec (n out : Z) : Prop :=
  out = #(fun x : Z => 1 <= x < n + 1 /\ AlmostPrime x).
