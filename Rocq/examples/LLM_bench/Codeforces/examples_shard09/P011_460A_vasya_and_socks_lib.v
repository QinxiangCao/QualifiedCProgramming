Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* Signature: solve_case(n,m:Z)->Z. Output is the consecutive number of days
   for which a morning pair exists, accounting for each m-th evening purchase. *)
Definition Pre (n m : Z) : Prop :=
  (* Stated explicitly in the P011 solver Require, which therefore omits the
     Pre(...) call: 1 <= n <= 100 /\ 2 <= m <= 100. *)
  True.
Definition Spec (n m out : Z) : Prop :=
  out > 0 /\ (forall d, 1 <= d <= out -> n + (d - 1) / m - (d - 1) > 0) /\
  n + out / m - out = 0.
