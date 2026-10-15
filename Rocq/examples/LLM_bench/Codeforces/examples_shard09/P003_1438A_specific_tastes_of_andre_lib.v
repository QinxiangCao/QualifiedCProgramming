Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Per-case signature: solve_case(n:Z)->list Z. Output is any perfect array. *)
Definition Pre (n : Z) : Prop :=
  (* Stated explicitly in the P003 solver Require, which therefore omits the
     Pre(...) call: 1 <= n <= 100. *)
  True.

Definition Perfect (n : Z) (a : list Z) : Prop :=
  Zlength a = n /\ Forall (fun x => 1 <= x <= 100) a /\
  forall l r, 0 <= l < r /\ r <= n -> (r-l | (fold_right Z.add 0) (sublist l r a)).

Definition Spec (n : Z) (out : list Z) : Prop := Perfect n out.

Definition VerdictCode (answer : bool) (code : Z) : Prop :=
  (answer = true /\ code = 1) \/
  (answer = false /\ code = 0).
