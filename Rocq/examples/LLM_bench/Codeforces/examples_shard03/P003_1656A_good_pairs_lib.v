Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(a : list Z) -> Z * Z, the two printed indices.
   The output is relational: any pair of 1-based indices (i, j) is accepted as
   long as |a_i - a_k| + |a_k - a_j| = |a_i - a_j| holds for every k, and i may
   equal j. *)
Definition Pre (a : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P003 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength a <= 100000 /\ Forall (fun x => 1 <= x <= 1000000000) a. *)
  True.

Definition Spec (a : list Z) (i j : Z) : Prop :=
  1 <= i <= Zlength a /\ 1 <= j <= Zlength a /\
  forall k, 1 <= k <= Zlength a ->
    Z.abs (Znth (i - 1) a 0 - Znth (k - 1) a 0) +
    Z.abs (Znth (k - 1) a 0 - Znth (j - 1) a 0) =
    Z.abs (Znth (i - 1) a 0 - Znth (j - 1) a 0).
