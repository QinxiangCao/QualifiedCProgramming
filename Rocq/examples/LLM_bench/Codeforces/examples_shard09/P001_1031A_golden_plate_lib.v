Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(w,h,k:Z)->Z. Output is the number of cells belonging
   to one of the k stated borders. *)
Definition Pre (w h k : Z) : Prop :=
  (* The solver Require states these constraints explicitly:
       3 <= w <= 100 /\ 3 <= h <= 100 /\
       1 <= k /\ 4 * k <= Z.min w h + 1. *)
  True.

Definition RingCell (w h k row col : Z) : Prop :=
  0 <= row < w /\ 0 <= col < h /\
  exists i, 0 <= i < k /\
    ((row = 2 * i \/ row = w-1-2*i) /\ 2 * i <= col < h-2 * i \/
     (col = 2 * i \/ col = h-1-2*i) /\ 2 * i <= row < w-2 * i).

Definition Spec (w h k out : Z) : Prop :=
  out = #(fun z : Z =>
    0 <= z < w*h /\ RingCell w h k (z / h) (z mod h)).
