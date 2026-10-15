Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import ListLib.General.IndexedElements.

Import ListNotations.
Local Open Scope Z_scope.

(* Per-case signature: solve_case(a,b:list Z)->option(list Z).
   Some c is a shortest nonempty common subsequence; None means none exists. *)
Definition Pre (a b : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P002 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength a <= 1000 /\ 1 <= Zlength b <= 1000 /\
       Forall (fun x => 1 <= x <= 1000) a /\
       Forall (fun x => 1 <= x <= 1000) b. *)
  True.

Definition CommonNonempty (a b c : list Z) : Prop :=
  c <> [] /\ is_subsequence c a /\ is_subsequence c b.

Definition Spec (a b : list Z) (out : option (list Z)) : Prop :=
  (out = None /\ ~ exists c, CommonNonempty a b c) \/
  (exists c, out = Some c /\ (fun P xs => min_object_of_subset Z.le P (fun ys => Zlength ys) xs) (CommonNonempty a b) c).
