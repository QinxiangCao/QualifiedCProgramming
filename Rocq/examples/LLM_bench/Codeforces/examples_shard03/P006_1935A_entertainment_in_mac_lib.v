Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(n : Z, s : list Z) -> list Z, the printed string.
   [s] is the given string as character codes.  Operation 1 appends the reverse
   of the current string to it, operation 2 reverses it, and exactly [n]
   operations must be applied.

   [LexLt] is the statement's own definition of "lexicographically smaller":
   a proper prefix comes first, otherwise the first differing position decides.
   The minimum is stated inline rather than through [min_value_of_subset]
   because that facility needs a [TotalOrder] instance for its order and the
   repository supplies none for the lexicographic order on [list Z]. *)
Definition ApplyOp (t : list Z) (op : Z) : list Z :=
  if op =? 1 then t ++ rev t else rev t.

Definition ReachableString (s : list Z) (n : Z) (r : list Z) : Prop :=
  exists ops, Zlength ops = n /\ Forall (fun o => o = 1 \/ o = 2) ops /\
    r = fold_left ApplyOp ops s.

Definition LexLt (x y : list Z) : Prop :=
  exists k, 0 <= k <= Zlength x /\ k <= Zlength y /\
    sublist 0 k x = sublist 0 k y /\
    ((k = Zlength x /\ k < Zlength y) \/
     (k < Zlength x /\ k < Zlength y /\ Znth k x 0 < Znth k y 0)).

Definition Pre (n : Z) (s : list Z) : Prop :=
  (* Stated explicitly in the P006 solver Require, so dropped here:
       2 <= n <= 1000000000 /\
       1 <= Zlength s <= 100 /\ Forall (fun c => 97 <= c <= 122) s /\ *)
  Z.even n = true.

Definition Spec (n : Z) (s : list Z) (out : list Z) : Prop :=
  ReachableString s n out /\
  forall r, ReachableString s n r -> out = r \/ LexLt out r.
