Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(cells : list Z) -> Z, the least number of action-1
   steps needed.  [cells] is the row as character codes, 46 = '.' (empty) and
   35 = '#' (blocked).  A water configuration is a list of the same length
   holding 1 where the cell currently contains water and 0 where it does not.

   Action 1 puts water into an empty cell and is the action being counted;
   action 2 moves existing water to another empty cell and is free; a cell with
   an empty neighbour on each side that both hold water fills up by itself. *)
Definition PlaceStep (cells w w' : list Z) : Prop :=
  exists i, 0 <= i < Zlength cells /\ Znth i cells 0 = 46 /\ Znth i w 0 = 0 /\
    w' = replace_Znth i 1 w.

Definition MoveStep (cells w w' : list Z) : Prop :=
  exists i j, 0 <= i < Zlength cells /\ 0 <= j < Zlength cells /\ i <> j /\
    Znth i w 0 = 1 /\ Znth j cells 0 = 46 /\ Znth j w 0 = 0 /\
    w' = replace_Znth j 1 (replace_Znth i 0 w).

Definition SpreadStep (cells w w' : list Z) : Prop :=
  exists i, 1 <= i < Zlength cells - 1 /\ Znth i cells 0 = 46 /\
    Znth i w 0 = 0 /\ Znth (i - 1) w 0 = 1 /\ Znth (i + 1) w 0 = 1 /\
    w' = replace_Znth i 1 w.

Definition AllCovered (cells w : list Z) : Prop :=
  forall i, 0 <= i < Zlength cells -> Znth i cells 0 = 46 -> Znth i w 0 = 1.

(* [k] action-1 steps suffice: some run starting from the dry row reaches a
   configuration covering every empty cell, and [k] of its steps are placements. *)
Definition CoverableWith (cells : list Z) (k : Z) : Prop :=
  exists (ws : list (list Z)) (costs : list Z),
    Zlength ws = Zlength costs + 1 /\
    Znth 0 ws nil = map (fun _ => 0) cells /\
    (forall q, 0 <= q < Zlength costs ->
       (Znth q costs 0 = 1 /\
        PlaceStep cells (Znth q ws nil) (Znth (q + 1) ws nil)) \/
       (Znth q costs 0 = 0 /\
        (MoveStep cells (Znth q ws nil) (Znth (q + 1) ws nil) \/
         SpreadStep cells (Znth q ws nil) (Znth (q + 1) ws nil)))) /\
    AllCovered cells (Znth (Zlength costs) ws nil) /\
    k = fold_right Z.add 0 costs.

Definition Pre (cells : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P005 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength cells <= 100 /\ Forall (fun c => c = 46 \/ c = 35) cells. *)
  True.

Definition Spec (cells : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (CoverableWith cells) (fun x => x) out.
