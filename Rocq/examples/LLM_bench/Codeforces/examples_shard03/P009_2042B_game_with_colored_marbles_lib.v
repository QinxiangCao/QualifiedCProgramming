Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(c : list Z) -> Z, Alice's score at the end.
   [c] lists the colour of every marble.  The players alternately take one of
   the remaining marbles, Alice first, so a play is the order in which the
   marbles are removed and Alice owns the ones taken at the even-numbered
   turns.  She scores one point per colour she holds at all and one more per
   colour she holds completely.

   Alice maximises her score and Bob minimises it, so the value is the largest
   score she can force: she fixes a strategy that always names a marble still
   in the game, and every finished play in which she follows it — Bob's turns
   being unrestricted, hence worst-case — pays her at least that score. *)
Definition PartialPlay (n : Z) (order : list Z) : Prop :=
  Zlength order <= n /\ NoDup order /\ Forall (fun i => 0 <= i < n) order.

Definition FollowsAlice (A : list Z -> Z) (order : list Z) : Prop :=
  forall k, 0 <= k < Zlength order -> Z.even k = true ->
    Znth k order 0 = A (sublist 0 k order).

Definition AliceTook (order : list Z) (i : Z) : Prop :=
  exists k, 0 <= k < Zlength order /\ Z.even k = true /\ Znth k order 0 = i.

Definition AliceHasColour (c order : list Z) (x : Z) : Prop :=
  exists i, 0 <= i < Zlength c /\ Znth i c 0 = x /\ AliceTook order i.

Definition AliceHasWholeColour (c order : list Z) (x : Z) : Prop :=
  (exists i, 0 <= i < Zlength c /\ Znth i c 0 = x) /\
  (forall i, 0 <= i < Zlength c -> Znth i c 0 = x -> AliceTook order i).

Definition AliceScore (c order : list Z) : Z :=
  #(fun x : Z => 1 <= x < Zlength c + 1 /\ AliceHasColour c order x) +
  #(fun x : Z => 1 <= x < Zlength c + 1 /\ AliceHasWholeColour c order x).

Definition AliceForces (c : list Z) (v : Z) : Prop :=
  exists A : list Z -> Z,
    (forall order,
       PartialPlay (Zlength c) order -> FollowsAlice A order ->
       Zlength order < Zlength c -> Z.even (Zlength order) = true ->
       0 <= A order < Zlength c /\ ~ In (A order) order) /\
    (forall order,
       PartialPlay (Zlength c) order -> FollowsAlice A order ->
       Zlength order = Zlength c -> v <= AliceScore c order).

Definition Pre (c : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P009 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength c <= 1000 /\ Forall (fun x => 1 <= x <= Zlength c) c. *)
  True.

Definition Spec (c : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le (AliceForces c) (fun x => x) out.
