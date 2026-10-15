Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(s : list Z) -> Z, the score Alice ends the game with.
   [s] is the binary string as character codes, 48 = '0' and 49 = '1'.

   A move deletes one block of consecutive equal characters; the players move
   alternately starting with Alice, the game ends with the empty string, and a
   player's score counts the '1' characters that player deleted.  The value is
   stated as the largest score Alice can force: she fixes a strategy, and every
   complete play in which she follows it — that is, against every behaviour of
   Bob, who is trying to keep his own score, and hence Alice's, as low as
   possible — pays her at least that much. *)
Definition RemoveBlock (t : list Z) (start len : Z) (t' : list Z) : Prop :=
  0 <= start /\ 1 <= len /\ start + len <= Zlength t /\
  (forall i, start <= i < start + len -> Znth i t 0 = Znth start t 0) /\
  t' = sublist 0 start t ++ sublist (start + len) (Zlength t) t.

(* The states of a play, together with the move played from each one.  A play
   is complete when its last state is the empty string. *)
Definition PartialPlay (s : list Z) (states : list (list Z))
                       (moves : list (Z * Z)) : Prop :=
  Zlength states = Zlength moves + 1 /\
  Znth 0 states nil = s /\
  forall k, 0 <= k < Zlength moves ->
    RemoveBlock (Znth k states nil)
                (fst (Znth k moves (0, 0))) (snd (Znth k moves (0, 0)))
                (Znth (k + 1) states nil).

(* Alice moves at the even-numbered turns, choosing from the states seen so
   far; Bob's turns are left unconstrained. *)
Definition FollowsAlice (A : list (list Z) -> Z * Z) (states : list (list Z))
                        (moves : list (Z * Z)) : Prop :=
  forall k, 0 <= k < Zlength moves -> Z.even k = true ->
    Znth k moves (0, 0) = A (sublist 0 (k + 1) states).

Definition DeletedOnes (t : list Z) (start len : Z) : Z :=
  if Znth start t 0 =? 49 then len else 0.

Definition AliceScore (states : list (list Z)) (moves : list (Z * Z)) : Z :=
  sum_range 0 (Zlength moves - 1)
    (fun k => if Z.even k
              then DeletedOnes (Znth k states nil)
                     (fst (Znth k moves (0, 0))) (snd (Znth k moves (0, 0)))
              else 0).

(* [x] is a score Alice can force: some strategy of hers is playable at every
   position it reaches and never lets a finished play pay her less than [x]. *)
Definition AliceForces (s : list Z) (x : Z) : Prop :=
  exists A : list (list Z) -> Z * Z,
    (forall states moves,
       PartialPlay s states moves -> FollowsAlice A states moves ->
       Z.even (Zlength moves) = true ->
       Znth (Zlength moves) states nil <> nil ->
       exists t', RemoveBlock (Znth (Zlength moves) states nil)
                    (fst (A states)) (snd (A states)) t') /\
    (forall states moves,
       PartialPlay s states moves -> FollowsAlice A states moves ->
       Znth (Zlength moves) states nil = nil ->
       x <= AliceScore states moves).

Definition Pre (s : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P002 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength s <= 100 /\ Forall (fun c => c = 48 \/ c = 49) s. *)
  True.

Definition Spec (s : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le (AliceForces s) (fun x => x) out.
