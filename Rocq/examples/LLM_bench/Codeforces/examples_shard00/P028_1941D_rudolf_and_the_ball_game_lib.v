Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ThrowAllows (direction : Z) (clockwise : bool) : Prop :=
  direction = 63 \/
  (direction = 48 /\ clockwise = true) \/
  (direction = 49 /\ clockwise = false).

Definition PossibleBallHolder
    (n start : Z) (throws : list (Z * Z)) (holder : Z) : Prop :=
  exists directions positions,
    Zlength directions = Zlength throws /\
    Zlength positions = Zlength throws + 1 /\
    Znth 0 positions 0 = start /\
    Znth (Zlength throws) positions 0 = holder /\
    (forall k, 0 <= k < Zlength throws ->
       ThrowAllows (snd (Znth k throws (0, 0))) (Znth k directions false) /\
       Znth (k + 1) positions 0 =
         1 + ((Znth k positions 0 - 1 +
           (if Znth k directions false
            then fst (Znth k throws (0, 0))
            else - fst (Znth k throws (0, 0)))) mod n)).

Definition Pre (n start : Z) (throws : list (Z * Z)) : Prop :=
  2 <= n <= 1000 /\ 1 <= Zlength throws <= 1000 /\ 1 <= start <= n /\
  Forall (fun p => 1 <= fst p < n /\
    (snd p = 48 \/ snd p = 49 \/ snd p = 63)) throws.

Definition Spec (n start : Z) (throws : list (Z * Z)) (out : list Z) : Prop :=
  NoDup out /\
  mono_inc out /\
  forall holder, In holder out <-> PossibleBallHolder n start throws holder.
