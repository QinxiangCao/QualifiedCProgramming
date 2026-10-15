Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Import ListNotations.
Local Open Scope Z_scope.

Definition rock : list Z := [114; 111; 99; 107].
Definition paper : list Z := [112; 97; 112; 101; 114].
Definition scissors : list Z := [115; 99; 105; 115; 115; 111; 114; 115].

Definition Gesture (g : list Z) : Prop :=
  g = rock \/ g = paper \/ g = scissors.

Definition Beats (x y : list Z) : Prop :=
  (x = rock /\ y = scissors) \/
  (x = scissors /\ y = paper) \/
  (x = paper /\ y = rock).

Definition Pre (f m s : list Z) : Prop :=
  Gesture f /\ Gesture m /\ Gesture s.

Definition Spec (f m s out : list Z) : Prop :=
  (out = [70] /\ Beats f m /\ Beats f s) \/
  (out = [77] /\ Beats m f /\ Beats m s) \/
  (out = [83] /\ Beats s f /\ Beats s m) \/
  (out = [63] /\
    ~ (Beats f m /\ Beats f s) /\
    ~ (Beats m f /\ Beats m s) /\
    ~ (Beats s f /\ Beats s m)).
