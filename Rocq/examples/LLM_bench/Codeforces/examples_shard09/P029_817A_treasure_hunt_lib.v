Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Local Open Scope Z_scope.


Definition Pre (x1 y1 x2 y2 x y : Z) : Prop :=
  (* -100000 <= x1 <= 100000 /\
     -100000 <= y1 <= 100000 /\
     -100000 <= x2 <= 100000 /\
     -100000 <= y2 <= 100000 /\
     1 <= x <= 100000 /\
     1 <= y <= 100000. *)
  True.

Definition AbsDiff (a b : Z) : Z :=
  if a <? b then b - a else a - b.

Definition Reachable (x1 y1 x2 y2 x y : Z) : Prop :=
  Z.rem (AbsDiff x1 x2) x = 0 /\
  Z.rem (AbsDiff y1 y2) y = 0 /\
  Z.rem (Z.quot (AbsDiff x1 x2) x) 2 =
  Z.rem (Z.quot (AbsDiff y1 y2) y) 2.

Definition Spec (x1 y1 x2 y2 x y out : Z) : Prop :=
  ((Reachable x1 y1 x2 y2 x y /\ out = 1) \/
   (~ Reachable x1 y1 x2 y2 x y /\ out = 0)).
