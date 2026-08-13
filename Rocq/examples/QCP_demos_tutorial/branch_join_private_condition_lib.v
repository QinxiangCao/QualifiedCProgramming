Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Definition step (x: Z) : Z :=
  if Z.even x then x / 2 else 3 * x + 1.
