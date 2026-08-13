Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersFacts.

Module Type OrderedTypeFullFacts_Sig (Import O:OrderedTypeFull').

Include OrderedTypeFullFacts O.

End OrderedTypeFullFacts_Sig.

Module OrderedTypeFullDecFacts
         (Import O:OrderedTypeFull')
         (Import O': OrderedTypeFullFacts_Sig O).

Section decidability.

Variable x y: t.

Theorem dec: {x < y} + {x > y} + {x == y}.
Proof.
  intros.
  pose proof compare_spec x y.
  destruct (compare x y) eqn:HEQ.
  + right.
    inversion H.
    tauto.
  + left; left.
    inversion H.
    tauto.
  + left; right.
    inversion H.
    tauto.
Defined.

Definition lt_dec: {x < y} + {~ x < y}.
Proof.
  destruct dec as [[? | ?] | ?].
  + left; tauto.
  + right; order.
  + right; order.
Defined.

Definition le_dec: {x <= y} + {~ x <= y}.
Proof.
  destruct dec as [[? | ?] | ?].
  + left; order.
  + right; order.
  + left; order.
Defined.

Definition gt_dec: {x > y} + {~ x > y}.
Proof.
  destruct dec as [[? | ?] | ?].
  + right; order.
  + left; order.
  + right; order.
Defined.

Definition ge_dec: {x >= y} + {~ x >= y}.
Proof.
  destruct dec as [[? | ?] | ?].
  + right; order.
  + left; order.
  + left; order.
Defined.

Definition lt_ge_dec: {x < y} + {x >= y}.
Proof.
  destruct dec as [[? | ?] | ?].
  + left; order.
  + right; order.
  + right; order.
Defined.

Lemma lt_le_dec: {x < y} + {y <= x}.
Proof.
  destruct dec as [[? | ?] | ?].
  + left; order.
  + right; order.
  + right; order.
Defined.

Definition le_gt_dec: {x <= y} + {x > y}.
Proof.
  destruct dec as [[? | ?] | ?].
  + left; order.
  + right; order.
  + left; order.
Defined.

Definition gt_le_dec: {x > y} + {x <= y}.
Proof.
  destruct dec as [[? | ?] | ?].
  + right; order.
  + left; order.
  + right; order.
Defined.

Definition ge_lt_dec: {x >= y} + {x < y}.
Proof.
  destruct dec as [[? | ?] | ?].
  + right; order.
  + left; order.
  + left; order.
Defined.

End decidability.
End OrderedTypeFullDecFacts.
