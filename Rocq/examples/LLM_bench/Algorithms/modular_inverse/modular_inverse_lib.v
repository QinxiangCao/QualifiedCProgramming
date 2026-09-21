From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

(** The inverse equation is mathematical; canonical output bounds are kept
    explicitly in the contract as part of the requested representation. *)
Definition ModularInverse (a modulus inverse : Z) : Prop :=
  exists coefficient, a * inverse + modulus * coefficient = 1.
