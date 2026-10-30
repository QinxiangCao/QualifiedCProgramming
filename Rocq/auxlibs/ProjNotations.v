(** * Typeclass-based Projection Overloading
    
    This file provides a mechanism to define projections with the same name
    for different record types using typeclasses.
*)

Ltac red_twice T :=
  let T1 := eval red in T in
  let T2 := eval red in T1 in
  exact T2.

Class HasNrm A {B} := get_nrm : A -> B.
Arguments get_nrm {A B _} !a /.
(** The [Notation] below allows us to write [x.(nrm)] to access the "nrm" field
    of any record type that has a [HasNrm] instance.
    The [red_twice] tactic unfolds the definition to get exactly the projection
    defined in the instance. *)
Notation "x '.(nrm)'" := ltac:(red_twice (get_nrm x)) (at level 1, only parsing).

Class HasErr A {B} := get_err : A -> B.
Arguments get_err {A B _} !a /.
Notation "x '.(err)'" := ltac:(red_twice (get_err x)) (at level 1, only parsing).

Class HasRet A {B} := get_ret : A -> B.
Arguments get_ret {A B _} !a /.
Notation "x '.(ret)'" := ltac:(red_twice (get_ret x)) (at level 1, only parsing).

Class HasBrk A {B} := get_brk : A -> B.
Arguments get_brk {A B _} !a /.
Notation "x '.(brk)'" := ltac:(red_twice (get_brk x)) (at level 1, only parsing).

Class HasCnt A {B} := get_cnt : A -> B.
Arguments get_cnt {A B _} !a /.
Notation "x '.(cnt)'" := ltac:(red_twice (get_cnt x)) (at level 1, only parsing).


Module Example.
  (** You need to wrap each record definition in a module to avoid projection
      name conflicts. *)
  Module StateA.
    Record StateA := { nrm : nat; err : nat }.
    #[export] Instance StateA_nrm : HasNrm StateA := nrm.
    (** The only-printing [Notation] below ensures the projection is printed
        clearly as [x.(nrm)] without the module name. *)
    Notation "x '.(nrm)'" := (@nrm x) (at level 1, only printing).
    #[export] Instance StateA_err : HasErr StateA := err.
    Notation "x '.(err)'" := (@err x) (at level 1, only printing).
  End StateA.

  Module StateB.
    Record StateB := { nrm : nat; err : bool }.
    #[export] Instance StateB_nrm : HasNrm StateB := nrm.
    Notation "x '.(nrm)'" := (@nrm x) (at level 1, only printing).
    #[export] Instance StateB_err : HasErr StateB := err.
    Notation "x '.(err)'" := (@err x) (at level 1, only printing).
  End StateB.

  Import StateA StateB.
  Axiom a : StateA.
  Axiom b : StateB.
  (* Check a.(nrm).
  Check b.(nrm).
  Check a.(err).
  Check b.(err). *)
End Example.
