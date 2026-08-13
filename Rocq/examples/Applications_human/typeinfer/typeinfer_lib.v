Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.

Import naive_C_Rules.
Local Open Scope sac.
From SimpleC.EE.Applications_human.typeinfer Require Export type_infer_lib.

Fixpoint store_type(p: addr) (t: TypeTree) : Assertion :=
  match t with
    | TVar n =>
      “ 0 <= n ” && “ n < 100 ” &&
      (&((p) # "atype" ->ₛ "t") # Int |-> 3) **
      (&((p) # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> n)
    | TAtom n =>
      (&((p) # "atype" ->ₛ "t") # Int |-> 0) **
      (&((p) # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name") # Int |-> n)
    | TArrow from to =>
      EX p1 p2,
      (&(p # "atype" ->ₛ "t") # Int |-> 1) **
      (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> p1) **
      (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> p2) **
      store_type p1 from ** store_type p2 to
    | TApply tfn rand =>
      EX p1 p2,
      (&(p # "atype" ->ₛ "t") # Int |-> 2) **
      (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> p1) **
      (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> p2) **
      store_type p1 tfn ** store_type p2 rand
  end.

Definition store_type_aux(p: addr) (tp: TypeVarID) (t : TypeTree) : Assertion :=
  match t with
    | TVar n =>
      “ tp = 3 ” &&
      “ 0 <= n ” && “ n < 100 ” &&
      (&((p) # "atype" ->ₛ "d" .ₛ "VAR" .ₛ "name") # Int |-> n)
    | TAtom n =>
      “ tp = 0 ” &&
      (&((p) # "atype" ->ₛ "d" .ₛ "ATOM" .ₛ "name") # Int |-> n)
    | TArrow from to =>
      EX p1 p2,
      “ tp = 1 ” &&
      (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "from") # Ptr |-> p1) **
      (&(p # "atype" ->ₛ "d" .ₛ "ARROW" .ₛ "to") # Ptr |-> p2) **
      store_type p1 from ** store_type p2 to
    | TApply tfn rand =>
      EX p1 p2,
      “ tp = 2 ” &&
      (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "tfn") # Ptr |-> p1) **
      (&(p # "atype" ->ₛ "d" .ₛ "APP" .ₛ "rand") # Ptr |-> p2) **
      store_type p1 tfn ** store_type p2 rand
  end.

Definition store_option_type (x: addr) (t: option TypeTree) : Assertion :=
  match t with
  | None => “ x = NULL ” && emp
  | Some t => “ x <> NULL ” && store_type x t
end.

(* Pointer to pointer | Address of address *)
Definition store_type_addr (s : sol) (x: addr) (m: Z) (p: addr) : Assertion :=
  (x + m * sizeof(PTR)) # Ptr |-> p ** store_option_type p (s m).

Definition store_solution(x: addr) (s: sol): Assertion :=
EX l : (list addr),
  store_array (store_type_addr s) x 100 l.

Definition store_compressed_solution (x : addr) (s : sol) : Assertion :=
EX (s' : sol), 
  “ sol_compress_to s' s ” &&
  “ sol_finite s ” &&
  “ sol_no_loop s' ” &&
  store_solution x s'.

(* x[n] = y. Solution except for lo == n  *)
Definition store_solution_aux(x : addr) (s : sol) (n : Z) (y : addr) (t : option TypeTree): Assertion :=
EX l : (list addr),
  “ 0 <= n ” && “ n < 100 ” && “ y = Znth n l 100 ” && “ t = s n ” &&
  ((x + n * sizeof(PTR)) # Ptr |-> y) **
  (store_option_type y t) **
  (store_array_missing_i_rec (store_type_addr s) x n 0 100 l).

Definition solution_at(s : sol) (n : Z) (t : TypeTree) : Prop :=
  Some t = s n.

Definition not_occur (n: Z) (t: TypeTree): Prop :=
  ~occur n t.

Definition debug: Assertion :=
  emp.

Lemma solution_split: forall s x n,
  0 <= n < 100 ->
  store_solution x s
  |-- EX y, store_solution_aux x s n y (s n).
Proof.
  intros.
  unfold store_solution.
  Intros l.
  rewrite (store_array_split_to_missing_i _ (store_type_addr s) x n 100 l 100) .
  2: auto.

  unfold store_solution_aux.
  Exists (Znth n l 100) l.
  entailer!.
Qed.

Lemma store_some_type: forall x o,
  x <> 0 ->
  store_option_type x o
  |-- EX t, “ o = Some t ” && store_type x t.
Proof.
  intros.
  destruct o.
  - intros.
    unfold store_option_type.
    Exists t.
    entailer!.
  - intros.
    unfold store_option_type.
    entailer!.
Qed.

Lemma store_none_type: forall x,
  store_option_type x None
  |-- emp.
Proof.
  intros.
  unfold store_option_type.
  entailer!.
Qed.
