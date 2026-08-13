Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Nat.
Require Import Permutation.
Require Import String.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Local Open Scope Z_scope.
Import ListNotations.
Local Open Scope list.
Local Open Scope sets.
Local Open Scope string.

Import naive_C_Rules.
From SimpleC.EE.Applications_human.fme Require Import algorithm.
Local Open Scope sac.

Notation "'Zto_nat'" := (Z.to_nat).

Definition Constraint_list (c: Constraint): list Z :=
  c.(const) :: c.(coef).

Definition list_Constraint (l: list Z): Constraint :=
  match l with
    | nil    => {| const := 0; coef := nil; |}
    | l0::l' => {| const := l0; coef := l'; |}
  end.

Definition coef_Znth (i: Z) (c: Constraint) (default: Z): Z :=
  Znth i (Constraint_list c) default.

Definition coef_Zlength (c: Constraint): Z :=
  Z.of_nat (Datatypes.length (Constraint_list c)).

Definition coef_array (x: addr) (n: Z) (c: Constraint): Assertion :=
  “ x = NULL ” && emp || 
  “ x <> NULL ” && IntArray.full x n (Constraint_list c).

Definition coef_array_missing_i_rec (x: addr) (i lo hi: Z) (c: Constraint): Assertion :=
  IntArray.missing_i x i lo hi (Constraint_list c).

Definition coef_replace_Znth (i v: Z) (c: Constraint): Constraint :=
  list_Constraint (replace_Znth i v (Constraint_list c)).

Definition coef_pre_eq (i: Z) (c1 c2: Constraint): Prop :=
  forall i0, (0 <= i0 /\ i0 < i) -> coef_Znth i0 c1 0 = coef_Znth i0 c2 0.

Definition generate_new_constraint_partial (n: Z) (m m1 m2: Z) (c1 c2 c: Constraint): Prop :=
  m1 > 0 /\ m2 > 0 /\ m1 * coef_Znth n c1 0 + m2 * coef_Znth n c2 0 = 0 /\
  (forall i, (0 <= i /\ i < m) -> coef_Znth i c 0 = m1 * coef_Znth i c1 0 + m2 * coef_Znth i c2 0).
  
Fixpoint InequList (x: addr) (coef_len: Z) (lp: LP): Assertion :=
  match lp with
    | nil    => “ x = NULL ” && emp
    | a::lp' => “ x <> NULL ” &&
                EX c y: addr, 
                  “ c <> NULL ” &&
                  &(x # "InequList" ->ₛ "coef") # Ptr |-> c **
                  coef_array c coef_len a ** 
                  &(x # "InequList" ->ₛ "next") # Ptr |-> y **
                  InequList y coef_len lp'
  end.

Fixpoint InequList_seg (x y: addr) (coef_len: Z) (lp: LP): Assertion :=
  match lp with
    | nil    => “ x = y ” && emp
    | a::lp' => “ x <> NULL ” &&
                EX c z: addr,
                  “ c <> NULL ” &&
                  &(x # "InequList" ->ₛ "coef") # Ptr |-> c **
                  coef_array c coef_len a **
                  &(x # "InequList" ->ₛ "next") # Ptr |-> z **
                  InequList_seg z y coef_len lp'
  end.

Definition InequList_nth_pos (n: Z) (lp: LP): Prop :=
  forall c, In c lp -> coef_Znth n c 0 > 0 /\ coef_Znth n c 0 <= INT_MAX.

Definition InequList_nth_neg (n: Z) (lp: LP): Prop :=
  forall c, In c lp -> coef_Znth n c 0 < 0 /\ -coef_Znth n c 0 <= INT_MAX.

Definition InequList_nth_zero (n : Z) (lp : LP) : Prop :=
  forall c, In c lp -> coef_Znth n c 0 = 0.

Definition generate_new_constraints_partial (n: Z) (lp11: LP) (x: Constraint) (lp21 lp22 lp: LP): Prop :=
  exists res1 res2, (forall c, In c lp <-> (In c res1 \/ In c res2)) /\
                     generate_new_constraints n lp11 (List.app lp21 lp22) res1 /\
                    (forall c2, In c2 res2 -> (exists c1, In c1 lp21 /\ generate_new_constraint n x c1 c2)).

Definition construct_new_constraint (m1 m2: Z) (c1 c2: Constraint): Constraint :=
  {|
    const := m1 * c1.(const) + m2 * c2.(const);
    coef := list_add (mul_list m1 c1.(coef)) (mul_list m2 c2.(coef));
  |}.

Fixpoint construct_new_constraints1 (p1: Constraint) (lp2: LP): LP :=
  match lp2 with
    | nil    => nil
    | p2::l2 => (construct_new_constraint 1 1 p1 p2)::(construct_new_constraints1 p1 l2)
  end.

Fixpoint construct_new_constraints (lp1 lp2: LP): LP :=
  match lp1 with
    | nil    => nil
    | p1::l1 => List.app (construct_new_constraints1 p1 lp2) (construct_new_constraints l1 lp2)
  end.

Definition BoundPair (x: addr) (coef_len: Z) (bp: BP): Assertion :=
  EX u l r,
    &(x # "InequList" ->ₛ "upper") # Ptr |-> u **
    &(x # "InequList" ->ₛ "lower") # Ptr |-> l **
    &(x # "InequList" ->ₛ "remain") # Ptr |-> r **
    InequList u coef_len bp.(upper) **
    InequList l coef_len bp.(lower) **
    InequList r coef_len bp.(remain).

Definition form_BP (up lo re: LP) (bp: BP): Prop :=
  up = bp.(upper) /\ lo = bp.(lower) /\ re = bp.(remain).

Definition in_int_range (n m: Z) (c: Constraint): Prop :=
  forall i, (0 <= i /\ i < n) -> (-INT_MAX <= m * coef_Znth i c 0 /\ m * coef_Znth i c 0 <= INT_MAX).

Definition abs_in_int_range (n: Z) (c: Constraint): Prop :=
  forall i, (0 <= i /\ i < n) -> (coef_Znth i c 0 >= -INT_MAX /\ coef_Znth i c 0 <= INT_MAX).

Definition LP_abs_in_int_range (n: Z) (lp: LP): Prop :=
  forall c, In c lp -> abs_in_int_range n c.

Definition NonPos (l : list Constraint) : Prop :=
  forall c, In c l -> coef_Znth 0 c 0 <= 0.

Definition InequList_Zeros (l : list Constraint) (lo hi : Z) : Prop :=
  forall c, In c l -> forall i, (lo <= i /\ i < hi) -> coef_Znth i c 0 = 0.

Lemma InequList_Zeros_nil : forall lo hi, InequList_Zeros nil lo hi.
Proof. 
  unfold InequList_Zeros.
  intros.
  inversion H.
Qed.

Lemma InequList_Zeros_cons : forall c l lo hi,
    InequList_Zeros l lo hi ->
    (forall i, (lo <= i /\ i < hi) -> coef_Znth i c 0 = 0) ->
    InequList_Zeros (c::l) lo hi.
Proof.
  unfold InequList_Zeros.
  intros.
  inversion H1.
  - subst. apply H0. assumption.
  - apply H ; assumption.
Qed.

Lemma InequList_Zeros_app : forall l1 l2 lo hi,
    InequList_Zeros l1 lo hi ->
    InequList_Zeros l2 lo hi ->
    InequList_Zeros (l1 ++ l2) lo hi.
Proof.
  unfold InequList_Zeros.
  intros.
  apply in_app_or in H1.
  destruct H1.
  - apply H ; assumption.
  - apply H0 ; assumption.
Qed.

Lemma InequList_Zeros_app_split : forall l1 l2 lo hi,
    InequList_Zeros (l1 ++ l2) lo hi ->
    InequList_Zeros l1 lo hi /\ InequList_Zeros l2 lo hi.
Proof.
  unfold InequList_Zeros.
  intros.
  split.
  - intros.
    apply H ; try lia.
    apply in_or_app.
    left. assumption.
  - intros.
    apply H ; try lia.
    apply in_or_app.
    right. assumption.
Qed.

Lemma InequList_Zeros_range_empty : forall l lo,
  InequList_Zeros l lo lo.
Proof.
  unfold InequList_Zeros.
  intros.
  lia.
Qed.

Lemma InequList_Zeros_range_extend_left : forall l lo hi,
  InequList_Zeros l (lo + 1) hi ->
  InequList_nth_zero lo l ->
  InequList_Zeros l lo hi.
Proof.
  unfold InequList_Zeros, InequList_nth_zero.
  intros.
  destruct (Z_lt_dec i (lo + 1)).
  - assert (i = lo) by lia. subst. apply H0. assumption.
  - apply H ; try lia. auto.
Qed.

Lemma InequList_Zeros_range_extend_right : forall l lo hi,
  InequList_Zeros l lo hi ->
  InequList_nth_zero hi l ->
  InequList_Zeros l lo (hi + 1).
Proof.
  unfold InequList_Zeros, InequList_nth_zero.
  intros.
  destruct (Z_lt_dec i hi).
  - apply H ; try lia. auto.
  - assert (i = hi) by lia. subst. apply H0. assumption.
Qed.



