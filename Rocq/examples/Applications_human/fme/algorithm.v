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
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sets.

(* 
  represents a linear constraint of the form:
  const + coef[0] * x[0] + coef[1] * x[1] + ... + coef[n] * x[n] <= 0
*)
Record Constraint: Type := {
  const: Z;
  coef: list Z;
}.

Definition LP: Type := list Constraint.

Definition LP_sol: Type := list Z.

Fixpoint sum_prod (s: Z) (a b: list Z): Z :=
  match a, b with
  | nil, _ => s
  | _, nil => s
  | cons a0 a', cons b0 b' => sum_prod (s + a0 * b0) a' b'
  end.

Definition assignment (s: LP_sol) (c: Constraint): Z :=
  sum_prod c.(const) s c.(coef).

Definition satisfy_constraint (s: LP_sol) (c: Constraint): Prop :=
  assignment s c <= 0.

Definition satisfy_LP (s: LP_sol) (p: LP): Prop :=
  forall c, In c p -> satisfy_constraint s c.

Definition UNSAT (p : LP) : Prop :=
  forall s, ~ satisfy_LP s p.

Definition nth_coef (n: Z) (c: Constraint) :=
  nth (Z.to_nat (n - 1)) c.(coef) 0.

Definition LP_implies (p1 p2: LP): Prop :=
  forall s: LP_sol, satisfy_LP s p1 -> satisfy_LP s p2.

Record BP: Type := {
  upper: LP;
  lower: LP;
  remain: LP;
}.

Record eliminate_xn (num: Z) (lp: LP) (bp: BP): Prop := {
  elim_upper:
    forall c, In c bp.(upper) <-> In c lp /\ nth_coef num c > 0;
  elim_lower:
    forall c, In c bp.(lower) <-> In c lp /\ nth_coef num c < 0;
  elim_remain:
    forall c, In c bp.(remain) <-> In c lp /\ nth_coef num c = 0;
}.

Fixpoint list_add (l1 l2 : list Z): list Z :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1 
  | a::l1', b::l2' => (a+b)::(list_add l1' l2')
  end.

Definition mul_list (k: Z) (l: list Z): list Z :=
  map (fun i => k * i) l.

Definition generate_new_constraint (n: Z) (c1 c2 c: Constraint): Prop :=
  exists m1 m2,
    m1 > 0 /\ m2 > 0 /\ nth_coef n c = 0 /\
    c = {|
      const := m1 * c1.(const) + m2 * c2.(const);
      coef := list_add (mul_list m1 c1.(coef)) (mul_list m2 c2.(coef));
    |}.

Definition generate_new_constraints (n: Z) (lp1 lp2 lp: LP): Prop :=
  forall c,
    In c lp ->
    (exists c1 c2,
       In c1 lp1 /\ In c2 lp2 /\
       generate_new_constraint n c1 c2 c).

Inductive FME_step (cnt: Z) (lp: LP): LP -> Prop :=
| FME_step_constr:
    forall BP lp',
      eliminate_xn cnt lp BP ->
      generate_new_constraints cnt BP.(upper) BP.(lower) lp' ->
      FME_step cnt lp (List.app lp' BP.(remain)).

Lemma self_LP_implies: forall lp, LP_implies lp lp.
Proof.
  intros.
  unfold LP_implies.
  intros.
  apply H.
Qed.

Lemma LP_implies_trans:
  forall lp1 lp2 lp3,
    LP_implies lp1 lp2 ->
    LP_implies lp2 lp3 ->
    LP_implies lp1 lp3.
Proof.
  intros.
  unfold LP_implies in *.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Lemma LP_implies_nil: forall lp, LP_implies lp nil.
Proof.
  intros.
  unfold LP_implies.
  intros.
  unfold satisfy_LP.
  intros.
  unfold In in H0.
  tauto.
Qed.

Lemma list_add_nil_r: forall l, list_add l nil = l.
Proof.
  intros.
  destruct l.
  - reflexivity.
  - simpl. reflexivity.
Qed.  

Lemma sum_prod_nil_r: forall s l, sum_prod s l nil = s.
Proof.
  intros.
  destruct l.
  - reflexivity.
  - simpl. reflexivity.
Qed. 

Lemma const_add_sum_prod: 
  forall c1 c2 l1 l2, sum_prod (c1+c2) l1 l2 = c1 + sum_prod c2 l1 l2.
Proof.
  intros.
  revert c1 c2 l2.
  induction l1; intros.
  - reflexivity.
  - destruct l2.
    + simpl. reflexivity.
    + simpl. rewrite IHl1. rewrite IHl1. lia.
Qed.

Lemma sum_prod_linear_add:
  forall c c1 c2 l l1 l2 s,
    c = c1 + c2 ->
    l = list_add l1 l2 ->
    sum_prod c s l  = sum_prod c1 s l1 + sum_prod c2 s l2.
Proof.
  intros.
  revert c c1 c2 l l2 s H H0.
  induction l1; intros; simpl.
  - rewrite H.
    rewrite H0.
    rewrite sum_prod_nil_r.
    simpl. apply const_add_sum_prod.
  - destruct s.
    + simpl. apply H.
    + destruct l.
    -- destruct l2; simpl; discriminate H0.
    -- destruct l2.
    ++ simpl.
       specialize (IHl1 (c + z * z0) (c1 + z * a) c2 l nil s).
       rewrite list_add_nil_r in H0.
       rewrite sum_prod_nil_r in IHl1.
       injection H0 as ? ?.
       apply IHl1.
       lia.
       rewrite list_add_nil_r.
       tauto.
    ++ simpl.
       simpl in H0.
       injection H0 as ? ?.
       apply IHl1.
       nia.
       tauto.
Qed.

Lemma sum_prod_linear_mul:
  forall c c1 l l1 s k,
    c = k * c1 ->
    l = mul_list k l1 ->
    sum_prod c s l = k * sum_prod c1 s l1.
Proof.
  intros.
  revert c c1 l H H0 s.
  induction l1; intros; simpl.
  - simpl in H0.
    rewrite H0.
    rewrite sum_prod_nil_r.
    rewrite sum_prod_nil_r.
    tauto.
  - destruct l; simpl in H0; try discriminate H0.
    injection H0 as ? ?.
    destruct s.
    + simpl. apply H.
    + simpl. apply IHl1.
      nia.
      tauto. 
Qed.

Lemma sum_prod_linear:
  forall c c1 c2 l l1 l2 s k1 k2,
    c = k1 * c1 + k2 * c2 ->
    l = list_add (mul_list k1 l1) (mul_list k2 l2) ->
    sum_prod c s l = k1 * sum_prod c1 s l1 + k2 * sum_prod c2 s l2.
Proof.
  intros.
  assert (Hk1: sum_prod (k1 * c1) s (mul_list k1 l1) = k1 * sum_prod c1 s l1).
  {
    apply sum_prod_linear_mul; reflexivity.
  }
  rewrite <- Hk1.
  assert (Hk2: sum_prod (k2 * c2) s (mul_list k2 l2) = k2 * sum_prod c2 s l2).
  {
    apply sum_prod_linear_mul; reflexivity.
  }
  rewrite <- Hk2.
  apply sum_prod_linear_add; tauto.
Qed.

Lemma generate_new_constraint_sum:
  forall n c1 c2 c s,
    generate_new_constraint n c1 c2 c ->
    (exists m1 m2,
      m1 > 0 /\ m2 > 0 /\ 
      m1 * assignment s c1 + m2 * assignment s c2 = assignment s c).
Proof.
  intros.
  unfold generate_new_constraint in H.
  destruct H as [m1 [m2 [Hm1 [Hm2 [? Hc]]]]].
  exists m1.
  exists m2.
  split; try tauto.
  split; try tauto.
  unfold assignment.
  destruct c.
  injection Hc as ? ?.
  simpl.
  symmetry.
  apply sum_prod_linear; tauto.
Qed.

Lemma generate_new_constraint_sound:
  forall n c1 c2 c s, 
  generate_new_constraint n c1 c2 c ->
  satisfy_constraint s c1 -> 
  satisfy_constraint s c2 ->
  satisfy_constraint s c.
Proof.
  intros.
  pose proof generate_new_constraint_sum _ _ _ _ s H.
  destruct H2 as [x[y[H2[H3 H4]]]].
  unfold satisfy_constraint in *.
  rewrite <- H4.
  nia.
Qed.

Lemma generate_new_constraints_sound:
  forall n lp1 lp2 lp s,
    generate_new_constraints n lp1 lp2 lp ->
    satisfy_LP s lp1 ->
    satisfy_LP s lp2 ->
    satisfy_LP s lp.
Proof.
  intros.
  unfold generate_new_constraints in H.
  unfold satisfy_LP.
  intros.
  specialize (H c).
  unfold satisfy_LP in *.
  apply H in H2.
  destruct H2 as [c1 [c2 [Hc1[Hc2 H2]]]].
  apply generate_new_constraint_sound with (s:=s) in H2.
  - tauto.
  - apply H0. tauto.
  - apply H1. tauto.
Qed.   

Lemma eliminate_xn_iff:
  forall n lp bp c,
    eliminate_xn n lp bp ->
    In c lp <->
    In c bp.(upper) \/ In c bp.(lower) \/ In c bp.(remain).
Proof.
  intros.
  split; intros.
  - induction H.
    destruct (nth_coef n c >? 0) eqn:Hgt. 
    + left.
      apply Z.gtb_lt in Hgt.
      apply elim_upper0.
      split; [tauto | lia].
    + destruct (nth_coef n c <? 0) eqn:Hlt.
      * right. left.
        apply Z.ltb_lt in Hlt.
        apply elim_lower0.
        split; [tauto | lia].
      * right. right.
        apply elim_remain0.
        split; [tauto | lia].
  - induction H.
    destruct H0 as [H0 | [H0 | H0]].
    + apply elim_upper0 in H0.
      tauto.
    + apply elim_lower0 in H0.
      tauto.
    + apply elim_remain0 in H0.
      tauto.
Qed.

Theorem FME_step_sound:
  forall n lp lp', FME_step n lp lp' -> LP_implies lp lp'.
Proof.
  intros.
  induction H.
  unfold LP_implies.
  unfold satisfy_LP in *.
  intros.
  apply in_app_iff in H2.
  destruct H2.
  - apply generate_new_constraints_sound with (s:=s) in H0.
    + apply H0; tauto.
    + unfold satisfy_LP; intros.
      apply eliminate_xn_iff with (c:=c0) in H.
      apply H1.
      tauto.
    + unfold satisfy_LP; intros.
      apply eliminate_xn_iff with (c:=c0) in H.
      apply H1.
      tauto.
  - apply eliminate_xn_iff with (c:=c) in H.
    apply H1.
    tauto.
Qed.
