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

From SimpleC.EE.Applications_human.fme Require Export algorithm implement implement_lemma.

Lemma InequList_nth_zero_split : forall l1 l2 n,
    InequList_nth_zero n (l1 ++ l2) ->
    InequList_nth_zero n l1 /\ InequList_nth_zero n l2.
Proof.
  intros.
  unfold InequList_nth_zero in *.
  split; intros; apply H ; apply in_app_iff; tauto.
Qed.

Lemma eliminate_keep_Zeros : forall (l : LP) (b : BP) (n lo hi : Z),
    eliminate_xn n l b ->
    InequList_Zeros l lo hi ->
    0 <= n < lo -> lo <= hi ->
    forall up low re, form_BP up low re b ->
    InequList_Zeros up lo hi /\ InequList_Zeros low lo hi /\ InequList_Zeros re lo hi.
Proof.
  intros.
  destruct H3 as [ ? [ ? ?]].
  subst.
  repeat split ; unfold InequList_Zeros in * ; intros.
  - rewrite (elim_upper _ _ _ H _ ) in H3.
    apply H0 ; try tauto.
  - rewrite (elim_lower _ _ _ H _ ) in H3.
    apply H0 ; try tauto.
  - rewrite (elim_remain _ _ _ H _ ) in H3.
    apply H0 ; try tauto.
Qed.

Lemma eliminate_keep_range : forall (l : LP) (b : BP) (n hi : Z),
    eliminate_xn n l b ->
    LP_abs_in_int_range hi l ->
    forall up low re, form_BP up low re b ->
    LP_abs_in_int_range hi up /\ LP_abs_in_int_range hi low /\ LP_abs_in_int_range hi re.
Proof.
  intros.
  destruct H1 as [ ? [ ? ?]].
  subst.
  unfold LP_abs_in_int_range in *.
  split ; [ | split] ; intros.
  - rewrite (elim_upper _ _ _ H _ ) in H1.
    apply H0 ; try tauto.
  - rewrite (elim_lower _ _ _ H _ ) in H1.
    apply H0 ; try tauto.
  - rewrite (elim_remain _ _ _ H _ ) in H1.
    apply H0 ; try tauto.
Qed.

Lemma eliminate_add_Zeros : forall (l : LP) (b : BP) (n lo hi : Z),
    eliminate_xn n l b ->
    InequList_Zeros l lo hi ->
    LP_abs_in_int_range hi l ->
    1 <= n < lo -> lo <= hi -> 
    forall up low re, form_BP up low re b ->
    InequList_nth_pos n up /\ InequList_nth_neg n low /\ InequList_nth_zero n re.
Proof.
  intros.
  pose proof (eliminate_keep_range l b n hi H H1 up low re H4) as Rng.
  destruct H4 as [ ? [ ? ?]].
  subst.
  destruct Rng as [ ? [ ? ?]].
  split ; [unfold InequList_nth_pos | split ; [unfold InequList_nth_neg | unfold InequList_nth_zero]] ; intros.
  - specialize (H4 _ H7).
    rewrite (elim_upper _ _ _ H _ ) in H7. 
    rewrite <- coef_Znth_nth in H7 ; try lia.
    specialize (H4 n (ltac:(lia))).
    lia.
  - specialize (H5 _ H7).
    rewrite (elim_lower _ _ _ H _ ) in H7.
    rewrite <- coef_Znth_nth in H7 ; try lia.
    specialize (H5 n (ltac:(lia))).
    lia.
  - specialize (H6 _ H7).
    rewrite (elim_remain _ _ _ H _ ) in H7.
    rewrite <- coef_Znth_nth in H7 ; try lia.
Qed.

Lemma list_add_zero : forall l1 l2 n,
  Znth n l1 0 = 0 ->
  Znth n l2 0 = 0 ->
  Znth n (list_add l1 l2) 0 = 0.
Proof.
  induction l1 ; simpl in * ; intros ; try lia.
  destruct l2 ; simpl in * ; try lia.
  specialize (IHl1 l2 (n - 1)).
  destruct (Z_lt_dec n 1) ; try lia.
  - unfold Znth in *.
    replace (Zto_nat n) with 0%nat in * by lia.
    simpl in *. lia.
  - rewrite Znth_cons in * ; try lia.
Qed.

Lemma mul_list_zero : forall l m n,
  Znth n l 0 = 0 ->
  Znth n (mul_list m l) 0 = 0.
Proof.
  induction l ; simpl in * ; intros ; try lia.
  specialize (IHl m (n - 1)).
  destruct (Z_lt_dec n 1) ; try lia.
  - unfold Znth in *.
    replace (Zto_nat n) with 0%nat in * by lia.
    simpl in *. lia.
  - rewrite Znth_cons in * ; try lia.
Qed.

Lemma generate_new_contraints_keep_Zeros : forall (l1 l2 l3 : LP) (n lo hi : Z),
    generate_new_constraints n l1 l2 l3 ->
    InequList_Zeros l1 lo hi ->
    InequList_Zeros l2 lo hi ->
    0 <= n < lo -> lo <= hi ->
    InequList_Zeros l3 lo hi.
Proof.
  intros.
  unfold generate_new_constraints in H.
  unfold InequList_Zeros in *.
  intros.
  apply H in H4.
  destruct H4 as [ c1  [c2 [? [?  ?]]]].
  unfold generate_new_constraint in H7. 
  destruct H7 as [ m1 [m2 [ ? [? [? ?]]]]].
  subst c. simpl.
  specialize (H0 _ H4 i H5).
  specialize (H1 _ H6 i H5).
  unfold coef_Znth, Constraint_list in *. simpl in *.
  rewrite Znth_cons in * ; try lia.
  apply list_add_zero ; apply mul_list_zero ; try lia.
Qed.

Lemma generate_new_contraints_add_Zeros : forall (l1 l2 l3 : LP) (n lo hi : Z),
    generate_new_constraints n l1 l2 l3 ->
    InequList_Zeros l1 lo hi ->
    InequList_Zeros l2 lo hi ->
    1 <= n < lo -> lo <= hi ->
    InequList_nth_zero n l3.
Proof.
  intros.
  unfold generate_new_constraints in H.
  unfold InequList_nth_zero in *.
  intros.
  apply H in H4.
  destruct H4 as [ c1  [c2 [? [?  ?]]]].
  unfold generate_new_constraint in H6.
  destruct H6 as [ m1 [m2 [ ? [? [? ?]]]]].
  rewrite coef_Znth_nth ; try lia.
Qed.

Lemma InequList_nth_zero_app : forall l1 l2 n,
    InequList_nth_zero n l1 -> InequList_nth_zero n l2 ->
    InequList_nth_zero n (l1 ++ l2).
Proof.
  intros.
  unfold InequList_nth_zero in *.
  intros.
  apply in_app_or in H1.
  destruct H1 ; [apply H | apply H0] ; try tauto.
Qed.

Lemma LP_Implies_UNSAT : forall l1 l2,
    LP_implies l1 l2 ->
    UNSAT l2 ->
    UNSAT l1.
Proof.
  intros.
  intro.
  intro.
  apply (H0 s).
  apply H.
  auto.
Qed.

Lemma sum_prod_zeros : forall x s,
  (forall i, 1 <= i < coef_Zlength x -> coef_Znth i x 0 = 0) ->
  sum_prod (const x) s (coef x) = const x.
Proof.
  intros.
  unfold coef_Zlength, coef_Znth, Constraint_list in *.
  set (a := const x) in *.
  set (l := coef x) in *.
  clearbody a l.
  clear x.
  generalize dependent a. revert l.
  induction s ; intros ; simpl in * ; try lia.
  destruct l ; simpl in * ; auto.
  assert (z = 0).
  {
    specialize (H 1 (ltac: (lia))).
    rewrite Znth_cons in H ; try lia.
    replace (1 - 1) with 0 in H by lia.
    rewrite Znth0_cons in H. lia.
  }
  replace (a0 + a * z) with a0 by lia.
  apply IHs.
  intros.
  rewrite Znth_cons ; try lia.
  specialize (H (i + 1) (ltac: (lia))).
  rewrite Znth_cons in H ; try lia.
  rewrite Znth_cons in H ; try lia.
  replace (i + 1 - 1 - 1) with (i - 1) in H by lia.
  lia.
Qed.