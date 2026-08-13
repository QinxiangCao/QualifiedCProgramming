Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.fme Require Import algorithm.
From SimpleC.EE.Applications_human.fme Require Import implement.
Local Open Scope sac.

Lemma coef_Znth_nth:
  forall n c,
    n >= 1 ->
    coef_Znth n c 0 = nth_coef n c.
Proof.
  intros.
  unfold coef_Znth, nth_coef.
  unfold Constraint_list.
  rewrite Znth_cons; try lia.
  unfold Znth.
  auto.
Qed.

Lemma In_x_nil:
  forall T:Type, forall a x: T,
    In a (x::nil) -> a = x.
Proof.
  intros.
  destruct H; try tauto.
  symmetry. apply H.
Qed.

Lemma in_app_list_iff:
  forall l l' x n c,
    l' = l ++ x::nil ->
    coef_Znth n c 0 <> coef_Znth n x 0 ->
    In c l <-> In c l'.
Proof.
  intros; split; intros.
  - rewrite H. apply in_or_app. tauto.
  - rewrite H in H1.
    apply in_app_or in H1.
    destruct H1; try tauto.
    pose proof In_x_nil _ _ _ H1.
    rewrite H2 in H0.
    tauto.
Qed.

Lemma eliminate_xn_step_re: 
  forall l l' up lo re bp n x,
    eliminate_xn n l bp ->
    form_BP up lo re bp ->
    l' = l ++ x::nil ->
    coef_Znth n x 0 = 0 ->
    n >= 1 ->
    eliminate_xn n l' {| upper := up; lower := lo; remain := x::re|}.
Proof.
  intros.
  split; intros; induction H; simpl;
  unfold form_BP in H0;
  destruct H0 as [BP1 [BP2 BP3]];
  rewrite <- BP1 in elim_upper;
  rewrite <- BP2 in elim_lower;
  rewrite <- BP3 in elim_remain;
  clear BP1 BP2 BP3.
  - rewrite elim_upper.
    split; intros.
    + pose proof (in_app_list_iff l l' x n c H1).
      destruct H.
      split; try tauto.
      apply H0; try tauto.
      rewrite H2.
      rewrite <- coef_Znth_nth in H4; lia.
    + pose proof (in_app_list_iff l l' x n c H1).
      destruct H.
      split; try tauto.
      apply H0; try tauto.
      rewrite H2.
      rewrite <- coef_Znth_nth in H4; lia.
  - rewrite elim_lower.
    split; intros.
    + pose proof (in_app_list_iff l l' x n c H1).
      destruct H.
      split; try tauto.
      apply H0; try tauto.
      rewrite H2.
      rewrite <- coef_Znth_nth in H4; lia.
    + pose proof (in_app_list_iff l l' x n c H1).
      destruct H.
      split; try tauto.
      apply H0; try tauto.
      rewrite H2.
      rewrite <- coef_Znth_nth in H4; lia.
  - split; intros.
    + destruct H.
      * rewrite <- H.
        rewrite <- coef_Znth_nth; try lia.
        split; try lia.
        rewrite H1.
        apply in_elt.
      * rewrite elim_remain in H.
        destruct H; split; try tauto.
        rewrite H1.
        apply in_or_app; tauto.
    + destruct H.
      rewrite H1 in H.
      apply in_app_or in H.
      destruct H.
      * right. apply elim_remain. tauto.
      * left. symmetry. apply In_x_nil. tauto.   
Qed.

(* proof similar to eliminate_xn_step_re *)
Lemma eliminate_xn_step_lo: 
  forall l l' up lo re bp n x,
    eliminate_xn n l bp ->
    form_BP up lo re bp ->
    l' = l ++ x::nil ->
    coef_Znth n x 0 < 0 ->
    n >= 1 ->
    eliminate_xn n l' {| upper := up; lower := x::lo; remain := re|}.
Proof.
  intros.
  split; intros; induction H; simpl;
  unfold form_BP in H0;
  destruct H0 as [BP1 [BP2 BP3]];
  rewrite <- BP1 in elim_upper;
  rewrite <- BP2 in elim_lower;
  rewrite <- BP3 in elim_remain;
  clear BP1 BP2 BP3.
  - rewrite elim_upper.
  split; intros.
  + pose proof (in_app_list_iff l l' x n c H1).
    destruct H.
    split; try tauto.
    apply H0; try tauto.
    rewrite <- coef_Znth_nth in H4; lia.
  + pose proof (in_app_list_iff l l' x n c H1).
    destruct H.
    split; try tauto.
    apply H0; try tauto.
    rewrite <- coef_Znth_nth in H4; lia.
  - split; intros.
  + destruct H.
    * rewrite <- H.
      rewrite <- coef_Znth_nth; try lia.
      split; try lia.
      rewrite H1.
      apply in_elt.
    * rewrite elim_lower in H.
      destruct H; split; try tauto.
      rewrite H1.
      apply in_or_app; tauto.
  + destruct H.
    rewrite H1 in H.
    apply in_app_or in H.
    destruct H.
    * right. apply elim_lower. tauto.
    * left. symmetry. apply In_x_nil. tauto.
  - rewrite elim_remain.
  split; intros.
  + pose proof (in_app_list_iff l l' x n c H1).
    destruct H.
    split; try tauto.
    apply H0; try tauto.
    rewrite <- coef_Znth_nth in H4; lia.
  + pose proof (in_app_list_iff l l' x n c H1).
    destruct H.
    split; try tauto.
    apply H0; try tauto.
    rewrite <- coef_Znth_nth in H4; lia.
Qed.

(* proof similar to eliminate_xn_step_re *)
Lemma eliminate_xn_step_up: 
  forall l l' up lo re bp n x,
    eliminate_xn n l bp ->
    form_BP up lo re bp ->
    l' = l ++ x::nil ->
    coef_Znth n x 0 > 0 ->
    n >= 1 ->
    eliminate_xn n l' {| upper := x::up; lower := lo; remain := re|}.
Proof.
  intros.
  split; intros; induction H; simpl;
  unfold form_BP in H0;
  destruct H0 as [BP1 [BP2 BP3]];
  rewrite <- BP1 in elim_upper;
  rewrite <- BP2 in elim_lower;
  rewrite <- BP3 in elim_remain;
  clear BP1 BP2 BP3.
  - split; intros.
  + destruct H.
    * rewrite <- H.
      rewrite <- coef_Znth_nth; try lia.
      split; try lia.
      rewrite H1.
      apply in_elt.
    * rewrite elim_upper in H.
      destruct H; split; try tauto.
      rewrite H1.
      apply in_or_app; tauto.
  + destruct H.
    rewrite H1 in H.
    apply in_app_or in H.
    destruct H.
    * right. apply elim_upper. tauto.
    * left. symmetry. apply In_x_nil. tauto.
  - rewrite elim_lower.
  split; intros.
  + pose proof (in_app_list_iff l l' x n c H1).
    destruct H.
    split; try tauto.
    apply H0; try tauto.
    rewrite <- coef_Znth_nth in H4; lia.
  + pose proof (in_app_list_iff l l' x n c H1).
    destruct H.
    split; try tauto.
    apply H0; try tauto.
    rewrite <- coef_Znth_nth in H4; lia.
  - rewrite elim_remain.
  split; intros.
  + pose proof (in_app_list_iff l l' x n c H1).
    destruct H.
    split; try tauto.
    apply H0; try tauto.
    rewrite <- coef_Znth_nth in H4; lia.
  + pose proof (in_app_list_iff l l' x n c H1).
    destruct H.
    split; try tauto.
    apply H0; try tauto.
    rewrite <- coef_Znth_nth in H4; lia.
Qed.

Lemma list_split_adjust:
  forall T: Type, forall l1 l2: list T, forall x : T,
    l1 ++ x::l2 = (l1 ++ x::nil) ++ l2.
Proof.
  intros.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma inequlist_0_implies_nil:
  forall l n,
    InequList 0 n l |-- “ l = nil ” && emp.
Proof.
  pre_process.
  destruct l.
  - simpl. entailer!.
  - simpl. Intros c0 y. tauto.
Qed.

Lemma coef_array_length: forall x n c, x <> NULL ->
  coef_array x n c |-- “ coef_Zlength c = n ”.
Proof.
  intros.
  unfold coef_array. Split.
  - Intros. lia. 
  - Intros.
  unfold coef_Zlength.
  sep_apply IntArray.full_length.
  entailer!.
Qed.

Lemma coef_array_merge: forall x n m a l,
  0 <= n < m -> 1 <= n -> x <> NULL -> 
  store_int (x + n * sizeof(INT)) a ** coef_array_missing_i_rec x n 0 m l |-- coef_array x m (coef_replace_Znth n a l).
Proof.
  intros.
  unfold coef_array, coef_array_missing_i_rec.
  simpl.
  replace (x + n * 4) with (x + n * sizeof (INT))
    by (rewrite sizeof_int; lia).
  sep_apply IntArray.missing_i_merge_to_full ; try lia.
  Right.
  unfold coef_replace_Znth.
  unfold Constraint_list.
  rewrite replace_Znth_cons; try lia. entailer!.
Qed.

Lemma gcd_quot_left_pos:
  forall x z, (exists y, x > 0 /\ y > 0 /\ z = Zgcd x y) ->
    x ÷ z > 0.
Proof.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  assert (0 < z).
  + assert (0 <= z).
    - rewrite H1.
      apply Z.gcd_nonneg.
    - destruct z.
      * apply eq_sym in H1.
        apply Z.gcd_eq_0_l in H1.
        lia.
      * lia.
      * lia.
  + rewrite Z.quot_div_exact.
    assert (forall a b, a < b -> b > a) by lia. 
    apply H3.
    - apply Z.div_str_pos.
      split; try lia.
      apply Z.divide_pos_le; try lia.
      rewrite H1.
      apply Z.gcd_divide_l.
    - lia.
    - rewrite H1.
      apply Z.gcd_divide_l.
Qed.

Lemma gcd_quot_right_pos:
  forall y z, (exists x, x > 0 /\ y > 0 /\ z = Zgcd x y) ->
    y ÷ z > 0.
Proof.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  assert (0 < z).
  + assert (0 <= z).
    - rewrite H1.
      apply Z.gcd_nonneg.
    - destruct z.
      * apply eq_sym in H1.
        apply Z.gcd_eq_0_l in H1.
        lia.
      * lia.
      * lia.
  + rewrite Z.quot_div_exact.
    assert (forall a b, a < b -> b > a) by lia. 
    apply H3.
    - apply Z.div_str_pos.
      split; try lia.
      apply Z.divide_pos_le; try lia.
      rewrite H1.
      apply Z.gcd_divide_r.
    - lia.
    - rewrite H1.
      apply Z.gcd_divide_r.
Qed.

Lemma mul_list_length:
  forall m l, length (mul_list m l) = length l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma list_add_length:
  forall l1 l2, 
    length l1 = length l2 ->
    length (list_add l1 l2) = length l1.
Proof.
  intros l1.
  induction l1; intros.
  - destruct l2; try tauto.
    simpl in H.
    simpl.
    discriminate H.
  - destruct l2; try tauto.
    simpl in H.
    assert (length l1 = length l2) by lia.
    simpl.
    rewrite IHl1; try tauto.
Qed.

Lemma generate_new_constr_length:
  forall c1 c2 m1 m2 n, (coef_Zlength c1 = n /\ coef_Zlength c2 = n) ->
    coef_Zlength
    {|
      const := m1 * const c1 + m2 * const c2;
      coef := list_add (mul_list m1 (coef c1)) (mul_list m2 (coef c2))
    |} = n.
Proof. 
  intros.
  unfold coef_Zlength in *.
  simpl in *.
  destruct H.
  assert (length (coef c1) = length (coef c2)) by lia.
  rewrite list_add_length.
  rewrite mul_list_length.
  tauto.
  repeat rewrite mul_list_length.
  apply H1.
Qed.

Lemma constr_list_constr:
  forall l, l <> nil -> Constraint_list (list_Constraint l) = l.
Proof.
  intros.
  unfold Constraint_list.
  destruct l.
  - tauto.
  - simpl. reflexivity.
Qed.

Lemma nth_a_replace_nth_b:
  forall T: Type, 
  forall l: list T, forall a b: nat, forall v u: T,
    (a <> b)%nat ->
    nth a (replace_nth b l v) u = nth a l u.
Proof.
  intros.
  revert a b H.
  induction l; intros.
  - destruct a;
    destruct b; try lia; reflexivity.
  - destruct a0; simpl.
    + destruct b; simpl; [lia | reflexivity].
    + destruct b; simpl; try reflexivity.
      assert (a0 <> b)%nat by lia.
      apply IHl.
      easy. 
Qed.

Lemma replace_nth_length:
  forall T: Type, forall l: list T, forall i v, 
    length (replace_nth i l v) = length l.
Proof.
  intros.
  revert i v.
  induction l; intros; simpl.
  - destruct i; reflexivity.
  - destruct i; simpl; try reflexivity.
    rewrite IHl. reflexivity.
Qed.

Lemma nth_replace_nth_eq:
  forall T: Type, forall l: list T, forall i v u, 
    (i < length l)%nat ->
    nth i (replace_nth i l v) u = v.
Proof.
  intros.
  revert i H.
  induction l; intros; simpl.
  - simpl in H. lia.  
  - simpl in H.
    destruct i; simpl.
    + reflexivity.
    + apply IHl. lia.
Qed. 

Lemma coef_replace_Znth_le:
  forall c n m v, 0 <= n /\ n < m /\ m < coef_Zlength (coef_replace_Znth m v c) ->
    coef_Znth n (coef_replace_Znth m v c) 0 = coef_Znth n c 0.
Proof. 
  intros.
  destruct H as [H0 [H1 H2]].
  clear H2.
  unfold coef_Znth.
  unfold coef_replace_Znth in *.
  rewrite constr_list_constr. 
  2:{
    unfold Constraint_list.
    rewrite replace_Znth_cons by lia.
    easy.
  }
  set (l := Constraint_list c).
  unfold Znth.
  unfold replace_Znth.
  set (a := Zto_nat n).
  set (b := Zto_nat m).
  assert (a <> b)%nat by lia.
  clear H0 H1.
  apply nth_a_replace_nth_b.
  easy.
Qed.

Lemma coef_replace_Znth_eq:
  forall c n v, 0 <= n /\ n < coef_Zlength (coef_replace_Znth n v c) ->
    coef_Znth n (coef_replace_Znth n v c) 0 = v.
Proof. 
  intros.
  destruct H.
  unfold coef_Znth.
  unfold coef_replace_Znth in *.
  unfold coef_Zlength in H0.
  assert (replace_Znth n v (Constraint_list c) <> nil).
  {
    unfold Constraint_list.
    destruct n.
    - unfold replace_Znth.
      simpl.
      easy.
    - rewrite replace_Znth_cons; easy.
    - lia.
  }
  rewrite constr_list_constr in *; try apply H1.
  unfold replace_Znth in H0.
  rewrite replace_nth_length in H0.
  unfold Znth.
  unfold replace_Znth.
  apply nth_replace_nth_eq.
  lia.
Qed.

Lemma coef_replace_Znth_ge:
  forall c n m v, 0 <= m /\ m < n /\ n < coef_Zlength (coef_replace_Znth m v c) ->
    coef_Znth n (coef_replace_Znth m v c) 0 = coef_Znth n c 0.
Proof. 
  intros.
  destruct H as [H0 [H1 H2]].
  clear H2.
  unfold coef_Znth.
  unfold coef_replace_Znth in *.
  rewrite constr_list_constr. 
  2:{
    unfold Constraint_list.
    destruct m; try lia.
    - unfold replace_Znth.
      simpl.
      easy. 
    - rewrite replace_Znth_cons by lia.
      easy.
  }
  set (l := Constraint_list c).
  unfold Znth.
  unfold replace_Znth.
  set (a := Zto_nat n).
  set (b := Zto_nat m).
  assert (a <> b)%nat by lia.
  clear H0 H1.
  apply nth_a_replace_nth_b.
  easy.
Qed.

Lemma coef_Zlength_pos:
  forall c, coef_Zlength c > 0.
Proof.
  intros.
  unfold coef_Zlength.
  unfold Constraint_list.
  simpl.
  lia.
Qed.

Lemma list_add_mul_ext:
  forall l l1 l2 m1 m2,
    length l1 = length l2 ->
    l = list_add (mul_list m1 l1) (mul_list m2 l2) ->
    length l = length l1 /\
    (forall i, nth i l 0 = m1 * nth i l1 0 + m2 * nth i l2 0).
Proof.
  intros.
  split.
  - assert (length (mul_list m1 l1) = length (mul_list m2 l2)).
    repeat rewrite mul_list_length. easy.
    assert (length l = length (mul_list m1 l1)).
    rewrite H0. apply list_add_length. easy.
    rewrite H2. apply mul_list_length.
  - revert l l2 H H0.
    induction l1; intros.
    + simpl in H.
      destruct l2; try discriminate H.
      simpl in H0.
      rewrite H0.
      destruct i; simpl; lia.
    + simpl in H.
      destruct l2; try discriminate H.
      simpl in H0.
      destruct l; try discriminate H0.
      simpl in H.
      assert (length l1 = length l2) by lia; clear H.
      inversion H0; clear H0 H2; rename H3 into H.
      destruct i; simpl; try easy.
      rewrite <- H.
      apply IHl1; easy.
Qed.

Lemma list_eq_ext:
  forall T: Type, forall l1 l2: list T, forall d,
    length l1 = length l2 ->
    (forall i, (i < length l1)%nat -> nth i l1 d = nth i l2 d) ->
    l1 = l2.
Proof.
  intros.
  revert l2 H H0.
  induction l1; intros; simpl.
  - destruct l2; easy.
  - destruct l2; try easy.
    f_equal.
    + specialize H0 with O.
      simpl in H0.
      apply H0. lia.
    + apply IHl1.
      simpl in H; lia.
      intros.
      specialize H0 with (S i).
      simpl in H0.
      apply H0. lia.
Qed.

Lemma coef_Zlength_length_coef:
  forall c n,
    n = coef_Zlength c -> Z.of_nat(length (coef c)) = n-1.
Proof.
  intros.
  unfold coef_Zlength in H.
  unfold Constraint_list in H.
  simpl in H.
  lia.
Qed.

Lemma coef_Zlength_overflow :
  forall c n, n >= coef_Zlength c ->
    coef_Znth n c 0 = 0.
Proof.
  intros.
  unfold coef_Znth.
  unfold coef_Zlength in H.
  unfold Constraint_list in *.
  unfold Znth.
  apply nth_overflow.
  lia.
Qed.

Lemma generate_new_constraint_complete:
  forall num c1 c2 c3, num >= 1 ->
    (exists n m1 m2, n = coef_Zlength c1 /\ n = coef_Zlength c2 /\ n = coef_Zlength c3 /\
            generate_new_constraint_partial num n m1 m2 c1 c2 c3) ->
    generate_new_constraint num c1 c2 c3.
Proof. 
  intros.
  rename H into num_H.
  rename H0 into H.
  destruct H as [n [m1 [m2 H]]].
  destruct H as [Hc1 [Hc2 [Hc3 H]]].
  unfold generate_new_constraint_partial in H.
  destruct H as [H2 [H3 [nth_num H]]].
  unfold generate_new_constraint.
  exists m1, m2.
  repeat split; try tauto.
  {
    rewrite <- coef_Znth_nth ; try lia.
    destruct (Z_lt_dec num n).
    - specialize (H num (ltac:(lia))).
      rewrite nth_num in H. lia.
    - apply coef_Zlength_overflow. lia.
  }
  destruct c3 as [c ef].
  pose proof coef_Zlength_pos c1.
  unfold coef_Znth in H.
  unfold Constraint_list in H.
  unfold Znth in H.
  f_equal.
  - specialize H with 0.
    assert (0 <= 0 < n) by lia.
    pose proof H H1.
    clear H H0 H1.
    rename H4 into H.
    simpl in H.
    easy. 
  - assert 
    (K: forall k,
      Z.of_nat k < n - 1 -> 
      nth k ef 0  =  m1 * nth k (coef c1) 0 + m2 * nth k (coef c2) 0).
    {
      intros.
      specialize H with (Z.of_nat (S k)).
      assert (0 <= Z.of_nat (S k) < n) by lia.
      pose proof H H4.
      clear H H4; rename H5 into H.
      rewrite Nat2Z.id in H.
      simpl in H.
      easy.
    }
    clear H.
    set (l := list_add (mul_list m1 (coef c1)) (mul_list m2 (coef c2))).
    pose proof coef_Zlength_length_coef _ _ Hc1.
    pose proof coef_Zlength_length_coef _ _ Hc2.
    pose proof coef_Zlength_length_coef _ _ Hc3.
    clear Hc1 Hc2 Hc3.
    simpl in H4.
    assert (length (coef c1) = length (coef c2)) by lia.
    assert (L: l = list_add (mul_list m1 (coef c1)) (mul_list m2 (coef c2))) by easy.
    pose proof list_add_mul_ext l _ _ m1 m2 H5 L.
    destruct H6.
    apply list_eq_ext with (d:=0); try lia.
    intros.
    rewrite H7.
    apply K.
    lia.
Qed.

Lemma InequList_seg_append: forall l x n p1 p2 p3 coef,
  p2 <> NULL -> coef <> NULL ->
  coef_array coef n x **
  &( p2 # "InequList" ->ₛ "coef") # Ptr |-> coef **
  &( p2 # "InequList" ->ₛ "next") # Ptr |-> p3 **
  InequList_seg p1 p2 n l
|--
  InequList_seg p1 p3 n (l ++ x :: nil).
Proof.
  intros.
  revert p1 p2 p3 H.
  induction l; simpl; intros.
  - entailer!.
    Exists coef p3. entailer!.
    rewrite H1. entailer!.
  - Intros.
    Intros x0 z.
    entailer!.
    Exists x0 z.
    entailer!.
    specialize IHl with z p2 p3.
    apply IHl in H.
    sep_apply H.
    easy.
Qed.

Lemma InequList_seg_append_list: forall l1 l2 x n p1 p2 p3 coef,
  p2 <> NULL -> coef <> NULL ->
  coef_array coef n x **
  &( p2 # "InequList" ->ₛ "coef") # Ptr |-> coef **
  &( p2 # "InequList" ->ₛ "next") # Ptr |-> p3 **
  InequList_seg p1 p2 n l1 **
  InequList p3 n l2
|--
  InequList p1 n (l1 ++ x :: l2).
Proof. 
  intros.
  sep_apply InequList_seg_append; try easy.
  revert p1 p3 l2.
  induction l1; intros; simpl.
  - Intros x0 z.
    Exists x0 z. entailer!.
    rewrite H5; easy.
  - Intros x0 z. 
    Exists x0 z. entailer!. 
Qed.

Lemma InequList_seg_degeneration: forall p n l,
  InequList_seg p 0 n l |-- InequList p n l.
Proof. 
  intros.
  revert p.
  induction l; intros; simpl.
  - entailer!.
  - Intros c z. Exists c z.
    entailer!.
Qed.

Lemma InequList_seg_app: forall l1 l2 n p1 p2,
  InequList_seg p1 p2 n l1 **
  InequList p2 n l2
|--
  InequList p1 n (l1 ++ l2).
Proof. 
  intros.
  revert p1 p2 l2.
  induction l1; intros; simpl.
  - Intros. subst. entailer!.
  - Intros x0 z. 
    Exists x0 z. entailer!. 
Qed.

Lemma InequList_length : forall l n x p,
  InequList p n (x :: l) |-- “ coef_Zlength x = n ”.
Proof. 
  intros.
  simpl.
  Intros c y.
  prop_apply (coef_array_length) ; try lia.
  entailer!.
Qed.

Lemma in_list_app1: forall T: Type, forall (x1 x2: T) l,
  In x1 l -> In x1 (l ++ x2 :: nil).
Proof.
  intros.
  apply in_or_app.
  auto.
Qed.

Lemma generate_new_constraints_step: forall n l1 x1 l21 x2 l22 x3 l3,
  generate_new_constraints_partial n l1 x1 l21 (x2::l22) l3 /\
  generate_new_constraint n x1 x2 x3 ->
  generate_new_constraints_partial n l1 x1 (List.app l21 (x2::nil)) l22 (x3::l3).
Proof.
  unfold generate_new_constraints_partial.
  intros.
  destruct H.
  destruct H.
  exists x.
  destruct H.
  exists (x3 :: x0).
  destruct H.
  destruct H1.
  split; intros.
  + pose proof H c.
    split; intros.
    - unfold In in H4.
      destruct H4.
      * right.
        rewrite H4.
        unfold In.
        left.
        auto.
      * destruct H3.
        assert (In c x \/ In c x0).
        ++ apply H3. apply H4.
        ++ destruct H6.
           -- auto.
           -- right.
              apply in_cons.
              auto.
    - destruct H4.
      * destruct H3.
        assert (In c l3) by auto.
        apply in_cons.
        auto.
      * unfold In in H4.
        destruct H4.
        ++ unfold In. left. auto.
        ++ destruct H3.
           assert (In c l3) by auto.
           apply in_cons.
           auto.
  + split; intros.
    - rewrite <-list_split_adjust.
      auto.
    - pose proof H2 c2.
      destruct H3.
      * exists x2.
        split.
        ++ apply in_elt.
        ++ rewrite <-H3. auto.
      * destruct H4.
        ++ auto.
        ++ destruct H4.
           exists x4.
           split.
           -- apply in_list_app1. auto.
           -- auto.
Qed.

Lemma generate_new_constraints_complete: forall n l1 x1 l2 l3,
  generate_new_constraints_partial n l1 x1 l2 nil l3 ->
  generate_new_constraints n (l1 ++ x1 :: nil) l2 l3.
Proof. 
  intros.
  unfold generate_new_constraints_partial in H.
  destruct H as [res1 [res2 H]].
  destruct H as [H0 [H1 H2]].
  unfold generate_new_constraints in *. intros.
  specialize H0 with c.
  destruct H0 as [H0 _]. 
  apply H0 in H. clear H0; destruct H.
  - apply H1 in H; clear H1.
    destruct H as [c1 [c2 H]].
    exists c1. exists c2.
    repeat split; try tauto.
    + apply in_or_app. left. easy.
    + destruct H. destruct H0.
      apply in_app_or in H0.
      destruct H0; try easy.
  - apply H2 in H; clear H2.
    destruct H as [c2 H].
    exists x1. exists c2.
    repeat split; try tauto.
    apply in_elt.
Qed.
