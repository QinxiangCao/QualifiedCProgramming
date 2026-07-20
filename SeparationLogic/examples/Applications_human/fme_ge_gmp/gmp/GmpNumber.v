Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
From SumLib Require Import SumLib.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import CommonAssertion Mem SeparationLogic IntLib.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import GmpAux. Import Aux.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Require Import String.
Local Open Scope string.
Import naive_C_Rules.
Local Open Scope sac.
Import SumLib.Sum.

Lemma uint_array_undef_seg_align4 : forall ptr size cap,
  UIntArray.undef_seg ptr size cap |-- store_align4_n (cap - size).
Proof.
  intros.
  unfold UIntArray.undef_seg.
  destruct (Z_le_dec size cap).
  - set (n := Z.to_nat (cap - size)).
    replace (cap - size) with (Z.of_nat n) by lia.
    replace (cap) with (size + Z.of_nat n) by lia.
    clearbody n. clear l cap.
    revert ptr size.
    induction n ; simpl in * ; intros.
    + unfold store_align4_n. Exists nil.
      entailer!.
      constructor.
    + replace (size + Z.pos (Pos.of_succ_nat n)) with (size + 1 + Z.of_nat n) by lia.
      sep_apply IHn.
      sep_apply undef_store_uint_align4.
      sep_apply (store_align4_merge 1 (Z.of_nat n)).
      replace (Z.pos (Pos.of_succ_nat n)) with (1 + Z.of_nat n) by lia.
      entailer!.
  - replace (Z.to_nat (cap - size)) with 0%nat by lia.
    simpl. Intros.
    lia.
Qed.

Lemma uint_array_undef_full_align4 : forall ptr size,
  UIntArray.undef_full ptr size |-- store_align4_n size.
Proof.
  intros.
  sep_apply UIntArray.undef_full_to_undef_seg.
  sep_apply uint_array_undef_seg_align4.
  replace (size - 0) with size by lia.
  entailer!.
Qed.

Lemma uint_array_undef_full_implies_int_length : forall ptr size,
  UIntArray.undef_full ptr size |-- “ size <= INT_MAX ”.
Proof.
  intros.
  sep_apply (uint_array_undef_full_align4 ptr size).
  prop_apply (store_align4_n_valid size).
  Intros.
  change Int.max_unsigned with 4294967295 in H.
  assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity.
  rewrite Hcalc in H.
  change INT_MAX with 2147483647.
  entailer!.
Qed.
  
Lemma uint_array_full_align4 : forall ptr size data,
  UIntArray.full ptr size data |-- store_align4_n size.
Proof.
  intros.
  sep_apply UIntArray.full_to_undef_full.
  sep_apply uint_array_undef_full_align4.
  entailer!.
Qed.


Definition Prod2 {A B} (a : A) (b : B) := (a , b).

Section Internal.
  
Variable Base : Z.
Variable Base_pos: 0 < Base.

Definition mpd_store_list (ptr: addr) (data: list Z): Assertion :=
  UIntArray.full ptr (Zlength data) data.

Definition list_to_Z (data: list Z): Z :=
  sum (fun i => 0 <= i < Zlength data)
      (fun i => Znth i data 0 * Base ^ i).

Fixpoint list_within_bound (data: list Z): Prop :=
  match data with
   | nil => True
   | a :: l0 => 0 <= a < Base /\ (list_within_bound l0)
  end.

Definition mpd_store_Z (ptr: addr) (n: Z) (size: Z) : Assertion :=
  EX data,
    “ list_to_Z data = n /\ list_within_bound data ” && “ size = Zlength data ” && mpd_store_list ptr data.

Definition mpd_store_Z_compact (ptr: addr) (n size: Z): Assertion :=
  EX data,
    “ list_to_Z data = n /\ last data 1 >= 1 /\ list_within_bound data ” && “ size = Zlength data ” && mpd_store_list ptr data.

Definition is_compact_Z (n: Z) (size: Z) : Prop :=
exists data, 
  list_to_Z data = n /\
  Zlength data = size /\ 
  list_within_bound data /\
  last data 1 >= 1.

Lemma list_to_Z_injection: forall l1 l2 n1 n2,
  list_to_Z l1 = n1 ->
  list_to_Z l2 = n2 ->
  l1 = l2 -> n1 = n2.
Proof.
  intros.
  subst.
  lia.
Qed.

Lemma list_to_Z_cons : forall a l,
  list_to_Z (a :: l) = a + Base * list_to_Z l.
Proof.
  intros a l.
  unfold list_to_Z.
  rewrite (sum_Z_range_Znth_cons_indexed 0 a l
    (fun i x => x * Base ^ i)).
  rewrite Z.pow_0_r.
  rewrite Z.mul_1_r.
  rewrite <- sum_Z_range_factor_l.
  f_equal.
  apply sum_Z_range_ext.
  intros i Hi.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  ring.
Qed.

Lemma list_to_Z_nil :
  list_to_Z [] = 0.
Proof.
  unfold list_to_Z.
  rewrite Zlength_nil.
  rewrite sum_Z_range_empty by lia.
  reflexivity.
Qed.

Lemma list_to_Z_single : forall a,
  list_to_Z [a] = a.
Proof.
  intros a.
  rewrite list_to_Z_cons, list_to_Z_nil.
  ring.
Qed.

Lemma list_to_Z_app :
  0 < Base ->
  forall l1 l2,
  list_to_Z (l1 ++ l2) = list_to_Z l1 + list_to_Z l2 * (Base ^ (Zlength l1)).
Proof.
  intros _ l1 l2.
  unfold list_to_Z.
  rewrite (sum_Z_range_Znth_app_indexed 0 l1 l2
    (fun i x => x * Base ^ i)).
  assert (Hright :
    sum (fun i => 0 <= i < Zlength l2)
      (fun i => Znth i l2 0 * Base ^ (i + Zlength l1)) =
    sum (fun i => 0 <= i < Zlength l2)
      (fun i => Base ^ Zlength l1 * (Znth i l2 0 * Base ^ i))).
  {
    apply sum_Z_range_ext.
    intros i Hi.
    rewrite Z.pow_add_r by (try apply Zlength_nonneg; lia).
    ring.
  }
  rewrite Hright.
  rewrite sum_Z_range_factor_l.
  ring.
Qed. 

Lemma list_to_Z_zeros : forall m,
  list_to_Z (zeros m) = 0.
Proof.
  intros m.
  unfold list_to_Z, zeros.
  rewrite (sum_Z_range_Znth_repeat_indexed 0 0 (Z.to_nat m)
    (fun i x => x * Base ^ i)).
  apply sum_Z_range_eq_zero.
  intros i Hi.
  ring.
Qed.

Lemma zeros_list_within_bound : forall n,
  list_within_bound (zeros n).
Proof.
  intros.
  unfold zeros.
  induction (Z.to_nat n) ; simpl ; try tauto.
  split ; try lia.
  auto.
Qed.

Lemma __list_within_bound_concat_r: forall (l1: list Z) (a: Z),
  list_within_bound l1 ->
  0 <= a < Base ->
  list_within_bound (l1 ++ [a]).
Proof.
  intros.
  induction l1.
  + rewrite app_nil_l.
    simpl.
    lia.
  + simpl in *; repeat split; try tauto.
Qed.

Lemma list_within_bound_concat: forall (l1 l2: list Z),
  list_within_bound l1 ->
  list_within_bound l2 ->
  list_within_bound (l1 ++ l2).
Proof.
  intros.
  revert l1 H.
  induction l2.
  + intros.
    rewrite app_nil_r.
    tauto.
  + intros.
    simpl in H0.
    destruct H0.
    rewrite Aux.list_app_cons.
    pose proof (__list_within_bound_concat_r l1 a H H0).
    specialize (IHl2 H1 (app l1 [a]) H2).
    tauto.
Qed.

Lemma list_within_bound_Znth_bound: forall (l: list Z) (i: Z),
  0 <= i < Zlength l ->
  list_within_bound l ->
  0 <= Znth i l 0 < Base.
Proof.
  intros.
  revert i H.
  induction l; intros.
  + rewrite Zlength_nil in H.
    lia.
  + assert (i = 0 \/ i > 0). { lia. }
    destruct H1.
    - rewrite H1.
      rewrite (Znth0_cons 0 a l).
      simpl in H0.
      lia.
    - rewrite Znth_cons; try lia.
      simpl in H0; destruct H0.
      rewrite Zlength_cons in H; unfold Z.succ in H.
      specialize (IHl H2 (i - 1) ltac:(lia)).
      lia.
Qed.

Lemma list_within_bound_Znth: forall (l: list Z) (i: Z),
  0 <= i ->
  list_within_bound l ->
  0 <= Znth i l 0 < Base.
Proof.
  intros.
  destruct (Z_lt_dec i (Zlength l)).
  - apply list_within_bound_Znth_bound; try tauto.
  - rewrite <- (app_nil_r l).
    rewrite app_Znth2 ; try lia.
    assert (i - Zlength l >= 0) by lia.
    unfold Znth.
    destruct (Z.to_nat (i - Zlength l)) ; simpl; lia.
Qed.

Lemma list_within_bound_sublist : forall (l: list Z) (lo hi: Z),
  0 <= lo <= hi -> hi <= Zlength l ->
  list_within_bound l ->
  list_within_bound (sublist lo hi l).
Proof.
  intros.
  generalize dependent lo. 
  generalize dependent hi.
  revert H1.
  induction l; intros.
  - rewrite Zlength_nil in H0.
    rewrite Zsublist_nil  ; try lia.
    tauto.
  - destruct (Z.eq_dec hi lo).
    + subst. rewrite Zsublist_nil ; try lia.
      simpl. tauto.
    + simpl in H1. 
      destruct (Z.eq_dec lo 0).
      * subst lo. 
        rewrite sublist_cons1 ; try lia.
        rewrite Zlength_cons in H0.
        split ; try tauto. 
        apply IHl ; try tauto ; try lia.
      * rewrite sublist_cons2 ; try lia.
        rewrite Zlength_cons in H0.
        apply IHl ; try tauto ; try lia.  
Qed.
    

Lemma __list_within_bound_split_r: forall (l1: list Z) (a: Z),
  list_within_bound (l1 ++ [a]) ->
  list_within_bound l1 /\ 0 <= a < Base.
Proof.
  intros.
  induction l1.
  + rewrite app_nil_l in H.
    simpl in *.
    tauto.
  + simpl in *.
    destruct H.
    specialize (IHl1 H0).
    tauto.
Qed.

Lemma list_within_bound_split: forall (l1 l2: list Z),
  list_within_bound (l1 ++ l2) ->
  list_within_bound l1 /\ list_within_bound l2.
Proof.
  intros.
  revert l1 H.
  induction l2.
  + intros.
    simpl.
    rewrite app_nil_r in H.
    tauto.
  + intros.
    simpl.
    rewrite Aux.list_app_cons in H.
    specialize (IHl2 (app l1 [a]) H).
    destruct IHl2.
    apply __list_within_bound_split_r in H0.
    tauto.
Qed.

Lemma list_to_Z_Leading_zeros_equiv : forall l m,
  0 < Base ->
  list_to_Z l = list_to_Z (l ++ zeros m).
Proof.
  intros.
  rewrite list_to_Z_app by exact H.
  rewrite list_to_Z_zeros.
  lia.
Qed.

Lemma list_to_Z_pos : forall l,
  list_within_bound l ->
  list_to_Z l >= 0.
Proof.
  intros l Hbound.
  unfold list_to_Z.
  apply Z.le_ge.
  apply sum_nonneg.
  intros i Hi.
  apply Z.mul_nonneg_nonneg.
  - pose proof (list_within_bound_Znth_bound l i Hi Hbound). lia.
  - apply Z.pow_nonneg; lia.
Qed.

Lemma list_to_Z_zero : forall l,
  list_within_bound l ->
  list_to_Z l = 0 -> l = zeros (Zlength l).
Proof.
  intros.
  induction l ; intros.
  - reflexivity.
  - simpl in *.
    rewrite list_to_Z_cons in H0.
    destruct H.
    pose proof (list_to_Z_pos l H1).
    assert (a = 0) by nia.
    assert (list_to_Z l = 0) by nia.
    rewrite IHl at 1 ; try tauto.
    subst a.
    rewrite Zlength_cons. 
    unfold zeros.
    pose proof (Zlength_nonneg l). 
    replace (Z.to_nat (Z.succ (Zlength l))) with (S (Z.to_nat (Zlength l))) ; try lia.
    reflexivity.
Qed.
    

Lemma list_to_Z_reverse_injection: forall l1 l2,
  list_to_Z l1 = list_to_Z l2 -> list_within_bound l1 ->
  list_within_bound l2 ->
  exists n m, n >= 0 /\ m >= 0 /\ (l1 ++ zeros n)%list = (l2 ++ zeros m)%list.
Proof.
  intros l1.
  induction l1 ; intros.
  - rewrite list_to_Z_nil in H.
    symmetry in H.
    apply list_to_Z_zero in H ; try auto.
    exists (Zlength l2), 0. 
    rewrite <- H.
    unfold zeros. simpl. rewrite app_nil_r.
    repeat split ; try lia.
    pose proof Zlength_nonneg l2. lia.
  - simpl in *.
    destruct H0.
    pose proof (list_to_Z_pos l1 H2).
    rewrite list_to_Z_cons in H.
    destruct l2 ; simpl in *.
    + rewrite list_to_Z_nil in H.
      assert (a = 0) by nia.
      assert (list_to_Z l1 = 0) by nia.
      apply list_to_Z_zero in H5 ; try auto.
      exists 0, (Zlength l1 + 1).
      subst.
      pose proof (Zlength_nonneg l1). 
      repeat split ; try lia.
      unfold zeros.
      simpl.
      rewrite app_nil_r.
      replace (Z.to_nat (Zlength l1 + 1)) with (S (Z.to_nat (Zlength l1))) ; try lia.
      simpl. rewrite H5 at 1. unfold zeros. reflexivity.
    + rewrite list_to_Z_cons in H.
      destruct H1. 
      assert (a = z).
      {
        assert (Heq_canon : list_to_Z l1 * Base + a = list_to_Z l2 * Base + z) by nia.
        assert (z = (list_to_Z l1 * Base + a) mod Base).
        {
          rewrite Heq_canon.
          apply (Zmod_unique _ _ (list_to_Z l2) _ ) ; try lia.
        }
        assert (a = (list_to_Z l1 * Base + a) mod Base).
        {
          apply (Zmod_unique _ _ (list_to_Z l1) _ ) ; try lia.
        }
        lia.
      }
      assert (list_to_Z l1 = list_to_Z l2) by nia.
      specialize (IHl1 _ H6 H2 H4).
      destruct IHl1 as [n [m ?]].
      exists n, m. 
      subst a. simpl. 
      destruct H7 as [? [ ? ?]].
      rewrite H8. 
      repeat split ; try lia.
Qed.

Lemma Zlength_zeros: forall n,
  0 <= n ->
  Zlength (zeros n) = n.
Proof.
  intros.
  unfold zeros.
  set (nat_n := Z.to_nat n).
  replace n with (Z.of_nat nat_n) by lia.
  clearbody nat_n. clear n H. rename nat_n into n.
  induction n ; simpl repeat ; try lia.
  - rewrite Zlength_nil.
    lia.
  - rewrite Zlength_cons.
    rewrite IHn.
    lia.
Qed.


Lemma list_to_Z_reverse_same_length_injection: forall l1 l2,
  list_to_Z l1 = list_to_Z l2 -> list_within_bound l1 ->
  list_within_bound l2 ->
  Zlength l1 = Zlength l2 ->
  l1 = l2.
Proof.
  intros.
  pose proof (list_to_Z_reverse_injection l1 l2 H H0 H1).
  destruct H3 as [n [m [? [? ?]]]].
  assert (Zlength (l1 ++ zeros n) = Zlength (l2 ++ zeros m)). {
    rewrite H5.
    reflexivity.
  }
  do 2 rewrite Zlength_app in H6.
  do 2 rewrite Zlength_zeros in H6; try lia.
  assert (n = m) by lia.
  subst n.
  apply app_inv_tail in H5. auto.
Qed.

Lemma list_to_Z_concat_r:
  0 < Base ->
  forall (l1: list Z) (a: Z),
  0 <= a < Base ->
  list_to_Z (l1 ++ [a]) = a * (Base ^ (Zlength l1)) + list_to_Z l1.
Proof.
  intros Hpos l1 a Ha.
  rewrite list_to_Z_app by exact Hpos.
  rewrite list_to_Z_cons.
  change (list_to_Z []) with 0.
  ring.
Qed.

Lemma list_to_Z_concat:
  0 < Base ->
  forall (l1 l2: list Z),
  list_within_bound l1 ->
  list_within_bound l2 ->
  list_to_Z (l1 ++ l2) = list_to_Z l1 + (list_to_Z l2) * (Base ^ (Zlength l1)).
Proof.
  intros Hpos l1 l2 _ _.
  apply list_to_Z_app.
  exact Hpos.
Qed.

Lemma list_to_Z_weighted_sum_bound : forall high a,
  0 <= high ->
  (forall i, 0 <= i < high -> 0 <= a i < Base) ->
  0 <= sum (fun i => 0 <= i < high) (fun i => a i * Base ^ i) < Base ^ high.
Proof.
  intros high a Hhigh Ha.
  remember (Z.to_nat high) as n eqn:Hn.
  assert (Hhigh_eq : high = Z.of_nat n) by (subst n; lia).
  rewrite Hhigh_eq in Ha |- *.
  clear high Hhigh Hhigh_eq Hn.
  revert a Ha.
  induction n as [|n IH]; intros a Ha.
  - rewrite sum_Z_range_empty by lia.
    rewrite Z.pow_0_r.
    lia.
  - replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) in * by lia.
    rewrite sum_Z_range_cons by lia.
    rewrite Z.pow_0_r, Z.mul_1_r.
    replace (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1) by lia.
    rewrite sum_Z_range_shift_1.
    erewrite sum_Z_range_ext with
      (g := fun i => Base * (a (i + 1) * Base ^ i)).
    2: {
      intros i Hi.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring.
    }
    rewrite sum_Z_range_factor_l.
    pose proof (Ha 0 ltac:(lia)) as Ha0.
    assert (Hshift : forall i, 0 <= i < Z.of_nat n -> 0 <= a (i + 1) < Base).
    {
      intros i Hi.
      apply Ha.
      lia.
    }
    pose proof (IH (fun i => a (i + 1)) Hshift) as Htail.
    pose proof (Z.pow_pos_nonneg Base (Z.of_nat n) Base_pos ltac:(lia)) as Hpow_pos.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    nia.
Qed.

Lemma list_to_Z_bound: forall (l1: list Z),
  list_within_bound l1 ->
  0 <= list_to_Z l1 < Base ^ (Zlength l1).
Proof.
  intros l1 Hbound.
  unfold list_to_Z.
  apply list_to_Z_weighted_sum_bound.
  - apply Zlength_nonneg.
  - intros i Hi.
    pose proof (list_within_bound_Znth_bound l1 i Hi Hbound).
    lia.
Qed.

Lemma list_to_Z_list_append: forall (l: list Z) (i: Z),
  0 <= i < Zlength l ->
  list_within_bound l ->
  list_to_Z (sublist 0 (i + 1) l) = list_to_Z (sublist 0 i l) + Znth i l 0 * (Base ^ i).
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l); try lia.
  rewrite (sublist_single 0 i l) ; try lia.
  pose proof list_within_bound_Znth l i (ltac:(lia)) H0.
  rewrite list_to_Z_concat_r ; try lia.
  rewrite Zlength_sublist ; try lia.
  replace (i - 0) with i by lia.
  nia.
Qed.

Lemma replace_Znth_sublist_head: forall (l: list Z) (i n v: Z),
  0 <= i /\ i < n /\ n <= Zlength l ->
  replace_Znth 0 v (sublist i n l) = v :: sublist (i + 1) n l.
Proof.
  intros.
  rewrite (sublist_split i n (i + 1) l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  reflexivity.
Qed.

Lemma sublist_cons_head: forall (x: Z) (l: list Z),
  sublist 0 1 (x :: l) = x :: nil.
Proof.
  reflexivity.
Qed.

Lemma sublist_cons_tail_all: forall (x: Z) (l: list Z),
  sublist 1 (Zlength (x :: l)) (x :: l) = l.
Proof.
  intros.
  unfold sublist.
  simpl.
  rewrite firstn_all2.
  - reflexivity.
  - rewrite Zlength_correct.
    rewrite Nat2Z.id.
    lia.
Qed.

Lemma list_to_Z_split: forall (l1 l2: list Z),
  list_within_bound (l1 ++ l2) ->
  list_to_Z l1 = list_to_Z (l1 ++ l2) mod (Base ^ (Zlength l1)) /\
  list_to_Z l2 = list_to_Z (l1 ++ l2) / (Base ^ (Zlength l1)).
Proof.
  intros l1 l2 Hbound.
  pose proof (list_within_bound_split l1 l2 Hbound) as Hsplit_bound.
  pose proof (list_to_Z_bound l1 ltac:(tauto)) as Hprefix_bound.
  pose proof (Z.pow_pos_nonneg Base (Zlength l1) Base_pos ltac:(apply Zlength_nonneg)) as Hpow_pos.
  rewrite list_to_Z_app by exact Base_pos.
  split.
  - rewrite Z_mod_plus by lia.
    rewrite Z.mod_small by lia.
    reflexivity.
  - rewrite Z_div_plus by lia.
    rewrite Z.div_small by lia.
    lia.
Qed.

Lemma list_to_Z_compact_bound: forall (l1: list Z),
  list_within_bound l1 -> last l1 1 >= 1 ->
  Base ^ ((Zlength l1) - 1) <= list_to_Z l1 < Base ^ (Zlength l1).
Proof.
  intros.
  destruct l1.
  + rewrite Zlength_nil.
    rewrite list_to_Z_nil.
    simpl. lia.
  + pose proof (list_to_Z_bound (z :: l1) H).
    split ; try lia.
    pose proof (@app_removelast_last Z (z :: l1) 1 ltac:(congruence)).
    pose proof (list_to_Z_split (removelast (z :: l1)) ([last (z :: l1) 1])%list).
    rewrite Aux.Zlength_removelast in H3 ; try congruence.
    rewrite Zlength_cons in *. 
    replace (Z.succ (Zlength l1) - 1) with (Zlength l1) in * by lia.
    rewrite H2 in H.
    specialize (H3 H).
    destruct H3.
    rewrite <- H2 in H3 , H4.
    rewrite list_to_Z_single in H4.
    rewrite H4 in H0.
    pose proof (Zlength_nonneg l1).
    assert (Base ^ (Zlength l1) >= 1) by nia.
    pose proof (Zdiv_ge_1_larger (list_to_Z (z :: l1)) (Base ^ Zlength l1) (ltac:(lia)) (ltac:(lia)) (ltac:(lia))).
    nia.
Qed.

Lemma list_to_Z_nth: forall (l: list Z) (n: Z) (i: Z),
  0 <= i < Zlength l -> list_within_bound l -> 
  Znth i l 0 = (list_to_Z l / (Base ^ i)) mod Base.
Proof.
  intros l n i Hi Hbound.
  pose proof (sublist_split 0 (Zlength l) i l ltac:(lia) ltac:(lia)) as Hsplit_i.
  rewrite (sublist_self l (Zlength l) ltac:(lia)) in Hsplit_i.
  pose proof Hbound as Hbound_i.
  rewrite Hsplit_i in Hbound_i.
  pose proof (list_to_Z_split (sublist 0 i l) (sublist i (Zlength l) l) Hbound_i) as [_ Hquot].
  rewrite Hsplit_i.
  rewrite Zlength_sublist in Hquot by lia.
  replace (i - 0) with i in Hquot by lia.
  rewrite <- Hquot.
  pose proof (sublist_split i (Zlength l) (i + 1) l ltac:(lia) ltac:(lia)) as Hsplit_tail.
  rewrite (sublist_single 0 i l) in Hsplit_tail by lia.
  pose proof (list_within_bound_sublist l i (Zlength l) ltac:(lia) ltac:(lia) Hbound) as Htail_bound.
  rewrite Hsplit_tail in Htail_bound.
  pose proof (list_to_Z_split [Znth i l 0] (sublist (i + 1) (Zlength l) l) Htail_bound) as [Hmod _].
  rewrite Hsplit_tail.
  rewrite Zlength_cons, Zlength_nil in Hmod.
  replace (Z.succ 0) with 1 in Hmod by lia.
  rewrite Z.pow_1_r in Hmod.
  rewrite <- Hmod.
  rewrite list_to_Z_single.
  rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia.
  replace (i - (i - 0)) with 0 by lia.
  rewrite app_Znth1 by (rewrite Zlength_cons, Zlength_nil; lia).
  rewrite Znth0_cons.
  reflexivity.
Qed.

Lemma list_to_Z_cmp_same_length: forall l1 l2 i,
  0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 ->
  sublist (i + 1) (Zlength l1) l1 = sublist (i + 1) (Zlength l2) l2 ->
  list_within_bound l1 ->
  list_within_bound l2 ->
  Znth i l1 0 < Znth i l2 0 ->
  list_to_Z l1 < list_to_Z l2.
Proof.
  intros.
  pose proof (sublist_split 0 (Zlength l1) i l1 ltac:(lia) ltac:(lia)).
  pose proof (sublist_split 0 (Zlength l2) i l2 ltac:(lia) ltac:(lia)).
  rewrite (sublist_self l1 (Zlength l1) ltac:(lia)) in H5.
  rewrite (sublist_self l2 (Zlength l2) ltac:(lia)) in H6.
  rewrite H5, H6.
  rewrite H5 in H2.
  rewrite H6 in H3.
  apply list_within_bound_split in H2.
  apply list_within_bound_split in H3.
  do 2 (rewrite list_to_Z_concat by (try exact Base_pos; try tauto)).
  pose proof (list_to_Z_bound (sublist 0 i l1) (ltac:(tauto))).
  pose proof (list_to_Z_bound (sublist 0 i l2) (ltac:(tauto))).
  do 2 (rewrite Zlength_sublist in * ; try lia).
  replace (i - 0) with i in * by lia.
  rewrite (sublist_split i (Zlength l1) (i + 1)) ; try lia.
  rewrite (sublist_split i (Zlength l2) (i + 1)) ; try lia.
  rewrite (sublist_single 0 i l1) ; try lia.
  rewrite (sublist_single 0 i l2) ; try lia.
  rewrite !list_to_Z_app by exact Base_pos.
  rewrite !list_to_Z_single.
  rewrite !Zlength_cons, !Zlength_nil.
  replace (Z.succ 0) with 1 by lia.
  rewrite !Z.pow_1_r.
  rewrite H1.
  pose proof (Z.pow_pos_nonneg Base i Base_pos ltac:(lia)).
  nia.
Qed.

Lemma list_to_Z_cmp_diff_length: forall l1 l2,
  Zlength l1 < Zlength l2 ->
  list_within_bound l1 -> list_within_bound l2 ->
  last l1 1 >= 1 -> last l2 1 >= 1 ->
  list_to_Z l1 < list_to_Z l2.
Proof.
  intros.
  pose proof (list_to_Z_compact_bound l1 H0 H2).
  pose proof (list_to_Z_compact_bound l2 H1 H3).
  assert (Base ^ (Zlength l1) <= Base ^ (Zlength l2 - 1)). {
    pose proof (Zlength_nonneg l1).
    pose proof (Zlength_nonneg l2).
    apply Z.pow_le_mono_r ; try lia.
  }
  lia.
Qed.

Lemma mpd_store_Z_zero : forall ptr n,
  mpd_store_Z ptr n 0 |-- “ n = 0 ”.
Proof.
  intros.
  unfold mpd_store_Z.
  Intros data.
  symmetry in H0.
  apply Zlength_nil_inv in H0.
  subst data.
  rewrite list_to_Z_nil in H.
  entailer!.
Qed.

Lemma mpd_store_Z_compact_pos : forall ptr n size,
  size > 0 ->
  mpd_store_Z_compact ptr n size |-- “ n > 0 ”.
Proof.
  intros.
  unfold mpd_store_Z_compact , mpd_store_list.
  Intros data.
  subst size. destruct H0 as [? [? ?]].
  subst n.
  entailer!.
  destruct data as [|a data].
  - rewrite Zlength_nil in *.
    lia.
  - pose proof (list_to_Z_compact_bound (a :: data) H2 H1) as Hcompact.
    pose proof (Zlength_nonneg data) as Hlen.
    rewrite Zlength_cons in Hcompact.
    replace (Z.succ (Zlength data) - 1) with (Zlength data) in Hcompact by lia.
    pose proof (Z.pow_pos_nonneg Base (Zlength data) Base_pos ltac:(lia)).
    nia.
Qed.

Lemma mpd_store_Z_compact_zero : forall ptr n,
  mpd_store_Z_compact ptr n 0 |-- “ n = 0 ”.
Proof.
  intros.
  unfold mpd_store_Z_compact.
  Intros data.
  symmetry in H0.
  apply Zlength_nil_inv in H0.
  subst data.
  rewrite list_to_Z_nil in H.
  entailer!.
Qed.


Lemma mpd_store_Z_compact_align4 : forall ptr n size,
  mpd_store_Z_compact ptr n size |-- store_align4_n size.
Proof.
  intros.
  unfold mpd_store_Z_compact , mpd_store_list.
  Intros data.
  rewrite <- H0.
  sep_apply uint_array_full_align4.
  entailer!.
Qed.

Lemma mpd_store_Z_compact_range : forall ptr n size,
  mpd_store_Z_compact ptr n size |-- “ 0 <= size <= Int.max_unsigned /4 + 1 ”.
Proof.
  intros.
  sep_apply mpd_store_Z_compact_align4.
  prop_apply store_align4_n_valid.
  Intros.
  unfold store_align4_n.
  Intros l.
  pose proof (Zlength_nonneg l).
  entailer!.
Qed.

(* Convert a number to its digit list representation *)
Fixpoint Z_to_list (n: Z) (size: nat) : list Z :=
  match size with
  | O => nil
  | S size' => (n mod Base) :: Z_to_list (n / Base) size'
  end.

Lemma Z_to_list_length : forall n size,
  Zlength (Z_to_list n size) = Z.of_nat size.
Proof.
  intros. revert n.
  induction size; simpl.
  - rewrite Zlength_nil. lia.
  - intros. rewrite Zlength_cons. rewrite IHsize. lia.
Qed.

Lemma Z_to_list_within_bound : forall n size,
  0 <= n ->
  list_within_bound (Z_to_list n size).
Proof.
  intros.
  revert n H.
  induction size; intros; simpl.
  - tauto.
  - split.
    + pose proof (Z.mod_pos_bound n Base Base_pos). lia.
    + apply IHsize. apply Z_div_pos; lia.
Qed.

Lemma Z_to_list_correct : forall n size,
  0 <= n ->
  list_to_Z (Z_to_list n size) = n mod (Base ^ (Z.of_nat size)).
Proof.
  intros.
  revert n H.
  induction size; intros.
  - change (Z_to_list n 0) with (@nil Z).
    rewrite list_to_Z_nil.
    rewrite Z.mod_1_r. lia.
  - change (Z_to_list n (S size)) with ((n mod Base) :: Z_to_list (n / Base) size).
    rewrite list_to_Z_cons.
  change (n mod Z.pow_pos Base (Pos.of_succ_nat size)) with (n mod Base ^ Z.of_nat (S size)).
   rewrite IHsize; [ | apply Z_div_pos; lia].
    pose proof Nat2Z.inj_succ size. rewrite H0.
    pose proof Z.pow_succ_r Base (Z.of_nat size) ltac:(lia).
    rewrite H1.
    rewrite Z.rem_mul_r.
    + lia.
    + lia.
    + lia.
Qed.

Lemma Z_to_list_exact : forall n size,
  0 <= n < Base ^ (Z.of_nat size) ->
  list_to_Z (Z_to_list n size) = n.
Proof.
  intros.
  rewrite Z_to_list_correct; try lia.
  rewrite Z.mod_small; lia.
Qed.

Lemma Z_to_list_last : forall n size,
  0 <= n < Base ^ (Z.of_nat size) ->
  Base ^ (Z.of_nat size - 1) <= n ->
  last (Z_to_list n size) 1 >= 1.
Proof.
  intros.
  revert n H H0.
  induction size; intros.
  - simpl. lia.
  - simpl. pose proof IHsize (n / Base).
  assert (Hcond1: 0 <= n / Base < Base ^ Z.of_nat size).
  {
    split.
    - apply Z_div_pos; lia.
    - apply Z.div_lt_upper_bound; try lia.
    rewrite <- Z.pow_succ_r; try lia.
  }
  assert (Hcond2: Base ^ (Z.of_nat size - 1) <= n / Base). {
    apply Z.div_le_lower_bound; try lia.
    destruct (Nat.eq_dec size 0) as [Hsize0 | Hsize_pos].
    -- subst. simpl in *. lia.
    -- rewrite <- Z.pow_succ_r; try lia.
      replace (Z.succ (Z.of_nat size - 1)) with (Z.of_nat size) by lia.
      (* 现在目标是 Base ^ Z.of_nat size <= n *)
      (* 从 H0: Base ^ (Z.of_nat (S size) - 1) <= n *)
      replace (Z.of_nat (S size) - 1) with (Z.of_nat size) in H0 by lia.
      exact H0. 
  }
  pose proof H1 Hcond1 Hcond2.
  destruct size.
    + simpl.
      rewrite Nat2Z.inj_succ in H, H0.
      simpl in H, H0.
      pose proof (Z.mod_pos_bound n Base Base_pos).
      pose proof Z.mod_small. rewrite H4; lia.
    + remember (S size) as size'.
      assert (Z_to_list (n / Base) size' <> nil). {
        subst size'.
        simpl. congruence.
      }
      destruct (Z_to_list (n / Base) size').
      -- contradiction.
      -- lia. 
Qed.

(* Simpler lemma: if we know the exact bounds, the compact representation exists *)
Lemma is_compact_Z_from_bounds : forall n size,
  size >= 0 ->
  (size = 0 /\ n = 0) \/ (size > 0 /\ Base ^ (size - 1) <= n < Base ^ size) ->
  is_compact_Z n size.
Proof.
  intros.
  destruct H0.
  - (* size = 0, n = 0 case *)
    destruct H0; subst.
    unfold is_compact_Z.
    exists nil.
    rewrite list_to_Z_nil.
    rewrite Zlength_nil.
    simpl.
    repeat split; lia.
  - (* size > 0, proper bounds *)
    destruct H0 as [Hsize [Hlo Hhi]].
    unfold is_compact_Z.
    destruct (Z.to_nat size) eqn:Hnat.
    + lia.
    + exists (Z_to_list n (S n0)).
      repeat split.
      * rewrite Z_to_list_exact; try lia.
        replace (Z.of_nat (S n0)) with size by lia. lia.
      * rewrite Z_to_list_length. lia.
      * apply Z.mod_pos_bound. lia.
      * apply Z.mod_pos_bound. lia.
      * apply Z_to_list_within_bound. apply Z_div_pos; lia.
      * apply Z_to_list_last.
        -- replace (Z.of_nat (S n0)) with size by lia. lia.
        -- replace (Z.of_nat (S n0)) with size by lia. lia.
Qed.

(* Compact representation properties from is_compact_Z *)
Lemma is_compact_Z_bounds : forall n size,
  is_compact_Z n size ->
  size >= 0 /\
  ((size = 0 /\ n = 0) \/ (size > 0 /\ Base ^ (size - 1) <= n < Base ^ size)).
Proof.
  intros.
  unfold is_compact_Z in H.
  destruct H as [data [Heq [Hlen [Hbound Hlast]]]].
  split.
  - pose proof (Zlength_nonneg data). lia.
  - destruct data.
    + left. rewrite Zlength_nil in Hlen.
     rewrite list_to_Z_nil in Heq.
     split; lia.
    + right.
      simpl in Hlast.
      pose proof (list_to_Z_compact_bound (z :: data) Hbound Hlast).
      rewrite Zlength_cons in Hlen.
      pose proof (Zlength_nonneg data).
      split; try lia.
      rewrite Zlength_cons in H.
      subst. lia.
Qed.

Lemma is_compact_Z_add_helper_1 : forall n m size,
  Base>2 ->
  size >= 0 ->
  0 <= n -> 0 <= m ->
  Base ^ size <= n + m < 2 * Base ^ size ->
  is_compact_Z (n + m) (size + 1).
Proof.
  intros.
  apply is_compact_Z_from_bounds; try lia.
  right.
  split; try lia.
  split.
  - replace (size + 1 - 1) with size by lia. lia.
  - rewrite Aux.Zpow_add_1; try lia.
    rewrite Z.mul_comm.
    pose proof Z.pow_pos_nonneg.
    nia.
Qed.

End Internal.


Definition UINT_MOD := (4294967296).

Theorem UINT_MOD_pos : 0 < UINT_MOD.
Proof.
  unfold UINT_MOD.
  lia.
Qed.

Lemma is_compact_Z_exists_nonneg :
  forall n, 0 <= n -> exists size, is_compact_Z UINT_MOD n size.
Proof.
  intros n Hn.
  destruct (Z.eq_dec n 0) as [Hzero | Hnz].
  - subst n. exists 0.
    apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos); [lia | left; lia].
  - assert (Hpos : 0 < n) by lia.
    set (lg := Z.log2 n).
    set (size := lg / 32 + 1).
    exists size.
    apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos).
    + subst size lg. pose proof (Z.log2_nonneg n).
      pose proof (Z.div_pos (Z.log2 n) 32 ltac:(lia) ltac:(lia)).
      lia.
    + right. split.
      * subst size lg. pose proof (Z.log2_nonneg n).
        pose proof (Z.div_pos (Z.log2 n) 32 ltac:(lia) ltac:(lia)).
        lia.
      * pose proof (Z.log2_spec n Hpos) as [Hlo Hhi].
        assert (Hlg_nonneg : 0 <= lg) by (subst lg; apply Z.log2_nonneg).
        pose proof (Z.div_mod lg 32 ltac:(lia)) as Hdivmod.
        assert (Hrem : 0 <= lg mod 32 < 32) by (apply Z.mod_pos_bound; lia).
        split.
        -- change UINT_MOD with (2 ^ 32).
           rewrite <- Z.pow_mul_r by lia.
           apply Z.le_trans with (m := 2 ^ lg).
           ++ apply Z.pow_le_mono_r; lia.
           ++ exact Hlo.
        -- change UINT_MOD with (2 ^ 32).
           rewrite <- Z.pow_mul_r by lia.
           apply Z.lt_le_trans with (m := 2 ^ (lg + 1)).
           ++ replace (lg + 1) with (Z.succ lg) by lia.
              exact Hhi.
           ++ apply Z.pow_le_mono_r; lia.
Qed.

(* same_sign: two integers have the same sign *)
Definition same_sign (a b: Z) : Prop :=
  (a >= 0 /\ b >= 0) \/ (a < 0 /\ b < 0).

Definition same_sign_or_zero (a b: Z) : Prop :=
  a = 0 \/ same_sign a b.

Lemma mpz_init2_alloc_round : forall bits alloc,
  bits = alloc * 32 ->
  alloc > 0 ->
  alloc <= 2147483647 ->
  signed_last_nbits (1 + unsigned_last_nbits (bits - 1) 64 / 32) 32 = alloc.
Proof.
  intros bits alloc Hbits Hpos Hmax.
  subst bits.
  rewrite unsigned_last_nbits_eq.
  2:{ change (2 ^ 64) with 18446744073709551616; nia. }
  replace (alloc * 32 - 1) with ((alloc - 1) * 32 + 31) by ring.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by lia.
  replace (1 + (alloc - 1 + 0)) with alloc by ring.
  rewrite signed_last_nbits_eq; lia.
Qed.

Lemma mpz_init2_alloc_round_quot : forall bits alloc,
  bits = alloc * 32 ->
  alloc > 0 ->
  alloc <= 2147483647 ->
  signed_last_nbits (1 + unsigned_last_nbits (bits - 1) 64 ÷ 32) 32 = alloc.
Proof.
  intros bits alloc Hbits Hpos Hmax.
  subst bits.
  rewrite unsigned_last_nbits_eq.
  2:{ change (2 ^ 64) with 18446744073709551616; nia. }
  rewrite Z.quot_div_nonneg by nia.
  replace (alloc * 32 - 1) with ((alloc - 1) * 32 + 31) by ring.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by lia.
  replace (1 + (alloc - 1 + 0)) with alloc by ring.
  rewrite signed_last_nbits_eq; lia.
Qed.

Lemma same_sign_refl : forall a, same_sign a a.
Proof.
  intros. unfold same_sign. lia.
Qed.

Lemma same_sign_sym : forall a b, same_sign a b -> same_sign b a.
Proof.
  intros. unfold same_sign in *. lia.
Qed.

Record bigint_ent: Type := {
    cap: Z;
    data: list Z;
    sign: Prop;
}.

Definition store_Z (x: addr) (n: Z): Assertion :=
  EX (ptr: addr) (size cap: Z),
    “ Zabs size <= cap ” && 
    “ same_sign n size ” && mpd_store_Z_compact UINT_MOD ptr (Z.abs n) (Z.abs size) ** UIntArray.undef_seg ptr (Z.abs size) cap **
    &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
    &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr.

Definition store_Z_dummy (x dummy_ptr: addr): Assertion :=
  &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> 0 **
  &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> 0 **
  &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> dummy_ptr.

Definition mpd_read0_data (data: list Z): list Z :=
  match data with
  | nil => 0 :: nil
  | _ => data
  end.

Definition normalized_size_read0_guard (n: Z) (data: list Z): Prop :=
  n > 0 \/ Znth 0 data 0 = 0.

Definition Zmax (x y: Z): Z := Z.max x y.

Definition mpd_store_Z_read0 (ptr: addr) (n size: Z): Assertion :=
  EX data,
    “ list_to_Z UINT_MOD data = n /\
      list_within_bound UINT_MOD data /\
      size = Zlength data ” &&
    UIntArray.full ptr (Zmax size 1) (mpd_read0_data data).

Definition mpd_store_Z_compact_read0 (ptr: addr) (n size: Z): Assertion :=
  EX data,
    “ list_to_Z UINT_MOD data = n /\
      last data 1 >= 1 /\
      list_within_bound UINT_MOD data /\
      size = Zlength data ” &&
    UIntArray.full ptr (Zmax size 1) (mpd_read0_data data).

Definition store_Z_read0 (x: addr) (n: Z): Assertion :=
  EX (ptr: addr) (size cap: Z),
    “ Zabs size <= cap ” &&
    “ same_sign n size ” &&
    mpd_store_Z_compact_read0 ptr (Z.abs n) (Z.abs size) **
    UIntArray.undef_seg ptr (Zmax (Z.abs size) 1) cap **
    &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
    &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr.

Definition store_Z_remain_size (x: addr) (n: Z) (real_size: Z): Assertion :=
  EX (ptr: addr) (old_size cap: Z),
    “ Zabs real_size <= cap ” && 
    “ same_sign n real_size ” && mpd_store_Z_compact UINT_MOD ptr (Z.abs n) (Z.abs real_size) ** UIntArray.undef_seg ptr (Z.abs real_size) cap **
    &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> old_size **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
    &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr.

Definition store_Z_with_old_size (x: addr) (old_n n real_size: Z): Assertion :=
  EX (ptr: addr) (old_size cap: Z),
    “ Zabs old_size <= cap ” &&
    “ Zabs real_size <= cap ” &&
    “ same_sign old_n old_size ” &&
    “ same_sign n real_size ” &&
    mpd_store_Z_compact UINT_MOD ptr (Z.abs n) (Z.abs real_size) **
    UIntArray.undef_seg ptr (Z.abs real_size) cap **
    &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> old_size **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap **
    &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr.

Lemma mpd_store_Z_bound: forall ptr n size,
  mpd_store_Z UINT_MOD ptr n size |-- 
  “ 0 <= n < UINT_MOD ^ size ”.
Proof.
  intros.
  unfold mpd_store_Z.
  Intros data.
  pose proof list_to_Z_bound UINT_MOD.
  unfold UINT_MOD in  H1,H.
  pose proof H1 ltac:(lia) as H1.
  pose proof H1 data as H1. destruct H.
  pose proof H1 H2 as H1.
  subst. 
  entailer!.
Qed.

Lemma mpd_store_Z_compact_bound: forall ptr n size,
  mpd_store_Z_compact UINT_MOD ptr n size |--
  “ 0 <= n < UINT_MOD ^ size ”.
Proof.
  intros.
  unfold mpd_store_Z_compact.
  Intros data.
  pose proof list_to_Z_bound UINT_MOD.
  unfold UINT_MOD in  H1,H.
  pose proof H1 ltac:(lia) as H1.
  pose proof H1 data as H1. destruct H.
  destruct H2.
  pose proof H1 H3 as H1.
  subst. 
  entailer!.
Qed.

Lemma mpn_add_ret_0_or_1: forall ap bp rp val_a val_b val_r an bn ret_val,
  val_r + ret_val * UINT_MOD ^ an = val_a + val_b -> an >= bn ->
  ( mpd_store_Z UINT_MOD ap val_a an ) **
  ( mpd_store_Z UINT_MOD bp val_b bn ) **
  ( mpd_store_Z UINT_MOD rp val_r an ) |--
    “ ret_val = 0 \/ ret_val = 1 ”.
Proof.
  intros.
  prop_apply mpd_store_Z_bound.
  prop_apply mpd_store_Z_bound.
  Intros.
  prop_apply (mpd_store_Z_bound rp val_r an).
  Intros.
  entailer!.
  assert (UINT_MOD ^ an >= UINT_MOD ^ bn).
  { unfold UINT_MOD in *. 
  pose proof Z.pow_le_mono_r 4294967296 bn an as Hpow.
  pose proof Hpow ltac:(lia) ltac:(lia) as Hpow.
  lia. }
  assert (0 <= val_b < UINT_MOD ^ an) by lia.
  clear H2.
  clear H4.
  assert ( ret_val < 2).
  { destruct (Z_lt_le_dec ret_val 2) as [? | Hge2]; auto.
    exfalso.
    assert (val_a+val_b < 2 * UINT_MOD ^ an) by lia.
    assert (ret_val * UINT_MOD ^an >= 2 * UINT_MOD ^an).
    { pose proof Z.mul_le_mono_nonneg_r 2 ret_val (UINT_MOD ^ an).
    lia. }
    assert (val_r + ret_val * UINT_MOD ^ an >= 2 * UINT_MOD ^ an) by lia.
    assert (val_r + ret_val * UINT_MOD ^ an > val_a + val_b) by lia.
    lia.
  }
  assert (ret_val >=0).
  {
      destruct (Z_lt_le_dec ret_val 0) as [Hneg | ?]; auto.
      exfalso.
      - assert (ret_val * UINT_MOD ^ an <= -1 * UINT_MOD ^ an).
      {
          pose proof Z.mul_le_mono_nonneg_r ret_val (-1) (UINT_MOD ^ an).
          unfold UINT_MOD in H4 at 1.
          pose proof H4 ltac:(lia) ltac:(lia) as H4.
          lia.
      }
      assert (val_r + ret_val * UINT_MOD ^ an < 0) by lia.
      lia.
      -lia.
  }
  lia.
Qed.

Lemma mpn_add_ret_0_or_1_compact: forall rp val_a val_b val_r an bn ret_val,
  val_r + ret_val * UINT_MOD ^ an = val_a + val_b ->
  an >= bn ->
  is_compact_Z UINT_MOD val_a an ->
  is_compact_Z UINT_MOD val_b bn ->
  (mpd_store_Z UINT_MOD rp val_r an) |--
    “ ret_val = 0 \/ ret_val = 1 ”.
Proof.
  intros.
  prop_apply (mpd_store_Z_bound rp val_r an).
  Intros.
  apply derivable1s_coq_prop_r.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos val_a an H1) as [Han Hval_a].
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos val_b bn H2) as [Hbn Hval_b].
  assert (0 <= val_a < UINT_MOD ^ an).
  { destruct Hval_a as [[? ?] | [? [? ?]]]; unfold UINT_MOD in *; lia. }
  assert (0 <= val_b < UINT_MOD ^ bn).
  { destruct Hval_b as [[? ?] | [? [? ?]]]; unfold UINT_MOD in *; lia. }
  assert (UINT_MOD ^ bn <= UINT_MOD ^ an).
  { apply Z.pow_le_mono_r; unfold UINT_MOD; lia. }
  assert (0 <= val_b < UINT_MOD ^ an) by lia.
  assert (ret_val < 2).
  { destruct (Z_lt_le_dec ret_val 2) as [? | Hge2]; auto.
    exfalso.
    assert (0 < UINT_MOD ^ an) by (apply Z.pow_pos_nonneg; unfold UINT_MOD; lia).
    assert (val_a + val_b < 2 * UINT_MOD ^ an) by lia.
    pose proof (Z.mul_le_mono_nonneg_r 2 ret_val (UINT_MOD ^ an)).
    assert (ret_val * UINT_MOD ^ an >= 2 * UINT_MOD ^ an) by lia.
    lia. }
  assert (ret_val >= 0).
  { destruct (Z_lt_le_dec ret_val 0) as [Hneg | ?].
    - exfalso.
      assert (0 < UINT_MOD ^ an) by (apply Z.pow_pos_nonneg; unfold UINT_MOD; lia).
      pose proof (Z.mul_le_mono_nonneg_r ret_val (-1) (UINT_MOD ^ an)).
      assert (ret_val * UINT_MOD ^ an <= -1 * UINT_MOD ^ an) by lia.
      lia.
    - lia. }
  lia.
Qed.

Lemma mpn_sub_ret_0: forall ap bp rp val_a val_b val_r an bn rn ret_val ,
  val_r - ret_val * UINT_MOD ^ an = val_a - val_b -> 
  an >= bn ->
  bn >= 0 ->
  val_a >= val_b ->
  rn <= an ->
  ( mpd_store_Z UINT_MOD ap val_a an ) **
  ( mpd_store_Z UINT_MOD bp val_b bn ) **
  ( mpd_store_Z_compact UINT_MOD rp val_r rn ) |--
    “ ret_val = 0 ”.
Proof.
  intros.
  prop_apply mpd_store_Z_bound.
  prop_apply mpd_store_Z_bound.
  Intros.
  prop_apply (mpd_store_Z_compact_bound rp val_r rn).
  Intros.
  entailer!.
  assert (UINT_MOD ^ an >= UINT_MOD ^ bn).
  { unfold UINT_MOD in *. 
  pose proof Z.pow_le_mono_r 4294967296 bn an as Hpow.
  pose proof Hpow ltac:(lia) ltac:(lia) as Hpow.
  lia. }
  assert (0 <= val_b < UINT_MOD ^ an) by lia.
  assert (0 <= val_r < UINT_MOD ^ rn) by lia.
  assert (0 <= val_a - val_b < UINT_MOD ^ an) by lia.
  assert (UINT_MOD ^ rn <= UINT_MOD ^ an).
  {
    unfold UINT_MOD in *. 
    pose proof Z.pow_le_mono_r 4294967296 rn an as Hpow.
    pose proof Hpow ltac:(lia) ltac:(lia) as Hpow. lia.
  }
  assert (0 <= val_r < UINT_MOD ^ an) by lia.
  clear H6 H7 H9 H11 H5.
  assert ( ret_val < 1).
  { destruct (Z_lt_le_dec ret_val 1) as [? | Hge1]; auto.
    exfalso.
    assert (-ret_val * UINT_MOD ^an <= (-1) * UINT_MOD ^an).
    { pose proof Z.mul_le_mono_nonneg_r (-ret_val) (-1) (UINT_MOD ^ an). unfold UINT_MOD in H5 at 1.
    pose proof H5 ltac:(lia) ltac:(lia) as H5. lia.  }
    assert (val_r - ret_val * UINT_MOD ^ an <= 0) by lia.
    lia.
  }
  assert (ret_val >= 0).
  {
      destruct (Z_lt_le_dec ret_val 0) as [Hneg | ?]; auto.
      exfalso.
      - assert (-ret_val * UINT_MOD ^ an >=   UINT_MOD ^ an).
      {
          pose proof Z.mul_le_mono_nonneg_r 1 (-ret_val) (UINT_MOD ^ an).
          unfold UINT_MOD in H6 at 1.
          pose proof H6 ltac:(lia) ltac:(lia) as H6.
          rewrite Z.mul_1_l in H6.
          pose proof Z.le_ge (UINT_MOD ^ an) (- ret_val * UINT_MOD ^ an).
          lia.
      }
      assert (val_r - ret_val * UINT_MOD ^ an > UINT_MOD ^ an) by lia.
      lia.
      -lia.
  }
  lia.
Qed.

Lemma mpn_sub_ret_0_compact: forall rp val_a val_b val_r an bn rn ret_val,
  val_r - ret_val * UINT_MOD ^ an = val_a - val_b ->
  an >= bn ->
  val_a >= val_b ->
  rn <= an ->
  is_compact_Z UINT_MOD val_a an ->
  is_compact_Z UINT_MOD val_b bn ->
  mpd_store_Z_compact UINT_MOD rp val_r rn |--
    “ ret_val = 0 ”.
Proof.
  intros.
  prop_apply (mpd_store_Z_compact_bound rp val_r rn).
  Intros.
  apply derivable1s_coq_prop_r.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos val_a an H3) as [Han Hval_a].
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos val_b bn H4) as [Hbn Hval_b].
  assert (0 <= val_a < UINT_MOD ^ an).
  { destruct Hval_a as [[? ?] | [? [? ?]]]; unfold UINT_MOD in *; lia. }
  assert (0 <= val_b < UINT_MOD ^ bn).
  { destruct Hval_b as [[? ?] | [? [? ?]]]; unfold UINT_MOD in *; lia. }
  assert (UINT_MOD ^ bn <= UINT_MOD ^ an).
  { apply Z.pow_le_mono_r; unfold UINT_MOD; lia. }
  assert (0 <= val_b < UINT_MOD ^ an) by lia.
  assert (0 <= val_a - val_b < UINT_MOD ^ an) by lia.
  assert (UINT_MOD ^ rn <= UINT_MOD ^ an).
  { apply Z.pow_le_mono_r; unfold UINT_MOD; lia. }
  assert (0 <= val_r < UINT_MOD ^ an) by lia.
  assert (ret_val < 1).
  { destruct (Z_lt_le_dec ret_val 1) as [Hlt | Hge1].
    - lia.
    - exfalso.
    assert (0 < UINT_MOD ^ an) by (apply Z.pow_pos_nonneg; unfold UINT_MOD; lia).
    assert (-ret_val * UINT_MOD ^ an <= -1 * UINT_MOD ^ an).
    { pose proof (Z.mul_le_mono_nonneg_r (- ret_val) (-1) (UINT_MOD ^ an)).
      lia. }
    assert (val_r - ret_val * UINT_MOD ^ an <= 0) by lia.
    lia. }
  assert (ret_val >= 0).
  { destruct (Z_lt_le_dec ret_val 0) as [Hneg | Hnonneg].
    - exfalso.
    assert (0 < UINT_MOD ^ an) by (apply Z.pow_pos_nonneg; unfold UINT_MOD; lia).
    assert (-ret_val * UINT_MOD ^ an >= UINT_MOD ^ an).
    { pose proof (Z.mul_le_mono_nonneg_r 1 (- ret_val) (UINT_MOD ^ an)).
      lia. }
    assert (val_r - ret_val * UINT_MOD ^ an >= UINT_MOD ^ an) by lia.
    lia.
    - lia. }
  lia.
Qed.

Lemma mpd_store_Z_to_mpd_store_Z_compact: forall ptr n size,
    is_compact_Z UINT_MOD n size ->
    (mpd_store_Z UINT_MOD ptr n size) |--
    (mpd_store_Z_compact UINT_MOD ptr n size).
Proof.
    intros.
    unfold mpd_store_Z, mpd_store_Z_compact.
    Intros data.
    Exists data. entailer!.
    unfold is_compact_Z in H.
    destruct H.
    pose proof list_to_Z_reverse_same_length_injection UINT_MOD.
    unfold UINT_MOD in H2 at 1.
    pose proof H2 ltac:(lia) data x as H2.
    destruct H.
    rewrite H in H2.
    pose proof H2 ltac:(lia) as H2.
    destruct H0.
    destruct H3.
    destruct H5.
    pose proof H2 H4 H5 ltac:(lia) as H2.
    rewrite H2.
    tauto.
Qed.

Lemma is_compact_Z_add_0: forall n m size1 size2,
  is_compact_Z UINT_MOD n size1 ->
  is_compact_Z UINT_MOD m size2 ->
  n + m < UINT_MOD ^ (Z.max size1 size2) ->
  is_compact_Z UINT_MOD (n + m) (Z.max size1 size2).
Proof.
  intros n m size1 size2 H1 H2 Hbound.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos n size1 H1) as [Hs1 Hn].
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos m size2 H2) as [Hs2 Hm].
  apply is_compact_Z_from_bounds; unfold UINT_MOD; try lia.
  destruct Hn as [[Hn1 Hn2] | [Hn1 [Hn2 Hn3]]];
  destruct Hm as [[Hm1 Hm2] | [Hm1 [Hm2 Hm3]]].
  - (* size1 = 0, n = 0, size2 = 0, m = 0 *)
    left. subst. simpl. lia.
  - (* size1 = 0, n = 0, size2 > 0 *)
    subst n. rewrite Z.add_0_l.
    right. split.
    + rewrite Z.max_r; lia.
    + rewrite Z.max_r; try lia.
      split; unfold UINT_MOD in *; try lia. 
  - (* size1 > 0, size2 = 0, m = 0 *)
    subst m. rewrite Z.add_0_r.
    right. split.
    + rewrite Z.max_l; lia.
    + rewrite Z.max_l; try lia. unfold UINT_MOD in *.
      split; try lia.
  - (* size1 > 0, size2 > 0 *)
    right. split.
    + lia.
    + split.
      * destruct (Z.max_spec size1 size2) as [[Hle Heq] | [Hlt Heq]]; rewrite Heq.
        -- assert (UINT_MOD ^ (size2 - 1) <= m) by lia.
           assert (0 <= n) by (unfold UINT_MOD in *; lia).
           unfold UINT_MOD in *.
           lia.
        -- assert (UINT_MOD ^ (size1 - 1) <= n) by lia.
           unfold UINT_MOD in *; lia.
      * unfold UINT_MOD in *. lia.
Qed.


Lemma is_compact_Z_add_1: forall n m size1 size2,
  is_compact_Z UINT_MOD n size1 ->
  is_compact_Z UINT_MOD m size2 ->
  n + m >= UINT_MOD ^ (Z.max size1 size2) ->
  n + m < 2 * UINT_MOD ^ (Z.max size1 size2) ->
  is_compact_Z UINT_MOD (n + m) ((Z.max size1 size2)+1).
Proof.
  intros n m size1 size2 H1 H2 Hlo Hhi.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos n size1 H1) as [Hs1 Hn].
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos m size2 H2) as [Hs2 Hm].
  apply is_compact_Z_add_helper_1; unfold UINT_MOD in *; try lia.
Qed.

Lemma mpd_store_Z_to_is_compact_Z: forall ptr n size,
  (mpd_store_Z_compact UINT_MOD ptr n size) |--
  “ is_compact_Z UINT_MOD n size ”.
Proof.
  intros.
  unfold mpd_store_Z_compact, is_compact_Z.
  Intros data.
  entailer!. exists data.
  rewrite H0. tauto.
Qed.

Lemma mpd_store_Z_compact_to_mpd_store_Z: 
forall (ptr: Z) (size: Z) (l: Z) ,
  mpd_store_Z_compact UINT_MOD ptr l size  |--
  mpd_store_Z UINT_MOD ptr l size .
Proof.
  intros.
  unfold mpd_store_Z_compact, mpd_store_Z. Intros data. Exists data. entailer!.
Qed.

Lemma mpd_store_Z_compact_mono_size: forall ap bp n m size1 size2,
  n>m ->
  mpd_store_Z_compact UINT_MOD ap n size1 **
  mpd_store_Z_compact UINT_MOD bp m size2 |--
  “ size1 >= size2 ”.
Proof.
  intros.
  unfold mpd_store_Z_compact.
  Intros data_a data_b.
  entailer!.
  subst size1 size2.
  destruct H0 as [Hn [Hlast_a Hbound_a]].
  destruct H2 as [Hm [Hlast_b Hbound_b]].
  subst n m.
  (* data_b = nil 的情况 *)
  destruct data_b as [ | z data_b'].
  - rewrite Zlength_nil.
    pose proof (Zlength_nonneg data_a). lia.
  - (* data_b 非空，使用 compact bound *)
    pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos (z :: data_b') Hbound_b Hlast_b) as Hb.
    pose proof (list_to_Z_pos UINT_MOD UINT_MOD_pos data_a Hbound_a) as Hpos_a.
    (* data_a 也必须非空，因为 list_to_Z data_a > list_to_Z (z::data_b') > 0 *)
    destruct data_a as [ | y data_a'].
    + rewrite list_to_Z_nil in H.
      rewrite Zlength_cons in Hb.
      replace (Z.succ (Zlength data_b') - 1) with (Zlength data_b') in Hb by lia.
      pose proof (Zlength_nonneg data_b') as Hlen_b.
      pose proof (Z.pow_pos_nonneg UINT_MOD (Zlength data_b') UINT_MOD_pos ltac:(lia)).
      lia. (* 矛盾：list_to_Z nil = 0 *)
    + pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos (y :: data_a') Hbound_a Hlast_a) as Ha.
      (* 反证：如果 Zlength data_a < Zlength data_b *)
      destruct (Z_lt_dec (Zlength (y :: data_a')) (Zlength (z :: data_b'))).
      * exfalso.
        (* n < UINT_MOD^size1 <= UINT_MOD^(size2-1) <= m，矛盾 *)
        assert (UINT_MOD ^ (Zlength (y :: data_a')) <= UINT_MOD ^ (Zlength (z :: data_b') - 1)).
        { apply Z.pow_le_mono_r.
          - unfold UINT_MOD. lia.
          - pose proof (Zlength_nonneg data_a').
            pose proof (Zlength_nonneg data_b').
            rewrite !Zlength_cons in *. lia. }
        lia.
      * lia.
Qed.


Lemma lxor_negative_implies_opposite_signs_simple:
  forall x y : Z,
    Z.lxor x y < 0 ->
    (x < 0 /\ y >= 0) \/ (x >= 0 /\ y < 0).
Proof.
    intros x y Hlxor.
    destruct (Z_lt_ge_dec x 0) as [Hx_neg | Hx_nonneg].
    -   left.
        split.
        * lia.
        * destruct (Z_lt_ge_dec y 0) as [Hy_neg | Hy_nonneg].
        + 
        exfalso.
        assert (H: 0 <= Z.lxor x y).
        {
            rewrite Z.lxor_nonneg.
            split; intro; lia.
        }
        lia.
        + 
        exact Hy_nonneg.
    -   right.
        split; [lia| ].
        destruct (Z_lt_ge_dec y 0) as [Hy_neg | Hy_nonneg].
        + 
        exact Hy_neg.
        + 
        exfalso.
        assert (H: 0 <= Z.lxor x y).
        {
            rewrite Z.lxor_nonneg.
            split; intro; lia.
        }
        lia.
Qed.

Lemma lxor_nonneg_implies_same_sign:
  forall x y : Z,
    Z.lxor x y >= 0 ->
    (x >= 0 /\ y >= 0) \/ (x < 0 /\ y < 0).
Proof.
  intros x y Hlxor.
  pose proof (proj1 (Z.lxor_nonneg x y) ltac:(lia)) as Hsame.
  destruct (Z_lt_ge_dec x 0); destruct (Z_lt_ge_dec y 0);
    try (left; lia); try (right; lia).
Qed.

Lemma store_Z_remain_size_2_same_sign: forall x n real_size,
  store_Z_remain_size x n real_size |--
  “ same_sign n real_size ”.
Proof.
  intros.
  unfold store_Z_remain_size, same_sign.
  Intros ptr old_size cap.
  entailer!.
Qed.

Lemma store_Z_with_old_size_2_same_sign: forall x old_n n real_size,
  store_Z_with_old_size x old_n n real_size |--
  “ same_sign n real_size ”.
Proof.
  intros.
  unfold store_Z_with_old_size, same_sign.
  Intros ptr old_size cap.
  entailer!.
Qed.

Lemma store_Z_with_old_size_int_range : forall x old_v v s,
  store_Z_with_old_size x old_v v s |--
    “ INT_MIN < s <= INT_MAX ”.
Proof.
  intros.
  unfold store_Z_with_old_size.
  Intros ptr old_size cap.
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD ptr (Zabs v) (Zabs s)).
  Intros.
  match goal with
  | H : 0 <= Zabs s <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H;
      pose proof (Z.abs_le s 1073741824)
  end.
  entailer!.
Qed.
(* Project/minigmp1 merged helper lemmas for mpz add/sub proofs. *)
Lemma store_Z_remain_size_int_range : forall x v s,
  store_Z_remain_size x v s |--
    “ INT_MIN < s <= INT_MAX ”.
Proof.
  intros.
  unfold store_Z_remain_size.
  Intros ptr old_size cap.
  prop_apply_p (mpd_store_Z_compact_range UINT_MOD ptr (Zabs v) (Zabs s)).
  Intros.
  match goal with
  | H : 0 <= Zabs s <= _ |- _ =>
      change Int.max_unsigned with 4294967295 in H;
      assert (4294967295 / 4 + 1 = 1073741824) as Hcalc by reflexivity;
      rewrite Hcalc in H;
      pose proof (Z.abs_le s 1073741824)
  end.
    entailer!.
Qed.

Lemma store_Z_store_Z_neq : forall x y vx vy,
  store_Z x vx ** store_Z y vy |-- “ x <> y ”.
Proof.
  intros.
  unfold store_Z.
  Intros ptr1 size1 cap1 ptr2 size2 cap2.
  destruct (Z.eq_dec x y) as [Heq | Hneq].
  - subst y.
    sep_apply (dup_store_int (&(x # "__mpz_struct" ->ₛ "_mp_size")) size1 size2).
    pre_process.
  - entailer!.
Qed.

Lemma same_sign_opp_compact_abs : forall a b,
  same_sign a b ->
  is_compact_Z UINT_MOD (Zabs a) (Zabs b) ->
  same_sign (- a) (- b).
Proof.
  intros a b H Hcompact.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos (Zabs a) (Zabs b) Hcompact)
    as [_ Hbounds].
  unfold same_sign in *.
  destruct H as [[Ha Hb] | [Ha Hb]].
  - destruct Hbounds as [[Hsize Hzero] | [Hsize Hbound]].
    + left. lia.
    + right.
      pose proof (Z.pow_pos_nonneg UINT_MOD (Zabs b - 1) UINT_MOD_pos ltac:(lia)).
      lia.
  - left; lia.
Qed.

Lemma is_compact_Z_from_full_last:
  forall (data: list Z) size val,
    0 < size ->
    Zlength data = size ->
    list_within_bound UINT_MOD data ->
    list_to_Z UINT_MOD data = val ->
    last data 1 >= 1 ->
    is_compact_Z UINT_MOD val size.
Proof.
  intros data size val Hpos Hlen Hbound Hval Hlast.
  apply is_compact_Z_from_bounds; [unfold UINT_MOD; lia | lia |].
  right.
  split; [lia |].
  pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos data Hbound Hlast) as Hbounds.
  rewrite Hlen in Hbounds.
  rewrite Hval in Hbounds.
  exact Hbounds.
Qed.

Lemma mpd_store_Z_to_undef_full : forall ptr n size,
  mpd_store_Z UINT_MOD ptr n size |--
    UIntArray.undef_full ptr size.
Proof.
  intros.
  unfold mpd_store_Z.
  Intros data.
  subst size.
  sep_apply UIntArray.full_to_undef_full.
  entailer!.
Qed.

Lemma UIntArray_full_to_empty_mpd_store_Z_compact_undef_seg :
  forall ptr size data,
  UIntArray.full ptr size data |--
    mpd_store_Z_compact UINT_MOD ptr 0 0 **
    UIntArray.undef_seg ptr 0 size.
Proof.
  intros.
  sep_apply UIntArray.full_to_undef_full.
  sep_apply (UIntArray.undef_full_to_undef_seg ptr size).
  unfold mpd_store_Z_compact, mpd_store_list.
  Exists (@nil Z).
  rewrite UIntArray.full_empty.
  entailer!.
  simpl.
  lia.
Qed.

Lemma mpd_store_Z_compact_undef_tail_to_undef_split : forall ptr n used split high,
  0 <= used ->
  used <= high ->
  0 <= split ->
  split <= high ->
  mpd_store_Z_compact UINT_MOD ptr n used **
  UIntArray.undef_seg ptr used high |--
    “ is_compact_Z UINT_MOD n used ” &&
    UIntArray.undef_full ptr split **
    UIntArray.undef_seg ptr split high.
Proof.
  intros.
  prop_apply mpd_store_Z_to_is_compact_Z.
  Intros.
  sep_apply mpd_store_Z_compact_to_mpd_store_Z.
  sep_apply mpd_store_Z_to_undef_full.
  sep_apply UIntArray.undef_full_to_undef_seg.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg ptr 0 used high).
  sep_apply (UIntArray.undef_seg_split_to_undef_seg ptr 0 split high).
  sep_apply (UIntArray.undef_seg_to_undef_full ptr 0 split).
  replace (ptr + 0 * sizeof(UINT)) with ptr by lia.
  replace (split - 0) with split by lia.
  entailer!.
  all: lia.
Qed.

Lemma store_Z_zero_from_fields : forall x ptr old_size c old_val,
  Zabs old_size <= c -> same_sign old_val old_size ->
  &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> 0 **
  UIntArray.undef_seg ptr (Zabs old_size) c **
  mpd_store_Z_compact UINT_MOD ptr (Zabs old_val) (Zabs old_size) **
  &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr **
  &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> c
  |-- store_Z x 0.
Proof.
  intros.
  unfold store_Z.
  Exists ptr 0 c.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split ptr (Zabs old_val) (Zabs old_size) 0 c).
  unfold mpd_store_Z_compact.
  Exists (@nil Z).
  unfold mpd_store_list.
  rewrite UIntArray.undef_full_empty.
  rewrite UIntArray.full_empty.
  replace (Zabs 0) with 0 by lia.
  entailer!.
  all: try (simpl; lia).
  all: try apply same_sign_refl.
Qed.

Lemma store_Z_from_fields : forall x ptr size c z,
  Zabs size <= c -> same_sign z size ->
  &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size **
  UIntArray.undef_seg ptr (Zabs size) c **
  mpd_store_Z_compact UINT_MOD ptr (Zabs z) (Zabs size) **
  &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr **
  &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> c
  |-- store_Z x z.
Proof.
  intros.
  unfold store_Z.
  Exists ptr size c.
  entailer!.
Qed.

Lemma store_Z_from_zero_fields : forall x ptr c,
  0 <= c ->
  &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> 0 **
  UIntArray.undef_seg ptr 0 c **
  mpd_store_Z_compact UINT_MOD ptr 0 0 **
  &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr **
  &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> c
  |-- store_Z x 0.
Proof.
  intros.
  unfold store_Z.
  Exists ptr 0 c.
  replace (Zabs 0) with 0 by lia.
  entailer!.
  apply same_sign_refl.
Qed.

Lemma is_compact_Z_positive_size : forall n size,
  is_compact_Z UINT_MOD n size ->
  n > 0 ->
  size > 0.
Proof.
  intros n size Hcompact Hpos.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos n size Hcompact)
    as [_ [[Hsize Hzero] | [Hsize _]]]; lia.
Qed.

Lemma is_compact_Z_mono_size : forall n m size1 size2,
  n > m ->
  is_compact_Z UINT_MOD n size1 ->
  is_compact_Z UINT_MOD m size2 ->
  size1 >= size2.
Proof.
  intros n m size1 size2 Hgt Hn Hm.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos n size1 Hn)
    as [Hs1 Hbn].
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos m size2 Hm)
    as [Hs2 Hbm].
  destruct Hbm as [[Hsize2 Hzero2] | [Hsize2 [Hlo2 Hhi2]]].
  - lia.
  - destruct Hbn as [[Hsize1 Hzero1] | [Hsize1 [Hlo1 Hhi1]]].
    + pose proof (Z.pow_pos_nonneg UINT_MOD (size2 - 1) UINT_MOD_pos ltac:(lia)).
      lia.
    + destruct (Z_lt_ge_dec size1 size2) as [Hlt | Hge]; [exfalso | lia].
      assert (UINT_MOD ^ size1 <= UINT_MOD ^ (size2 - 1)).
      {
        apply Z.pow_le_mono_r; unfold UINT_MOD; lia.
      }
      lia.
Qed.

Lemma is_compact_Z_size_lt_value_lt : forall a b asize bsize,
  is_compact_Z UINT_MOD a asize ->
  is_compact_Z UINT_MOD b bsize ->
  0 < b ->
  asize < bsize ->
  a < b.
Proof.
  intros a b asize bsize Ha Hb Hbpos Hlt.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos a asize Ha) as [Hasize Habounds].
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos b bsize Hb) as [Hbsize Hbbounds].
  destruct Hbbounds as [[Hbsize0 Hbzero] | [Hbsizepos [Hblo Hbhi]]].
  - lia.
  - destruct Habounds as [[Hasize0 Hazero] | [Hasizepos [Halo Hahi]]].
    + lia.
    + assert (UINT_MOD ^ asize <= UINT_MOD ^ (bsize - 1)).
      { apply Z.pow_le_mono_r; unfold UINT_MOD; lia. }
      lia.
Qed.

Lemma is_compact_Z_same_value_size_eq : forall n size1 size2,
  n > 0 ->
  is_compact_Z UINT_MOD n size1 ->
  is_compact_Z UINT_MOD n size2 ->
  size1 = size2.
Proof.
  intros n size1 size2 Hpos Hcompact1 Hcompact2.
  destruct (Z.eq_dec size1 size2) as [Heq | Hneq].
  - assumption.
  - assert (size1 < size2 \/ size2 < size1) as [Hlt | Hlt] by lia.
    + pose proof (is_compact_Z_size_lt_value_lt
        n n size1 size2 Hcompact1 Hcompact2 ltac:(lia) Hlt).
      lia.
    + pose proof (is_compact_Z_size_lt_value_lt
        n n size2 size1 Hcompact2 Hcompact1 ltac:(lia) Hlt).
      lia.
Qed.

Lemma is_compact_Z_abs_same_value_size_eq : forall n size1 size2,
  n <> 0 ->
  is_compact_Z UINT_MOD (Zabs n) (Zabs size1) ->
  is_compact_Z UINT_MOD (Zabs n) (Zabs size2) ->
  Zabs size1 = Zabs size2.
Proof.
  intros.
  eapply is_compact_Z_same_value_size_eq; eauto.
  pose proof (proj2 (Z.abs_pos n) H).
  lia.
Qed.

Lemma mpd_read0_data_uint_props : forall data n size,
  list_to_Z UINT_MOD data = n ->
  last data 1 >= 1 ->
  list_within_bound UINT_MOD data ->
  size = Zlength data ->
  0 <= n <= 4294967295 ->
  Zlength (mpd_read0_data data) = Zmax size 1 /\
  list_within_bound UINT_MOD (mpd_read0_data data) /\
  list_to_Z UINT_MOD (mpd_read0_data data) = n /\
  Znth 0 (mpd_read0_data data) 0 = n.
Proof.
  intros data n size Hval Hlast Hbound Hsize Hrange.
  destruct data as [|a l].
  - rewrite list_to_Z_nil in Hval.
    rewrite Zlength_nil in Hsize.
    subst n size.
    change (mpd_read0_data (@nil Z)) with (0 :: nil).
    unfold Zmax.
    change (Z.max 0 1) with 1.
    split; [reflexivity|].
    split; [simpl; unfold UINT_MOD; lia|].
    split; [rewrite list_to_Z_single; reflexivity|reflexivity].
  - change (mpd_read0_data (a :: l)) with (a :: l).
    assert (Hcompact : is_compact_Z UINT_MOD n (Zlength (a :: l))).
    { unfold is_compact_Z. exists (a :: l).
      split; [exact Hval|].
      split; [reflexivity|].
      split; [exact Hbound| exact Hlast]. }
    pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos n
      (Zlength (a :: l)) Hcompact) as [_ Hcbounds].
    assert (Hnpos : n > 0).
    { destruct Hcbounds as [[Hlen0 Hn0] | [Hsz [Hlo Hhi]]].
      - rewrite Zlength_cons in Hlen0.
        pose proof (Zlength_nonneg l).
        lia.
      - pose proof (Z.pow_pos_nonneg UINT_MOD
          (Zlength (a :: l) - 1) UINT_MOD_pos
          ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia))
          as Hpowpos.
        apply Z.lt_gt.
        exact (Z.lt_le_trans 0 (UINT_MOD ^ (Zlength (a :: l) - 1))
          n Hpowpos Hlo). }
    assert (Hcompact1 : is_compact_Z UINT_MOD n 1).
    { apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos); [lia|].
      right. split; [lia|].
      change (1 - 1) with 0.
      change (UINT_MOD ^ 0) with 1.
      unfold UINT_MOD in *; lia. }
    pose proof (is_compact_Z_same_value_size_eq n (Zlength (a :: l)) 1
      Hnpos Hcompact Hcompact1) as Hlen1.
    clear Hcbounds Hcompact Hcompact1.
    assert (Hlen0 : Zlength l = 0).
    { rewrite Zlength_cons in Hlen1.
      unfold Z.succ in Hlen1.
      replace (Zlength l) with ((Zlength l + 1) - 1) by ring.
      rewrite Hlen1. ring. }
    apply Zlength_nil_inv in Hlen0.
    subst l.
    rewrite Zlength_cons, Zlength_nil in Hlen1.
    subst size.
    rewrite list_to_Z_single in Hval.
    subst n.
    split.
    { rewrite Zlength_cons, Zlength_nil.
      unfold Zmax.
      change (Z.max 1 1) with 1.
      reflexivity. }
    split; [exact Hbound|].
    split; [rewrite list_to_Z_single; reflexivity|reflexivity].
Qed.

Lemma is_compact_Z_size_pos_value_pos : forall n size,
  is_compact_Z UINT_MOD n size ->
  0 < size ->
  0 < n.
Proof.
  intros n size Hcompact Hsize.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos n size Hcompact)
    as [_ [[Hsize0 Hzero] | [Hsizepos [Hlo Hhi]]]]; try lia.
  pose proof (Z.pow_pos_nonneg UINT_MOD (size - 1) UINT_MOD_pos ltac:(lia)).
  lia.
Qed.

Lemma mpd_read0_signed_abs_same_sign : forall n size data,
  list_to_Z UINT_MOD data = n ->
  last data 1 >= 1 ->
  list_within_bound UINT_MOD data ->
  Zlength data = Zabs size ->
  0 <= n ->
  Zabs (if Z_lt_dec size 0 then - n else n) = n /\
  same_sign (if Z_lt_dec size 0 then - n else n) size.
Proof.
  intros n size data Hval Hlast Hbound Hlen Hnnonneg.
  split.
  - destruct (Z_lt_dec size 0).
    + rewrite Z.abs_opp. rewrite Z.abs_eq by lia. reflexivity.
    + rewrite Z.abs_eq by lia. reflexivity.
  - destruct (Z_lt_dec size 0) as [Hneg | Hnneg].
    + assert (Hcompact : is_compact_Z UINT_MOD n (Zabs size)).
      { unfold is_compact_Z. exists data.
        split; [exact Hval|].
        split; [exact Hlen|].
        split; [exact Hbound|exact Hlast]. }
      pose proof (is_compact_Z_size_pos_value_pos n (Zabs size) Hcompact ltac:(lia)) as Hnpos.
      unfold same_sign. right. lia.
    + unfold same_sign. left. lia.
Qed.

Lemma same_sign_compact_size_lt_value_lt : forall a b asize bsize,
  same_sign a asize ->
  same_sign b bsize ->
  is_compact_Z UINT_MOD (Zabs a) (Zabs asize) ->
  is_compact_Z UINT_MOD (Zabs b) (Zabs bsize) ->
  asize < bsize ->
  a < b.
Proof.
  intros a b asize bsize Ha Hb Hca Hcb Hlt.
  unfold same_sign in *.
  destruct Ha as [[Ha Hasize] | [Ha Hasize]];
  destruct Hb as [[Hb Hbsize] | [Hb Hbsize]].
  - assert (0 < Zabs b).
    { eapply is_compact_Z_size_pos_value_pos; eauto. lia. }
    assert (Zabs a < Zabs b).
    { eapply is_compact_Z_size_lt_value_lt; eauto; lia. }
    rewrite Z.abs_eq in H0 by lia.
    rewrite Z.abs_eq in H0 by lia.
    lia.
  - lia.
  - lia.
  - assert (0 < Zabs a).
    { eapply is_compact_Z_size_pos_value_pos; eauto. lia. }
    assert (Zabs b < Zabs a).
    { eapply is_compact_Z_size_lt_value_lt; eauto; lia. }
    rewrite Z.abs_neq in H0 by lia.
    rewrite Z.abs_neq in H0 by lia.
    lia.
Qed.

Lemma store_Z_to_store_Z_remain_size_zero : forall x n,
  store_Z x n |-- store_Z_remain_size x 0 0.
Proof.
  intros.
  unfold store_Z, store_Z_remain_size.
  Intros ptr size cap.
  Exists ptr; Exists size; Exists cap.
  sep_apply (mpd_store_Z_compact_undef_tail_to_undef_split ptr (Zabs n) (Zabs size) 0 cap).
  unfold mpd_store_Z_compact.
  Exists (@nil Z).
  unfold mpd_store_list.
  rewrite UIntArray.undef_full_empty.
  rewrite UIntArray.full_empty.
  replace (Zabs 0) with 0 by lia.
  entailer!.
  all: try (simpl; lia).
  all: try apply same_sign_refl.
Qed.

Lemma mpd_store_Z_append_one_compact : forall ptr val size,
  mpd_store_Z UINT_MOD ptr val size **
  (ptr + size * sizeof(UINT)) # UInt |-> 1 |--
    mpd_store_Z_compact UINT_MOD ptr (val + UINT_MOD ^ size) (size + 1).
Proof.
  intros.
  unfold mpd_store_Z, mpd_store_Z_compact, mpd_store_list.
  Intros data.
  subst size.
  Exists ((data ++ 1 :: nil)%list).
  sep_apply (UIntArray.seg_single ptr (Zlength data) 1).
  sep_apply (UIntArray.seg_to_full ptr (Zlength data) (Zlength data + 1) (1 :: nil)).
  sep_apply_l_atomic
    (UIntArray.full_merge_to_full ptr (Zlength data) (Zlength data + 1) data (1 :: nil)).
  { entailer!.
    pose proof (Zlength_nonneg data); lia. }
  rewrite Zlength_app.
  simpl.
  entailer!.
  - rewrite list_to_Z_app by exact UINT_MOD_pos.
    rewrite list_to_Z_single.
    unfold UINT_MOD in *.
    destruct (4294967296 ^ Zlength data); lia.
  - rewrite last_last; lia.
  - apply list_within_bound_concat.
    + tauto.
    + simpl; unfold UINT_MOD; lia.
Qed.

Lemma list_within_bound_app_single: forall Base (l: list Z) (x: Z),
  list_within_bound Base l ->
  0 <= x < Base ->
  list_within_bound Base (l ++ (x :: nil)).
Proof.
  intros Base l.
  induction l; intros.
  - simpl. tauto.
  - simpl in *.
    destruct H as [Ha Hl].
    split; [assumption |].
    apply IHl; assumption.
Qed.

Lemma div_unique_1: forall bp cy,
  0 <= bp < 2^32 -> 0 <= cy <= 2 -> 2^32 <= bp + cy -> bp + cy < 2 * 2^32 ->
  (bp + cy) / 2^32 = 1.
Proof.
  intros.
  symmetry.
  apply (Z.div_unique _ _ _ (bp + cy - 2^32)); lia.
Qed.

Lemma mod_overflow_bound: forall bp cy,
  0 <= bp < 2^32 -> 0 <= cy <= 2 -> 2^32 <= bp + cy -> bp + cy < 2 * 2^32 ->
  (bp + cy) mod 2^32 < cy.
Proof.
  intros.
  rewrite Zmod_eq by lia.
  rewrite div_unique_1 by lia.
  lia.
Qed.

Lemma ulb_ge_cy_implies_no_overflow: forall bp cy,
  0 <= bp < 2^32 -> 0 <= cy <= 2 ->
  (bp + cy) mod 2^32 >= cy ->
  bp + cy < 2^32.
Proof.
  intros.
  destruct (Z_lt_dec (bp + cy) (2^32)).
  - lia.
  - exfalso.
    assert (H2lt: bp + cy < 2 * 2^32) by lia.
    assert (H2ge: 2^32 <= bp + cy) by lia.
    pose proof (mod_overflow_bound bp cy H H0 H2ge H2lt).
    lia.
Qed.

Lemma UIntArray_full_to_mpd_store_Z_exact:
  forall ptr size data val,
    Zlength data = size ->
    list_to_Z UINT_MOD data = val ->
    list_within_bound UINT_MOD data ->
    UIntArray.full ptr size data |--
      mpd_store_Z UINT_MOD ptr val size.
Proof.
  intros ptr size data_in val Hlen Hval Hbound.
  unfold mpd_store_Z, mpd_store_list.
  Exists data_in.
  entailer!.
  rewrite Hlen.
  entailer!.
Qed.

Lemma list_last_eq_Znth_last:
  forall (data: list Z) size,
    Zlength data = size ->
    0 < size ->
    last data 1 = Znth (size - 1) data 0.
Proof.
  intros data size Hlen Hpos.
  assert (Hsplit:
            data =
            (sublist 0 (size - 1) data ++
             (Znth (size - 1) data 0 :: nil))%list).
  {
    rewrite <- (sublist_self data size) at 1 by lia.
    rewrite (sublist_split 0 size (size - 1) data) by lia.
    f_equal.
    assert (Hone:
              sublist (size - 1) size data =
              (Znth (size - 1) data 0 :: nil)).
    {
      replace (sublist (size - 1) size data)
        with (sublist (size - 1) ((size - 1) + 1) data)
        by (f_equal; lia).
      rewrite (sublist_single 0 (size - 1) data) by (rewrite Hlen; lia).
      reflexivity.
    }
    rewrite Hone.
    reflexivity.
  }
  rewrite Hsplit at 1.
  rewrite (@last_last Z (sublist 0 (size - 1) data)
             (Znth (size - 1) data 0) 1).
  reflexivity.
Qed.

Lemma list_to_Z_high_zero_prefix:
  forall (data: list Z) size,
    Zlength data = size ->
    0 < size ->
    Znth (size - 1) data 0 = 0 ->
    list_to_Z UINT_MOD (sublist 0 (size - 1) data) =
    list_to_Z UINT_MOD data.
Proof.
  intros data size Hlen Hpos Hzero.
  rewrite <- (sublist_self data size) at 2 by lia.
  rewrite (sublist_split 0 size (size - 1) data) by lia.
  assert (Hone:
            sublist (size - 1) size data =
            (Znth (size - 1) data 0 :: nil)).
  {
    replace (sublist (size - 1) size data)
      with (sublist (size - 1) ((size - 1) + 1) data)
      by (f_equal; lia).
    rewrite (sublist_single 0 (size - 1) data) by (rewrite Hlen; lia).
    reflexivity.
  }
  rewrite Hone.
  rewrite list_to_Z_app by exact UINT_MOD_pos.
  rewrite list_to_Z_single.
  rewrite Hzero.
  lia.
Qed.

Lemma is_compact_Z_full_high_nonzero:
  forall (data: list Z) size,
    Zlength data = size ->
    list_within_bound UINT_MOD data ->
    0 < size ->
    Znth (size - 1) data 0 <> 0 ->
    is_compact_Z UINT_MOD (list_to_Z UINT_MOD data) size.
Proof.
  intros data size Hlen Hbound Hpos Hnonzero.
  unfold is_compact_Z.
  exists data.
  repeat split; try assumption.
  rewrite (list_last_eq_Znth_last data size Hlen Hpos).
  pose proof (list_within_bound_Znth_bound UINT_MOD data (size - 1)
    ltac:(lia) Hbound).
  lia.
Qed.

Local Open Scope list.

Lemma UIntArray_full_to_mpd_store_Z_compact:
  forall ptr size data val,
    Zlength data = size ->
    list_to_Z UINT_MOD data = val ->
    list_within_bound UINT_MOD data ->
    is_compact_Z UINT_MOD val size ->
    UIntArray.full ptr size data |--
      mpd_store_Z_compact UINT_MOD ptr val size.
Proof.
  intros ptr size digits val Hlen Hval Hbound Hcompact.
  sep_apply (UIntArray_full_to_mpd_store_Z_exact ptr size digits val); try assumption.
  sep_apply (mpd_store_Z_to_mpd_store_Z_compact ptr val size); try assumption.
  entailer!.
Qed.

Lemma UIntArray_read0_split_to_full : forall ptr size data,
  size = Zlength data ->
  UIntArray.seg ptr 0 1 (sublist 0 1 (mpd_read0_data data)) **
  UIntArray.seg ptr 1 (Zmax size 1) (sublist 1 (Zmax size 1) (mpd_read0_data data)) |--
  UIntArray.full ptr (Zmax size 1) (mpd_read0_data data).
Proof.
  intros ptr size data Hsize.
  assert (Hlen : Zlength (mpd_read0_data data) = Zmax size 1).
  {
    subst size.
    destruct data as [|a l].
    - change (mpd_read0_data (@nil Z)) with (0 :: nil).
      rewrite Zlength_cons, Zlength_nil.
      unfold Z.succ, Zmax.
      simpl. reflexivity.
    - change (mpd_read0_data (a :: l)) with (a :: l).
      rewrite Zlength_cons.
      unfold Zmax.
      pose proof (Zlength_nonneg l).
      replace (Z.max (Z.succ (Zlength l)) 1) with (Z.succ (Zlength l)) by lia.
      reflexivity.
  }
  sep_apply (UIntArray.seg_merge_to_seg ptr 0 1 (Zmax size 1)
    (sublist 0 1 (mpd_read0_data data))
    (sublist 1 (Zmax size 1) (mpd_read0_data data))).
  - rewrite <- sublist_split with (mid:=1) (lo:=0) (hi:=Zmax size 1)
      (l:=mpd_read0_data data) by lia.
    rewrite sublist_self by lia.
    sep_apply (UIntArray.seg_to_full ptr 0 (Zmax size 1) (mpd_read0_data data)).
    replace (ptr + 0 * sizeof(UINT)) with ptr by lia.
    replace (Zmax size 1 - 0) with (Zmax size 1) by lia.
    entailer!.
  - unfold Zmax. lia.
Qed.

Lemma UIntArray_full_to_mpd_store_Z_compact_read0 : forall ptr n size data,
  list_to_Z UINT_MOD data = n ->
  last data 1 >= 1 ->
  list_within_bound UINT_MOD data ->
  size = Zlength data ->
  UIntArray.full ptr (Zmax size 1) (mpd_read0_data data) |--
  mpd_store_Z_compact_read0 ptr n size.
Proof.
  intros ptr n size data Hval Hlast Hbound Hsize.
  unfold mpd_store_Z_compact_read0.
  Exists data.
  entailer!.
Qed.

Lemma UInt_cell_to_mpd_store_Z_compact_1 : forall ptr v,
  0 < v <= UINT_MAX ->
  ptr # UInt |-> v |--
  mpd_store_Z_compact UINT_MOD ptr v 1.
Proof.
  intros ptr v Hrange.
  replace (ptr # UInt |-> v)
    with ((ptr + 0 * sizeof(UINT)) # UInt |-> v)
    by (replace (ptr + 0 * sizeof(UINT)) with ptr by lia; reflexivity).
  sep_apply_l_atomic (UIntArray.seg_single ptr 0 v).
  sep_apply (UIntArray.seg_to_full ptr 0 (0 + 1) (v :: nil)).
  replace (ptr + 0 * sizeof(UINT)) with ptr by lia.
  replace (0 + 1 - 0) with 1 by lia.
  sep_apply_l_atomic (UIntArray_full_to_mpd_store_Z_compact ptr 1 (v :: nil) v).
  - apply derivable1s_coq_prop_r. rewrite Zlength_cons, Zlength_nil. reflexivity.
  - apply derivable1s_coq_prop_r. rewrite list_to_Z_single. reflexivity.
  - apply derivable1s_coq_prop_r. simpl. unfold UINT_MOD. lia.
  - apply derivable1s_coq_prop_r.
    apply (is_compact_Z_from_bounds UINT_MOD UINT_MOD_pos); [lia|].
    right. split; [lia|].
    change (1 - 1) with 0.
    change (UINT_MOD ^ 0) with 1.
    unfold UINT_MOD in *; lia.
  - entailer!.
Qed.

Lemma UInt_cell_zero_undef_to_mpd_store_Z_compact_0 : forall ptr cap,
  1 <= cap ->
  ptr # UInt |-> 0 ** UIntArray.undef_seg ptr 1 cap |--
  mpd_store_Z_compact UINT_MOD ptr 0 0 ** UIntArray.undef_seg ptr 0 cap.
Proof.
  intros ptr cap Hcap.
  replace (ptr # UInt |-> 0)
    with ((ptr + 0 * sizeof(UINT)) # UInt |-> 0)
    by (replace (ptr + 0 * sizeof(UINT)) with ptr by lia; reflexivity).
  sep_apply_l_atomic (UIntArray.seg_single ptr 0 0).
  sep_apply_l_atomic (UIntArray.seg_to_undef_seg ptr 0 (0 + 1) (0 :: nil)).
  replace (0 + 1) with 1 by lia.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg ptr 0 1 cap).
  - unfold mpd_store_Z_compact, mpd_store_list.
    Exists (@nil Z).
    rewrite (UIntArray.full_empty ptr 0).
    entailer!.
    simpl. lia.
  - unfold Zmax in *. lia.
Qed.

Lemma mpd_store_Z_compact_read0_to_mpd_store_Z_compact : forall ptr n size cap,
  mpd_store_Z_compact_read0 ptr n size **
  UIntArray.undef_seg ptr (Zmax size 1) cap |--
    mpd_store_Z_compact UINT_MOD ptr n size **
    UIntArray.undef_seg ptr size cap.
Proof.
  intros ptr n size cap.
  unfold mpd_store_Z_compact_read0.
  unfold Zmax.
  Intros data.
  destruct H as [Hval [Hlast [Hbound Hsize]]].
  destruct data as [|a l].
  - rewrite list_to_Z_nil in Hval.
    simpl in Hsize.
    subst n size.
    change (mpd_read0_data []) with [0].
    replace (Z.max 0 1) with 1 by lia.
    prop_apply (UIntArray.undef_seg_valid ptr 1 cap).
    Intros.
    unfold mpd_store_Z_compact, mpd_store_list.
    Exists (@nil Z).
    rewrite (UIntArray.full_empty ptr 0).
    sep_apply_l_atomic (UIntArray.full_to_seg ptr 1 [0]).
    sep_apply_l_atomic (UIntArray.seg_to_undef_seg ptr 0 1 [0]).
    sep_apply (UIntArray.undef_seg_merge_to_undef_seg ptr 0 1 cap); try lia.
    entailer!.
  - assert (Hsize_pos : 1 <= size).
    { rewrite Hsize, Zlength_cons. pose proof (Zlength_nonneg l). lia. }
    change (mpd_read0_data (a :: l)) with (a :: l).
    replace (Z.max size 1) with size by lia.
    assert (Hcompact : is_compact_Z UINT_MOD n size).
    {
      unfold is_compact_Z.
      exists (a :: l).
      exact (conj Hval (conj (eq_sym Hsize) (conj Hbound Hlast))).
    }
    sep_apply (UIntArray_full_to_mpd_store_Z_compact ptr size (a :: l) n); eauto.
    entailer!.
Qed.

Lemma mpd_store_Z_compact_read0_same_sign : forall ptr n size,
  mpd_store_Z_compact_read0 ptr n size |-- “ same_sign n size ”.
Proof.
  intros.
  unfold mpd_store_Z_compact_read0.
  Intros data.
  destruct H as [Hval [Hlast [Hbound Hsize]]].
  subst n size.
  entailer!.
  unfold same_sign.
  left.
  split.
  - pose proof (list_to_Z_bound UINT_MOD UINT_MOD_pos data Hbound) as Hrange.
    lia.
  - pose proof (Zlength_nonneg data).
    lia.
Qed.

Lemma mpd_store_Z_compact_read0_same_sign_opp : forall ptr n size,
  mpd_store_Z_compact_read0 ptr n size |-- “ same_sign (- n) (- size) ”.
Proof.
  intros.
  unfold mpd_store_Z_compact_read0.
  Intros data.
  destruct H as [Hval [Hlast [Hbound Hsize]]].
  subst n size.
  entailer!.
  destruct data as [|a l].
  - rewrite list_to_Z_nil.
    rewrite Zlength_nil.
    unfold same_sign.
    left.
    split; lia.
  - unfold same_sign.
    right.
    split.
    + pose proof (list_to_Z_compact_bound UINT_MOD UINT_MOD_pos (a :: l) Hbound Hlast) as Hcompact.
      pose proof (Zlength_nonneg l) as Hlen.
      rewrite Zlength_cons in Hcompact.
      replace (Z.succ (Zlength l) - 1) with (Zlength l) in Hcompact by lia.
      pose proof (Z.pow_pos_nonneg UINT_MOD (Zlength l) UINT_MOD_pos ltac:(lia)).
      nia.
    + rewrite Zlength_cons.
      pose proof (Zlength_nonneg l).
      lia.
Qed.

Lemma store_Z_read0_to_store_Z : forall x n,
  store_Z_read0 x n |-- store_Z x n.
Proof.
  intros x n.
  unfold store_Z_read0, store_Z.
  Intros ptr size cap.
  Exists ptr size cap.
  entailer!.
  sep_apply (mpd_store_Z_compact_read0_to_mpd_store_Z_compact ptr (Z.abs n) (Z.abs size) cap).
  entailer!.
Qed.

Lemma store_Z_dummy_to_store_Z_0 : forall x dummy_ptr,
  store_Z_dummy x dummy_ptr |-- store_Z x 0.
Proof.
  intros x dummy_ptr.
  unfold store_Z_dummy, store_Z, mpd_store_Z_compact, mpd_store_list.
  Exists dummy_ptr 0 0.
  Exists (@nil Z).
  rewrite UIntArray.full_empty.
  rewrite UIntArray.undef_seg_empty.
  entailer!.
  all: cbn; unfold same_sign; lia.
Qed.

Lemma store_Z_read0_from_compact_read0_tail :
  forall x ptr n size absn abss cap_len mid hi l_tail,
    absn = Zabs n ->
    abss = Zabs size ->
    Zmax abss 1 <= mid ->
    mid <= hi ->
    hi <= cap_len ->
    same_sign n size ->
    mpd_store_Z_compact_read0 ptr absn abss **
    UIntArray.undef_seg ptr (Zmax abss 1) mid **
    UIntArray.seg ptr mid hi l_tail **
    UIntArray.undef_seg ptr hi cap_len **
    &(x # "__mpz_struct" ->ₛ "_mp_size") # Int |-> size **
    &(x # "__mpz_struct" ->ₛ "_mp_alloc") # Int |-> cap_len **
    &(x # "__mpz_struct" ->ₛ "_mp_d") # Ptr |-> ptr |--
      store_Z_read0 x n.
Proof.
  intros.
  unfold store_Z_read0.
  Exists ptr.
  Exists size.
  Exists cap_len.
  subst absn abss.
  entailer!.
  sep_apply_l_atomic (UIntArray.seg_to_undef_seg ptr mid hi l_tail).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg ptr (Zmax (Zabs size) 1) mid hi); try lia.
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg ptr (Zmax (Zabs size) 1) hi cap_len); try lia.
  entailer!.
  unfold Zmax in H1.
  lia.
Qed.

Lemma mpd_store_Z_compact_to_mpd_store_Z_compact_read0_nonzero : forall ptr n size,
  n <> 0 ->
  mpd_store_Z_compact UINT_MOD ptr n size |--
    mpd_store_Z_compact_read0 ptr n size.
Proof.
  intros ptr n size Hn.
  unfold mpd_store_Z_compact, mpd_store_Z_compact_read0.
  unfold Zmax.
  Intros data.
  destruct H as [Hval [Hlast Hbound]].
  destruct data as [|a l].
  - rewrite list_to_Z_nil in Hval.
    lia.
  - assert (Hsize_pos : 1 <= size).
    { rewrite H0, Zlength_cons. pose proof (Zlength_nonneg l). lia. }
    replace (Z.max size 1) with size by lia.
    Exists (a :: l).
    entailer!.
    unfold mpd_store_list.
    change (mpd_read0_data (a :: l)) with (a :: l).
    rewrite H0.
    entailer!.
Qed.

Lemma store_Z_to_store_Z_read0_nonzero : forall x n,
  n <> 0 ->
  store_Z x n |-- store_Z_read0 x n.
Proof.
  intros x n Hn.
  unfold store_Z, store_Z_read0.
  Intros ptr size cap.
  prop_apply (mpd_store_Z_compact_bound ptr (Z.abs n) (Z.abs size)).
  Intros.
  Exists ptr size cap.
  entailer!.
  sep_apply (mpd_store_Z_compact_to_mpd_store_Z_compact_read0_nonzero ptr (Z.abs n) (Z.abs size)); try lia.
  assert (Hsize_pos : 1 <= Z.abs size).
  assert (Habs_nonzero : Z.abs size <> 0).
  { intro Hzero. rewrite Hzero in H1. rewrite Z.pow_0_r in H1. lia. }
  pose proof (Z.abs_nonneg size).
  lia.
  unfold Zmax.
  replace (Z.max (Z.abs size) 1) with (Z.abs size) by lia.
  entailer!.
Qed.

Lemma UIntArray_full_high_zero_to_mpd_store_Z_compact:
  forall ptr size data val cap,
    0 < size ->
    Zlength data = size ->
    list_within_bound UINT_MOD data ->
    list_to_Z UINT_MOD data = val ->
    Znth (size - 1) data 0 = 0 ->
    is_compact_Z UINT_MOD val (size - 1) ->
    size <= cap ->
    UIntArray.full ptr size data **
    UIntArray.undef_seg ptr size cap |--
      mpd_store_Z_compact UINT_MOD ptr val (size - 1) **
      UIntArray.undef_seg ptr (size - 1) cap.
Proof.
  intros ptr size data val cap Hpos Hlen Hbound Hval Hhigh Hcompact Hcap.
  sep_apply (UIntArray.full_split_to_seg ptr (size - 1) size data); try lia.
  sep_apply (UIntArray.seg_to_undef_seg ptr (size - 1) size
    (sublist (size - 1) size data)).
  sep_apply (UIntArray.undef_seg_merge_to_undef_seg ptr (size - 1) size cap); try lia.
  sep_apply (UIntArray.seg_to_full ptr 0 (size - 1) (sublist 0 (size - 1) data)).
  replace (ptr + 0 * sizeof(UINT)) with ptr by lia.
  replace (size - 1 - 0) with (size - 1) by lia.
  assert (Hprefix_len: Zlength (sublist 0 (size - 1) data) = size - 1).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hprefix_bound: list_within_bound UINT_MOD (sublist 0 (size - 1) data)).
  { apply list_within_bound_sublist; try lia; assumption. }
  assert (Hprefix_val: list_to_Z UINT_MOD (sublist 0 (size - 1) data) = val).
  {
    rewrite <- Hval.
    apply list_to_Z_high_zero_prefix; lia.
  }
  sep_apply (UIntArray_full_to_mpd_store_Z_compact ptr (size - 1)
    (sublist 0 (size - 1) data) val); try assumption.
  entailer!.
Qed.

Lemma UIntArray_full_high_zero_to_mpd_store_Z_compact_exact:
  forall ptr size data val,
    0 < size ->
    Zlength data = size ->
    list_within_bound UINT_MOD data ->
    list_to_Z UINT_MOD data = val ->
    Znth (size - 1) data 0 = 0 ->
    is_compact_Z UINT_MOD val (size - 1) ->
    UIntArray.full ptr size data |--
      mpd_store_Z_compact UINT_MOD ptr val (size - 1) **
      UIntArray.undef_seg ptr (size - 1) size.
Proof.
  intros ptr size data val Hpos Hlen Hbound Hval Hhigh Hcompact.
  sep_apply (UIntArray.full_split_to_seg ptr (size - 1) size data); try lia.
  sep_apply (UIntArray.seg_to_undef_seg ptr (size - 1) size
    (sublist (size - 1) size data)).
  sep_apply (UIntArray.seg_to_full ptr 0 (size - 1) (sublist 0 (size - 1) data)).
  replace (ptr + 0 * sizeof(UINT)) with ptr by lia.
  replace (size - 1 - 0) with (size - 1) by lia.
  assert (Hprefix_len: Zlength (sublist 0 (size - 1) data) = size - 1).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hprefix_bound: list_within_bound UINT_MOD (sublist 0 (size - 1) data)).
  { apply list_within_bound_sublist; try lia; assumption. }
  assert (Hprefix_val: list_to_Z UINT_MOD (sublist 0 (size - 1) data) = val).
  {
    rewrite <- Hval.
    apply list_to_Z_high_zero_prefix; lia.
  }
  sep_apply (UIntArray_full_to_mpd_store_Z_compact ptr (size - 1)
    (sublist 0 (size - 1) data) val); try assumption.
  entailer!.
Qed.

Lemma UIntArray_full_to_mpd_store_Z_compact_exact:
  forall ptr size data val,
    Zlength data = size ->
    list_to_Z UINT_MOD data = val ->
    list_within_bound UINT_MOD data ->
    is_compact_Z UINT_MOD val size ->
    UIntArray.full ptr size data |--
      mpd_store_Z_compact UINT_MOD ptr val size **
      UIntArray.undef_seg ptr size size.
Proof.
  intros ptr size data val Hlen Hval Hbound Hcompact.
  rewrite UIntArray.undef_seg_empty.
  sep_apply (UIntArray_full_to_mpd_store_Z_compact ptr size data val); try assumption.
  entailer!.
Qed.

Lemma mpd_store_Z_zero_to_emp:
  forall ptr n,
    mpd_store_Z UINT_MOD ptr n 0 |-- “ n = 0 ” && emp.
Proof.
  intros.
  unfold mpd_store_Z, mpd_store_list.
  Intros data.
  symmetry in H0.
  apply Zlength_nil_inv in H0.
  subst data.
  simpl in H.
  rewrite UIntArray.full_empty.
  entailer!.
Qed.
