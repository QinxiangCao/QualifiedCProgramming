Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition Zmap_range {A : Type} (f : Z -> A) (n : Z) : list A :=
  map f (Zrange 0 n).

Definition OneAppleCut (before after : list Z) : Prop :=
  exists prefix e suffix,
    before = prefix ++ e :: suffix /\ after = prefix ++ [e + 1; e + 1] ++ suffix.

Definition EqualDyadicShares (m : Z) (pieces : list Z) : Prop :=
  exists shares depth,
    Zlength shares = m /\ Permutation pieces (concat shares) /\
    Forall (fun e => 0 <= e <= depth) pieces /\
    forall i j, 0 <= i < m -> 0 <= j < m ->
      fold_right (fun e total => 2 ^ (depth - e) + total) 0 (Znth i shares nil) =
      fold_right (fun e total => 2 ^ (depth - e) + total) 0 (Znth j shares nil).

Definition AchievableAppleDivision (n m cuts : Z) : Prop :=
  exists states,
    Zlength states = cuts + 1 /\
    Znth 0 states nil = Zmap_range (fun _ => 0) n /\
    (forall i, 0 <= i < cuts -> OneAppleCut (Znth i states nil) (Znth (i + 1) states nil)) /\
    EqualDyadicShares m (Znth cuts states nil).

Definition Pre (n m : Z) : Prop := 1 <= n <= 1000000000 /\ 1 <= m <= 1000000000.

Definition Spec (n m out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun cuts : Z => 0 <= cuts /\ AchievableAppleDivision n m cuts)
    (fun cuts => cuts) out \/
  (out = -1 /\ forall cuts, ~ (0 <= cuts /\ AchievableAppleDivision n m cuts)).

Definition GcdValue (a b : Z) : Z := Z.gcd a b.

Definition PowerOfTwo (x : Z) : Prop :=
  exists k, 0 <= k /\ x = 2 ^ k.

Definition DyadicResidue (start modulus i : Z) : Z :=
  (2 ^ i * start) mod modulus.

Definition DyadicRemainderPrefix
    (start modulus current total : Z) : Prop :=
  exists k,
    0 <= k /\
    current = DyadicResidue start modulus k /\
    total = fold_right Z.add 0
              (Zmap_range (fun i => DyadicResidue start modulus i) k).

Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Zquot.
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Lemma positive_gcd_quotient_bounds__solver_setup :
  forall n m : Z, 0 < n -> 0 < m ->
    0 < Z.gcd n m /\ 1 <= m ÷ Z.gcd n m <= m.
Proof.
  intros n m Hn Hm.
  assert (Hg : 0 < Z.gcd n m).
  { pose proof (Z.gcd_nonneg n m).
    destruct (Z.eq_dec (Z.gcd n m) 0) as [Heq | Hneq].
    - apply Z.gcd_eq_0_l in Heq. lia.
    - lia. }
  destruct (Z.gcd_divide_r n m) as (q & Hq).
  assert (Hquot : m ÷ Z.gcd n m = q).
  { rewrite Zquot_Zdiv_pos by lia.
    rewrite Hq at 1.
    apply Z.div_mul.
    lia. }
  split; [exact Hg |].
  nia.
Qed.
Lemma rem_mod_pos__solver_setup :
  forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b = a mod b.
Proof.
  intros a b Ha Hb.
  apply Zrem_Zmod_pos.
  all: lia.
Qed.
Lemma land_pred_zero_power_of_two__solver_setup :
  forall x : Z, 0 < x -> Z.land x (x - 1) = 0 ->
  exists k : Z, 0 <= k /\ x = 2 ^ k.
Proof.
  intros x Hx H.
  destruct x as [|p|p]; try lia.
  induction p.
  - simpl in H.
    assert (Hdiag : N.land (N.pos p) (N.pos p) = N.pos p) by apply N.land_diag.
    simpl in Hdiag.
    rewrite Hdiag in H.
    discriminate.
  - destruct p.
    + simpl in H.
      assert (Hdiag : N.land (N.pos p) (N.pos p) = N.pos p) by apply N.land_diag.
      simpl in Hdiag.
      rewrite Hdiag in H.
      discriminate.
    + simpl in H.
      assert (Hrec : Z.land (Z.pos p~0) (Z.pos p~0 - 1) = 0).
      { simpl in H |- *.
        remember
          (match Pos.pred_double p with
           | xI q | xO q => Pos.Ndouble (Pos.land p q)
           | xH => N0
           end) as u.
        destruct u; simpl in H |- *; [reflexivity | discriminate]. }
      destruct (IHp ltac:(lia) Hrec) as (k & Hk & Heq).
      exists (k + 1).
      split; [lia|].
      replace (k + 1) with (Z.succ k) by lia.
      rewrite Z.pow_succ_r by lia.
      lia.
    + exists 1.
      split; [lia | reflexivity].
  - exists 0.
    split; reflexivity.
Qed.
Lemma dyadic_residue_succ__dyadic_transition :
  forall start modulus k,
    0 <= k -> modulus <> 0 ->
    DyadicResidue start modulus (k + 1) =
    (2 * DyadicResidue start modulus k) mod modulus.
Proof.
  intros start modulus k Hk Hmod.
  unfold DyadicResidue.
  replace (k + 1) with (Z.succ k) by lia.
  rewrite Z.pow_succ_r by lia.
  replace (2 * 2 ^ k * start) with (2 * (2 ^ k * start)) by ring.
  rewrite Z.mul_mod_idemp_r by exact Hmod.
  reflexivity.
Qed.
Lemma zrange_aux_length__dyadic_transition :
  forall low n, length (Zrange_aux low n) = n.
Proof.
  intros low n. revert low.
  induction n as [|n IH]; intros low; simpl; auto.
Qed.
Lemma zmap_range_length__dyadic_transition :
  forall (A : Type) (f : Z -> A) k,
    0 <= k -> Z.of_nat (length (Zmap_range f k)) = k.
Proof.
  intros A f k Hk.
  unfold Zmap_range, Zrange.
  rewrite length_map, zrange_aux_length__dyadic_transition.
  rewrite Z2Nat.id by lia.
  lia.
Qed.
Lemma zmap_range_succ__dyadic_transition :
  forall (A : Type) (f : Z -> A) k,
    0 <= k ->
    Zmap_range f (k + 1) = Zmap_range f k ++ [f k].
Proof.
  intros A f k Hk.
  unfold Zmap_range, Zrange.
  replace (Z.to_nat (k + 1 - 0)) with
      (Z.to_nat (k - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app, map_app.
  rewrite Z2Nat.id by lia.
  cbn [Zrange_aux].
  replace (0 + (k - 0)) with k by lia.
  reflexivity.
Qed.
Lemma fold_right_add_acc__dyadic_transition :
  forall xs acc,
    fold_right Z.add acc xs = fold_right Z.add 0 xs + acc.
Proof.
  intros xs acc. induction xs as [|x xs IH]; simpl; lia.
Qed.
Lemma dyadic_prefix_step__dyadic_transition :
  forall start modulus current total,
    modulus <> 0 ->
    DyadicRemainderPrefix start modulus current total ->
    DyadicRemainderPrefix start modulus
      ((2 * current) mod modulus) (total + current).
Proof.
  intros start modulus current total Hmod
    [k [Hk [Hcurrent Htotal]]].
  exists (k + 1).
  split; [lia|].
  split.
  - rewrite dyadic_residue_succ__dyadic_transition by assumption.
    now rewrite <- Hcurrent.
  - rewrite zmap_range_succ__dyadic_transition by lia.
    rewrite fold_right_app. simpl.
    rewrite fold_right_add_acc__dyadic_transition.
    rewrite Htotal, Hcurrent.
    lia.
Qed.
Lemma dyadic_prefix_stage_bound__dyadic_transition :
  forall n_pre m_pre current k,
    1 <= n_pre -> 1 <= m_pre -> m_pre <= 1000000000 ->
    PowerOfTwo (m_pre ÷ GcdValue n_pre m_pre) ->
    0 <= k ->
    current = DyadicResidue (n_pre mod m_pre) m_pre k ->
    current <> 0 ->
    k < 30.
Proof.
  intros n_pre m_pre current k Hn Hm Hmmax
    [e [He Hpower]] Hk Hcurrent Hnonzero.
  unfold GcdValue in Hpower.
  set (g := Z.gcd n_pre m_pre) in *.
  assert (Hgpos : 0 < g).
  {
    assert (Hg_nonneg : 0 <= g) by
      (subst g; apply Z.gcd_nonneg).
    assert (Hg_nz : g <> 0).
    {
      intro Hg0. subst g.
      apply Z.gcd_eq_0_l in Hg0.
      lia.
    }
    lia.
  }
  pose proof (Z.gcd_divide_l n_pre m_pre) as Hgn.
  pose proof (Z.gcd_divide_r n_pre m_pre) as Hgm.
  fold g in Hgn, Hgm.
  destruct Hgn as [a Hna].
  destruct Hgm as [b Hmb].
  assert (Hquot : m_pre ÷ g = b).
  {
    rewrite Hmb, Z.quot_mul by lia.
    reflexivity.
  }
  rewrite Hquot in Hpower.
  subst b.
  assert (Hepowpos : 0 < 2 ^ e) by
    (apply Z.pow_pos_nonneg; lia).
  assert (He_lt : e < 30).
  {
    assert (Htwo_le_m : 2 ^ e <= m_pre) by nia.
    destruct (Z_lt_ge_dec e 30) as [Hlt|Hge]; [exact Hlt|].
    assert (Hpowmono : 2 ^ 30 <= 2 ^ e).
    { apply Z.pow_le_mono_r; lia. }
    change (1073741824 <= 2 ^ e) in Hpowmono.
    lia.
  }
  destruct (Z_lt_ge_dec k 30) as [Hlt|Hge]; [exact Hlt|].
  exfalso.
  assert (Hele : e <= k) by lia.
  assert (Hpowfactor : 2 ^ k = 2 ^ (k - e) * 2 ^ e).
  {
    replace k with ((k - e) + e) at 1 by lia.
    rewrite Z.pow_add_r by lia.
    reflexivity.
  }
  apply Hnonzero.
  rewrite Hcurrent.
  unfold DyadicResidue.
  assert (Hmod_cong :
      (2 ^ k * (n_pre mod m_pre)) mod m_pre =
      (2 ^ k * n_pre) mod m_pre).
  {
    apply Z.mul_mod_idemp_r. lia.
  }
  rewrite Hmod_cong.
  rewrite Hpowfactor, Hna, Hmb.
  replace (2 ^ (k - e) * 2 ^ e * (a * g))
    with ((2 ^ (k - e) * a) * (2 ^ e * g)) by ring.
  apply Z.mod_mul. lia.
Qed.
Lemma fold_right_mod_bound__dyadic_transition :
  forall modulus xs,
    0 < modulus ->
    Forall (fun x => 0 <= x < modulus) xs ->
    fold_right Z.add 0 xs <= Z.of_nat (length xs) * modulus.
Proof.
  intros modulus xs Hmod Hforall.
  induction Hforall.
  - simpl. lia.
  - cbn [fold_right length].
    rewrite Nat2Z.inj_succ.
    nia.
Qed.
Lemma dyadic_prefix_total_bound__dyadic_transition :
  forall n_pre m_pre current total,
    1 <= n_pre -> 1 <= m_pre -> m_pre <= 1000000000 ->
    PowerOfTwo (m_pre ÷ GcdValue n_pre m_pre) ->
    DyadicRemainderPrefix (n_pre mod m_pre) m_pre current total ->
    current <> 0 ->
    total + current <= 30000000000.
Proof.
  intros n_pre m_pre current total Hn Hm Hmmax Hpower
    [k [Hk [Hcurrent Htotal]]] Hnonzero.
  pose proof (dyadic_prefix_stage_bound__dyadic_transition
    n_pre m_pre current k Hn Hm Hmmax Hpower Hk Hcurrent Hnonzero)
    as Hstage.
  set (xs := Zmap_range
    (fun i => DyadicResidue (n_pre mod m_pre) m_pre i) (k + 1)).
  assert (Hxs : xs =
      Zmap_range (fun i => DyadicResidue (n_pre mod m_pre) m_pre i) k ++
      [DyadicResidue (n_pre mod m_pre) m_pre k]).
  {
    unfold xs.
    apply zmap_range_succ__dyadic_transition.
    lia.
  }
  assert (Hsum : fold_right Z.add 0 xs = total + current).
  {
    rewrite Hxs, fold_right_app. simpl.
    rewrite fold_right_add_acc__dyadic_transition.
    rewrite Htotal, Hcurrent.
    lia.
  }
  assert (Hforall : Forall (fun x => 0 <= x < m_pre) xs).
  {
    apply Forall_forall.
    intros x Hxin.
    unfold xs, Zmap_range in Hxin.
    apply in_map_iff in Hxin.
    destruct Hxin as [i [Hx _]].
    subst x. unfold DyadicResidue.
    apply Z.mod_pos_bound. lia.
  }
  pose proof (fold_right_mod_bound__dyadic_transition
    m_pre xs ltac:(lia) Hforall) as Hbound.
  assert (Hlen : Z.of_nat (length xs) = k + 1).
  {
    unfold xs.
    apply zmap_range_length__dyadic_transition.
    lia.
  }
  rewrite Hsum, Hlen in Hbound.
  nia.
Qed.
Lemma land_pred_nonzero_not_power_of_two__dyadic_final :
  forall x, 0 < x -> Z.land x (x - 1) <> 0 -> ~ PowerOfTwo x.
Proof.
  intros x Hx Hland Hpow.
  unfold PowerOfTwo in Hpow.
  destruct Hpow as [k [Hk Hxk]].
  subst x.
  apply Hland.
  replace (2 ^ k - 1) with (Z.ones k) by
    (rewrite Z.ones_equiv; unfold Z.pred; reflexivity).
  rewrite Z.land_ones by exact Hk.
  apply Z.mod_same.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  lia.
Qed.
Lemma Zrange_aux_shift_one__dyadic_final :
  forall n low,
    Zrange_aux (low + 1) n =
    map (fun i => i + 1) (Zrange_aux low n).
Proof.
  induction n as [|n IH]; intros low; simpl; [reflexivity |].
  f_equal. apply IH.
Qed.
Lemma dyadic_residue_shift__dyadic_final :
  forall start modulus i,
    0 < modulus -> 0 <= i ->
    DyadicResidue start modulus (i + 1) =
    DyadicResidue (DyadicResidue start modulus 1) modulus i.
Proof.
  intros start modulus i Hmod Hi.
  unfold DyadicResidue.
  replace (i + 1) with (Z.succ i) by lia.
  rewrite Z.pow_succ_r by lia.
  simpl Z.pow at 1.
  rewrite Zmult_mod_idemp_r.
  f_equal. ring.
Qed.
Lemma dyadic_prefix_fold_step__dyadic_final :
  forall k start modulus,
    0 < modulus -> 0 <= start < modulus ->
    fold_right Z.add 0
      (Zmap_range (fun i => DyadicResidue start modulus i)
        (Z.of_nat (S k))) =
    start +
    fold_right Z.add 0
      (Zmap_range
        (fun i => DyadicResidue (DyadicResidue start modulus 1) modulus i)
        (Z.of_nat k)).
Proof.
  intros k start modulus Hmod Hstart.
  unfold Zmap_range, Zrange.
  replace (Z.to_nat (Z.of_nat (S k) - 0)) with (S k) by lia.
  replace (Z.to_nat (Z.of_nat k - 0)) with k by lia.
  simpl.
  pose proof (Zrange_aux_shift_one__dyadic_final k 0) as Hrange.
  simpl in Hrange. rewrite Hrange.
  rewrite map_map.
  assert (Hmaps :
      map
        (fun x => DyadicResidue start modulus (x + 1))
        (Zrange_aux 0 k) =
      map
        (fun x => DyadicResidue (DyadicResidue start modulus 1) modulus x)
        (Zrange_aux 0 k)).
  { apply map_ext_in. intros i Hin.
    apply dyadic_residue_shift__dyadic_final; [exact Hmod |].
    apply In_Zrange_aux in Hin. lia. }
  rewrite Hmaps.
  unfold DyadicResidue at 1.
  rewrite Z.pow_0_r.
  replace (1 * start) with start by ring.
  rewrite Z.mod_small by exact Hstart.
  reflexivity.
Qed.
Lemma dyadic_cost_power_shift__dyadic_final :
  forall k a q,
    0 <= a -> 0 <= q < 2 ^ Z.of_nat k ->
    (let fix cost (j : nat) (x : Z) : Z :=
       match j with
       | O => x
       | S j' => x mod 2 + cost j' (x / 2)
       end
     in cost k (a * 2 ^ Z.of_nat k + q)) =
    a +
    (let fix cost (j : nat) (x : Z) : Z :=
       match j with
       | O => x
       | S j' => x mod 2 + cost j' (x / 2)
       end
     in cost k q).
Proof.
  induction k as [|k IH]; intros a q Ha Hq.
  - cbn. assert (q = 0) by lia. subst q. ring.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. cbn beta iota zeta.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hq by lia.
    assert (Hpow : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
    assert (Hqmod :
        (a * (2 * 2 ^ Z.of_nat k) + q) mod 2 = q mod 2).
    { replace (a * (2 * 2 ^ Z.of_nat k) + q)
        with (q + (a * 2 ^ Z.of_nat k) * 2) by ring.
      apply Z_mod_plus_full. }
    rewrite Hqmod.
    assert (Hqdiv :
        (a * (2 * 2 ^ Z.of_nat k) + q) / 2 =
        a * 2 ^ Z.of_nat k + q / 2).
    { replace (a * (2 * 2 ^ Z.of_nat k) + q)
        with (q + (a * 2 ^ Z.of_nat k) * 2) by ring.
      rewrite Z_div_plus_full by lia. ring. }
    rewrite Hqdiv.
    assert (Hqhalf : 0 <= q / 2 < 2 ^ Z.of_nat k).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    specialize (IH a (q / 2) Ha Hqhalf). cbn zeta in IH.
    rewrite IH. ring.
Qed.
Lemma dyadic_cost_leading_digit__dyadic_final :
  forall k a q,
    0 <= a < 2 -> 0 <= q < 2 ^ Z.of_nat k ->
    (let fix cost (j : nat) (x : Z) : Z :=
       match j with
       | O => x
       | S j' => x mod 2 + cost j' (x / 2)
       end
     in cost (S k) (a * 2 ^ Z.of_nat k + q)) =
    a +
    (let fix cost (j : nat) (x : Z) : Z :=
       match j with
       | O => x
       | S j' => x mod 2 + cost j' (x / 2)
       end
     in cost k q).
Proof.
  induction k as [|k IH]; intros a q Ha Hq.
  - rewrite Z.pow_0_r. assert (q = 0) by lia. subst q.
    replace (a * 1 + 0) with a by ring.
    cbn beta iota zeta.
    rewrite Z.mod_small by lia.
    rewrite Z.div_small by lia. ring.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. cbn beta iota zeta.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hq by lia.
    assert (Hpow : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
    assert (Hqmod :
        (a * (2 * 2 ^ Z.of_nat k) + q) mod 2 = q mod 2).
    { replace (a * (2 * 2 ^ Z.of_nat k) + q)
        with (q + (a * 2 ^ Z.of_nat k) * 2) by ring.
      apply Z_mod_plus_full. }
    rewrite Hqmod.
    assert (Hqdiv :
        (a * (2 * 2 ^ Z.of_nat k) + q) / 2 =
        a * 2 ^ Z.of_nat k + q / 2).
    { replace (a * (2 * 2 ^ Z.of_nat k) + q)
        with (q + (a * 2 ^ Z.of_nat k) * 2) by ring.
      rewrite Z_div_plus_full by lia. ring. }
    rewrite Hqdiv.
    assert (Hqhalf : 0 <= q / 2 < 2 ^ Z.of_nat k).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    specialize (IH a (q / 2) Ha Hqhalf). cbn zeta in IH.
    rewrite IH. ring.
Qed.
Lemma complete_reduced_prefix_cost_identity__dyadic_final :
  forall k start modulus,
    0 < modulus -> 0 <= start < modulus ->
    DyadicResidue start modulus (Z.of_nat k) = 0 ->
    fold_right Z.add 0
      (Zmap_range (fun i => DyadicResidue start modulus i) (Z.of_nat k)) =
    modulus *
      (let fix cost (j : nat) (x : Z) : Z :=
         match j with
         | O => x
         | S j' => x mod 2 + cost j' (x / 2)
         end
       in cost k ((2 ^ Z.of_nat k * start) / modulus)) - start.
Proof.
  induction k as [|k IH]; intros start modulus Hmod Hstart Hcomplete.
  - unfold Zmap_range, Zrange. simpl.
    unfold DyadicResidue in Hcomplete. rewrite Z.pow_0_r in Hcomplete.
    replace (1 * start) with start in Hcomplete by ring.
    rewrite Z.mod_small in Hcomplete by exact Hstart.
    subst start. cbn. ring.
  - set (next := DyadicResidue start modulus 1).
    assert (Hnext_bounds : 0 <= next < modulus).
    { unfold next, DyadicResidue. apply Z.mod_pos_bound. lia. }
    assert (Hnext_complete :
        DyadicResidue next modulus (Z.of_nat k) = 0).
    { pose proof (dyadic_residue_shift__dyadic_final start modulus
        (Z.of_nat k) Hmod ltac:(lia)) as Hshift.
      replace (Z.of_nat k + 1) with (Z.of_nat (S k)) in Hshift by lia.
      unfold next. rewrite <- Hshift. exact Hcomplete. }
    specialize (IH next modulus Hmod Hnext_bounds Hnext_complete).
    rewrite dyadic_prefix_fold_step__dyadic_final by assumption.
    fold next.
    rewrite IH.
    set (carry := (2 * start) / modulus).
    set (qnext := (2 ^ Z.of_nat k * next) / modulus).
    assert (Hcarry : 0 <= carry < 2).
    { unfold carry. split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    assert (Hnext_eq : next = 2 * start - carry * modulus).
    { unfold next, carry, DyadicResidue.
      rewrite Z.pow_1_r. rewrite Z.mod_eq by lia. ring. }
    assert (Hqnext_bounds : 0 <= qnext < 2 ^ Z.of_nat k).
    { unfold qnext.
      assert (Hpow : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
      split.
      - apply Z.div_pos; nia.
      - apply Z.div_lt_upper_bound; nia. }
    assert (Hquot :
        (2 ^ Z.of_nat (S k) * start) / modulus =
        carry * 2 ^ Z.of_nat k + qnext).
    { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      unfold qnext.
      replace (2 * 2 ^ Z.of_nat k * start)
        with (2 ^ Z.of_nat k * next +
              (carry * 2 ^ Z.of_nat k) * modulus)
        by (rewrite Hnext_eq; ring).
      rewrite Z_div_plus_full by lia. ring. }
    rewrite Hquot.
    rewrite dyadic_cost_leading_digit__dyadic_final
      by (try exact Hcarry; exact Hqnext_bounds).
    unfold qnext in *.
    lia.
Qed.
Lemma complete_prefix_cost_identity__dyadic_final :
  forall k n modulus,
    0 < modulus -> 0 <= n ->
    DyadicResidue (n mod modulus) modulus (Z.of_nat k) = 0 ->
    fold_right Z.add 0
      (Zmap_range
        (fun i => DyadicResidue (n mod modulus) modulus i)
        (Z.of_nat k)) =
    modulus *
      (let fix cost (j : nat) (x : Z) : Z :=
         match j with
         | O => x
         | S j' => x mod 2 + cost j' (x / 2)
         end
       in cost k ((2 ^ Z.of_nat k * n) / modulus)) - n.
Proof.
  intros k n modulus Hmod Hn Hcomplete.
  set (r := n mod modulus).
  assert (Hr : 0 <= r < modulus).
  { unfold r. apply Z.mod_pos_bound. lia. }
  pose proof (complete_reduced_prefix_cost_identity__dyadic_final
    k r modulus Hmod Hr Hcomplete) as Hreduced.
  set (a := n / modulus).
  set (qr := (2 ^ Z.of_nat k * r) / modulus).
  assert (Ha : 0 <= a) by (unfold a; apply Z.div_pos; lia).
  assert (Hqr : 0 <= qr < 2 ^ Z.of_nat k).
  { unfold qr.
    assert (Hpow : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
    split; [apply Z.div_pos; nia | apply Z.div_lt_upper_bound; nia]. }
  assert (Hn_eq : n = a * modulus + r).
  { unfold a, r. pose proof (Z.div_mod n modulus ltac:(lia)). lia. }
  assert (Hquot :
      (2 ^ Z.of_nat k * n) / modulus =
      a * 2 ^ Z.of_nat k + qr).
  { unfold qr.
    replace (2 ^ Z.of_nat k * n)
      with (2 ^ Z.of_nat k * r +
            (a * 2 ^ Z.of_nat k) * modulus)
      by (rewrite Hn_eq; ring).
    rewrite Z_div_plus_full by lia. ring. }
  rewrite Hquot.
  rewrite dyadic_cost_power_shift__dyadic_final by assumption.
  rewrite Hreduced.
  set (C := (fix cost (j : nat) (x : Z) : Z :=
    match j with
    | O => x
    | S j' => x mod 2 + cost j' (x / 2)
    end) k qr).
  change (modulus * C - r = modulus * (a + C) - n).
  rewrite Hn_eq. ring.
Qed.
Lemma one_apple_cut_bounds_back__dyadic_final :
  forall before after depth,
    OneAppleCut before after ->
    Forall (fun e => e <= depth) after ->
    Forall (fun e => e <= depth) before.
Proof.
  intros before after depth Hcut Hafter.
  unfold OneAppleCut in Hcut.
  destruct Hcut as [prefix [e [suffix [-> ->]]]].
  apply Forall_app in Hafter.
  destruct Hafter as [Hprefix Hrest].
  apply Forall_app in Hrest.
  destruct Hrest as [Hpair Hsuffix].
  assert (Heplus : e + 1 <= depth).
  { apply Forall_forall with (x := e + 1) in Hpair.
    - exact Hpair.
    - simpl; auto. }
  apply Forall_app; split; [exact Hprefix |].
  constructor; [lia | exact Hsuffix].
Qed.
Lemma one_apple_cut_mass__dyadic_final :
  forall before after depth,
    OneAppleCut before after ->
    Forall (fun e => e <= depth) after ->
    fold_right (fun e total => 2 ^ (depth - e) + total) 0 before =
    fold_right (fun e total => 2 ^ (depth - e) + total) 0 after.
Proof.
  intros before after depth Hcut Hafter.
  unfold OneAppleCut in Hcut.
  destruct Hcut as [prefix [e [suffix [-> ->]]]].
  assert (He : e + 1 <= depth).
  { apply Forall_forall with (x := e + 1) in Hafter.
    - exact Hafter.
    - apply in_or_app. right. simpl. auto. }
  clear Hafter.
  induction prefix as [|p prefix IH]; simpl.
  - replace (depth - e) with (Z.succ (depth - (e + 1))) by lia.
    rewrite Z.pow_succ_r by lia.
    ring.
  - now rewrite IH.
Qed.
Lemma indexed_cut_chain_mass__dyadic_final :
  forall states depth,
    0 < Zlength states ->
    (forall i, 0 <= i < Zlength states - 1 ->
       OneAppleCut (Znth i states nil) (Znth (i + 1) states nil)) ->
    Forall (fun e => e <= depth)
      (Znth (Zlength states - 1) states nil) ->
    Forall (fun e => e <= depth) (Znth 0 states nil) /\
    fold_right (fun e total => 2 ^ (depth - e) + total) 0
      (Znth 0 states nil) =
    fold_right (fun e total => 2 ^ (depth - e) + total) 0
      (Znth (Zlength states - 1) states nil).
Proof.
  induction states as [|a states IH]; intros depth Hlen Hsteps Hfinal.
  { rewrite Zlength_nil in Hlen; lia. }
  destruct states as [|b states].
  { rewrite !Znth0_cons. simpl. auto. }
  assert (Htail_len : 0 < Zlength (b :: states)).
  { rewrite Zlength_cons. pose proof (Zlength_nonneg states). lia. }
  assert (Hlast :
      Znth (Zlength (a :: b :: states) - 1) (a :: b :: states) nil =
      Znth (Zlength (b :: states) - 1) (b :: states) nil).
  { rewrite Zlength_cons.
    rewrite Znth_cons by
      (rewrite Zlength_cons; pose proof (Zlength_nonneg states);
       unfold Z.succ; lia).
    f_equal. lia. }
  assert (Htail_steps : forall i,
      0 <= i < Zlength (b :: states) - 1 ->
      OneAppleCut (Znth i (b :: states) nil)
                  (Znth (i + 1) (b :: states) nil)).
  { intros i Hi.
    pose proof (Zlength_nonneg states) as Hstates_len.
    specialize (Hsteps (i + 1)).
    assert (Hidx : 0 <= i + 1 < Zlength (a :: b :: states) - 1).
    { destruct Hi as [Hi0 Hilt]. split; [lia |].
      rewrite Zlength_cons in Hilt.
      replace (Z.succ (Zlength states) - 1) with (Zlength states) in Hilt
        by (unfold Z.succ; lia).
      rewrite !Zlength_cons.
      replace (Z.succ (Z.succ (Zlength states)) - 1)
        with (Zlength states + 1) by (unfold Z.succ; lia).
      lia. }
    specialize (Hsteps Hidx).
    rewrite (Znth_cons nil (i + 1) a (b :: states)) in Hsteps by lia.
    rewrite (Znth_cons nil (i + 1 + 1) a (b :: states)) in Hsteps by lia.
    replace (i + 1 - 1) with i in Hsteps by lia.
    replace (i + 1 + 1 - 1) with (i + 1) in Hsteps by lia.
    exact Hsteps. }
  rewrite Hlast in Hfinal.
  specialize (IH depth Htail_len Htail_steps Hfinal).
  destruct IH as [Hb_bounds Htail_mass].
  assert (Hab : OneAppleCut a b).
  { specialize (Hsteps 0).
    specialize (Hsteps ltac:(rewrite !Zlength_cons;
                              pose proof (Zlength_nonneg states); lia)).
    rewrite Znth0_cons in Hsteps.
    replace (0 + 1) with 1 in Hsteps by lia.
    rewrite Znth_cons in Hsteps by lia.
    replace (1 - 1) with 0 in Hsteps by lia.
    rewrite Znth0_cons in Hsteps.
    exact Hsteps. }
  split.
  - rewrite Znth0_cons.
    apply one_apple_cut_bounds_back__dyadic_final with b; assumption.
  - rewrite Znth0_cons.
    rewrite Hlast.
    rewrite <- Htail_mass.
    rewrite Znth0_cons.
    apply one_apple_cut_mass__dyadic_final; assumption.
Qed.
Lemma mass_permutation__dyadic_final :
  forall depth xs ys,
    Permutation xs ys ->
    fold_right (fun e total => 2 ^ (depth - e) + total) 0 xs =
    fold_right (fun e total => 2 ^ (depth - e) + total) 0 ys.
Proof.
  intros depth xs ys Hperm.
  induction Hperm; simpl; lia.
Qed.
Lemma mass_app__dyadic_final :
  forall depth xs ys,
    fold_right (fun e total => 2 ^ (depth - e) + total) 0 (xs ++ ys) =
    fold_right (fun e total => 2 ^ (depth - e) + total) 0 xs +
    fold_right (fun e total => 2 ^ (depth - e) + total) 0 ys.
Proof.
  intros depth xs ys.
  induction xs as [|x xs IH]; simpl; lia.
Qed.
Lemma constant_share_concat_mass__dyadic_final :
  forall depth shares w,
    Forall
      (fun sh =>
         fold_right (fun e total => 2 ^ (depth - e) + total) 0 sh = w)
      shares ->
    fold_right (fun e total => 2 ^ (depth - e) + total) 0
      (concat shares) = Zlength shares * w.
Proof.
  intros depth shares w Hshares.
  induction Hshares as [|sh shares Hsh Hshares IH]; simpl.
  - reflexivity.
  - rewrite mass_app__dyadic_final, Hsh, IH, Zlength_cons. ring.
Qed.
Lemma equal_shares_total_mass__dyadic_final :
  forall m pieces shares depth,
    0 < m ->
    Zlength shares = m ->
    Permutation pieces (concat shares) ->
    (forall i j, 0 <= i < m -> 0 <= j < m ->
       fold_right (fun e total => 2 ^ (depth - e) + total) 0
         (Znth i shares nil) =
       fold_right (fun e total => 2 ^ (depth - e) + total) 0
         (Znth j shares nil)) ->
    exists w,
      fold_right (fun e total => 2 ^ (depth - e) + total) 0 pieces =
      m * w.
Proof.
  intros m pieces shares depth Hm Hlen Hperm Hequal.
  set (w := fold_right (fun e total => 2 ^ (depth - e) + total) 0
             (Znth 0 shares nil)).
  assert (Hall : Forall
      (fun sh => fold_right (fun e total => 2 ^ (depth - e) + total) 0 sh = w)
      shares).
  { apply Forall_forall.
    intros sh Hin.
    apply In_nth with (d := nil) in Hin.
    destruct Hin as [i [Hi Hnth]].
    specialize (Hequal (Z.of_nat i) 0).
    assert (Hzi : 0 <= Z.of_nat i < m).
    { rewrite <- Hlen, Zlength_correct. lia. }
    specialize (Hequal Hzi ltac:(lia)).
    unfold Znth in Hequal.
    rewrite Nat2Z.id in Hequal.
    rewrite Hnth in Hequal.
    exact Hequal. }
  exists w.
  rewrite (mass_permutation__dyadic_final depth pieces (concat shares) Hperm).
  rewrite (constant_share_concat_mass__dyadic_final depth shares w Hall).
  rewrite Hlen. reflexivity.
Qed.
Lemma Zlength_Zrange_aux__dyadic_final : forall low count,
  Zlength (Zrange_aux low count) = Z.of_nat count.
Proof.
  intros low count. revert low.
  induction count as [|count IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__dyadic_final : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle.
  unfold Zrange.
  rewrite Zlength_Zrange_aux__dyadic_final.
  lia.
Qed.
Lemma fold_mapped_zero_mass__dyadic_final :
  forall xs depth,
    fold_right (fun e total => 2 ^ (depth - e) + total) 0
      (map (fun _ : Z => 0) xs) = Zlength xs * 2 ^ depth.
Proof.
  induction xs as [|x xs IH]; intros depth; simpl.
  - reflexivity.
  - rewrite IH, Zlength_cons.
    replace (depth - 0) with depth by lia.
    unfold Z.succ. ring.
Qed.
Lemma fold_zero_map_range_mass__dyadic_final :
  forall n depth,
    0 <= n ->
    fold_right (fun e total => 2 ^ (depth - e) + total) 0
      (Zmap_range (fun _ => 0) n) = n * 2 ^ depth.
Proof.
  intros n depth Hn.
  unfold Zmap_range.
  rewrite fold_mapped_zero_mass__dyadic_final.
  rewrite Zlength_Zrange__dyadic_final by lia.
  ring.
Qed.
Lemma one_apple_cut_after_nonempty__dyadic_final :
  forall before after, OneAppleCut before after -> after <> nil.
Proof.
  intros before after Hcut.
  unfold OneAppleCut in Hcut.
  destruct Hcut as [prefix [e [suffix [_ ->]]]].
  destruct prefix; simpl; discriminate.
Qed.
Lemma indexed_cut_chain_nonempty__dyadic_final :
  forall states,
    0 < Zlength states ->
    (forall i, 0 <= i < Zlength states - 1 ->
       OneAppleCut (Znth i states nil) (Znth (i + 1) states nil)) ->
    Znth 0 states nil <> nil ->
    Znth (Zlength states - 1) states nil <> nil.
Proof.
  induction states as [|a states IH]; intros Hlen Hsteps Hfirst.
  { rewrite Zlength_nil in Hlen. lia. }
  destruct states as [|b states].
  { rewrite !Znth0_cons. exact Hfirst. }
  assert (Hab : OneAppleCut a b).
  { specialize (Hsteps 0).
    assert (Hidx : 0 <= 0 < Zlength (a :: b :: states) - 1).
    { rewrite !Zlength_cons.
      pose proof (Zlength_nonneg states).
      unfold Z.succ. lia. }
    specialize (Hsteps Hidx).
    change (OneAppleCut (Znth 0 (a :: b :: states) nil)
                         (Znth 1 (a :: b :: states) nil)) in Hsteps.
    rewrite Znth0_cons in Hsteps.
    rewrite (Znth_cons nil 1 a (b :: states)) in Hsteps by lia.
    replace (1 - 1) with 0 in Hsteps by lia.
    rewrite Znth0_cons in Hsteps.
    exact Hsteps. }
  assert (Hlast :
      Znth (Zlength (a :: b :: states) - 1) (a :: b :: states) nil =
      Znth (Zlength (b :: states) - 1) (b :: states) nil).
  { rewrite Zlength_cons.
    rewrite Znth_cons by
      (rewrite Zlength_cons; pose proof (Zlength_nonneg states);
       unfold Z.succ; lia).
    f_equal. lia. }
  rewrite Hlast.
  apply IH.
  - rewrite Zlength_cons.
    pose proof (Zlength_nonneg states). unfold Z.succ. lia.
  - intros i Hi.
    specialize (Hsteps (i + 1)).
    assert (Hidx : 0 <= i + 1 < Zlength (a :: b :: states) - 1).
    { destruct Hi as [Hi0 Hilt]. split; [lia |].
      rewrite Zlength_cons in Hilt.
      replace (Z.succ (Zlength states) - 1) with (Zlength states) in Hilt
        by (unfold Z.succ; lia).
      rewrite !Zlength_cons.
      replace (Z.succ (Z.succ (Zlength states)) - 1)
        with (Zlength states + 1) by (unfold Z.succ; lia).
      lia. }
    specialize (Hsteps Hidx).
    rewrite (Znth_cons nil (i + 1) a (b :: states)) in Hsteps by lia.
    rewrite (Znth_cons nil (i + 1 + 1) a (b :: states)) in Hsteps by lia.
    replace (i + 1 - 1) with i in Hsteps by lia.
    replace (i + 1 + 1 - 1) with (i + 1) in Hsteps by lia.
    exact Hsteps.
  - rewrite Znth0_cons.
    eapply one_apple_cut_after_nonempty__dyadic_final; exact Hab.
Qed.
Lemma achievable_equal_mass_equation__dyadic_final :
  forall n m cuts,
    0 < n -> 0 < m -> 0 <= cuts -> AchievableAppleDivision n m cuts ->
    exists depth w,
      0 <= depth /\ n * 2 ^ depth = m * w.
Proof.
  intros n m cuts Hn Hm Hcuts Hach.
  unfold AchievableAppleDivision in Hach.
  destruct Hach as [states [Hstates_len [Hinitial [Hsteps Hequal]]]].
  unfold EqualDyadicShares in Hequal.
  destruct Hequal as [shares [depth [Hshares_len [Hperm [Hbounds Hequal]]]]].
  assert (Hstates_pos : 0 < Zlength states) by lia.
  assert (Hlast : Zlength states - 1 = cuts) by lia.
  assert (Hupper : Forall (fun e => e <= depth) (Znth cuts states nil)).
  { rewrite Forall_forall in Hbounds |- *.
    intros e Hin. specialize (Hbounds e Hin). lia. }
  rewrite <- Hlast in Hupper.
  assert (Hsteps' : forall i, 0 <= i < Zlength states - 1 ->
      OneAppleCut (Znth i states nil) (Znth (i + 1) states nil)).
  { intros i Hi. apply Hsteps. lia. }
  pose proof (indexed_cut_chain_mass__dyadic_final states depth
    Hstates_pos Hsteps' Hupper) as Hchain.
  destruct Hchain as [Hinitial_upper Hmass].
  assert (Hfinal_nonempty : Znth cuts states nil <> nil).
  { rewrite <- Hlast.
    eapply indexed_cut_chain_nonempty__dyadic_final; try eassumption.
    rewrite Hinitial.
    unfold Zmap_range.
    destruct (Zrange 0 n) eqn:Hr.
    - assert (0 = Zlength (Zrange 0 n)) by (rewrite Hr; reflexivity).
      rewrite Zlength_Zrange__dyadic_final in H by lia. lia.
    - simpl; discriminate. }
  assert (Hdepth : 0 <= depth).
  { destruct (Znth cuts states nil) as [|e es] eqn:Hpieces.
    - exfalso. apply Hfinal_nonempty. reflexivity.
    - inversion Hbounds; lia. }
  pose proof (equal_shares_total_mass__dyadic_final m
    (Znth cuts states nil) shares depth Hm Hshares_len Hperm Hequal)
    as Htotal.
  destruct Htotal as [w Htotal].
  exists depth, w. split; [exact Hdepth |].
  rewrite <- Htotal.
  rewrite <- Hlast.
  rewrite <- Hmass.
  rewrite Hinitial.
  symmetry. apply fold_zero_map_range_mass__dyadic_final. lia.
Qed.
Lemma dyadic_share_denominator_characterization__dyadic_final :
  forall n m cuts,
    0 < n -> 0 < m -> 0 <= cuts -> AchievableAppleDivision n m cuts ->
    PowerOfTwo (m / GcdValue n m).
Proof.
  intros n m cuts Hn Hm Hcuts Hach.
  pose proof (achievable_equal_mass_equation__dyadic_final
    n m cuts Hn Hm Hcuts Hach) as Hmass.
  destruct Hmass as [depth [w [Hdepth Hmass]]].
  unfold GcdValue.
  set (g := Z.gcd n m).
  assert (Hg_nonneg : 0 <= g) by (unfold g; apply Z.gcd_nonneg).
  assert (Hg_n : (g | n)) by (unfold g; apply Z.gcd_divide_l).
  assert (Hg_m : (g | m)) by (unfold g; apply Z.gcd_divide_r).
  assert (Hg_pos : 0 < g).
  { destruct Hg_m as [q Hq].
    destruct (Z.eq_dec g 0) as [-> | Hg0].
    - simpl in Hq. lia.
    - lia. }
  assert (Hn_factor : n = g * (n / g)).
  { apply Zdivide_Zdiv_eq; assumption. }
  assert (Hm_factor : m = g * (m / g)).
  { apply Zdivide_Zdiv_eq; assumption. }
  assert (Hred_pos : 0 < m / g).
  { rewrite Hm_factor in Hm.
    nia. }
  assert (Hcancel : (n / g) * 2 ^ depth = (m / g) * w).
  { apply Z.mul_reg_l with g; [lia |].
    rewrite !Z.mul_assoc.
    rewrite <- Hn_factor, <- Hm_factor.
    exact Hmass. }
  assert (Hdiv_product : (m / g | (n / g) * 2 ^ depth)).
  { exists w. rewrite (Z.mul_comm w (m / g)). exact Hcancel. }
  assert (Hrel : rel_prime (n / g) (m / g)).
  { apply Zis_gcd_rel_prime; try lia.
    unfold g. apply Zgcd_is_gcd. }
  assert (Hdiv_power : (m / g | 2 ^ depth)).
  { eapply Gauss; [exact Hdiv_product |].
    apply rel_prime_sym. exact Hrel. }
  destruct (Zdivide_power_2 (m / g) 2 depth Hdepth ltac:(lia)
    prime_2 Hdiv_power) as [k Hk].
  unfold PowerOfTwo.
  exists k. split.
  - destruct (Z_lt_ge_dec k 0); [|lia].
    rewrite Z.pow_neg_r in Hk by lia. lia.
  - exact Hk.
Qed.
Lemma nondyadic_no_achievable_division__dyadic_final :
  forall n m,
    0 < n -> 0 < m -> ~ PowerOfTwo (m / GcdValue n m) ->
    forall cuts, ~ (0 <= cuts /\ AchievableAppleDivision n m cuts).
Proof.
  intros n m Hn Hm Hnot cuts [Hcuts Hach].
  apply Hnot.
  eapply dyadic_share_denominator_characterization__dyadic_final;
    eassumption.
Qed.
Lemma reduced_denominator_positive__dyadic_final :
  forall n m, 0 < n -> 0 < m -> 0 < m / GcdValue n m.
Proof.
  intros n m Hn Hm.
  unfold GcdValue.
  set (g := Z.gcd n m).
  assert (Hg_nonneg : 0 <= g) by (unfold g; apply Z.gcd_nonneg).
  assert (Hg_m : (g | m)) by (unfold g; apply Z.gcd_divide_r).
  assert (Hg_pos : 0 < g).
  { destruct Hg_m as [q Hq].
    destruct (Z.eq_dec g 0) as [-> | Hg0].
    - simpl in Hq. lia.
    - lia. }
  assert (Hm_factor : m = g * (m / g)).
  { apply Zdivide_Zdiv_eq; assumption. }
  rewrite Hm_factor in Hm. nia.
Qed.
Lemma gcd_value_positive__dyadic_final :
  forall n m, 0 < n -> 0 < m -> 0 < GcdValue n m.
Proof.
  intros n m Hn Hm.
  unfold GcdValue.
  pose proof (Z.gcd_nonneg n m) as Hg.
  pose proof (Z.gcd_divide_r n m) as Hdiv.
  destruct Hdiv as [q Hq].
  destruct (Z.eq_dec (Z.gcd n m) 0) as [Hz | Hz]; [|lia].
  rewrite Hz in Hq. simpl in Hq. lia.
Qed.
Lemma split_top_depth_pieces__dyadic_final :
  forall k pieces,
    Forall (fun e => 0 <= e <= Z.of_nat (S k)) pieces ->
    exists u lower,
      0 <= u /\
      Permutation pieces
        (repeat (Z.of_nat (S k)) (Z.to_nat u) ++ lower) /\
      Zlength pieces = u + Zlength lower /\
      Forall (fun e => 0 <= e <= Z.of_nat k) lower /\
      fold_right
        (fun e total => 2 ^ (Z.of_nat (S k) - e) + total) 0 pieces =
      u + 2 * fold_right
        (fun e total => 2 ^ (Z.of_nat k - e) + total) 0 lower.
Proof.
  intros k pieces Hbounds.
  induction Hbounds as [|e pieces He Hbounds IH].
  - exists 0, nil. simpl. repeat split; try lia; constructor.
  - destruct IH as [u [lower [Hu [Hperm [Hlen [Hlower Hmass]]]]]].
    destruct (Z.eq_dec e (Z.of_nat (S k))) as [Heq | Hneq].
    + exists (u + 1), lower.
      subst e. repeat split; try lia.
      * eapply Permutation_trans; [apply perm_skip; exact Hperm |].
        assert (Hnat : Z.to_nat (u + 1) = S (Z.to_nat u)) by lia.
        rewrite Hnat. reflexivity.
      * rewrite Zlength_cons, Hlen. unfold Z.succ. lia.
      * exact Hlower.
      * rewrite Nat2Z.inj_succ in Hmass |- *.
        simpl.
        replace (2 ^ (Z.succ (Z.of_nat k) - Z.succ (Z.of_nat k)))
          with 1 by (rewrite Z.sub_diag; reflexivity).
        rewrite Hmass.
        set (M := fold_right
          (fun e total => 2 ^ (Z.of_nat k - e) + total) 0 lower) in *.
        change (1 + (u + 2 * M) = u + 1 + 2 * M).
        lia.
    + exists u, (e :: lower).
      repeat split; try lia.
      * eapply Permutation_trans; [apply perm_skip; exact Hperm |].
        apply Permutation_middle.
      * rewrite !Zlength_cons, Hlen. unfold Z.succ. lia.
      * constructor; [|exact Hlower].
        rewrite Nat2Z.inj_succ in He. lia.
      * rewrite Nat2Z.inj_succ in Hmass |- *.
        simpl. rewrite Hmass.
        rewrite Nat2Z.inj_succ in He.
        replace (Z.succ (Z.of_nat k) - e)
          with (Z.succ (Z.of_nat k - e)) by lia.
        rewrite Z.pow_succ_r by lia.
        set (P := 2 ^ (Z.of_nat k - e)) in *.
        set (M := fold_right
          (fun x total => 2 ^ (Z.of_nat k - x) + total) 0 lower) in *.
        change (2 * P + (u + 2 * M) = u + 2 * (P + M)).
        ring.
Qed.
Lemma Zlength_repeat_Z__dyadic_final :
  forall (x n : Z), 0 <= n -> Zlength (repeat x (Z.to_nat n)) = n.
Proof.
  intros x n Hn.
  rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma repeat_depth_bounds__dyadic_final :
  forall k n,
    0 <= n ->
    Forall (fun e => 0 <= e <= Z.of_nat k)
      (repeat (Z.of_nat k) (Z.to_nat n)).
Proof.
  intros k n Hn.
  apply Forall_forall. intros e He.
  apply repeat_spec in He. subst. lia.
Qed.
Lemma repeat_depth_mass__dyadic_final :
  forall k n,
    0 <= n ->
    fold_right (fun e total => 2 ^ (Z.of_nat k - e) + total) 0
      (repeat (Z.of_nat k) (Z.to_nat n)) = n.
Proof.
  intros k n Hn.
  assert (Hnat : forall r,
      fold_right (fun e total => 2 ^ (Z.of_nat k - e) + total) 0
        (repeat (Z.of_nat k) r) = Z.of_nat r).
  { induction r as [|r IH].
    - reflexivity.
    - change
        (2 ^ (Z.of_nat k - Z.of_nat k) +
         fold_right (fun e total => 2 ^ (Z.of_nat k - e) + total) 0
           (repeat (Z.of_nat k) r) = Z.of_nat (S r)).
      rewrite IH, Z.sub_diag, Z.pow_0_r, Nat2Z.inj_succ.
      rewrite <- Z.add_1_r. lia. }
  rewrite Hnat, Z2Nat.id by lia. reflexivity.
Qed.
Lemma zero_depth_mass_length__dyadic_final :
  forall pieces,
    Forall (fun e => e = 0) pieces ->
    fold_right (fun e total => 2 ^ (0 - e) + total) 0 pieces =
    Zlength pieces.
Proof.
  induction pieces as [|e pieces IH]; intros Hzero.
  - reflexivity.
  - inversion Hzero as [|? ? He Htail]. subst e.
    change
      (2 ^ (0 - 0) +
       fold_right (fun e total => 2 ^ (0 - e) + total) 0 pieces =
       Zlength (0 :: pieces)).
    rewrite IH by exact Htail.
    rewrite Zlength_cons.
    replace (0 - 0) with 0 by lia.
    rewrite Z.pow_0_r, Z.add_comm.
    apply Z.add_1_r.
Qed.
Lemma dyadic_representation_piece_lower_bound__dyadic_final :
  forall k pieces q,
    Forall (fun e => 0 <= e <= Z.of_nat k) pieces ->
    fold_right (fun e total => 2 ^ (Z.of_nat k - e) + total) 0 pieces = q ->
    (let fix cost (j : nat) (x : Z) : Z :=
       match j with
       | O => x
       | S j' => x mod 2 + cost j' (x / 2)
       end
     in cost k q) <= Zlength pieces.
Proof.
  induction k as [|k IH]; intros pieces q Hbounds Hmass.
  - simpl in *.
    assert (Hallzero : Forall (fun e => e = 0) pieces).
    { rewrite Forall_forall in Hbounds |- *.
      intros e Hin. specialize (Hbounds e Hin). lia. }
    clear Hbounds.
    pose proof (zero_depth_mass_length__dyadic_final pieces Hallzero) as Hzero.
    change
      (fold_right (fun e total => 2 ^ (- e) + total) 0 pieces =
       Zlength pieces) in Hzero.
    rewrite Hmass in Hzero. lia.
  - pose proof (split_top_depth_pieces__dyadic_final k pieces Hbounds)
      as Hsplit.
    destruct Hsplit as [u [lower [Hu [_ [Hlen [Hlower Hdecomp]]]]]].
    set (v := fold_right
      (fun e total => 2 ^ (Z.of_nat k - e) + total) 0 lower).
    assert (Hv : 0 <= v).
    { unfold v. clear -Hlower.
      induction Hlower; simpl; [lia |].
      pose proof (Z.pow_nonneg 2 (Z.of_nat k - x) ltac:(lia)). lia. }
    assert (Hq : q = u + 2 * v) by (rewrite <- Hmass; exact Hdecomp).
    set (merged := lower ++ repeat (Z.of_nat k) (Z.to_nat (u / 2))).
    assert (Hu2 : 0 <= u / 2) by (apply Z_div_pos; lia).
    assert (Hmerged_bounds :
        Forall (fun e => 0 <= e <= Z.of_nat k) merged).
    { unfold merged. apply Forall_app. split; [exact Hlower |].
      apply repeat_depth_bounds__dyadic_final. exact Hu2. }
    assert (Hmerged_mass :
        fold_right (fun e total => 2 ^ (Z.of_nat k - e) + total) 0
          merged = q / 2).
    { unfold merged.
      rewrite mass_app__dyadic_final.
      rewrite repeat_depth_mass__dyadic_final by exact Hu2.
      fold v.
      rewrite Hq.
      assert (Hdiv : (u + 2 * v) / 2 = u / 2 + v).
      { replace (u + 2 * v) with (u + v * 2) by ring.
        rewrite Z_div_plus_full by lia. reflexivity. }
      rewrite Hdiv. ring. }
    specialize (IH merged (q / 2) Hmerged_bounds Hmerged_mass).
    simpl.
    assert (Hmerged_len : Zlength merged = Zlength lower + u / 2).
    { unfold merged. rewrite Zlength_app.
      rewrite Zlength_repeat_Z__dyadic_final by exact Hu2. reflexivity. }
    rewrite Hmerged_len in IH.
    assert (Hqmod : q mod 2 = u mod 2).
    { rewrite Hq.
      replace (u + 2 * v) with (u + v * 2) by ring.
      apply Z_mod_plus_full. }
    pose proof (Z.div_mod u 2 ltac:(lia)) as Hudiv.
    rewrite Hlen.
    simpl.
    set (C := (fix cost (j : nat) (x : Z) : Z :=
      match j with
      | O => x
      | S j' => x mod 2 + cost j' (x / 2)
      end) k (q / 2)) in *.
    set (L := Zlength lower) in *.
    lia.
Qed.
Lemma one_apple_cut_length__dyadic_final :
  forall before after,
    OneAppleCut before after -> Zlength after = Zlength before + 1.
Proof.
  intros before after Hcut.
  unfold OneAppleCut in Hcut.
  destruct Hcut as [prefix [e [suffix [-> ->]]]].
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  repeat rewrite Zlength_nil.
  unfold Z.succ. lia.
Qed.
Lemma indexed_cut_chain_length__dyadic_final :
  forall states,
    0 < Zlength states ->
    (forall i, 0 <= i < Zlength states - 1 ->
       OneAppleCut (Znth i states nil) (Znth (i + 1) states nil)) ->
    Zlength (Znth (Zlength states - 1) states nil) =
    Zlength (Znth 0 states nil) + (Zlength states - 1).
Proof.
  induction states as [|a states IH]; intros Hlen Hsteps.
  { rewrite Zlength_nil in Hlen. lia. }
  destruct states as [|b states].
  { rewrite !Znth0_cons. simpl. lia. }
  assert (Hab : OneAppleCut a b).
  { specialize (Hsteps 0).
    assert (Hidx : 0 <= 0 < Zlength (a :: b :: states) - 1).
    { rewrite !Zlength_cons.
      pose proof (Zlength_nonneg states). unfold Z.succ. lia. }
    specialize (Hsteps Hidx).
    change (OneAppleCut (Znth 0 (a :: b :: states) nil)
                         (Znth 1 (a :: b :: states) nil)) in Hsteps.
    rewrite Znth0_cons in Hsteps.
    rewrite (Znth_cons nil 1 a (b :: states)) in Hsteps by lia.
    replace (1 - 1) with 0 in Hsteps by lia.
    rewrite Znth0_cons in Hsteps. exact Hsteps. }
  assert (Htail_steps : forall i,
      0 <= i < Zlength (b :: states) - 1 ->
      OneAppleCut (Znth i (b :: states) nil)
                  (Znth (i + 1) (b :: states) nil)).
  { intros i Hi.
    specialize (Hsteps (i + 1)).
    assert (Hidx : 0 <= i + 1 < Zlength (a :: b :: states) - 1).
    { destruct Hi as [Hi0 Hilt]. split; [lia |].
      rewrite Zlength_cons in Hilt.
      replace (Z.succ (Zlength states) - 1) with (Zlength states) in Hilt
        by (unfold Z.succ; lia).
      rewrite !Zlength_cons.
      replace (Z.succ (Z.succ (Zlength states)) - 1)
        with (Zlength states + 1) by (unfold Z.succ; lia).
      lia. }
    specialize (Hsteps Hidx).
    rewrite (Znth_cons nil (i + 1) a (b :: states)) in Hsteps by lia.
    rewrite (Znth_cons nil (i + 1 + 1) a (b :: states)) in Hsteps by lia.
    replace (i + 1 - 1) with i in Hsteps by lia.
    replace (i + 1 + 1 - 1) with (i + 1) in Hsteps by lia.
    exact Hsteps. }
  assert (Htail_len : 0 < Zlength (b :: states)).
  { rewrite Zlength_cons. pose proof (Zlength_nonneg states).
    unfold Z.succ. lia. }
  specialize (IH Htail_len Htail_steps).
  assert (Hlast :
      Znth (Zlength (a :: b :: states) - 1) (a :: b :: states) nil =
      Znth (Zlength (b :: states) - 1) (b :: states) nil).
  { rewrite Zlength_cons.
    rewrite Znth_cons by
      (rewrite Zlength_cons; pose proof (Zlength_nonneg states);
       unfold Z.succ; lia).
    f_equal. lia. }
  rewrite Hlast, Znth0_cons.
  rewrite Znth0_cons in IH.
  rewrite IH.
  rewrite one_apple_cut_length__dyadic_final with (before := a) (after := b)
    by exact Hab.
  repeat rewrite Zlength_cons.
  unfold Z.succ. lia.
Qed.
Lemma concat_length_lower_bound__dyadic_final :
  forall (shares : list (list Z)) (c : Z),
    Forall (fun sh => c <= Zlength sh) shares ->
    Zlength shares * c <= Zlength (concat shares).
Proof.
  intros shares c Hshares.
  induction Hshares as [|sh shares Hsh Hshares IH].
  - rewrite Zlength_nil. simpl. apply Z.le_refl.
  - change
      (Zlength (sh :: shares) * c <= Zlength (sh ++ concat shares)).
    rewrite Zlength_cons, Zlength_app.
    rewrite <- Z.add_1_r.
    replace ((Zlength shares + 1) * c)
      with (Zlength shares * c + c) by ring.
    lia.
Qed.
Lemma equal_dyadic_shares_piece_lower_bound__dyadic_final :
  forall m pieces shares depth,
    0 < m -> 0 <= depth ->
    Zlength shares = m ->
    Permutation pieces (concat shares) ->
    Forall (fun e => 0 <= e <= depth) pieces ->
    (forall i j, 0 <= i < m -> 0 <= j < m ->
       fold_right (fun e total => 2 ^ (depth - e) + total) 0
         (Znth i shares nil) =
       fold_right (fun e total => 2 ^ (depth - e) + total) 0
         (Znth j shares nil)) ->
    let w := fold_right (fun e total => 2 ^ (depth - e) + total) 0
               (Znth 0 shares nil) in
    m *
      (let fix cost (j : nat) (x : Z) : Z :=
         match j with
         | O => x
         | S j' => x mod 2 + cost j' (x / 2)
         end
       in cost (Z.to_nat depth) w) <= Zlength pieces.
Proof.
  intros m pieces shares depth Hm Hdepth Hslen Hperm Hbounds Hequal.
  cbn zeta.
  set (w := fold_right (fun e total => 2 ^ (depth - e) + total) 0
             (Znth 0 shares nil)).
  set (c := (fix cost (j : nat) (x : Z) : Z :=
    match j with
    | O => x
    | S j' => x mod 2 + cost j' (x / 2)
    end) (Z.to_nat depth) w).
  assert (Hall : Forall (fun sh => c <= Zlength sh) shares).
  { apply Forall_forall. intros sh Hshin.
    pose proof Hshin as Hshin0.
    apply In_nth with (d := nil) in Hshin.
    destruct Hshin as [idx [Hidx Hnth]].
    assert (Hzidx : 0 <= Z.of_nat idx < m).
    { rewrite <- Hslen, Zlength_correct. lia. }
    assert (Hshmass :
        fold_right (fun e total => 2 ^ (depth - e) + total) 0 sh = w).
    { specialize (Hequal (Z.of_nat idx) 0 Hzidx ltac:(lia)).
      unfold Znth in Hequal. rewrite Nat2Z.id in Hequal.
      rewrite Hnth in Hequal. exact Hequal. }
    assert (Hshbounds : Forall (fun e => 0 <= e <= depth) sh).
    { rewrite Forall_forall in Hbounds |- *.
      intros e Hein. apply Hbounds.
      eapply Permutation_in; [apply Permutation_sym; exact Hperm |].
      apply in_concat. exists sh. split; [exact Hshin0 | exact Hein]. }
    pose proof (dyadic_representation_piece_lower_bound__dyadic_final
      (Z.to_nat depth) sh w) as Hlower.
    rewrite Z2Nat.id in Hlower by exact Hdepth.
    specialize (Hlower Hshbounds Hshmass).
    exact Hlower. }
  pose proof (concat_length_lower_bound__dyadic_final shares c Hall) as Hcat.
  rewrite Hslen in Hcat.
  assert (Hplen : Zlength pieces = Zlength (concat shares)).
  { rewrite !Zlength_correct. f_equal.
    apply Permutation_length. exact Hperm. }
  unfold c, w in *. lia.
Qed.
Lemma lift_dyadic_mass_one__dyadic_final :
  forall k pieces,
    Forall (fun e => 0 <= e <= Z.of_nat k) pieces ->
    fold_right
      (fun e total => 2 ^ (Z.of_nat (S k) - e) + total) 0 pieces =
    2 * fold_right
      (fun e total => 2 ^ (Z.of_nat k - e) + total) 0 pieces.
Proof.
  intros k pieces Hbounds.
  induction Hbounds as [|e pieces He Hbounds IH]; [reflexivity |].
  change
    (2 ^ (Z.of_nat (S k) - e) +
       fold_right
         (fun x total => 2 ^ (Z.of_nat (S k) - x) + total) 0 pieces =
     2 * (2 ^ (Z.of_nat k - e) +
       fold_right
         (fun x total => 2 ^ (Z.of_nat k - x) + total) 0 pieces)).
  rewrite IH, Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat k) - e)
    with (Z.succ (Z.of_nat k - e)) by lia.
  rewrite Z.pow_succ_r by lia.
  set (P := 2 ^ (Z.of_nat k - e)).
  set (M := fold_right
    (fun x total => 2 ^ (Z.of_nat k - x) + total) 0 pieces).
  change (2 * P + 2 * M = 2 * (P + M)). ring.
Qed.
Lemma minimal_share_representation_exists__dyadic_final :
  forall k q,
    0 <= q ->
    exists repr,
      Forall (fun e => 0 <= e <= Z.of_nat k) repr /\
      fold_right (fun e total => 2 ^ (Z.of_nat k - e) + total) 0 repr = q /\
      Zlength repr =
        (let fix cost (j : nat) (x : Z) : Z :=
           match j with
           | O => x
           | S j' => x mod 2 + cost j' (x / 2)
           end
         in cost k q).
Proof.
  induction k as [|k IH]; intros q Hq.
  - exists (repeat 0 (Z.to_nat q)).
    split.
    + apply repeat_depth_bounds__dyadic_final. exact Hq.
    + split.
      * apply repeat_depth_mass__dyadic_final. exact Hq.
      * rewrite Zlength_repeat_Z__dyadic_final by exact Hq. reflexivity.
  - assert (Hq2 : 0 <= q / 2) by (apply Z_div_pos; lia).
    specialize (IH (q / 2) Hq2).
    destruct IH as [lower [Hlower_bounds [Hlower_mass Hlower_len]]].
    set (r := q mod 2).
    assert (Hr : 0 <= r) by (unfold r; apply Z.mod_pos_bound; lia).
    assert (Hrlt : r < 2) by (unfold r; apply Z.mod_pos_bound; lia).
    exists (lower ++ repeat (Z.of_nat (S k)) (Z.to_nat r)).
    split.
    + apply Forall_app. split.
      * rewrite Nat2Z.inj_succ.
        rewrite Forall_forall in Hlower_bounds |- *.
        intros e Hein. specialize (Hlower_bounds e Hein). lia.
      * apply repeat_depth_bounds__dyadic_final. exact Hr.
    + split.
      * rewrite mass_app__dyadic_final.
        rewrite lift_dyadic_mass_one__dyadic_final by exact Hlower_bounds.
        rewrite Hlower_mass.
        rewrite repeat_depth_mass__dyadic_final by exact Hr.
        unfold r.
        pose proof (Z.div_mod q 2 ltac:(lia)) as Hdiv.
        lia.
      * rewrite Zlength_app, Hlower_len.
        rewrite Zlength_repeat_Z__dyadic_final by exact Hr.
        set (C := (fix cost (j : nat) (x : Z) : Z :=
          match j with
          | O => x
          | S j' => x mod 2 + cost j' (x / 2)
          end) k (q / 2)).
        change (C + r = q mod 2 + C).
        unfold r. ring.
Qed.
Lemma batch_cut_permuted_occurrences__dyadic_final :
  forall (e : Z) (r : nat) (current rest : list Z),
    Permutation current (repeat e r ++ rest) ->
    exists final,
      clos_refl_trans_n1 (list Z) OneAppleCut current final /\
      Permutation final (repeat (e + 1) (2 * r) ++ rest).
Proof.
  intros e r. induction r as [|r IH]; intros current rest Hperm.
  - exists current. split; [constructor |]. simpl in *. exact Hperm.
  - simpl in Hperm.
    assert (Hein : In e current).
    { eapply Permutation_in; [apply Permutation_sym; exact Hperm |].
      simpl; auto. }
    apply in_split in Hein.
    destruct Hein as [prefix [suffix Hcurrent]].
    subst current.
    set (next := prefix ++ [e + 1; e + 1] ++ suffix).
    assert (Hstep : OneAppleCut (prefix ++ e :: suffix) next).
    { unfold OneAppleCut, next.
      exists prefix, e, suffix. split; reflexivity. }
    set (tail := repeat e r ++ rest).
    assert (Hremove : Permutation tail (prefix ++ suffix)).
    { unfold tail.
      apply Permutation_cons_inv with e.
      eapply Permutation_trans.
      - apply Permutation_sym. exact Hperm.
      - apply Permutation_sym. apply Permutation_middle. }
    assert (Hnext :
        Permutation next (repeat e r ++ ([e + 1; e + 1] ++ rest))).
    { unfold next.
      rewrite app_assoc.
      eapply Permutation_trans with
        (l' := (([e + 1; e + 1] ++ prefix) ++ suffix)).
      - apply Permutation_app_tail.
        apply Permutation_app_comm.
      - eapply Permutation_trans with
          (l' := [e + 1; e + 1] ++ tail).
        + change (Permutation
            ([e + 1; e + 1] ++ (prefix ++ suffix))
            ([e + 1; e + 1] ++ tail)).
          apply Permutation_app_head. apply Permutation_sym. exact Hremove.
        + unfold tail.
          repeat rewrite app_assoc.
          apply Permutation_app_tail.
          apply Permutation_app_comm. }
    specialize (IH next ([e + 1; e + 1] ++ rest) Hnext).
    destruct IH as [final [Hclosure Hfinal]].
    exists final. split.
    + apply clos_rt_rtn1.
      eapply rt_trans.
      * apply rt_step. exact Hstep.
      * apply clos_rtn1_rt. exact Hclosure.
    + eapply Permutation_trans; [exact Hfinal |].
      replace (2 * S r)%nat with (2 * r + 2)%nat by lia.
      rewrite repeat_app.
      simpl.
      rewrite <- app_assoc.
      reflexivity.
Qed.
Lemma all_zero_list_repeat__dyadic_final :
  forall pieces,
    Forall (fun e : Z => e = 0) pieces ->
    pieces = repeat 0 (length pieces).
Proof.
  induction pieces as [|e pieces IH]; intros Hall; [reflexivity |].
  inversion Hall as [|? ? He Htail]. subst e.
  simpl. f_equal. apply IH. exact Htail.
Qed.
Lemma dyadic_mass_target_reachable__dyadic_final :
  forall k n target,
    0 <= n ->
    Forall (fun e => 0 <= e <= Z.of_nat k) target ->
    fold_right (fun e total => 2 ^ (Z.of_nat k - e) + total) 0 target =
      n * 2 ^ Z.of_nat k ->
    exists final,
      clos_refl_trans_n1 (list Z) OneAppleCut
        (repeat 0 (Z.to_nat n)) final /\
      Permutation final target.
Proof.
  induction k as [|k IH]; intros n target Hn Hbounds Hmass.
  - assert (Hallzero : Forall (fun e : Z => e = 0) target).
    { rewrite Forall_forall in Hbounds |- *.
      intros e Hein. specialize (Hbounds e Hein). lia. }
    pose proof (zero_depth_mass_length__dyadic_final target Hallzero) as Hlen.
    replace (n * 2 ^ Z.of_nat 0) with n in Hmass
      by (rewrite Z.pow_0_r; ring).
    change
      (fold_right (fun e total => 2 ^ (0 - e) + total) 0 target = n)
      in Hmass.
    rewrite Hmass in Hlen.
    exists (repeat 0 (Z.to_nat n)). split; [constructor |].
    rewrite (all_zero_list_repeat__dyadic_final target Hallzero).
    rewrite Zlength_correct in Hlen.
    assert (Hnat : length target = Z.to_nat n) by lia.
    now rewrite Hnat.
  - pose proof (split_top_depth_pieces__dyadic_final k target Hbounds)
      as Hsplit.
    destruct Hsplit as
      [u [lower [Hu [Hperm [Hlen [Hlower Hdecomp]]]]]].
    set (v := fold_right
      (fun e total => 2 ^ (Z.of_nat k - e) + total) 0 lower).
    assert (Hu_even : u mod 2 = 0).
    { rewrite Hdecomp in Hmass.
      rewrite Nat2Z.inj_succ in Hmass.
      rewrite Z.pow_succ_r in Hmass by lia.
      assert (Heq : u + 2 * v = 2 * (n * 2 ^ Z.of_nat k)).
      { unfold v. rewrite Hmass. ring. }
      replace u with (2 * (n * 2 ^ Z.of_nat k - v)) by lia.
      rewrite Z.mul_comm.
      apply Z.mod_mul. lia. }
    assert (Hu2 : 0 <= u / 2) by (apply Z_div_pos; lia).
    assert (Hu_double : u = 2 * (u / 2)).
    { pose proof (Z.div_mod u 2 ltac:(lia)) as Hdiv. lia. }
    set (merged := lower ++ repeat (Z.of_nat k) (Z.to_nat (u / 2))).
    assert (Hmerged_bounds :
        Forall (fun e => 0 <= e <= Z.of_nat k) merged).
    { unfold merged. apply Forall_app. split; [exact Hlower |].
      apply repeat_depth_bounds__dyadic_final. exact Hu2. }
    assert (Hmerged_mass :
        fold_right (fun e total => 2 ^ (Z.of_nat k - e) + total) 0 merged =
        n * 2 ^ Z.of_nat k).
    { unfold merged. rewrite mass_app__dyadic_final.
      rewrite repeat_depth_mass__dyadic_final by exact Hu2.
      fold v.
      rewrite Hdecomp in Hmass.
      rewrite Nat2Z.inj_succ in Hmass.
      rewrite Z.pow_succ_r in Hmass by lia.
      rewrite Hu_double in Hmass.
      nia. }
    specialize (IH n merged Hn Hmerged_bounds Hmerged_mass).
    destruct IH as [mid [Hreach Hmidperm]].
    assert (Hmidperm' :
        Permutation mid
          (repeat (Z.of_nat k) (Z.to_nat (u / 2)) ++ lower)).
    { eapply Permutation_trans; [exact Hmidperm |].
      unfold merged. apply Permutation_app_comm. }
    pose proof (batch_cut_permuted_occurrences__dyadic_final
      (Z.of_nat k) (Z.to_nat (u / 2)) mid lower Hmidperm') as Hbatch.
    destruct Hbatch as [final [Hbatchreach Hfinalperm]].
    exists final. split.
    + apply clos_rt_rtn1.
      eapply rt_trans.
      * apply clos_rtn1_rt. exact Hreach.
      * apply clos_rtn1_rt. exact Hbatchreach.
    + eapply Permutation_trans; [exact Hfinalperm |].
      eapply Permutation_trans.
      * replace (2 * Z.to_nat (u / 2))%nat with (Z.to_nat u).
        -- replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
           apply Permutation_refl.
        -- lia.
      * apply Permutation_sym. exact Hperm.
Qed.
Lemma Znth_app_single_before__dyadic_final :
  forall (A : Type) (l : list A) x d i,
    0 <= i < Zlength l ->
    Znth i (l ++ [x]) d = Znth i l d.
Proof.
  intros A l x d i Hi. unfold Znth.
  apply app_nth1. rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Znth_app_single_last__dyadic_final :
  forall (A : Type) (l : list A) x d,
    Znth (Zlength l) (l ++ [x]) d = x.
Proof.
  intros A l x d. unfold Znth. rewrite Zlength_correct.
  rewrite Nat2Z.id. rewrite app_nth2 by lia.
  replace (length l - length l)%nat with O by lia. reflexivity.
Qed.
Lemma closure_cut_trace__dyadic_final :
  forall start final,
    clos_refl_trans_n1 (list Z) OneAppleCut start final ->
    exists states,
      0 < Zlength states /\
      Znth 0 states nil = start /\
      Znth (Zlength states - 1) states nil = final /\
      (forall i, 0 <= i < Zlength states - 1 ->
        OneAppleCut (Znth i states nil) (Znth (i + 1) states nil)).
Proof.
  intros start final Hclosure. induction Hclosure as [|y z Hstep Hclosure IH].
  - exists [start]. split.
    + rewrite Zlength_cons, Zlength_nil. unfold Z.succ. lia.
    + split.
      * apply Znth0_cons.
      * split.
        -- rewrite Zlength_cons, Zlength_nil. unfold Z.succ.
           replace (0 + 1 - 1) with 0 by lia. apply Znth0_cons.
        -- intros i Hi. rewrite Zlength_cons, Zlength_nil in Hi.
           unfold Z.succ in Hi. lia.
  - destruct IH as [states [Hpos [Hfirst [Hlast Hchain]]]].
    exists (states ++ [z]).
    assert (Hnewlen : Zlength (states ++ [z]) = Zlength states + 1).
    { rewrite Zlength_app, Zlength_cons, Zlength_nil.
      unfold Z.succ. lia. }
    split.
    + rewrite Hnewlen. lia.
    + split.
      * rewrite Znth_app_single_before__dyadic_final by lia. exact Hfirst.
      * split.
        -- rewrite Hnewlen. replace (Zlength states + 1 - 1)
             with (Zlength states) by lia.
           apply Znth_app_single_last__dyadic_final.
        -- intros i Hi. rewrite Hnewlen in Hi.
           destruct (Z_lt_dec i (Zlength states - 1)) as [Hlt | Hnlt].
           ++ rewrite !Znth_app_single_before__dyadic_final.
              ** apply Hchain. lia.
              ** lia.
              ** lia.
           ++ assert (Hi_eq : i = Zlength states - 1) by lia. subst i.
              rewrite Znth_app_single_before__dyadic_final by lia.
              replace (Zlength states - 1 + 1) with (Zlength states) by lia.
              rewrite Znth_app_single_last__dyadic_final.
              rewrite Hlast. exact Hstep.
Qed.
Lemma zero_map_range_repeat__dyadic_final :
  forall n,
    0 <= n ->
    Zmap_range (fun _ => 0) n = repeat 0 (Z.to_nat n).
Proof.
  intros n Hn.
  assert (Hall : Forall (fun e : Z => e = 0)
      (Zmap_range (fun _ => 0) n)).
  { unfold Zmap_range. apply Forall_map. apply Forall_forall.
    intros; reflexivity. }
  pose proof (all_zero_list_repeat__dyadic_final _ Hall) as Heq.
  rewrite Heq.
  f_equal.
  pose proof (Zlength_Zrange__dyadic_final 0 n) as Hlen.
  unfold Zmap_range. rewrite length_map.
  rewrite Zlength_correct in Hlen. specialize (Hlen ltac:(lia)). lia.
Qed.
Lemma closure_equal_division_achievable__dyadic_final :
  forall n m final,
    0 <= n ->
    clos_refl_trans_n1 (list Z) OneAppleCut
      (repeat 0 (Z.to_nat n)) final ->
    EqualDyadicShares m final ->
    0 <= Zlength final - n /\
    AchievableAppleDivision n m (Zlength final - n).
Proof.
  intros n m final Hn Hclosure Hequal.
  destruct (closure_cut_trace__dyadic_final _ _ Hclosure)
    as [states [Hpos [Hfirst [Hlast Hchain]]]].
  pose proof (indexed_cut_chain_length__dyadic_final states Hpos Hchain)
    as Hlength.
  rewrite Hlast, Hfirst in Hlength.
  rewrite Zlength_repeat_Z__dyadic_final in Hlength by exact Hn.
  assert (Hcuts : Zlength final - n = Zlength states - 1) by lia.
  split; [lia |].
  unfold AchievableAppleDivision. exists states.
  repeat split.
  - rewrite Hcuts. lia.
  - rewrite Hfirst. symmetry.
    apply zero_map_range_repeat__dyadic_final. exact Hn.
  - intros i Hi. apply Hchain. rewrite <- Hcuts. exact Hi.
  - rewrite Hcuts, Hlast. exact Hequal.
Qed.
Lemma concat_repeat_bounds__dyadic_final :
  forall count repr depth,
    Forall (fun e => 0 <= e <= depth) repr ->
    Forall (fun e => 0 <= e <= depth) (concat (repeat repr count)).
Proof.
  induction count as [|count IH]; intros repr depth Hrepr; simpl.
  - constructor.
  - apply Forall_app. split; [exact Hrepr |]. apply IH. exact Hrepr.
Qed.
Lemma Zlength_concat_repeat__dyadic_final :
  forall count (repr : list Z),
    Zlength (concat (repeat repr count)) =
    Z.of_nat count * Zlength repr.
Proof.
  induction count as [|count IH]; intros repr.
  - simpl. rewrite Zlength_nil. ring.
  - change (Zlength (repr ++ concat (repeat repr count)) =
      Z.of_nat (S count) * Zlength repr).
    rewrite Zlength_app, IH, Nat2Z.inj_succ.
    unfold Z.succ. ring.
Qed.
Lemma dyadic_prefix_builds_equal_division__dyadic_final :
  forall n m total,
    0 <= n -> 0 < m ->
    DyadicRemainderPrefix (n mod m) m 0 total ->
    0 <= total /\ AchievableAppleDivision n m total.
Proof.
  intros n m total Hn Hm Hprefix.
  unfold DyadicRemainderPrefix in Hprefix.
  destruct Hprefix as [k [Hk [Hcurrent Htotal]]].
  set (K := Z.to_nat k).
  assert (Hk_nat : Z.of_nat K = k).
  { unfold K. apply Z2Nat.id. exact Hk. }
  set (q := (2 ^ Z.of_nat K * n) / m).
  assert (Hq : 0 <= q).
  { assert (Hpow : 0 < 2 ^ Z.of_nat K)
      by (apply Z.pow_pos_nonneg; lia).
    unfold q. apply Z.div_pos; nia. }
  destruct (minimal_share_representation_exists__dyadic_final K q Hq)
    as [repr [Hrepr_bounds [Hrepr_mass Hrepr_len]]].
  set (shares := repeat repr (Z.to_nat m)).
  set (target := concat shares).
  assert (Hshares_len : Zlength shares = m).
  { unfold shares. rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
    reflexivity. }
  assert (Htarget_bounds :
      Forall (fun e => 0 <= e <= Z.of_nat K) target).
  { unfold target, shares. apply concat_repeat_bounds__dyadic_final.
    exact Hrepr_bounds. }
  assert (Hmodzero : (2 ^ Z.of_nat K * n) mod m = 0).
  { rewrite <- Zmult_mod_idemp_r.
    rewrite Hk_nat.
    unfold DyadicResidue in Hcurrent.
    rewrite <- Hcurrent. reflexivity. }
  assert (Hexact : m * q = 2 ^ Z.of_nat K * n).
  { unfold q. pose proof (Z.div_mod
      (2 ^ Z.of_nat K * n) m ltac:(lia)) as Hdiv. lia. }
  assert (Htarget_mass :
      fold_right
        (fun e acc => 2 ^ (Z.of_nat K - e) + acc) 0 target =
      n * 2 ^ Z.of_nat K).
  { unfold target, shares.
    rewrite constant_share_concat_mass__dyadic_final with (w := q).
    - rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. nia.
    - apply Forall_forall. intros sh Hsh.
      apply repeat_spec in Hsh. subst sh. exact Hrepr_mass. }
  destruct (dyadic_mass_target_reachable__dyadic_final
    K n target Hn Htarget_bounds Htarget_mass)
    as [final [Hreach Hperm]].
  assert (Hfinal_equal : EqualDyadicShares m final).
  { unfold EqualDyadicShares. exists shares, (Z.of_nat K).
    repeat split.
    - exact Hshares_len.
    - exact Hperm.
    - rewrite Forall_forall in Htarget_bounds |- *.
      intros e Hein. apply Htarget_bounds.
      eapply Permutation_in; [exact Hperm | exact Hein].
    - intros i j Hi Hj. unfold shares.
      rewrite (Znth_repeat_lt nil (Z.to_nat m) i repr)
        by (rewrite Z2Nat.id by lia; exact Hi).
      rewrite (Znth_repeat_lt nil (Z.to_nat m) j repr)
        by (rewrite Z2Nat.id by lia; exact Hj).
      reflexivity. }
  destruct (closure_equal_division_achievable__dyadic_final
    n m final Hn Hreach Hfinal_equal) as [Hcuts Hach].
  assert (Htarget_len :
      Zlength target = m *
        (let fix cost (j : nat) (x : Z) : Z :=
           match j with
           | O => x
           | S j' => x mod 2 + cost j' (x / 2)
           end
         in cost K q)).
  { unfold target, shares.
    rewrite Zlength_concat_repeat__dyadic_final.
    rewrite Z2Nat.id by lia. rewrite Hrepr_len. reflexivity. }
  assert (Hfinal_len : Zlength final = Zlength target).
  { rewrite !Zlength_correct. f_equal. apply Permutation_length. exact Hperm. }
  pose proof (complete_prefix_cost_identity__dyadic_final
    K n m Hm Hn) as Hidentity.
  assert (HcompleteK :
      DyadicResidue (n mod m) m (Z.of_nat K) = 0).
  { rewrite Hk_nat. symmetry. exact Hcurrent. }
  specialize (Hidentity HcompleteK).
  rewrite <- Hk_nat in Htotal.
  unfold q in Htarget_len.
  assert (Htotalcuts : total = Zlength final - n).
  { rewrite Htotal, Hidentity, Hfinal_len, Htarget_len. reflexivity. }
  rewrite Htotalcuts. split; assumption.
Qed.
Lemma Zrange_aux_snoc__dyadic_final :
  forall count low,
    Zrange_aux low (S count) =
    Zrange_aux low count ++ [low + Z.of_nat count].
Proof.
  induction count as [|count IH]; intros low; simpl.
  - f_equal. lia.
  - apply f_equal.
    change (Zrange_aux (low + 1) (S count) =
      Zrange_aux (low + 1) count ++ [low + Z.of_nat (S count)]).
    rewrite IH.
    replace (low + 1 + Z.of_nat count)
      with (low + Z.of_nat (S count)) by lia.
    reflexivity.
Qed.
Lemma fold_Zadd_app__dyadic_final :
  forall xs ys,
    fold_right Z.add 0 (xs ++ ys) =
    fold_right Z.add 0 xs + fold_right Z.add 0 ys.
Proof.
  induction xs as [|x xs IH]; intros ys; simpl; [ring |].
  rewrite IH. ring.
Qed.
Lemma dyadic_prefix_fold_snoc__dyadic_final :
  forall k start modulus,
    fold_right Z.add 0
      (Zmap_range (fun i => DyadicResidue start modulus i)
        (Z.of_nat (S k))) =
    fold_right Z.add 0
      (Zmap_range (fun i => DyadicResidue start modulus i)
        (Z.of_nat k)) +
    DyadicResidue start modulus (Z.of_nat k).
Proof.
  intros k start modulus. unfold Zmap_range, Zrange.
  replace (Z.to_nat (Z.of_nat (S k) - 0)) with (S k) by lia.
  replace (Z.to_nat (Z.of_nat k - 0)) with k by lia.
  rewrite Zrange_aux_snoc__dyadic_final, map_app.
  simpl. rewrite fold_Zadd_app__dyadic_final. simpl.
  replace (0 + Z.of_nat k) with (Z.of_nat k) by lia. ring.
Qed.
Lemma dyadic_residue_next_zero__dyadic_final :
  forall start modulus i,
    0 < modulus -> 0 <= i ->
    DyadicResidue start modulus i = 0 ->
    DyadicResidue start modulus (i + 1) = 0.
Proof.
  intros start modulus i Hm Hi Hzero.
  unfold DyadicResidue in *.
  replace (i + 1) with (Z.succ i) by lia.
  rewrite Z.pow_succ_r by lia.
  replace (2 * 2 ^ i * start) with (2 * (2 ^ i * start)) by ring.
  rewrite <- Zmult_mod_idemp_r.
  rewrite Hzero. reflexivity.
Qed.
Lemma dyadic_residue_zero_extension__dyadic_final :
  forall base extra start modulus,
    0 < modulus ->
    DyadicResidue start modulus (Z.of_nat base) = 0 ->
    DyadicResidue start modulus (Z.of_nat (base + extra)) = 0.
Proof.
  intros base extra. induction extra as [|extra IH]; intros start modulus Hm Hz.
  - replace (base + 0)%nat with base by lia. exact Hz.
  - replace (base + S extra)%nat with (S (base + extra)) by lia.
    rewrite Nat2Z.inj_succ.
    apply dyadic_residue_next_zero__dyadic_final; try lia.
    apply IH; assumption.
Qed.
Lemma complete_prefix_fold_extension__dyadic_final :
  forall base extra start modulus,
    0 < modulus ->
    DyadicResidue start modulus (Z.of_nat base) = 0 ->
    fold_right Z.add 0
      (Zmap_range (fun i => DyadicResidue start modulus i)
        (Z.of_nat (base + extra))) =
    fold_right Z.add 0
      (Zmap_range (fun i => DyadicResidue start modulus i)
        (Z.of_nat base)).
Proof.
  intros base extra. induction extra as [|extra IH]; intros start modulus Hm Hz.
  - replace (base + 0)%nat with base by lia. reflexivity.
  - replace (base + S extra)%nat with (S (base + extra)) by lia.
    rewrite dyadic_prefix_fold_snoc__dyadic_final.
    rewrite IH by assumption.
    rewrite dyadic_residue_zero_extension__dyadic_final by assumption.
    ring.
Qed.
Lemma complete_prefix_fold_unique__dyadic_final :
  forall k1 k2 start modulus,
    0 < modulus ->
    DyadicResidue start modulus (Z.of_nat k1) = 0 ->
    DyadicResidue start modulus (Z.of_nat k2) = 0 ->
    fold_right Z.add 0
      (Zmap_range (fun i => DyadicResidue start modulus i) (Z.of_nat k1)) =
    fold_right Z.add 0
      (Zmap_range (fun i => DyadicResidue start modulus i) (Z.of_nat k2)).
Proof.
  intros k1 k2 start modulus Hm H1 H2.
  destruct (le_dec k1 k2) as [Hle | Hnle].
  - replace k2 with (k1 + (k2 - k1))%nat by lia.
    symmetry. apply complete_prefix_fold_extension__dyadic_final; assumption.
  - replace k1 with (k2 + (k1 - k2))%nat by lia.
    apply complete_prefix_fold_extension__dyadic_final; assumption.
Qed.
Lemma equal_shares_mass_at_zero__dyadic_final :
  forall m pieces shares depth,
    0 < m ->
    Zlength shares = m ->
    Permutation pieces (concat shares) ->
    (forall i j, 0 <= i < m -> 0 <= j < m ->
       fold_right (fun e total => 2 ^ (depth - e) + total) 0
         (Znth i shares nil) =
       fold_right (fun e total => 2 ^ (depth - e) + total) 0
         (Znth j shares nil)) ->
    fold_right (fun e total => 2 ^ (depth - e) + total) 0 pieces =
    m * fold_right (fun e total => 2 ^ (depth - e) + total) 0
      (Znth 0 shares nil).
Proof.
  intros m pieces shares depth Hm Hlen Hperm Hequal.
  set (w := fold_right (fun e total => 2 ^ (depth - e) + total) 0
    (Znth 0 shares nil)).
  assert (Hall : Forall
      (fun sh =>
        fold_right (fun e total => 2 ^ (depth - e) + total) 0 sh = w)
      shares).
  { apply Forall_forall. intros sh Hin.
    apply In_nth with (d := nil) in Hin.
    destruct Hin as [idx [Hidx Hnth]].
    specialize (Hequal (Z.of_nat idx) 0).
    assert (Hzidx : 0 <= Z.of_nat idx < m).
    { rewrite <- Hlen, Zlength_correct. lia. }
    specialize (Hequal Hzidx ltac:(lia)).
    unfold Znth in Hequal. rewrite Nat2Z.id in Hequal.
    rewrite Hnth in Hequal. exact Hequal. }
  rewrite (mass_permutation__dyadic_final depth pieces (concat shares) Hperm).
  rewrite constant_share_concat_mass__dyadic_final with (w := w)
    by exact Hall.
  rewrite Hlen. reflexivity.
Qed.
Lemma dyadic_prefix_cut_lower_bound__dyadic_final :
  forall n m total,
    0 < n -> 0 < m ->
    DyadicRemainderPrefix (n mod m) m 0 total ->
    forall cuts,
      0 <= cuts -> AchievableAppleDivision n m cuts -> total <= cuts.
Proof.
  intros n m total Hn Hm Hprefix cuts Hcuts Hach.
  unfold DyadicRemainderPrefix in Hprefix.
  destruct Hprefix as [k [Hk [Hcomplete Htotal]]].
  set (K := Z.to_nat k).
  assert (Hk_nat : Z.of_nat K = k).
  { unfold K. apply Z2Nat.id. exact Hk. }
  unfold AchievableAppleDivision in Hach.
  destruct Hach as [states [Hstates_len [Hinitial [Hsteps Hequal]]]].
  unfold EqualDyadicShares in Hequal.
  destruct Hequal as [shares [depth [Hshares_len [Hperm [Hbounds Heq]]]]].
  assert (Hstates_pos : 0 < Zlength states) by lia.
  assert (Hlast_idx : Zlength states - 1 = cuts) by lia.
  assert (Hsteps' : forall i, 0 <= i < Zlength states - 1 ->
      OneAppleCut (Znth i states nil) (Znth (i + 1) states nil)).
  { intros i Hi. apply Hsteps. lia. }
  assert (Hinitial_nonempty : Znth 0 states nil <> nil).
  { rewrite Hinitial, zero_map_range_repeat__dyadic_final by lia.
    destruct (Z.to_nat n) eqn:Hnat; simpl; [lia | discriminate]. }
  assert (Hfinal_nonempty : Znth cuts states nil <> nil).
  { rewrite <- Hlast_idx.
    eapply indexed_cut_chain_nonempty__dyadic_final; eassumption. }
  assert (Hdepth : 0 <= depth).
  { destruct (Znth cuts states nil) as [|e es] eqn:Hpieces.
    - exfalso. apply Hfinal_nonempty. reflexivity.
    - inversion Hbounds. lia. }
  assert (Hupper : Forall (fun e => e <= depth) (Znth cuts states nil)).
  { rewrite Forall_forall in Hbounds |- *.
    intros e Hein. specialize (Hbounds e Hein). lia. }
  assert (Hchain_mass :
      fold_right (fun e total => 2 ^ (depth - e) + total) 0
        (Znth 0 states nil) =
      fold_right (fun e total => 2 ^ (depth - e) + total) 0
        (Znth cuts states nil)).
  { pose proof (indexed_cut_chain_mass__dyadic_final states depth
      Hstates_pos Hsteps') as Hmass.
    rewrite Hlast_idx in Hmass. specialize (Hmass Hupper).
    tauto. }
  set (w := fold_right (fun e total => 2 ^ (depth - e) + total) 0
    (Znth 0 shares nil)).
  assert (Hfinal_mass :
      fold_right (fun e total => 2 ^ (depth - e) + total) 0
        (Znth cuts states nil) = m * w).
  { unfold w. eapply equal_shares_mass_at_zero__dyadic_final;
      eassumption. }
  assert (Hmass_eq : n * 2 ^ depth = m * w).
  { rewrite <- Hfinal_mass, <- Hchain_mass, Hinitial.
    symmetry. apply fold_zero_map_range_mass__dyadic_final. lia. }
  assert (Hpieces_len : Zlength (Znth cuts states nil) = n + cuts).
  { pose proof (indexed_cut_chain_length__dyadic_final states
    Hstates_pos Hsteps') as Hlen.
    rewrite Hlast_idx, Hinitial in Hlen.
    assert (Hzero_len : Zlength (Zmap_range (fun _ => 0) n) = n).
    { unfold Zmap_range. rewrite Zlength_correct, length_map.
      rewrite <- Zlength_correct.
      rewrite Zlength_Zrange__dyadic_final by lia. lia. }
    rewrite Hzero_len in Hlen.
    exact Hlen. }
  pose proof (equal_dyadic_shares_piece_lower_bound__dyadic_final
    m (Znth cuts states nil) shares depth Hm Hdepth Hshares_len
    Hperm Hbounds Heq) as Hlower.
  cbn zeta in Hlower.
  fold w in Hlower.
  set (D := Z.to_nat depth).
  assert (Hdepth_nat : Z.of_nat D = depth).
  { unfold D. apply Z2Nat.id. exact Hdepth. }
  assert (Hwquot : (2 ^ Z.of_nat D * n) / m = w).
  { rewrite Hdepth_nat.
    replace (2 ^ depth * n) with (m * w) by nia.
    rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
  assert (HcompleteD :
      DyadicResidue (n mod m) m (Z.of_nat D) = 0).
  { unfold DyadicResidue. rewrite Zmult_mod_idemp_r.
    rewrite Hdepth_nat.
    replace (2 ^ depth * n) with (w * m) by nia.
    apply Z.mod_mul. lia. }
  pose proof (complete_prefix_cost_identity__dyadic_final
    D n m Hm ltac:(lia) HcompleteD) as HidentityD.
  rewrite Hwquot in HidentityD.
  assert (HcompleteK :
      DyadicResidue (n mod m) m (Z.of_nat K) = 0).
  { rewrite Hk_nat. symmetry. exact Hcomplete. }
  pose proof (complete_prefix_fold_unique__dyadic_final
    K D (n mod m) m Hm HcompleteK HcompleteD) as Hunique.
  rewrite <- Hk_nat in Htotal.
  rewrite Htotal, Hunique, HidentityD.
  rewrite Hpieces_len in Hlower. unfold D. lia.
Qed.
Lemma complete_dyadic_prefix_minimum__dyadic_final :
  forall n m total,
    0 < n -> 0 < m ->
    DyadicRemainderPrefix (n mod m) m 0 total ->
    min_value_of_subset Z.le
      (fun cuts : Z => 0 <= cuts /\ AchievableAppleDivision n m cuts)
      (fun cuts => cuts) total.
Proof.
  intros n m total Hn Hm Hprefix.
  destruct (dyadic_prefix_builds_equal_division__dyadic_final
    n m total ltac:(lia) Hm Hprefix) as [Htotal_nonneg Htotal_ach].
  unfold MaxMin.min_value_of_subset, MaxMin.min_object_of_subset.
  exists total. split.
  - split.
    + split; assumption.
    + intros cuts [Hcuts Hach].
      cbn. exact (dyadic_prefix_cut_lower_bound__dyadic_final
        n m total Hn Hm Hprefix cuts Hcuts Hach).
  - reflexivity.
Qed.
