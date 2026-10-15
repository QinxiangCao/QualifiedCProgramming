Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition Luxury (x : Z) : Prop :=
  exists q, q > 0 /\ q * q <= x < (q + 1) * (q + 1) /\ (q | x).

Definition Pre (l r : Z) : Prop :=
  (* Every clause below is stated explicitly in the P033 solver Require, which
     therefore omits the Pre(...) call:
       1 <= l <= r /\ r <= Z.pow 10 18. *)
  True.

Definition Spec (l r out : Z) : Prop :=
  out = #(fun x : Z => l <= x < r + 1 /\ Luxury x).

Definition ISqrtSpec (v root : Z) : Prop :=
  0 <= root /\ root * root <= v < (root + 1) * (root + 1).

Definition LuxuryCountUpto (x out : Z) : Prop :=
  out = #(fun z : Z => 1 <= z < x + 1 /\ Luxury z).

Definition SqrtSearchBounds (v lo hi : Z) : Prop :=
  lo * lo <= v /\ v < (hi + 1) * (hi + 1).

Definition LuxuryBlockPrefix (x s m cnt : Z) : Prop :=
  cnt = 3 * (s - 1) +
    #(fun k : Z => 0 <= k < m /\ s * s + k * s <= x).

Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.ZArith.Znumtheory.
Lemma div_upper_implies_square_le__isqrt_invariant :
  forall v m : Z, 0 <= v -> 0 < m -> m <= v / m -> m * m <= v.
Proof.
  intros v m Hv Hm Hq.
  pose proof (Z.div_mod v m ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound v m ltac:(lia)) as Hmod.
  nia.
Qed.
Lemma div_lower_implies_square_gt__isqrt_invariant :
  forall v m : Z, 0 <= v -> 0 < m -> v / m < m -> v < m * m.
Proof.
  intros v m Hv Hm Hq.
  pose proof (Z.div_mod v m ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound v m ltac:(lia)) as Hmod.
  nia.
Qed.
Lemma isqrt_root_range__count_setup :
  forall x s : Z,
    0 < x ->
    x <= 1000000000000000000 ->
    ISqrtSpec x s ->
    1 <= s /\ s <= 1000000000.
Proof.
  intros x s Hx Hbound Hspec.
  unfold ISqrtSpec in Hspec.
  destruct Hspec as [Hs [Hsq Hnext]].
  split; nia.
Qed.
Lemma set_card_empty__count_setup :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma set_card_Z_as_sum__count_transitions :
  forall (low high : Z) (P : Z -> Prop),
    #(fun k : Z => low <= k < high /\ P k) =
    SumLib.Sum.sum (fun k : Z => low <= k < high)
      (fun k => if prop_dec (P k) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall ks : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun k => if prop_dec (P k) then true else false) ks) =
    fold_right (fun k acc : Z =>
      (if prop_dec (P k) then 1 else 0) + acc) 0 ks).
  {
    induction ks as [|k ks IH]; simpl; [reflexivity |].
    destruct (prop_dec (P k)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_true__count_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun k : Z => low <= k < high + 1 /\ P k) =
    #(fun k : Z => low <= k < high /\ P k) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__count_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [_ | Hnot]; [lia | contradiction].
Qed.
Lemma set_card_Z_extend_false__count_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun k : Z => low <= k < high + 1 /\ P k) =
    #(fun k : Z => low <= k < high /\ P k).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__count_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [Hp | _]; [contradiction | lia].
Qed.
Lemma luxury_block_prefix_hit_step__count_transitions :
  forall x s m cnt,
    1 <= s ->
    0 <= m < 3 ->
    LuxuryBlockPrefix x s m cnt ->
    s * s + m * s <= x ->
    LuxuryBlockPrefix x s (m + 1) (cnt + 1) /\ cnt + 1 <= 3 * s.
Proof.
  intros x s m cnt Hs Hm Hprefix Hhit.
  unfold LuxuryBlockPrefix in *.
  assert (Hcard :
    #(fun k : Z => 0 <= k < m /\ s * s + k * s <= x) = m).
  {
    rewrite set_card_Z_as_sum__count_transitions.
    transitivity
      (SumLib.Sum.sum (fun k : Z => 0 <= k < m) (fun _ => 1)).
    - apply SumLib.ZRange.sum_Z_range_ext.
      intros k Hk.
      destruct (prop_dec (s * s + k * s <= x)) as [_ | Hnot].
      + reflexivity.
      + exfalso. apply Hnot. nia.
    - rewrite SumLib.ZRange.sum_Z_range_const by lia.
      lia.
  }
  assert (Hextend :
    #(fun k : Z => 0 <= k < m + 1 /\ s * s + k * s <= x) =
    #(fun k : Z => 0 <= k < m /\ s * s + k * s <= x) + 1).
  {
    apply set_card_Z_extend_true__count_transitions.
    - lia.
    - exact Hhit.
  }
  split.
  - rewrite Hextend. lia.
  - rewrite Hcard in Hprefix. lia.
Qed.
Lemma luxury_block_prefix_miss_step__count_transitions :
  forall x s m cnt,
    1 <= s ->
    0 <= m < 3 ->
    LuxuryBlockPrefix x s m cnt ->
    s * s + m * s > x ->
    LuxuryBlockPrefix x s (m + 1) cnt.
Proof.
  intros x s m cnt Hs Hm Hprefix Hmiss.
  unfold LuxuryBlockPrefix in *.
  rewrite (set_card_Z_extend_false__count_transitions
    0 m (fun k : Z => s * s + k * s <= x)) by lia.
  exact Hprefix.
Qed.
Lemma set_card_empty__count_final :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma set_card_bijection__count_final :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
         (FP : Finite P) (FQ : Finite Q) (f : A -> B) (g : B -> A),
    (forall x, P x -> Q (f x)) ->
    (forall y, Q y -> P (g y)) ->
    (forall x, P x -> g (f x) = x) ->
    (forall y, Q y -> f (g y) = y) ->
    @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f g Hf Hg Hgf Hfg.
  unfold set_card, SumLib.Sum.sum.
  assert (Hnodup_map : NoDup (map f (@enum A P FP))).
  {
    assert (Hgeneral : forall xs : list A,
      NoDup xs -> (forall x, In x xs -> P x) -> NoDup (map f xs)).
    {
      intros xs Hnodup.
      induction Hnodup as [|x xs Hnotin Hnodup IH]; intros Hall; simpl.
      - constructor.
      - constructor.
        + intro Hin. apply in_map_iff in Hin.
          destruct Hin as [y [Hfy Hy]].
          apply Hnotin.
          assert (HPx : P x) by (apply Hall; left; reflexivity).
          assert (HPy : P y) by (apply Hall; right; exact Hy).
          assert (Hxy : x = y).
          { rewrite <- (Hgf x HPx), <- (Hgf y HPy). congruence. }
          rewrite Hxy. exact Hy.
        + apply IH. intros y Hy. apply Hall. right. exact Hy.
    }
    apply Hgeneral.
    - exact (@enum_nodup A P FP).
    - intros x Hx. apply (proj2 (@enum_ok A P FP x)). exact Hx.
  }
  assert (Hperm : Permutation (map f (@enum A P FP)) (@enum B Q FQ)).
  {
    apply NoDup_Permutation.
    - exact Hnodup_map.
    - exact (@enum_nodup B Q FQ).
    - intros y. rewrite <- (@enum_ok B Q FQ y). split.
      + intros Hin. apply in_map_iff in Hin.
        destruct Hin as [x [Hxy Hx]]. subst y.
        apply Hf. apply (proj2 (@enum_ok A P FP x)). exact Hx.
      + intros HyQ. apply in_map_iff. exists (g y). split.
        * apply Hfg. exact HyQ.
        * apply (proj1 (@enum_ok A P FP (g y))). apply Hg. exact HyQ.
  }
  assert (Hfold_count : forall (C : Type) (l : list C),
    fold_right (fun _ (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l)).
  {
    intros C l. induction l as [|x xs IH].
    - reflexivity.
    - cbn [fold_right length].
      rewrite IH, Nat2Z.inj_succ. lia.
  }
  rewrite !Hfold_count.
  rewrite <- (Permutation_length Hperm), length_map.
  reflexivity.
Qed.
Lemma set_card_Z_as_sum__count_final :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma square_block_root_unique__count_final :
  forall z q r,
    0 < q -> q * q <= z < (q + 1) * (q + 1) ->
    0 < r -> r * r <= z < (r + 1) * (r + 1) ->
    q = r.
Proof.
  intros z q r Hq Hqz Hr Hrz.
  destruct Hqz as [Hqlo Hqhi].
  destruct Hrz as [Hrlo Hrhi].
  nia.
Qed.
Lemma luxury_block_prefix_complete__count_final :
  forall x s cnt : Z,
    1 <= x -> ISqrtSpec x s -> LuxuryBlockPrefix x s 3 cnt ->
    LuxuryCountUpto x cnt.
Proof.
  intros x s cnt Hx Hsqrt Hprefix.
  unfold ISqrtSpec in Hsqrt.
  destruct Hsqrt as [Hs0 [Hslo Hshi]].
  assert (Hs : 1 <= s) by nia.
  set (root := fun z : Z =>
    epsilon (inhabits 0%Z)
      (fun q : Z => 0 < q /\ q * q <= z < (q + 1) * (q + 1) /\ (q | z))).
  assert (Hroot : forall z, Luxury z ->
    0 < root z /\ root z * root z <= z < (root z + 1) * (root z + 1) /\
    (root z | z)).
  {
    intros z Hz.
    unfold Luxury in Hz.
    unfold root.
    apply epsilon_spec.
    destruct Hz as [q [Hq Hrest]].
    exists q. split; [lia | exact Hrest].
  }
  set (P := fun z : Z => 1 <= z < x + 1 /\ Luxury z).
  set (Q := fun n : Z =>
    0 <= n < 3 * s /\
    let q := n / 3 + 1 in
    let k := n mod 3 in
    q * q + k * q <= x).
  set (encode := fun z : Z =>
    3 * (root z - 1) + (z / root z - root z)).
  set (decode := fun n : Z =>
    let q := n / 3 + 1 in
    let k := n mod 3 in
    q * q + k * q).
  assert (Hbij :
    #(fun z : Z => 1 <= z < x + 1 /\ Luxury z) =
    #(fun n : Z => 0 <= n < 3 * s /\
      let q := n / 3 + 1 in
      let k := n mod 3 in
      q * q + k * q <= x)).
  {
    change (@set_card Z P _ = @set_card Z Q _).
    eapply set_card_bijection__count_final with
      (f := encode) (g := decode).
    - intros z [[Hzlo Hzhi] Hzlux].
      pose proof (Hroot z Hzlux) as [Hr [Hrz Hrdiv]].
      set (t := z / root z).
      assert (Hzt : z = root z * t).
      { unfold t. apply Zdivide_Zdiv_eq; assumption. }
      assert (Hk : 0 <= t - root z < 3) by nia.
      assert (Hrs : root z <= s).
      {
        destruct Hrz as [Hrzlo Hrzhi].
        nia.
      }
      unfold Q, encode.
      fold t.
      assert (Hdiv : (3 * (root z - 1) + (t - root z)) / 3 = root z - 1).
      {
        replace (3 * (root z - 1) + (t - root z))
          with ((t - root z) + (root z - 1) * 3) by ring.
        rewrite Z.div_add by lia.
        rewrite Z.div_small by lia.
        lia.
      }
      assert (Hmod : (3 * (root z - 1) + (t - root z)) mod 3 = t - root z).
      {
        replace (3 * (root z - 1) + (t - root z))
          with ((t - root z) + (root z - 1) * 3) by ring.
        rewrite Z.mod_add by lia.
        apply Z.mod_small. lia.
      }
      split.
      + nia.
      + cbn zeta. rewrite Hdiv, Hmod. nia.
    - intros n [[Hnlo Hnhi] Hcond].
      pose proof (Z.mod_pos_bound n 3 ltac:(lia)) as Hk.
      assert (Hq : 1 <= n / 3 + 1 <= s).
      {
        assert (Hnq0 : 0 <= n / 3) by (apply Z_div_nonneg_nonneg; lia).
        assert (Hnqs : n / 3 < s) by (apply Z.div_lt_upper_bound; nia).
        lia.
      }
      unfold P, decode.
      cbn zeta in Hcond |- *.
      split.
      + nia.
      + exists (n / 3 + 1).
        split; [lia |].
        split.
        * split; nia.
        * exists (n / 3 + 1 + n mod 3).
          ring.
    - intros z [[Hzlo Hzhi] Hzlux].
      pose proof (Hroot z Hzlux) as [Hr [Hrz Hrdiv]].
      set (t := z / root z).
      assert (Hzt : z = root z * t).
      { unfold t. apply Zdivide_Zdiv_eq; assumption. }
      assert (Hk : 0 <= t - root z < 3) by nia.
      unfold decode, encode.
      fold t.
      assert (Hdiv : (3 * (root z - 1) + (t - root z)) / 3 = root z - 1).
      {
        replace (3 * (root z - 1) + (t - root z))
          with ((t - root z) + (root z - 1) * 3) by ring.
        rewrite Z.div_add by lia.
        rewrite Z.div_small by lia.
        lia.
      }
      assert (Hmod : (3 * (root z - 1) + (t - root z)) mod 3 = t - root z).
      {
        replace (3 * (root z - 1) + (t - root z))
          with ((t - root z) + (root z - 1) * 3) by ring.
        rewrite Z.mod_add by lia.
        apply Z.mod_small. lia.
      }
      rewrite Hdiv, Hmod.
      nia.
    - intros n [[Hnlo Hnhi] Hcond].
      pose proof (Z.mod_pos_bound n 3 ltac:(lia)) as Hk.
      assert (Hq : 1 <= n / 3 + 1 <= s).
      {
        assert (Hnq0 : 0 <= n / 3) by (apply Z_div_nonneg_nonneg; lia).
        assert (Hnqs : n / 3 < s) by (apply Z.div_lt_upper_bound; nia).
        lia.
      }
      unfold encode, decode.
      cbn zeta.
      set (q := n / 3 + 1).
      set (k := n mod 3).
      assert (Hlux : Luxury (q * q + k * q)).
      {
        exists q.
        split; [unfold q; lia |].
        split.
        - unfold q, k in *. split; nia.
        - exists (q + k). ring.
      }
      pose proof (Hroot (q * q + k * q) Hlux) as [Hr [Hrz Hrdiv]].
      assert (Hrootq : root (q * q + k * q) = q).
      {
        eapply square_block_root_unique__count_final; eauto.
        unfold q; lia.
        unfold q, k in *. split; nia.
      }
      rewrite Hrootq.
      assert (Hqne : q <> 0) by (unfold q; lia).
      assert (Hquot : (q * q + k * q) / q = q + k).
      { replace (q * q + k * q) with ((q + k) * q) by ring.
        apply Z.div_mul. exact Hqne. }
      rewrite Hquot.
      unfold q, k.
      pose proof (Z.div_mod n 3 ltac:(lia)) as Hdm.
      nia.
  }
  assert (Hcount :
    #(fun n : Z => 0 <= n < 3 * s /\
      let q := n / 3 + 1 in
      let k := n mod 3 in
      q * q + k * q <= x) =
    3 * (s - 1) +
      #(fun k : Z => 0 <= k < 3 /\ s * s + k * s <= x)).
  {
    rewrite set_card_Z_as_sum__count_final.
    rewrite (SumLib.ZRange.sum_Z_range_split 0 (3 * (s - 1)) (3 * s)) by nia.
    assert (Hfirst :
      SumLib.Sum.sum (fun n : Z => 0 <= n < 3 * (s - 1))
        (fun n => if prop_dec
          (let q := n / 3 + 1 in let k := n mod 3 in
           q * q + k * q <= x) then 1 else 0) =
      3 * (s - 1)).
    {
      rewrite (SumLib.ZRange.sum_Z_range_ext 0 (3 * (s - 1))
        (fun n => if prop_dec
          (let q := n / 3 + 1 in let k := n mod 3 in
           q * q + k * q <= x) then 1 else 0)
        (fun _ => 1)).
      - rewrite SumLib.ZRange.sum_Z_range_const by lia. ring.
      - intros n Hn.
        destruct (prop_dec
          (let q := n / 3 + 1 in let k := n mod 3 in
           q * q + k * q <= x)) as [Hyes | Hno]; [reflexivity |].
        exfalso. apply Hno. cbn zeta.
        pose proof (Z.mod_pos_bound n 3 ltac:(lia)) as Hk.
        assert (Hq0 : 0 <= n / 3) by (apply Z_div_nonneg_nonneg; lia).
        assert (Hqlt : n / 3 < s - 1).
        { apply Z.div_lt_upper_bound; nia. }
        nia.
    }
    cbn zeta in Hfirst.
    rewrite Hfirst.
    replace (3 * s) with (3 + 3 * (s - 1)) by ring.
    rewrite (SumLib.ZRange.sum_Z_range_shift 0 3 (3 * (s - 1))).
    rewrite set_card_Z_as_sum__count_final.
    f_equal.
    apply SumLib.ZRange.sum_Z_range_ext.
    intros k Hk.
    assert (Hdiv : (k + 3 * (s - 1)) / 3 = s - 1).
    { replace (k + 3 * (s - 1)) with (k + (s - 1) * 3) by ring.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
    assert (Hmod : (k + 3 * (s - 1)) mod 3 = k).
    { replace (k + 3 * (s - 1)) with (k + (s - 1) * 3) by ring.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite Hdiv, Hmod.
    destruct (prop_dec ((s - 1 + 1) * (s - 1 + 1) +
      k * (s - 1 + 1) <= x));
      destruct (prop_dec (s * s + k * s <= x));
      try reflexivity; exfalso; nia.
  }
  unfold LuxuryCountUpto.
  unfold LuxuryBlockPrefix in Hprefix.
  rewrite Hprefix.
  rewrite Hbij.
  symmetry. exact Hcount.
Qed.
Lemma fold_right_Zadd_permutation__solver_final :
  forall {A : Type} (f : A -> Z) (l1 l2 : list A),
    Permutation l1 l2 ->
    fold_right (fun x acc => f x + acc) 0 l1 =
    fold_right (fun x acc => f x + acc) 0 l2.
Proof.
  intros A f l1 l2 Hperm.
  induction Hperm; simpl; lia.
Qed.
Lemma fold_right_Zadd_app__solver_final :
  forall {A : Type} (f : A -> Z) (l1 l2 : list A),
    fold_right (fun x acc => f x + acc) 0 (l1 ++ l2) =
    fold_right (fun x acc => f x + acc) 0 l1 +
    fold_right (fun x acc => f x + acc) 0 l2.
Proof.
  intros A f l1 l2.
  induction l1 as [|x l1 IH]; simpl; lia.
Qed.
Lemma luxury_count_interval_difference__solver_final :
  forall l r a b : Z,
    1 <= l ->
    l <= r ->
    LuxuryCountUpto r a ->
    LuxuryCountUpto (l - 1) b ->
    Spec l r (a - b).
Proof.
  intros l r a b Hl Hlr Ha Hb.
  unfold LuxuryCountUpto in Ha, Hb.
  unfold Spec.
  replace (l - 1 + 1) with l in Hb by lia.
  subst a; subst b.
  assert (Hcard :
    set_card (fun z : Z => 1 <= z < r + 1 /\ Luxury z) =
    set_card (fun z : Z => 1 <= z < l /\ Luxury z) +
    set_card (fun z : Z => l <= z < r + 1 /\ Luxury z)).
  {
    unfold set_card, sum.
    transitivity
      (fold_right (fun _ acc => 1 + acc) 0
        (@enum Z (fun z => 1 <= z < l /\ Luxury z) _ ++
         @enum Z (fun z => l <= z < r + 1 /\ Luxury z) _)).
    - apply fold_right_Zadd_permutation__solver_final.
      apply NoDup_Permutation.
      + apply enum_nodup.
      + apply NoDup_app.
        * apply enum_nodup.
        * apply enum_nodup.
        * intros z Hzleft Hzright.
          apply (@enum_ok Z (fun z => 1 <= z < l /\ Luxury z) _) in Hzleft.
          apply (@enum_ok Z (fun z => l <= z < r + 1 /\ Luxury z) _) in Hzright.
          lia.
      + intros z.
        rewrite in_app_iff.
        rewrite <- (@enum_ok Z (fun z => 1 <= z < r + 1 /\ Luxury z) _ z).
        rewrite <- (@enum_ok Z (fun z => 1 <= z < l /\ Luxury z) _ z).
        rewrite <- (@enum_ok Z (fun z => l <= z < r + 1 /\ Luxury z) _ z).
        split.
        * intros [[Hzlow Hzupper] Hlux].
          destruct (Z_lt_ge_dec z l) as [Hzleft | Hzright].
          -- left. split; [lia | exact Hlux].
          -- right. split; [lia | exact Hlux].
        * intros [[[Hzlow Hzupper] Hlux] | [[Hzlow Hzupper] Hlux]].
          -- split; [lia | exact Hlux].
          -- split; [lia | exact Hlux].
    - apply fold_right_Zadd_app__solver_final.
  }
  lia.
Qed.
