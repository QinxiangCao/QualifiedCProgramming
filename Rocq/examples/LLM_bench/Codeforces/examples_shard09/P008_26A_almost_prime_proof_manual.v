From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P008_26A_almost_prime_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P008_26A_almost_prime_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P008_26A_almost_prime_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  rewrite Znth_repeat.
  split; [lia |].
  exists (@nil Z).
  simpl.
  repeat split; try constructor; intros; simpl in *; lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists counts_2 1.
  split_pure_spatial.
  - cancel (IntArray.full &( "ndiv" ) 3005 counts_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try lia.
    + intros a b [Ha Hp].
      destruct (PreH8 p ltac:(lia)) as
        [_ [old_ps [[[Hold_len Hold_nodup] Hold_sound] Hold_complete]]].
      rewrite PreH1 in Hold_len.
      apply Zlength_nil_inv in Hold_len.
      subst old_ps.
      destruct (Z_le_dec p a) as [Hpa | Hpa].
      * exact Hpa.
      * assert (Hfactor : forall z : Z, 1 < z ->
            exists q : Z,
              2 <= q /\
              (forall a0 b0 : Z,
                 2 <= a0 /\ q = a0 * b0 -> q <= a0) /\
              exists c : Z, 1 <= c /\ z = q * c).
        {
          intros z Hz.
          assert (Hz_nonneg : 0 <= z) by lia.
          revert Hz.
          pattern z.
          apply Z_lt_induction.
          intros z0 IH Hz0.
          destruct (Classical_Prop.classic (forall a0 b0 : Z,
              2 <= a0 /\ z0 = a0 * b0 -> z0 <= a0)) as
            [Hz_min | Hz_not_min].
          - exists z0.
            split; [lia |].
            split; [exact Hz_min |].
            exists 1.
            nia.
          - assert (Hex : exists d e : Z,
                2 <= d /\ z0 = d * e /\ d < z0).
            {
              apply Classical_Prop.NNPP.
              intros Hno.
              apply Hz_not_min.
              intros d e [Hd_ge Hde].
              destruct (Z_le_dec z0 d) as [Hzd | Hzd]; [exact Hzd |].
              exfalso.
              apply Hno.
              exists d, e.
              repeat split; try assumption; lia.
            }
            destruct Hex as [d [e [Hd_ge [Hde Hd_lt]]]].
            destruct (IH d ltac:(lia) ltac:(lia)) as
              [q [Hq_ge [Hq_min [c [Hc_ge Hdc]]]]].
            exists q.
            split; [exact Hq_ge |].
            split; [exact Hq_min |].
            exists (c * e).
            split; nia.
          - exact Hz_nonneg.
        }
        destruct (Hfactor a ltac:(lia)) as
          [q [Hq_ge [Hq_min [c [Hc_ge Hac]]]]].
        assert (Hq_in : In q (@nil Z)).
        {
          apply Hold_complete.
          split.
          - split.
            + split; nia.
            + exact Hq_min.
          - exists (c * b).
            split; nia.
        }
        contradiction.
    + intros x Hx.
      destruct (PreH8 x Hx) as
        [[Hcount_nonneg Hcount_upper]
         [cur_ps [[[Hcur_len Hcur_nodup] Hcur_sound] Hcur_complete]]].
      split.
      * split; [exact Hcount_nonneg | lia].
      * exists cur_ps.
        split.
        -- split.
           ++ split; assumption.
           ++ intros q Hq_in.
              destruct (Hcur_sound q Hq_in) as
                [[[Hq_ge Hq_lt] Hq_min] [qk [Hqk_ge Hxq]]].
              split.
              ** split.
                 --- split; assumption.
                 --- exists qk; split; assumption.
              ** left; exact Hq_lt.
        -- intros q Hq_new.
              destruct Hq_new as
                [[[Hq_ge Hq_min] [qk [Hqk_ge Hxq]]]
                 [Hq_lt | [Hq_eq Hx_lt]]].
              ** apply Hcur_complete.
                 split.
                 --- split.
                     +++ split; assumption.
                     +++ exact Hq_min.
                 --- exists qk; split; assumption.
              ** subst q.
                 nia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (replace_Znth m (Znth m counts_2 0 + 1) counts_2) (t_2 + 1).
  split_pure_spatial.
  - cancel (IntArray.full &("ndiv") 3005
              (replace_Znth m (Znth m counts_2 0 + 1) counts_2)).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. exact PreH6.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. nia.
    + dump_pre_spatial. rewrite Zlength_replace_Znth. exact PreH11.
    + dump_pre_spatial.
      intros x Hx.
      destruct (Z.eq_dec x m) as [Heq | Hneq].
      * subst x.
        rewrite Znth_replace_Znth_Same by (rewrite PreH11; lia).
        specialize (PreH12 m ltac:(lia)).
        destruct PreH12 as [[Hlo Hhi] [ps0 [[[Hlen Hnodup] Hin] Hall]]].
        assert (Hincl : incl ps0
          (map (fun n : nat => 2 + Z.of_nat n) (seq 0 (Z.to_nat (p - 2))))).
        {
          intros q Hqin.
          destruct (Hin q Hqin) as [[Hq _] Hrange].
          assert (Hqp : q < p).
          { destruct Hrange as [Hlt | [_ Hlt]]; lia. }
          apply in_map_iff.
          exists (Z.to_nat (q - 2)).
          split.
          - rewrite Z2Nat.id by lia. lia.
          - apply in_seq. split; [lia |].
            apply Z2Nat.inj_lt; lia.
        }
        pose proof (NoDup_incl_length Hnodup Hincl) as Hcard.
        rewrite length_map, length_seq in Hcard.
        apply Nat2Z.inj_le in Hcard.
        rewrite Z2Nat.id in Hcard by lia.
        rewrite <- Zlength_correct in Hcard.
        split.
        -- lia.
        -- exists (ps0 ++ (p :: nil)).
           split.
           ++ split.
              ** split.
                 --- rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
                 --- apply NoDup_app.
                     +++ exact Hnodup.
                     +++ constructor; [simpl; tauto | constructor].
                     +++ intros q Hqin Hqsingle.
                         simpl in Hqsingle.
                         destruct Hqsingle as [Hqp | Hfalse]; [subst q | contradiction].
                         destruct (Hin p Hqin) as [_ Hrange].
                         destruct Hrange as [Hlt | [_ Hlt]]; lia.
              ** intros q Hqin.
                 apply in_app_iff in Hqin.
                 destruct Hqin as [Hqin | Hqsingle].
                 --- destruct (Hin q Hqin) as [Hfacts Hrange].
                     split; [exact Hfacts |].
                     destruct Hrange as [Hlt | [Heq Hlt]].
                     +++ left. exact Hlt.
                     +++ right. split; [exact Heq | lia].
                 --- simpl in Hqsingle.
                     destruct Hqsingle as [Hqp | Hfalse]; [subst q | contradiction].
                     split.
                     +++ split.
                         *** split; [exact PreH4 | exact PreH6].
                         *** exists t_2. split; [exact PreH9 | exact PreH10].
                     +++ right. split; lia.
           ++ intros q Hnew.
              destruct Hnew as [Hfacts Hrange].
              apply in_app_iff.
              destruct (Z.eq_dec q p) as [Hqp | Hqp].
              ** right. subst q. simpl. auto.
              ** left. apply Hall. split; [exact Hfacts |].
                 destruct Hrange as [Hlt | [Heq _]].
                 --- left. exact Hlt.
                 --- contradiction.
      * assert (Hmrange : 0 <= m < Zlength counts_2) by (rewrite PreH11; lia).
        assert (Hxrange : 0 <= x < Zlength counts_2) by (rewrite PreH11; lia).
        rewrite Znth_replace_Znth_Diff by (try assumption; lia).
        specialize (PreH12 x Hx).
        destruct PreH12 as [Hbounds [ps0 [[[Hlen Hnodup] Hin] Hall]]].
        split; [exact Hbounds |].
        exists ps0.
        split.
        -- split.
           ++ split; [exact Hlen | exact Hnodup].
           ++ intros q Hqin.
              destruct (Hin q Hqin) as [Hfacts Hrange].
              split; [exact Hfacts |].
              destruct Hrange as [Hlt | [Heq Hlt]].
              ** left. exact Hlt.
              ** right. split; [exact Heq | lia].
        -- intros q Hnew.
           destruct Hnew as [Hfacts Hrange].
           apply Hall. split; [exact Hfacts |].
           destruct Hrange as [Hlt | [Heq Hlt]].
           ++ left. exact Hlt.
           ++ right. split; [exact Heq |].
              destruct Hfacts as [[_ _] [qk [Hqk Hxq]]].
              subst q.
              assert (Hqkneq : qk <> t_2).
              { intro Heq. apply Hneq. rewrite Hxq, PreH10, Heq. reflexivity. }
              rewrite Hxq, PreH10 in Hlt.
              replace (p * t_2 + p) with (p * (t_2 + 1)) in Hlt by ring.
              apply Z.mul_lt_mono_pos_l in Hlt; [|lia].
              rewrite Hxq, PreH10.
              apply Z.mul_lt_mono_pos_l; lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hprime_iff : forall q : Z,
    (2 <= q /\
     forall a b : Z, (2 <= a /\ q = a * b) -> q <= a) <-> Znumtheory.prime q).
  {
    intro q; split.
    - intros [Hq2 Hfac].
      apply (proj1 (Znumtheory.prime_alt q)).
      unfold Znumtheory.prime'.
      split; [lia |].
      intros d Hd Hdiv.
      destruct Hdiv as [z Hz].
      specialize (Hfac d z).
      lia.
    - intro Hq.
      split.
      + apply Znumtheory.prime_ge_2; exact Hq.
      + intros a b [Ha2 Hab].
        assert (HaDiv : (a | q)) by (exists b; nia).
        destruct (Znumtheory.prime_divisors q Hq a HaDiv) as [-> | [-> | [-> | ->]]]; lia.
  }
  destruct H as [Hx1 Hxn].
  specialize (PreH7 x (conj Hx1 Hxn)).
  destruct PreH7 as [[Hcount0 Hcountb]
    [divs [[[Hlen Hnodup] Hsound] Hcomplete]]].
  split.
  - split; [exact Hcount0 | lia].
  - destruct (Z.eq_dec (Znth x counts_2 0) 2) as [Htwo | Hnot_two].
    + left; split; [exact Htwo |].
      unfold AlmostPrime.
      destruct divs as [|a divs].
      { rewrite Zlength_nil in Hlen; lia. }
      destruct divs as [|b divs].
      { rewrite Zlength_cons, Zlength_nil in Hlen; lia. }
      destruct divs as [|c divs].
      2:{ do 3 rewrite Zlength_cons in Hlen.
          pose proof (Zlength_nonneg divs); lia. }
      destruct (Hsound a ltac:(simpl; auto)) as
        [[[Ha2 Hap] HaPrimeRaw] [ka [Hka Hxa]]].
      destruct (Hsound b ltac:(simpl; auto)) as
        [[[Hb2 Hbp] HbPrimeRaw] [kb [Hkb Hxb]]].
      assert (HaPrime : Znumtheory.prime a) by (apply Hprime_iff; auto).
      assert (HbPrime : Znumtheory.prime b) by (apply Hprime_iff; auto).
      inversion Hnodup as [|? ? HaNotIn HtailNodup]; subst.
      assert (Hab : a <> b).
      { intro HabEq; subst b; apply HaNotIn; simpl; auto. }
      exists a, b.
      split; [exact HaPrime |].
      split; [exact HbPrime |].
      split; [exact Hab |].
      split.
      * exists ka; nia.
      * split.
        { exists kb; nia. }
        intros r HrPrime HrDiv.
        destruct HrDiv as [kr Hxrk].
        assert (Hr2 : 2 <= r) by (apply Znumtheory.prime_ge_2; exact HrPrime).
        assert (Hkr : 1 <= kr) by nia.
        specialize (Hcomplete r).
        assert (HrIn : In r (a :: b :: nil)).
        { apply Hcomplete.
          split.
          - split.
            + split; [exact Hr2 | nia].
            + apply Hprime_iff; exact HrPrime.
          - exists kr; split; [exact Hkr | nia]. }
        simpl in HrIn.
        destruct HrIn as [Hr | [Hr | []]]; auto.
    + right; split; [exact Hnot_two |].
      intro HAlmost.
      unfold AlmostPrime in HAlmost.
      destruct HAlmost as
        [a [b [HaPrime [HbPrime [Hab [HaDiv [HbDiv Hall]]]]]]].
      assert (Ha2 : 2 <= a) by (apply Znumtheory.prime_ge_2; exact HaPrime).
      assert (Hb2 : 2 <= b) by (apply Znumtheory.prime_ge_2; exact HbPrime).
      destruct HaDiv as [ka Hxka].
      destruct HbDiv as [kb Hxkb].
      assert (Hka : 1 <= ka) by nia.
      assert (Hkb : 1 <= kb) by nia.
      assert (HaIn : In a divs).
      { apply Hcomplete.
        split.
        - split.
          + split; [exact Ha2 | nia].
          + apply Hprime_iff; exact HaPrime.
        - exists ka; split; [exact Hka | nia]. }
      assert (HbIn : In b divs).
      { apply Hcomplete.
        split.
        - split.
          + split; [exact Hb2 | nia].
          + apply Hprime_iff; exact HbPrime.
        - exists kb; split; [exact Hkb | nia]. }
      assert (Hmembers : forall r : Z, In r divs <-> In r (a :: b :: nil)).
      { intro r; split.
        - intro HrIn.
          destruct (Hsound r HrIn) as
            [[[Hr2 Hrp] HrPrimeRaw] [kr [Hkr Hxrk]]].
          assert (HrPrime : Znumtheory.prime r) by (apply Hprime_iff; auto).
          assert (HrDiv : (r | x)) by (exists kr; nia).
          specialize (Hall r HrPrime HrDiv).
          simpl; destruct Hall as [-> | ->]; auto.
        - simpl; intros [-> | [-> | []]]; assumption. }
      assert (Hnodup_ab : NoDup (a :: b :: nil)).
      { constructor.
        - simpl; intro HaEq; destruct HaEq as [HaEq | []]; exact (Hab (eq_sym HaEq)).
        - constructor; [simpl; auto | constructor]. }
      pose proof (NoDup_Permutation Hnodup Hnodup_ab Hmembers)
        as Hperm.
      pose proof (Permutation_length Hperm) as Hlength.
      rewrite !Zlength_correct in Hlen.
      simpl in Hlength.
      lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH12 x H).
  destruct PreH12 as [[Hcount0 Hcountb]
    [divs [[[Hlen Hnodup] Hsound] Hcomplete]]].
  split.
  - split; [exact Hcount0 | lia].
  - exists divs.
    split.
    + split.
      * split; assumption.
      * intros q HqIn.
        destruct (Hsound q HqIn) as
          [[[Hq2 HqPrime] [kq [Hkq Hxq]]] Hrange].
        split.
        { split.
          - split; [exact Hq2 | destruct Hrange as [Hlt | [Heq Hxm]]; lia].
          - exact HqPrime. }
        exists kq; split; assumption.
    + intros q Hq.
      destruct Hq as [[[Hq2 Hqlt] HqPrime] [kq [Hkq Hxq]]].
      apply Hcomplete.
      split.
      * split.
        { split; [exact Hq2 | exact HqPrime]. }
        exists kq; split; assumption.
      * assert (q < p \/ q = p) as Hqp by lia.
        destruct Hqp as [Hqp | Hqp].
        { left; exact Hqp. }
        right; split; [exact Hqp | lia].
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH4.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH11 v ltac:(lia)).
  destruct PreH11 as [_ [[_ Halmost] | [Hnot_two _]]]; [|contradiction].
  unfold Spec in *.
  assert (Hcard : forall high,
      @SpecHelpers.set_card Z (fun x => 1 <= x < high /\ AlmostPrime x)
        (SumLib.ZRange.finite_Z_range' 1 high AlmostPrime) =
      @SumLib.Sum.sum Z (fun x => 1 <= x < high)
        (SumLib.ZRange.finite_Z_range 1 high)
        (fun x => if SumLib.Sum.prop_dec (AlmostPrime x) then 1 else 0)).
  {
    intros high.
    unfold SpecHelpers.set_card, SumLib.Sum.sum.
    change
      (fold_right (fun _ acc : Z => 1 + acc) 0
         (filter
            (fun x =>
               if SumLib.Sum.prop_dec (AlmostPrime x) then true else false)
            (SumLib.ZRange.Zrange 1 high)) =
       fold_right
         (fun x acc : Z =>
            (if SumLib.Sum.prop_dec (AlmostPrime x) then 1 else 0) + acc)
         0 (SumLib.ZRange.Zrange 1 high)).
    assert (Hfilter : forall (test : Z -> bool) (l : list Z),
        fold_right (fun _ acc : Z => 1 + acc) 0 (filter test l) =
        fold_right
          (fun x acc : Z => (if test x then 1 else 0) + acc) 0 l).
    {
      intros test l.
      induction l as [|x xs IH].
      - reflexivity.
      - remember (test x) as b eqn:Htest.
        destruct b.
        + cbn [filter fold_right].
          rewrite <- Htest.
          cbn [filter fold_right].
          f_equal.
          exact IH.
        + cbn [filter fold_right].
          rewrite <- Htest.
          cbn [filter fold_right].
          exact IH.
    }
    rewrite Hfilter.
    induction (SumLib.ZRange.Zrange 1 high) as [|x xs IH].
    - reflexivity.
    - cbn [fold_right].
      remember (SumLib.Sum.prop_dec (AlmostPrime x)) as d eqn:Hdec.
      destruct d.
      + cbn.
        rewrite IH.
        reflexivity.
      + cbn.
        exact IH.
  }
  rewrite Hcard in PreH9 |- *.
  replace (v - 1 + 1) with v in PreH9 by lia.
  replace (v + 1 - 1 + 1) with (v + 1) by lia.
  rewrite (SumLib.ZRange.sum_Z_range_extend_right 1 v) by lia.
  destruct (SumLib.Sum.prop_dec (AlmostPrime v)) as [Hap | Hnap].
  - lia.
  - contradiction.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH11 v ltac:(lia)).
  destruct PreH11 as [_ [[Htwo _] | [_ Hnot_almost]]]; [contradiction|].
  unfold Spec in *.
  assert (Hcard : forall high,
      @SpecHelpers.set_card Z (fun x => 1 <= x < high /\ AlmostPrime x)
        (SumLib.ZRange.finite_Z_range' 1 high AlmostPrime) =
      @SumLib.Sum.sum Z (fun x => 1 <= x < high)
        (SumLib.ZRange.finite_Z_range 1 high)
        (fun x => if SumLib.Sum.prop_dec (AlmostPrime x) then 1 else 0)).
  {
    intros high.
    unfold SpecHelpers.set_card, SumLib.Sum.sum.
    change
      (fold_right (fun _ acc : Z => 1 + acc) 0
         (filter
            (fun x =>
               if SumLib.Sum.prop_dec (AlmostPrime x) then true else false)
            (SumLib.ZRange.Zrange 1 high)) =
       fold_right
         (fun x acc : Z =>
            (if SumLib.Sum.prop_dec (AlmostPrime x) then 1 else 0) + acc)
         0 (SumLib.ZRange.Zrange 1 high)).
    assert (Hfilter : forall (test : Z -> bool) (l : list Z),
        fold_right (fun _ acc : Z => 1 + acc) 0 (filter test l) =
        fold_right
          (fun x acc : Z => (if test x then 1 else 0) + acc) 0 l).
    {
      intros test l.
      induction l as [|x xs IH].
      - reflexivity.
      - remember (test x) as b eqn:Htest.
        destruct b.
        + cbn [filter fold_right].
          rewrite <- Htest.
          cbn [filter fold_right].
          f_equal.
          exact IH.
        + cbn [filter fold_right].
          rewrite <- Htest.
          cbn [filter fold_right].
          exact IH.
    }
    rewrite Hfilter.
    induction (SumLib.ZRange.Zrange 1 high) as [|x xs IH].
    - reflexivity.
    - cbn [fold_right].
      remember (SumLib.Sum.prop_dec (AlmostPrime x)) as d eqn:Hdec.
      destruct d.
      + cbn.
        rewrite IH.
        reflexivity.
      + cbn.
        exact IH.
  }
  rewrite Hcard in PreH9 |- *.
  replace (v - 1 + 1) with v in PreH9 by lia.
  replace (v + 1 - 1 + 1) with (v + 1) by lia.
  rewrite (SumLib.ZRange.sum_Z_range_extend_right 1 v) by lia.
  destruct (SumLib.Sum.prop_dec (AlmostPrime v)) as [Hap | Hnap].
  - contradiction.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace n_pre with (v - 1) by lia.
  exact PreH8.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
