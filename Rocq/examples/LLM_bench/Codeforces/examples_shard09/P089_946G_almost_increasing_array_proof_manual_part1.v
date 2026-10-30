From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_lib.
Local Open Scope sac.



Lemma proof_of_upd_safety_wit_1_split_goal_1 : upd_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_update_fenwick i ltac:(lia)) as Hlow.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_upd_safety_wit_1_split_goal_2 : upd_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_update_fenwick i ltac:(lia)) as Hlow.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_upd_safety_wit_1 : upd_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_upd_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_upd_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_upd_safety_wit_3_split_goal_1 : upd_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_update_fenwick i ltac:(lia)) as Hlow.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_upd_safety_wit_3_split_goal_2 : upd_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_update_fenwick i ltac:(lia)) as Hlow.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_upd_safety_wit_3 : upd_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_upd_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_upd_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_upd_entail_wit_1_split_goal_1 : upd_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MaxBitAddProgress.
  split; [ reflexivity | ].
  split.
  - intros _.
    apply maxbit_covers_self__bit_update_fenwick.
    lia.
  - intros t Ht.
    split.
    + intros [Hc Hlt].
      unfold MaxBitCovers in Hc.
      lia.
    + intros _.
      reflexivity.
Qed.

Lemma proof_of_upd_entail_wit_1_split_goal_2 : upd_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  apply PreH9.
  auto.
Qed.

Lemma proof_of_upd_entail_wit_1 : upd_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_upd_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_upd_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_upd_entail_wit_2_1_split_goal_1 : upd_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_update_fenwick i ltac:(lia)) as Hlow.
  unfold MaxBitAddProgress in PreH15.
  destruct PreH15 as [Hlen [Hcov Hstep]].
  assert (Hci : MaxBitCovers i i_pre) by (apply Hcov; lia).
  assert (Hbnd : 0 <= i < Zlength bit_cur_2) by lia.
  unfold MaxBitAddProgress.
  split.
  { rewrite zlength_replace_Znth__bit_update_fenwick. exact Hlen. }
  split.
  - intros _.
    apply maxbit_covers_ancestor__bit_update_fenwick; [ lia | exact Hci ].
  - intros t Ht.
    specialize (Hstep t Ht).
    destruct Hstep as [Hupd Hold].
    destruct (Z.eq_dec t i) as [Hti | Hti].
    + subst t.
      assert (Hcur : Znth i bit_cur_2 0 = Znth i bit_l 0)
        by (apply Hold; right; lia).
      rewrite (Znth_replace_Znth_Same 0 bit_cur_2 i v_pre Hbnd).
      split.
      * intros _. lia.
      * intros [Hnc | Hge].
        -- contradiction.
        -- lia.
    + assert (Hbndt : 0 <= t < Zlength bit_cur_2) by lia.
      rewrite (Znth_replace_Znth_Diff 0 bit_cur_2 i t v_pre Hbnd Hbndt
                 ltac:(congruence)).
      split.
      * intros [Hc Hlt].
        apply Hupd.
        split; [ exact Hc | ].
        destruct (Z_le_gt_dec t i) as [Hle | Hgt]; [ lia | ].
        exfalso.
        pose proof (maxbit_nodelo_gap__bit_update_fenwick i t
                      ltac:(lia) ltac:(lia)) as Hgap.
        unfold MaxBitCovers in Hc.
        lia.
      * intros [Hnc | Hge].
        -- apply Hold. left. exact Hnc.
        -- apply Hold. right. lia.
Qed.

Lemma proof_of_upd_entail_wit_2_1_split_goal_2 : upd_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite zlength_replace_Znth__bit_update_fenwick.
  exact PreH12.
Qed.

Lemma proof_of_upd_entail_wit_2_1_split_goal_3 : upd_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_update_fenwick i ltac:(lia)) as Hlow.
  lia.
Qed.

Lemma proof_of_upd_entail_wit_2_1_split_goal_4 : upd_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_update_fenwick i ltac:(lia)) as Hlow.
  lia.
Qed.

Lemma proof_of_upd_entail_wit_2_1 : upd_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_upd_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_upd_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_upd_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_upd_entail_wit_2_1_split_goal_4.
Qed.

Lemma proof_of_upd_entail_wit_2_2_split_goal_1 : upd_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_update_fenwick i ltac:(lia)) as Hlow.
  unfold MaxBitAddProgress in PreH15.
  destruct PreH15 as [Hlen [Hcov Hstep]].
  assert (Hci : MaxBitCovers i i_pre) by (apply Hcov; lia).
  unfold MaxBitAddProgress.
  split; [ exact Hlen | ].
  split.
  - intros _.
    apply maxbit_covers_ancestor__bit_update_fenwick; [ lia | exact Hci ].
  - intros t Ht.
    specialize (Hstep t Ht).
    destruct Hstep as [Hupd Hold].
    split.
    + intros [Hc Hlt].
      destruct (Z_le_gt_dec t i) as [Hle | Hgt].
      * destruct (Z.eq_dec t i) as [Hti | Hti].
        -- subst t.
           assert (Hcur : Znth i bit_cur_2 0 = Znth i bit_l 0)
             by (apply Hold; right; lia).
           lia.
        -- apply Hupd. split; [ exact Hc | lia ].
      * exfalso.
        pose proof (maxbit_nodelo_gap__bit_update_fenwick i t
                      ltac:(lia) ltac:(lia)) as Hgap.
        unfold MaxBitCovers in Hc.
        lia.
    + intros [Hnc | Hge].
      * apply Hold. left. exact Hnc.
      * apply Hold. right. lia.
Qed.

Lemma proof_of_upd_entail_wit_2_2_split_goal_2 : upd_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_update_fenwick i ltac:(lia)) as Hlow.
  lia.
Qed.

Lemma proof_of_upd_entail_wit_2_2_split_goal_3 : upd_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_update_fenwick i ltac:(lia)) as Hlow.
  lia.
Qed.

Lemma proof_of_upd_entail_wit_2_2 : upd_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_upd_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_upd_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_upd_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_upd_return_wit_1_split_goal_1 : upd_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (maxbit_rep_of_progress__bit_update_fenwick
           m bit_l bit_cur nvals_pre i_pre i v_pre);
    [ lia | lia | exact PreH13 | exact PreH14 ].
Qed.

Lemma proof_of_upd_return_wit_1_split_goal_2 : upd_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  apply PreH12.
  auto.
Qed.

Lemma proof_of_upd_return_wit_1 : upd_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_upd_return_wit_1_split_goal_1.
  - Goal_apply proof_of_upd_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_qry_safety_wit_4_split_goal_1 : qry_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_query_fenwick i ltac:(lia)) as Hlb.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_qry_safety_wit_4_split_goal_2 : qry_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_query_fenwick i ltac:(lia)) as Hlb.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_qry_safety_wit_4 : qry_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_qry_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_qry_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_qry_safety_wit_6_split_goal_1 : qry_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_query_fenwick i ltac:(lia)) as Hlb.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_qry_safety_wit_6_split_goal_2 : qry_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_query_fenwick i ltac:(lia)) as Hlb.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_qry_safety_wit_6 : qry_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_qry_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_qry_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_qry_entail_wit_1_split_goal_1 : qry_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MaxBitQueryState.
  rewrite (rangemax_empty__bit_query_fenwick m (i_pre + 1) (i_pre + 1) ltac:(lia)).
  unfold MaxBitNeg. reflexivity.
Qed.

Lemma proof_of_qry_entail_wit_1_split_goal_2 : qry_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH7; assumption.
Qed.

Lemma proof_of_qry_entail_wit_1 : qry_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_qry_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_qry_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_qry_entail_wit_2_1_split_goal_1 : qry_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MaxBitQueryState in *.
  destruct PreH13 as [Hlen Hrep].
  pose proof (lowbit_pos_le__bit_query_fenwick i ltac:(lia)) as Hlb.
  pose proof (Hrep i ltac:(lia)) as Hi.
  unfold MaxBitNodeLo, MaxBitLowbit in Hi.
  rewrite (rangemax_concat__bit_query_fenwick m (i - Z.land i (- i) + 1) (i + 1) (i_pre + 1) ltac:(lia) ltac:(lia)).
  rewrite <- Hi. rewrite <- PreH14. lia.
Qed.

Lemma proof_of_qry_entail_wit_2_1_split_goal_2 : qry_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_query_fenwick i ltac:(lia)) as Hlb.
  lia.
Qed.

Lemma proof_of_qry_entail_wit_2_1_split_goal_3 : qry_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_query_fenwick i ltac:(lia)) as Hlb.
  lia.
Qed.

Lemma proof_of_qry_entail_wit_2_1 : qry_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_qry_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_qry_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_qry_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_qry_entail_wit_2_2_split_goal_1 : qry_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MaxBitQueryState in *.
  destruct PreH13 as [Hlen Hrep].
  pose proof (lowbit_pos_le__bit_query_fenwick i ltac:(lia)) as Hlb.
  pose proof (Hrep i ltac:(lia)) as Hi.
  unfold MaxBitNodeLo, MaxBitLowbit in Hi.
  rewrite (rangemax_concat__bit_query_fenwick m (i - Z.land i (- i) + 1) (i + 1) (i_pre + 1) ltac:(lia) ltac:(lia)).
  rewrite <- Hi. rewrite <- PreH14. lia.
Qed.

Lemma proof_of_qry_entail_wit_2_2_split_goal_2 : qry_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_query_fenwick i ltac:(lia)) as Hlb.
  lia.
Qed.

Lemma proof_of_qry_entail_wit_2_2_split_goal_3 : qry_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (lowbit_pos_le__bit_query_fenwick i ltac:(lia)) as Hlb.
  lia.
Qed.

Lemma proof_of_qry_entail_wit_2_2 : qry_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_qry_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_qry_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_qry_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_qry_return_wit_1_split_goal_1 : qry_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MaxBitQueryState in PreH13.
  replace (i + 1) with 1 in PreH13 by lia.
  exact PreH13.
Qed.

Lemma proof_of_qry_return_wit_1 : qry_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_qry_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_rank_of_entail_wit_1_split_goal_1 : rank_of_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold RankSearchState.
  split.
  - intros k Hk. lia.
  - destruct PreH8 as [k0 [Hk0 Hk0v]].
    destruct (Z.eq_dec k0 (nvals_pre - 1)) as [Heq | Hne].
    + subst k0. lia.
    + assert (Znth k0 vals_l 0 < Znth (nvals_pre - 1) vals_l 0)
        by (apply PreH7; lia).
      lia.
Qed.

Lemma proof_of_rank_of_entail_wit_1_split_goal_2 : rank_of_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH9; lia.
Qed.

Lemma proof_of_rank_of_entail_wit_1 : rank_of_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rank_of_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_rank_of_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_rank_of_entail_wit_2_split_goal_1 : rank_of_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_lt_upper_bound (lo + hi) 2 hi ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_rank_of_entail_wit_2_split_goal_2 : rank_of_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_le_lower_bound (lo + hi) 2 lo ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_rank_of_entail_wit_2_split_goal_3 : rank_of_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH8; lia.
Qed.

Lemma proof_of_rank_of_entail_wit_2 : rank_of_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rank_of_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_rank_of_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_rank_of_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_rank_of_entail_wit_3_1_split_goal_1 : rank_of_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH15 as [Hleft Hright].
  unfold RankSearchState.
  split; [ | exact Hright ].
  intros k Hk.
  destruct (Z_lt_le_dec k lo) as [Hklo | Hklo].
  - apply Hleft. lia.
  - assert (Znth k vals_l 0 <= Znth mid vals_l 0) as Hle.
    { destruct (Z.eq_dec k mid) as [Heq | Hne].
      - subst k. lia.
      - assert (Znth k vals_l 0 < Znth mid vals_l 0) by (apply PreH9; lia).
        lia. }
    lia.
Qed.

Lemma proof_of_rank_of_entail_wit_3_1_split_goal_2 : rank_of_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH8; lia.
Qed.

Lemma proof_of_rank_of_entail_wit_3_1 : rank_of_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rank_of_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_rank_of_entail_wit_3_1_split_goal_2.
Qed.

Lemma proof_of_rank_of_entail_wit_3_2_split_goal_1 : rank_of_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH15 as [Hleft Hright].
  unfold RankSearchState.
  split; [ exact Hleft | lia ].
Qed.

Lemma proof_of_rank_of_entail_wit_3_2_split_goal_2 : rank_of_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH8; lia.
Qed.

Lemma proof_of_rank_of_entail_wit_3_2 : rank_of_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rank_of_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_rank_of_entail_wit_3_2_split_goal_2.
Qed.

Lemma proof_of_rank_of_return_wit_1_split_goal_1 : rank_of_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (lo = hi) as Heq by lia.
  subst hi.
  pose proof (rank_search_pin__rank_binary_search vals_l nvals_pre v_pre lo
                PreH9 PreH10 PreH14 ltac:(lia)) as Hpin.
  destruct PreH14 as [Hleft Hright].
  unfold RankResult.
  split; [ lia | ].
  split.
  - replace (lo + 1 - 1) with lo by lia. exact Hpin.
  - intros k Hk. apply Hleft. lia.
Qed.

Lemma proof_of_rank_of_return_wit_1 : rank_of_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_rank_of_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hseg : forall (m : nat) (x lo hi : Z),
            hi - lo = Z.of_nat m ->
            Int64Array.seg_shape x lo hi
            |-- EX l, “ Zlength l = hi - lo ” && Int64Array.seg x lo hi l).
  { clear.
    induction m as [| m IH]; intros x lo hi Hm.
    - assert (hi = lo) as He by lia. subst hi.
      rewrite Int64Array.seg_shape_empty.
      Exists (@nil Z).
      rewrite Int64Array.seg_empty.
      split_pure_spatial.
      + cancel.
      + split_pures.
        * dump_pre_spatial. rewrite Zlength_nil. lia.
        * dump_pre_spatial. lia.
    - assert (lo < hi) as Hlt by lia.
      rewrite (Int64Array.seg_shape_unfold x lo hi Hlt).
      Intros a.
      sep_apply_l_atomic (IH x (lo + 1) hi).
      + dump_pre_spatial. lia.
      + Intros l.
        Exists (a :: l).
        rewrite (Int64Array.seg_unfold x lo hi l a).
        split_pure_spatial.
        * cancel.
        * split_pures. dump_pre_spatial. rewrite Zlength_cons. lia. }
  assert (Hfull : forall (x n : Z),
            0 <= n ->
            Int64Array.full_shape x n |-- EX l, “ Zlength l = n ” && Int64Array.full x n l).
  { clear - Hseg.
    intros x n Hn.
    sep_apply_l_atomic (Int64Array.full_shape_to_seg_shape x n).
    sep_apply_l_atomic (Hseg (Z.to_nat n) x 0 n).
    - dump_pre_spatial. lia.
    - Intros l.
      Exists l.
      sep_apply_l_atomic (Int64Array.seg_to_full x 0 n l).
      replace (x + 0 * sizeof ( INT64 )) with x by lia.
      replace (n - 0) with n by lia.
      split_pure_spatial.
      + cancel.
      + split_pures. dump_pre_spatial. lia. }
  sep_apply_l_atomic (Hfull c_pre n_pre).
  - dump_pre_spatial. lia.
  - Intros c_l.
    Exists c_l.
    split_pure_spatial.
    + do 8 cancel.
    + split_pures; dump_pre_spatial;
      try (intros ? ?; exfalso; lia);
      try lia;
      try assumption.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (keyprefix_extend__key_and_vals_fill values c_l_2
           (replace_Znth i (Znth i values 0 - i) c_l_2) i).
  - lia.
  - exact PreH9.
  - unfold KeyAt. apply Znth_replace_Znth_Same. lia.
  - intros j Hj. apply Znth_replace_Znth_Diff; lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = n_pre) by lia. subst i.
  assert (Hseg : forall (m : nat) (x lo hi : Z),
            hi - lo = Z.of_nat m ->
            IntArray.seg_shape x lo hi
            |-- EX l, “ Zlength l = hi - lo ” && IntArray.seg x lo hi l).
  { clear.
    induction m as [| m IH]; intros x lo hi Hm.
    - assert (hi = lo) as He by lia. subst hi.
      rewrite IntArray.seg_shape_empty.
      Exists (@nil Z).
      rewrite IntArray.seg_empty.
      split_pure_spatial.
      + cancel.
      + split_pures.
        * dump_pre_spatial. rewrite Zlength_nil. lia.
        * dump_pre_spatial. lia.
    - assert (lo < hi) as Hlt by lia.
      rewrite (IntArray.seg_shape_unfold x lo hi Hlt).
      Intros a.
      sep_apply_l_atomic (IH x (lo + 1) hi).
      + dump_pre_spatial. lia.
      + Intros l.
        Exists (a :: l).
        rewrite (IntArray.seg_unfold x lo hi l a).
        split_pure_spatial.
        * cancel.
        * split_pures. dump_pre_spatial. rewrite Zlength_cons. lia. }
  assert (Hfull : forall (x n : Z),
            0 <= n ->
            IntArray.full_shape x n |-- EX l, “ Zlength l = n ” && IntArray.full x n l).
  { clear - Hseg.
    intros x n Hn.
    sep_apply_l_atomic (IntArray.full_shape_to_seg_shape x n).
    sep_apply_l_atomic (Hseg (Z.to_nat n) x 0 n).
    - dump_pre_spatial. lia.
    - Intros l.
      Exists l.
      sep_apply_l_atomic (IntArray.seg_to_full x 0 n l).
      replace (x + 0 * sizeof ( INT )) with x by lia.
      replace (n - 0) with n by lia.
      split_pure_spatial.
      + cancel.
      + split_pures. dump_pre_spatial. lia. }
  sep_apply_l_atomic (Hfull vals_pre (2 * n_pre)).
  - dump_pre_spatial. lia.
  - Intros vals_l.
    Exists vals_l c_l_2.
    split_pure_spatial.
    + do 8 cancel.
    + split_pures; dump_pre_spatial;
      try (intros ? ?; exfalso; lia);
      try lia;
      try assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (valsraw_extend__key_and_vals_fill values vals_l_2
           (replace_Znth (2 * i + 1) (Znth i c_l_2 0 + 1)
              (replace_Znth (2 * i) (Znth i c_l_2 0) vals_l_2)) i).
  - lia.
  - exact PreH13.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    apply PreH11. lia.
  - rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia).
    rewrite (PreH11 i ltac:(lia)). reflexivity.
  - intros j Hj.
    rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH14. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace n_pre with i by lia. exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst nvals.
  Exists l1 l1 vals_l c_l_2.
  assert (HL : Zlength l1 = 2 * n_pre)
    by (rewrite <- (perm_Zlength__dedup_scan _ _ PreH1); exact PreH9).
  assert (Hrange : forall k, 0 <= k < 2 * n_pre ->
                   -2000000000 <= Znth k l1 0 <= 2000000000).
  { intros k Hk.
    apply (perm_range_bound__dedup_scan vals_l l1 (-2000000000) 2000000000 PreH1).
    - intros k0 Hk0. apply PreH13. lia.
    - lia. }
  assert (HD : DedupState l1 l1 0 0).
  { unfold DedupState. split; [| split; [| split; [| split]]].
    - intros p q Hp Hpq Hq. lia.
    - intros p Hp. exfalso. lia.
    - intros q Hq. exfalso. lia.
    - intros Hs. exfalso. lia.
    - intros p Hp. reflexivity. }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
    try solve [ assumption | lia | auto ].
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst nvals.
  Exists (replace_Znth uniq (Znth i cur_l_2 0) cur_l_2) sorted_l_2 raw_l_2 c_l_2.
  assert (HZ : Zlength (replace_Znth uniq (Znth i cur_l_2 0) cur_l_2) = 2 * n_pre)
    by (rewrite Zlength_replace_Znth; exact PreH11).
  assert (Hrange : forall k, 0 <= k < 2 * n_pre ->
      -2000000000 <= Znth k (replace_Znth uniq (Znth i cur_l_2 0) cur_l_2) 0 <= 2000000000).
  { intros k Hk. destruct (Z.eq_dec k uniq) as [He | He].
    - subst k. rewrite Znth_replace_Znth_Same by lia. apply PreH18. lia.
    - rewrite Znth_replace_Znth_Diff by lia. apply PreH18. lia. }
  assert (Htail : forall p, uniq + 1 <= p < 2 * n_pre ->
      Znth p (replace_Znth uniq (Znth i cur_l_2 0) cur_l_2) 0 = Znth p sorted_l_2 0).
  { intros p Hp. rewrite Znth_replace_Znth_Diff by lia. apply PreH22. lia. }
  assert (HD : DedupState sorted_l_2 (replace_Znth uniq (Znth i cur_l_2 0) cur_l_2)
                 (uniq + 1) (i + 1)).
  { apply dedup_keep_step__dedup_scan; try lia.
    - exact PreH16.
    - intros p Hp. apply PreH22. lia.
    - exact PreH23. }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
    try solve [ assumption | lia | auto ].
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst nvals.
  Exists (replace_Znth uniq (Znth i cur_l_2 0) cur_l_2) sorted_l_2 raw_l_2 c_l_2.
  assert (HZ : Zlength (replace_Znth uniq (Znth i cur_l_2 0) cur_l_2) = 2 * n_pre)
    by (rewrite Zlength_replace_Znth; exact PreH12).
  assert (Hrange : forall k, 0 <= k < 2 * n_pre ->
      -2000000000 <= Znth k (replace_Znth uniq (Znth i cur_l_2 0) cur_l_2) 0 <= 2000000000).
  { intros k Hk. destruct (Z.eq_dec k uniq) as [He | He].
    - subst k. rewrite Znth_replace_Znth_Same by lia. apply PreH19. lia.
    - rewrite Znth_replace_Znth_Diff by lia. apply PreH19. lia. }
  assert (Htail : forall p, uniq + 1 <= p < 2 * n_pre ->
      Znth p (replace_Znth uniq (Znth i cur_l_2 0) cur_l_2) 0 = Znth p sorted_l_2 0).
  { intros p Hp. rewrite Znth_replace_Znth_Diff by lia. apply PreH23. lia. }
  assert (HD : DedupState sorted_l_2 (replace_Znth uniq (Znth i cur_l_2 0) cur_l_2)
                 (uniq + 1) (i + 1)).
  { apply dedup_keep_step__dedup_scan; try lia.
    - exact PreH17.
    - intros p Hp. apply PreH23. lia.
    - exact PreH24. }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
    try solve [ assumption | lia | auto ].
Qed.

Lemma proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst nvals.
  Exists cur_l_2 sorted_l_2 raw_l_2 c_l_2.
  assert (HD : DedupState sorted_l_2 cur_l_2 uniq (i + 1)).
  { apply dedup_skip_step__dedup_scan; try lia.
    - intros p Hp. apply PreH23. lia.
    - exact PreH24. }
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
    try solve [ assumption | lia | auto ].
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hseg : forall (m : nat) (x lo hi : Z),
                   hi - lo = Z.of_nat m ->
                   IntArray.seg_shape x lo hi
                   |-- EX l, “ Zlength l = hi - lo ” && IntArray.seg x lo hi l).
  { intros m. induction m; intros x lo hi Hm.
    - assert (hi = lo) as He by lia. subst hi.
      rewrite IntArray.seg_shape_empty.
      Exists (@nil Z).
      rewrite IntArray.seg_empty.
      split_pure_spatial.
      + cancel.
      + split_pures.
        * dump_pre_spatial. rewrite Zlength_nil. lia.
        * dump_pre_spatial. lia.
    - assert (lo < hi) as Hlt by lia.
      rewrite (IntArray.seg_shape_unfold x lo hi Hlt).
      Intros a.
      sep_apply (IHm x (lo + 1) hi ltac:(lia)).
      Intros l.
      Exists (a :: l).
      rewrite IntArray.seg_unfold.
      split_pure_spatial.
      + cancel.
      + split_pures. dump_pre_spatial. rewrite Zlength_cons. lia. }
  assert (Hsplit : forall (x n m : Z),
                     0 <= n <= m ->
                     IntArray.full_shape x m
                     |-- EX l, “ Zlength l = n ”
                               && IntArray.full x n l ** IntArray.seg_shape x n m).
  { intros x n m Hnm.
    sep_apply (IntArray.full_shape_split_to_seg_shape x n m Hnm).
    sep_apply (Hseg (Z.to_nat n) x 0 n ltac:(lia)).
    Intros l.
    Exists l.
    change (IntArray.full x n l) with (IntArray.seg x 0 n l).
    split_pure_spatial.
    - cancel.
    - split_pures. dump_pre_spatial. lia. }
  assert (i = 2 * n_pre) as Hi by lia.
  subst i.
  assert (1 <= uniq) as Huniq.
  { unfold DedupState in PreH22.
    destruct PreH22 as [_ [_ [_ [Hne _]]]].
    destruct (Hne ltac:(lia)) as [Hu _]. lia. }
  assert (CompressedKeys values cur_l uniq) as Hck.
  { apply (dedup_to_compressed__compressed_keys values raw_l sorted_l cur_l n_pre uniq (2 * n_pre));
    try assumption; try lia. }
  sep_apply (Hsplit bit0_pre (uniq + 1) (2 * n_pre + 1) ltac:(lia)).
  Intros bit0_l.
  sep_apply (Hsplit bit1_pre (uniq + 1) (2 * n_pre + 1) ltac:(lia)).
  Intros bit1_l.
  sep_apply (Hsplit bitX_pre (uniq + 1) (2 * n_pre + 1) ltac:(lia)).
  Intros bitX_l.
  Exists bitX_l bit1_l bit0_l cur_l c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [ assumption | lia ].
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_1 : solver_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_2 : solver_entail_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_solver_entail_wit_10_split_goal_3 : solver_entail_wit_10_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hrec : forall (nn : nat) (xx lo hi : Z),
      store_undef_array_rec (fun p j => EX a, StoreIntAsElement.storeA p j a) xx lo hi nn
      |-- EX l : list Z, “ Zlength l = Z.of_nat nn ” && store_array_rec StoreIntAsElement.storeA xx lo hi l).
  { induction nn as [| nn IHnn]; intros xx lo hi; simpl.
    - Intros_p Hlo. Exists (@nil Z). simpl.
      split_pure_spatial.
      + cancel.
      + split_pures; dump_pre_spatial; auto.
    - Intros a. sep_apply IHnn. Intros l. Exists (a :: l). simpl.
      split_pure_spatial.
      + cancel.
      + split_pures. dump_pre_spatial. rewrite Zlength_cons. lia. }
  assert (Hfull : forall (xx nn : Z), 0 <= nn ->
      IntArray.full_shape xx nn |-- EX l : list Z, “ Zlength l = nn ” && IntArray.full xx nn l).
  { intros xx nn Hnn.
    unfold IntArray.full_shape, IntArray.full, store_undef_array, store_array.
    sep_apply Hrec. Intros l. Exists l.
    unfold StoreIntAsElement.storeA.
    split_pure_spatial.
    - cancel.
    - split_pures. dump_pre_spatial. lia. }
  assert (Hs0 : forall k, 0 <= k <= nvals -> Znth k bit0_l_2 0 = MaxBitNeg).
  { intros k Hk. unfold MaxBitNeg.
    destruct (PreH20 k ltac:(lia)) as [[Hb0 Hb1] HbX]. exact Hb0. }
  assert (Hs1 : forall k, 0 <= k <= nvals -> Znth k bit1_l_2 0 = MaxBitNeg).
  { intros k Hk. unfold MaxBitNeg.
    destruct (PreH20 k ltac:(lia)) as [[Hb0 Hb1] HbX]. exact Hb1. }
  assert (HsX : forall k, 0 <= k <= nvals -> Znth k bitX_l_2 0 = MaxBitNeg).
  { intros k Hk. unfold MaxBitNeg.
    destruct (PreH20 k ltac:(lia)) as [[Hb0 Hb1] HbX]. exact HbX. }
  sep_apply (Hfull dp0_pre n_pre ltac:(lia)).
  Intros dp0_l.
  Exists bitX_l_2 bit1_l_2 bit0_l_2 bitX_l_2 bit1_l_2 bit0_l_2 dp0_l vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
    + intros k3 Hk3.
      rewrite (Hs0 k3 ltac:(lia)), (Hs1 k3 ltac:(lia)), (HsX k3 ltac:(lia)).
      unfold MaxBitNeg. lia.
    + apply maxbit_rep_sentinel__bit_clear_loop;
        [ lia | lia | exact Hs0 | intros t Ht; apply Hs0; lia ].
    + apply maxbit_rep_sentinel__bit_clear_loop;
        [ lia | lia | exact Hs1 | intros t Ht; apply Hs1; lia ].
    + apply maxbit_rep_sentinel__bit_clear_loop;
        [ lia | lia | exact HsX | intros t Ht; apply HsX; lia ].
    + intros r Hr.
      rewrite (Hs0 r ltac:(lia)), (Hs1 r ltac:(lia)), (HsX r ltac:(lia)).
      unfold MaxBitNeg. lia.
    + apply dp0_prefix_zero__bit_clear_loop. lia.
    + apply bit0_model_sentinel__bit_clear_loop;
        [ lia | lia | intros r Hr; apply Hs0; lia ].
    + apply bit1_model_sentinel__bit_clear_loop;
        [ lia | lia | intros r Hr; apply Hs1; lia ].
    + apply bit0_model_sentinel__bit_clear_loop;
        [ lia | lia | intros r Hr; apply HsX; lia ].
    + apply clamped_prefix_max_zero__bit_clear_loop. lia.
    + apply clamped_best1_zero__bit_clear_loop. lia.
    + apply clamped_prefix_max_zero__bit_clear_loop. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (retval + 1) dp0_l_2) 0 = retval + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (retval + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max retval 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_3 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (retval_2 + 1)).
  { replace (retval_2 + 1) with (Z.max (Z.max retval_5 retval_2) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_4 retval_5 retval_2);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (retval + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (retval_2 + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_4 (retval_2 + 1))
         (MaxBitInsert m0_2 retval_3 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0
                     = Z.max (Znth r m0_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0
                     = Z.max (Znth r m1_2 0) (retval_2 + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_4) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) m0_2 i nvals retval_3 (retval + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_4 (retval_2 + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (retval_2 + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (0 + 1)).
  { replace (0 + 1) with (Z.max retval_4 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_2 retval_4);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max (Z.max retval_5 retval) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_3 retval_5 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (0 + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (retval + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0
                     = Z.max (Znth r m0_2 0) (0 + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_2) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0
                     = Z.max (Znth r m1_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) m0_2 i nvals retval_2 (0 + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_3 (retval + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (retval + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_3 : solver_entail_wit_12_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (retval + 1) dp0_l_2) 0 = retval + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (retval + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max retval 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_3 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (retval_2 + 1)).
  { replace (retval_2 + 1) with (Z.max (Z.max retval_5 retval_2) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_4 retval_5 retval_2);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (retval + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (retval_2 + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_4 (retval_2 + 1))
         (MaxBitInsert m0_2 retval_3 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0
                     = Z.max (Znth r m0_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0
                     = Z.max (Znth r m1_2 0) (retval_2 + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_4) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) m0_2 i nvals retval_3 (retval + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_4 (retval_2 + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (retval_2 + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_4 : solver_entail_wit_12_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (0 + 1)).
  { replace (0 + 1) with (Z.max retval_4 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_2 retval_4);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max (Z.max retval_5 retval) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_3 retval_5 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (0 + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (retval + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0
                     = Z.max (Znth r m0_2 0) (0 + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_2) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0
                     = Z.max (Znth r m1_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) m0_2 i nvals retval_2 (0 + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_3 (retval + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (retval + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_5 : solver_entail_wit_12_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (retval + 1) dp0_l_2) 0 = retval + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (retval + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max retval 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_3 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (retval_2 + 1)).
  { replace (retval_2 + 1) with (Z.max (Z.max retval_2 retval_5) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_4 retval_2 retval_5);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (retval + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (retval_2 + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_4 (retval_2 + 1))
         (MaxBitInsert m0_2 retval_3 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0
                     = Z.max (Znth r m0_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0
                     = Z.max (Znth r m1_2 0) (retval_2 + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_4) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) m0_2 i nvals retval_3 (retval + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_4 (retval_2 + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (retval_2 + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_6 : solver_entail_wit_12_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (0 + 1)).
  { replace (0 + 1) with (Z.max retval_4 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_2 retval_4);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max (Z.max retval retval_5) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_3 retval retval_5);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (0 + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (retval + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0
                     = Z.max (Znth r m0_2 0) (0 + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_2) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0
                     = Z.max (Znth r m1_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) m0_2 i nvals retval_2 (0 + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_3 (retval + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (retval + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_7 : solver_entail_wit_12_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (retval + 1) dp0_l_2) 0 = retval + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (retval + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max retval 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_2 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (0 + 1)).
  { replace (0 + 1) with (Z.max (Z.max retval_4 retval_5) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_3 retval_4 retval_5);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (retval + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (0 + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (0 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_2 (retval + 1)) 0
                     = Z.max (Znth r m0_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_2 (retval + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_2) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_3 (0 + 1)) 0
                     = Z.max (Znth r m1_2 0) (0 + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_3 (0 + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) m0_2 i nvals retval_2 (retval + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_3 (0 + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (0 + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.
