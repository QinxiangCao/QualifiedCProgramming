From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P053_1594D_the_number_of_imposters_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P053_1594D_the_number_of_imposters_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hseg : forall (p : nat) (x lo hi : Z),
            hi - lo = Z.of_nat p ->
            IntArray.seg_shape x lo hi
            |-- EX l, “ Zlength l = hi - lo ” && IntArray.seg x lo hi l).
  { clear.
    induction p as [| p IH]; intros x lo hi Hp.
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
            IntArray.full_shape x n
            |-- EX l, “ Zlength l = n ” && IntArray.full x n l).
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
  sep_apply_l_atomic (Hfull head_pre (n_pre + 1)).
  - dump_pre_spatial. lia.
  - Intros hs.
    sep_apply_l_atomic (Hfull nxt_pre (2 * m_pre)).
    + dump_pre_spatial. pose proof (Zlength_nonneg comments). lia.
    + Intros ns.
      sep_apply_l_atomic (Hfull to_pre (2 * m_pre)).
      * dump_pre_spatial. pose proof (Zlength_nonneg comments). lia.
      * Intros ts.
        sep_apply_l_atomic (Hfull wt_pre (2 * m_pre)).
        -- dump_pre_spatial. pose proof (Zlength_nonneg comments). lia.
        -- Intros ws.
           sep_apply_l_atomic (Hfull color_pre (n_pre + 1)).
           ++ dump_pre_spatial. lia.
           ++ Intros cs.
              sep_apply_l_atomic (Hfull stack__pre (n_pre + 1)).
              ** dump_pre_spatial. lia.
              ** Intros ks.
                 Exists ks cs ws ts ns hs.
                 split_pure_spatial.
                 --- do 9 cancel.
                 --- split_pures; dump_pre_spatial;
                     try (unfold HeadsInitialised; intros; lia);
                     try (pose proof (Zlength_nonneg comments); lia);
                     try assumption.
                     intros i Hi.
                     specialize (PreH4 i Hi) as Hb.
                     specialize (PreH9 i Hi) as Hm.
                     intuition (auto with *).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold HeadsInitialised in *.
  intros i Hi.
  destruct (Z.eq_dec i v) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply PreH19.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ForwardStarRanges.
  split.
  - intros u Hu.
    rewrite PreH19 by lia.
    lia.
  - intros e He.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ForwardStar.
  repeat split; try lia.
  intros u Hu.
  exists (@nil Z).
  split.
  - rewrite PreH19 by lia.
    apply adj_end.
  - split.
    + constructor.
    + intros e.
      split.
      * intros Hin. inversion Hin.
      * intros He. lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  specialize (PreH10 q H) as Hmeta.
  destruct Hmeta as [[[Hbounds Hsrc] Htgt] Hkind].
  rewrite Hsrc, Htgt, Hkind.
  intuition (auto with *).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ForwardStarRanges in *.
  destruct PreH15 as [Hheads Hedges].
  unfold ForwardStar in PreH14.
  destruct PreH14 as [Hhs [Hns [Hts [Hws Hstar]]]].
  pose proof (PreH10 i ltac:(lia)) as Hi.
  assert (Hsrc : 1 <= Znth i comment_sources 0 <= n_pre) by tauto.
  assert (Hdst : 1 <= Znth i comment_targets 0 <= n_pre) by tauto.
  assert (Hneq : Znth i comment_sources 0 <> Znth i comment_targets 0) by tauto.
  assert (Hkind : Znth i comment_kinds 0 = 0 \/ Znth i comment_kinds 0 = 1) by tauto.
  split.
  - intros u Hu.
    destruct (Z.eq_dec u (Znth i comment_targets 0)) as [-> | Hudst].
    + rewrite Znth_replace_Znth_Same.
      * lia.
      * rewrite Zlength_replace_Znth__forward_star_build_step, Hhs. lia.
    + rewrite Znth_replace_Znth_Diff.
      * destruct (Z.eq_dec u (Znth i comment_sources 0)) as [-> | Husrc].
        -- rewrite Znth_replace_Znth_Same; lia.
        -- rewrite Znth_replace_Znth_Diff; try lia.
           pose proof (Hheads u Hu). lia.
      * rewrite Zlength_replace_Znth__forward_star_build_step, Hhs. lia.
      * rewrite Zlength_replace_Znth__forward_star_build_step, Hhs. lia.
      * lia.
  - intros e He.
    destruct (Z.eq_dec e (2 * i + 1)) as [-> | Heodd].
    + rewrite Znth_replace_Znth_Same by
          (rewrite Zlength_replace_Znth__forward_star_build_step, Hns; lia).
      rewrite Znth_replace_Znth_Same by
          (rewrite Zlength_replace_Znth__forward_star_build_step, Hts; lia).
      rewrite Znth_replace_Znth_Same by
          (rewrite Zlength_replace_Znth__forward_star_build_step, Hws; lia).
      rewrite Znth_replace_Znth_Diff; try lia.
      pose proof (Hheads (Znth i comment_targets 0) Hdst). lia.
    + destruct (Z.eq_dec e (2 * i)) as [-> | Heven].
      * assert (Hnxtval :
          Znth (2 * i)
            (replace_Znth (2 * i + 1)
              (Znth (Znth i comment_targets 0)
                (replace_Znth (Znth i comment_sources 0) (2 * i) hs_2) 0)
              (replace_Znth (2 * i) (Znth (Znth i comment_sources 0) hs_2 0) ns_2)) 0 =
          Znth (Znth i comment_sources 0) hs_2 0).
        { rewrite Znth_replace_Znth_Diff by
              (try rewrite Zlength_replace_Znth__forward_star_build_step;
               try rewrite Hns; lia).
          rewrite Znth_replace_Znth_Same; lia. }
        assert (Htoval :
          Znth (2 * i)
            (replace_Znth (2 * i + 1) (Znth i comment_sources 0)
              (replace_Znth (2 * i) (Znth i comment_targets 0) ts_2)) 0 =
          Znth i comment_targets 0).
        { rewrite Znth_replace_Znth_Diff by
              (try rewrite Zlength_replace_Znth__forward_star_build_step;
               try rewrite Hts; lia).
          rewrite Znth_replace_Znth_Same; lia. }
        assert (Hwtval :
          Znth (2 * i)
            (replace_Znth (2 * i + 1) (Znth i comment_kinds 0)
              (replace_Znth (2 * i) (Znth i comment_kinds 0) ws_2)) 0 =
          Znth i comment_kinds 0).
        { rewrite Znth_replace_Znth_Diff by
              (try rewrite Zlength_replace_Znth__forward_star_build_step;
               try rewrite Hws; lia).
          rewrite Znth_replace_Znth_Same; lia. }
        rewrite Hnxtval, Htoval, Hwtval.
        pose proof (Hheads (Znth i comment_sources 0) Hsrc).
        repeat split; try lia; assumption.
      * assert (0 <= e < 2 * i) by lia.
        specialize (Hedges e H).
        assert (Hnxtval :
          Znth e
            (replace_Znth (2 * i + 1)
              (Znth (Znth i comment_targets 0)
                (replace_Znth (Znth i comment_sources 0) (2 * i) hs_2) 0)
              (replace_Znth (2 * i) (Znth (Znth i comment_sources 0) hs_2 0) ns_2)) 0 =
          Znth e ns_2 0).
        { rewrite Znth_replace_Znth_Diff by
              (try rewrite Zlength_replace_Znth__forward_star_build_step;
               try rewrite Hns; lia).
          rewrite Znth_replace_Znth_Diff; lia. }
        assert (Htoval :
          Znth e
            (replace_Znth (2 * i + 1) (Znth i comment_sources 0)
              (replace_Znth (2 * i) (Znth i comment_targets 0) ts_2)) 0 =
          Znth e ts_2 0).
        { rewrite Znth_replace_Znth_Diff by
              (try rewrite Zlength_replace_Znth__forward_star_build_step;
               try rewrite Hts; lia).
          rewrite Znth_replace_Znth_Diff; lia. }
        assert (Hwtval :
          Znth e
            (replace_Znth (2 * i + 1) (Znth i comment_kinds 0)
              (replace_Znth (2 * i) (Znth i comment_kinds 0) ws_2)) 0 =
          Znth e ws_2 0).
        { rewrite Znth_replace_Znth_Diff by
              (try rewrite Zlength_replace_Znth__forward_star_build_step;
               try rewrite Hws; lia).
          rewrite Znth_replace_Znth_Diff; lia. }
        rewrite Hnxtval, Htoval, Hwtval.
        destruct Hedges as [Hnxt [Hto Hwt]].
        repeat split; try lia; assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ForwardStar in *.
  destruct PreH14 as [Hhs [Hns [Hts [Hws [Hki [Hkcomments [Hobs Hadjs]]]]]]].
  pose proof (PreH10 i ltac:(lia)) as Hi.
  assert (Hsrc : 1 <= Znth i comment_sources 0 <= n_pre) by tauto.
  assert (Hdst : 1 <= Znth i comment_targets 0 <= n_pre) by tauto.
  assert (Hneq : Znth i comment_sources 0 <> Znth i comment_targets 0) by tauto.
  assert (Hsrcmeta : Znth i comment_sources 0 =
      fst (fst (Znth i comments __default__Prod__Prod_Z_Z_Z))) by tauto.
  assert (Hdstmeta : Znth i comment_targets 0 =
      snd (fst (Znth i comments __default__Prod__Prod_Z_Z_Z))) by tauto.
  assert (Hwtmeta : Znth i comment_kinds 0 =
      snd (Znth i comments __default__Prod__Prod_Z_Z_Z)) by tauto.
  assert (Hcat : comment_at comments i = Znth i comments __default__Prod__Prod_Z_Z_Z).
  { unfold comment_at. apply Znth_indep. lia. }
  assert (Hdiv_even : (2 * i) / 2 = i).
  { rewrite Z.mul_comm, Z.div_mul; lia. }
  assert (Hdiv_odd : (2 * i + 1) / 2 = i).
  { replace (2 * i + 1) with (1 + i * 2) by ring.
    rewrite Z.div_add by lia. reflexivity. }
  assert (Heven_even : Z.even (2 * i) = true).
  { rewrite Z.even_mul. reflexivity. }
  assert (Heven_odd : Z.even (2 * i + 1) = false).
  { replace (2 * i + 1) with (1 + 2 * i) by ring.
    rewrite Z.even_add, Z.even_mul. reflexivity. }
  assert (Hsrc_even : edge_src comments (2 * i) = Znth i comment_sources 0).
  { unfold edge_src. rewrite Hdiv_even, Hcat, Heven_even.
    rewrite triple_src__forward_star_build_step.
    symmetry; exact Hsrcmeta. }
  assert (Hsrc_odd : edge_src comments (2 * i + 1) = Znth i comment_targets 0).
  { unfold edge_src. rewrite Hdiv_odd, Hcat, Heven_odd.
    rewrite triple_dst__forward_star_build_step.
    symmetry; exact Hdstmeta. }
  assert (Hdst_even : edge_dst comments (2 * i) = Znth i comment_targets 0).
  { unfold edge_dst. rewrite Hdiv_even, Hcat, Heven_even.
    rewrite triple_dst__forward_star_build_step.
    symmetry; exact Hdstmeta. }
  assert (Hdst_odd : edge_dst comments (2 * i + 1) = Znth i comment_sources 0).
  { unfold edge_dst. rewrite Hdiv_odd, Hcat, Heven_odd.
    rewrite triple_src__forward_star_build_step.
    symmetry; exact Hsrcmeta. }
  assert (Hwt_even : edge_wt comments (2 * i) = Znth i comment_kinds 0).
  { unfold edge_wt. rewrite Hdiv_even, Hcat.
    rewrite triple_wt__forward_star_build_step.
    symmetry; exact Hwtmeta. }
  assert (Hwt_odd : edge_wt comments (2 * i + 1) = Znth i comment_kinds 0).
  { unfold edge_wt. rewrite Hdiv_odd, Hcat.
    rewrite triple_wt__forward_star_build_step.
    symmetry; exact Hwtmeta. }
  set (hs' := replace_Znth (Znth i comment_targets 0) (2 * i + 1)
      (replace_Znth (Znth i comment_sources 0) (2 * i) hs_2)).
  set (ns' := replace_Znth (2 * i + 1)
      (Znth (Znth i comment_targets 0)
        (replace_Znth (Znth i comment_sources 0) (2 * i) hs_2) 0)
      (replace_Znth (2 * i) (Znth (Znth i comment_sources 0) hs_2 0) ns_2)).
  set (ts' := replace_Znth (2 * i + 1) (Znth i comment_sources 0)
      (replace_Znth (2 * i) (Znth i comment_targets 0) ts_2)).
  set (ws' := replace_Znth (2 * i + 1) (Znth i comment_kinds 0)
      (replace_Znth (2 * i) (Znth i comment_kinds 0) ws_2)).
  change (Zlength hs' = n_pre + 1 /\
    Zlength ns' = 2 * m_pre /\ Zlength ts' = 2 * m_pre /\ Zlength ws' = 2 * m_pre /\
    0 <= i + 1 <= m_pre /\ i + 1 <= Zlength comments /\
    (forall e, 0 <= e < 2 * (i + 1) -> Znth e ts' 0 = edge_dst comments e /\ Znth e ws' 0 = edge_wt comments e) /\
    (forall u, 1 <= u <= n_pre -> exists es, AdjChain ns' (Znth u hs' 0) es /\ NoDup es /\
      forall e, In e es <-> 0 <= e < 2 * (i + 1) /\ edge_src comments e = u)).
  repeat apply conj.
  - subst hs'. rewrite !Zlength_replace_Znth__forward_star_build_step. exact Hhs.
  - subst ns'. rewrite !Zlength_replace_Znth__forward_star_build_step. exact Hns.
  - subst ts'. rewrite !Zlength_replace_Znth__forward_star_build_step. exact Hts.
  - subst ws'. rewrite !Zlength_replace_Znth__forward_star_build_step. exact Hws.
  - lia.
  - lia.
  - lia.
  - intros edge He.
    destruct (Z.eq_dec edge (2 * i + 1)) as [-> | Heodd].
    + subst ts' ws'.
      rewrite !Znth_replace_Znth_Same; try rewrite Zlength_replace_Znth__forward_star_build_step; try lia.
    + destruct (Z.eq_dec edge (2 * i)) as [-> | Heven].
      * subst ts' ws'.
        assert (Htoval :
          Znth (2 * i)
            (replace_Znth (2 * i + 1) (Znth i comment_sources 0)
              (replace_Znth (2 * i) (Znth i comment_targets 0) ts_2)) 0 =
          Znth i comment_targets 0).
        { rewrite Znth_replace_Znth_Diff by
              (try rewrite Zlength_replace_Znth__forward_star_build_step;
               try rewrite Hts; lia).
          rewrite Znth_replace_Znth_Same; lia. }
        assert (Hwtval :
          Znth (2 * i)
            (replace_Znth (2 * i + 1) (Znth i comment_kinds 0)
              (replace_Znth (2 * i) (Znth i comment_kinds 0) ws_2)) 0 =
          Znth i comment_kinds 0).
        { rewrite Znth_replace_Znth_Diff by
              (try rewrite Zlength_replace_Znth__forward_star_build_step;
               try rewrite Hws; lia).
          rewrite Znth_replace_Znth_Same; lia. }
        rewrite Htoval, Hwtval, Hdst_even, Hwt_even. tauto.
      * assert (0 <= edge < 2 * i) by lia.
        specialize (Hobs edge H).
        subst ts' ws'.
        assert (Htoval :
          Znth edge
            (replace_Znth (2 * i + 1) (Znth i comment_sources 0)
              (replace_Znth (2 * i) (Znth i comment_targets 0) ts_2)) 0 =
          Znth edge ts_2 0).
        { rewrite Znth_replace_Znth_Diff by
              (try rewrite Zlength_replace_Znth__forward_star_build_step;
               try rewrite Hts; lia).
          rewrite Znth_replace_Znth_Diff; lia. }
        assert (Hwtval :
          Znth edge
            (replace_Znth (2 * i + 1) (Znth i comment_kinds 0)
              (replace_Znth (2 * i) (Znth i comment_kinds 0) ws_2)) 0 =
          Znth edge ws_2 0).
        { rewrite Znth_replace_Znth_Diff by
              (try rewrite Zlength_replace_Znth__forward_star_build_step;
               try rewrite Hws; lia).
          rewrite Znth_replace_Znth_Diff; lia. }
        rewrite Htoval, Hwtval. exact Hobs.
  - intros u Hu.
    specialize (Hadjs u Hu).
    destruct Hadjs as [es [Hchain [Hnodup Hmem]]].
    assert (Hchain' : AdjChain ns' (Znth u hs_2 0) es).
    { eapply AdjChain_ext__forward_star_build_step; [exact Hchain|].
      intros x Hx. apply Hmem in Hx. destruct Hx as [Hx _].
      subst ns'.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Zlength_replace_Znth__forward_star_build_step; try rewrite Hns; lia).
      rewrite Znth_replace_Znth_Diff; lia. }
    assert (Hheadsrc : Znth (Znth i comment_sources 0) hs' 0 = 2 * i).
    { subst hs'.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Zlength_replace_Znth__forward_star_build_step; try rewrite Hhs; lia).
      rewrite Znth_replace_Znth_Same; lia. }
    assert (Hheaddst : Znth (Znth i comment_targets 0) hs' 0 = 2 * i + 1).
    { subst hs'. rewrite Znth_replace_Znth_Same.
      - reflexivity.
      - rewrite Zlength_replace_Znth__forward_star_build_step, Hhs. lia. }
    assert (Hnexteven : Znth (2 * i) ns' 0 = Znth (Znth i comment_sources 0) hs_2 0).
    { subst ns'.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite Zlength_replace_Znth__forward_star_build_step; try rewrite Hns; lia).
      rewrite Znth_replace_Znth_Same; lia. }
    assert (Hnextodd : Znth (2 * i + 1) ns' 0 = Znth (Znth i comment_targets 0) hs_2 0).
    { subst ns'.
      rewrite Znth_replace_Znth_Same by
        (rewrite Zlength_replace_Znth__forward_star_build_step, Hns; lia).
      rewrite Znth_replace_Znth_Diff; try lia. }
    destruct (Z.eq_dec u (Znth i comment_sources 0)) as [-> | Husrc].
    + exists ((2 * i) :: es).
      repeat apply conj.
      * rewrite Hheadsrc. constructor; [lia|].
        rewrite Hnexteven. exact Hchain'.
      * constructor.
        -- intro Hin. apply Hmem in Hin. lia.
        -- exact Hnodup.
      * intros edge.
        change ((2 * i = edge \/ In edge es) <->
          0 <= edge < 2 * (i + 1) /\ edge_src comments edge = Znth i comment_sources 0).
        split.
        -- intros [Hnew | Hold].
           ++ subst edge. apply conj.
              ** apply conj; lia.
              ** exact Hsrc_even.
           ++ apply Hmem in Hold. destruct Hold as [Hb Hs]. split; [lia|exact Hs].
        -- intros [Hb Hs].
           destruct (Z.eq_dec edge (2 * i)) as [-> | Hneweven].
           ++ left; reflexivity.
           ++ destruct (Z.eq_dec edge (2 * i + 1)) as [-> | Hnewodd].
              ** rewrite Hsrc_odd in Hs. exfalso. apply Hneq. symmetry; exact Hs.
              ** right. apply Hmem. split; [lia|exact Hs].
    + destruct (Z.eq_dec u (Znth i comment_targets 0)) as [-> | Hudst].
      * exists ((2 * i + 1) :: es).
        repeat apply conj.
        -- rewrite Hheaddst. constructor; [lia|].
           rewrite Hnextodd. exact Hchain'.
        -- constructor.
           ++ intro Hin. apply Hmem in Hin. lia.
           ++ exact Hnodup.
        -- intros edge.
           change ((2 * i + 1 = edge \/ In edge es) <->
             0 <= edge < 2 * (i + 1) /\ edge_src comments edge = Znth i comment_targets 0).
           split.
           ++ intros [Hnew | Hold].
              ** subst edge. split; [lia|exact Hsrc_odd].
              ** apply Hmem in Hold. destruct Hold as [Hb Hs]. split; [lia|exact Hs].
           ++ intros [Hb Hs].
              destruct (Z.eq_dec edge (2 * i + 1)) as [-> | Hnewodd].
              ** left; reflexivity.
              ** destruct (Z.eq_dec edge (2 * i)) as [-> | Hneweven].
                 --- rewrite Hsrc_even in Hs. exfalso. apply Hneq. exact Hs.
                 --- right. apply Hmem. split; [lia|exact Hs].
      * exists es.
        repeat apply conj.
        -- subst hs'.
           rewrite Znth_replace_Znth_Diff by
             (try rewrite Zlength_replace_Znth__forward_star_build_step; try rewrite Hhs; lia).
           rewrite Znth_replace_Znth_Diff; try lia. exact Hchain'.
        -- exact Hnodup.
        -- intros edge. split.
           ++ intro Hold. apply Hmem in Hold. destruct Hold as [Hb Hs]. split; [lia|exact Hs].
           ++ intros [Hb Hs].
              destruct (Z.eq_dec edge (2 * i + 1)) as [-> | Hnewodd].
              ** rewrite Hsrc_odd in Hs. exfalso. apply Hudst. symmetry; exact Hs.
              ** destruct (Z.eq_dec edge (2 * i)) as [-> | Hneweven].
                 --- rewrite Hsrc_even in Hs. exfalso. apply Husrc. symmetry; exact Hs.
                 --- apply Hmem. split; [lia|exact Hs].
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
  unfold ColoursInitialised.
  intros v Hv.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = m_pre) by lia.
  subst i.
  exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_3 : solver_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = m_pre) by lia.
  subst i.
  exact PreH14.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_4 : solver_entail_wit_5_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH10 q H).
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ColoursInitialised in *.
  intros x Hx.
  destruct (Z.eq_dec x v) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same; lia.
  - rewrite Znth_replace_Znth_Diff; try lia.
    apply PreH17.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_6_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_2 : solver_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply max_imposters_on_empty__outer_loop_entry.
  - lia.
  - exact PreH15.
  - intros v Hv.
    apply PreH17; lia.
  - intros i Hi.
    assert (HiM : 0 <= i < m_pre) by lia.
    specialize (PreH10 i HiM).
    unfold comment_at.
    assert (Hindep :
      Znth i comments (0, 0, 0) =
      Znth i comments __default__Prod__Prod_Z_Z_Z).
    {
      apply Znth_indep.
      lia.
    }
    rewrite Hindep.
    destruct (Znth i comments __default__Prod__Prod_Z_Z_Z)
      as [[u v] w].
    simpl in *.
    destruct PreH10 as [[[[[[Huv Htvn] _] _] Hsu] Htv] _].
    split.
    + rewrite <- Hsu; tauto.
    + rewrite <- Htv; tauto.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_3 : solver_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ColouredClosed.
  intros i Hi.
  assert (HiM : 0 <= i < m_pre) by lia.
  specialize (PreH10 i HiM).
  unfold comment_at.
  assert (Hindep :
    Znth i comments (0, 0, 0) =
    Znth i comments __default__Prod__Prod_Z_Z_Z).
  {
    apply Znth_indep.
    lia.
  }
  rewrite Hindep.
  destruct (Znth i comments __default__Prod__Prod_Z_Z_Z)
    as [[u v] w].
  simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  split; intros Hcol; exfalso; apply Hcol; apply PreH17; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_4 : solver_entail_wit_7_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ParityRespected.
  intros i Hi.
  assert (HiM : 0 <= i < m_pre) by lia.
  specialize (PreH10 i HiM).
  unfold comment_at.
  assert (Hindep :
    Znth i comments (0, 0, 0) =
    Znth i comments __default__Prod__Prod_Z_Z_Z).
  {
    apply Znth_indep.
    lia.
  }
  rewrite Hindep.
  destruct (Znth i comments __default__Prod__Prod_Z_Z_Z)
    as [[u v] w].
  simpl in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  intros Hu _.
  rewrite (PreH17 u ltac:(lia)) in Hu.
  contradiction.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_5 : solver_entail_wit_7_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ColourValues.
  split.
  - exact PreH15.
  - intros v Hv.
    left.
    apply PreH17; lia.
Qed.

Lemma proof_of_solver_entail_wit_7_split_goal_6 : solver_entail_wit_7_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_7_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (proj1 PreH18) as Hcslen.
  assert (Hbefore_s : Znth s cs_2 0 = -1).
  {
    pose proof ((proj2 PreH18) s ltac:(lia)) as Hvalue.
    destruct Hvalue as [Hminus | [Hzero | Hone]]; lia.
  }
  assert (Hstack_range : forall j, 0 <= j < 1 ->
    1 <= Znth j (replace_Znth 0 s ks_2) 0 <= n_pre).
  {
    intros j Hj.
    assert (j = 0) by lia; subst j.
    rewrite Znth_replace_Znth_Same; lia.
  }
  assert (Hksafter : Zlength (replace_Znth 0 s ks_2) = n_pre + 1).
  { rewrite Zlength_replace_Znth; exact PreH23. }
  assert (Hafter_nonminus :
    Znth s (replace_Znth s 0 cs_2) 0 <> -1).
  { rewrite Znth_replace_Znth_Same; lia. }
  assert (Hfrontier : ComponentFrontierStrong n_pre comments cs_2
    (replace_Znth s 0 cs_2) nil
    (sublist 0 1 (replace_Znth 0 s ks_2)) 0 0).
  {
    apply singleton_component_frontier_strong__outer_loop_entry;
      try assumption; lia.
  }
  Exists hs_2 ns_2 ts_2 ws_2 (@nil Z)
    (replace_Znth s 0 cs_2) cs_2 (replace_Znth 0 s ks_2).
  split_pure_spatial.
  - cancel (IntArray.full stack__pre (n_pre + 1) (replace_Znth 0 s ks_2)).
    cancel (IntArray.full color_pre (n_pre + 1) (replace_Znth s 0 cs_2)).
    cancel (IntArray.full comment_u_pre m_pre comment_sources).
    cancel (IntArray.full comment_v_pre m_pre comment_targets).
    cancel (IntArray.full comment_diff_pre m_pre comment_kinds).
    cancel (IntArray.full head_pre (n_pre + 1) hs_2).
    cancel (IntArray.full nxt_pre (2 * m_pre) ns_2).
    cancel (IntArray.full to_pre (2 * m_pre) ts_2).
    cancel (IntArray.full wt_pre (2 * m_pre) ws_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hu : 1 <= Znth (top - 1) ks 0 <= n_pre).
  { apply PreH20. lia. }
  pose proof
    (component_frontier_pop_to_scan__frontier_pop_to_scan
      n_pre comments before_2 cs_2 finished_2 ks c0 c1 0 top
      hs ns_2 ts_2 ws_2 m_pre)
    as Htransition.
  specialize (Htransition ltac:(lia) PreH22 ltac:(lia) PreH33 ltac:(lia) PreH1
    PreH30 PreH6 PreH31).
  destruct Htransition as [Hscan Hsum].
  simpl in Hscan.
  pose proof PreH32 as Hranges.
  destruct Hranges as [Hheads Hedges].
  specialize (Hheads _ Hu) as Hhead.
  assert (Hedge : Znth (Znth (top - 1) ks 0) hs 0 <> -1 ->
    ((1 <= Znth (Znth (Znth (top - 1) ks 0) hs 0) ts_2 0 <= n_pre /\
      (Znth (Znth (Znth (top - 1) ks 0) hs 0) ws_2 0 = 0 \/
       Znth (Znth (Znth (top - 1) ks 0) hs 0) ws_2 0 = 1)) /\
     -1 <= Znth (Znth (Znth (top - 1) ks 0) hs 0) ns_2 0) /\
    Znth (Znth (Znth (top - 1) ks 0) hs 0) ns_2 0 < 2 * m_pre).
  {
    intro Hne.
    specialize (Hedges (Znth (Znth (top - 1) ks 0) hs 0) ltac:(lia)).
    tauto.
  }
  assert (Hpending : forall j, 0 <= j < top - 1 ->
    1 <= Znth j ks 0 <= n_pre).
  { intros j Hj. apply PreH20. lia. }
  Left.
  Exists hs finished_2 before_2 ks ns_2 ws_2 ts_2 cs_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre (n_pre + 1) hs).
    cancel (IntArray.full color_pre (n_pre + 1) cs_2).
    cancel (IntArray.full stack__pre (n_pre + 1) ks).
    cancel (IntArray.full comment_u_pre m_pre comment_sources).
    cancel (IntArray.full comment_v_pre m_pre comment_targets).
    cancel (IntArray.full comment_diff_pre m_pre comment_kinds).
    cancel (IntArray.full nxt_pre (2 * m_pre) ns_2).
    cancel (IntArray.full to_pre (2 * m_pre) ts_2).
    cancel (IntArray.full wt_pre (2 * m_pre) ws_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try (assumption || lia || eauto).
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hu : 1 <= Znth (top - 1) ks 0 <= n_pre).
  { apply PreH20. lia. }
  assert (Hcolor1 : Znth (Znth (top - 1) ks 0) cs_2 0 = 1).
  {
    pose proof PreH30 as Hfront.
    unfold ComponentFrontierStrong, ComponentFrontier, NewColourSet in Hfront.
    destruct Hfront as
      [[Hvalues [Hnew [Hchoices [Hscanned [Hcount0 Hcount1]]]]] Hlocal].
    destruct Hvalues as [_ Hvalues].
    destruct Hnew as [Hnd [Hall [Hiff Hsame]]].
    assert (Htop' : 0 < top <= Zlength ks) by lia.
    pose proof (sublist_pop_permutation__frontier_pop_to_scan ks top Htop') as Hpop.
    assert (Hin : In (Znth (top - 1) ks 0) (sublist 0 top ks)).
    {
      eapply Permutation_in; [apply Permutation_sym; exact Hpop|].
      left. reflexivity.
    }
    assert (Hcoloured : Znth (Znth (top - 1) ks 0) cs_2 0 <> -1).
    {
      specialize (Hiff (Znth (top - 1) ks 0) Hu).
      apply Hiff. apply in_or_app. right. exact Hin.
    }
    specialize (Hvalues (Znth (top - 1) ks 0) Hu).
    destruct Hvalues as [Hm1 | [Hz | Ho]]; congruence.
  }
  pose proof
    (component_frontier_pop_to_scan__frontier_pop_to_scan
      n_pre comments before_2 cs_2 finished_2 ks c0 c1 1 top
      hs ns_2 ts_2 ws_2 m_pre)
    as Htransition.
  specialize (Htransition ltac:(lia) PreH22 ltac:(lia) PreH33 ltac:(lia) Hcolor1
    PreH30 PreH6 PreH31).
  destruct Htransition as [Hscan Hsum].
  simpl in Hscan.
  pose proof PreH32 as Hranges.
  destruct Hranges as [Hheads Hedges].
  specialize (Hheads _ Hu) as Hhead.
  assert (Hedge : Znth (Znth (top - 1) ks 0) hs 0 <> -1 ->
    ((1 <= Znth (Znth (Znth (top - 1) ks 0) hs 0) ts_2 0 <= n_pre /\
      (Znth (Znth (Znth (top - 1) ks 0) hs 0) ws_2 0 = 0 \/
       Znth (Znth (Znth (top - 1) ks 0) hs 0) ws_2 0 = 1)) /\
     -1 <= Znth (Znth (Znth (top - 1) ks 0) hs 0) ns_2 0) /\
    Znth (Znth (Znth (top - 1) ks 0) hs 0) ns_2 0 < 2 * m_pre).
  {
    intro Hne.
    specialize (Hedges (Znth (Znth (top - 1) ks 0) hs 0) ltac:(lia)).
    tauto.
  }
  assert (Hpending : forall j, 0 <= j < top - 1 ->
    1 <= Znth j ks 0 <= n_pre).
  { intros j Hj. apply PreH20. lia. }
  Right.
  Exists hs finished_2 before_2 ks ns_2 ws_2 ts_2 cs_2.
  split_pure_spatial.
  - cancel (IntArray.full head_pre (n_pre + 1) hs).
    cancel (IntArray.full color_pre (n_pre + 1) cs_2).
    cancel (IntArray.full stack__pre (n_pre + 1) ks).
    cancel (IntArray.full comment_u_pre m_pre comment_sources).
    cancel (IntArray.full comment_v_pre m_pre comment_targets).
    cancel (IntArray.full comment_diff_pre m_pre comment_kinds).
    cancel (IntArray.full nxt_pre (2 * m_pre) ns_2).
    cancel (IntArray.full to_pre (2 * m_pre) ts_2).
    cancel (IntArray.full wt_pre (2 * m_pre) ws_2).
  - split_pures.
    all: dump_pre_spatial.
    all: try (assumption || lia || eauto).
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH27 PreH3) as Hranges.
  destruct Hranges as [Hranges Hnxthi].
  destruct Hranges as [Hranges Hnxtlo].
  destruct Hranges as [Hdstbounds Hwt].
  destruct Hdstbounds as [Hdstlo Hdsthi].
  eapply (scan_conflict_spec__scan_conflict n_pre m_pre comments hs_2 ns_2
    ts ws before cs finished (sublist 0 top ks_2) u e c0 c1);
    eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_2 : solver_entail_wit_10_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH27 PreH3) as Hranges.
  destruct Hranges as [Hranges Hnxthi].
  destruct Hranges as [Hranges Hnxtlo].
  destruct Hranges as [Hdstbounds Hwt].
  destruct Hdstbounds as [Hdstlo Hdsthi].
  destruct Hwt as [-> | ->]; cbn; lia.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_3 : solver_entail_wit_10_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH27 PreH3) as Hranges.
  destruct Hranges as [Hranges Hnxthi].
  destruct Hranges as [Hranges Hnxtlo].
  destruct Hranges as [Hdstbounds Hwt].
  destruct Hdstbounds as [Hdstlo Hdsthi].
  destruct Hwt as [-> | ->]; cbn; lia.
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH27 PreH3) as Hranges.
  destruct Hranges as [Hranges Hnxthi].
  destruct Hranges as [Hranges Hnxtlo].
  destruct Hranges as [Hdstbounds Hwt].
  destruct Hdstbounds as [Hdstlo Hdsthi].
  eapply (scan_conflict_spec__scan_conflict n_pre m_pre comments hs_2 ns_2
    ts ws before cs finished (sublist 0 top ks_2) u e c0 c1);
    eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_2 : solver_entail_wit_10_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH27 PreH3) as Hranges.
  destruct Hranges as [Hranges Hnxthi].
  destruct Hranges as [Hranges Hnxtlo].
  destruct Hranges as [Hdstbounds Hwt].
  destruct Hdstbounds as [Hdstlo Hdsthi].
  destruct Hwt as [-> | ->]; cbn; lia.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_3 : solver_entail_wit_10_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH27 PreH3) as Hranges.
  destruct Hranges as [Hranges Hnxthi].
  destruct Hranges as [Hranges Hnxtlo].
  destruct Hranges as [Hdstbounds Hwt].
  destruct Hdstbounds as [Hdstlo Hdsthi].
  destruct Hwt as [-> | ->]; cbn; lia.
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_10_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_10_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_10_2_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists hs_2 finished_2 before_2
    (replace_Znth top (Znth e ts_2 0) ks_2)
    ns_2 ws_2 ts_2
    (replace_Znth (Znth e ts_2 0)
      (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2).
  split_pure_spatial.
  - cancel (IntArray.full comment_u_pre m_pre comment_sources).
    cancel (IntArray.full comment_v_pre m_pre comment_targets).
    cancel (IntArray.full comment_diff_pre m_pre comment_kinds).
    cancel (IntArray.full head_pre (n_pre + 1) hs_2).
    cancel (IntArray.full nxt_pre (2 * m_pre) ns_2).
    cancel (IntArray.full to_pre (2 * m_pre) ts_2).
    cancel (IntArray.full wt_pre (2 * m_pre) ws_2).
    cancel (IntArray.full color_pre (n_pre + 1)
      (replace_Znth (Znth e ts_2 0)
        (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2)).
    cancel (IntArray.full stack__pre (n_pre + 1)
      (replace_Znth top (Znth e ts_2 0) ks_2)).
  - split_pures.
  all: try (dump_pre_spatial; assumption).
  all: try (dump_pre_spatial; lia).
  + dump_pre_spatial.
    assert (Hcslen : Zlength cs_2 = n_pre + 1).
    { unfold ComponentScanStrong, ComponentScan, ColourValues in PreH38.
      tauto. }
    specialize (PreH26 PreH2).
    destruct PreH26 as [[[Hvrange Hwrange] Hnlo] Hnhi].
    assert (Hune : u <> Znth e ts_2 0).
    { intro Heq. rewrite <- Heq in PreH1. lia. }
    rewrite Znth_replace_Znth_Diff by lia. exact PreH18.
  + dump_pre_spatial.
    intros Hnext.
    unfold ForwardStarRanges in PreH40.
    destruct PreH40 as [_ Hranges].
    assert (Hnrange : 0 <= Znth e ns_2 0 < 2 * m_pre).
    { specialize (PreH26 PreH2). lia. }
    destruct (Hranges (Znth e ns_2 0) Hnrange)
      as [[Hnslo Hnshi] [Hts Hws]].
    exact (conj (conj (conj Hts Hws) Hnslo) Hnshi).
  + dump_pre_spatial.
    intros Hnext.
    pose proof (PreH27 (conj PreH2 PreH1)) as Htoplt.
    assert (Hpost : ComponentScanStrong n_pre comments ns_2 before_2
      (replace_Znth (Znth e ts_2 0)
        (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2)
      finished_2
      (sublist 0 (top + 1) (replace_Znth top (Znth e ts_2 0) ks_2))
      u (Znth e ns_2 0) c0 c1).
    { eapply component_scan_advance_new_stack__scan_edge_transitions;
        try eassumption; lia. }
    eapply component_scan_pending_top_lt__scan_edge_transitions
      with (ks := replace_Znth top (Znth e ts_2 0) ks_2).
    * lia.
    * lia.
    * lia.
    * rewrite Zlength_replace_Znth; exact PreH30.
    * exact Hpost.
  + dump_pre_spatial.
    intros j Hj.
    pose proof (PreH27 (conj PreH2 PreH1)) as Htoplt.
    specialize (PreH26 PreH2).
    destruct PreH26 as [[[Hvrange Hwrange] Hnlo] Hnhi].
    destruct (Z.eq_dec j top) as [->|Hne].
    * rewrite Znth_replace_Znth_Same by lia.
      exact Hvrange.
    * rewrite Znth_replace_Znth_Diff by lia.
      apply PreH28. lia.
  + dump_pre_spatial.
    pose proof (PreH27 (conj PreH2 PreH1)) as Htoplt.
    rewrite Zlength_replace_Znth; lia.
  + dump_pre_spatial.
    assert (Hcslen : Zlength cs_2 = n_pre + 1).
    { unfold ComponentScanStrong, ComponentScan, ColourValues in PreH38.
      tauto. }
    specialize (PreH26 PreH2).
    destruct PreH26 as [[[Hvrange Hwrange] Hnlo] Hnhi].
    destruct (Z.eq_dec s (Znth e ts_2 0)) as [Heq|Hne].
    * subst s. rewrite Znth_replace_Znth_Same by lia.
      destruct Hwrange as [Hw|Hw]; rewrite PreH18, Hw; vm_compute; lia.
    * rewrite Znth_replace_Znth_Diff by lia. exact PreH37.
  + dump_pre_spatial.
    pose proof (PreH27 (conj PreH2 PreH1)) as Htoplt.
    eapply component_scan_advance_new_stack__scan_edge_transitions;
      try eassumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  Exists hs_2 finished_2 before_2
    (replace_Znth top (Znth e ts_2 0) ks_2)
    ns_2 ws_2 ts_2
    (replace_Znth (Znth e ts_2 0)
      (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2).
  split_pure_spatial.
  - cancel (IntArray.full comment_u_pre m_pre comment_sources).
    cancel (IntArray.full comment_v_pre m_pre comment_targets).
    cancel (IntArray.full comment_diff_pre m_pre comment_kinds).
    cancel (IntArray.full head_pre (n_pre + 1) hs_2).
    cancel (IntArray.full nxt_pre (2 * m_pre) ns_2).
    cancel (IntArray.full to_pre (2 * m_pre) ts_2).
    cancel (IntArray.full wt_pre (2 * m_pre) ws_2).
    cancel (IntArray.full color_pre (n_pre + 1)
      (replace_Znth (Znth e ts_2 0)
        (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2)).
    cancel (IntArray.full stack__pre (n_pre + 1)
      (replace_Znth top (Znth e ts_2 0) ks_2)).
  - split_pures.
  all: try (dump_pre_spatial; assumption).
  all: try (dump_pre_spatial; lia).
  + dump_pre_spatial.
    assert (Hcslen : Zlength cs_2 = n_pre + 1).
    { unfold ComponentScanStrong, ComponentScan, ColourValues in PreH38.
      tauto. }
    specialize (PreH26 PreH2).
    destruct PreH26 as [[[Hvrange Hwrange] Hnlo] Hnhi].
    assert (Hune : u <> Znth e ts_2 0).
    { intro Heq. rewrite <- Heq in PreH1. lia. }
    rewrite Znth_replace_Znth_Diff by lia. exact PreH18.
  + dump_pre_spatial.
    intros Hnext.
    unfold ForwardStarRanges in PreH40.
    destruct PreH40 as [_ Hranges].
    assert (Hnrange : 0 <= Znth e ns_2 0 < 2 * m_pre).
    { specialize (PreH26 PreH2). lia. }
    destruct (Hranges (Znth e ns_2 0) Hnrange)
      as [[Hnslo Hnshi] [Hts Hws]].
    exact (conj (conj (conj Hts Hws) Hnslo) Hnshi).
  + dump_pre_spatial.
    intros Hnext.
    pose proof (PreH27 (conj PreH2 PreH1)) as Htoplt.
    assert (Hpost : ComponentScanStrong n_pre comments ns_2 before_2
      (replace_Znth (Znth e ts_2 0)
        (Z.lxor (Znth u cs_2 0) (Znth e ws_2 0)) cs_2)
      finished_2
      (sublist 0 (top + 1) (replace_Znth top (Znth e ts_2 0) ks_2))
      u (Znth e ns_2 0) c0 c1).
    { eapply component_scan_advance_new_stack__scan_edge_transitions;
        try eassumption; lia. }
    eapply component_scan_pending_top_lt__scan_edge_transitions
      with (ks := replace_Znth top (Znth e ts_2 0) ks_2).
    * lia.
    * lia.
    * lia.
    * rewrite Zlength_replace_Znth; exact PreH30.
    * exact Hpost.
  + dump_pre_spatial.
    intros j Hj.
    pose proof (PreH27 (conj PreH2 PreH1)) as Htoplt.
    specialize (PreH26 PreH2).
    destruct PreH26 as [[[Hvrange Hwrange] Hnlo] Hnhi].
    destruct (Z.eq_dec j top) as [->|Hne].
    * rewrite Znth_replace_Znth_Same by lia.
      exact Hvrange.
    * rewrite Znth_replace_Znth_Diff by lia.
      apply PreH28. lia.
  + dump_pre_spatial.
    pose proof (PreH27 (conj PreH2 PreH1)) as Htoplt.
    rewrite Zlength_replace_Znth; lia.
  + dump_pre_spatial.
    assert (Hcslen : Zlength cs_2 = n_pre + 1).
    { unfold ComponentScanStrong, ComponentScan, ColourValues in PreH38.
      tauto. }
    specialize (PreH26 PreH2).
    destruct PreH26 as [[[Hvrange Hwrange] Hnlo] Hnhi].
    destruct (Z.eq_dec s (Znth e ts_2 0)) as [Heq|Hne].
    * subst s. rewrite Znth_replace_Znth_Same by lia.
      destruct Hwrange as [Hw|Hw]; rewrite PreH18, Hw; vm_compute; lia.
    * rewrite Znth_replace_Znth_Diff by lia. exact PreH37.
  + dump_pre_spatial.
    pose proof (PreH27 (conj PreH2 PreH1)) as Htoplt.
    eapply component_scan_advance_new_stack__scan_edge_transitions;
      try eassumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_11_3 : solver_entail_wit_11_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists hs_2 finished_2 before_2 ks_2 ns_2 ws_2 ts_2 cs_2.
  split_pure_spatial.
  - cancel (IntArray.full comment_u_pre m_pre comment_sources).
    cancel (IntArray.full comment_v_pre m_pre comment_targets).
    cancel (IntArray.full comment_diff_pre m_pre comment_kinds).
    cancel (IntArray.full head_pre (n_pre + 1) hs_2).
    cancel (IntArray.full nxt_pre (2 * m_pre) ns_2).
    cancel (IntArray.full to_pre (2 * m_pre) ts_2).
    cancel (IntArray.full wt_pre (2 * m_pre) ws_2).
    cancel (IntArray.full color_pre (n_pre + 1) cs_2).
    cancel (IntArray.full stack__pre (n_pre + 1) ks_2).
  - split_pures.
  all: try (dump_pre_spatial; assumption).
  all: try (dump_pre_spatial; lia).
  + dump_pre_spatial.
    intros Hnext.
    unfold ForwardStarRanges in PreH41.
    destruct PreH41 as [_ Hranges].
    assert (Hnrange : 0 <= Znth e ns_2 0 < 2 * m_pre).
    { specialize (PreH27 PreH3). lia. }
    destruct (Hranges (Znth e ns_2 0) Hnrange)
      as [[Hnslo Hnshi] [Hts Hws]].
    exact (conj (conj (conj Hts Hws) Hnslo) Hnshi).
  + dump_pre_spatial.
    intros _.
    eapply component_scan_pending_top_lt__scan_edge_transitions;
      try eassumption; lia.
  + dump_pre_spatial.
    pose proof PreH40 as Hfs.
    unfold ForwardStar in Hfs.
    destruct Hfs as [_ [_ [_ [_ [_ [_ [Hedges _]]]]]]].
    specialize (Hedges e).
    assert (0 <= e < 2 * m_pre) by lia.
    specialize (Hedges H).
    destruct Hedges as [Hdst Hwt].
    eapply component_scan_advance_existing__scan_edge_transitions;
      try eassumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_11_4 : solver_entail_wit_11_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  Exists hs_2 finished_2 before_2 ks_2 ns_2 ws_2 ts_2 cs_2.
  split_pure_spatial.
  - cancel (IntArray.full comment_u_pre m_pre comment_sources).
    cancel (IntArray.full comment_v_pre m_pre comment_targets).
    cancel (IntArray.full comment_diff_pre m_pre comment_kinds).
    cancel (IntArray.full head_pre (n_pre + 1) hs_2).
    cancel (IntArray.full nxt_pre (2 * m_pre) ns_2).
    cancel (IntArray.full to_pre (2 * m_pre) ts_2).
    cancel (IntArray.full wt_pre (2 * m_pre) ws_2).
    cancel (IntArray.full color_pre (n_pre + 1) cs_2).
    cancel (IntArray.full stack__pre (n_pre + 1) ks_2).
  - split_pures.
  all: try (dump_pre_spatial; assumption).
  all: try (dump_pre_spatial; lia).
  + dump_pre_spatial.
    intros Hnext.
    unfold ForwardStarRanges in PreH41.
    destruct PreH41 as [_ Hranges].
    assert (Hnrange : 0 <= Znth e ns_2 0 < 2 * m_pre).
    { specialize (PreH27 PreH3). lia. }
    destruct (Hranges (Znth e ns_2 0) Hnrange)
      as [[Hnslo Hnshi] [Hts Hws]].
    exact (conj (conj (conj Hts Hws) Hnslo) Hnshi).
  + dump_pre_spatial.
    intros _.
    eapply component_scan_pending_top_lt__scan_edge_transitions;
      try eassumption; lia.
  + dump_pre_spatial.
    pose proof PreH40 as Hfs.
    unfold ForwardStar in Hfs.
    destruct Hfs as [_ [_ [_ [_ [_ [_ [Hedges _]]]]]]].
    specialize (Hedges e).
    assert (0 <= e < 2 * m_pre) by lia.
    specialize (Hedges H).
    destruct Hedges as [Hdst Hwt].
    eapply component_scan_advance_existing__scan_edge_transitions;
      try eassumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst e.
  Exists hs_2 ns_2 ts_2 ws_2 (finished_2 ++ u :: nil) cs_2 before_2 ks_2.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    exact (component_scan_done__scan_and_component_closure
      n_pre comments ns_2 before_2 cs_2 finished_2
      (sublist 0 top ks_2) u c0 c1 PreH37).
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst e.
  Exists hs_2 ns_2 ts_2 ws_2 (finished_2 ++ u :: nil) cs_2 before_2 ks_2.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    exact (component_scan_done__scan_and_component_closure
      n_pre comments ns_2 before_2 cs_2 finished_2
      (sublist 0 top ks_2) u c0 c1 PreH37).
Qed.

Lemma proof_of_solver_entail_wit_13 : solver_entail_wit_13.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst top.
  Exists hs_2 ns_2 ts_2 ws_2 finished cs_2 ks_2 before_2.
  split_pure_spatial.
  - repeat progress cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    rewrite Zsublist_nil in PreH29.
    exact (component_frontier_complete__scan_and_component_closure
      n_pre m_pre comments hs_2 ns_2 ts_2 ws_2 before_2 cs_2 finished
      c0 c1 PreH5 PreH30 PreH31 PreH23 PreH24 PreH29).
  all: lia.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_1 : solver_entail_wit_14_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete,
    ComponentFrontier, NewColourSet in PreH28.
  destruct PreH28 as [Hcomplete _].
  destruct Hcomplete as [Hfront _].
  destruct Hfront as [_ [Hnew _]].
  destruct Hnew as [_ [_ [Hmembership Hpreserve]]].
  rewrite app_nil_r in Hmembership, Hpreserve.
  match goal with
  | Hrange : 1 <= v /\ v < s + 1 |- _ => destruct Hrange as [Hvlow Hvhigh]
  end.
  assert (v < s \/ v = s) as [Hvlt | ->] by lia.
  - specialize (PreH25 v ltac:(lia)).
    assert (~ In v vertices) as Hnotin.
    {
      intro Hin.
      specialize (proj1 (Hmembership v ltac:(lia)) Hin) as [Hbefore _].
      contradiction.
    }
    rewrite (Hpreserve v ltac:(lia) Hnotin).
    exact PreH25.
  - exact PreH27.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_2 : solver_entail_wit_14_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete in PreH28.
  destruct PreH28 as [Hcomplete _].
  destruct Hcomplete as [_ [_ [_ Hlift]]].
  specialize (Hlift total PreH24).
  rewrite Z.max_l in Hlift by lia.
  exact Hlift.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_3 : solver_entail_wit_14_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete in PreH28.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_4 : solver_entail_wit_14_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete in PreH28.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_5 : solver_entail_wit_14_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete, ComponentFrontier in PreH28.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_6 : solver_entail_wit_14_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete in PreH28.
  destruct PreH28 as [Hcomplete _].
  destruct Hcomplete as [_ [_ [_ Hlift]]].
  specialize (Hlift total PreH24).
  rewrite Z.max_l in Hlift by lia.
  eapply MaxImpostersOn_upper_bound__outer_loop_component_commit.
  exact Hlift.
Qed.

Lemma proof_of_solver_entail_wit_14_1_split_goal_7 : solver_entail_wit_14_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_14_1_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_1 : solver_entail_wit_14_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete,
    ComponentFrontier, NewColourSet in PreH28.
  destruct PreH28 as [Hcomplete _].
  destruct Hcomplete as [Hfront _].
  destruct Hfront as [_ [Hnew _]].
  destruct Hnew as [_ [_ [Hmembership Hpreserve]]].
  rewrite app_nil_r in Hmembership, Hpreserve.
  match goal with
  | Hrange : 1 <= v /\ v < s + 1 |- _ => destruct Hrange as [Hvlow Hvhigh]
  end.
  assert (v < s \/ v = s) as [Hvlt | ->] by lia.
  - specialize (PreH25 v ltac:(lia)).
    assert (~ In v vertices) as Hnotin.
    {
      intro Hin.
      specialize (proj1 (Hmembership v ltac:(lia)) Hin) as [Hbefore _].
      contradiction.
    }
    rewrite (Hpreserve v ltac:(lia) Hnotin).
    exact PreH25.
  - exact PreH27.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_2 : solver_entail_wit_14_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete in PreH28.
  destruct PreH28 as [Hcomplete _].
  destruct Hcomplete as [_ [_ [_ Hlift]]].
  specialize (Hlift total PreH24).
  rewrite Z.max_r in Hlift by lia.
  exact Hlift.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_3 : solver_entail_wit_14_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete in PreH28.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_4 : solver_entail_wit_14_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete in PreH28.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_5 : solver_entail_wit_14_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete, ComponentFrontier in PreH28.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_6 : solver_entail_wit_14_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold ComponentCompleteStrong, ComponentComplete in PreH28.
  destruct PreH28 as [Hcomplete _].
  destruct Hcomplete as [_ [_ [_ Hlift]]].
  specialize (Hlift total PreH24).
  rewrite Z.max_r in Hlift by lia.
  eapply MaxImpostersOn_upper_bound__outer_loop_component_commit.
  exact Hlift.
Qed.

Lemma proof_of_solver_entail_wit_14_2_split_goal_7 : solver_entail_wit_14_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH10.
  exact H.
Qed.

Lemma proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_14_2_split_goal_7.
Qed.

Lemma proof_of_solver_entail_wit_15_split_goal_1 : solver_entail_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (max_imposters_on_total_implies_spec__final_specification
    n_pre comments cs_2 total); try assumption.
  - intros v Hv. apply PreH21. lia.
  - intros i Hi.
    specialize (PreH10 i).
    assert (0 <= i < m_pre) as Him by lia.
    specialize (PreH10 Him).
    unfold comment_at.
    destruct (Znth i comments __default__Prod__Prod_Z_Z_Z) as [[u v] w] eqn:Hat.
    simpl in PreH10.
    destruct PreH10 as [[[[[[[[Hsu HsuN] Htv] HtvN] Hne] Hw] Hsrc] Hdst] Hkind].
    rewrite <- (Znth_indep comments i __default__Prod__Prod_Z_Z_Z (0, 0, 0) Hi).
    rewrite Hat. simpl.
    rewrite <- Hsrc, <- Hdst, <- Hkind.
    tauto.
Qed.

Lemma proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_15_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape comment_u_pre m_pre comment_sources).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape comment_v_pre m_pre comment_targets).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape comment_diff_pre m_pre comment_kinds).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape head_pre (n_pre + 1) hs).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape nxt_pre (2 * m_pre) ns).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape to_pre (2 * m_pre) ts).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape wt_pre (2 * m_pre) ws).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape color_pre (n_pre + 1) cs).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape stack__pre (n_pre + 1) ks).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_spatial : solver_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape comment_u_pre m_pre comment_sources).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape comment_v_pre m_pre comment_targets).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape comment_diff_pre m_pre comment_kinds).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape head_pre (n_pre + 1) hs).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape nxt_pre (2 * m_pre) ns).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape to_pre (2 * m_pre) ts).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape wt_pre (2 * m_pre) ws).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape color_pre (n_pre + 1) cs).
  sep_apply_l_atomic
    (IntArray.full_to_full_shape stack__pre (n_pre + 1) ks).
  cancel.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_spatial.
Qed.
