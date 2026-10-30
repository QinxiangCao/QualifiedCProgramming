From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_support_lib.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** ===== group: solver_lit_removable ===== *)
Lemma removable_reason_scan_advance_level0__lit_removable :
  forall n M l minl base done stack tags tagged C v p i,
    removable_reason_scan_inv n M l minl base done stack tags tagged C v p i ->
    1 <= i < Zlength C ->
    level_of (msolver_view n M)
      (literal_var (Znth i C (Pos 0))) = Some 0 ->
    removable_reason_scan_inv n M l minl base done stack tags tagged C v p (i + 1).
Proof.
  intros n M l minl base done stack tags tagged C v p i Hinv Hi Hlevel.
  unfold removable_reason_scan_inv in *.
  destruct Hinv as [Hdfs [Hfocus [Hrange [Hwf Hprev]]]].
  split; [exact Hdfs|].
  split; [exact Hfocus|].
  split; [lia|].
  split; [exact Hwf|].
  intros k Hk.
  destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
  - apply Hprev. lia.
  - assert (k = i) by lia. subst k. exact (or_introl Hlevel).
Qed.

Lemma removable_rollback_start__lit_removable :
  forall n top base entry_tags tags0 tagged l minl M stack done,
    top = Zlength base ->
    analysis_tags_exact n entry_tags base ->
    removable_dfs_loop_inv n M l minl base tags0 tagged stack done ->
    removable_rollback_inv n top top base entry_tags tags0 tagged tags0.
Proof.
  intros n top base entry_tags tags0 tagged l minl M stack done
    Htop Hentry Hdfs.
  unfold removable_dfs_loop_inv in Hdfs.
  destruct Hdfs as [fresh [Htagged [Hexact _]]].
  unfold removable_rollback_inv.
  subst top. subst tagged.
  split; [apply Zlength_nonneg|].
  split; [lia|].
  split.
  { rewrite Zlength_app. pose proof (Zlength_nonneg fresh). lia. }
  split; [reflexivity|].
  split; [apply sublist_app_exact1|].
  split; [exact Hentry|].
  split; [exact Hexact|].
  assert (Hsl : sublist (Zlength base) (Zlength base) (base ++ fresh) = (@nil Z)).
  { apply length_zero_iff_nil.
    rewrite (sublist_length (Zlength base) (Zlength base) (base ++ fresh)).
    - simpl. lia.
    - pose proof (Zlength_nonneg base). lia.
    - rewrite Zlength_app. pose proof (Zlength_nonneg fresh). lia. }
  rewrite Hsl. reflexivity.
Qed.

Lemma clear_indices_snoc__lit_removable :
  forall xs x tags,
    clear_indices (xs ++ x :: nil) tags =
    replace_Znth x 0 (clear_indices xs tags).
Proof.
  induction xs as [|a xs IH]; intros x tags; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma removable_rollback_step__lit_removable :
  forall n top j base entry_tags tags0 tagged tags,
    removable_rollback_inv n top j base entry_tags tags0 tagged tags ->
    j < Zlength tagged ->
    removable_rollback_inv n top (j + 1) base entry_tags tags0 tagged
      (replace_Znth (Znth j tagged 0) 0 tags).
Proof.
  intros n top j base entry_tags tags0 tagged tags Hinv Hj.
  unfold removable_rollback_inv in *.
  destruct Hinv as [Htop0 [Htopj [Hjlen [Htop [Hprefix [Hentry [Hexact Htags]]]]]]].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [exact Htop|].
  split; [exact Hprefix|].
  split; [exact Hentry|].
  split; [exact Hexact|].
  rewrite (sublist_split top (j + 1) j tagged) by lia.
  rewrite (sublist_single 0 j tagged) by lia.
  rewrite clear_indices_snoc__lit_removable.
  now rewrite <- Htags.
Qed.

Lemma removable_dfs_loop_inv_stack_perm__lit_removable :
  forall n M l minl base tags tagged stack stack' done,
    Permutation stack stack' ->
    removable_dfs_loop_inv n M l minl base tags tagged stack done ->
    removable_dfs_loop_inv n M l minl base tags tagged stack' done.
Proof.
  intros n M l minl base tags tagged stack stack' done Hperm Hinv.
  unfold removable_dfs_loop_inv in *.
  destruct Hinv as (fresh & Htagged & Hexact & Hfresh & Hnodup & Hpart & Hassigned & Hreason & Hinv).
  destruct Hinv as [Hdfs Hminl].
  exists fresh.
  split; [exact Htagged|].
  split; [exact Hexact|].
  split; [exact Hfresh|].
  split.
  - eapply Permutation_NoDup.
    + apply Permutation_app_head. exact Hperm.
    + exact Hnodup.
  - split.
    + eapply Permutation_trans.
      * apply Permutation_app_head. apply Permutation_sym. exact Hperm.
      * exact Hpart.
    + split; [exact Hassigned|].
      split.
      * intros x Hx. apply Hreason.
        eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hx].
      * split.
        -- intros x Hx.
           destruct (Hdfs x Hx) as [c [Hr Hc]].
           exists c. split; [exact Hr|].
           intros q Hq Hneq.
           specialize (Hc q Hq Hneq).
           destruct Hc as [H0 | [Hb | [Hd | Hs]]].
           ++ exact (or_introl H0).
           ++ exact (or_intror (or_introl Hb)).
           ++ exact (or_intror (or_intror (or_introl Hd))).
           ++ right. right. right.
              eapply Permutation_in; [exact Hperm | exact Hs].
        -- exact Hminl.
Qed.

Lemma analysis_cancel_ready_semantic_core__lit_removable :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    mtrail_wf n (ms_core M) /\
    stable_view (msolver_view n M) /\
    reasons_entailed F (msolver_view n M) /\
    db_wf n (msolver_db M) /\
    reason_head_ok M.
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (conj (asc_trail_wf _ _ _ Hctx)
    (conj (asc_stable _ _ _ Hctx) (conj (asc_reasons_ent _ _ _ Hctx)
      (conj (asc_db_wf _ _ _ Hctx) (asc_reason_head _ _ _ Hctx))))).
Qed.

Lemma removable_reason_scan_focus_tagged__lit_removable :
  forall n M l minl base done stack tags tagged C v p i,
    removable_reason_scan_inv n M l minl base done stack tags tagged C v p i ->
    In (lit_var_c l) base ->
    In v tagged.
Proof.
  intros n M l minl base done stack tags tagged C v p i Hscan Hbase.
  unfold removable_reason_scan_inv in Hscan.
  destruct Hscan as [Hdfs _].
  unfold removable_dfs_loop_inv in Hdfs.
  destruct Hdfs as [fresh
    [Htagged [Hexact [Hfresh [Hnodup [Hpart Hrest]]]]]].
  rewrite Htagged. apply in_or_app.
  assert (Hin : In v (lit_var_c l :: fresh)).
  { eapply Permutation_in; [exact Hpart|].
    apply in_or_app. right. left. reflexivity. }
  destruct Hin as [Heq | Hfreshv].
  - left. subst v. exact Hbase.
  - right. exact Hfreshv.
Qed.

Lemma removable_reason_scan_side_neq_untagged__lit_removable :
  forall n M l minl base done stack tags tagged C v p i,
    removable_reason_scan_inv n M l minl base done stack tags tagged C v p i ->
    In (lit_var_c l) base ->
    0 <= literal_var (Znth i C (Pos 0)) < n ->
    Znth (literal_var (Znth i C (Pos 0))) tags 0 = 0 ->
    literal_var (Znth i C (Pos 0)) <> v.
Proof.
  intros n M l minl base done stack tags tagged C v p i
    Hscan Hbase Hx Hzero Heq. subst v.
  pose proof (removable_reason_scan_focus_tagged__lit_removable
    n M l minl base done stack tags tagged C
    (literal_var (Znth i C (Pos 0))) p i Hscan Hbase) as Hin.
  unfold removable_reason_scan_inv in Hscan.
  destruct Hscan as [Hdfs _].
  unfold removable_dfs_loop_inv in Hdfs.
  destruct Hdfs as [fresh [_ [Hexact _]]].
  unfold analysis_tags_exact in Hexact.
  destruct Hexact as [_ [_ [_ [_ Hiff]]]].
  apply (proj2 (Hiff _ Hx)) in Hin. congruence.
Qed.

Lemma analysis_tags_exact_push__lit_removable :
  forall n tags tagged x,
    analysis_tags_exact n tags tagged ->
    0 <= x < n ->
    Znth x tags 0 = 0 ->
    analysis_tags_exact n (replace_Znth x 1 tags) (tagged ++ x :: nil).
Proof.
  intros n tags tagged x Hexact Hx Hzero.
  unfold analysis_tags_exact in *.
  destruct Hexact as [Hlen [Hnodup [Hbounds [Hcells Hiff]]]].
  assert (Hnotin : ~ In x tagged).
  { intro Hin. apply (proj2 (Hiff x Hx)) in Hin. congruence. }
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + apply NoDup_snoc; assumption.
    + split.
      * rewrite Forall_forall in *.
        intros y Hy. apply in_app_or in Hy.
        destruct Hy as [Hy | [<- | []]]; auto.
      * split.
        -- apply Forall_replace_Znth; [exact Hcells|].
           right. reflexivity.
        -- intros y Hy.
           destruct (Z.eq_dec y x) as [-> | Hne].
           ++ rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
              split; intro; [apply in_or_app; right; left; reflexivity|reflexivity].
           ++ rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
              rewrite Hiff by exact Hy.
              split; intro Hin.
              ** apply in_or_app. left. exact Hin.
              ** apply in_app_or in Hin. destruct Hin as [Hin | [Heq | []]].
                 --- exact Hin.
                 --- exfalso. apply Hne. symmetry. exact Heq.
Qed.

Lemma assigned_below_level_word_zero__lit_removable :
  forall n M x,
    mtrail_wf n (ms_core M) ->
    assigned_below_current (msolver_view n M) x ->
    Znth x (mt_levels (ms_core M)) 0 = 0 ->
    level_of (msolver_view n M) x = Some 0.
Proof.
  intros n M x Htrail
    [d [r [Hlevel [Hrank Hbelow]]]] Hword.
  assert (Hrank' : trail_pos (ms_core M) x = Some r).
  { exact Hrank. }
  pose proof (trail_pos_bound (ms_core M) x r Hrank') as Hbound.
  pose proof (trail_pos_var (ms_core M) x r Hrank') as Hvar.
  pose proof (mtw_levels_agree Htrail (Z.of_nat r)) as Hagree.
  specialize (Hagree ltac:(lia)).
  rewrite Hvar, Hword in Hagree.
  unfold msolver_view, view_of.
  cbn [level_of].
  rewrite Hrank'. simpl. f_equal.
  symmetry. exact Hagree.
Qed.

Lemma assigned_below_in_trail__lit_removable :
  forall n M x,
    assigned_below_current (msolver_view n M) x ->
    In x (map lit_var_c (mt_trail (ms_core M))).
Proof.
  intros n M x [_ [r [_ [Hrank _]]]].
  unfold msolver_view, view_of in Hrank.
  cbn [assignment_rank] in Hrank.
  pose proof (trail_pos_bound (ms_core M) x r Hrank) as Hbound.
  pose proof (trail_pos_var (ms_core M) x r Hrank) as Hvar.
  rewrite <- Hvar. unfold trail_var.
  apply in_map. apply Znth_In. lia.
Qed.

Lemma assignment_of_rank__lit_removable :
  forall n M x r,
    mtrail_wf n (ms_core M) ->
    assignment_rank (msolver_view n M) x = Some r ->
    exists b, assignment (msolver_view n M) x = Some b.
Proof.
  intros n M x r Hwf Hrank.
  destruct (assignment (msolver_view n M) x) as [b|] eqn:Hassignment.
  - now exists b.
  - exfalso.
    assert (Hnone : trail_pos (ms_core M) x = None).
    { apply (proj1 (view_unassigned_iff n (ms_core M) x Hwf)).
      exact Hassignment. }
    unfold msolver_view, view_of in Hrank.
    cbn [assignment_rank] in Hrank.
    congruence.
Qed.

Lemma removable_reason_scan_side_assigned_below__lit_removable :
  forall n F A_arr K M focus l minl base done stack tags tagged C v p i,
    analysis_cancel_ready n F A_arr K M focus ->
    removable_reason_scan_inv
      n M l minl base done stack tags tagged C v p i ->
    1 <= i < Zlength C ->
    literal_var (Znth i C (Pos 0)) <> v ->
    assigned_below_current (msolver_view n M)
      (literal_var (Znth i C (Pos 0))).
Proof.
  intros n F A_arr K M focus l minl base done stack tags tagged C v p i
    Hready Hscan Hi Hdifferent.
  destruct (analysis_cancel_ready_semantic_core__lit_removable
    n F A_arr K M focus Hready)
    as [Htrail [Hstable _]].
  unfold removable_reason_scan_inv in Hscan.
  destruct Hscan as [Hdfs [Hfocus _]].
  unfold removable_dfs_loop_inv in Hdfs.
  destruct Hdfs as [fresh
    [Htagged [Hexact [Hfresh [Hnodup [Hpart
      [Hassigned [Hreason [Hwitness Hminl]]]]]]]]].
  assert (Hvin : In v (lit_var_c l :: fresh)).
  { eapply Permutation_in; [exact Hpart|].
    apply in_or_app. right. left. reflexivity. }
  destruct (Hassigned v Hvin) as
    [dv [rv [Hvlevel [Hvrank Hvbelow]]]].
  destruct (assignment_of_rank__lit_removable
    n M v rv Htrail Hvrank) as [bv Hvassignment].
  destruct Hstable as [Hgrounded Hclosed].
  destruct (Hgrounded v bv Hvassignment) as
    [dv' [rv' [Hvlevel' [Hvrank' Hvreason]]]].
  assert (Hfocus_reason :
    reason_of (msolver_view n M) v = Some C).
  { unfold removable_reason_focus, reason_target_wf in Hfocus.
    destruct Hfocus as [_ [_ [_ [Hreason_mem _]]]].
    unfold msolver_view, view_of.
    cbn [reason_of].
    unfold msolver_view, view_of in Hvrank.
    cbn [assignment_rank] in Hvrank.
    rewrite Hvrank. exact Hreason_mem. }
  destruct Hvreason as [Hnone | [C' [Hreason' Hvalid]]].
  - congruence.
  - rewrite Hfocus_reason in Hreason'. inversion Hreason'. subst C'.
    unfold reason_valid in Hvalid.
    destruct Hvalid as
      [b [d [rx [Hb [Hd [Hrx [Hsat Hside]]]]]]].
    specialize (Hside (Znth i C (Pos 0))).
    assert (Hin : In (Znth i C (Pos 0)) C) by (apply Znth_In; lia).
    specialize (Hside Hin Hdifferent).
    destruct Hside as [_ [dy [ry [Hxlevel [Hxrank [Hdle Hranklt]]]]]].
    unfold assigned_below_current.
    exists dy, ry. split; [exact Hxlevel|].
    split; [exact Hxrank|].
    rewrite Hvlevel in Hd. inversion Hd. lia.
Qed.

Lemma removable_reason_scan_advance_classified__lit_removable :
  forall n M l minl base done stack tags tagged C v p i,
    removable_reason_scan_inv n M l minl base done stack tags tagged C v p i ->
    1 <= i < Zlength C ->
    (let x := literal_var (Znth i C (Pos 0)) in
     level_of (msolver_view n M) x = Some 0 \/
     In x base \/ In x done \/ In x stack) ->
    removable_reason_scan_inv n M l minl base done stack tags tagged C v p (i + 1).
Proof.
  intros n M l minl base done stack tags tagged C v p i Hscan Hi Hclass.
  unfold removable_reason_scan_inv in *.
  destruct Hscan as [Hdfs [Hfocus [Hrange [Hwf Hprev]]]].
  split; [exact Hdfs|].
  split; [exact Hfocus|].
  split; [lia|].
  split; [exact Hwf|].
  intros k Hk.
  destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
  - apply Hprev. lia.
  - assert (k = i) by lia. subst k. exact Hclass.
Qed.

Lemma removable_reason_scan_advance_seen__lit_removable :
  forall n M l minl base done stack tags tagged C v p i,
    removable_reason_scan_inv n M l minl base done stack tags tagged C v p i ->
    1 <= i < Zlength C ->
    literal_var (Znth i C (Pos 0)) <> v ->
    Znth (literal_var (Znth i C (Pos 0))) tags 0 <> 0 ->
    removable_reason_scan_inv n M l minl base done stack tags tagged C v p (i + 1).
Proof.
  intros n M l minl base done stack tags tagged C v p i
    Hscan Hi Hneq Hseen.
  assert (Hscan_copy := Hscan).
  unfold removable_reason_scan_inv in Hscan_copy.
  destruct Hscan_copy as [Hdfs _].
  unfold removable_dfs_loop_inv in Hdfs.
  destruct Hdfs as [fresh
    [Htagged [Hexact [Hfresh [Hnodup [Hpart Hrest]]]]]].
  unfold analysis_tags_exact in Hexact.
  destruct Hexact as [Hlen [Htagged_nodup [Hbounds [Hcells Hiff]]]].
  set (x := literal_var (Znth i C (Pos 0))) in *.
  assert (Hxrange : 0 <= x < n).
  { unfold removable_reason_scan_inv in Hscan.
    destruct Hscan as [_ [_ [_ [Hwf _]]]].
    unfold x, literal_wf, var_in_range.
    exact (Forall_Znth_elim _ _ _ (Pos 0) i Hwf ltac:(lia)). }
  assert (Hcell : Znth x tags 0 = 1).
  { assert (Hinrange : 0 <= x < Zlength tags) by lia.
    pose proof (Forall_Znth_elim _ _ _ 0 x Hcells Hinrange) as Hcell_domain.
    destruct Hcell_domain; [congruence|assumption]. }
  assert (Hintagged : In x tagged).
  { apply (proj1 (Hiff x Hxrange)). exact Hcell. }
  assert (Hclass : In x base \/ In x done \/ In x stack).
  { rewrite Htagged in Hintagged.
    apply in_app_or in Hintagged. destruct Hintagged as [Hb | Hfreshx].
    - left. exact Hb.
    - assert (Hpartition : In x (done ++ v :: stack)).
      { eapply Permutation_in; [apply Permutation_sym; exact Hpart|].
        right. exact Hfreshx. }
      apply in_app_or in Hpartition. destruct Hpartition as [Hd | [Heq | Hs]].
      + right. left. exact Hd.
      + exfalso. apply Hneq. symmetry. exact Heq.
      + right. right. exact Hs. }
  eapply removable_reason_scan_advance_classified__lit_removable;
    [exact Hscan | exact Hi |].
  exact (or_intror Hclass).
Qed.

Lemma removable_reason_scan_push_pending__lit_removable :
  forall n M l minl base done stack tags tagged C v p i x q Cx,
    removable_reason_scan_inv n M l minl base done stack tags tagged C v p i ->
    In (lit_var_c l) base ->
    1 <= i < Zlength C ->
    x = literal_var (Znth i C (Pos 0)) ->
    0 <= x < n ->
    Znth x tags 0 = 0 ->
    assigned_below_current (msolver_view n M) x ->
    reason_target_wf n M x q Cx ->
    removable_reason_scan_inv n M l minl base done (stack ++ x :: nil)
      (replace_Znth x 1 tags) (tagged ++ x :: nil) C v p (i + 1).
Proof.
  intros n M l minl base done stack tags tagged C v p i x q Cx
    Hscan Hbase Hi Hxdef Hx Hzero Hbelow Hreasonx.
  subst x.
  set (x := literal_var (Znth i C (Pos 0))) in *.
  unfold removable_reason_scan_inv in Hscan |- *.
  destruct Hscan as [Hdfs [Hfocus [Hrange [Hwf Hfrontier]]]].
  unfold removable_dfs_loop_inv in Hdfs |- *.
  destruct Hdfs as [fresh
    [Htagged [Hexact [Hfresh [Hnodup [Hpart
      [Hassigned [Hreason [Hwitness Hminl]]]]]]]]].
  assert (Hnot_tagged : ~ In x tagged).
  { unfold analysis_tags_exact in Hexact.
    destruct Hexact as [_ [_ [_ [_ Hiff]]]].
    intro Hin. apply (proj2 (Hiff x Hx)) in Hin. congruence. }
  assert (Hnot_fresh : ~ In x (lit_var_c l :: fresh)).
  { intro Hin. destruct Hin as [Heq | Hin].
    - apply Hnot_tagged. rewrite Htagged. apply in_or_app. left.
      rewrite <- Heq. exact Hbase.
    - apply Hnot_tagged. rewrite Htagged. apply in_or_app. right. exact Hin. }
  assert (Hnot_work : ~ In x (done ++ v :: stack)).
  { intro Hin. apply Hnot_fresh.
    eapply Permutation_in; [exact Hpart|exact Hin]. }
  refine (conj _ _); [|].
  - exists (fresh ++ x :: nil).
    split.
    + rewrite Htagged, app_assoc. reflexivity.
    + split.
      * apply analysis_tags_exact_push__lit_removable; assumption.
      * split.
        -- change (NoDup ((lit_var_c l :: fresh) ++ x :: nil)).
           apply NoDup_snoc; assumption.
        -- split.
           ++ rewrite app_comm_cons.
              rewrite app_assoc.
              apply NoDup_snoc; assumption.
           ++ split.
              ** rewrite app_comm_cons.
                 rewrite app_assoc.
                 change (Permutation ((done ++ v :: stack) ++ x :: nil)
                   ((lit_var_c l :: fresh) ++ x :: nil)).
                 apply Permutation_app_tail. exact Hpart.
              ** split.
                 --- intros y Hy. rewrite app_comm_cons in Hy.
                     apply in_app_or in Hy.
                     destruct Hy as [Hy | [Heq | []]].
                     +++ apply Hassigned. exact Hy.
                     +++ subst y. exact Hbelow.
                 --- split.
                     +++ intros y Hy. rewrite app_comm_cons in Hy.
                         apply in_app_or in Hy.
                         destruct Hy as [Hy | [Heq | []]].
                         *** apply Hreason. exact Hy.
                         *** subst y. exists q, Cx. exact Hreasonx.
                     +++ split.
                         *** intros y Hy.
                             destruct (Hwitness y Hy) as [Cy [Hry HCy]].
                             exists Cy. split; [exact Hry|].
                             intros a Ha Hay.
                             destruct (HCy a Ha Hay) as [H0 | [Hb | [Hd | Hs]]].
                             { left. exact H0. }
                             { right. left. exact Hb. }
                             { right. right. left. exact Hd. }
                             right. right. right.
                             destruct Hs as [Heq | Hs].
                             { left. exact Heq. }
                             right. apply in_or_app. left. exact Hs.
                         *** exact Hminl.
  - split; [exact Hfocus|].
    split; [lia|].
    split; [exact Hwf|].
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + specialize (Hfrontier k ltac:(lia)).
      destruct Hfrontier as [H0 | [Hb | [Hd | Hs]]].
      * left. exact H0.
      * right. left. exact Hb.
      * right. right. left. exact Hd.
      * right. right. right. apply in_or_app. left. exact Hs.
    + assert (k = i) by lia. subst k.
      right. right. right. apply in_or_app. right. left. reflexivity.
Qed.

Lemma reason_target_wf_view_reason__lit_removable :
  forall n M v p C,
    assigned_below_current (msolver_view n M) v ->
    reason_target_wf n M v p C ->
    reason_of (msolver_view n M) v = Some C.
Proof.
  intros n M v p C [_ [r [_ [Hrank _]]]] Htarget.
  unfold reason_target_wf in Htarget.
  destruct Htarget as [_ [_ [_ [Hreason _]]]].
  unfold msolver_view, view_of.
  cbn [reason_of].
  unfold msolver_view, view_of in Hrank.
  cbn [assignment_rank] in Hrank.
  now rewrite Hrank.
Qed.

Lemma reason_target_wf_tag_shape__lit_removable :
  forall n F A_arr K M focus v p C,
    analysis_cancel_ready n F A_arr K M focus ->
    reason_target_wf n M v p C ->
    is_tag p = true ->
    C = [lit_denote (trail_lit_of (ms_core M) v);
         literal_neg (lit_denote (tag_lit p))].
Proof.
  intros n F A_arr K M focus v p C Hready Htarget Htag.
  destruct Htarget as [Hvrange [Hp [Hpnonzero [Hreason Hkind]]]].
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K M focus Hready) as [Hsize [Hmatch Hbinary]].
  assert (Hpositive : 0 < p).
  { destruct Hkind as [[_ [Hpositive _]] | [co [Hreal _]]].
    - exact Hpositive.
    - congruence. }
  assert (Hcodec : reason_word_ok (ms_core M) v (msolver_db M) p
    (ms_reason_of M v)).
  { rewrite Hp. apply Hmatch. lia. }
  pose proof (reason_word_ok_tag
    (ms_core M) v (msolver_db M) p (ms_reason_of M v)
    Hpositive Htag Hcodec) as Hshape.
  rewrite Hreason in Hshape. inversion Hshape. reflexivity.
Qed.

Lemma removable_dfs_tagged_push__lit_removable :
  forall n F A_arr K M focus l minl base done stack tags tagged C v p x q Cx,
    analysis_cancel_ready n F A_arr K M focus ->
    removable_reason_scan_inv
      n M l minl base done stack tags tagged C v p 1 ->
    In (lit_var_c l) base ->
    is_tag p = true ->
    x = lit_var_c (tag_lit p) ->
    0 <= x < n ->
    Znth x tags 0 = 0 ->
    reason_target_wf n M x q Cx ->
    removable_dfs_loop_inv n M l minl base
      (replace_Znth x 1 tags) (tagged ++ x :: nil)
      (stack ++ x :: nil) (v :: done).
Proof.
  intros n F A_arr K M focus l minl base done stack tags tagged C v p x q Cx
    Hready Hscan Hbase Htag Hxdef Hx Hzero Hreasonx.
  assert (Hscan_copy := Hscan).
  unfold removable_reason_scan_inv in Hscan_copy.
  destruct Hscan_copy as [Hdfs [Hfocus Hscan_rest]].
  unfold removable_dfs_loop_inv in Hdfs.
  destruct Hdfs as [fresh
    [Htagged [Hexact [Hfresh [Hnodup [Hpart
      [Hassigned [Hreason [Hwitness Hminl]]]]]]]]].
  assert (Hvin : In v (lit_var_c l :: fresh)).
  { eapply Permutation_in; [exact Hpart|].
    apply in_or_app. right. left. reflexivity. }
  pose proof (Hassigned v Hvin) as Hvbelow.
  assert (Hshape : C =
    [lit_denote (trail_lit_of (ms_core M) v);
     literal_neg (lit_denote (tag_lit p))]).
  { eapply reason_target_wf_tag_shape__lit_removable;
      eauto. }
  assert (Hside_var : literal_var (Znth 1 C (Pos 0)) = x).
  { rewrite Hshape.
    change (literal_var (literal_neg (lit_denote (tag_lit p))) = x).
    rewrite literal_var_neg, lit_var_c_denote.
    exact (eq_sym Hxdef). }
  assert (Hside_neq : literal_var (Znth 1 C (Pos 0)) <> v).
  { destruct (analysis_cancel_ready_reason_core
      n F A_arr K M focus Hready) as [Hsize [Hmatch Hbinary]].
    unfold removable_reason_focus, reason_target_wf in Hfocus.
    destruct Hfocus as [Hvrange [Hp [Hpnonzero [HC Hkind]]]].
    destruct (Hbinary v ltac:(lia)) as [_ [_ Hdifferent]].
    - now rewrite <- Hp.
    - rewrite Hside_var, Hxdef, Hp. exact Hdifferent. }
  assert (Hxbelow : assigned_below_current (msolver_view n M) x).
  { rewrite <- Hside_var.
    eapply removable_reason_scan_side_assigned_below__lit_removable;
      [exact Hready | exact Hscan |
       rewrite Hshape, Zlength_cons, Zlength_cons, Zlength_nil; lia |
       exact Hside_neq]. }
  assert (Hvnonneg : 0 <= v).
  { unfold removable_reason_focus, reason_target_wf in Hfocus. lia. }
  assert (Hnot_tagged : ~ In x tagged).
  { unfold analysis_tags_exact in Hexact.
    destruct Hexact as [_ [_ [_ [_ Hiff]]]].
    intro Hin. apply (proj2 (Hiff x Hx)) in Hin. congruence. }
  assert (Hnot_fresh : ~ In x (lit_var_c l :: fresh)).
  { intro Hin. destruct Hin as [Heq | Hin].
    - apply Hnot_tagged. rewrite Htagged. apply in_or_app. left.
      rewrite <- Heq. exact Hbase.
    - apply Hnot_tagged. rewrite Htagged. apply in_or_app. right. exact Hin. }
  assert (Hworkperm : Permutation (v :: done ++ stack) (done ++ v :: stack)).
  { apply Permutation_middle. }
  assert (Hnot_work : ~ In x (v :: done ++ stack)).
  { intro Hin. apply Hnot_fresh.
    eapply Permutation_in; [eapply Permutation_trans;
      [exact Hworkperm | exact Hpart] | exact Hin]. }
  unfold removable_dfs_loop_inv.
  exists (fresh ++ x :: nil).
  split; [rewrite Htagged, app_assoc; reflexivity|].
  split.
  - apply analysis_tags_exact_push__lit_removable; assumption.
  - split; [change (NoDup ((lit_var_c l :: fresh) ++ x :: nil));
      apply NoDup_snoc; assumption|].
    split.
    + rewrite app_assoc.
      apply NoDup_snoc.
      * eapply Permutation_NoDup.
        -- apply Permutation_sym. exact Hworkperm.
        -- exact Hnodup.
      * exact Hnot_work.
    + split.
      * rewrite app_assoc.
        change (Permutation ((v :: done ++ stack) ++ x :: nil)
          ((lit_var_c l :: fresh) ++ x :: nil)).
        apply Permutation_app_tail.
        eapply Permutation_trans; [exact Hworkperm|exact Hpart].
      * split.
        -- intros y Hy. rewrite app_comm_cons in Hy.
           apply in_app_or in Hy.
           destruct Hy as [Hy | [Heq | []]].
           ++ apply Hassigned. exact Hy.
           ++ subst y. exact Hxbelow.
        -- split.
           ++ intros y Hy. apply in_app_or in Hy.
              destruct Hy as [Hy | [Heq | []]].
              ** apply Hreason. right. exact Hy.
              ** subst y. exists q, Cx. exact Hreasonx.
           ++ split.
              ** eapply dfs_witness_extend with (c := C).
                 --- exact Hwitness.
                 --- eapply reason_target_wf_view_reason__lit_removable;
                     [exact Hvbelow|exact Hfocus].
                 --- intros a Ha Hneq.
                     rewrite Hshape in Ha.
                     destruct Ha as [Heq | [Heq | []]].
                     +++ exfalso. apply Hneq. subst a.
                         rewrite lit_var_c_denote,
                           (trail_lit_of_var (ms_core M) v Hvnonneg).
                         reflexivity.
                     +++ right. right. right. apply in_or_app. right. left.
                         subst a. rewrite literal_var_neg, lit_var_c_denote.
                         exact Hxdef.
                 --- intros y Hy. apply in_or_app. left. exact Hy.
              ** exact Hminl.
Qed.

Lemma reason_target_wf_nodup__lit_removable :
  forall n F A_arr K M focus v p C,
    analysis_cancel_ready n F A_arr K M focus ->
    reason_target_wf n M v p C ->
    NoDup (map literal_var C).
Proof.
  intros n F A_arr K M focus v p C Hready Htarget.
  destruct Htarget as [Hvrange [Hp [Hpnonzero [Hreason Hkind]]]].
  destruct Hkind as [[Htag [Hpositive Hwf]] |
    [co [Htag [Hbinary [Hin HC]]]]].
  - eapply (analysis_cancel_ready_tagged_reason_nodup
      n F A_arr K M focus v C).
    + exact Hready.
    + destruct (analysis_cancel_ready_reason_core
        n F A_arr K M focus Hready) as [Hsize _].
      rewrite Hsize. exact Hvrange.
    + rewrite <- Hp. exact Htag.
    + exact Hreason.
  - subst C. apply (obj_wf_nodup_vars n co).
    destruct (analysis_cancel_ready_semantic_core__lit_removable
      n F A_arr K M focus Hready) as [_ [_ [_ [Hdb _]]]].
    exact (db_wf_obj n (msolver_db M) p co Hdb Hin).
Qed.

Lemma reason_target_wf_head_var__lit_removable :
  forall n F A_arr K M focus v p C,
    analysis_cancel_ready n F A_arr K M focus ->
    reason_target_wf n M v p C ->
    literal_var (Znth 0 C (Pos 0)) = v.
Proof.
  intros n F A_arr K M focus v p C Hready Htarget.
  destruct Htarget as [Hvrange [Hp [Hpnonzero [Hreason Hkind]]]].
  destruct Hkind as [[Htag [Hpositive Hwf]] |
    [co [Htag [Hbinary [Hin HC]]]]].
  - destruct (analysis_cancel_ready_reason_core
      n F A_arr K M focus Hready) as [Hsize [Hmatch Hsame]].
    assert (Hcodec : reason_word_ok (ms_core M) v (msolver_db M) p
      (ms_reason_of M v)).
    { rewrite Hp. apply Hmatch. lia. }
    pose proof (reason_word_ok_tag
      (ms_core M) v (msolver_db M) p (ms_reason_of M v)
      Hpositive Htag Hcodec) as Hshape.
    rewrite Hreason in Hshape. inversion Hshape. subst C.
    cbn. rewrite lit_var_c_denote, trail_lit_of_var; lia.
  - subst C.
    destruct (analysis_cancel_ready_semantic_core__lit_removable
      n F A_arr K M focus Hready) as [_ [_ [_ [Hdb Hhead]]]].
    pose proof (db_wf_obj n (msolver_db M) p co Hdb Hin) as Hobj.
    unfold denote_obj, lits_denote.
    rewrite (Znth_map Z literal lit_denote (co_lits co) 0 0 (Pos 0)) by
      (destruct Hobj as [Hlen _]; lia).
    rewrite lit_var_c_denote.
    unfold co_watch0 in Hhead.
    eapply Hhead.
    + exact Hvrange.
    + rewrite <- Hp. exact Htag.
    + rewrite <- Hp. exact Hpnonzero.
    + rewrite <- Hp. exact Hin.
Qed.

Lemma nodup_map_Znth_neq__lit_removable :
  forall C i j,
    NoDup (map literal_var C) ->
    0 <= i < Zlength C ->
    0 <= j < Zlength C ->
    i <> j ->
    literal_var (Znth i C (Pos 0)) <>
      literal_var (Znth j C (Pos 0)).
Proof.
  intros C i j Hnodup Hi Hj Hij Heq.
  rewrite NoDup_nth_error in Hnodup.
  specialize (Hnodup (Z.to_nat i) (Z.to_nat j)).
  rewrite length_map in Hnodup.
  assert (Hli : (Z.to_nat i < List.length C)%nat).
  { rewrite Zlength_correct in Hi. lia. }
  assert (Hlj : (Z.to_nat j < List.length C)%nat).
  { rewrite Zlength_correct in Hj. lia. }
  assert (Hnth : nth_error (map literal_var C) (Z.to_nat i) =
    nth_error (map literal_var C) (Z.to_nat j)).
  { rewrite !nth_error_map.
    rewrite (nth_error_nth' C (Pos 0) Hli).
    rewrite (nth_error_nth' C (Pos 0) Hlj).
    simpl. unfold Znth in Heq. now rewrite Heq. }
  specialize (Hnodup Hli Hnth).
  apply Hij. lia.
Qed.

Lemma removable_reason_scan_side_neq__lit_removable :
  forall n F A_arr K M focus l minl base done stack tags tagged C v p i,
    analysis_cancel_ready n F A_arr K M focus ->
    removable_reason_scan_inv
      n M l minl base done stack tags tagged C v p i ->
    1 <= i < Zlength C ->
    literal_var (Znth i C (Pos 0)) <> v.
Proof.
  intros n F A_arr K M focus l minl base done stack tags tagged C v p i
    Hready Hscan Hi.
  assert (Hfocus : reason_target_wf n M v p C).
  { unfold removable_reason_scan_inv in Hscan. tauto. }
  pose proof (reason_target_wf_nodup__lit_removable
    n F A_arr K M focus v p C Hready Hfocus) as Hnodup.
  pose proof (reason_target_wf_head_var__lit_removable
    n F A_arr K M focus v p C Hready Hfocus) as Hhead.
  rewrite <- Hhead.
  eapply nodup_map_Znth_neq__lit_removable;
    [exact Hnodup | lia | lia | lia].
Qed.

Lemma analysis_tags_exact_permutation__lit_removable :
  forall n tags tagged tagged',
    Permutation tagged tagged' ->
    analysis_tags_exact n tags tagged ->
    analysis_tags_exact n tags tagged'.
Proof.
  intros n tags tagged tagged' Hperm
    (Hlen & Hnodup & Hrange & Hbits & Hexact).
  unfold analysis_tags_exact.
  split; [exact Hlen |].
  split; [apply (Permutation_NoDup Hperm); exact Hnodup |].
  split.
  - rewrite Forall_forall in Hrange |- *.
    intros x Hx. apply Hrange.
    eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hx].
  - split; [exact Hbits |].
    intros v Hv. rewrite Hexact by exact Hv.
    split; intro Hin.
    + eapply Permutation_in; eauto.
    + eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin].
Qed.

Lemma analysis_tags_exact_clear_head__lit_removable :
  forall n tags x xs,
    analysis_tags_exact n tags (x :: xs) ->
    analysis_tags_exact n (replace_Znth x 0 tags) xs.
Proof.
  intros n tags x xs
    (Hlen & Hnodup & Hrange & Hbits & Hexact).
  pose proof Hlen as Hlen0.
  assert (Hnewlen : Zlength (replace_Znth x 0 tags) = n)
    by (rewrite Zlength_replace_Znth; exact Hlen0).
  inversion Hnodup as [| ? ? Hnotin Hnodup']; subst.
  inversion Hrange as [| ? ? Hxrange Hrange']; subst.
  unfold analysis_tags_exact.
  split; [exact Hnewlen |].
  split; [exact Hnodup' |].
  split; [exact Hrange' |].
  split.
  - apply Forall_replace_Znth; [exact Hbits | left; reflexivity].
  - intros v Hv. destruct (Z.eq_dec v x) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      simpl. split; [discriminate | intros Hin; exfalso; exact (Hnotin Hin)].
    + rewrite Znth_replace_Znth_Diff by lia.
      rewrite Hexact by exact Hv. simpl.
      split.
      * intros [Heq | Hin]; [congruence | exact Hin].
      * intros Hin. right. exact Hin.
Qed.

Lemma analysis_tags_exact_clear_suffix__lit_removable :
  forall n tags base suffix,
    analysis_tags_exact n tags (base ++ suffix) ->
    analysis_tags_exact n (clear_indices suffix tags) base.
Proof.
  intros n tags base suffix. revert tags.
  induction suffix as [| x rest IH]; intros tags Hexact.
  - simpl in *. rewrite app_nil_r in Hexact. exact Hexact.
  - simpl. apply IH.
    apply analysis_tags_exact_clear_head__lit_removable.
    eapply analysis_tags_exact_permutation__lit_removable.
    + apply Permutation_sym. apply Permutation_middle.
    + exact Hexact.
Qed.

Lemma analysis_tags_exact_unique__lit_removable :
  forall n tags1 tags2 tagged,
    analysis_tags_exact n tags1 tagged ->
    analysis_tags_exact n tags2 tagged ->
    tags1 = tags2.
Proof.
  intros n tags1 tags2 tagged
    (Hlen1 & _ & _ & Hbits1 & Hexact1)
    (Hlen2 & _ & _ & Hbits2 & Hexact2).
  apply (proj2 (list_eq_ext tags1 tags2 0)). split.
  - lia.
  - intros i Hi.
    assert (Hi2 : 0 <= i < Zlength tags2) by lia.
    assert (Hin1 : In (Znth i tags1 0) tags1) by (apply Znth_In; exact Hi).
    assert (Hin2 : In (Znth i tags2 0) tags2) by (apply Znth_In; exact Hi2).
    rewrite Forall_forall in Hbits1, Hbits2.
    specialize (Hbits1 _ Hin1). specialize (Hbits2 _ Hin2).
    specialize (Hexact1 i ltac:(lia)). specialize (Hexact2 i ltac:(lia)).
    destruct Hbits1 as [Hzero1 | Hone1];
      destruct Hbits2 as [Hzero2 | Hone2].
    + rewrite Hzero1, Hzero2. reflexivity.
    + rewrite Hzero1, Hone2. exfalso.
      pose proof (proj1 Hexact2 Hone2) as Hin.
      pose proof (proj2 Hexact1 Hin) as Hbad. rewrite Hzero1 in Hbad. discriminate.
    + rewrite Hone1, Hzero2. exfalso.
      pose proof (proj1 Hexact1 Hone1) as Hin.
      pose proof (proj2 Hexact2 Hin) as Hbad. rewrite Hzero2 in Hbad. discriminate.
    + rewrite Hone1, Hone2. reflexivity.
Qed.

Lemma removable_rollback_restore__lit_removable :
  forall n top j base entry_tags tags0 tagged tags,
    removable_rollback_inv n top j base entry_tags tags0 tagged tags ->
    j = Zlength tagged ->
    tags = entry_tags /\ sublist 0 top tagged = base.
Proof.
  intros n top j base entry_tags tags0 tagged tags Hinv Hj.
  unfold removable_rollback_inv in Hinv.
  destruct Hinv as
    (Htop0 & Htopj & Hjlen & Htoplen & Hprefix & Hentry & Htagged & Hclear).
  subst j. split; [| exact Hprefix].
  rewrite Hclear.
  assert (Hdecomp : tagged = base ++ sublist top (Zlength tagged) tagged).
  { rewrite <- (sublist_self tagged (Zlength tagged) eq_refl) at 1.
    rewrite (sublist_split 0 (Zlength tagged) top tagged) by lia.
    rewrite Hprefix. reflexivity. }
  apply analysis_tags_exact_unique__lit_removable
    with (n := n) (tagged := base).
  - apply analysis_tags_exact_clear_suffix__lit_removable.
    rewrite <- Hdecomp. exact Htagged.
  - exact Hentry.
Qed.

Lemma clause_db_pair_refold__lit_removable :
  forall prob learnt c is_learnt words,
    MiniSatClause.rep c is_learnt words **
    clause_db_pair_remainder prob learnt c is_learnt words |--
    clause_db_rep prob ** clause_db_rep learnt.
Proof.
  intros prob learnt c is_learnt words.
  unfold clause_db_pair_remainder at 1. Split.
  - Intros co pre post.
    destruct H as (Hdb & Hlits & Htag). subst prob.
    sep_apply_r_atomic (clause_db_rep_app_intro pre ((c, co) :: post)).
    rewrite clause_db_rep_cons. cbn [fst snd]. rewrite Htag, Hlits. (Intros; cancel).
  - Intros co pre post.
    destruct H as (Hdb & Hlits & Htag). subst learnt.
    sep_apply_r_atomic (clause_db_rep_app_intro pre ((c, co) :: post)).
    rewrite clause_db_rep_cons. cbn [fst snd]. rewrite Htag, Hlits. msat_entailer_with lia.
Qed.

Lemma analysis_cancel_ready_shape__lit_removable :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    Zlength (ms_orderpos M) = ms_size M ->
    Zlength (ms_activity M) = ms_size M ->
    Zlength (ms_tags M) = ms_size M ->
    Zlength (ms_stats M) = 11 ->
    solver_shape M.
Proof.
  intros n F A_arr K M focus [M0 [[[Hpending Hctx] Hcancel] [Hequiv Hrest]]]
    Horder Hactivity Htags Hstats.
  eapply analysis_core_equiv_shape; try eassumption.
  exact (msolver_inv_ctx_shape n F A_arr K M0 Hctx).
Qed.

Lemma analysis_cancel_ready_size__lit_removable :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus -> n = ms_size M.
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (asc_size _ _ _ Hctx).
Qed.

Lemma solver_removable_scratch_refold_residual__lit_removable :
  forall s M rsn lvl trl tgs tagged_ptr tagged_cap stack wl,
    solver_shape M ->
    (Veci.rep &(s # "solver_t" ->ₛ "stack") stack **
     Veci.rep_at &(s # "solver_t" ->ₛ "tagged") tagged_ptr
       (ms_tagged M) tagged_cap **
     clause_db_rep (ms_prob M) **
     clause_db_rep (ms_learnt M) **
     CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
     solver_removable_frame_at s M trl wl **
     &(s # "solver_t" ->ₛ "tags") # Ptr |-> tgs **
     solver_char_tail tgs (ms_size M) (ms_cap M) **
     &(s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
     &(s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
     &(s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
     PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
     solver_ptr_tail rsn (ms_size M) (ms_cap M) **
     IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
     solver_int_tail lvl (ms_size M) (ms_cap M) **
     binary_scratch_rep (ms_binary M) (ms_binary_lits M) |--
     solver_rep_analyze_at s
       (msolver_scratch_update M (ms_tags M) (ms_tagged M) stack) rsn lvl trl tgs wl).
Proof. msat_removable_scratch_refold wl act asg opos. Qed.

Lemma solver_removable_scratch_refold_return3__lit_removable :
  forall s M rsn lvl trl tgs tagged_ptr tagged_cap stack wl,
    solver_shape M ->
    (Veci.rep &(s # "solver_t" ->ₛ "stack") stack **
     Veci.rep_at &(s # "solver_t" ->ₛ "tagged") tagged_ptr
       (ms_tagged M) tagged_cap **
     CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
     solver_removable_frame_at s M trl wl **
     &(s # "solver_t" ->ₛ "tags") # Ptr |-> tgs **
     solver_char_tail tgs (ms_size M) (ms_cap M) **
     &(s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
     &(s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
     &(s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
     PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
     solver_ptr_tail rsn (ms_size M) (ms_cap M) **
     IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
     solver_int_tail lvl (ms_size M) (ms_cap M) **
     clause_db_rep (ms_prob M) **
     clause_db_rep (ms_learnt M) **
     binary_scratch_rep (ms_binary M) (ms_binary_lits M) |--
     solver_rep_analyze_at s
       (msolver_scratch_update M (ms_tags M) (ms_tagged M) stack) rsn lvl trl tgs wl).
Proof. msat_removable_scratch_refold wl act asg opos. Qed.

Lemma solver_shape_scratch_update__lit_removable :
  forall M tags tagged stack,
    solver_shape M ->
    Zlength tags = ms_size M ->
    solver_shape
      (msolver_scratch_update M tags tagged stack).
Proof.
  intros M tags tagged stack Hshape Htags.
  unfold solver_shape, msolver_scratch_update, msolver_analysis_update in *.
  simpl in *. tauto.
Qed.

Lemma solver_removable_scratch_refold_general__lit_removable :
  forall s M n rsn lvl trl tgs tags tagged stack wl,
    n = ms_size M ->
    solver_shape
      (msolver_scratch_update M tags tagged stack) ->
    (Veci.rep &(s # "solver_t" ->ₛ "stack") stack **
     CharArray.seg tgs 0 n tags **
     solver_removable_frame_at s M trl wl **
     &(s # "solver_t" ->ₛ "size") # Int |-> n **
     &(s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
     &(s # "solver_t" ->ₛ "levels") # Ptr |-> lvl **
     &(s # "solver_t" ->ₛ "tags") # Ptr |-> tgs **
     PtrArray.seg rsn 0 n (ms_reason_words M) **
     solver_ptr_tail rsn n (ms_cap M) **
     IntArray.seg lvl 0 n (mt_levels (ms_core M)) **
     solver_int_tail lvl n (ms_cap M) **
     solver_char_tail tgs n (ms_cap M) **
     Veci.rep &(s # "solver_t" ->ₛ "tagged") tagged **
     clause_db_rep (ms_prob M) **
     clause_db_rep (ms_learnt M) **
     binary_scratch_rep (ms_binary M) (ms_binary_lits M) |--
     solver_rep_analyze_at s
       (msolver_scratch_update M tags tagged stack)
       rsn lvl trl tgs wl).
Proof.
  intros s M n rsn lvl trl tgs tags tagged stack
    wl Hn Hshape. subst n.
  unfold solver_removable_frame_at at 1. Intros act asg opos.
  unfold solver_rep_analyze_at. Exists act asg opos.
  unfold solver_rep_at.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_vecs_rep, solver_ptrs_rep,
  solver_var_arrays_rep.
  cbn [msolver_scratch_update msolver_analysis_update ].
  unfold solver_scalars_rep, clause_new_scalars_frame,
    solver_levels_slice_at.
  cbn [msolver_scratch_update msolver_analysis_update ms_size ms_cap ms_qtail ms_capacity_pending_qhead
    ms_capacity_root_propagation_pending ms_core ms_root_level ms_reason_words ms_reason_of ms_prob
    ms_learnt ms_binary ms_binary_lits ms_wm ms_activity ms_orderpos
    ms_order ms_model ms_tags ms_tagged ms_stack ms_var_inc ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed ms_progress
    ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats].
  change (solver_fp_rep s (msolver_scratch_update M tags tagged stack))
    with (solver_fp_rep s M).
  change (solver_trail_array_rep (msolver_scratch_update M tags tagged stack) trl)
    with (solver_trail_array_rep M trl).
  msat_entailer_with ltac:(first [exact Hshape | lia]).
Qed.

Lemma solver_removable_frame_lengths_keep__lit_removable :
  forall s M trl wl,
    solver_removable_frame_at s M trl wl |--
      “ Zlength (ms_activity M) = ms_size M /\
        Zlength (ms_orderpos M) = ms_size M /\
        Zlength (ms_stats M) = 11 ” &&
      solver_removable_frame_at s M trl wl.
Proof.
  intros s M trl wl.
  unfold solver_removable_frame_at at 1. Intros act asg opos.
  prop_apply_p (DoubleArray.seg_Zlength act 0 (ms_size M) (ms_activity M)).
  Intros_p Hactivity_len.
  prop_apply_p (IntArray.seg_Zlength opos 0 (ms_size M) (ms_orderpos M)).
  Intros_p Horder_len.
  unfold stats_rep at 1. Intros_p Hstats_len.
  unfold solver_removable_frame_at. Exists act asg opos.
  unfold stats_rep. msat_entailer_with lia.
Qed.

Lemma removable_dfs_complete_post__lit_removable :
  forall n M l minl base tags tagged done,
    removable_dfs_loop_inv n M l minl base tags tagged [] done ->
    exists fresh,
      tagged = base ++ fresh /\
      analysis_tags_exact n tags tagged /\
      removable_witness (msolver_view n M) base (lit_var_c l :: fresh) /\
      (forall x, In x (lit_var_c l :: fresh) ->
         assigned_below_current (msolver_view n M) x).
Proof.
  intros n M l minl base tags tagged done Hinv.
  unfold removable_dfs_loop_inv in Hinv.
  destruct Hinv as (fresh & Htagged & Hexact & Hnodup1 & Hnodup2 & Hperm & Hassigned & Htargets &
    Hinv).
  destruct Hinv as [Hdfs Hminl].
  exists fresh. split; [exact Htagged |].
  split; [exact Hexact |].
  split; [| exact Hassigned].
  pose proof (dfs_witness_complete (msolver_view n M) base done Hdfs) as Hdone.
  unfold removable_witness in Hdone |- *.
  rewrite app_nil_r in Hperm.
  intros x Hx.
  assert (Hxdone : In x done).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hx]. }
  destruct (Hdone x Hxdone) as [C [Hr Hside]].
  exists C. split; [exact Hr |].
  intros q Hq Hneq.
  destruct (Hside q Hq Hneq) as [H0 | [Hb | Hd]].
  - left. exact H0.
  - right. left. exact Hb.
  - right. right.
    eapply Permutation_in; [exact Hperm | exact Hd].
Qed.

Lemma removable_success_post_pure__lit_removable :
  forall n F A_arr K M focus tags tagged stack l fresh,
    analysis_cancel_ready n F A_arr K
      (msolver_scratch_update M tags tagged stack) focus ->
    msolver_seed_shadow
      (msolver_scratch_update M tags tagged stack) ->
    analysis_core_equiv M
      (msolver_scratch_update M tags tagged stack) ->
    stack = (@nil Z) ->
    tagged = List.app (ms_tagged M) fresh ->
    analysis_tags_exact n tags tagged ->
    removable_witness (msolver_view n M) (ms_tagged M)
      (cons (lit_var_c l) fresh) ->
    (forall x, In x (cons (lit_var_c l) fresh) ->
       assigned_below_current (msolver_view n M) x) ->
    analysis_cancel_ready n F A_arr K
      (msolver_scratch_update M tags tagged stack) focus /\
    msolver_seed_shadow
      (msolver_scratch_update M tags tagged stack) /\
    analysis_core_equiv M
      (msolver_scratch_update M tags tagged stack) /\
    ((1 = 0 /\
       ms_tags
         (msolver_scratch_update M tags tagged stack) =
       ms_tags M /\
       ms_tagged
         (msolver_scratch_update M tags tagged stack) =
       ms_tagged M) \/
     (1 = 1 /\
       ms_stack
         (msolver_scratch_update M tags tagged stack) =
       (@nil Z) /\
       exists fresh',
         ms_tagged
           (msolver_scratch_update M tags tagged stack) =
         List.app (ms_tagged M) fresh' /\
         analysis_tags_exact n
           (ms_tags
             (msolver_scratch_update M tags tagged stack))
           (ms_tagged
             (msolver_scratch_update M tags tagged stack)) /\
         removable_witness (msolver_view n M) (ms_tagged M)
           (cons (lit_var_c l) fresh') /\
         (forall x, In x (cons (lit_var_c l) fresh') ->
            assigned_below_current (msolver_view n M) x))).
Proof.
  intros n F A_arr K M focus tags tagged stack l fresh
    Hready Hseed Hequiv Hstack Htagged Hexact Hrem Hassigned.
  split; [exact Hready |].
  split; [exact Hseed |].
  split; [exact Hequiv |].
  right. split; [reflexivity |]. split.
  - change (stack = (@nil Z)). exact Hstack.
  - exists fresh.
    change (tagged = List.app (ms_tagged M) fresh /\
      analysis_tags_exact n tags tagged /\
      removable_witness (msolver_view n M) (ms_tagged M)
        (cons (lit_var_c l) fresh) /\
      (forall x, In x (cons (lit_var_c l) fresh) ->
         assigned_below_current (msolver_view n M) x)).
    split; [exact Htagged |].
    split; [exact Hexact |].
    split; [exact Hrem | exact Hassigned].
Qed.

Lemma removable_failure_post_pure__lit_removable :
  forall n F A_arr K M focus tags tagged stack,
    analysis_cancel_ready n F A_arr K
      (msolver_scratch_update M tags tagged stack) focus ->
    msolver_seed_shadow
      (msolver_scratch_update M tags tagged stack) ->
    analysis_core_equiv M
      (msolver_scratch_update M tags tagged stack) ->
    tags = ms_tags M ->
    tagged = ms_tagged M ->
    analysis_cancel_ready n F A_arr K
      (msolver_scratch_update M tags tagged stack) focus /\
    msolver_seed_shadow
      (msolver_scratch_update M tags tagged stack) /\
    analysis_core_equiv M
      (msolver_scratch_update M tags tagged stack) /\
    ((0 = 0 /\
       ms_tags
         (msolver_scratch_update M tags tagged stack) =
       ms_tags M /\
       ms_tagged
         (msolver_scratch_update M tags tagged stack) =
       ms_tagged M) \/
     (0 = 1 /\
       ms_stack
         (msolver_scratch_update M tags tagged stack) =
       (@nil Z) /\
       exists fresh,
         ms_tagged
           (msolver_scratch_update M tags tagged stack) =
         List.app (ms_tagged M) fresh /\
         analysis_tags_exact n
           (ms_tags
             (msolver_scratch_update M tags tagged stack))
           (ms_tagged
             (msolver_scratch_update M tags tagged stack)) /\
         removable_witness (msolver_view n M) (ms_tagged M) fresh /\
         (forall x, In x fresh ->
            assigned_below_current (msolver_view n M) x))).
Proof.
  intros n F A_arr K M focus tags tagged stack
    Hready Hseed Hequiv Htags Htagged.
  split; [exact Hready |].
  split; [exact Hseed |].
  split; [exact Hequiv |].
  left. split; [reflexivity |].
  split.
  - change (tags = ms_tags M). exact Htags.
  - change (tagged = ms_tagged M). exact Htagged.
Qed.

Lemma removable_dfs_loop_inv_finish_head__lit_removable :
  forall n M l minl base tags tagged v stack done C,
    removable_dfs_loop_inv n M l minl base tags tagged (v :: stack) done ->
    reason_of (msolver_view n M) v = Some C ->
    (forall q, In q C -> literal_var q <> v ->
       level_of (msolver_view n M) (literal_var q) = Some 0 \/
       In (literal_var q) base \/
       In (literal_var q) (v :: done) \/ In (literal_var q) stack) ->
    removable_dfs_loop_inv n M l minl base tags tagged stack (v :: done).
Proof.
  intros n M l minl base tags tagged v stack done C
    Hinv Hr Hside.
  unfold removable_dfs_loop_inv in *.
  destruct Hinv as (fresh & Htagged & Hexact & Hfresh & Hnodup & Hpart & Hassigned & Hreason & Hinv).
  destruct Hinv as [Hdfs Hminl].
  exists fresh. split; [exact Htagged |].
  split; [exact Hexact |].
  split; [exact Hfresh |].
  split.
  - eapply Permutation_NoDup.
    + apply Permutation_sym. apply Permutation_middle.
    + exact Hnodup.
  - split.
    + eapply Permutation_trans.
      * apply Permutation_middle.
      * exact Hpart.
    + split; [exact Hassigned |].
      split.
      * intros x Hx. apply Hreason. right. exact Hx.
      * split.
        -- eapply dfs_witness_extend with (c := C) (stk := stack).
           ++ exact Hdfs.
           ++ exact Hr.
           ++ exact Hside.
           ++ apply incl_refl.
        -- exact Hminl.
Qed.

Lemma removable_dfs_tagged_member_partition__lit_removable :
  forall n M l minl base tags tagged stack done x,
    removable_dfs_loop_inv n M l minl base tags tagged stack done ->
    In x tagged -> In x base \/ In x done \/ In x stack.
Proof.
  intros n M l minl base tags tagged stack done x Hinv Hx.
  unfold removable_dfs_loop_inv in Hinv.
  destruct Hinv as (fresh & Htagged & _ & _ & _ & Hpart & Hinv).
  rewrite Htagged in Hx. apply in_app_or in Hx.
  destruct Hx as [Hb | Hfresh]; [tauto |].
  assert (Hrhs : In x (lit_var_c l :: fresh)) by (right; exact Hfresh).
  pose proof (Permutation_in x (Permutation_sym Hpart) Hrhs) as Hlhs.
  apply in_app_or in Hlhs. tauto.
Qed.

Lemma analysis_tags_exact_nonzero_in__lit_removable :
  forall n tags tagged v,
    analysis_tags_exact n tags tagged ->
    0 <= v < n -> Znth v tags 0 <> 0 -> In v tagged.
Proof.
  intros n tags tagged v Hexact Hv Hnz.
  unfold analysis_tags_exact in Hexact.
  destruct Hexact as [Hlen [Hnodup [Hrange [Hbits Hiff]]]].
  apply (proj1 (Hiff v Hv)).
  pose proof (Forall_Znth_elim Z
    (fun z => z = 0 \/ z = 1) tags 0 v Hbits
    ltac:(rewrite Hlen; exact Hv)) as Hbit.
  destruct Hbit as [Hzero | Hone].
  - contradiction.
  - exact Hone.
Qed.

Lemma analysis_cancel_ready_trail_stable__lit_removable :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    mtrail_wf n (ms_core M) /\ stable_view (msolver_view n M).
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (conj (asc_trail_wf _ _ _ Hctx) (asc_stable _ _ _ Hctx)).
Qed.

Lemma analysis_cancel_ready_db_head__lit_removable :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    db_wf n (msolver_db M) /\ reason_head_ok M.
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (conj (asc_db_wf _ _ _ Hctx) (asc_reason_head _ _ _ Hctx)).
Qed.

Lemma stable_reason_valid__lit_removable :
  forall n M v C,
    mtrail_wf n (ms_core M) ->
    stable_view (msolver_view n M) ->
    reason_of (msolver_view n M) v = Some C ->
    reason_valid (msolver_view n M) v C.
Proof.
  intros n M v C Hwf [Hgrounded _] Hr.
  pose proof Hr as Hrraw.
  unfold msolver_view, view_of in Hrraw.
  cbn [reason_of] in Hrraw.
  destruct (trail_pos (ms_core M) v) as [r |] eqn:Hrank;
    [|discriminate].
  assert (Hrank' : assignment_rank (msolver_view n M) v = Some r).
  { unfold msolver_view, view_of. cbn [assignment_rank]. exact Hrank. }
  destruct (assignment_of_rank__lit_removable
    n M v r Hwf Hrank') as [b Hb].
  destruct (Hgrounded v b Hb) as [d [rx [Hd [Hrx Hreason]]]].
  destruct Hreason as [Hnone | [C' [Hr' Hvalid]]].
  - rewrite Hnone in Hr. discriminate.
  - rewrite Hr in Hr'. inversion Hr'. subst C'. exact Hvalid.
Qed.

Lemma assigned_rank_level_word_zero__lit_removable :
  forall n M x d r,
    mtrail_wf n (ms_core M) ->
    level_of (msolver_view n M) x = Some d ->
    assignment_rank (msolver_view n M) x = Some r ->
    Znth x (mt_levels (ms_core M)) 0 = 0 ->
    level_of (msolver_view n M) x = Some 0.
Proof.
  intros n M x d r Hwf Hlevel Hrank Hzero.
  assert (Hrank' : trail_pos (ms_core M) x = Some r).
  { exact Hrank. }
  pose proof (trail_pos_bound (ms_core M) x r Hrank') as Hbound.
  pose proof (trail_pos_var (ms_core M) x r Hrank') as Hvar.
  pose proof (mtw_levels_agree Hwf (Z.of_nat r)) as Hagree.
  specialize (Hagree ltac:(lia)). rewrite Hvar, Hzero in Hagree.
  unfold msolver_view, view_of. cbn [level_of].
  rewrite Hrank'. simpl. f_equal. symmetry. exact Hagree.
Qed.

Lemma removable_reason_focus_view__lit_removable :
  forall n F A_arr K M focus v p C,
    analysis_cancel_ready n F A_arr K M focus ->
    removable_reason_focus n M v p C ->
    reason_of (msolver_view n M) v = Some C.
Proof.
  intros n F A_arr K M focus v p C Hready Hfocus.
  destruct (analysis_cancel_ready_trail_stable__lit_removable
    n F A_arr K M focus Hready) as [Hwf Hstable].
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K M focus Hready) as [Hsize [Hmatch Hbinary]].
  unfold removable_reason_focus, reason_target_wf in Hfocus.
  destruct Hfocus as [Hv [Hp [Hp0 [Hr Hkind]]]].
  assert (Hvn : 0 <= v < n) by lia.
  specialize (Hmatch v Hvn). rewrite <- Hp in Hmatch.
  pose proof (reason_word_ok_nonzero_assigned
    (ms_core M) v (msolver_db M) p (ms_reason_of M v) Hp0 Hmatch)
    as Hassigned.
  apply (proj1 (mtw_assigned_iff Hwf v Hvn)) in Hassigned.
  destruct (find_var_pos_in v (mt_trail (ms_core M)) Hassigned)
    as [r Hrank].
  change ((match trail_pos (ms_core M) v with
           | Some _ => ms_reason_of M v
           | None => None
           end) = Some C).
  unfold trail_pos. rewrite Hrank. exact Hr.
Qed.

Lemma removable_reason_side_level_word_zero__lit_removable :
  forall n F A_arr K M focus v p C q,
    analysis_cancel_ready n F A_arr K M focus ->
    removable_reason_focus n M v p C ->
    In q C -> literal_var q <> v ->
    Znth (literal_var q) (mt_levels (ms_core M)) 0 = 0 ->
    level_of (msolver_view n M) (literal_var q) = Some 0.
Proof.
  intros n F A_arr K M focus v p C q
    Hready Hfocus Hq Hneq Hzero.
  destruct (analysis_cancel_ready_trail_stable__lit_removable
    n F A_arr K M focus Hready) as [Hwf Hstable].
  pose proof (removable_reason_focus_view__lit_removable
    n F A_arr K M focus v p C Hready Hfocus) as Hr.
  pose proof (stable_reason_valid__lit_removable
    n M v C Hwf Hstable Hr) as Hvalid.
  destruct Hvalid as [b [d [rv [_ [_ [_ [_ Hside]]]]]]].
  destruct (Hside q Hq Hneq) as
    [_ [dq [rq [Hlevel [Hrank Hbounds]]]]].
  eapply assigned_rank_level_word_zero__lit_removable;
    [exact Hwf | exact Hlevel | exact Hrank | exact Hzero].
Qed.

Lemma tagged_reason_clause_shape__lit_removable :
  forall n F A_arr K M focus v p C,
    analysis_cancel_ready n F A_arr K M focus ->
    removable_reason_focus n M v p C ->
    is_tag p = true ->
    C = [lit_denote (trail_lit_of (ms_core M) v);
         literal_neg (lit_denote (tag_lit p))].
Proof.
  intros n F A_arr K M focus v p C Hready Hfocus Htag.
  unfold removable_reason_focus, reason_target_wf in Hfocus.
  destruct Hfocus as [Hv [Hp [Hp0 [Hr Hkind]]]].
  destruct Hkind as [[_ [Hpos _]] | Hreal].
  2: { destruct Hreal as [co [Hnotag _]]; congruence. }
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K M focus Hready) as [Hsize [Hmatch _]].
  assert (Hvn : 0 <= v < n) by lia.
  specialize (Hmatch v Hvn). rewrite <- Hp in Hmatch.
  pose proof (reason_word_ok_tag (ms_core M) v (msolver_db M) p
    (ms_reason_of M v) Hpos Htag Hmatch) as Hshape.
  rewrite Hr in Hshape. inversion Hshape. reflexivity.
Qed.

Lemma real_reason_clause_head__lit_removable :
  forall n F A_arr K M focus v p C,
    analysis_cancel_ready n F A_arr K M focus ->
    removable_reason_focus n M v p C ->
    is_tag p = false ->
    literal_var (Znth 0 C (Pos 0)) = v.
Proof.
  intros n F A_arr K M focus v p C Hready Hfocus Hnotag.
  destruct (analysis_cancel_ready_db_head__lit_removable
    n F A_arr K M focus Hready) as [Hdbwf Hhead].
  unfold removable_reason_focus, reason_target_wf in Hfocus.
  destruct Hfocus as [Hv [Hp [Hp0 [Hr Hkind]]]].
  destruct Hkind as [[Htag _] | [co [Htag [Hpbin [Hin HC]]]]];
    [congruence |].
  pose proof (db_wf_obj n (msolver_db M) p co Hdbwf Hin) as Hobj.
  destruct Hobj as [Hlen _].
  assert (Hnotag' : is_tag (Znth v (ms_reason_words M) 0) = false)
    by (rewrite <- Hp; exact Hnotag).
  assert (Hp0' : Znth v (ms_reason_words M) 0 <> 0)
    by (rewrite <- Hp; exact Hp0).
  rewrite Hp in Hin.
  pose proof (Hhead v co Hv Hnotag' Hp0' Hin) as Hcohead.
  rewrite HC. unfold denote_obj, lits_denote, co_watch0 in *.
  rewrite (Znth_map Z literal lit_denote (co_lits co) 0 0 (Pos 0)) by lia.
  rewrite lit_var_c_denote. exact Hcohead.
Qed.

Lemma tagged_reason_side_seen__lit_removable :
  forall n F A_arr K M focus l minl base tags tagged v stack done p C,
    analysis_cancel_ready n F A_arr K M focus ->
    removable_dfs_loop_inv n M l minl base tags tagged (v :: stack) done ->
    removable_reason_focus n M v p C ->
    is_tag p = true ->
    In (lit_var_c (tag_lit p)) tagged ->
    forall q, In q C -> literal_var q <> v ->
      level_of (msolver_view n M) (literal_var q) = Some 0 \/
      In (literal_var q) base \/
      In (literal_var q) (v :: done) \/ In (literal_var q) stack.
Proof.
  intros n F A_arr K M focus l minl base tags tagged v stack done p C
    Hready Hinv Hfocus Htag Hseen q Hq Hneq.
  pose proof Hfocus as Hfocus_bounds.
  unfold removable_reason_focus, reason_target_wf in Hfocus_bounds.
  destruct Hfocus_bounds as [Hv _].
  pose proof (tagged_reason_clause_shape__lit_removable
    n F A_arr K M focus v p C Hready Hfocus Htag) as Hshape.
  rewrite Hshape in Hq. simpl in Hq.
  destruct Hq as [Hq | [Hq | []]].
  - subst q. rewrite lit_var_c_denote,
      (trail_lit_of_var (ms_core M) v) in Hneq by lia.
    contradiction.
  - subst q. rewrite literal_var_neg, lit_var_c_denote.
    destruct (removable_dfs_tagged_member_partition__lit_removable
      n M l minl base tags tagged (v :: stack) done
      (lit_var_c (tag_lit p)) Hinv Hseen) as [Hb | [Hd | Hstk]].
    + right. left. exact Hb.
    + right. right. left. right. exact Hd.
    + destruct Hstk as [Heq | Hstk].
      * right. right. left. left. exact Heq.
      * right. right. right. exact Hstk.
Qed.

Lemma tagged_reason_side_level_word_zero__lit_removable :
  forall n F A_arr K M focus v p C x,
    analysis_cancel_ready n F A_arr K M focus ->
    removable_reason_focus n M v p C ->
    is_tag p = true ->
    x = lit_var_c (tag_lit p) ->
    Znth x (mt_levels (ms_core M)) 0 = 0 ->
    forall q, In q C -> literal_var q <> v ->
      level_of (msolver_view n M) (literal_var q) = Some 0.
Proof.
  intros n F A_arr K M focus v p C x
    Hready Hfocus Htag Hx Hzero q Hq Hneq.
  pose proof Hfocus as Hfocus_bounds.
  unfold removable_reason_focus, reason_target_wf in Hfocus_bounds.
  destruct Hfocus_bounds as [Hv _].
  pose proof (tagged_reason_clause_shape__lit_removable
    n F A_arr K M focus v p C Hready Hfocus Htag) as Hshape.
  rewrite Hshape in Hq. simpl in Hq.
  destruct Hq as [Hq | [Hq | []]].
  - subst q. rewrite lit_var_c_denote,
      (trail_lit_of_var (ms_core M) v) in Hneq by lia.
    contradiction.
  - subst q.
    eapply removable_reason_side_level_word_zero__lit_removable
      with (v := v) (p := p) (C := C).
    + exact Hready.
    + exact Hfocus.
    + rewrite Hshape. simpl. tauto.
    + exact Hneq.
    + rewrite literal_var_neg, lit_var_c_denote, <- Hx. exact Hzero.
Qed.

Lemma removable_reason_scan_finish__lit_removable :
  forall n M l minl base done stack tags tagged C v p i,
    removable_reason_scan_inv n M l minl base done stack
      tags tagged C v p i ->
    i = Zlength C ->
    literal_var (Znth 0 C (Pos 0)) = v ->
    removable_dfs_loop_inv n M l minl base tags tagged stack (v :: done).
Proof.
  intros n M l minl base done stack tags tagged C v p i
    Hscan Hlen Hhead.
  unfold removable_reason_scan_inv in Hscan.
  destruct Hscan as [Hloop [Hfocus [[Hi Hilen] [Hwf Hfront]]]].
  assert (Hr : reason_of (msolver_view n M) v = Some C).
  { pose proof Hloop as Hloop_copy.
    unfold removable_dfs_loop_inv in Hloop_copy.
    destruct Hloop_copy as (fresh & Htagged & Hexact & Hfresh & Hnodup & Hpart & Hloop_copy).
    destruct Hloop_copy as [Hassigned Hrest].
    assert (Hvin : In v (lit_var_c l :: fresh)).
    { eapply Permutation_in; [exact Hpart |].
      apply in_or_app. right. left. reflexivity. }
    destruct (Hassigned v Hvin) as
      [d [r [Hvlevel [Hvrank Hvbelow]]]].
    unfold removable_reason_focus, reason_target_wf in Hfocus.
    destruct Hfocus as [_ [_ [_ [Hreason _]]]].
    unfold msolver_view, view_of. cbn [reason_of].
    unfold msolver_view, view_of in Hvrank.
    cbn [assignment_rank] in Hvrank.
    rewrite Hvrank. exact Hreason. }
  eapply removable_dfs_loop_inv_finish_head__lit_removable
    with (C := C).
  - exact Hloop.
  - exact Hr.
  - intros q Hq Hneq.
    destruct (In_Znth_ex literal C (Pos 0) q Hq)
      as [k [Hk Hqval]].
    destruct (Z.eq_dec k 0) as [-> | Hk0].
    + exfalso. apply Hneq. rewrite <- Hqval. exact Hhead.
    + specialize (Hfront k ltac:(lia)).
      rewrite Hqval in Hfront.
      destruct Hfront as [Hlevel | [Hbase | [Hdone | Hstack]]].
      * left. exact Hlevel.
      * right. left. exact Hbase.
      * right. right. left. simpl. right. exact Hdone.
      * right. right. right. exact Hstack.
Qed.

Lemma list_snoc_permutation :
  forall (l : list Z) (x : Z),
    Permutation (List.app l (x :: nil)) (x :: l).
Proof.
  intros l x. induction l as [|a l IH].
  - simpl. apply Permutation_refl.
  - simpl. eapply Permutation_trans.
    + apply perm_skip. exact IH.
    + apply perm_swap.
Qed.

(** ** Cancel algebra.
    Facts preserved by [analysis_cancel_ready] in both propagation contexts. *)

Lemma analysis_cancel_ready_db_wf__lit_removable :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    db_wf n (msolver_db M).
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (asc_db_wf _ _ _ Hctx).
Qed.

Lemma analysis_cancel_ready_db_binary__lit_removable :
  forall n F A_arr K M focus,
  analysis_cancel_ready n F A_arr K M focus ->
  db_wf n (msolver_db M) /\
  ~ In (ms_binary M) (map fst (msolver_db M)).
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (conj (asc_db_wf _ _ _ Hctx) (asc_binary_out _ _ _ Hctx)).
Qed.

Lemma analysis_cancel_ready_reason_target__lit_removable :
  forall n F A_arr K M focus v,
  analysis_cancel_ready n F A_arr K M focus ->
  0 <= v < n ->
  Znth v (ms_reason_words M) 0 <> 0 ->
  exists C,
    reason_target_wf n M v (Znth v (ms_reason_words M) 0) C.
Proof.
  intros n F A_arr K M focus v Hready Hv Hnonzero.
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K M focus Hready) as [Hsize [Hmatch Hbinary]].
  destruct (analysis_cancel_ready_db_binary__lit_removable
    n F A_arr K M focus Hready) as [_ Hbinary_out].
  set (p := Znth v (ms_reason_words M) 0) in *.
  assert (HvM : 0 <= v < ms_size M) by lia.
  assert (Hp0 : (p =? 0) = false) by
    (apply Z.eqb_neq; exact Hnonzero).
  specialize (Hmatch v Hv).
  change (reason_word_ok (ms_core M) v (msolver_db M) p
    (ms_reason_of M v)) in Hmatch.
  unfold reason_word_ok in Hmatch. rewrite Hp0 in Hmatch.
  destruct (is_tag p) eqn:Htag.
  - destruct (Hbinary v HvM Htag) as [Hwf _].
    change (lit_wf_c (ms_size M) (tag_lit p)) in Hwf.
    rewrite <- Hsize in Hwf.
    destruct Hmatch as [_ Hreason].
    exists [lit_denote (trail_lit_of (ms_core M) v);
            literal_neg (lit_denote (tag_lit p))].
    unfold reason_target_wf.
    split; [exact HvM |].
    split; [reflexivity |].
    split; [exact Hnonzero |].
    split; [exact Hreason |].
    left. split; [exact Htag |].
    split.
    + eapply tag_pos_of_lit_wf; eassumption.
    + exact Hwf.
  - destruct Hmatch as [_ [co [Hin Hreason]]].
    assert (Hnotbinary : p <> ms_binary M).
    { intro Heq.
      pose proof (in_map fst (msolver_db M) (p, co) Hin) as Hmap.
      cbn in Hmap. apply Hbinary_out. rewrite <- Heq. exact Hmap. }
    exists (denote_obj co).
    unfold reason_target_wf.
    split; [exact HvM |].
    split; [reflexivity |].
    split; [exact Hnonzero |].
    split; [exact Hreason |].
    right. exists co.
    split; [exact Htag |].
    split; [exact Hnotbinary |].
    split; [exact Hin | reflexivity].
Qed.

Lemma analysis_tags_exact_untagged_strict__lit_removable :
  forall n tags tagged v,
  analysis_tags_exact n tags tagged ->
  0 <= v < n ->
  Znth v tags 0 = 0 ->
  Zlength tagged < n.
Proof.
  intros n tags tagged v
    [Htags_len [Hnodup [Hrange [Hbits Hexact]]]] Hv Hzero.
  assert (Hnotin : ~ In v tagged).
  { intro Hin.
    pose proof (proj2 (Hexact v Hv) Hin) as Hone.
    lia. }
  assert (Hcons_nodup : NoDup (v :: tagged)).
  { constructor; assumption. }
  assert (Hbounded : forall x, In x (v :: tagged) -> 0 <= x < n).
  { intros x [-> | Hin]; [exact Hv |].
    rewrite Forall_forall in Hrange. exact (Hrange x Hin). }
  pose proof (NoDup_Z_bounded_length (v :: tagged) n ltac:(lia)
    Hcons_nodup Hbounded) as Hlen.
  rewrite Zlength_correct. simpl in Hlen. lia.
Qed.

Lemma removable_dfs_last_reason__lit_removable :
  forall n M l minl base tags tagged stack done,
  removable_dfs_loop_inv n M l minl base tags tagged stack done ->
  0 < Zlength stack ->
  exists C,
    reason_target_wf n M (Znth (Zlength stack - 1) stack 0)
      (Znth (Znth (Zlength stack - 1) stack 0)
        (ms_reason_words M) 0) C.
Proof.
  intros n M l minl base tags tagged stack done Hinv Hlen.
  destruct Hinv as
    [fresh [_ [_ [_ [_ [_ [_ [Htargets _]]]]]]]].
  assert (Hin : In (Znth (Zlength stack - 1) stack 0) stack).
  { apply Znth_In. lia. }
  destruct (Htargets _ Hin) as [p [C Htarget]].
  unfold reason_target_wf in Htarget.
  destruct Htarget as [Hv [Hp Hrest]]. subst p.
  exists C. unfold reason_target_wf. tauto.
Qed.

Lemma list_last_sublist__lit_removable :
  forall (xs : list Z) v,
  0 < Zlength xs ->
  v = Znth (Zlength xs - 1) xs 0 ->
  xs = sublist 0 (Zlength xs - 1) xs ++ [v].
Proof.
  intros xs v Hlen Hv.
  pose proof (sublist_split 0 (Zlength xs) (Zlength xs - 1) xs
    ltac:(lia) ltac:(lia)) as Hsplit.
  rewrite (sublist_self xs (Zlength xs) eq_refl) in Hsplit.
  assert (Htail :
    sublist (Zlength xs - 1) (Zlength xs) xs =
      [Znth (Zlength xs - 1) xs 0]).
  { pose proof (sublist_single 0 (Zlength xs - 1) xs ltac:(lia))
      as Hsingle.
    replace (Zlength xs - 1 + 1) with (Zlength xs) in Hsingle by lia.
    exact Hsingle. }
  rewrite Htail in Hsplit.
  rewrite Hv. exact Hsplit.
Qed.

Lemma ptrarray_missing_i_index_range__lit_removable :
  forall x i lo hi (words : list Z),
  PtrArray.missing_i x i lo hi words |-- “ lo <= i < hi ”.
Proof.
  intros x i lo hi words. revert i lo hi.
  induction words as [|word words IH]; intros i lo hi.
  - sep_apply_l_atomic (PtrArray.missing_i_empty x i lo hi). apply coq_prop_False_left. tauto.
  - sep_apply_l_atomic (PtrArray.missing_i_unfold x i lo hi words word). Split.
    + Intros_p Heq. subst i.
      prop_apply_p (PtrArray.seg_valid x (lo + 1) hi words). Intros_p Hle.
      dump_pre_spatial. lia.
    + Intros_p Hgt. prop_apply_p (IH i (lo + 1) hi). Intros_p Hr.
      dump_pre_spatial. lia.
Qed.

Lemma clause_db_pair_remainder_ptr_wf__lit_removable :
  forall n prob learnt c is_learnt words,
  db_wf n (prob ++ learnt) ->
  clause_db_pair_remainder prob learnt c is_learnt words
  |-- “ 0 < c /\ c mod 2 = 0 ”.
Proof.
  intros n prob learnt c is_learnt words Hdb.
  unfold clause_db_pair_remainder. Split.
  - Intros co pre post.
    match goal with
    | Hfocus : prob = _ /\ _ |- _ => destruct Hfocus as [Hprob _]
    end.
    assert (Hin : In (c, co) (prob ++ learnt)).
    { rewrite Hprob. apply in_or_app. left.
      apply in_or_app. right. simpl. auto. }
    pose proof (db_wf_ptr_pos n (prob ++ learnt) c co Hdb Hin) as Hpos.
    pose proof (db_wf_even n (prob ++ learnt) c co Hdb Hin) as Heven.
    apply clause_ptr_mod2 in Heven. (Intros; split_pures; dump_pre_spatial; solve [auto | (lia)]).
  - Intros co pre post.
    match goal with
    | Hfocus : learnt = _ /\ _ |- _ => destruct Hfocus as [Hlearnt _]
    end.
    assert (Hin : In (c, co) (prob ++ learnt)).
    { rewrite Hlearnt. apply in_or_app. right.
      apply in_or_app. right. simpl. auto. }
    pose proof (db_wf_ptr_pos n (prob ++ learnt) c co Hdb Hin) as Hpos.
    pose proof (db_wf_even n (prob ++ learnt) c co Hdb Hin) as Heven.
    apply clause_ptr_mod2 in Heven. msat_entailer_with lia.
Qed.

Lemma removable_reason_focus_tag_range__lit_removable :
  forall n M v p C,
  removable_reason_focus n M v p C ->
  is_tag p = true ->
  0 <= lit_var_c (tag_lit p) < n.
Proof.
  intros n M v p C Hfocus Htag.
  unfold removable_reason_focus, reason_target_wf in Hfocus.
  destruct Hfocus as [_ [_ [_ [_ [Htagged | Hreal]]]]].
  - destruct Htagged as [_ [_ Hwf]].
    exact (lit_var_c_in_range n (tag_lit p) Hwf).
  - destruct Hreal as [co [Hfalse _]]. congruence.
Qed.


Lemma removable_scan_stack_strict__lit_removable :
  forall n M l minl base done stack tags tagged C v p i,
  removable_reason_scan_inv n M l minl base done stack tags tagged C v p i ->
  n = ms_size M ->
  Zlength stack < n.
Proof.
  intros n M l minl base done stack tags tagged C v p i Hscan Hsize.
  unfold removable_reason_scan_inv in Hscan.
  destruct Hscan as [Hdfs _].
  unfold removable_dfs_loop_inv in Hdfs.
  destruct Hdfs as [fresh Hdfs].
  assert (Hnodup : NoDup (done ++ (v :: stack))) by tauto.
  assert (Htargets : forall x, In x (v :: stack) -> exists p0 C0,
    reason_target_wf n M x p0 C0) by tauto.
  assert (Hnodup_tail : NoDup (v :: stack)).
  { eapply NoDup_app_remove_l. exact Hnodup. }
  assert (Hbounded : forall x, In x (v :: stack) -> 0 <= x < n).
  { intros x Hin.
    destruct (Htargets x Hin) as [p0 [C0 Htarget]].
    unfold reason_target_wf in Htarget.
    rewrite Hsize. tauto. }
  assert (Hn : 0 <= n).
  { pose proof (Hbounded v (or_introl eq_refl)). lia. }
  pose proof (NoDup_Z_bounded_length (v :: stack) n Hn
    Hnodup_tail Hbounded) as Hlen.
  cbn in Hlen. rewrite Zlength_correct. lia.
Qed.

Lemma clause_db_pair_focus_from_member__lit_removable :
  forall prob learnt p co,
  In (p, co) (prob ++ learnt) ->
  clause_db_rep prob ** clause_db_rep learnt |--
  MiniSatClause.rep p (co_learnt co) (co_lits co) **
  clause_db_pair_remainder prob learnt p (co_learnt co) (co_lits co).
Proof.
  intros prob learnt p co Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - apply in_split in Hin. destruct Hin as [pre [post Hprob]].
    subst prob.
    sep_apply (clause_db_rep_app_elim pre ((p, co) :: post)).
    rewrite clause_db_rep_cons.
    unfold clause_db_pair_remainder.
    Left. Exists co pre post. cbn [fst snd].
    split_pure_spatial.
    + cancel (MiniSatClause.rep p (co_learnt co) (co_lits co)).
      cancel (clause_db_rep pre).
      cancel (clause_db_rep post).
      cancel (clause_db_rep learnt).
    + dump_pre_spatial. repeat split.
  - apply in_split in Hin. destruct Hin as [pre [post Hlearnt]].
    subst learnt.
    sep_apply (clause_db_rep_app_elim pre ((p, co) :: post)).
    rewrite clause_db_rep_cons.
    unfold clause_db_pair_remainder.
    Right. Exists co pre post. cbn [fst snd].
    split_pure_spatial.
    + cancel (MiniSatClause.rep p (co_learnt co) (co_lits co)).
      cancel (clause_db_rep pre).
      cancel (clause_db_rep post).
      cancel (clause_db_rep prob).
    + dump_pre_spatial. repeat split.
Qed.

(** ===== group: solver_analyze ===== *)
Lemma analyze_inv_rank_partition_unique__analyze :
  forall F a S R learnt S' R' learnt',
    analyze_inv F a S R learnt ->
    analyze_inv F a S' R' learnt' ->
    Permutation (analyze_tags S R learnt)
                (analyze_tags S' R' learnt') ->
    Zlength S = Zlength S' ->
    forall y, In y S <-> In y S'.
Proof.
  intros F a S R learnt S' R' learnt' Hinv Hinv' Hperm Hlen.
  assert (Hforward :
    forall S1 R1 learnt1 S2 R2 learnt2,
      analyze_inv F a S1 R1 learnt1 ->
      analyze_inv F a S2 R2 learnt2 ->
      Permutation (analyze_tags S1 R1 learnt1)
                  (analyze_tags S2 R2 learnt2) ->
      Zlength S1 = Zlength S2 ->
      forall y, In y S1 -> In y S2).
  {
    intros S1 R1 learnt1 S2 R2 learnt2
      Hinv1 Hinv2 Hperm12 Hlen12 y HyS1.
    destruct Hinv1 as
      (_ & Hnd1 & HlevS1 & _ & _ & HrankR1 & HlevL1 & _).
    destruct Hinv2 as
      (_ & Hnd2 & HlevS2 & _ & _ & HrankR2 & HlevL2 & _).
    assert (HyAll2 : In y (analyze_tags S2 R2 learnt2)).
    {
      eapply Permutation_in; [exact Hperm12 |].
      unfold analyze_tags. rewrite !in_app_iff. tauto.
    }
    unfold analyze_tags in HyAll2.
    rewrite !in_app_iff in HyAll2.
    destruct HyAll2 as [HyS2 | [HyR2 | HyL2]].
    - exact HyS2.
    - assert (HyNotS2 : ~ In y S2).
      {
        intro HyS2.
        unfold analyze_tags in Hnd2.
        pose proof
          (NoDup_app_disjoint S2 (R2 ++ map literal_var learnt2) y
             Hnd2 HyS2) as Hdis.
        apply Hdis. rewrite in_app_iff. tauto.
      }
      assert (Hdec : forall z : Z, {~ In z S1} + {~ ~ In z S1}).
      {
        intro z.
        destruct (in_dec Z.eq_dec z S1) as [Hz | Hz];
          [right; tauto | left; exact Hz].
      }
      destruct (Exists_dec (fun z => ~ In z S1) S2 Hdec) as [Hex | Hnoz0].
      + apply Exists_exists in Hex.
        destruct Hex as [z [HzS2 HzNotS1]].
        assert (HzAll1 : In z (analyze_tags S1 R1 learnt1)).
        {
          eapply Permutation_in; [apply Permutation_sym; exact Hperm12 |].
          unfold analyze_tags. rewrite !in_app_iff. tauto.
        }
        unfold analyze_tags in HzAll1.
        rewrite !in_app_iff in HzAll1.
        destruct HzAll1 as [HzS1 | [HzR1 | HzL1]].
        * contradiction.
        * rewrite Forall_forall in HrankR1, HrankR2.
          specialize (HrankR1 z HzR1 y HyS1).
          specialize (HrankR2 y HyR2 z HzS2).
          unfold rank_lt in HrankR1, HrankR2.
          destruct HrankR1 as
            [ry [rz [Hranky [Hrankz Hlt_yz]]]].
          destruct HrankR2 as
            [rz' [ry' [Hrankz' [Hranky' Hlt_zy]]]].
          rewrite Hranky in Hranky'. injection Hranky' as ->.
          rewrite Hrankz in Hrankz'. injection Hrankz' as ->.
          lia.
        * rewrite Forall_forall in HlevS2, HlevL1.
          specialize (HlevS2 z HzS2).
          rewrite in_map_iff in HzL1.
          destruct HzL1 as [l [HzEq HzIn]].
          destruct (HlevL1 l HzIn) as [d [Hlevel Hd]].
          rewrite HzEq in Hlevel. rewrite HlevS2 in Hlevel.
          injection Hlevel as Hdeq. lia.
      + assert (Hnoz : ~ (exists z, In z S2 /\ ~ In z S1)).
        {
          intro Hex0. apply Hnoz0. apply Exists_exists.
          destruct Hex0 as [z [HzS2 HzNotS1]]. exists z. tauto.
        }
        assert (Hincl : incl S2 S1).
        {
          intros z HzS2.
          destruct (in_dec Z.eq_dec z S1) as [HzS1 | HzNotS1]; [exact HzS1 |].
          exfalso. apply Hnoz. exists z. tauto.
        }
        destruct (in_split y S1 HyS1) as [before [after HS1]].
        assert (Hincl_remove : incl S2 (before ++ after)).
        {
          intros z HzS2.
          specialize (Hincl z HzS2).
          rewrite HS1 in Hincl.
          rewrite in_app_iff in Hincl. simpl in Hincl.
          rewrite in_app_iff.
          destruct Hincl as [HzBefore | [HzEq | HzAfter]].
          - tauto.
          - subst z. contradiction.
          - tauto.
        }
        assert (HndS2 : NoDup S2).
        {
          unfold analyze_tags in Hnd2.
          eapply NoDup_app_remove_r. exact Hnd2.
        }
        pose proof (NoDup_incl_length HndS2 Hincl_remove) as Hlength.
        rewrite !Zlength_correct in Hlen12.
        apply Nat2Z.inj in Hlen12.
        rewrite HS1, !length_app in Hlen12. simpl in Hlen12.
        rewrite length_app in Hlength.
        lia.
    - rewrite Forall_forall in HlevS1, HlevL2.
      specialize (HlevS1 y HyS1).
      rewrite in_map_iff in HyL2.
      destruct HyL2 as [l [HyEq HyIn]].
      destruct (HlevL2 l HyIn) as [d [Hlevel Hd]].
      rewrite HyEq in Hlevel. rewrite HlevS1 in Hlevel.
      injection Hlevel as Hdeq. lia.
  }
  intro y. split.
  - eapply Hforward; eauto.
  - eapply Hforward; eauto using Permutation_sym.
Qed.

Lemma analysis_cancel_ready_trail_wf__analyze :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    mtrail_wf n (ms_core M).
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (asc_trail_wf _ _ _ Hctx).
Qed.

Lemma analyze_minimize_init__analyze :
  forall n M original,
    1 <= Zlength original ->
    Forall (lit_wf_c n) original ->
    analysis_tags_exact n (ms_tags M) (ms_tagged M) ->
    minimize_tag_scope n M original nil ->
    analyze_minimize_loop_inv n M original
      (sublist 0 1 original) nil original nil 1 1.
Proof.
  intros n M original Hlen Hwf Htags Hscope.
  assert (Hsingle : sublist 0 1 original = Znth 0 original 0 :: nil).
  { apply sublist_single. lia. }
  assert (Hparts :
    sublist 0 1 original ++ sublist 1 (Zlength original) original = original).
  { rewrite <- (sublist_split 0 (Zlength original) 1 original) by lia.
    apply sublist_self. reflexivity. }
  assert (Htail : tl original = sublist 1 (Zlength original) original).
  { rewrite Hsingle in Hparts. cbn in Hparts.
    apply (f_equal (@tl Z)) in Hparts. cbn in Hparts.
    symmetry. exact Hparts. }
  unfold analyze_minimize_loop_inv.
  repeat match goal with |- _ /\ _ => split end.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - exact Hwf.
  - exact Hwf.
  - rewrite Hsingle. reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Htags.
  - cbn [app]. rewrite Hsingle. cbn [tl lits_denote].
    rewrite Htail. apply Permutation_refl.
  - intros x Hx. contradiction.
  - rewrite Hparts. exact Hscope.
  - constructor.
  - intros x Hx. contradiction.
  - rewrite Hsingle. reflexivity.
Qed.

Lemma msolver_view_level_in_trail__analyze :
  forall n M x d,
    level_of (msolver_view n M) x = Some d ->
    In x (map lit_var_c (mt_trail (ms_core M))).
Proof.
  intros n M x d Hlevel.
  unfold msolver_view, view_of in Hlevel; cbn in Hlevel.
  destruct (trail_pos (ms_core M) x) as [r|] eqn:Hpos;
    cbn in Hlevel; try discriminate.
  destruct (in_dec Z.eq_dec x
    (map lit_var_c (mt_trail (ms_core M)))) as [Hin | Hnot];
    [exact Hin |].
  pose proof (proj2 (trail_pos_none_iff (ms_core M) x) Hnot) as Hnone.
  rewrite Hnone in Hpos. discriminate.
Qed.

Lemma analyze_clause_cert_vars_in_trail__analyze :
  forall n F M words,
    analyze_clause_cert n F M words ->
    incl (map lit_var_c words)
      (map lit_var_c (mt_trail (ms_core M))).
Proof.
  intros n F M words [Huip Hroot] x Hx.
  rewrite <- map_literal_var_lits_denote in Hx.
  apply in_map_iff in Hx.
  destruct Hx as [l [Hxl Hl]]. subst x.
  destruct Huip as [Hsound [Hnodup [h [rest [Heq [Hhead Htail]]]]]].
  rewrite Heq in Hl. destruct Hl as [Hl | Hl].
  - subst l. eapply msolver_view_level_in_trail__analyze.
    exact Hhead.
  - rewrite Forall_forall in Htail.
    destruct (Htail l Hl) as [d [Hlevel Hd]].
    eapply msolver_view_level_in_trail__analyze.
    exact Hlevel.
Qed.

Lemma analysis_core_equiv_view__analyze :
  forall n M M', analysis_core_equiv M M' ->
    msolver_view n M' = msolver_view n M.
Proof.
  intros n M M' Hequiv.
  unfold analysis_core_equiv in Hequiv.
  unfold msolver_view, view_of, msolver_clauses, msolver_db.
  destruct Hequiv as
    [_ [_ [_ [Ecore [_ [_ [Ereason [Eprob [Elearnt _]]]]]]]]].
  rewrite Ecore, Ereason, Eprob, Elearnt. reflexivity.
Qed.

Lemma removable_witness_union_rebase_below__analyze :
  forall (a : cdcl_view) S1 S2 S T1 T2,
    grounded_at a ->
    removable_witness a S1 T1 ->
    removable_witness a S2 T2 ->
    (forall x, In x T2 -> assigned_below_current a x) ->
    (forall x, In x T2 -> exists b, assignment a x = Some b) ->
    (forall y, In y S1 -> In y S \/ In y (T1 ++ T2)) ->
    (forall y, In y S2 ->
       level_of a y = Some (current_level a) \/
       In y S \/ In y (T1 ++ T2)) ->
    removable_witness a S (T1 ++ T2).
Proof.
  intros a S1 S2 S T1 T2 Hground Hwit1 Hwit2 Hbelow Hassign
    Hbase1 Hbase2 x Hx.
  apply in_app_or in Hx. destruct Hx as [Hx1|Hx2].
  - destruct (Hwit1 x Hx1) as [c [Hr Hc]].
    exists c. split; [exact Hr|].
    intros l Hl Hne.
    destruct (Hc l Hl Hne) as [Hz|[HS1|HT1]].
    + left. exact Hz.
    + destruct (Hbase1 _ HS1) as [HS|HT].
      * right; left; exact HS.
      * right; right; exact HT.
    + right; right. apply in_or_app. left. exact HT1.
  - destruct (Hwit2 x Hx2) as [c [Hr Hc]].
    destruct (Hbelow x Hx2) as [d [r [Hlevx [Hrankx Hd]]]].
    destruct (Hassign x Hx2) as [b Hass].
    destruct (Hground x b Hass) as [d' [r' [Hlevx' [Hrankx' Horigin]]]].
    destruct Horigin as [Hnone | [c' [Hr' Hvalid]]].
    { rewrite Hnone in Hr. discriminate. }
    assert (Ec : c' = c) by congruence. subst c'.
    exists c. split; [exact Hr|].
    intros l Hl Hne.
    destruct (Hc l Hl Hne) as [Hz|[HS2|HT2]].
    + left. exact Hz.
    + destruct (Hbase2 _ HS2) as [Hcur|[HS|HT]].
      * destruct Hvalid as
          [bx [dx [rx [Hassx [Hlx [Hrx [Hsat Hside]]]]]]].
        assert (Ed : dx = d) by congruence. subst dx.
        destruct (Hside l Hl Hne) as
          [Hfalse [dy [ry [Hly [Hry [Hyd Hrr]]]]]].
        rewrite Hcur in Hly. inversion Hly. lia.
      * right; left; exact HS.
      * right; right; exact HT.
    + right; right. apply in_or_app. right. exact HT2.
Qed.

Lemma analysis_core_equiv_trans__analyze :
  forall M0 M1 M2,
    analysis_core_equiv M0 M1 -> analysis_core_equiv M1 M2 ->
    analysis_core_equiv M0 M2.
Proof.
  intros M0 M1 M2 H01 H12.
  unfold analysis_core_equiv in *.
  intuition congruence.
Qed.

Lemma analyze_clause_cert_transport__analyze :
  forall n F M M' words,
    analysis_core_equiv M M' ->
    analyze_clause_cert n F M words ->
    analyze_clause_cert n F M' words.
Proof.
  intros n F M M' words Hequiv [Huip [Hroot Hpositive]].
  split.
  - rewrite (analysis_core_equiv_view__analyze n M M' Hequiv).
    exact Huip.
  - split.
    + unfold analysis_core_equiv in Hequiv. intuition congruence.
    + unfold learned_tail_positive in *.
      rewrite (analysis_core_equiv_view__analyze n M M' Hequiv).
      exact Hpositive.
Qed.

Lemma solver_rep_analyze_at_shape__analyze :
  forall s M rsn lvl trl tgs wl,
    solver_rep_analyze_at s M rsn lvl trl tgs wl |--
      “ solver_shape M ” && solver_rep_analyze_at s M rsn lvl trl tgs wl.
Proof.
  intros s M rsn lvl trl tgs wl.
  unfold solver_rep_analyze_at, solver_rep_at.
  Intros act asg opos.
  Exists act asg opos. msat_entailer_with lia.
Qed.

Lemma analysis_cancel_ready_grounded__analyze :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    grounded_at (msolver_view n M).
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (proj1 (asc_stable _ _ _ Hctx)).
Qed.

Lemma analysis_cancel_ready_weak_facts__analyze :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    grounded_at (msolver_view n M) /\
    reasons_entailed F (msolver_view n M) /\
    reasons_var_injective (msolver_view n M) /\
    mtrail_wf n (ms_core M) /\
    db_wf n (msolver_db M) /\
    ~ In (ms_binary M) (map fst (msolver_db M)) /\
    trail_implied F (ms_core M).
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (conj (proj1 (asc_stable _ _ _ Hctx))
    (conj (asc_reasons_ent _ _ _ Hctx) (conj (asc_reasons_inj _ _ _ Hctx)
      (conj (asc_trail_wf _ _ _ Hctx) (conj (asc_db_wf _ _ _ Hctx)
        (conj (asc_binary_out _ _ _ Hctx) (asc_trail_impl _ _ _ Hctx))))))).
Qed.

Lemma literal_wf_neg__analyze :
  forall n l, literal_wf n l -> literal_wf n (literal_neg l).
Proof. intros n [x|x] H; exact H. Qed.

Lemma analysis_cancel_ready_reason_bundle__analyze :
  forall n F A_arr K M focus v r,
    analysis_cancel_ready n F A_arr K M focus ->
    0 <= v < n ->
    assignment_rank (msolver_view n M) v = Some r ->
    Znth v (ms_reason_words M) 0 <> 0 ->
    exists C,
      reason_target_wf n M v (Znth v (ms_reason_words M) 0) C /\
      analysis_clause_focus n M (Znth v (ms_reason_words M) 0) C /\
      reason_valid (msolver_view n M) v C /\
      entails_clause F C /\
      Forall (literal_wf n) C /\
      NoDup (map literal_var C).
Proof.
  intros n F A_arr K M focus v r Hready Hv Hrank Hnonzero.
  destruct (analysis_cancel_ready_weak_facts__analyze
    n F A_arr K M focus Hready) as
    [Hground [Hent [Hinj [Htrailwf [Hdbwf [Hbinaryout Htrailimpl]]]]]].
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K M focus Hready) as [Hsize [Hmatch Hbinary]].
  assert (HvM : 0 <= v < ms_size M) by lia.
  assert (Hreason_valid : forall C, ms_reason_of M v = Some C ->
      reason_valid (msolver_view n M) v C /\ entails_clause F C).
  { intros C HC.
    destruct (assignment_of_rank__lit_removable
      n M v r Htrailwf Hrank) as [b Hass].
    destruct (Hground v b Hass) as [d [r' [Hlev [Hrank' Horigin]]]].
    destruct Horigin as [Hnone | [C' [HC' Hvalid]]].
    { change ((match trail_pos (ms_core M) v with
                | Some _ => ms_reason_of M v
                | None => None
                end) = None) in Hnone.
      change (trail_pos (ms_core M) v = Some r) in Hrank.
      rewrite Hrank in Hnone.
      rewrite Hnone in HC. discriminate. }
    change ((match trail_pos (ms_core M) v with
              | Some _ => ms_reason_of M v
              | None => None
              end) = Some C') in HC'.
    change (trail_pos (ms_core M) v = Some r) in Hrank.
    rewrite Hrank in HC'.
    assert (EC : C' = C) by congruence. subst C'.
    split; [exact Hvalid|].
    apply (Hent v C).
    change ((match trail_pos (ms_core M) v with
              | Some _ => ms_reason_of M v
              | None => None
              end) = Some C).
    rewrite Hrank. exact HC. }
  pose proof (Hmatch v Hv) as Hrw.
  unfold reason_word_ok in Hrw.
  destruct ((Znth v (ms_reason_words M) 0 =? 0)%Z) eqn:Ezero.
  { apply Z.eqb_eq in Ezero. contradiction. }
  destruct (is_tag (Znth v (ms_reason_words M) 0)) eqn:Htag.
  - destruct Hrw as [Hassigned Ereason].
    set (C := lit_denote (trail_lit_of (ms_core M) v) ::
               literal_neg (lit_denote
                 (tag_lit (Znth v (ms_reason_words M) 0))) :: nil).
    assert (HC : ms_reason_of M v = Some C) by (subst C; exact Ereason).
    assert (Htarget : reason_target_wf n M v
      (Znth v (ms_reason_words M) 0) C).
    { unfold reason_target_wf.
      split; [exact HvM|].
      split; [reflexivity|].
      split; [exact Hnonzero|].
      split; [exact HC|].
      left.
      destruct (Hbinary v HvM Htag) as [Hwf _].
      split; [exact Htag|].
      split; [eapply tag_pos_of_lit_wf; eauto|].
      rewrite Hsize. exact Hwf. }
    assert (Hfocus : analysis_clause_focus n M
      (Znth v (ms_reason_words M) 0) C).
    { right; left. exists v. split; assumption. }
    destruct (Hreason_valid C HC) as [Hvalid HentC].
    exists C.
    split; [exact Htarget|].
    split; [exact Hfocus|].
    split; [exact Hvalid|].
    split.
    + exact HentC.
    + split.
      * subst C. constructor.
        -- apply lit_denote_wf. apply trail_lit_of_wf. lia.
        -- constructor.
           ++ apply literal_wf_neg__analyze.
              apply lit_denote_wf.
              rewrite Hsize. exact (proj1 (Hbinary v HvM Htag)).
           ++ constructor.
      * eapply analysis_cancel_ready_tagged_reason_nodup; eauto.
  - destruct Hrw as [Hassigned [co [Hin Ereason]]].
    set (C := denote_obj co).
    assert (HC : ms_reason_of M v = Some C) by (subst C; exact Ereason).
    assert (Hneqbin : Znth v (ms_reason_words M) 0 <> ms_binary M).
    { intro E. apply Hbinaryout. rewrite <- E.
      unfold db_lookup in Hin.
      exact (in_map fst (msolver_db M)
        (Znth v (ms_reason_words M) 0, co) Hin). }
    assert (Htarget : reason_target_wf n M v
      (Znth v (ms_reason_words M) 0) C).
    { unfold reason_target_wf.
      split; [exact HvM|].
      split; [reflexivity|].
      split; [exact Hnonzero|].
      split; [exact HC|].
      right. exists co.
      split; [exact Htag|].
      split; [exact Hneqbin|].
      split; [exact Hin|].
      subst C. reflexivity. }
    assert (Hfocus : analysis_clause_focus n M
      (Znth v (ms_reason_words M) 0) C).
    { right; right. exists co.
      split; [exact Hneqbin|].
      split; [exact Htag|].
      split; [exact Hin|].
      subst C. reflexivity. }
    destruct (Hreason_valid C HC) as [Hvalid HentC].
    exists C.
    split; [exact Htarget|].
    split; [exact Hfocus|].
    split; [exact Hvalid|].
    split.
    + exact HentC.
    + split.
      * subst C. eapply db_clause_wf; eauto.
      * subst C. apply (obj_wf_nodup_vars n co). eapply db_wf_obj; eauto.
Qed.

Lemma analyze_minimize_remove__analyze :
  forall n F A_arr K focus M M' original kept removed words T i j fresh,
    analyze_minimize_loop_inv n M original kept removed words T i j ->
    0 <= i < Zlength words ->
    analysis_cancel_ready n F A_arr K M focus ->
    analysis_core_equiv M M' ->
    ms_tagged M' = ms_tagged M ++ fresh ->
    analysis_tags_exact n (ms_tags M') (ms_tagged M') ->
    removable_witness (msolver_view n M) (ms_tagged M)
      (lit_var_c (Znth i words 0) :: fresh) ->
    (forall x, In x (lit_var_c (Znth i words 0) :: fresh) ->
       assigned_below_current (msolver_view n M) x) ->
    analyze_minimize_loop_inv n M' original kept
      (removed ++ Znth i words 0 :: nil) words
      (T ++ lit_var_c (Znth i words 0) :: fresh) (i + 1) j.
Proof.
  intros n F A_arr K focus M M' original kept removed words T i j fresh
    Hinv Hi Hready Hequiv Etagged Htags' Hfresh Hbelow.
  pose proof (analysis_core_equiv_view__analyze n M M' Hequiv)
    as Eview.
  pose proof (analysis_cancel_ready_trail_wf__analyze
    n F A_arr K M focus Hready) as Htrailwf.
  pose proof (analysis_cancel_ready_grounded__analyze
    n F A_arr K M focus Hready) as Hground.
  unfold analyze_minimize_loop_inv in Hinv |- *.
  destruct Hinv as
    [Hj0 [Hji [Hiorig [Hlen [Hhead [Hwforig [Hwfwords
    [Hkept [Hremoved [Hsuffix [Htags [Hperm [Hwit [Hscope
    [HremIn [HTlev Hprefix]]]]]]]]]]]]]]]].
  assert (Hcur_suffix :
    Znth i words 0 = Znth i original 0 /\
    sublist (i + 1) (Zlength original) words =
      sublist (i + 1) (Zlength original) original).
  { assert (Ew := sublist_suffix_cons 0 words i Hi).
    assert (Eo := sublist_suffix_cons 0 original i ltac:(lia)).
    rewrite Hlen in Ew.
    rewrite Ew, Eo in Hsuffix.
    split.
    - exact (f_equal (@hd Z 0) Hsuffix).
    - exact (f_equal (@tl Z) Hsuffix). }
  destruct Hcur_suffix as [Hcur Hsuffix1].
  assert (Hpending : sublist i (Zlength original) original =
    Znth i words 0 :: sublist (i + 1) (Zlength original) original).
  { rewrite (sublist_suffix_cons 0 original i) by lia.
    rewrite Hcur. reflexivity. }
  assert (Hbase1 : forall y,
    In y (map lit_var_c (kept ++ sublist i (Zlength original) original)) ->
    In y (map lit_var_c
      (kept ++ sublist (i + 1) (Zlength original) original)) \/
    In y (T ++ lit_var_c (Znth i words 0) :: fresh)).
  { intros y Hy. rewrite Hpending, !map_app in Hy. rewrite !map_app.
    cbn in Hy |- *.
    apply in_app_or in Hy. destruct Hy as [Hk|[Hcury|Hp]].
    - left. apply in_or_app. left. exact Hk.
    - right. apply in_or_app. right. left. exact Hcury.
    - left. apply in_or_app. right. exact Hp. }
  assert (Hbase2 : forall y, In y (ms_tagged M) ->
    level_of (msolver_view n M) y =
      Some (current_level (msolver_view n M)) \/
    In y (map lit_var_c
      (kept ++ sublist (i + 1) (Zlength original) original)) \/
    In y (T ++ lit_var_c (Znth i words 0) :: fresh)).
  { intros y Hy. destruct (Hscope y Hy) as [Hlev|[Hb|HT]].
    - left. exact Hlev.
    - right. destruct (Hbase1 y Hb) as [Hnew|HTnew]; tauto.
    - right; right. apply in_or_app. left. exact HT. }
  assert (Hassign : forall x,
    In x (lit_var_c (Znth i words 0) :: fresh) ->
    exists b, assignment (msolver_view n M) x = Some b).
  { intros x Hx. destruct (Hbelow x Hx) as [d [r [Hlev [Hrank Hd]]]].
    eapply assignment_of_rank__lit_removable; eauto. }
  assert (Hwit' : removable_witness (msolver_view n M)
    (map lit_var_c
      (kept ++ sublist (i + 1) (Zlength original) original))
    (T ++ lit_var_c (Znth i words 0) :: fresh)).
  { eapply removable_witness_union_rebase_below__analyze
      with (S1 := map lit_var_c
        (kept ++ sublist i (Zlength original) original))
           (S2 := ms_tagged M); eauto. }
  repeat match goal with |- _ /\ _ => split end.
  - exact Hj0.
  - lia.
  - lia.
  - exact Hlen.
  - exact Hhead.
  - exact Hwforig.
  - exact Hwfwords.
  - exact Hkept.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hremoved. lia.
  - exact Hsuffix1.
  - exact Htags'.
  - assert (Erhs :
      map lit_denote (tl kept) ++ map lit_denote removed ++
        lit_denote (Znth i words 0) ::
          map lit_denote (sublist (i + 1) (Zlength original) original) =
      map lit_denote (tl kept) ++
        map lit_denote (removed ++ Znth i words 0 :: nil) ++
          map lit_denote (sublist (i + 1) (Zlength original) original)).
    { rewrite map_app. cbn. rewrite <- !app_assoc. reflexivity. }
    rewrite Hpending in Hperm.
    unfold lits_denote in Hperm |- *.
    cbn in Hperm.
    rewrite <- Erhs. exact Hperm.
  - rewrite Eview. exact Hwit'.
  - unfold minimize_tag_scope in Hscope |- *.
    rewrite Eview, Etagged.
    intros x Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx].
    + destruct (Hscope x Hx) as [Hlev|[Hb|HT]].
      * left. exact Hlev.
      * right. destruct (Hbase1 x Hb) as [Hnew|HTnew]; tauto.
      * right; right. apply in_or_app. left. exact HT.
    + right; right. apply in_or_app. right. right. exact Hx.
  - rewrite Forall_forall in HremIn |- *.
    intros l Hl. apply in_app_or in Hl. destruct Hl as [Hl|[Hl|[]]].
    + apply in_or_app. left. exact (HremIn l Hl).
    + apply in_or_app. right. left. subst l. reflexivity.
  - intros x Hx. rewrite Eview.
    apply in_app_or in Hx. destruct Hx as [Hx|Hx].
    + exact (HTlev x Hx).
    + exact (Hbelow x Hx).
  - exact Hprefix.
Qed.

Lemma analysis_cancel_ready_shape__analyze :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    analysis_tags_exact n (ms_tags M) (ms_tagged M) ->
    Zlength (ms_activity M) = n ->
    Zlength (ms_stats M) = 11 ->
    solver_shape M.
Proof.
  intros n F A_arr K M focus Hready Htags Hactivity Hstats.
  pose proof (analysis_cancel_ready_size__lit_removable
    n F A_arr K M focus Hready) as Hsize.
  eapply analysis_cancel_ready_shape__lit_removable; [exact Hready | | | |exact Hstats].
  - destruct Hready as (M0 & Hcancel & Hequiv & Hheap & Hrest).
    unfold heap_wf, msolver_heap in Hheap; cbn in Hheap.
    rewrite <- Hsize. tauto.
  - rewrite <- Hsize. exact Hactivity.
  - rewrite <- Hsize. exact (proj1 Htags).
Qed.

Lemma sublist_replace_prefix__analyze :
  forall (words : list Z) (j v : Z),
    0 <= j < Zlength words ->
    sublist 0 (j + 1) (replace_Znth j v words) =
      sublist 0 j words ++ v :: nil.
Proof.
  intros words j v Hj.
  rewrite (replace_Znth_split j v words Hj).
  assert (Hplen : List.length (sublist 0 j words) = Z.to_nat j).
  { rewrite sublist_length by lia. f_equal. lia. }
  unfold sublist at 1. rewrite skipn_O, firstn_app.
  rewrite firstn_all2 by (rewrite Hplen; lia).
  rewrite Hplen.
  replace (Z.to_nat (j + 1) - Z.to_nat j)%nat with 1%nat by lia.
  reflexivity.
Qed.

Lemma analyze_minimize_keep__analyze :
  forall n M original kept removed words T i j,
    analyze_minimize_loop_inv n M original kept removed words T i j ->
    0 <= i < Zlength words -> 1 <= j -> j <= i ->
    analyze_minimize_loop_inv n M original
      (kept ++ Znth i words 0 :: nil) removed
      (replace_Znth j (Znth i words 0) words) T (i + 1) (j + 1).
Proof.
  intros n M original kept removed words T i j Hinv Hi Hj Hji.
  unfold analyze_minimize_loop_inv in Hinv |- *.
  destruct Hinv as
    [Hj0 [Hji0 [Hiorig [Hlen [Hhead [Hwforig [Hwfwords
    [Hkept [Hremoved [Hsuffix [Htags [Hperm [Hwit [Hscope
    [HremIn [HTlev Hprefix]]]]]]]]]]]]]]]].
  assert (Hwfcur : lit_wf_c n (Znth i words 0)).
  { exact (Forall_Znth_elim _ _ _ 0 i Hwfwords Hi). }
  assert (Hcur_suffix :
    Znth i words 0 = Znth i original 0 /\
    sublist (i + 1) (Zlength original) words =
      sublist (i + 1) (Zlength original) original).
  { assert (Ew := sublist_suffix_cons 0 words i Hi).
    assert (Eo := sublist_suffix_cons 0 original i ltac:(lia)).
    rewrite Hlen in Ew.
    rewrite Ew, Eo in Hsuffix.
    split.
    - exact (f_equal (@hd Z 0) Hsuffix).
    - exact (f_equal (@tl Z) Hsuffix). }
  destruct Hcur_suffix as [Hcur Hsuffix1].
  assert (Hpending : sublist i (Zlength original) original =
    Znth i words 0 :: sublist (i + 1) (Zlength original) original).
  { rewrite (sublist_suffix_cons 0 original i) by lia.
    rewrite Hcur. reflexivity. }
  assert (Hbase :
    (kept ++ Znth i words 0 :: nil) ++
      sublist (i + 1) (Zlength original) original =
    kept ++ sublist i (Zlength original) original).
  { rewrite Hpending. rewrite <- app_assoc. reflexivity. }
  repeat match goal with |- _ /\ _ => split end.
  - lia.
  - lia.
  - lia.
  - rewrite Zlength_replace_Znth. lia.
  - rewrite (Znth_replace_Znth_Diff 0 words j 0 (Znth i words 0)) by lia.
    exact Hhead.
  - exact Hwforig.
  - apply Forall_replace_Znth; assumption.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hkept. lia.
  - lia.
  - rewrite sublist_replace_Znth_outside by lia.
    exact Hsuffix1.
  - exact Htags.
  - assert (Htl : tl (kept ++ Znth i words 0 :: nil) =
                      tl kept ++ Znth i words 0 :: nil).
    { destruct kept as [|k kept']; cbn in Hkept; [lia|]. reflexivity. }
    rewrite Htl, lits_denote_app.
    rewrite Hpending in Hperm.
    unfold lits_denote in Hperm |- *. cbn in Hperm |- *.
    eapply Permutation_trans; [exact Hperm|].
    assert (Hmove : Permutation
      ((map lit_denote removed ++ (lit_denote (Znth i words 0) :: nil)) ++
       map lit_denote (sublist (i + 1) (Zlength original) original))
      (((lit_denote (Znth i words 0) :: nil) ++ map lit_denote removed) ++
       map lit_denote (sublist (i + 1) (Zlength original) original))).
    { apply Permutation_app_tail. apply Permutation_app_comm. }
    rewrite <- !app_assoc.
    rewrite <- !app_assoc in Hmove.
    exact (Permutation_app_head _ Hmove).
  - rewrite Hbase. exact Hwit.
  - rewrite Hbase. exact Hscope.
  - exact HremIn.
  - exact HTlev.
  - rewrite sublist_replace_prefix__analyze by lia.
    rewrite Hprefix.
    assert (Hkept_self : sublist 0 j kept = kept).
    { rewrite <- Hkept. apply sublist_self. reflexivity. }
    rewrite Hkept_self.
    replace (j + 1) with (Zlength (kept ++ (Znth i words 0 :: nil))).
    2: { rewrite Zlength_app, Zlength_cons, Zlength_nil, Hkept; lia. }
    symmetry. apply sublist_self. reflexivity.
Qed.

Lemma analyze_minimize_loop_inv_transport__analyze :
  forall n M M' original kept removed words T i j,
    analysis_core_equiv M M' ->
    ms_tags M' = ms_tags M ->
    ms_tagged M' = ms_tagged M ->
    analyze_minimize_loop_inv n M original kept removed words T i j ->
    analyze_minimize_loop_inv n M' original kept removed words T i j.
Proof.
  intros n M M' original kept removed words T i j Hequiv Etags Etagged Hinv.
  assert (Eview : msolver_view n M' = msolver_view n M).
  { unfold analysis_core_equiv in Hequiv.
    unfold msolver_view, view_of, msolver_clauses, msolver_db.
    destruct Hequiv as
      [_ [_ [_ [Ecore [_ [_ [Ereason [Eprob [Elearnt _]]]]]]]]].
    rewrite Ecore, Ereason, Eprob, Elearnt. reflexivity. }
  unfold analyze_minimize_loop_inv in Hinv |- *.
  unfold minimize_tag_scope in Hinv |- *.
  rewrite Eview, Etags, Etagged.
  exact Hinv.
Qed.

Lemma replace_Znth_incl_self__analyze :
  forall (words : list Z) j x,
    0 <= j < Zlength words -> In x words ->
    incl (replace_Znth j x words) words.
Proof.
  intros words j x Hj Hx y Hy.
  destruct (In_Znth_ex Z (replace_Znth j x words) 0 y Hy)
    as [k [Hk Hval]].
  rewrite Zlength_replace_Znth in Hk.
  rewrite <- Hval.
  destruct (Z.eq_dec k j) as [->|Hne].
  - rewrite Znth_replace_Znth_Same by lia. exact Hx.
  - rewrite Znth_replace_Znth_Diff by lia.
    apply Znth_In. exact Hk.
Qed.

Lemma incl_map_of_incl__analyze :
  forall (f : Z -> Z) xs ys,
    incl xs ys -> incl (map f xs) (map f ys).
Proof.
  intros f xs ys Hinc z Hz.
  apply in_map_iff in Hz.
  destruct Hz as [x [<- Hx]].
  apply in_map. apply Hinc. exact Hx.
Qed.

Lemma analysis_cancel_ready_qtail_eq__analyze :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    Zlength (mt_trail (ms_core M)) = ms_qtail M.
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (asc_qtail _ _ _ Hctx).
Qed.

Lemma analyze_pending_tagged__analyze :
  forall n tags tagged S R learnt x,
    analysis_tags_exact n tags tagged ->
    Permutation tagged (analyze_tags S R learnt) ->
    In x S -> Znth x tags 0 = 1.
Proof.
  intros n tags tagged S R learnt x
    [Hlen [Hnd [Hrange [Hbits Hiff]]]] Hperm Hx.
  assert (HinA : In x (analyze_tags S R learnt)).
  { unfold analyze_tags. apply in_or_app. left. exact Hx. }
  assert (HinT : In x tagged).
  { exact (Permutation_in x (Permutation_sym Hperm) HinA). }
  rewrite Forall_forall in Hrange.
  apply (proj2 (Hiff x (Hrange x HinT))). exact HinT.
Qed.

Lemma analyze_pending_rank_lt_untagged_index__analyze :
  forall n M tags tagged S R learnt x r ind,
    analysis_tags_exact n tags tagged ->
    Permutation tagged (analyze_tags S R learnt) ->
    In x S ->
    assignment_rank (msolver_view n M) x = Some r ->
    Z.of_nat r <= ind ->
    Znth (trail_var (ms_core M) ind) tags 0 = 0 ->
    Z.of_nat r < ind.
Proof.
  intros n M tags tagged S R learnt x r ind Htags Hperm Hx Hrank Hr Hzero.
  assert (Htag := analyze_pending_tagged__analyze
    n tags tagged S R learnt x Htags Hperm Hx).
  destruct (Z.eq_dec (Z.of_nat r) ind) as [Heq|Hne]; [|lia].
  assert (Hvar : trail_var (ms_core M) (Z.of_nat r) = x).
  { apply trail_pos_var.
    change (trail_pos (ms_core M) x = Some r) in Hrank.
    exact Hrank. }
  rewrite Heq in Hvar. rewrite Hvar in Hzero. lia.
Qed.

Lemma analyze_backward_scan_decr__analyze :
  forall n F A_arr K M focus words cnt ind S R learnt,
    analyze_backward_scan_inv n F A_arr K M focus words cnt ind S R learnt ->
    Znth (trail_var (ms_core M) ind) (ms_tags M) 0 = 0 ->
    analyze_backward_scan_inv n F A_arr K M focus words cnt (ind - 1) S R learnt /\
    0 <= ind - 1 /\
    0 <= trail_var (ms_core M) (ind - 1) < n /\
    (Znth (trail_var (ms_core M) (ind - 1)) (ms_tags M) 0 = 0 ->
     0 < ind - 1).
Proof.
  intros n F A_arr K M focus words cnt ind S R learnt Hinv Hzero.
  unfold analyze_backward_scan_inv in Hinv |- *.
  destruct Hinv as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Hdenote
    [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  destruct Hex as [x [r [Hx [Hrank Hr]]]].
  pose proof (analyze_pending_rank_lt_untagged_index__analyze
    n M (ms_tags M) (ms_tagged M) S R learnt x r ind
    Htags Hperm Hx Hrank Hr Hzero) as Hrlt.
  assert (Hindpos : 0 < ind) by (pose proof (Nat2Z.is_nonneg r); lia).
  assert (HSrank' : forall y, In y S -> exists q,
    assignment_rank (msolver_view n M) y = Some q /\
    Z.of_nat q <= ind - 1).
  { intros y Hy. destruct (HSrank y Hy) as [q [Hq Hqi]].
    exists q. split; [exact Hq|].
    pose proof (analyze_pending_rank_lt_untagged_index__analyze
      n M (ms_tags M) (ms_tagged M) S R learnt y q ind
      Htags Hperm Hy Hq Hqi Hzero).
    lia. }
  assert (HRrank' : forall y, In y R -> exists q,
    assignment_rank (msolver_view n M) y = Some q /\
    ind - 1 < Z.of_nat q).
  { intros y Hy. destruct (HRrank y Hy) as [q [Hq Hqi]].
    exists q. split; [exact Hq|lia]. }
  pose proof (analysis_cancel_ready_trail_wf__analyze
    n F A_arr K M focus Hready) as Hwf.
  pose proof (analysis_cancel_ready_qtail_eq__analyze
    n F A_arr K M focus Hready) as Hqtail.
  assert (Hnewrange : 0 <= trail_var (ms_core M) (ind - 1) < n).
  { apply trail_var_range with (t := ms_core M); [exact Hwf|].
    unfold trail_var. apply in_map. apply Znth_In. lia. }
  assert (Hguard :
    Znth (trail_var (ms_core M) (ind - 1)) (ms_tags M) 0 = 0 ->
    0 < ind - 1).
  { intro Hzero'. destruct (HSrank' x Hx) as [q [Hq Hqi]].
    pose proof (analyze_pending_rank_lt_untagged_index__analyze
      n M (ms_tags M) (ms_tagged M) S R learnt x q (ind - 1)
      Htags Hperm Hx Hq Hqi Hzero').
    pose proof (Nat2Z.is_nonneg q). lia. }
  split.
  - repeat match goal with |- _ /\ _ => split end;
      try assumption; try lia.
    exists x, r. split; [ | split ]; try assumption; lia.
  - split; [lia|]. split; [exact Hnewrange|exact Hguard].
Qed.

Lemma lit_wf_c_of_var_range__analyze :
  forall n l,
    0 <= lit_var_c l < n -> lit_wf_c n l.
Proof.
  intros n l Hvar.
  unfold lit_wf_c, lit_var_c in *.
  pose proof (Z.mod_pos_bound l 2 ltac:(lia)) as Hmod.
  pose proof (Z.div_mod l 2 ltac:(lia)) as Hdiv.
  lia.
Qed.

Lemma analyze_resolution_exit_uip__analyze :
  forall n F A_arr K M focus p words,
    analyze_resolution_exit n F A_arr K M focus p words ->
    let uip_words := replace_Znth 0 (lit_neg_c p) words in
    analysis_cancel_ready n F A_arr K M focus /\
    1 <= Zlength uip_words <= n /\
    Forall (lit_wf_c n) uip_words /\
    NoDup (map lit_var_c uip_words) /\
    analyze_clause_cert n F M uip_words /\
    analysis_tags_exact n (ms_tags M) (ms_tagged M) /\
    incl (map lit_var_c uip_words) (ms_tagged M) /\
    minimize_tag_scope n M uip_words nil.
Proof.
  intros n F A_arr K M focus p words Hexit.
  unfold analyze_resolution_exit in Hexit.
  destruct Hexit as
    [Hready [Hlen [Hroot
      [x [R [learnt [r
        [Hx [Hrank [Htrail [Hdenote [Hinv [Htail [Htags Hperm]]]]]]]]]]]]]].
  subst x.
  pose proof (analysis_cancel_ready_trail_wf__analyze
    n F A_arr K M focus Hready) as Htrail_wf.
  change (trail_pos (ms_core M) (lit_var_c p) = Some r) in Hrank.
  pose proof (trail_pos_bound (ms_core M) (lit_var_c p) r Hrank) as Hrank_bound.
  pose proof (trail_lit_nonneg n (ms_core M) (Z.of_nat r)
    Htrail_wf ltac:(lia)) as Hp_nonneg.
  rewrite Htrail in Hp_nonneg.
  pose proof (analyze_exit F (msolver_view n M) (lit_var_c p) R learnt Hinv)
    as Huip.
  destruct Hinv as
    [Hent [Hnd_analyze [Hlevels_S [Hassigned_S [Hlevels_R
      [Hranks_R [Hlevels_learnt Hfalse_learnt]]]]]]].
  destruct words as [|h tail]; cbn in Hlen; [lia|].
  cbn in Htail.
  cbn [replace_Znth].
  assert (Hclause :
    lits_denote (lit_neg_c p :: tail) =
      literal_neg (view_lit (msolver_view n M) (lit_var_c p)) :: learnt).
  { change (lit_denote (lit_neg_c p) :: lits_denote tail =
      literal_neg (view_lit (msolver_view n M) (lit_var_c p)) :: learnt).
    rewrite lit_denote_neg by exact Hp_nonneg.
    rewrite Hdenote, Htail. reflexivity. }
  assert (Hincl :
    incl (map lit_var_c (lit_neg_c p :: tail)) (ms_tagged M)).
  { intros v Hv.
    apply (Permutation_in v (Permutation_sym Hperm)).
    unfold analyze_tags. cbn [map] in Hv |- *.
    destruct Hv as [<-|Hv].
    - rewrite lit_var_c_neg. left. reflexivity.
    - apply in_or_app. right. apply in_or_app. right.
      rewrite <- Htail, map_literal_var_lits_denote. exact Hv. }
  assert (Hwf : Forall (lit_wf_c n) (lit_neg_c p :: tail)).
  { apply Forall_forall. intros l Hl.
    apply lit_wf_c_of_var_range__analyze.
    pose proof Htags as Htags_parts.
    destruct Htags_parts as [_ [_ [Hrange _]]].
    rewrite Forall_forall in Hrange.
    apply Hrange, Hincl, in_map. exact Hl. }
  assert (Hnodup : NoDup (map lit_var_c (lit_neg_c p :: tail))).
  { destruct Huip as [_ [Hnd _]].
    rewrite <- map_literal_var_lits_denote, Hclause. exact Hnd. }
  assert (Hcert : analyze_clause_cert n F M (lit_neg_c p :: tail)).
  { unfold analyze_clause_cert. split.
    - rewrite Hclause. exact Huip.
    - split; [exact Hroot|].
      unfold learned_tail_positive. cbn [tl]. rewrite Htail.
      eapply Forall_impl; [|exact Hlevels_learnt].
      intros l [d [Hlevel Hd]]. exists d. split; [exact Hlevel|lia]. }
  assert (Hscope : minimize_tag_scope n M (lit_neg_c p :: tail) nil).
  { unfold minimize_tag_scope. intros v Hv.
    assert (Hana : In v (analyze_tags (lit_var_c p :: nil) R learnt)).
    { exact (Permutation_in v Hperm Hv). }
    unfold analyze_tags in Hana. cbn [app] in Hana.
    destruct Hana as [Heq | Hana].
    - subst v. right. left. cbn. rewrite lit_var_c_neg. auto.
    - apply in_app_or in Hana. destruct Hana as [HinR | HinL].
      + left. rewrite Forall_forall in Hlevels_R.
        exact (Hlevels_R v HinR).
      + right. left. cbn. right.
        rewrite <- Htail, map_literal_var_lits_denote in HinL.
        exact HinL. }
  assert (Huip_words :
    replace_Znth 0 (lit_neg_c p) (h :: tail) = lit_neg_c p :: tail)
    by reflexivity.
  rewrite Huip_words.
  split; [exact Hready|].
  split; [cbn in Hlen |- *; lia|].
  split; [exact Hwf|].
  split; [exact Hnodup|].
  split; [exact Hcert|].
  split; [exact Htags|].
  split; [exact Hincl|exact Hscope].
Qed.

Lemma count_le_mono__analyze :
  forall i j xs, i <= j -> count_le i xs <= count_le j xs.
Proof.
  intros i j xs Hij. induction xs as [|x xs IH]; cbn; [lia|].
  destruct (Z.leb x i) eqn:Ei; destruct (Z.leb x j) eqn:Ej; try lia.
Qed.

Lemma analyze_backward_scan_hit__analyze :
  forall n F A_arr K M focus words cnt ind S R learnt,
    analyze_backward_scan_inv n F A_arr K M focus words cnt ind S R learnt ->
    Znth (trail_var (ms_core M) ind) (ms_tags M) 0 <> 0 ->
    let v := trail_var (ms_core M) ind in
    In v S /\
    assignment_rank (msolver_view n M) v = Some (Z.to_nat ind) /\
    (forall s, In s S -> s <> v -> rank_lt (msolver_view n M) s v) /\
    lit_denote (Znth ind (mt_trail (ms_core M)) 0) =
      view_lit (msolver_view n M) v.
Proof.
  intros n F A_arr K M focus words cnt ind S R learnt Hinv Htag_nonzero.
  unfold analyze_backward_scan_inv in Hinv.
  destruct Hinv as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Htail
      [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  destruct Hainv as
    [Hent [Hnd [HlevelsS [HassignedS [HlevelsR
      [HranksR [HlevelsL HfalseL]]]]]]].
  pose proof (analysis_cancel_ready_trail_wf__analyze
    n F A_arr K M focus Hready) as Hwf.
  pose proof (analysis_cancel_ready_qtail_eq__analyze
    n F A_arr K M focus Hready) as Hqtail.
  assert (Hind_trail : 0 <= ind < Zlength (mt_trail (ms_core M))) by lia.
  assert (Hrankv :
    assignment_rank (msolver_view n M) (trail_var (ms_core M) ind) =
      Some (Z.to_nat ind)).
  { change (trail_pos (ms_core M) (trail_var (ms_core M) ind) =
      Some (Z.to_nat ind)).
    apply trail_pos_of_index; [exact (mtw_trail_nodup Hwf)|exact Hind_trail]. }
  assert (Hvrange : 0 <= trail_var (ms_core M) ind < n).
  { apply trail_var_range with (t := ms_core M); [exact Hwf|].
    unfold trail_var. apply in_map. apply Znth_In. exact Hind_trail. }
  assert (Hvtagged : In (trail_var (ms_core M) ind) (ms_tagged M)).
  { pose proof Htags as Htags_parts.
    destruct Htags_parts as [Htags_len [Htagged_nd [Htagged_range
      [Hbits Hiff]]]].
    assert (Hbit : Znth (trail_var (ms_core M) ind) (ms_tags M) 0 = 0 \/
                   Znth (trail_var (ms_core M) ind) (ms_tags M) 0 = 1).
    { apply (Forall_Znth_elim Z (fun z => z = 0 \/ z = 1)
        (ms_tags M) 0 (trail_var (ms_core M) ind) Hbits).
      rewrite Htags_len. exact Hvrange. }
    apply (proj1 (Hiff _ Hvrange)). destruct Hbit; [contradiction|assumption]. }
  assert (Hana : In (trail_var (ms_core M) ind) (analyze_tags S R learnt)).
  { exact (Permutation_in _ Hperm Hvtagged). }
  assert (HvinS : In (trail_var (ms_core M) ind) S).
  { unfold analyze_tags in Hana. apply in_app_or in Hana.
    destruct Hana as [HinS | Hana]; [exact HinS|].
    apply in_app_or in Hana. destruct Hana as [HinR | HinL].
    - destruct (HRrank _ HinR) as [rr [Hrr Hrr_ind]].
      rewrite Hrankv in Hrr. injection Hrr as Err.
      assert (Z.of_nat rr = ind).
      { rewrite <- Err. apply Z2Nat.id. lia. }
      lia.
    - rewrite Forall_forall in HlevelsL.
      rewrite in_map_iff in HinL.
      destruct HinL as [l [Hvarl Hlin]].
      destruct (HlevelsL l Hlin) as [d [Hlevelv Hd]].
      rewrite Hvarl in Hlevelv.
      destruct Hex as [x [rx [HxS [Hrankx Hrx_ind]]]].
      rewrite Forall_forall in HlevelsS.
      pose proof (HlevelsS x HxS) as Hlevelx.
      unfold msolver_view, view_of in Hlevelx, Hlevelv; cbn in Hlevelx, Hlevelv.
      change (trail_pos (ms_core M) x = Some rx) in Hrankx.
      change (trail_pos (ms_core M) (trail_var (ms_core M) ind) =
        Some (Z.to_nat ind)) in Hrankv.
      rewrite Hrankx in Hlevelx. cbn in Hlevelx.
      rewrite Hrankv in Hlevelv. cbn in Hlevelv.
      rewrite Z2Nat.id in Hlevelv by lia.
      pose proof (count_le_mono__analyze
        (Z.of_nat rx) ind (mt_lim (ms_core M)) Hrx_ind) as Hmono.
      unfold level_of_index in Hlevelx, Hlevelv.
      inversion Hlevelx. inversion Hlevelv.
      rewrite msolver_view_current_level in Hd. exfalso. lia. }
  assert (Hlatest : forall s, In s S ->
    s <> trail_var (ms_core M) ind ->
    rank_lt (msolver_view n M) s (trail_var (ms_core M) ind)).
  { intros s Hs Hne.
    destruct (HSrank s Hs) as [rs [Hranks Hrs_ind]].
    exists rs, (Z.to_nat ind). split; [ | split ]; try assumption.
    assert (Hneq_rank : rs <> Z.to_nat ind).
    { intro Ers. subst rs.
      change (trail_pos (ms_core M) s = Some (Z.to_nat ind)) in Hranks.
      pose proof (trail_pos_var (ms_core M) s (Z.to_nat ind) Hranks) as Es.
      rewrite Z2Nat.id in Es by lia.
      apply Hne. symmetry. exact Es. }
    apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    pose proof (Nat2Z.is_nonneg rs). lia. }
  assert (Hdenote :
    lit_denote (Znth ind (mt_trail (ms_core M)) 0) =
      view_lit (msolver_view n M) (trail_var (ms_core M) ind)).
  { set (l := Znth ind (mt_trail (ms_core M)) 0).
    assert (Hlwf : lit_wf_c n l).
    { subst l. exact (Forall_Znth_elim Z (lit_wf_c n)
        (mt_trail (ms_core M)) 0 ind (mtw_trail_lits Hwf) Hind_trail). }
    assert (Htrue : Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = lit_sig l).
    { pose proof (mtw_trail_true Hwf) as Halltrue.
      rewrite Forall_forall in Halltrue.
      apply Halltrue. subst l. apply Znth_In. exact Hind_trail. }
    assert (Hass : assignment (msolver_view n M) (lit_var_c l) = Some (lit_pol l)).
    { unfold msolver_view, view_of; cbn.
      rewrite mt_pv_nonneg by (exact (proj1 (lit_var_c_in_range n l Hlwf))).
      unfold assigns_pv, assigns_val. rewrite Htrue. apply lbool_val_lit_sig. }
    subst l. rewrite lit_denote_satisfying.
    unfold trail_var. symmetry. apply view_lit_assigned. exact Hass. }
  repeat split; assumption.
Qed.

Lemma nodup_member_other__analyze :
  forall (xs : list Z) x,
    NoDup xs -> In x xs -> 1 < Zlength xs ->
    exists y, In y xs /\ y <> x.
Proof.
  intros xs x Hnd Hx Hlen.
  destruct xs as [|a xs]; [cbn in Hlen; lia|].
  destruct (Z.eq_dec a x) as [->|Hne].
  - destruct xs as [|b xs]; [cbn in Hlen; lia|].
    inversion Hnd as [|? ? Hnotin Hnd']; subst.
    exists b. split; [right; left; reflexivity|].
    intro E. subst b. apply Hnotin. left. reflexivity.
  - exists a. split; [left; reflexivity|exact Hne].
Qed.

Lemma analyze_selected_reason_nonzero__analyze :
  forall n F A_arr K M focus words cnt ind S R learnt,
    analyze_backward_scan_inv n F A_arr K M focus words cnt ind S R learnt ->
    Znth (trail_var (ms_core M) ind) (ms_tags M) 0 <> 0 ->
    1 < cnt ->
    Znth (trail_var (ms_core M) ind) (ms_reason_words M) 0 <> 0.
Proof.
  intros n F A_arr K M focus words cnt ind S R learnt
    Hscan Htag Hcntgt Hzero.
  pose proof (analyze_backward_scan_hit__analyze
    n F A_arr K M focus words cnt ind S R learnt Hscan Htag) as Hhit.
  cbn in Hhit.
  destruct Hhit as [HvinS [Hrankv [Hlatest Hdenote]]].
  unfold analyze_backward_scan_inv in Hscan.
  destruct Hscan as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Htail
      [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  destruct Hainv as
    [Hent [Hnd [HlevelsS [HassignedS [HlevelsR
      [HranksR [HlevelsL HfalseL]]]]]]].
  pose proof (NoDup_app_remove_r S (R ++ map literal_var learnt) Hnd)
    as HndS.
  destruct (nodup_member_other__analyze
    S (trail_var (ms_core M) ind) HndS HvinS ltac:(lia))
    as [y [HyS Hyne]].
  pose proof Hready as Hready_copy.
  destruct Hready_copy as
    (M0 & Hcancel & Hequiv & Hheap & Hcovers & Hreasonless & Hfocus & Hfp).
  rewrite Forall_forall in HlevelsS.
  pose proof (HlevelsS _ HvinS) as Hlevelv.
  pose proof (HlevelsS y HyS) as Hlevely.
  rewrite msolver_view_current_level in Hlevelv, Hlevely.
  destruct (Hreasonless (Zlength (mt_lim (ms_core M))) ltac:(lia)
    (trail_var (ms_core M) ind) Hlevelv Hzero) as [Hnone Hboundary].
  change (trail_pos (ms_core M) (trail_var (ms_core M) ind) =
    Some (Z.to_nat
      (Znth (Zlength (mt_lim (ms_core M)) - 1) (mt_lim (ms_core M)) 0)))
    in Hboundary.
  rewrite Hrankv in Hboundary. injection Hboundary as Hind_boundary_nat.
  destruct (Hlatest y HyS Hyne) as
    [ry [rv [Hranky [Hrankv' Hryv]]]].
  change (trail_pos (ms_core M) (trail_var (ms_core M) ind) = Some rv)
    in Hrankv'.
  rewrite Hrankv in Hrankv'. injection Hrankv' as Erv.
  subst rv.
  change (trail_pos (ms_core M) y = Some ry) in Hranky.
  unfold msolver_view, view_of in Hlevely; cbn in Hlevely.
  rewrite Hranky in Hlevely. cbn in Hlevely.
  unfold level_of_index in Hlevely.
  injection Hlevely as Hcount.
  pose proof (count_le_all_inv (Z.of_nat ry) (mt_lim (ms_core M)) Hcount)
    as Hall_bounds.
  pose proof (analysis_cancel_ready_trail_wf__analyze
    n F A_arr K M focus Hready) as Htrailwf.
  destruct (Z.eq_dec (Zlength (mt_lim (ms_core M))) 0)
    as [Hlevel_zero|Hlevel_pos].
  { rewrite Hlevel_zero in Hind_boundary_nat.
    destruct (mt_lim (ms_core M)) as [|b bs] eqn:Elim.
    - assert (Hnil : Znth (0 - 1) (@nil Z) 0 = 0).
      { unfold Znth. destruct (Z.to_nat (0 - 1)); reflexivity. }
      rewrite Hnil in Hind_boundary_nat.
      cbn in Hind_boundary_nat. lia.
    - rewrite Zlength_cons in Hlevel_zero.
      pose proof (Zlength_nonneg bs). lia. }
  pose proof (Zlength_nonneg (mt_lim (ms_core M))) as Hlevel_nonneg.
  assert (Hlast_range :
    0 <= Znth (Zlength (mt_lim (ms_core M)) - 1)
      (mt_lim (ms_core M)) 0).
  { pose proof (Forall_Znth_elim Z
      (fun b => 0 <= b < Zlength (mt_trail (ms_core M)))
      (mt_lim (ms_core M)) 0
      (Zlength (mt_lim (ms_core M)) - 1)
      (mtw_lim_range Htrailwf) ltac:(lia)) as Hr.
    exact (proj1 Hr). }
  assert (Hlast_le :
    Znth (Zlength (mt_lim (ms_core M)) - 1)
      (mt_lim (ms_core M)) 0 <= Z.of_nat ry).
  { rewrite Forall_forall in Hall_bounds.
    apply Hall_bounds, Znth_In. lia. }
  apply (f_equal Z.of_nat) in Hind_boundary_nat.
  rewrite Z2Nat.id in Hind_boundary_nat by lia.
  rewrite Z2Nat.id in Hind_boundary_nat by exact Hlast_range.
  pose proof (Nat2Z.is_nonneg ry).
  lia.
Qed.

Lemma analyze_backward_scan_selected__analyze :
  forall n F A_arr K M focus words cnt ind S R learnt,
    analyze_backward_scan_inv n F A_arr K M focus words cnt ind S R learnt ->
    Znth (trail_var (ms_core M) ind) (ms_tags M) 0 <> 0 ->
    1 < cnt ->
    exists C,
      Znth (trail_var (ms_core M) ind) (ms_reason_words M) 0 <> 0 /\
      reason_target_wf n M (trail_var (ms_core M) ind)
        (Znth (trail_var (ms_core M) ind) (ms_reason_words M) 0) C /\
      analyze_resolution_loop_inv n F A_arr K M focus AnalyzeSelected
        (Znth (trail_var (ms_core M) ind) (ms_reason_words M) 0) C words
        (cnt - 1) (ind - 1) (Znth ind (mt_trail (ms_core M)) 0).
Proof.
  intros n F A_arr K M focus words cnt ind S R learnt Hscan Htag Hcntgt.
  pose proof (analyze_selected_reason_nonzero__analyze
    n F A_arr K M focus words cnt ind S R learnt Hscan Htag Hcntgt)
    as Hnonzero.
  pose proof (analyze_backward_scan_hit__analyze
    n F A_arr K M focus words cnt ind S R learnt Hscan Htag) as Hhit.
  cbn in Hhit.
  destruct Hhit as [HvinS [Hrankv [Hlatest Hdenote]]].
  pose proof Hscan as Hscan_parts.
  unfold analyze_backward_scan_inv in Hscan_parts.
  destruct Hscan_parts as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Htail
      [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  pose proof Hainv as Hainv_parts.
  destruct Hainv_parts as
    [Hent [Hnd [HlevelsS [HassignedS [HlevelsR
      [HranksR [HlevelsL HfalseL]]]]]]].
  pose proof (NoDup_app_remove_r S (R ++ map literal_var learnt) Hnd)
    as HndS.
  destruct (nodup_member_other__analyze
    S (trail_var (ms_core M) ind) HndS HvinS ltac:(lia))
    as [y [HyS Hyne]].
  destruct (Hlatest y HyS Hyne) as
    [ry [rv [Hranky [Hrankv' Hryv]]]].
  change (trail_pos (ms_core M) (trail_var (ms_core M) ind) = Some rv)
    in Hrankv'.
  rewrite Hrankv in Hrankv'. injection Hrankv' as Erv. subst rv.
  pose proof (Nat2Z.is_nonneg ry).
  assert (Hindpos : 0 < ind).
  { apply Nat2Z.inj_lt in Hryv.
    rewrite Z2Nat.id in Hryv by lia. lia. }
  pose proof (analysis_cancel_ready_trail_wf__analyze
    n F A_arr K M focus Hready) as Htrailwf.
  assert (Hind_trail : 0 <= ind < Zlength (mt_trail (ms_core M))).
  { pose proof (analysis_cancel_ready_qtail_eq__analyze
      n F A_arr K M focus Hready). lia. }
  assert (Hp_wf : lit_wf_c n (Znth ind (mt_trail (ms_core M)) 0)).
  { exact (Forall_Znth_elim Z (lit_wf_c n)
      (mt_trail (ms_core M)) 0 ind (mtw_trail_lits Htrailwf) Hind_trail). }
  assert (Hp_not_minus_two :
    Znth ind (mt_trail (ms_core M)) 0 <> -2).
  { unfold lit_wf_c in Hp_wf. lia. }
  destruct (analysis_cancel_ready_reason_bundle__analyze
    n F A_arr K M focus (trail_var (ms_core M) ind) (Z.to_nat ind)
    Hready ltac:(eapply trail_var_range; [exact Htrailwf|];
      unfold trail_var; apply in_map; apply Znth_In; exact Hind_trail)
    Hrankv Hnonzero) as
    [C [Htarget [HfocusC [Hvalid [HentC [HwfC HnodupC]]]]]].
  pose proof Htarget as Htarget_parts.
  unfold reason_target_wf in Htarget_parts.
  destruct Htarget_parts as
    [HvM [Hpword [Hword [Hreason Htarget_shape]]]].
  exists C. split; [exact Hnonzero|]. split; [exact Htarget|].
  unfold analyze_resolution_loop_inv.
  split; [exact Hready|].
  split; [lia|].
  split; [exact Hwords|].
  split; [exact Hroot|].
  split; [exact Htags|].
  cbn.
  exists S, R, learnt, (trail_var (ms_core M) ind).
  split; [exact Hp_not_minus_two|].
  split; [unfold trail_var; reflexivity|].
  split; [exact HvinS|].
  split; [replace (ind - 1 + 1) with ind by lia; reflexivity|].
  split.
  { replace (ind - 1 + 1) with ind by lia. exact Hrankv. }
  split; [exact Hlatest|].
  split; [exact Hdenote|].
  split; [lia|].
  split; [lia|].
  split; [reflexivity|].
  split; [exact Hreason|].
  split; [exact Htarget|].
  split; [exact HfocusC|].
  split; [exact Hvalid|].
  split; [exact HentC|].
  split; [exact HwfC|].
  split; [exact HnodupC|].
  split; [exact Hainv|].
  split; [exact Htail|exact Hperm].
Qed.

Lemma analyze_backward_scan_exit__analyze :
  forall n F A_arr K M focus words cnt ind S R learnt,
    analyze_backward_scan_inv n F A_arr K M focus words cnt ind S R learnt ->
    Znth (trail_var (ms_core M) ind) (ms_tags M) 0 <> 0 ->
    cnt = 1 ->
    analyze_resolution_exit n F A_arr K M focus
      (Znth ind (mt_trail (ms_core M)) 0) words.
Proof.
  intros n F A_arr K M focus words cnt ind S R learnt Hinv Htag Hcnt1.
  pose proof (analyze_backward_scan_hit__analyze
    n F A_arr K M focus words cnt ind S R learnt Hinv Htag) as Hhit.
  cbn in Hhit.
  destruct Hhit as [HvinS [Hrankv [Hlatest Hdenote]]].
  unfold analyze_backward_scan_inv in Hinv.
  destruct Hinv as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Htail
      [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  assert (HS : S = trail_var (ms_core M) ind :: nil).
  { assert (HlenS : Zlength S = 1) by lia.
    destruct S as [|a S']; [cbn in HlenS; lia|].
    rewrite Zlength_cons in HlenS.
    destruct S' as [|b S''].
    - cbn in HvinS. destruct HvinS as [<-|[]]. reflexivity.
    - rewrite Zlength_cons in HlenS.
      pose proof (Zlength_nonneg S''). lia. }
  unfold analyze_resolution_exit.
  split; [exact Hready|]. split; [exact Hwords|]. split; [exact Hroot|].
  exists (trail_var (ms_core M) ind), R, learnt, (Z.to_nat ind).
  split; [reflexivity|].
  split.
  { change (trail_pos (ms_core M) (trail_var (ms_core M) ind) =
      Some (Z.to_nat ind)).
    exact Hrankv. }
  split; [rewrite Z2Nat.id by lia; reflexivity|].
  split; [exact Hdenote|].
  split; [rewrite <- HS; exact Hainv|].
  split; [exact Htail|].
  split; [exact Htags|].
  rewrite <- HS. exact Hperm.
Qed.

Lemma trail_implied_level_zero__analyze :
  forall n F M x b,
    mtrail_wf n (ms_core M) ->
    trail_implied F (ms_core M) ->
    assignment (msolver_view n M) x = Some b ->
    level_of (msolver_view n M) x = Some 0 ->
    entails_clause F (satisfying_literal x b :: nil).
Proof.
  intros n F M x b Hwf Himpl Hass Hlevel.
  change (mt_pv (ms_core M) x = Some b) in Hass.
  change
    (option_map
      (fun k => level_of_index (ms_core M) (Z.of_nat k))
      (trail_pos (ms_core M) x) = Some 0) in Hlevel.
  destruct (trail_pos (ms_core M) x) as [r|] eqn:Hrank;
    cbn in Hlevel; try discriminate.
  inversion Hlevel as [Hlevel0].
  pose proof (trail_pos_bound (ms_core M) x r Hrank) as Hbound.
  assert (Hlit : Znth (Z.of_nat r) (mt_trail (ms_core M)) 0 =
      trail_lit_of (ms_core M) x).
  { pose proof (trail_pos_var (ms_core M) x r Hrank) as Hvar.
    assert (Hwf_lit : lit_wf_c n
      (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)).
    { eapply Forall_Znth_elim; [exact (mtw_trail_lits Hwf)|lia]. }
    assert (Hnonneg : 0 <= Znth (Z.of_nat r)
      (mt_trail (ms_core M)) 0) by (destruct Hwf_lit; lia).
    assert (Htrue :
      Znth (lit_var_c (Znth (Z.of_nat r)
        (mt_trail (ms_core M)) 0)) (mt_assigns (ms_core M)) 0 =
      lit_sig (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)).
    { pose proof (mtw_trail_true Hwf) as Hall.
      rewrite Forall_forall in Hall. apply Hall. apply Znth_In. lia. }
    assert (Hxnonneg : 0 <= x).
    { rewrite <- Hvar. apply (lit_var_c_nonneg n). exact Hwf_lit. }
    assert (Hsign : lit_sign_c (Znth (Z.of_nat r)
        (mt_trail (ms_core M)) 0) =
      lit_sign_c (trail_lit_of (ms_core M) x)).
    { fold (trail_var (ms_core M) (Z.of_nat r)) in Htrue.
      rewrite Hvar in Htrue.
      unfold trail_lit_of, lit_sig, lit_sign_c in *.
      destruct (Z.eqb (Znth x (mt_assigns (ms_core M)) 0) (-1)) eqn:Eneg;
      destruct (Z.odd (Znth (Z.of_nat r)
        (mt_trail (ms_core M)) 0)) eqn:Eodd.
      - replace (2 * x + 1) with (Z.succ (2 * x)) by lia.
        rewrite Z.odd_succ, Z.even_mul. reflexivity.
      - apply Z.eqb_eq in Eneg. rewrite Eneg in Htrue. cbn in Htrue. lia.
      - apply Z.eqb_neq in Eneg. cbn in Htrue. contradiction.
      - rewrite Z.odd_mul. reflexivity. }
    pose proof (lit_pack_unpack
      (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0) Hnonneg) as E1.
    pose proof (lit_pack_unpack (trail_lit_of (ms_core M) x)
      (trail_lit_of_nonneg (ms_core M) x Hxnonneg)) as E2.
    fold (trail_var (ms_core M) (Z.of_nat r)) in E1.
    rewrite Hvar, Hsign in E1.
    rewrite (trail_lit_of_var (ms_core M) x Hxnonneg) in E2.
    lia. }
  pose proof (Himpl (Z.of_nat r)
    (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)
    ltac:(lia) eq_refl) as Hent.
  rewrite Hlevel0 in Hent.
  unfold decisions_upto, ztake in Hent. cbn in Hent.
  unfold cnf_with_units in Hent. cbn in Hent. rewrite app_nil_r in Hent.
  change (entails_clause F
    (lit_denote (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0) :: nil)) in Hent.
  assert (Hdenote :
    lit_denote (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0) =
    satisfying_literal x b).
  { rewrite Hlit. apply trail_lit_of_denote.
    - pose proof (trail_pos_var (ms_core M) x r Hrank) as Hvar.
    assert (Hwf_lit : lit_wf_c n
      (Znth (Z.of_nat r) (mt_trail (ms_core M)) 0)).
    { eapply Forall_Znth_elim; [exact (mtw_trail_lits Hwf)|lia]. }
    rewrite <- Hvar. apply (lit_var_c_nonneg n). exact Hwf_lit.
    - exact Hass. }
  rewrite Hdenote in Hent. exact Hent.
Qed.

Lemma analysis_cancel_ready_reason_nodup__analyze :
  forall n F A_arr K M focus x r c,
    analysis_cancel_ready n F A_arr K M focus ->
    0 <= x < n ->
    assignment_rank (msolver_view n M) x = Some r ->
    reason_of (msolver_view n M) x = Some c ->
    NoDup (map literal_var c).
Proof.
  intros n F A_arr K M focus x r c Hready Hx Hrank Hreason.
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K M focus Hready) as [Hsize [Hmatch Hbinary]].
  assert (Hnonzero : Znth x (ms_reason_words M) 0 <> 0).
  { intro Ezero.
    pose proof (Hmatch x Hx) as Hok.
    rewrite Ezero in Hok.
    pose proof (reason_word_ok_null (ms_core M) x (msolver_db M)
      (ms_reason_of M x) Hok) as Hnone.
    change (trail_pos (ms_core M) x = Some r) in Hrank.
    change
      ((match trail_pos (ms_core M) x with
        | Some _ => ms_reason_of M x
        | None => None
        end) = Some c) in Hreason.
    rewrite Hrank, Hnone in Hreason. discriminate. }
  destruct (analysis_cancel_ready_reason_bundle__analyze
    n F A_arr K M focus x r Hready Hx Hrank Hnonzero)
    as [C [Htarget [Hfocus [Hvalid [Hent [Hwf Hnodup]]]]]].
  unfold reason_target_wf in Htarget.
  destruct Htarget as [_ [_ [_ [HC _]]]].
  change (trail_pos (ms_core M) x = Some r) in Hrank.
  change
    ((match trail_pos (ms_core M) x with
      | Some _ => ms_reason_of M x
      | None => None
      end) = Some c) in Hreason.
  rewrite Hrank in Hreason.
  assert (C = c) by congruence. subst C. exact Hnodup.
Qed.

Lemma analyze_minimize_finish__analyze :
  forall n F A_arr K M focus original kept removed words T i j,
    analysis_cancel_ready n F A_arr K M focus ->
    analyze_clause_cert n F M original ->
    analyze_minimize_loop_inv n M original kept removed words T i j ->
    Zlength original <= i ->
    let compact := sublist 0 j words in
    1 <= Zlength compact /\
    Zlength compact <= n /\
    Forall (lit_wf_c n) compact /\
    NoDup (map lit_var_c compact) /\
    analyze_clause_cert n F M compact.
Proof.
  intros n F A_arr K M focus original kept removed words T i j
    Hready Hcert Hinv Hdone compact.
  destruct (analysis_cancel_ready_weak_facts__analyze
    n F A_arr K M focus Hready) as
    [Hground [Hreasonent [Hreasoninj [Htrailwf
      [Hdbwf [Hbinaryout Htrailimpl]]]]]].
  unfold analyze_minimize_loop_inv in Hinv.
  destruct Hinv as
    (Hjpos & Hji & Hiend & Hwordslen & Hhead & Hwforig & Hwfwords &
     Hkeptlen & Hremovedlen & Hsuffix & Htagsexact & Hperm & Hwitness &
     Hscope & Hremoved & Hbelow & Hprefix).
  assert (Ei : i = Zlength original) by lia.
  assert (Hpending : sublist i (Zlength original) original = nil).
  { rewrite Ei. apply sublist_nil. lia. }
  rewrite Hpending, app_nil_r in Hperm.
  assert (Hcompact : compact = kept).
  { subst compact. rewrite Hprefix.
    apply sublist_self. rewrite Hkeptlen. lia. }
  assert (Hpermfull : Permutation (lits_denote original)
      (lits_denote kept ++ lits_denote removed)).
  { assert (Hheadkept : Znth 0 kept 0 = Znth 0 original 0).
    { rewrite <- Hcompact. subst compact.
      rewrite Znth_sublist by lia. exact Hhead. }
    destruct original as [|o ot]; [cbn in Hiend; lia|].
    destruct kept as [|k kt]; [cbn in Hkeptlen; lia|].
    cbn in Hheadkept. subst k.
    cbn [lits_denote] in Hperm |- *.
    apply perm_skip. exact Hperm. }
  destruct Hcert as [Huip [Hroot Hpositive]].
  destruct Huip as [[Hentailed Hfalse] [Hnodup Hasserting]].
  assert (Hfalse_kept : clause_false (assignment (msolver_view n M))
      (lits_denote kept)).
  { intros l Hl. apply Hfalse.
    eapply Permutation_in; [exact (Permutation_sym Hpermfull)|].
    apply in_or_app. left. exact Hl. }
  assert (Hwfcompact : Forall (lit_wf_c n) compact).
  { subst compact. unfold sublist. rewrite skipn_O.
    rewrite <- (firstn_skipn (Z.to_nat j) words) in Hwfwords.
    apply Forall_app in Hwfwords. tauto. }
  assert (Hnodupcompact : NoDup (map lit_var_c compact)).
  { rewrite Hcompact, <- map_literal_var_lits_denote.
    pose proof (Permutation_map literal_var Hpermfull) as Hpermvars.
    pose proof (Permutation_NoDup Hpermvars Hnodup) as Hndall.
    rewrite map_app in Hndall.
    eapply NoDup_app_remove_r. exact Hndall. }
  assert (Hlencompact : Zlength compact = j).
  { rewrite Hcompact. exact Hkeptlen. }
  assert (Hlenbound : Zlength compact <= n).
  { assert (Hvarbound : forall x,
        In x (map lit_var_c compact) -> 0 <= x < n).
    { intros x Hx. apply in_map_iff in Hx.
      destruct Hx as [l [<- Hl]].
      apply lit_var_c_in_range. rewrite Forall_forall in Hwfcompact.
      exact (Hwfcompact l Hl). }
    pose proof (NoDup_Z_bounded_length (map lit_var_c compact) n
      (mtw_n_nonneg Htrailwf) Hnodupcompact Hvarbound) as Hle.
    rewrite length_map in Hle. rewrite Zlength_correct. exact Hle. }
  rewrite Hpending, app_nil_r in Hwitness.
  assert (Hremoved_clause :
    Forall (fun l => In (literal_var l) T) (lits_denote removed)).
  { rewrite Forall_forall in Hremoved |- *.
    intros l Hl. unfold lits_denote in Hl.
    apply in_map_iff in Hl. destruct Hl as [w [<- Hw]].
    rewrite lit_var_c_denote. exact (Hremoved w Hw). }
  assert (Hentailed_kept : entails_clause F (lits_denote kept)).
  { eapply (minimization_sound F (msolver_view n M)
      (map lit_var_c kept) T (lits_denote original)
      (lits_denote kept) (lits_denote removed)).
    - exact Hground.
    - intros x b Hass Hlev.
      eapply trail_implied_level_zero__analyze; eauto.
    - intros x b Hxin HnotT Hass.
      apply in_map_iff in Hxin.
      destruct Hxin as [w [<- Hw]].
      apply entails_clause_units_unit.
      apply in_map_iff.
      exists (lit_denote w). split.
      + assert (Hlw : In (lit_denote w) (lits_denote kept)).
        { unfold lits_denote. apply in_map. exact Hw. }
        assert (Hlo : In (lit_denote w) (lits_denote original)).
        { eapply Permutation_in; [exact (Permutation_sym Hpermfull)|].
          apply in_or_app. left. exact Hlw. }
        destruct (eval_partial_false_shape _ _ (Hfalse _ Hlo))
          as [b' [Hass' Hshape]].
        rewrite lit_var_c_denote in Hass'.
        rewrite lit_var_c_denote in Hshape.
        assert (b' = b) by congruence. subst b'.
        rewrite Hshape, <- literal_neg_satisfying,
          literal_neg_involutive. reflexivity.
      + unfold lits_denote. apply in_map. exact Hw.
    - exact Hwitness.
    - intros x c Hx Hreason. exact (Hreasonent x c Hreason).
    - intros x c Hx Hreason.
      destruct (Hbelow x Hx) as [d [r [Hlev [Hrank Hlt]]]].
      assert (Hxrange : 0 <= x < n).
      { apply (trail_var_range n (ms_core M) x Htrailwf).
        eapply msolver_view_level_in_trail__analyze.
        exact Hlev. }
      eapply analysis_cancel_ready_reason_nodup__analyze;
        eauto.
    - exact Hpermfull.
    - exact Hremoved_clause.
    - exact Hfalse.
    - exact Hentailed. }
  assert (Hentailed_compact : entails_clause F (lits_denote compact)).
  { rewrite Hcompact. exact Hentailed_kept. }
  assert (Hfalse_compact : clause_false
      (assignment (msolver_view n M)) (lits_denote compact)).
  { rewrite Hcompact. exact Hfalse_kept. }
  assert (Hnodup_lits : NoDup (map literal_var (lits_denote compact))).
  { rewrite map_literal_var_lits_denote. exact Hnodupcompact. }
  assert (Hheadcompact : Znth 0 compact 0 = Znth 0 original 0).
  { subst compact. rewrite Znth_sublist by lia. exact Hhead. }
  assert (Hasserting_compact :
      exists l rest,
        lits_denote compact = l :: rest /\
        level_of (msolver_view n M) (literal_var l) =
          Some (current_level (msolver_view n M)) /\
        Forall (fun k => exists dk,
          level_of (msolver_view n M) (literal_var k) = Some dk /\
          dk < current_level (msolver_view n M)) rest).
  { assert (Horig_nonempty : original <> nil).
    { intro E. rewrite E in Hiend. cbn in Hiend. lia. }
    assert (Hcompact_nonempty : compact <> nil).
    { intro E. rewrite E in Hlencompact. cbn in Hlencompact. lia. }
    destruct original as [|ow ot] eqn:Eorig; [contradiction|].
    destruct compact as [|cw ct] eqn:Ecompact; [contradiction|].
    cbn in Hheadcompact. subst cw.
    rewrite <- Hcompact in Hperm. cbn [lits_denote] in Hperm.
    destruct Hasserting as [l [rest [Eshape [Hlevel Hlevels]]]].
    cbn [lits_denote] in Eshape.
    inversion Eshape; subst l rest.
    exists (lit_denote ow), (lits_denote ct).
    split; [ | split ]; try reflexivity; try exact Hlevel.
    rewrite Forall_forall in Hlevels |- *.
    intros k Hk. apply Hlevels.
    eapply Permutation_in; [exact (Permutation_sym Hperm)|].
    apply in_or_app. left. exact Hk. }
  assert (Hcert_compact : analyze_clause_cert n F M compact).
  { split.
    - split.
      + split; [exact Hentailed_compact|exact Hfalse_compact].
      + split; [exact Hnodup_lits|exact Hasserting_compact].
    - split; [exact Hroot|].
      unfold learned_tail_positive in *.
      rewrite Hcompact.
      rewrite Forall_forall in Hpositive |- *.
      intros l Hl. apply Hpositive.
      eapply Permutation_in; [exact (Permutation_sym Hperm)|].
      apply in_or_app. left. exact Hl. }
  split.
  - rewrite Hlencompact. exact Hjpos.
  - split; [exact Hlenbound|].
    split; [exact Hwfcompact|].
    split; [exact Hnodupcompact|exact Hcert_compact].
Qed.

Lemma clear_indices_app__analyze : forall xs ys tags,
  clear_indices (xs ++ ys) tags = clear_indices ys (clear_indices xs tags).
Proof.
  induction xs as [|x xs IH]; intros ys tags; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma analysis_tags_exact_index_range__analyze :
  forall n tags tagged i,
  analysis_tags_exact n tags tagged ->
  0 <= i < Zlength tagged ->
  0 <= Znth i tagged 0 < n.
Proof.
  intros n tags tagged i H Hidx.
  unfold analysis_tags_exact in H.
  destruct H as [_ [_ [Hrange _]]].
  exact (Forall_Znth_elim _ _ _ 0 i Hrange Hidx).
Qed.

Lemma analyze_clear_start__analyze : forall n tags tagged,
  analysis_tags_exact n tags tagged ->
  analyze_clear_loop_inv n 0 tagged tags tags.
Proof.
  intros n tags tagged Hexact.
  unfold analyze_clear_loop_inv.
  split; [pose proof (Zlength_nonneg tagged); lia|].
  split; [exact Hexact|].
  rewrite Zsublist_nil by lia. reflexivity.
Qed.

Lemma analyze_clear_step__analyze : forall n i tagged tags0 tags,
  analyze_clear_loop_inv n i tagged tags0 tags ->
  i < Zlength tagged ->
  analyze_clear_loop_inv n (i + 1) tagged tags0
    (replace_Znth (Znth i tagged 0) 0 tags).
Proof.
  intros n i tagged tags0 tags Hinv Hi.
  unfold analyze_clear_loop_inv in *.
  destruct Hinv as [Hirange [Hexact Htags]].
  split; [lia|]. split; [exact Hexact|].
  rewrite Htags, (sublist_snoc 0) by lia.
  rewrite clear_indices_app__analyze. reflexivity.
Qed.

Lemma analysis_tags_exact_clear_all__analyze :
  forall n tags tagged,
  analysis_tags_exact n tags tagged ->
  analysis_tags_exact n (clear_indices tagged tags) (@nil Z).
Proof.
  intros n tags tagged. revert tags.
  induction tagged as [|x xs IH]; intros tags H; simpl; [exact H|].
  apply IH. apply analysis_tags_exact_clear_head__lit_removable. exact H.
Qed.

Lemma analyze_clear_done__analyze :
  forall n i tagged tags0 tags,
  analyze_clear_loop_inv n i tagged tags0 tags ->
  i = Zlength tagged ->
  analysis_tags_exact n tags (sublist 0 0 tagged).
Proof.
  intros n i tagged tags0 tags Hinv Hi.
  unfold analyze_clear_loop_inv in Hinv.
  destruct Hinv as [_ [Hexact Htags]]. subst i.
  rewrite Zsublist_nil by lia.
  rewrite (sublist_self tagged (Zlength tagged) ltac:(reflexivity)) in Htags.
  subst tags.
  apply analysis_tags_exact_clear_all__analyze. exact Hexact.
Qed.

Lemma move_Znth_to_front_with_replacement__analyze :
  forall (l : list Z) i d x,
  0 <= i < Zlength l ->
  Permutation (Znth i l d :: replace_Znth i x l) (x :: l).
Proof.
  induction l as [|a l IH]; intros i d x Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite Znth0_cons. simpl. apply perm_swap.
    + rewrite Znth_cons by lia. rewrite replace_Znth_cons by lia.
      eapply Permutation_trans.
      * apply perm_swap.
      * eapply Permutation_trans.
        -- apply perm_skip. apply IH. lia.
        -- apply perm_swap.
Qed.

Lemma swap_Znth_zero_perm__analyze : forall l i,
  0 <= i < Zlength l ->
  Permutation
    (replace_Znth i (Znth 0 l 0)
      (replace_Znth 0 (Znth i l 0) l)) l.
Proof.
  intros l i Hi.
  destruct l as [|a l]; [rewrite Zlength_nil in Hi; lia|].
  rewrite Zlength_cons in Hi.
  destruct (Z.eq_dec i 0) as [-> | Hne].
  - simpl. reflexivity.
  - assert (Hnth : Znth i (a :: l) 0 = Znth (i - 1) l 0).
    { rewrite Znth_cons by lia. reflexivity. }
    rewrite Hnth.
    rewrite Znth0_cons.
    assert (Hrep0 : replace_Znth 0 (Znth (i - 1) l 0) (a :: l) =
      Znth (i - 1) l 0 :: l) by reflexivity.
    rewrite Hrep0.
    rewrite replace_Znth_cons by lia.
    apply move_Znth_to_front_with_replacement__analyze.
    lia.
Qed.

Lemma swap_Znth_one_perm : forall l j,
  1 <= j < Zlength l ->
  Permutation
    (replace_Znth j (Znth 1 l 0)
      (replace_Znth 1 (Znth j l 0) l)) l.
Proof.
  intros l j Hj.
  destruct l as [|a l]; [rewrite Zlength_nil in Hj; lia|].
  rewrite Zlength_cons in Hj.
  assert (Hone : Znth 1 (a :: l) 0 = Znth 0 l 0).
  { rewrite Znth_cons by lia. reflexivity. }
  assert (Hjth : Znth j (a :: l) 0 = Znth (j - 1) l 0).
  { rewrite Znth_cons by lia. reflexivity. }
  rewrite Hone, Hjth.
  rewrite replace_Znth_cons by lia.
  rewrite replace_Znth_cons by lia.
  apply perm_skip.
  apply swap_Znth_zero_perm__analyze.
  lia.
Qed.

Lemma swap_Znth_one_head__analyze : forall l j,
  1 <= j < Zlength l ->
  Znth 0
    (replace_Znth j (Znth 1 l 0)
      (replace_Znth 1 (Znth j l 0) l)) 0 = Znth 0 l 0.
Proof.
  intros l j Hj.
  rewrite Znth_replace_Znth_Diff by (try rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff by lia. reflexivity.
Qed.

Lemma analyze_backjump_singleton__analyze : forall n F M words,
  Zlength words = 1 ->
  analyze_clause_cert n F M words ->
  NoDup (map lit_var_c words) /\
  analyze_backjump_cert n M words (ms_root_level M).
Proof.
  intros n F M words Hlen Hcert.
  destruct words as [|w words]; [rewrite Zlength_nil in Hlen; lia|].
  rewrite Zlength_cons in Hlen.
  destruct words as [|w' words];
    [|rewrite Zlength_cons in Hlen; pose proof (Zlength_nonneg words); lia].
  unfold analyze_clause_cert in Hcert.
  destruct Hcert as [Huip [Hroot Hpositive]].
  unfold uip_exit_cert in Huip.
  destruct Huip as [Hsound [Hnodup [l [rest [Heq [Hhead Htail]]]]]].
  simpl in Heq. inversion Heq; subst l rest.
  split.
  - rewrite <- map_literal_var_lits_denote. exact Hnodup.
  - unfold analyze_backjump_cert.
    repeat split.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + simpl. reflexivity.
    + lia.
    + simpl. rewrite msolver_view_current_level in Hhead. exact Hhead.
    + simpl. constructor.
Qed.

Lemma analyze_clause_cert_perm_head__analyze :
  forall n F M words' words,
  1 <= Zlength words ->
  Permutation words' words ->
  Znth 0 words' 0 = Znth 0 words 0 ->
  analyze_clause_cert n F M words ->
  analyze_clause_cert n F M words'.
Proof.
  intros n F M words' words Hlen Hperm Hhead Hcert.
  assert (Hlen' : 1 <= Zlength words').
  { rewrite (Zlength_perm_eq _ _ _ Hperm). exact Hlen. }
  destruct words as [|w ws]; [rewrite Zlength_nil in Hlen; lia|].
  destruct words' as [|w' ws']; [rewrite Zlength_nil in Hlen'; lia|].
  rewrite !Znth0_cons in Hhead. subst w'.
  assert (Htails : Permutation ws' ws).
  { apply (Permutation_cons_inv (a := w)). exact Hperm. }
  assert (Hden : Permutation (lits_denote (w :: ws))
    (lits_denote (w :: ws'))).
  { apply lits_denote_perm. apply Permutation_sym. exact Hperm. }
  unfold analyze_clause_cert in *.
  destruct Hcert as [Huip [Hroot Hpositive]]. split.
  2: { split; [exact Hroot|].
       unfold learned_tail_positive in *; cbn [tl lits_denote] in *.
       eapply Permutation_Forall; [|exact Hpositive].
       apply lits_denote_perm, Permutation_sym. exact Htails. }
  unfold uip_exit_cert in *.
  destruct Huip as [Hsound [Hnodup [l [rest [Heq [Hl Hrest]]]]]].
  simpl in Heq. inversion Heq; subst l rest.
  split.
  - unfold learned_clause_sound in *.
    destruct Hsound as [Hent Hfalse]. split.
    + eapply entails_clause_perm; [exact Hden|exact Hent].
    + eapply clause_false_perm; [exact Hden|exact Hfalse].
  - split.
    + eapply Permutation_NoDup; [|exact Hnodup].
      apply Permutation_map. exact Hden.
    + exists (lit_denote w), (lits_denote ws').
      split; [reflexivity|]. split; [exact Hl|].
      eapply Permutation_Forall; [|exact Hrest].
      apply lits_denote_perm. apply Permutation_sym. exact Htails.
Qed.

Lemma level_of_msolver_view_levels__analyze : forall n M x d,
  mtrail_wf n (ms_core M) ->
  level_of (msolver_view n M) x = Some d ->
  Znth x (mt_levels (ms_core M)) 0 = d.
Proof.
  intros n M x d Hwf Hlevel.
  unfold msolver_view, view_of in Hlevel.
  cbn [level_of] in Hlevel.
  destruct (trail_pos (ms_core M) x) as [k|] eqn:Hpos;
    [|discriminate].
  simpl in Hlevel. inversion Hlevel; subst d.
  rewrite <- (trail_pos_var (ms_core M) x k Hpos).
  assert (Hk : 0 <= Z.of_nat k < Zlength (mt_trail (ms_core M))).
  { split; [lia|]. apply trail_pos_bound in Hpos. exact Hpos. }
  exact (mtw_levels_agree Hwf (Z.of_nat k) Hk).
Qed.

Lemma analyze_max_tail_bound__analyze :
  forall n M words i max_i max,
  i = Zlength words ->
  analyze_max_loop_inv n M words i max_i max ->
  Forall (fun w =>
    Znth (lit_var_c w) (mt_levels (ms_core M)) 0 <= max) (tl words).
Proof.
  intros n M words i max_i max Hi Hinv.
  unfold analyze_max_loop_inv in Hinv.
  destruct Hinv as [Hirange [_ [_ [_ Hbound]]]].
  destruct words as [|w ws]; [constructor|]. simpl.
  rewrite Forall_forall. intros x Hx.
  destruct (In_Znth_index ws x Hx) as [k [Hk Hval]].
  specialize (Hbound (k + 1) ltac:(rewrite Zlength_cons in Hi; lia)).
  rewrite Znth_cons in Hbound by lia.
  replace (k + 1 - 1) with k in Hbound by lia.
  rewrite Hval in Hbound. exact Hbound.
Qed.

Lemma swap_Znth_one_at_one__analyze : forall l j,
  1 <= j < Zlength l ->
  Znth 1
    (replace_Znth j (Znth 1 l 0)
      (replace_Znth 1 (Znth j l 0) l)) 0 = Znth j l 0.
Proof.
  intros l j Hj.
  destruct (Z.eq_dec j 1) as [-> | Hne].
  - rewrite replace_Znth_replace_Znth_Same by lia.
    rewrite Znth_replace_Znth_Same by lia. reflexivity.
  - rewrite Znth_replace_Znth_Diff
      by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia. reflexivity.
Qed.

Lemma tail_perm_of_perm_head__analyze : forall l' l,
  1 <= Zlength l ->
  Permutation l' l ->
  Znth 0 l' 0 = Znth 0 l 0 ->
  Permutation (tl l') (tl l).
Proof.
  intros l' l Hlen Hperm Hhead.
  assert (Hlen' : 1 <= Zlength l').
  { rewrite (Zlength_perm_eq _ _ _ Hperm). exact Hlen. }
  destruct l as [|x xs]; [rewrite Zlength_nil in Hlen; lia|].
  destruct l' as [|x' xs']; [rewrite Zlength_nil in Hlen'; lia|].
  rewrite !Znth0_cons in Hhead. subst x'. simpl.
  apply (Permutation_cons_inv (a := x)). exact Hperm.
Qed.

Lemma backjump_tail_forall__analyze : forall n M words max,
  mtrail_wf n (ms_core M) ->
  Forall (fun l => exists d,
    level_of (msolver_view n M) (literal_var l) = Some d /\
    d < current_level (msolver_view n M)) (lits_denote words) ->
  Forall (fun w =>
    Znth (lit_var_c w) (mt_levels (ms_core M)) 0 <= max) words ->
  Forall (fun l => exists d,
    level_of (msolver_view n M) (literal_var l) = Some d /\
    d <= Z.max (ms_root_level M) max) (lits_denote words).
Proof.
  intros n M words max Hwftrail Hlevels Hbounds.
  induction words as [|a xs IH]; [constructor|].
  simpl in Hlevels, Hbounds |- *.
  inversion Hlevels as [|? ? Halevel Hlevels']; subst.
  inversion Hbounds as [|? ? Habound Hbounds']; subst.
  constructor.
  - destruct Halevel as [d [Halevel Hd]]. exists d. split; [exact Halevel|].
    pose proof (level_of_msolver_view_levels__analyze
      n M (literal_var (lit_denote a)) d Hwftrail Halevel) as Harray.
    rewrite lit_var_c_denote in Harray. lia.
  - apply IH; assumption.
Qed.

Lemma analyze_backjump_swap_complete__analyze :
  forall n F A_arr K M focus words i max_i max,
  i = Zlength words ->
  analysis_cancel_ready n F A_arr K M focus ->
  analyze_max_loop_inv n M words i max_i max ->
  analyze_clause_cert n F M words ->
  analyze_backjump_cert n M
    (replace_Znth max_i (Znth 1 words 0)
      (replace_Znth 1 (Znth max_i words 0) words))
    (Z.max (ms_root_level M) max).
Proof.
  intros n F A_arr K M focus words i max_i max
    Hi Hready Hinv Hcert.
  unfold analyze_max_loop_inv in Hinv.
  destruct Hinv as [Hirange [Hmaxi [Hwf [Hmaxeq Hmaxbound]]]].
  assert (Hlen : 2 <= Zlength words) by lia.
  set (sw := replace_Znth max_i (Znth 1 words 0)
    (replace_Znth 1 (Znth max_i words 0) words)).
  assert (Hperm : Permutation sw words).
  { subst sw. apply swap_Znth_one_perm. lia. }
  assert (Hhead : Znth 0 sw 0 = Znth 0 words 0).
  { subst sw. apply swap_Znth_one_head__analyze. lia. }
  assert (Hat1 : Znth 1 sw 0 = Znth max_i words 0).
  { subst sw. apply swap_Znth_one_at_one__analyze. lia. }
  assert (Hcertsw : analyze_clause_cert n F M sw).
  { eapply analyze_clause_cert_perm_head__analyze;
      eauto; lia. }
  assert (Htailold : Forall (fun w =>
    Znth (lit_var_c w) (mt_levels (ms_core M)) 0 <= max) (tl words)).
  { eapply analyze_max_tail_bound__analyze; [exact Hi|].
    unfold analyze_max_loop_inv.
    split; [exact Hirange|]. split; [exact Hmaxi|].
    split; [exact Hwf|]. split; assumption. }
  assert (Htailperm : Permutation (tl sw) (tl words)).
  { eapply tail_perm_of_perm_head__analyze; eauto; lia. }
  assert (Htailsw : Forall (fun w =>
    Znth (lit_var_c w) (mt_levels (ms_core M)) 0 <= max) (tl sw)).
  { eapply Permutation_Forall; [|exact Htailold].
    apply Permutation_sym. exact Htailperm. }
  assert (Hwftrail : mtrail_wf n (ms_core M)).
  { eapply analysis_cancel_ready_trail_wf__analyze; eauto. }
  assert (Hlensw : 2 <= Zlength sw).
  { rewrite (Zlength_perm_eq _ _ _ Hperm). exact Hlen. }
  unfold analyze_clause_cert in Hcertsw.
  destruct Hcertsw as [Huip [Hroot Hpositive]].
  unfold uip_exit_cert in Huip.
  destruct Huip as [_ [_ [head [rest [Heq [Hheadlevel Hrest]]]]]].
  destruct sw as [|w [|v vs]].
  - rewrite Zlength_nil in Hlensw. lia.
  - rewrite Zlength_cons, Zlength_nil in Hlensw. lia.
  - simpl in Heq. inversion Heq; subst head rest.
    simpl in Htailsw. inversion Htailsw as [|? ? Hvbound Hvsbound].
    simpl in Hrest. inversion Hrest as [|? ? Hvlevel Hvslevel].
    destruct Hvlevel as [d [Hdlevel Hdlt]].
    pose proof (level_of_msolver_view_levels__analyze
      n M (literal_var (lit_denote v)) d Hwftrail Hdlevel) as Harrayd.
    rewrite lit_var_c_denote in Harrayd.
    rewrite Znth_cons in Hat1 by lia.
    replace (1 - 1) with 0 in Hat1 by lia.
    rewrite Znth0_cons in Hat1.
    assert (Hmaxd : max = d).
    { rewrite Hat1 in Harrayd. lia. }
    subst d.
    unfold analyze_backjump_cert.
    repeat split.
    + simpl. lia.
    + assert (Hltb : Z.ltb 1 (Zlength (w :: v :: vs)) = true).
      { apply Z.ltb_lt. rewrite !Zlength_cons. pose proof (Zlength_nonneg vs). lia. }
      rewrite Hltb.
      rewrite Znth_cons by lia. replace (1 - 1) with 0 by lia.
      rewrite Znth0_cons. rewrite <- Hmaxd. reflexivity.
    + apply Z.le_max_l.
    + apply Z.max_lub_lt_iff. split; [exact Hroot|].
      rewrite Hmaxd. exact Hdlt.
    + simpl. rewrite msolver_view_current_level in Hheadlevel.
      exact Hheadlevel.
    + simpl.
      exact (backjump_tail_forall__analyze
        n M (v :: vs) max Hwftrail Hrest Htailsw).
Qed.

Lemma analysis_cancel_ready_db_tags__analyze :
  forall n F A_arr K M focus,
    analysis_cancel_ready n F A_arr K M focus ->
    prob_db (ms_prob M) /\
    learnt_db (ms_learnt M) /\
    msat_fp32_nonnegative (ms_cla_inc M).
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  destruct Hready as [M0 [Hcancel [Hequiv [_ [_ [_ [_ Hcla]]]]]]].
  exact (conj (asc_prob_db _ _ _ Hctx) (conj (asc_learnt_db _ _ _ Hctx) Hcla)).
Qed.

Lemma lits_denote_wf_inv__analyze :
  forall n words,
    Forall (literal_wf n) (lits_denote words) ->
    Forall (lit_wf_c n) words.
Proof.
  intros n words Hwf.
  rewrite Forall_forall in Hwf |- *.
  intros l Hin.
  apply lit_wf_c_of_var_range__analyze.
  assert (Hdenote : In (lit_denote l) (lits_denote words)).
  { unfold lits_denote. apply in_map. exact Hin. }
  specialize (Hwf (lit_denote l) Hdenote).
  unfold literal_wf, var_in_range in Hwf.
  rewrite lit_var_c_denote in Hwf. exact Hwf.
Qed.

Lemma analyze_resolution_real_clause_source__analyze :
  forall n F A_arr K M focus phase c C words cnt ind p,
    analyze_resolution_loop_inv
      n F A_arr K M focus phase c C words cnt ind p ->
    is_tag c = false ->
    (c = ms_binary M /\
     C = lits_denote (ms_binary_lits M) /\
     Forall (lit_wf_c n) (ms_binary_lits M) /\ ms_binary_lits M <> []) \/
    exists co,
      c <> ms_binary M /\
      In (c, co) (msolver_db M) /\
      C = lits_denote (co_lits co) /\
      Forall (lit_wf_c n) (co_lits co).
Proof.
  intros n F A_arr K M focus phase c C words cnt ind p Hresolution Hreal.
  pose proof Hresolution as Hloop.
  unfold analyze_resolution_loop_inv in Hloop.
  destruct Hloop as
    [Hready [Hind [Hwords [Hroot [Htags Hphase]]]]].
  destruct phase.
  - cbn in Hphase.
    destruct Hphase as
      [Hp [Hcnt [Htrail [Hcert [Hptr [Htagged Htail]]]]]].
    destruct Hcert as
      [Hentails [Hfalse [Hwf [Hnodup Hcurrent]]]].
    destruct Hptr as
      [[Hbinary [HC [Hout Hinitialized]]] | [co [Hbinary [Hin HC]]]].
    + left. split; [exact Hbinary|]. split; [exact HC|].
      split; [|exact Hinitialized].
      apply lits_denote_wf_inv__analyze.
      unfold denote_obj in HC. rewrite <- HC. exact Hwf.
    + right. exists co. split; [exact Hbinary|].
      split; [exact Hin|]. split.
      * unfold denote_obj in HC. exact HC.
      * apply lits_denote_wf_inv__analyze.
        unfold denote_obj in HC. rewrite <- HC. exact Hwf.
  - cbn in Hphase.
    destruct Hphase as [S [R [learnt [x Hphase]]]].
    destruct Hphase as (Hp & Hx & HinS & Htrail & Hrank & Hother & Hlit & Hcnt &
        Hpos & Hcx & Hreason & Htarget & Hfocus & Hvalid & Hentails & Hwf & Hnodup &
        Hinv & Hwords_eq & Hperm).
    destruct Hfocus as
      [[Hbinary [HC Hinitialized]] |
       [[v [Htarget' Htag]] |
        [co [Hbinary [Htag [Hin HC]]]]]].
    + left. split; [exact Hbinary|]. split; [exact HC|].
      split; [|exact Hinitialized].
      apply lits_denote_wf_inv__analyze.
      unfold denote_obj in HC. rewrite <- HC. exact Hwf.
    + rewrite Hreal in Htag. discriminate.
    + right. exists co. split; [exact Hbinary|].
      split; [exact Hin|]. split.
      * unfold denote_obj in HC. exact HC.
      * apply lits_denote_wf_inv__analyze.
        unfold denote_obj in HC. rewrite <- HC. exact Hwf.
Qed.

Lemma analyze_resolution_real_ptr_source__analyze :
  forall n F A_arr K M focus phase c C words cnt ind p,
    analyze_resolution_loop_inv
      n F A_arr K M focus phase c C words cnt ind p ->
    is_tag c = false ->
    c = ms_binary M \/
    exists co, In (c, co) (msolver_db M).
Proof.
  intros n F A_arr K M focus phase c C words cnt ind p Hinv Hreal.
  unfold analyze_resolution_loop_inv in Hinv.
  destruct Hinv as [_ [_ [_ [_ [_ Hphase]]]]].
  destruct phase.
  - cbn in Hphase.
    assert (Hptr : conflict_ptr_denotes M c C) by tauto.
    unfold conflict_ptr_denotes in Hptr.
    destruct Hptr as [[Hc _] | [co [_ [Hin _]]]].
    + left. exact Hc.
    + right. exists co. exact Hin.
  - cbn in Hphase.
    destruct Hphase as [S [R [learnt [x Hphase]]]].
    assert (Hfocus : analysis_clause_focus n M c C) by tauto.
    unfold analysis_clause_focus in Hfocus.
    destruct Hfocus as [[Hc _] | [[v [_ Htag]] | [co [_ [Htag [Hin _]]]]]].
    + left. exact Hc.
    + congruence.
    + right. exists co. exact Hin.
Qed.

Lemma clause_db_rep_positive__analyze :
  forall entries,
    clause_db_rep entries
    |-- “ Forall (fun e => 0 < fst e) entries ”.
Proof.
  intros entries.
  sep_apply clause_db_rep_ptrs.
  Intros_p H.
  dump_pre_spatial.
  rewrite Forall_forall in *.
  intros e Hin.
  specialize (H e Hin).
  tauto.
Qed.


Lemma propagation_ctx_scan_begin__analyze :
  forall n F A_arr K M simp_count prop_count,
    msolver_inv_ctx n F A_arr K M ->
    solver_shape (msolver_propagation_scan_begin M simp_count prop_count) ->
    mtrail_wf n
      (ms_core (msolver_propagation_scan_begin M simp_count prop_count)) ->
    msolver_inv_ctx n F A_arr K
      (msolver_propagation_scan_begin M simp_count prop_count).
Proof.
  intros n F A_arr K M simp_count prop_count Hweak Hshape Hwf.
  destruct K as [A_inst|A_proc]; cbn in Hweak |- *;
    destruct Hweak; constructor; cbn in *; try assumption.
Qed.

Lemma propagation_weak_scan_begin_sum__analyze :
  forall n F A_arr K M simp_count prop_count,
    solver_propagation_inv n F A_arr K M ->
    solver_shape (msolver_propagation_scan_begin M simp_count prop_count) ->
    mtrail_wf n
      (ms_core (msolver_propagation_scan_begin M simp_count prop_count)) ->
    solver_propagation_weak n F A_arr K
      (msolver_propagation_scan_begin M simp_count prop_count).
Proof.
  intros n F A_arr K M simp_count prop_count Hinv Hshape Hwf.
  pose proof (msolver_inv_ctx_of_propagation n F A_arr K M Hinv) as Hctx.
  destruct Hinv as [Hroot _]. split; [exact Hroot|].
  exact (propagation_ctx_scan_begin__analyze n F A_arr K M simp_count
    prop_count Hctx Hshape Hwf).
Qed.

Lemma solver_shape_propagation_scan_begin :
  forall M simp_count prop_count,
    solver_shape M ->
    ms_qtail M - mt_qhead (ms_core M) > 0 ->
    ms_qtail M = Zlength (mt_trail (ms_core M)) ->
    solver_shape (msolver_propagation_scan_begin M simp_count prop_count).
Proof.
  intros M simp_count prop_count Hshape Hpending Hqtail.
  unfold solver_shape in Hshape |- *.
  cbn [msolver_propagation_scan_begin msolver_propagation_scan msolver_propagation_update mt_set_qhead] in *.
  assert (Hnotroot : ms_capacity_root_propagation_pending M <> 1).
  { intro Hrp. intuition lia. }
  decompose [and] Hshape.
  repeat split; try assumption; try contradiction; try lia;
    try rewrite Zlength_replace_Znth; try assumption; try lia.
  - change (0 <= mt_qhead (ms_core M) + 1). lia.
  - change (mt_qhead (ms_core M) + 1 <= ms_qtail M). lia.
  - change (Zlength (stats_set_propagations prop_count (ms_stats M)) = 11).
    unfold stats_set_propagations. rewrite Zlength_replace_Znth. lia.
Qed.

(* Reduce the concrete scan-begin overlay before a projection proof.  The
   semantic frontier, heap and trail arguments remain explicit at each call. *)
Local Ltac msat_scan_begin_fields Mscan :=
  unfold Mscan;
  cbn [msolver_propagation_scan_begin msolver_propagation_scan
    msolver_propagation_update mt_set_qhead].

Lemma propagation_scan_begin_initial__analyze :
  forall n F A_arr K M0 M p simp_count prop_count cf words,
    solver_shape M ->
    solver_propagation_inv n F A_arr K M ->
    msolver_seed_shadow M ->
    propagation_caller_frame M0 M ->
    ms_qtail M - mt_qhead (ms_core M) > 0 ->
    ms_qtail M = Zlength (mt_trail (ms_core M)) ->
    p = Znth (mt_qhead (ms_core M)) (mt_trail (ms_core M)) 0 ->
    words = Znth p (ms_wm M) nil ->
    cf = 0 ->
    let Mscan := msolver_propagation_scan_begin M simp_count prop_count in
      solver_shape Mscan /\
      msolver_seed_shadow Mscan /\
      propagation_caller_frame M0 Mscan /\
      propagation_scan_frontier M Mscan p /\
      solver_propagation_scan_semantics
        n F A_arr K Mscan p cf (@nil Z) words.
Proof.
  intros n F A_arr K M0 M p simp_count prop_count cf words
    Hshape Hinv Hseed Hcaller Hpending Hqtail Hp Hwords Hcf.
  set (Mscan := msolver_propagation_scan_begin M simp_count prop_count).
  assert (Hshape_scan : solver_shape Mscan)
    by (unfold Mscan; apply solver_shape_propagation_scan_begin;
        assumption).
  pose proof (propagation_inv_context_facts__analyze n F A_arr K M Hinv)
    as [Hroot [Hlevel [Hfrontier [Hheap_ready [Hreasonless [Hwf Hwm_exact]]]]]].
  assert (Hwf_scan : mtrail_wf n (ms_core Mscan)) by
    (unfold Mscan;
     cbn [msolver_propagation_scan_begin msolver_propagation_scan msolver_propagation_update];
     apply mtrail_wf_set_qhead;
     [exact Hwf | pose proof (mtw_qhead_range Hwf); lia]).
  assert (Hweak_scan_sum : solver_propagation_weak n F A_arr K Mscan).
  { unfold Mscan. apply propagation_weak_scan_begin_sum__analyze;
      [exact Hinv | exact Hshape_scan | exact Hwf_scan]. }
  pose proof (mtw_qhead_range Hwf) as Hqrange.
  assert (Hlit : lit_wf_c n p).
  { pose proof (Forall_Znth_elim _ _ (mt_trail (ms_core M)) 0
      (mt_qhead (ms_core M)) (mtw_trail_lits Hwf)
      ltac:(rewrite <- Hqtail; lia)) as Hlit0.
    replace (mt_qhead (ms_core M) - 0) with (mt_qhead (ms_core M))
      in Hlit0 by lia.
    rewrite <- Hp in Hlit0. exact Hlit0. }
  assert (Htrue : lit_true (mt_assigns (ms_core M)) p).
  { unfold lit_true.
    pose proof (Forall_Znth_elim _ _ (mt_trail (ms_core M)) 0
      (mt_qhead (ms_core M)) (mtw_trail_true Hwf)
      ltac:(rewrite <- Hqtail; lia)) as Htrue0.
    replace (mt_qhead (ms_core M) - 0) with (mt_qhead (ms_core M))
      in Htrue0 by lia.
    rewrite <- Hp in Htrue0. exact Htrue0. }
  assert (Hprocessed : processed (mt_assigns (ms_core M))
    (mt_trail (ms_core M)) (mt_qhead (ms_core M) + 1) p).
  { split; [exact Htrue|]. exists (mt_qhead (ms_core M)).
    split; [lia|symmetry; exact Hp]. }
  pose proof Hheap_ready as Hheap_ready0.
  assert (Hfull_scan : heap_covers n (msolver_heap Mscan)
    (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
    (mt_qhead (ms_core Mscan))).
  { unfold Mscan.
    cbn [msolver_propagation_scan_begin
      msolver_propagation_scan msolver_propagation_update mt_set_qhead msolver_heap].
    destruct Hheap_ready as [Hfull | [Hlevels [Hqueue Hexcept]]].
    - eapply heap_covers_qhead_mono
        with (qhead := mt_qhead (ms_core M))
             (qhead' := mt_qhead (ms_core M) + 1);
        [exact Hfull|lia].
    - eapply heap_covers_except_qhead
        with (qhead := mt_qhead (ms_core M))
             (qhead' := mt_qhead (ms_core M) + 1)
             (v0 := lit_var_c p).
      + rewrite Hp. exact Hexcept.
      + lia.
      + msat_scan_begin_fields Mscan.
        change (Znth (lit_var_c p) (mt_assigns (ms_core M)) 0 <> 0).
        unfold lit_true in Htrue. rewrite Htrue. apply lit_sig_nonzero.
      + exists (mt_qhead (ms_core M)). split; [lia|].
        msat_scan_begin_fields Mscan.
        change (lit_var_c (Znth (mt_qhead (ms_core M))
          (mt_trail (ms_core M)) 0) = lit_var_c p).
        rewrite <- Hp. reflexivity. }
  assert (Hlevel_focus : level_of (msolver_view n Mscan) (lit_var_c p) =
    Some (Zlength (mt_lim (ms_core Mscan)))).
  { unfold Mscan.
    cbn [msolver_propagation_scan_begin
      msolver_propagation_scan msolver_propagation_update mt_set_qhead msolver_view view_of].
    change (option_map
      (fun k => level_of_index (ms_core M) (Z.of_nat k))
      (trail_pos (ms_core M) (lit_var_c p)) =
      Some (Zlength (mt_lim (ms_core M)))).
    assert (Hvar : lit_var_c p =
      trail_var (ms_core M) (mt_qhead (ms_core M))).
    { unfold trail_var. rewrite Hp. reflexivity. }
    rewrite Hvar.
    rewrite (trail_pos_of_index (ms_core M) (mt_qhead (ms_core M))
      (mtw_trail_nodup Hwf)) by (rewrite <- Hqtail; lia).
    cbn. rewrite Z2Nat.id by lia. f_equal.
    apply prop_level_unpropagated_current; [exact Hlevel|lia]. }
  assert (Hfrontier_scan : minisat_watch_frontier_except n (msolver_db Mscan)
    (mt_assigns (ms_core Mscan)) (mt_trail (ms_core Mscan))
    (mt_qhead (ms_core Mscan)) (lit_denote p)).
  { unfold Mscan.
    cbn [msolver_propagation_scan_begin
      msolver_propagation_scan msolver_propagation_update mt_set_qhead msolver_db].
    unfold minisat_watch_frontier in Hfrontier.
    unfold minisat_watch_frontier_except.
    eapply watch_frontier_open; [exact Hfrontier|].
    intro l. split.
    + intros [packed [Hpacked [Hden [Hpacktrue [i [Hi Htrail]]]]]].
      change (lit_true (mt_assigns (ms_core M)) packed) in Hpacktrue.
      change (Znth i (mt_trail (ms_core M)) 0 = packed) in Htrail.
      destruct Hi as [Hi0 Hi1].
      destruct (Z_lt_ge_dec i (mt_qhead (ms_core M))) as [Hbefore|Hcurrent].
      * left. exists packed.
        split; [exact Hpacked|].
        split; [exact Hden|].
        split; [exact Hpacktrue|].
        exists i. split; [split; assumption|exact Htrail].
      * right.
        change (i < mt_qhead (ms_core M) + 1) in Hi1.
        assert (i = mt_qhead (ms_core M)) by lia. subst i.
        assert (Hpacked_eq : packed = p).
        { rewrite <- Hp in Htrail. symmetry. exact Htrail. }
        rewrite Hpacked_eq in Hden. symmetry. exact Hden.
    + intros [Hold|Heq].
      * destruct Hold as [packed [Hpacked [Hden [Hpacktrue [i [Hi Htrail]]]]]].
        exists packed.
        split; [exact Hpacked|].
        split; [exact Hden|].
        split; [exact Hpacktrue|].
        exists i. split.
        -- change (0 <= i < mt_qhead (ms_core M) + 1).
           destruct Hi as [Hi0 Hi1]. lia.
        -- change (Znth i (mt_trail (ms_core M)) 0 = packed).
           exact Htrail.
      * subst l. exists p.
        split; [exact Hlit|].
        split; [reflexivity|].
        split; [exact Htrue|].
        exists (mt_qhead (ms_core M)). split.
        -- change (0 <= mt_qhead (ms_core M) <
             mt_qhead (ms_core M) + 1). lia.
        -- change (Znth (mt_qhead (ms_core M))
             (mt_trail (ms_core M)) 0 = p).
           symmetry. exact Hp. }
  assert (Hfocus_scan : minisat_focus_scan_carrier (msolver_db Mscan) p
    (minisat_processed n (mt_assigns (ms_core Mscan))
      (mt_trail (ms_core Mscan)) (mt_qhead (ms_core Mscan))) (@nil Z) words).
  { unfold Mscan.
    cbn [msolver_propagation_scan_begin
      msolver_propagation_scan msolver_propagation_update mt_set_qhead msolver_db].
    replace words with (Znth p (ms_wm M) nil).
    - eapply minisat_focus_scan_init with (n := n) (wm := ms_wm M);
        [exact Hwm_exact|].
      exact Hlit. }
  assert (Hrollback : propagation_heap_rollback_ready Mscan p).
  { unfold Mscan.
    eapply propagation_heap_rollback_ready_scan_begin with (n := n).
    - exact Hwf.
    - exact Hheap_ready.
    - lia.
    - exact Hqtail.
    - exact Hp. }
  assert (Hscan_frontier : propagation_scan_frontier M Mscan p).
  { unfold propagation_scan_frontier.
    msat_scan_begin_fields Mscan.
    split; [reflexivity|].
    split; [exact Hp|].
    split.
    - change (ms_qtail M <= ms_qtail M). lia.
    - split.
      + apply sublist_self. exact Hqtail.
      + exact Hrollback. }
  assert (Hscan_sem : solver_propagation_scan_semantics n F A_arr
    K Mscan p cf (@nil Z) words).
  { left.
    split; [exact Hcf|].
    split; [exact Hweak_scan_sum|].
    split.
    + apply prop_level_qhead_advance; [exact Hlevel|].
      msat_scan_begin_fields Mscan. lia.
    + split; [left; exact Hfull_scan|].
      split; [exact Hfull_scan|].
      split.
      * msat_scan_begin_fields Mscan. exact Hreasonless.
      * split; [exact Hlevel_focus|].
        split; [exact Hlit|].
        split.
        -- msat_scan_begin_fields Mscan. exact Hprocessed.
        -- split; [exact Hfrontier_scan|exact Hfocus_scan]. }
  split; [exact Hshape_scan|].
  split.
  + unfold Mscan.
    cbn [msolver_propagation_scan_begin
      msolver_propagation_scan msolver_propagation_update]. exact Hseed.
  + split.
    * unfold propagation_caller_frame in *.
      unfold Mscan.
      cbn [msolver_propagation_scan_begin msolver_propagation_scan
        msolver_propagation_update mt_set_qhead] in *. exact Hcaller.
    * split; [exact Hscan_frontier|exact Hscan_sem].
Qed.

