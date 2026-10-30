From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_support_lib.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** ===== group: solver_reducedb ===== *)
Lemma rem_zero_mod_zero__reducedb : forall x : Z,
  0 <= x -> x % 2 = 0 -> x mod 2 = 0.
Proof.
  intros x Hnonneg Hrem.
  assert (Htwo : (2 : Z) <> 0) by lia.
  apply (proj2 (Z.mod_divide x 2 Htwo)).
  apply (proj1 (Z.rem_divide x 2 Htwo)).
  exact Hrem.
Qed.

Lemma clause_rep_refold__reducedb : forall c lits activity,
  0 <= Zlength lits -> 0 < c -> c mod 2 = 0 ->
  msat_fp32_nonnegative activity ->
  (clause_hdr_addr c # Int |-> clause_hdr_word msat_true (Zlength lits)) **
  ((clause_act_addr c (Zlength lits) # Float |-> activity) **
   IntArray.seg (clause_lits_addr c) 0 (Zlength lits) lits)
  |-- MiniSatClause.rep c msat_true lits.
Proof.
  intros c lits activity Hlen Hpos Heven Hactivity.
  unfold MiniSatClause.rep, activity_state, msat_true.
  Exists activity.
  msat_entailer_with lia.
Qed.

Lemma msolver_inv_reorder_learnts__reducedb :
  forall n F A_arr A_inst M db_sorted,
  Permutation (ms_learnt M) db_sorted ->
  msolver_inv n F A_arr A_inst M ->
  msolver_inv n F A_arr A_inst (msolver_reorder_learnts M db_sorted).
Proof.
  intros n F A_arr A_inst M db_sorted Hdb Hinv.
  destruct Hinv as [Hweak Hprop Hfront Hheap Hreason].
  assert (Hfull : Permutation (msolver_db M)
      (msolver_db (msolver_reorder_learnts M db_sorted))).
  { unfold msolver_db. cbn. apply Permutation_app_head. exact Hdb. }
  destruct Hweak as
    [Hsize Hn Hshape HF HA Htrail Hlevel Hroot Hassump Hincl Hsat
     Hstable Hrent Hrinj Himpl Hwf Hmatches Himplied Hcomplete Hlearnt
     Hprob Hbinary Hreasons Hhead Hbin Hwmap Htags Hheapwf Hinc Hseed].
  constructor.
  - constructor; cbn in *.
    + exact Hsize.
    + exact Hn.
    + exact Hshape.
    + exact HF.
    + exact HA.
    + exact Htrail.
    + exact Hlevel.
    + exact Hroot.
    + exact Hassump.
    + exact Hincl.
    + exact Hsat.
    + exact Hstable.
    + exact Hrent.
    + exact Hrinj.
    + exact Himpl.
    + eapply db_wf_perm; [exact Hfull | exact Hwf].
    + exact Hmatches.
    + unfold db_implied in *. cbn in *.
      eapply Forall_of_perm; [apply Permutation_map; exact Hdb | exact Himplied].
    + exact Hcomplete.
    + unfold learnt_db in *. cbn in *.
      eapply Forall_of_perm; [exact Hdb | exact Hlearnt].
    + exact Hprob.
    + intro Hin. apply Hbinary.
      eapply Permutation_in;
        [apply Permutation_sym; apply Permutation_map; exact Hfull | exact Hin].
    + eapply reasons_match_db_incl; [| exact Hreasons].
      intros x Hx. eapply Permutation_in; [exact Hfull | exact Hx].
    + unfold reason_head_ok in *. cbn in *.
      intros v co Hv Htag Hnz Hin.
      eapply Hhead; try eassumption.
      eapply Permutation_in;
        [apply Permutation_sym; exact Hfull | exact Hin].
    + exact Hbin.
    + eapply wmap_exact_perm_db; [exact Hfull | exact Hwmap].
    + exact Htags.
    + exact Hheapwf.
    + exact Hinc.
    + exact Hseed.
  - exact Hprop.
  - unfold minisat_watch_frontier, watch_frontier in *.
    eapply Forall_of_perm;
      [apply minisat_watch_occurrences_perm; exact Hfull | exact Hfront].
  - exact Hheap.
  - exact Hreason.
Qed.

Lemma db_remove_ptr_split__reducedb :
  forall p co pre post,
    ~ In p (map fst pre) ->
    db_remove_ptr p (pre ++ (p, co) :: post) = pre ++ post.
Proof.
  intros p co pre. induction pre as [|[q cq] pre IH]; intros post Hfresh.
  - change (db_remove_ptr p ((p, co) :: post) = post).
    change ((if Z.eq_dec p p then post else (p, co) :: db_remove_ptr p post) = post).
    destruct (Z.eq_dec p p); [reflexivity | contradiction].
  - cbn [map] in Hfresh. apply Decidable.not_or in Hfresh.
    destruct Hfresh as [Hqp Hpre].
    change
      ((if Z.eq_dec q p
        then pre ++ (p, co) :: post
        else (q, cq) :: db_remove_ptr p (pre ++ (p, co) :: post)) =
       (q, cq) :: (pre ++ post)).
    destruct (Z.eq_dec q p) as [Heq | Hne].
    + contradiction.
    + f_equal. apply IH. exact Hpre.
Qed.

Lemma wmap_remove_first_perm__reducedb :
  forall wm index word found wm',
    0 <= index < Zlength wm ->
    first_occurrence word (Znth index wm []) found ->
    wm' = wmap_remove_first wm index word found ->
    Zlength wm' = Zlength wm /\
    forall l, 0 <= l < Zlength wm ->
      Permutation (Znth l wm [])
        ((if index =? l then [word] else []) ++ Znth l wm' []).
Proof.
  intros wm index word found wm' Hindex Hfound ->.
  split.
  - unfold wmap_remove_first. apply Zlength_replace_Znth.
  - intros l Hl. unfold wmap_remove_first.
    destruct (index =? l) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst l. rewrite Znth_replace_Znth_Same by exact Hindex.
      simpl. apply first_occurrence_perm. exact Hfound.
    + apply Z.eqb_neq in Heq.
      rewrite Znth_replace_Znth_Diff by (try exact Hindex; try exact Hl; congruence).
      simpl. apply Permutation_refl.
Qed.

Lemma obj_wf_watch_indices_distinct__reducedb :
  forall n co,
    obj_wf n co ->
    lit_neg_c (co_watch0 co) <> lit_neg_c (co_watch1 co).
Proof.
  intros n [lits learnt] [Hlen [_ Hnodup]] Heq.
  destruct lits as [|a [|b rest]].
  - cbn in Hlen. lia.
  - cbn in Hlen. lia.
  - cbn [co_watch0 co_watch1] in Heq.
    cbn [map] in Hnodup.
    inversion Hnodup as [|? ? Hnotin _]; subst.
    apply Hnotin. left.
    change (lit_neg_c a = lit_neg_c b) in Heq.
    pose proof (f_equal lit_var_c Heq) as Hvars.
    rewrite !lit_var_c_neg in Hvars. symmetry. exact Hvars.
Qed.

Lemma clause_remove_result_wmap_diff__reducedb :
  forall n c co wm wm',
    obj_wf n co ->
    Zlength wm = 2 * n ->
    clause_remove_result c (co_lits co) wm wm' ->
    forall l, 0 <= l < 2 * n ->
      Permutation (Znth l wm [])
        (entry_watchers (c, co) l ++ Znth l wm' []).
Proof.
  intros n c co wm wm' Hobj Hwm Hremove.
  destruct Hremove as [found0 [found1 [wm0 [Hfound0 [Hwm0 [Hfound1 Hwm']]]]]].
  set (i0 := lit_neg_c (co_watch0 co)).
  set (i1 := lit_neg_c (co_watch1 co)).
  set (w0 := clause_watch_word c (co_lits co) (co_watch1 co)).
  set (w1 := clause_watch_word c (co_lits co) (co_watch0 co)).
  assert (Hi0 : 0 <= i0 < Zlength wm).
  { rewrite Hwm. unfold i0. apply lit_neg_c_wf. apply obj_wf_watch0. exact Hobj. }
  assert (Hi1 : 0 <= i1 < Zlength wm).
  { rewrite Hwm. unfold i1. apply lit_neg_c_wf. apply obj_wf_watch1. exact Hobj. }
  assert (Hne : i0 <> i1).
  { unfold i0, i1. apply obj_wf_watch_indices_distinct__reducedb
      with (n := n). exact Hobj. }
  change (first_occurrence w0 (Znth i0 wm []) found0) in Hfound0.
  change (wm0 = wmap_remove_first wm i0 w0 found0) in Hwm0.
  destruct (wmap_remove_first_perm__reducedb
    wm i0 w0 found0 wm0 Hi0 Hfound0 Hwm0) as [Hlen0 Hperm0].
  assert (Hi1' : 0 <= i1 < Zlength wm0) by (rewrite Hlen0; exact Hi1).
  change (first_occurrence w1 (Znth i1 wm0 []) found1) in Hfound1.
  change (wm' = wmap_remove_first wm0 i1 w1 found1) in Hwm'.
  destruct (wmap_remove_first_perm__reducedb
    wm0 i1 w1 found1 wm' Hi1' Hfound1 Hwm') as [_ Hperm1].
  assert (Hentry0 : entry_watchers (c, co) i0 = [w0]).
  { unfold entry_watchers, w0, i0, i1, co_watch0, co_watch1,
           clause_watch_word.
    rewrite leb3_ltb2, Z.eqb_refl.
    assert (E : (lit_neg_c (Znth 1 (co_lits co) 0) =?
                 lit_neg_c (Znth 0 (co_lits co) 0)) = false)
      by (apply Z.eqb_neq; intro Eeq; apply Hne;
          unfold i0, i1; symmetry; exact Eeq).
    rewrite E. apply app_nil_r. }
  assert (Hentry1 : entry_watchers (c, co) i1 = [w1]).
  { unfold entry_watchers, w1, i0, i1, co_watch0, co_watch1,
           clause_watch_word.
    rewrite leb3_ltb2, Z.eqb_refl.
    assert (E : (lit_neg_c (Znth 0 (co_lits co) 0) =?
                 lit_neg_c (Znth 1 (co_lits co) 0)) = false)
      by (apply Z.eqb_neq; intro Eeq; apply Hne;
          unfold i0, i1; exact Eeq).
    rewrite E. reflexivity. }
  intros l Hl.
  assert (Hlwm : 0 <= l < Zlength wm) by (rewrite Hwm; exact Hl).
  destruct (Z.eq_dec l i0) as [-> | Hli0].
  - rewrite Hentry0.
    assert (Hi0' : 0 <= i0 < Zlength wm0) by (rewrite Hlen0; exact Hi0).
    specialize (Hperm0 i0 Hi0).
    specialize (Hperm1 i0 Hi0').
    rewrite Z.eqb_refl in Hperm0.
    assert (E10 : (i1 =? i0) = false) by (apply Z.eqb_neq; congruence).
    rewrite E10 in Hperm1. simpl in Hperm0, Hperm1 |- *.
    eapply Permutation_trans; [exact Hperm0 |].
    apply perm_skip. exact Hperm1.
  - destruct (Z.eq_dec l i1) as [-> | Hli1].
    + rewrite Hentry1.
      specialize (Hperm0 i1 Hi1).
      specialize (Hperm1 i1 Hi1').
      assert (E01 : (i0 =? i1) = false) by (apply Z.eqb_neq; congruence).
      rewrite E01 in Hperm0. rewrite Z.eqb_refl in Hperm1.
      simpl in Hperm0, Hperm1 |- *.
      eapply Permutation_trans; eassumption.
    + assert (Hentry : entry_watchers (c, co) l = []).
      { unfold entry_watchers, i0, i1, co_watch0, co_watch1.
        assert (E0 : (lit_neg_c (Znth 0 (co_lits co) 0) =? l) = false)
          by (apply Z.eqb_neq; intro Eeq; apply Hli0; symmetry; exact Eeq).
        assert (E1 : (lit_neg_c (Znth 1 (co_lits co) 0) =? l) = false)
          by (apply Z.eqb_neq; intro Eeq; apply Hli1; symmetry; exact Eeq).
        rewrite E0, E1. reflexivity. }
      rewrite Hentry. simpl.
      assert (Hlwm0 : 0 <= l < Zlength wm0) by (rewrite Hlen0; exact Hlwm).
      specialize (Hperm0 l Hlwm).
      specialize (Hperm1 l Hlwm0).
      assert (E0 : (i0 =? l) = false)
        by (apply Z.eqb_neq; intro Eeq; apply Hli0; symmetry; exact Eeq).
      assert (E1 : (i1 =? l) = false)
        by (apply Z.eqb_neq; intro Eeq; apply Hli1; symmetry; exact Eeq).
      rewrite E0 in Hperm0. rewrite E1 in Hperm1. simpl in Hperm0, Hperm1.
      eapply Permutation_trans; eassumption.
Qed.

Lemma NoDup_delete_middle :
  forall (A : Type) (pre post : list A) (x : A),
    NoDup (pre ++ x :: post) -> NoDup (pre ++ post).
Proof.
  intros A pre. induction pre as [|a pre IH]; intros post x Hnd.
  - cbn in *. inversion Hnd. assumption.
  - cbn in *. inversion Hnd as [|? ? Hnot Htail]; subst.
    constructor.
    + intro Hin. apply Hnot. apply in_app_or in Hin.
      destruct Hin as [Hinpre | Hinpost].
      * apply in_or_app. left. exact Hinpre.
      * apply in_or_app. right. right. exact Hinpost.
    + apply IH with (x := x). exact Htail.
Qed.

Lemma Forall_delete_middle :
  forall (A : Type) (P : A -> Prop) pre post x,
    Forall P (pre ++ x :: post) -> Forall P (pre ++ post).
Proof.
  intros A P pre post x H.
  rewrite Forall_forall in H |- *. intros y Hy. apply H.
  apply in_app_or in Hy. destruct Hy as [Hinpre | Hinpost].
  - apply in_or_app. left. exact Hinpre.
  - apply in_or_app. right. right. exact Hinpost.
Qed.

Lemma db_wf_delete_middle__reducedb :
  forall n pre post e,
    db_wf n (pre ++ e :: post) -> db_wf n (pre ++ post).
Proof.
  intros n pre post e [Hkeys [Hptrs Hobjs]]. split.
  - rewrite !map_app in *. cbn [map] in Hkeys.
    apply NoDup_delete_middle with (x := fst e). exact Hkeys.
  - split.
    + apply Forall_delete_middle with (x := e). exact Hptrs.
    + apply Forall_delete_middle with (x := e). exact Hobjs.
Qed.

Lemma learnt_db_delete_middle__reducedb :
  forall pre post e,
    learnt_db (pre ++ e :: post) -> learnt_db (pre ++ post).
Proof.
  intros pre post e H. unfold learnt_db in *.
  apply Forall_delete_middle with (x := e). exact H.
Qed.

Lemma db_clauses_delete_middle__reducedb :
  forall pre post e,
    db_clauses (pre ++ e :: post) =
      db_clauses pre ++ denote_obj (snd e) :: db_clauses post /\
    db_clauses (pre ++ post) = db_clauses pre ++ db_clauses post.
Proof.
  intros. unfold db_clauses. rewrite !map_app. split; reflexivity.
Qed.

Lemma incl_delete_middle__reducedb :
  forall (A : Type) (pre post : list A) (x : A),
    incl (pre ++ post) (pre ++ x :: post).
Proof.
  intros A pre post x y Hy. apply in_app_or in Hy.
  apply in_or_app. destruct Hy as [Hy | Hy].
  - left. exact Hy.
  - right. right. exact Hy.
Qed.

Lemma NoDup_middle_fresh__reducedb :
  forall (A : Type) (pre post : list A) (x : A),
    NoDup (pre ++ x :: post) -> ~ In x pre.
Proof.
  intros A pre. induction pre as [|a pre IH]; intros post x Hnd Hin.
  - contradiction.
  - cbn in Hnd, Hin. inversion Hnd as [|? ? Hnot Htail]; subst.
    destruct Hin as [<- | Hin].
    + apply Hnot. apply in_or_app. right. left. reflexivity.
    + eapply IH; eassumption.
Qed.

Lemma db_wf_learnt_split_fresh__reducedb :
  forall n M pre post p co,
    db_wf n (msolver_db M) ->
    ms_learnt M = pre ++ (p, co) :: post ->
    ~ In p (map fst pre).
Proof.
  intros n M pre post p co [Hkeys _] Hsplit.
  assert (Hlearnt : NoDup (map fst (ms_learnt M))).
  { eapply NoDup_app_remove_l. unfold msolver_db in Hkeys.
    rewrite map_app in Hkeys. exact Hkeys. }
  rewrite Hsplit, map_app in Hlearnt. cbn [map] in Hlearnt.
  eapply NoDup_middle_fresh__reducedb. exact Hlearnt.
Qed.

Lemma reason_word_ok_delete_middle__reducedb :
  forall t v pre post p co w r,
    w <> p ->
    reason_word_ok t v (pre ++ (p, co) :: post) w r ->
    reason_word_ok t v (pre ++ post) w r.
Proof.
  intros t v pre post p co w r Hne H.
  unfold reason_word_ok, db_lookup in *.
  destruct (w =? 0); [exact H |].
  destruct H as [Hassigned H]. split; [exact Hassigned |].
  destruct (is_tag w); [exact H |].
  destruct H as [co' [Hin Hr]]. exists co'. split; [|exact Hr].
  apply in_app_or in Hin. apply in_or_app.
  destruct Hin as [Hin | Hin].
  - left. exact Hin.
  - cbn in Hin. destruct Hin as [Heq | Hin].
    + exfalso. apply Hne. injection Heq. auto.
    + right. exact Hin.
Qed.

Lemma reasons_match_delete_middle__reducedb :
  forall n t pre post p co words r,
    Zlength words = n ->
    clause_unlocked_words p words ->
    reasons_match n t (pre ++ (p, co) :: post) words r ->
    reasons_match n t (pre ++ post) words r.
Proof.
  intros n t pre post p co words r Hlen Hunlocked Hmatch v Hv.
  eapply reason_word_ok_delete_middle__reducedb.
  - unfold clause_unlocked_words in Hunlocked.
    eapply Forall_Znth_elim; [exact Hunlocked | rewrite Hlen; exact Hv].
  - apply Hmatch. exact Hv.
Qed.

Lemma minisat_watch_frontier_delete_middle__reducedb :
  forall n pre post e assigns trail qhead,
    minisat_watch_frontier n (pre ++ e :: post) assigns trail qhead ->
    minisat_watch_frontier n (pre ++ post) assigns trail qhead.
Proof.
  intros n pre post e assigns trail qhead H.
  unfold minisat_watch_frontier in *.
  eapply watch_frontier_thin; [|exact H].
  intros o Ho. unfold minisat_watch_occurrences in *.
  apply in_map_iff in Ho. destruct Ho as [x [<- Hx]].
  apply in_map. eapply incl_delete_middle__reducedb. exact Hx.
Qed.

Lemma clause_remove_result_length__reducedb :
  forall c lits wm wm',
    clause_remove_result c lits wm wm' -> Zlength wm' = Zlength wm.
Proof.
  intros c lits wm wm' [found0 [found1 [wm0 [_ [-> [_ ->]]]]]].
  unfold wmap_remove_first.
  rewrite !Zlength_replace_Znth. reflexivity.
Qed.

Lemma solver_shape_remove_clause__reducedb :
  forall M p wm stats,
    solver_shape M ->
    Zlength wm = 2 * ms_size M ->
    Zlength stats = 11 ->
    solver_shape (msolver_remove_clause M true p wm stats).
Proof. msat_shape_remove_clause. Qed.

Lemma msolver_inv_weak_remove_clause_core :
  forall n F A_arr A_inst M from_learnt c co pre post wm stats,
    let M' := msolver_remove_clause M from_learnt c wm stats in
    msolver_inv_weak n F A_arr A_inst M ->
    msolver_db M = pre ++ (c, co) :: post ->
    msolver_db M' = pre ++ post ->
    clause_remove_result c (co_lits co) (ms_wm M) wm ->
    clause_unlocked_words c (ms_reason_words M) ->
    solver_shape M' -> db_matches_cnf F M' -> db_implied F M' ->
    db_complete F M' -> learnt_db (ms_learnt M') -> prob_db (ms_prob M') ->
    msolver_inv_weak n F A_arr A_inst M'.
Proof.
  intros n F A_arr A_inst M from_learnt c co pre post wm stats M'
    Hinv HoldDB HnewDB Hremove Hunlocked Hshape Hmatches Himplied Hcomplete Hlearnt Hprob.
  assert (Hobj : obj_wf n co).
  { eapply db_wf_obj; [exact (msw_db_wf Hinv)|].
    rewrite HoldDB. apply in_or_app. right. left. reflexivity. }
  assert (Hwm0 : Zlength (ms_wm M) = 2 * n)
    by exact (proj1 (msw_wmap_exact Hinv)).
  assert (Hwm : Zlength wm = 2 * n).
  { rewrite (clause_remove_result_length__reducedb
      c (co_lits co) (ms_wm M) wm Hremove).
    exact (proj1 (msw_wmap_exact Hinv)). }
  constructor.
  - unfold M'. cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_size Hinv).
  - exact (msw_n_range Hinv).
  - exact Hshape.
  - exact (msw_F_wf Hinv).
  - exact (msw_A_wf Hinv).
  - unfold M'. cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_trail_wf Hinv).
  - unfold M'. cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_level_bound Hinv).
  - unfold M'. cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_root_range Hinv).
  - unfold M'. cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_assumptions Hinv).
  - exact (msw_assump_incl Hinv).
  - unfold M'. cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_assump_sat Hinv).
  - eapply stable_view_installed_irrel;
      [reflexivity | reflexivity | exact (msw_stable Hinv)].
  - pose proof (msw_reasons_ent Hinv) as H.
    unfold reasons_entailed, msolver_view, view_of in H |- *.
    cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ] in H |- *.
    exact H.
  - pose proof (msw_reasons_inj Hinv) as H.
    unfold reasons_var_injective, msolver_view, view_of in H |- *.
    cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ] in H |- *.
    exact H.
  - unfold M'. cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_trail_impl Hinv).
  - rewrite HnewDB.
    eapply db_wf_delete_middle__reducedb.
    rewrite <- HoldDB. exact (msw_db_wf Hinv).
  - exact Hmatches.
  - exact Himplied.
  - exact Hcomplete.
  - exact Hlearnt.
  - exact Hprob.
  - change (~ In (ms_binary M) (map fst (msolver_db M'))).
    intro Hin. apply (msw_binary_out Hinv).
    rewrite HnewDB in Hin. rewrite HoldDB, !map_app in *.
    eapply incl_delete_middle__reducedb. exact Hin.
  - change (reasons_match n (ms_core M) (msolver_db M')
      (ms_reason_words M) (ms_reason_of M)).
    rewrite HnewDB.
    eapply reasons_match_delete_middle__reducedb
      with (pre := pre) (p := c) (co := co).
    + rewrite (msw_size Hinv).
      apply solver_shape_reasons_len. exact (msw_shape Hinv).
    + exact Hunlocked.
    + rewrite <- HoldDB. exact (msw_reasons_mem Hinv).
  - pose proof (msw_reason_head Hinv) as Hhead.
    unfold reason_head_ok in Hhead |- *.
    cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ] in Hhead |- *.
    intros v co' Hv Htag Hnz Hin.
    apply (Hhead v co'); try assumption.
    rewrite HoldDB. eapply incl_delete_middle__reducedb.
    change (In (Znth v (ms_reason_words M) 0, co') (msolver_db M')) in Hin.
    rewrite HnewDB in Hin. exact Hin.
  - pose proof (msw_reason_bin Hinv) as H.
    unfold binary_reason_same_level in H |- *.
    cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ] in H |- *.
    exact H.
  - change (wmap_exact n (msolver_db M') wm).
    rewrite HnewDB.
    eapply wmap_remove_clause with (e := (c, co)).
    + rewrite <- HoldDB. exact (msw_wmap_exact Hinv).
    + exact Hwm.
    + eapply clause_remove_result_wmap_diff__reducedb;
        eassumption.
  - pose proof (msw_tags_clear Hinv) as H.
    unfold solver_tags_clear in H |- *.
    cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ] in H |- *.
    exact H.
  - unfold M', msolver_heap.
  cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_heap_wf Hinv).
  - unfold M'. cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_cla_inc_nonnegative Hinv).
  - pose proof (msw_seed Hinv) as H.
    unfold msolver_seed_ok in H |- *.
    cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ] in H |- *.
    exact H.
Qed.

Theorem msolver_inv_weak_remove_learnt__reducedb :
  forall n F A_arr A_inst M c co pre post wm stats,
    msolver_inv_weak n F A_arr A_inst M ->
    ms_learnt M = pre ++ (c, co) :: post ->
    ~ In c (map fst pre) ->
    clause_remove_result c (co_lits co) (ms_wm M) wm ->
    Zlength stats = 11 ->
    clause_unlocked_words c (ms_reason_words M) ->
    msolver_inv_weak n F A_arr A_inst
      (msolver_remove_clause M true c wm stats).
Proof.
  intros n F A_arr A_inst M c co pre post wm stats
    Hinv Hsplit Hfresh Hremove Hstats Hunlocked.
  set (M' := msolver_remove_clause M true c wm stats).
  set (fullpre := ms_prob M ++ pre).
  assert (HoldDB : msolver_db M = fullpre ++ (c, co) :: post).
  { unfold fullpre, msolver_db. rewrite Hsplit, app_assoc. reflexivity. }
  assert (HnewDB : msolver_db M' = fullpre ++ post).
  { unfold M', fullpre, msolver_db, msolver_remove_clause,
           msolver_propagation_overlay, msolver_propagation_update. cbn.
    rewrite Hsplit, db_remove_ptr_split__reducedb by exact Hfresh.
    rewrite app_assoc. reflexivity. }
  eapply msolver_inv_weak_remove_clause_core
    with (co := co) (pre := fullpre) (post := post).
  - exact Hinv.
  - exact HoldDB.
  - exact HnewDB.
  - exact Hremove.
  - exact Hunlocked.
  - unfold M'. apply solver_shape_remove_clause__reducedb;
      [exact (msw_shape Hinv) | | exact Hstats].
    rewrite (clause_remove_result_length__reducedb
      c (co_lits co) (ms_wm M) wm Hremove).
    apply solver_shape_wm_len. exact (msw_shape Hinv).
  - pose proof (msw_db_matches Hinv) as H.
    unfold db_matches_cnf in H |- *.
    cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact H.
  - pose proof (msw_db_implied Hinv) as H.
    unfold db_implied in H |- *.
    change (Forall (entails_clause F)
      (db_clauses (db_remove_ptr c (ms_learnt M)))).
    rewrite Hsplit,
      db_remove_ptr_split__reducedb by exact Hfresh.
    rewrite Hsplit in H.
    destruct (db_clauses_delete_middle__reducedb
                pre post (c, co)) as [Hold Hnew].
    rewrite Hnew. eapply Forall_delete_middle.
    rewrite <- Hold. exact H.
  - pose proof (msw_db_complete Hinv) as H.
    unfold db_complete in H |- *.
    cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact H.
  - change (learnt_db (db_remove_ptr c (ms_learnt M))).
    rewrite Hsplit,
      db_remove_ptr_split__reducedb by exact Hfresh.
    eapply learnt_db_delete_middle__reducedb.
    pose proof (msw_learnt_db Hinv) as H. rewrite Hsplit in H. exact H.
  - cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_prob_db Hinv).
Qed.

Theorem msolver_inv_remove_learnt__reducedb :
  forall n F A_arr A_inst M c co pre post wm stats,
    msolver_inv n F A_arr A_inst M ->
    ms_learnt M = pre ++ (c, co) :: post ->
    ~ In c (map fst pre) ->
    clause_remove_result c (co_lits co) (ms_wm M) wm ->
    Zlength stats = 11 ->
    clause_unlocked_words c (ms_reason_words M) ->
    msolver_inv n F A_arr A_inst
      (msolver_remove_clause M true c wm stats).
Proof.
  intros n F A_arr A_inst M c co pre post wm stats
    Hinv Hsplit Hfresh Hremove Hstats Hunlocked.
  constructor.
  - eapply msolver_inv_weak_remove_learnt__reducedb;
      [exact (msi_weak Hinv) | exact Hsplit | exact Hfresh |
       exact Hremove | exact Hstats | exact Hunlocked].
  - cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msi_prop_level Hinv).
  - change (minisat_watch_frontier n
      (msolver_db (msolver_remove_clause M true c wm stats))
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M))).
    assert (HoldDB :
      msolver_db M = (ms_prob M ++ pre) ++ (c, co) :: post).
    { unfold msolver_db. rewrite Hsplit, app_assoc. reflexivity. }
    assert (HnewDB :
      msolver_db (msolver_remove_clause M true c wm stats) =
        (ms_prob M ++ pre) ++ post).
    { unfold msolver_db, msolver_remove_clause, msolver_propagation_overlay, msolver_propagation_update.
      cbn. rewrite Hsplit,
        db_remove_ptr_split__reducedb by exact Hfresh.
      rewrite app_assoc. reflexivity. }
    rewrite HnewDB.
    eapply minisat_watch_frontier_delete_middle__reducedb.
    rewrite <- HoldDB. exact (msi_watch_frontier Hinv).
  - cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update msolver_heap].
    exact (msi_heap_covers Hinv).
  - pose proof (msi_reasonless_current Hinv) as H.
    unfold current_reasonless_earliest, msolver_view, view_of in H |- *.
    cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ] in H |- *.
    exact H.
Qed.

Lemma map_fst_db_remove_ptr_split__reducedb :
  forall p db pre post,
    map fst db = pre ++ p :: post ->
    ~ In p pre ->
    map fst (db_remove_ptr p db) = pre ++ post.
Proof.
  intros p db. induction db as [|[q co] db IH];
    intros pre post Hmap Hfresh.
  - destruct pre; simpl in Hmap; discriminate.
  - destruct pre as [|x pre].
    + change (q :: map fst db = p :: post) in Hmap.
      pose proof (f_equal
        (fun xs : list Z => match xs with [] => 0 | y :: _ => y end)
        Hmap) as Hqp.
      pose proof (f_equal (@List.tl Z) Hmap) as Htail.
      cbn in Hqp, Htail.
      change
        (map fst (db_remove_ptr p ((q, co) :: db)) = post).
      unfold db_remove_ptr at 1.
      destruct (Z.eq_dec (fst (q, co)) p) as [Heq | Hneq].
      * exact Htail.
      * exfalso. apply Hneq. change (q = p). exact Hqp.
    + change (q :: map fst db = x :: (pre ++ p :: post)) in Hmap.
      pose proof (f_equal
        (fun xs : list Z => match xs with [] => 0 | y :: _ => y end)
        Hmap) as Hqx.
      pose proof (f_equal (@List.tl Z) Hmap) as Htail.
      cbn in Hqx, Htail. subst x.
      apply Decidable.not_or in Hfresh.
      destruct Hfresh as [Hpq Hfresh].
      change
        (map fst (db_remove_ptr p ((q, co) :: db)) =
          q :: (pre ++ post)).
      unfold db_remove_ptr at 1.
      destruct (Z.eq_dec (fst (q, co)) p) as [Heq | Hneq].
      * exfalso. apply Hpq. change (q = p) in Heq. exact Heq.
      * cbn [map]. f_equal. eapply IH; eassumption.
Qed.

Lemma db_compaction_inv_remove_current__reducedb :
  forall n F A_arr A_inst M words i j c wm stats,
    msolver_inv_weak n F A_arr A_inst M ->
    db_compaction_inv M words i j ->
    i < Zlength words ->
    c = Znth i words 0 ->
    db_compaction_inv (msolver_remove_clause M true c wm stats)
      words (i + 1) j.
Proof.
  intros n F A_arr A_inst M words i j c wm stats Hinv Hcomp Hilt ->.
  destruct Hcomp as [Hj [Hji [Hi Hmap]]].
  unfold db_compaction_inv. split; [exact Hj |]. split; [lia |].
  split; [lia |].
  assert (Hsuffix :
    sublist i (Zlength words) words =
      Znth i words 0 :: sublist (i + 1) (Zlength words) words).
  { rewrite (sublist_split i (Zlength words) (i + 1) words) by lia.
    rewrite (sublist_single 0 i words) by lia. reflexivity. }
  assert (Hlearnt_keys : NoDup (map fst (ms_learnt M))).
  { destruct (msw_db_wf Hinv) as [Hkeys _].
    eapply NoDup_app_remove_l. unfold msolver_db in Hkeys.
    rewrite map_app in Hkeys. exact Hkeys. }
  rewrite Hmap, Hsuffix in Hlearnt_keys.
  assert (Hfresh : ~ In (Znth i words 0) (sublist 0 j words)).
  { eapply NoDup_middle_fresh__reducedb. exact Hlearnt_keys. }
  change
    (map fst
       (db_remove_ptr (Znth i words 0) (ms_learnt M)) =
     sublist 0 j words ++
       sublist (i + 1) (Zlength words) words).
  eapply map_fst_db_remove_ptr_split__reducedb.
  - rewrite Hmap, Hsuffix. reflexivity.
  - exact Hfresh.
Qed.

Lemma msolver_remove_learnt_split_proj__reducedb :
  forall M c co pre post wm stats,
    ms_learnt M = pre ++ (c, co) :: post ->
    ~ In c (map fst pre) ->
    ms_learnt (msolver_remove_clause M true c wm stats) = pre ++ post.
Proof.
  intros M c co pre post wm stats Hsplit Hfresh.
  unfold msolver_remove_clause, msolver_propagation_overlay, msolver_propagation_update.
  cbn. rewrite Hsplit.
  rewrite db_remove_ptr_split__reducedb by exact Hfresh.
  reflexivity.
Qed.

Lemma solver_db_mutation_frame_at_remove_learnt__reducedb :
  forall s M lvl c wm stats,
    solver_db_mutation_frame_at s
      (msolver_remove_clause M true c wm stats) lvl =
    solver_db_mutation_frame_at s M lvl.
Proof. reflexivity. Qed.

(** ===== group: solver_search ===== *)
Lemma trail_pos_some_var_range__search :
  forall n t v k,
    mtrail_wf n t -> trail_pos t v = Some k -> 0 <= v < n.
Proof.
  intros n t v k Hwf Hpos.
  pose proof (trail_pos_bound _ _ _ Hpos) as Hk.
  pose proof (trail_pos_var _ _ _ Hpos) as Hv.
  unfold trail_var in Hv.
  assert (Hin : In (Znth (Z.of_nat k) (mt_trail t) 0) (mt_trail t)).
  { apply Znth_In. lia. }
  pose proof (proj1 (Forall_forall _ _) (mtw_trail_lits Hwf) _ Hin) as Hwfl.
  unfold lit_wf_c in Hwfl. unfold lit_var_c in Hv.
  subst v. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma level_of_some_var_range__search :
  forall n M v d,
    mtrail_wf n (ms_core M) ->
    level_of (msolver_view n M) v = Some d ->
    0 <= v < n.
Proof.
  intros n M v d Hwf Hlev.
  unfold msolver_view, view_of in Hlev. simpl in Hlev.
  destruct (trail_pos (ms_core M) v) as [k|] eqn:Hpos; [|discriminate].
  eapply trail_pos_some_var_range__search; eauto.
Qed.

Lemma analyze_words_wf__search :
  forall n F A_arr A_inst M focus words,
    analysis_cancel_ready n F A_arr (PropagationStable A_inst) M focus ->
    analyze_clause_cert n F M words ->
    Forall (lit_wf_c n) words.
Proof.
  intros n F A_arr A_inst M focus words Hready Hcert.
  destruct Hready as [M0 [Hcancel [Hequiv _]]].
  destruct Hcancel as [Hweak _].
  destruct Hweak as [_ Hinvw].
  assert (Htw : mtrail_wf n (ms_core M)).
  { destruct Hequiv as [_ [_ [_ [Hcore _]]]]. rewrite Hcore.
    exact (msw_trail_wf Hinvw). }
  destruct Hcert as [Huip _].
  destruct Huip as [_ [_ [l [rest [Heq [Hhead Htail]]]]]].
  apply Forall_forall. intros w Hw.
  assert (Hin : In (lit_denote w) (lits_denote words))
    by (apply lits_denote_in; exact Hw).
  rewrite Heq in Hin.
  assert (Hlev : exists d,
    level_of (msolver_view n M) (literal_var (lit_denote w)) = Some d).
  { destruct Hin as [Hl | Hr].
    - subst l. eauto.
    - destruct (proj1 (Forall_forall _ _) Htail _ Hr) as [dk [Hdk _]].
      eauto. }
  destruct Hlev as [d Hlev].
  rewrite lit_var_c_denote in Hlev.
  pose proof (level_of_some_var_range__search
                _ _ _ _ Htw Hlev) as Hrange.
  unfold lit_var_c in Hrange. unfold lit_wf_c.
  destruct Hrange as [Hlo Hhi].
  assert (Hwnonneg : 0 <= w).
  { destruct (Z_lt_le_dec w 0) as [Hneg|]; [|assumption].
    exfalso.
    assert (Hle : w / 2 <= (-1) / 2)
      by (apply Z.div_le_mono; lia).
    change ((-1) / 2) with (-1) in Hle. lia. }
  split; [exact Hwnonneg|].
  destruct (Z_lt_le_dec w (2 * n)) as [|Hge]; [assumption|].
  exfalso.
  assert (Hle : (2 * n) / 2 <= w / 2)
    by (apply Z.div_le_mono; lia).
  replace (2 * n) with (n * 2) in Hle by lia.
  rewrite Z.div_mul in Hle by lia. lia.
Qed.

Lemma analyze_words_nodup__search :
  forall n F M words,
    analyze_clause_cert n F M words ->
    NoDup (map lit_var_c words).
Proof.
  intros n F M words [Huip _].
  destruct Huip as [_ [Hnd _]].
  rewrite map_literal_var_lits_denote in Hnd. exact Hnd.
Qed.


Lemma msolver_view_cancel_project__search :
  forall n M level orderpos order root,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    msolver_view n
      (msolver_cancel_project M level orderpos order root) =
    view_of n (mt_cancel (ms_core M) level) (ms_reason_of M)
      (msolver_clauses M).
Proof. msat_view_cancel_project. Qed.

Lemma db_complete_cancel_project__search :
  forall n F M level orderpos order root,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    db_complete F M ->
    db_complete F
      (msolver_cancel_project M level orderpos order root).
Proof. msat_db_complete_cancel_project. Qed.

Lemma reason_head_ok_cancel_project__search :
  forall n M level orderpos order root,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    Zlength (ms_reason_words M) = n ->
    n = ms_size M ->
    reason_head_ok M ->
    reason_head_ok
      (msolver_cancel_project M level orderpos order root).
Proof. msat_reason_head_ok_cancel_project. Qed.

Lemma binary_reason_same_level_cancel_project__search :
  forall n M level orderpos order root,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    Zlength (ms_reason_words M) = n ->
    n = ms_size M ->
    binary_reason_same_level M ->
    binary_reason_same_level
      (msolver_cancel_project M level orderpos order root).
Proof. msat_binary_reason_cancel_project. Qed.

Lemma decisions_upto_cancel_below__search :
  forall n t root level,
    mtrail_wf n t -> 0 <= root <= level ->
    level < Zlength (mt_lim t) ->
    decisions_upto (mt_cancel t level) root = decisions_upto t root.
Proof.
  intros n t root level Hwf Hroots Hlevel.
  assert (Hroot : 0 <= root < Zlength (mt_lim t)) by lia.
  assert (Hlevel' : 0 <= level < Zlength (mt_lim t)) by lia.
  pose proof (lim_lt_trail n t level Hwf Hlevel') as Hcut.
  pose proof (mtw_lim_sorted Hwf) as Hsorted.
  unfold decisions_upto.
  rewrite mt_cancel_lim, mt_cancel_trail.
  rewrite ztake_ztake by lia.
  apply map_ext_in. intros b Hb'.
  assert (Hdlen : Zlength (ztake root (mt_lim t)) = root).
  { apply Zlength_ztake. lia. }
  destruct (In_Znth_index _ _ Hb') as [j [Hj Hjval]].
  rewrite Hdlen in Hj.
  rewrite Znth_ztake in Hjval by lia.
  assert (Hjb_root : b < Znth root (mt_lim t) 0).
  { rewrite <- Hjval.
    apply strict_sorted_Znth; [exact Hsorted|lia|lia|exact (proj2 Hroot)]. }
  assert (Hroot_cut :
      Znth root (mt_lim t) 0 <= Znth level (mt_lim t) 0).
  { destruct (Z.eq_dec root level) as [->|Hne]; [lia|].
    pose proof (strict_sorted_Znth (mt_lim t) j root Hsorted) as Hjroot.
    pose proof (strict_sorted_Znth (mt_lim t) root level Hsorted) as Hrlevel.
    specialize (Hjroot ltac:(lia) ltac:(lia) ltac:(lia)).
    specialize (Hrlevel ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  assert (Hb0 : 0 <= b).
  { pose proof (mtw_lim_range Hwf) as HF. rewrite Forall_forall in HF.
    assert (Hinb : In b (mt_lim t)) by (eapply In_ztake; eauto).
    pose proof (HF b Hinb). lia. }
  rewrite Znth_ztake by lia. reflexivity.
Qed.

Lemma assump_sat_cancel_below__search :
  forall n t root level A,
    mtrail_wf n t -> 0 <= root <= level ->
    level < Zlength (mt_lim t) ->
    Forall (assump_true_at_root t root) A ->
    Forall (assump_true_at_root (mt_cancel t level) root) A.
Proof.
  intros n t root level A Hwf Hroots Hlevel Hsat.
  assert (Hroot : 0 <= root < Zlength (mt_lim t)) by lia.
  assert (Hlevel' : 0 <= level < Zlength (mt_lim t)) by lia.
  rewrite Forall_forall in Hsat |- *.
  intros a Ha.
  destruct (Hsat a Ha) as [Heval Halevel].
  destruct (eval_partial_literal_assigned (mt_pv t) a true Heval)
    as [b Hcell].
  assert (Hvarin : In (literal_var a) (map lit_var_c (mt_trail t))).
  { destruct (List.in_dec Z.eq_dec (literal_var a)
      (map lit_var_c (mt_trail t))) as [Hin|Hnin]; [exact Hin|].
    exfalso.
    pose proof ((proj2 (mt_pv_none_iff n t (literal_var a) Hwf)) Hnin)
      as Hnone. rewrite Hcell in Hnone. discriminate. }
  destruct (In_Znth_index _ _ Hvarin) as [i [Hi Hival]].
  rewrite Zlength_map_Z in Hi.
  assert (Hvar : lit_var_c (Znth i (mt_trail t) 0) = literal_var a).
  { rewrite <- Hival. symmetry.
    apply (Znth_map Z Z lit_var_c (mt_trail t) i 0 0). exact Hi. }
  assert (Hlevel_i : level_of_index t i <= root).
  { rewrite <- (mtw_levels_agree Hwf i Hi).
    unfold trail_var. rewrite Hvar. exact Halevel. }
  assert (Hi_root : i < Znth root (mt_lim t) 0).
  { unfold level_of_index in Hlevel_i.
    apply strict_sorted_count_suffix; [exact (mtw_lim_sorted Hwf)|exact Hlevel_i|].
    exact Hroot. }
  assert (Hroot_cut :
      Znth root (mt_lim t) 0 <= Znth level (mt_lim t) 0).
  { destruct (Z.eq_dec root level) as [->|Hne]; [lia|].
    apply Z.lt_le_incl.
    apply strict_sorted_Znth; [exact (mtw_lim_sorted Hwf)|lia|lia|lia]. }
  assert (Hkeepvar : In (literal_var a)
      (map lit_var_c (mt_trail (mt_cancel t level)))).
  { rewrite mt_cancel_trail. apply in_map_iff.
    exists (Znth i (ztake (Znth level (mt_lim t) 0) (mt_trail t)) 0).
    split.
    - rewrite Znth_ztake by lia. exact Hvar.
    - apply Znth_In. rewrite Zlength_ztake by
        (pose proof (lim_lt_trail n t level Hwf Hlevel'); lia). lia. }
  assert (Hkeep : mt_pv (mt_cancel t level) (literal_var a) =
      mt_pv t (literal_var a)).
  { apply (mt_pv_cancel_keep n t level (literal_var a)); assumption. }
  split.
  - unfold eval_partial_literal in Heval |- *. rewrite Hkeep. exact Heval.
  - rewrite mt_cancel_levels. exact Halevel.
Qed.

Lemma msolver_inv_weak_cancel_below__search :
  forall n F A_arr A_inst M level orderpos order,
    msolver_inv_weak n F A_arr A_inst M ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    ms_root_level M <= level ->
    heap_wf (ms_size M) (heap_of_lists order orderpos) ->
    incl (ms_order M) order ->
    cancel_reinserted (heap_of_lists order orderpos)
      (mt_trail (ms_core M))
      (Znth level (mt_lim (ms_core M)) 0)
      (mt_qhead (ms_core M)) ->
    msolver_inv_weak n F A_arr A_inst
      (msolver_cancel_project M level orderpos order
                              (ms_root_level M)).
Proof.
  intros n F A_arr A_inst M level orderpos order
    Hweak Hlevel Hrootle Hheap Hincl Hre.
  pose proof (msw_trail_wf Hweak) as Htrail.
  pose proof (mtrail_wf_cancel n (ms_core M) level Htrail Hlevel) as Htrail'.
  pose proof (view_of_cancel n (ms_core M) (ms_reason_of M)
    (msolver_clauses M) level Htrail Hlevel) as Hrestrict.
  assert (Hwords : Zlength (ms_reason_words M) = n).
  { pose proof (msw_shape Hweak) as Hshape.
    unfold solver_shape in Hshape.
    rewrite <- (msw_size Hweak) in Hshape. tauto. }
  assert (Hroot_nonneg : 0 <= ms_root_level M).
  { pose proof (msw_root_range Hweak). lia. }
  assert (Hroot_range :
      0 <= ms_root_level M < Zlength (mt_lim (ms_core M))).
  { pose proof (msw_root_range Hweak). lia. }
  assert (Hdec :
      decisions_upto (mt_cancel (ms_core M) level) (ms_root_level M) =
      decisions_upto (ms_core M) (ms_root_level M)).
  { apply decisions_upto_cancel_below__search with (n := n);
      [exact Htrail|lia|lia]. }
  assert (Hassump :
      Forall (assump_true_at_root (mt_cancel (ms_core M) level)
        (ms_root_level M)) A_arr).
  { apply assump_sat_cancel_below__search with (n := n);
      [exact Htrail|lia|lia|exact (msw_assump_sat Hweak)]. }
  refine {| msw_size := _; msw_n_range := _; msw_shape := _;
    msw_F_wf := _; msw_A_wf := _; msw_trail_wf := _;
    msw_level_bound := _; msw_root_range := _; msw_assumptions := _;
    msw_assump_incl := _; msw_assump_sat := _; msw_stable := _;
    msw_reasons_ent := _; msw_reasons_inj := _; msw_trail_impl := _;
    msw_db_wf := _; msw_db_matches := _; msw_db_implied := _;
    msw_db_complete := _; msw_learnt_db := _; msw_prob_db := _;
    msw_binary_out := _; msw_reasons_mem := _; msw_reason_head := _;
    msw_reason_bin := _; msw_wmap_exact := _; msw_tags_clear := _;
    msw_heap_wf := _; msw_cla_inc_nonnegative := _; msw_seed := _ |}.
  - simpl. exact (msw_size Hweak).
  - exact (msw_n_range Hweak).
  - apply solver_shape_cancel_project__search
      with (n := n);
      [exact (msw_shape Hweak)|exact Htrail|exact Hlevel|
       exact Hheap|exact Hroot_nonneg].
  - exact (msw_F_wf Hweak).
  - exact (msw_A_wf Hweak).
  - exact Htrail'.
  - simpl. rewrite Zlength_ztake by lia.
    pose proof (msw_level_bound Hweak). lia.
  - simpl. rewrite Zlength_ztake by lia.
    pose proof (msw_root_range Hweak). lia.
  - simpl. rewrite Hdec. exact (msw_assumptions Hweak).
  - exact (msw_assump_incl Hweak).
  - exact Hassump.
  - assert (Hrootold :
      0 <= level <= current_level (msolver_view n M)).
    { rewrite msolver_view_current_level.
      pose proof (msw_root_range Hweak) as Hr.
      lia. }
    rewrite (msolver_view_cancel_project__search
      n M level orderpos order (ms_root_level M) Htrail Hlevel).
    apply stable_view_restrict__search
      with (old := msolver_view n M) (root := level);
      [exact (msw_stable Hweak)|exact Hrestrict|exact Hrootold].
  - rewrite (msolver_view_cancel_project__search
      n M level orderpos order (ms_root_level M) Htrail Hlevel).
    apply reasons_entailed_restrict
      with (old := msolver_view n M) (root := level);
      [exact (msw_reasons_ent Hweak)|exact Hrestrict].
  - rewrite (msolver_view_cancel_project__search
      n M level orderpos order (ms_root_level M) Htrail Hlevel).
    apply reasons_var_injective_restrict
      with (old := msolver_view n M) (root := level);
      [exact (msw_reasons_inj Hweak)|exact Hrestrict].
  - apply trail_implied_cancel with (n := n) (F := F) (t := ms_core M)
      (level := level);
      [exact Htrail|exact Hlevel|exact (msw_trail_impl Hweak)].
  - simpl. exact (msw_db_wf Hweak).
  - simpl. exact (msw_db_matches Hweak).
  - simpl. exact (msw_db_implied Hweak).
  - apply db_complete_cancel_project__search
      with (n := n) (M := M) (level := level);
      [exact Htrail|exact Hlevel|exact (msw_db_complete Hweak)].
  - simpl. exact (msw_learnt_db Hweak).
  - simpl. exact (msw_prob_db Hweak).
  - simpl. exact (msw_binary_out Hweak).
  - simpl. apply reasons_match_cancel__canceluntil_cap;
      [exact Htrail|exact Hlevel|exact Hwords|exact (msw_reasons_mem Hweak)].
  - apply reason_head_ok_cancel_project__search
      with (n := n) (M := M) (level := level);
      [exact Htrail|exact Hlevel|exact Hwords|exact (msw_size Hweak)|
       exact (msw_reason_head Hweak)].
  - apply binary_reason_same_level_cancel_project__search
      with (n := n) (M := M) (level := level);
      [exact Htrail|exact Hlevel|exact Hwords|exact (msw_size Hweak)|
       exact (msw_reason_bin Hweak)].
  - simpl. exact (msw_wmap_exact Hweak).
  - simpl. exact (msw_tags_clear Hweak).
  - simpl. rewrite (msw_size Hweak). exact Hheap.
  - simpl. exact (msw_cla_inc_nonnegative Hweak).
  - simpl. exact (msw_seed Hweak).
Qed.

Lemma current_reasonless_cancel_project__search :
  forall n F A_arr A_inst M level orderpos order root,
    msolver_inv_weak n F A_arr A_inst M ->
    current_reasonless_earliest n M ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    root = ms_root_level M ->
    current_reasonless_earliest n
      (msolver_cancel_project M level orderpos order root).
Proof.
  intros n F A_arr A_inst M level orderpos order root
    Hweak Hready Hlevel Hroot.
  pose proof (msw_trail_wf Hweak) as Htrail.
  assert (Hroot_nonneg : 0 <= root).
  { rewrite Hroot. exact (proj1 (msw_root_range Hweak)). }
  pose proof (view_of_cancel n (ms_core M) (ms_reason_of M)
    (msolver_clauses M) level Htrail Hlevel) as Hrestrict.
  pose proof (msolver_view_cancel_project__search
    n M level orderpos order root Htrail Hlevel) as Eview.
  assert (Hwords : Zlength (ms_reason_words M) = n).
  { pose proof (msw_shape Hweak) as Hshape.
    unfold solver_shape in Hshape. rewrite <- (msw_size Hweak) in Hshape.
    tauto. }
  unfold current_reasonless_earliest in *.
  intros d Hd v Hlevnew Hzeronew.
  assert (Hlennew :
      Zlength (mt_lim (ms_core
        (msolver_cancel_project M level orderpos order root))) = level).
  { simpl. rewrite Zlength_ztake by lia. reflexivity. }
  rewrite Hlennew in Hd.
  change (root < d <= level) in Hd.
  assert (Hdidx : 0 <= d - 1 < level) by lia.
  rewrite Eview in Hlevnew.
  destruct Hrestrict as [Hcur [Hdb Hagree]].
  specialize (Hagree v).
  destruct (level_of (msolver_view n M) v) as [d0|] eqn:Hlevold.
  - destruct (Z.leb d0 level) eqn:Hle.
    + assert (Hlevold_view :
          level_of (view_of n (ms_core M) (ms_reason_of M)
            (msolver_clauses M)) v = Some d0) by exact Hlevold.
      rewrite Hlevold_view, Hle in Hagree.
      destruct Hagree as [Hassign [Hlev [Hreason Hrankeq]]].
      rewrite Hlevnew in Hlev. inversion Hlev; subst d0.
      assert (Hkeep : In v (map lit_var_c
          (ztake (Znth level (mt_lim (ms_core M)) 0)
            (mt_trail (ms_core M))))).
      { rewrite <- mt_cancel_trail.
        destruct (in_dec Z.eq_dec v
          (map lit_var_c (mt_trail (mt_cancel (ms_core M) level))))
          as [Hin|Hnotin]; [exact Hin|].
        exfalso.
        pose proof (proj2 (trail_pos_none_iff
          (mt_cancel (ms_core M) level) v) Hnotin) as Hnone.
        change (option_map
          (fun k : nat => level_of_index (mt_cancel (ms_core M) level)
            (Z.of_nat k))
          (trail_pos (mt_cancel (ms_core M) level) v) = Some d)
          in Hlevnew.
        rewrite Hnone in Hlevnew. discriminate. }
      assert (Hnot : ~ In v (map lit_var_c
          (zdrop (Znth level (mt_lim (ms_core M)) 0)
            (mt_trail (ms_core M))))).
      { intro Hin.
        eapply NoDup_app_disjoint.
        - rewrite <- map_ztake_zdrop. exact (mtw_trail_nodup Htrail).
        - exact Hkeep.
        - exact Hin. }
      assert (Hv : 0 <= v < n).
      { eapply level_of_some_var_range__search;
          [exact Htrail|exact Hlevold]. }
      assert (Hrange : forall x,
          In x (zdrop (Znth level (mt_lim (ms_core M)) 0)
            (mt_trail (ms_core M))) ->
          0 <= lit_var_c x < Zlength (ms_reason_words M)).
      { intros x Hx. rewrite Hwords. apply lit_var_c_in_range.
        pose proof (mtw_trail_lits Htrail) as Hlits.
        rewrite Forall_forall in Hlits. apply Hlits.
        apply In_zdrop in Hx. exact Hx. }
      assert (Holdzero : Znth v (ms_reason_words M) 0 = 0).
      { change (Znth v
          (clear_vars (zdrop (Znth level (mt_lim (ms_core M)) 0)
            (mt_trail (ms_core M))) (ms_reason_words M)) 0 = 0)
          in Hzeronew.
        assert (Hsame : Znth v
            (clear_vars (zdrop (Znth level (mt_lim (ms_core M)) 0)
              (mt_trail (ms_core M))) (ms_reason_words M)) 0 =
            Znth v (ms_reason_words M) 0).
        { apply clear_vars_notin.
          - rewrite Hwords. exact Hv.
          - exact Hrange.
          - exact Hnot. }
        rewrite Hsame in Hzeronew. exact Hzeronew. }
      destruct (Hready d ltac:(simpl in Hd; lia)
        v Hlevold Holdzero) as [Hnone Hrankold].
      change (assignment_rank
        (view_of n (ms_core M) (ms_reason_of M) (msolver_clauses M)) v =
        Some (Z.to_nat (Znth (d - 1) (mt_lim (ms_core M)) 0)))
        in Hrankold.
      split.
      * simpl. rewrite clear_reason_fun_notin by exact Hnot. exact Hnone.
      * rewrite Eview. rewrite Hrankeq, Hrankold.
        f_equal. f_equal. simpl.
        rewrite Znth_ztake by exact Hdidx. reflexivity.
    + assert (Hlevold_view :
          level_of (view_of n (ms_core M) (ms_reason_of M)
            (msolver_clauses M)) v = Some d0) by exact Hlevold.
      rewrite Hlevold_view, Hle in Hagree.
      destruct Hagree as [_ [Hnone _]]. rewrite Hnone in Hlevnew. discriminate.
  - assert (Hlevold_view :
        level_of (view_of n (ms_core M) (ms_reason_of M)
          (msolver_clauses M)) v = None) by exact Hlevold.
    rewrite Hlevold_view in Hagree.
    destruct Hagree as [_ [Hnone _]]. rewrite Hnone in Hlevnew. discriminate.
Qed.

Lemma record_ready_cert_cancel_project__search :
  forall n F A_arr A_inst M focus words level orderpos order root,
    msolver_inv_weak n F A_arr A_inst M ->
    analysis_cancel_ready n F A_arr (PropagationStable A_inst) M focus ->
    analyze_clause_cert n F M words ->
    analyze_backjump_cert n M words level ->
    root = ms_root_level M ->
    record_ready_cert n F
      (msolver_cancel_project M level orderpos order root) words.
Proof.
  intros n F A_arr A_inst M focus words level orderpos order root
    Hweak Hready Hcert Hback Hroot.
  pose proof Hcert as Hcert0.
  pose proof (msw_trail_wf Hweak) as Htrail.
  destruct Hcert as [Huip Hrootcert].
  destruct Huip as [[Hent Hfalse] [Hnoduplits Hassert]].
  destruct Hback as [Hlen [Hleveldef [Hrootle [Hlevel
    [Hheadlevel Htaillevels]]]]].
  assert (Hwfwords : Forall (lit_wf_c n) words).
  { eapply analyze_words_wf__search; eauto. }
  assert (Hnodup : NoDup (map lit_var_c words)).
  { eapply analyze_words_nodup__search; exact Hcert0. }
  assert (Hlevel_bounds :
      0 <= level < Zlength (mt_lim (ms_core M))).
  { pose proof (msw_root_range Hweak) as Hroot_range. lia. }
  pose proof (view_of_cancel n (ms_core M) (ms_reason_of M)
    (msolver_clauses M) level Htrail Hlevel_bounds) as Hrestrict.
  destruct Hrestrict as [Hcur [Hdb Hagree]].
  pose proof (mtrail_wf_cancel n (ms_core M) level Htrail
    Hlevel_bounds) as Htrailnew.
  unfold record_ready_cert.
  repeat split.
  - exact Hlen.
  - exact Hwfwords.
  - exact Hnodup.
  - exact Hent.
  - set (v := lit_var_c (Znth 0 words 0)).
    assert (Hv : 0 <= v < n).
    { unfold v. apply lit_var_c_in_range.
      eapply Forall_Znth_elim; [exact Hwfwords|lia]. }
    specialize (Hagree v).
    rewrite lit_var_c_denote in Hheadlevel.
    assert (Hheadlevel_view :
      level_of (view_of n (ms_core M) (ms_reason_of M)
        (msolver_clauses M)) v =
      Some (Zlength (mt_lim (ms_core M)))).
    { unfold v. exact Hheadlevel. }
    rewrite Hheadlevel_view in Hagree.
    assert (Hgt :
      (Zlength (mt_lim (ms_core M)) <=? level) = false).
    { apply Z.leb_gt. lia. }
    rewrite Hgt in Hagree.
    destruct Hagree as [Hnone _].
    change (mt_pv (mt_cancel (ms_core M) level) v = None) in Hnone.
    rewrite mt_pv_nonneg in Hnone by lia.
    apply lbool_val_none in Hnone.
    pose proof (Forall_Znth_elim _ _ _ 0 v (mtw_cells Htrailnew)) as Hcell.
    rewrite (mtw_assigns_len Htrailnew) in Hcell.
    specialize (Hcell Hv). unfold lbool_cell in Hcell.
    destruct Hcell as [Hneg|[Hzero|Hpos]].
    + exfalso. apply (proj2 Hnone). exact Hneg.
    + exact Hzero.
    + exfalso. apply (proj1 Hnone). exact Hpos.
  - unfold clause_false in Hfalse |- *.
    intros l Hl.
    assert (Hlall : In l (lits_denote words)).
    { destruct (lits_denote words) as [|a ls] eqn:E; simpl in Hl |- *;
        [contradiction|right; exact Hl]. }
    pose proof (Hfalse l Hlall) as Holdfalse.
    rewrite Forall_forall in Htaillevels.
    destruct (Htaillevels l Hl) as [d [Hlev Hd]].
    specialize (Hagree (literal_var l)).
    assert (Hlev_view :
      level_of (view_of n (ms_core M) (ms_reason_of M)
        (msolver_clauses M)) (literal_var l) = Some d) by exact Hlev.
    rewrite Hlev_view in Hagree.
    assert (Hleb : (d <=? level) = true) by (apply Z.leb_le; exact Hd).
    rewrite Hleb in Hagree.
    destruct Hagree as [Hassign _].
    change (mt_pv (mt_cancel (ms_core M) level) (literal_var l) =
      mt_pv (ms_core M) (literal_var l)) in Hassign.
    assert (Heval :
      eval_partial_literal (mt_pv (mt_cancel (ms_core M) level)) l =
      eval_partial_literal (mt_pv (ms_core M)) l).
    { unfold eval_partial_literal.
      destruct (mt_pv (mt_cancel (ms_core M) level) (literal_var l))
        eqn:Enew;
      destruct (mt_pv (ms_core M) (literal_var l)) eqn:Eold;
      try discriminate Hassign; inversion Hassign; reflexivity. }
    change (eval_partial_literal (mt_pv (mt_cancel (ms_core M) level)) l =
      Some false).
    rewrite Heval. exact Holdfalse.
  - intro Hsingle.
    rewrite Hsingle in Hleveldef.
    assert (Hltb : Z.ltb 1 1 = false) by reflexivity.
    rewrite Hltb in Hleveldef.
    unfold solver_at_root. simpl.
    rewrite Zlength_ztake by lia. rewrite Hroot, Hleveldef. reflexivity.
Qed.

Lemma solver_shape_before_cancel_project__search :
  forall M0 M level orderpos order root,
    analysis_core_equiv M0 M ->
    solver_shape M0 ->
    Zlength (ms_orderpos M) = ms_size M ->
    solver_shape
      (msolver_cancel_project M level orderpos order root) ->
    solver_shape M.
Proof.
  intros M0 M level orderpos order root
    Hequiv Hshape0 Horderpos Hshapeback.
  unfold analysis_core_equiv in Hequiv.
  unfold solver_shape in Hshape0 |- *.
  unfold solver_shape, msolver_cancel_project, msolver_core_heap_update,
    heap_of_lists in Hshapeback; simpl in Hshapeback.
  intuition (try congruence; try lia).
Qed.

Lemma analysis_cancel_ready_weak__search :
  forall n F A_arr A_inst M focus,
    analysis_cancel_ready n F A_arr (PropagationStable A_inst) M focus ->
    solver_shape M ->
    ms_tags M = repeat_Z 0 n ->
    ms_tagged M = (@nil Z) ->
    msolver_inv_weak n F A_arr A_inst M.
Proof.
  intros n F A_arr A_inst M focus Hready Hshape Htags Htagged.
  destruct Hready as [M0 [Hcancel [Hequiv
    [Hheap [Hcovers [Hreasonless [Hfocus Hcla]]]]]]].
  destruct Hcancel as [[Hpending Hweak] Hcancel_rest].
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason &
     Eprob & Elearnt & Ebinary &
     Ebinarylits & Ewm & Emodel &
     Edecay & Eseed & Ependq & Erootpending & Esimpassigns & Esimpprops).
  assert (Edb : msolver_db M = msolver_db M0).
  { unfold msolver_db. rewrite Eprob, Elearnt. reflexivity. }
  assert (Eview : msolver_view n M = msolver_view n M0).
  { unfold msolver_view. rewrite Ecore, Ereason.
    unfold msolver_clauses. rewrite Edb. reflexivity. }
  refine {| msw_size := _; msw_n_range := _; msw_shape := _;
    msw_F_wf := _; msw_A_wf := _; msw_trail_wf := _;
    msw_level_bound := _; msw_root_range := _; msw_assumptions := _;
    msw_assump_incl := _; msw_assump_sat := _; msw_stable := _;
    msw_reasons_ent := _; msw_reasons_inj := _; msw_trail_impl := _;
    msw_db_wf := _; msw_db_matches := _; msw_db_implied := _;
    msw_db_complete := _; msw_learnt_db := _; msw_prob_db := _;
    msw_binary_out := _; msw_reasons_mem := _; msw_reason_head := _;
    msw_reason_bin := _; msw_wmap_exact := _; msw_tags_clear := _;
    msw_heap_wf := _; msw_cla_inc_nonnegative := _; msw_seed := _ |}.
  - rewrite Esize. exact (msw_size Hweak).
  - exact (msw_n_range Hweak).
  - exact Hshape.
  - exact (msw_F_wf Hweak).
  - exact (msw_A_wf Hweak).
  - rewrite Ecore. exact (msw_trail_wf Hweak).
  - rewrite Ecore. exact (msw_level_bound Hweak).
  - rewrite Ecore, Eroot. exact (msw_root_range Hweak).
  - rewrite Ecore, Eroot. exact (msw_assumptions Hweak).
  - exact (msw_assump_incl Hweak).
  - rewrite Ecore, Eroot. exact (msw_assump_sat Hweak).
  - rewrite Eview. exact (msw_stable Hweak).
  - rewrite Eview. exact (msw_reasons_ent Hweak).
  - rewrite Eview. exact (msw_reasons_inj Hweak).
  - rewrite Ecore. exact (msw_trail_impl Hweak).
  - rewrite Edb. exact (msw_db_wf Hweak).
  - unfold db_matches_cnf. rewrite Eprob. exact (msw_db_matches Hweak).
  - unfold db_implied. rewrite Elearnt. exact (msw_db_implied Hweak).
  - unfold db_complete. rewrite Eprob, Ecore. exact (msw_db_complete Hweak).
  - rewrite Elearnt. exact (msw_learnt_db Hweak).
  - rewrite Eprob. exact (msw_prob_db Hweak).
  - rewrite Ebinary, Edb. exact (msw_binary_out Hweak).
  - rewrite Ecore, Edb, Ewords, Ereason. exact (msw_reasons_mem Hweak).
  - unfold reason_head_ok. rewrite Esize, Ewords, Edb.
    exact (msw_reason_head Hweak).
  - unfold binary_reason_same_level. rewrite Esize, Ewords, Ecore.
    exact (msw_reason_bin Hweak).
  - rewrite Edb, Ewm. exact (msw_wmap_exact Hweak).
  - unfold solver_tags_clear. split.
    + rewrite Htags. unfold repeat_Z.
      generalize (Z.to_nat n) as k. intro k.
      induction k as [|k IH]; simpl; constructor; auto.
    + exact Htagged.
  - exact Hheap.
  - exact Hcla.
  - unfold msolver_seed_ok. rewrite Eseed. exact (msw_seed Hweak).
Qed.

Lemma analysis_cancel_ready_cancel_facts__search :
  forall n F A_arr A_inst M focus,
    analysis_cancel_ready n F A_arr (PropagationStable A_inst) M focus ->
    ms_capacity_root_propagation_pending M = 0 /\
    prop_level (ms_core M) /\
    lit_wf_c n focus /\
    level_of (msolver_view n M) (lit_var_c focus) =
      Some (Zlength (mt_lim (ms_core M))) /\
    minisat_watch_frontier_except n (msolver_db M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) (lit_denote focus) /\
    heap_covers n (msolver_heap M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) /\
    current_reasonless_earliest n M.
Proof.
  intros n F A_arr A_inst M focus Hready.
  destruct Hready as
    [M0 [Hcancel [Hequiv [Hheap [Hcovers [Hreasonless [Hfocus Hcla]]]]]]].
  destruct Hcancel as
    [Hweakprop [Hprop [Hfocuswf [Hprocessed [Hfocus0
      [Hfront [Hheap0 [Hcovers0 Hreasonless0]]]]]]]].
  destruct Hweakprop as [Hpending Hweak].
  unfold analysis_core_equiv in Hequiv.
  destruct Hequiv as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason &
     Eprob & Elearnt & Ebinary &
     Ebinarylits & Ewm & Emodel &
     Edecay & Eseed & Ependq & Erootpending & Esimpassigns & Esimpprops).
  assert (Edb : msolver_db M = msolver_db M0).
  { unfold msolver_db. rewrite Eprob, Elearnt. reflexivity. }
  refine (conj _ _).
  { rewrite Erootpending. exact Hpending. }
  refine (conj _ _).
  { rewrite Ecore. exact Hprop. }
  refine (conj Hfocuswf _).
  refine (conj Hfocus _).
  refine (conj _ _).
  { rewrite Edb, Ecore. exact Hfront. }
  exact (conj Hcovers Hreasonless).
Qed.

Lemma assump_sat_cancel_at_root__search :
  forall n t root A,
    mtrail_wf n t -> 0 <= root < Zlength (mt_lim t) ->
    Forall (assump_true_at_root t root) A ->
    Forall (assump_true_at_root (mt_cancel t root) root) A.
Proof.
  intros n t root A Hwf Hroot Hsat.
  eapply assump_sat_cancel_below__search;
    [exact Hwf | lia | lia | exact Hsat].
Qed.

Lemma minisat_watch_frontier_cancel__search :
  forall n M level orderpos order root,
    mtrail_wf n (ms_core M) ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    Znth level (mt_lim (ms_core M)) 0 <= mt_qhead (ms_core M) ->
    minisat_watch_frontier n (msolver_db M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) ->
    minisat_watch_frontier n
      (msolver_db (msolver_cancel_project M level orderpos order root))
      (mt_assigns (ms_core
        (msolver_cancel_project M level orderpos order root)))
      (mt_trail (ms_core
        (msolver_cancel_project M level orderpos order root)))
      (mt_qhead (ms_core
        (msolver_cancel_project M level orderpos order root))).
Proof.
  intros n M level orderpos order root Hwf Hlevel Hbound Hfront.
  assert (Hprocessed : forall l,
      minisat_processed n (mt_assigns (mt_cancel (ms_core M) level))
        (mt_trail (mt_cancel (ms_core M) level))
        (mt_qhead (mt_cancel (ms_core M) level)) l ->
      minisat_processed n (mt_assigns (ms_core M))
        (mt_trail (ms_core M)) (mt_qhead (ms_core M)) l).
  { intros l [packed [Hpacked [Hden [Htrue [i [Hi Hlit]]]]]].
    exists packed. split; [exact Hpacked|]. split; [exact Hden|].
    split.
    - pose proof (mtw_trail_true Hwf) as Htrailtrue.
      rewrite Forall_forall in Htrailtrue. apply Htrailtrue.
      rewrite mt_cancel_qhead in Hi. rewrite mt_cancel_trail in Hlit.
      pose proof (lim_lt_trail n (ms_core M) level Hwf Hlevel) as Hb.
      rewrite Znth_ztake in Hlit by lia.
      rewrite <- Hlit. apply Znth_In. lia.
    - exists i. split.
      + rewrite mt_cancel_qhead in Hi. lia.
      + rewrite mt_cancel_qhead in Hi. rewrite mt_cancel_trail in Hlit.
        rewrite Znth_ztake in Hlit by lia. exact Hlit. }
  unfold minisat_watch_frontier in *.
  unfold msolver_cancel_project, msolver_core_heap_update,
    msolver_db in *; simpl in *.
  apply watch_frontier_shrink with
    (Pold := minisat_processed n (mt_assigns (ms_core M))
      (mt_trail (ms_core M)) (mt_qhead (ms_core M))).
  - exact Hfront.
  - intros l Hl. apply Hprocessed. exact Hl.
Qed.

Lemma msolver_inv_weak_cancel__search :
  forall n F A_arr A_inst M level orderpos order,
    msolver_inv_weak n F A_arr A_inst M ->
    0 <= level < Zlength (mt_lim (ms_core M)) ->
    level = ms_root_level M ->
    heap_wf (ms_size M) (heap_of_lists order orderpos) ->
    incl (ms_order M) order ->
    cancel_reinserted (heap_of_lists order orderpos)
      (mt_trail (ms_core M))
      (Znth level (mt_lim (ms_core M)) 0)
      (mt_qhead (ms_core M)) ->
    msolver_inv_weak n F A_arr A_inst
      (msolver_cancel_project M level orderpos order
                              (ms_root_level M)).
Proof.
  intros n F A_arr A_inst M level orderpos order
    Hweak Hlevel Hroot Hheap Hincl Hre.
  apply msolver_inv_weak_cancel_below__search;
    [ exact Hweak | exact Hlevel | lia | exact Hheap | exact Hincl
    | exact Hre ].
Qed.

Lemma fp64_eq_seed_exact__search : forall x z,
  seed_ok z -> fp64_eq x (Z_to_fp64 z) -> x = Z_to_fp64 z.
Proof.
  intros x z Hz Heq.
  assert (Hyfin : fp64_isFinite (Z_to_fp64 z)).
  { apply MSatFloatFacts.Z_to_fp64_i32_finite.
    unfold seed_ok in Hz. lia. }
  assert (Hxfin : fp64_isFinite x).
  { destruct x; simpl in Heq |- *; try reflexivity; try discriminate.
    pose proof (MSatFloatFacts.Z_to_fp64_i32_finite z) as Hfin.
    assert (Hzrange : -2147483648 <= z <= 2147483647).
    { unfold seed_ok in Hz. lia. }
    specialize (Hfin Hzrange).
    destruct (Z_to_fp64 z) eqn:Hy; simpl in Heq; try discriminate.
    all: try discriminate Hfin.
    all: cbv [fp64_eq fp64_compare Binary.Bcompare
      BinarySingleNaN.Bcompare] in Heq; try discriminate; try congruence.
    all: cbv [Binary.B2BSN BinarySingleNaN.B2SF SpecFloat.SFcompare]
      in Heq; try discriminate; try congruence.
    all: destruct s; discriminate. }
  assert (Hr : Binary.B2R 53 1024 x =
      Binary.B2R 53 1024 (Z_to_fp64 z)).
  { unfold fp64_eq, fp64_compare in Heq.
    rewrite Binary.Bcompare_correct in Heq by assumption.
    inversion Heq. apply Flocq.Core.Raux.Rcompare_Eq_inv. exact H0. }
  pose proof (MSatFloatFacts.Z_to_fp64_ge_one z) as Hypos.
  assert (Hzpos : 1 <= z <= 2147483647).
  { unfold seed_ok in Hz. lia. }
  specialize (Hypos Hzpos).
  assert (Hxstrict : Binary.is_finite_strict 53 1024 x = true).
  { destruct x; simpl in Hxfin, Hr |- *; try reflexivity; try discriminate.
    exfalso. rewrite <- Hr in Hypos. simpl in Hypos.
    pose proof (Flocq.Core.Raux.bpow_gt_0 Flocq.Core.Zaux.radix2 0).
    lra. }
  assert (Hystrict : Binary.is_finite_strict 53 1024 (Z_to_fp64 z) = true).
  { destruct (Z_to_fp64 z); simpl in Hyfin, Hypos |- *;
      try reflexivity; try discriminate.
    exfalso.
    pose proof (Flocq.Core.Raux.bpow_gt_0 Flocq.Core.Zaux.radix2 0).
    lra. }
  apply Binary.B2R_inj; assumption.
Qed.

Lemma solver_search_select_transition_intro__search :
  forall (A_inst A_arr : list literal) (F : cnf) (n : Z)
    (Mdb : msolver) (orderpos_now order_now : list Z)
    (seed_now : fp64) (seed_shadow_now next : Z),
  msolver_inv n F A_arr A_inst Mdb ->
  mt_qhead (ms_core Mdb) = ms_qtail Mdb ->
  ms_capacity_root_propagation_pending Mdb = 0 ->
  ms_model Mdb = @nil Z ->
  msat_fp32_positive_finite (ms_cla_decay Mdb) ->
  order_select_post (ms_size Mdb) next (ms_order Mdb)
    order_now orderpos_now (mt_assigns (ms_core Mdb))
    (mt_trail (ms_core Mdb)) (mt_qhead (ms_core Mdb)) ->
  seed_ok seed_shadow_now ->
  fp64_eq seed_now (Z_to_fp64 seed_shadow_now) ->
  exists Mselected,
    solver_search_select_transition n F A_arr A_inst Mdb next
      orderpos_now order_now seed_now
      (search_decision_stats_update (ms_stats Mdb)) Mselected.
Proof.
  intros A_inst A_arr F n Mdb orderpos_now order_now seed_now
    seed_shadow_now next Hinv Hqhead Hpending Hmodel Hdecay
    Hpost Hseedok Hseedeq.
  set (stats_after := search_decision_stats_update (ms_stats Mdb)).
  set (Mselected := msolver_search_select Mdb orderpos_now order_now
    seed_now stats_after).
  destruct Hpost as (Hheapwf & Hincl & Hcases).
  assert (Hseed_eq : seed_now = Z_to_fp64 seed_shadow_now).
  { apply fp64_eq_seed_exact__search; assumption. }
  assert (Hseedfinite : fp64_isFinite seed_now).
  { rewrite Hseed_eq. apply MSatFloatFacts.Z_to_fp64_i32_finite.
    unfold seed_ok in Hseedok. lia. }
  assert (Hseedshadow : msolver_seed_shadow Mselected).
  { exists seed_shadow_now. unfold Mselected, msolver_search_select.
    simpl. split; assumption. }
  pose proof (msi_shape Hinv) as Hshape0.
  assert (Hshape_selected : solver_shape Mselected).
  { unfold solver_shape in Hshape0 |- *.
    unfold Mselected, msolver_search_select, stats_after,
      search_decision_stats_update, stats_set_decisions. cbn in *.
    rewrite Zlength_replace_Znth.
    unfold order_heap_wf, heap_wf in Hheapwf.
    tauto. }
  assert (Hweak : msolver_inv_weak n F A_arr A_inst Mselected).
  { destruct (msi_weak Hinv).
    constructor; simpl; try assumption.
    all: try exact Hshape_selected.
    all: try (unfold Mselected, msolver_search_select,
      msolver_seed_ok; simpl; exact Hseedfinite).
    all: unfold msolver_heap, Mselected, msolver_search_select; cbn.
    all: unfold order_heap_wf in Hheapwf;
      rewrite (msi_size Hinv); exact Hheapwf. }
  assert (Htwo : 2 * n <= INT_MAX).
  { unfold solver_shape in Hshape0. pose proof (msi_size Hinv). lia. }
  exists Mselected.
  unfold solver_search_select_transition.
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  { unfold Mselected, msolver_search_select. simpl. exact Hdecay. }
  split; [reflexivity|].
  split.
  { rewrite (msi_size Hinv).
    exact (conj Hheapwf (conj Hincl Hcases)). }
  destruct Hcases as [[Hret [Hempty Hall]] | (Hnext & Hunassigned & Hexcept)].
  - left. split; [exact Hret|].
    unfold solver_search_model_ready.
    assert (Hbelow : assigned_below_qhead n
        (mt_assigns (ms_core Mdb)) (mt_trail (ms_core Mdb))
        (mt_qhead (ms_core Mdb))).
    { apply mtrail_wf_assigned_below_qhead.
      - exact (msi_trail_wf Hinv).
      - unfold solver_shape in Hshape0. lia. }
    assert (Hheapcov : heap_covers n (msolver_heap Mselected)
        (mt_assigns (ms_core Mselected)) (mt_trail (ms_core Mselected))
        (mt_qhead (ms_core Mselected))).
    { unfold heap_covers. intros v Hv Hmissing.
      unfold Mselected, msolver_search_select in *. simpl in *.
      split.
      - apply Hall. rewrite <- (msi_size Hinv). exact Hv.
      - apply Hbelow; [exact Hv|].
        apply Hall. rewrite <- (msi_size Hinv). exact Hv. }
    assert (Hinv_selected : msolver_inv n F A_arr A_inst Mselected).
    { refine {| msi_weak := Hweak;
                msi_prop_level := _;
                msi_watch_frontier := _;
                msi_heap_covers := Hheapcov;
                msi_reasonless_current := _ |}.
      - unfold Mselected, msolver_search_select; simpl.
        exact (msi_prop_level Hinv).
      - unfold Mselected, msolver_search_select; simpl.
        exact (msi_watch_frontier Hinv).
      - unfold current_reasonless_earliest in *.
        unfold Mselected, msolver_search_select; simpl.
        exact (msi_reasonless_current Hinv). }
    unfold Mselected, msolver_search_select in *. simpl in *.
    tauto.
  - right. unfold solver_search_selection_state.
    unfold Mselected, msolver_search_select in *. simpl in *.
    rewrite <- (msi_size Hinv) in Hnext.
    rewrite <- (msi_size Hinv) in Hexcept.
    split; [exact Hweak|].
    split; [exact (msi_prop_level Hinv)|].
    split; [exact (msi_watch_frontier Hinv)|].
    split; [exact (msi_reasonless_current Hinv)|].
    split; [exact Hpending|].
    split; [exact Hqhead|].
    split; [exact Hseedshadow|].
    split; [exact Hmodel|].
    split; [exact Hdecay|].
    split; [exact Htwo|].
    split; [exact Hnext|].
    split; [exact Hunassigned|].
    exact Hexcept.
Qed.

Lemma stats_without_decisions_update_join__search : forall p st,
  stats_without_decisions_rep p st **
    &(p # "stats_t" ->ₛ "decisions") # UInt64 |->
      unsigned_last_nbits (stats_decisions st + 1) 64 |--
  stats_rep p (search_decision_stats_update st).
Proof.
  intros p st.
  unfold stats_without_decisions_rep, stats_rep,
    search_decision_stats_update, stats_set_decisions.
  unfold stats_starts, stats_decisions, stats_propagations,
    stats_inspects, stats_conflicts, stats_clauses, stats_clauses_literals,
    stats_learnts, stats_learnts_literals, stats_max_literals, stats_tot_literals.
  Intros_p Hlen.
  rewrite (Znth_replace_Znth_Diff 0 st 1 0) by lia.
  rewrite (Znth_replace_Znth_Same 0 st 1) by lia.
  rewrite (Znth_replace_Znth_Diff 0 st 1 2) by lia.
  rewrite (Znth_replace_Znth_Diff 0 st 1 3) by lia.
  rewrite (Znth_replace_Znth_Diff 0 st 1 4) by lia.
  rewrite (Znth_replace_Znth_Diff 0 st 1 5) by lia.
  rewrite (Znth_replace_Znth_Diff 0 st 1 6) by lia.
  rewrite (Znth_replace_Znth_Diff 0 st 1 7) by lia.
  rewrite (Znth_replace_Znth_Diff 0 st 1 8) by lia.
  rewrite (Znth_replace_Znth_Diff 0 st 1 9) by lia.
  rewrite (Znth_replace_Znth_Diff 0 st 1 10) by lia.
  unfold MiniSatTarget.lo64, MiniSatTarget.two64, unsigned_last_nbits.
  replace (2 ^ 64) with 18446744073709551616 by reflexivity.
  split_pure_spatial.
  - cancel (&( p # "stats_t" ->ₛ "starts") # UInt64 |-> Znth 0 st 0).
    cancel.
  - dump_pre_spatial.
    rewrite Zlength_replace_Znth. exact Hlen.
Qed.

Lemma solver_search_select_join_rep_levels_at__search :
  forall (Mdb Mselected : msolver)
    (activity_ptr assigns_select orderpos_ptr s levels wl : Z)
    (seed_now : fp64) (orderpos_now order_now : list Z),
  Mselected = msolver_search_select Mdb orderpos_now order_now seed_now
    (search_decision_stats_update (ms_stats Mdb)) ->
  solver_shape Mselected ->
  (&(s # "solver_t" ->ₛ "size") # Int |-> ms_size Mdb **
   &(s # "solver_t" ->ₛ "random_seed") # Double |-> seed_now **
   &(s # "solver_t" ->ₛ "stats" .ₛ "decisions") # UInt64
     |-> unsigned_last_nbits (stats_decisions (ms_stats Mdb) + 1) 64 **
   &(s # "solver_t" ->ₛ "activity") # Ptr |-> activity_ptr **
   DoubleArray.seg activity_ptr 0 (ms_size Mdb) (ms_activity Mdb) **
   &(s # "solver_t" ->ₛ "assigns") # Ptr |-> assigns_select **
   CharArray.seg assigns_select 0 (ms_size Mdb)
     (mt_assigns (ms_core Mdb)) **
   &(s # "solver_t" ->ₛ "orderpos") # Ptr |-> orderpos_ptr **
   IntArray.seg orderpos_ptr 0 (ms_size Mdb) orderpos_now **
   Veci.rep &(s # "solver_t" ->ₛ "order") order_now **
   solver_search_order_frame_at s Mdb levels activity_ptr assigns_select
     orderpos_ptr wl) |--
  solver_rep_levels_wl_at s Mselected wl levels.
Proof.
  intros Mdb Mselected activity_ptr assigns_select orderpos_ptr s levels wl
    seed_now orderpos_now order_now HM Hshape_selected.
  assert (Hdecisions_addr :
    &(s # "solver_t" ->ₛ "stats" .ₛ "decisions") =
    &(&(s # "solver_t" ->ₛ "stats") ->ₛ "decisions"))
    by (csimpl; reflexivity).
  assert (Hdecisions_typed :
    eval_addr_expr (RE_addr_of
      (LE_arrow_field
        (RE_addr_of (LE_arrow_field
          (RE_const s (FET_alias "solver_t")) "stats"))
        "decisions")) =
    eval_addr_expr (RE_addr_of
      (LE_arrow_field
        (RE_const
          (eval_addr_expr (RE_addr_of (LE_arrow_field
            (RE_const s (FET_alias "solver_t")) "stats")))
          (FET_alias "stats_t"))
        "decisions")))
    by (csimpl; reflexivity).
  unfold solver_search_order_frame_at.
  Intros rsn trl tgs.
  rewrite Hdecisions_addr, Hdecisions_typed.
  
  
  sep_apply_l_atomic
    (stats_without_decisions_update_join__search
      (eval_addr_expr
        (RE_addr_of
          (LE_arrow_field (RE_const s (FET_alias "solver_t")) "stats")))
      (ms_stats Mdb)).
  unfold solver_rep_levels_wl_at.
  Exists activity_ptr assigns_select orderpos_ptr rsn trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep,
    clause_new_scalars_frame, solver_fp_rep, solver_fp_without_seed_rep,
    solver_vecs_rep, solver_vecs_without_order_rep,
    solver_trail_array_rep, solver_levels_slice_at.
  subst Mselected. unfold msolver_search_select. simpl.
  msat_entailer_with lia.
Qed.

Lemma In_Zseq_offset : forall start len i,
  0 <= i < Z.of_nat len -> In (start + i) (Zseq start len).
Proof.
  intros start len. revert start.
  induction len as [|len IH]; intros start i Hi; [lia|].
  simpl. destruct (Z.eq_dec i 0) as [->|Hne].
  - left. lia.
  - right. replace (start + i) with (Z.succ start + (i - 1)) by lia.
    apply IH. lia.
Qed.

Lemma solver_rep_levels_at_assume_focus__search : forall s M levels wl,
  solver_rep_levels_wl_at s M wl levels |--
  EX asg : Z,
    &(s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
    enqueue_state_at s asg levels (ms_size M) (ms_cap M) (ms_qtail M)
      (mt_assigns (ms_core M)) (mt_levels (ms_core M))
      (ms_reason_words M) (mt_trail (ms_core M))
      (mt_lim (ms_core M)) **
    solver_assume_frame_wl s M wl.
Proof.
  intros s M levels wl.
  unfold solver_rep_levels_wl_at.
  Intros act asg opos rsn trl tgs.
  Exists asg.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, enqueue_state_at.
  Exists rsn trl.
  unfold solver_assume_frame_wl, solver_enqueue_frame_with_scalars_wl, solver_enqueue_cells_at.
  Exists act opos tgs.
  unfold solver_scalars_rep, solver_assume_scalars_frame,
    solver_fp_rep, solver_vecs_rep, solver_vecs_without_lim_rep,
    solver_levels_slice_at, solver_trail_array_rep.
  msat_entailer_with ltac:(unfold solver_shape in H; tauto).
Qed.

Lemma NoDup_Forall_range_missing_length_lt__search : forall n l x,
  0 <= n -> NoDup l -> Forall (fun v => 0 <= v < n) l ->
  0 <= x < n -> ~ In x l -> Zlength l < n.
Proof.
  intros n l x Hn Hnd Hall Hx Hmissing.
  assert (Hndx : NoDup (x :: l)).
  { constructor; assumption. }
  assert (Hincl : incl (x :: l) (Zseq 0 (Z.to_nat n))).
  { intros y Hy. destruct Hy as [Hy|Hy].
    - subst y. replace x with (0 + x) by lia.
      apply In_Zseq_offset.
      rewrite Z2Nat.id by lia. exact Hx.
    - rewrite Forall_forall in Hall. specialize (Hall y Hy).
      replace y with (0 + y) by lia.
      apply In_Zseq_offset.
      rewrite Z2Nat.id by lia. exact Hall. }
  pose proof (NoDup_incl_length Hndx Hincl) as Hlen.
  rewrite Zseq_length in Hlen.
  apply Nat2Z.inj_le in Hlen.
  simpl in Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  rewrite Zlength_correct.
  lia.
Qed.

Lemma strict_sorted_NoDup__search : forall l,
  strict_sorted l -> NoDup l.
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  simpl in H. destruct H as [Hall Hsorted]. constructor.
  - intro Hin. rewrite Forall_forall in Hall. specialize (Hall a Hin). lia.
  - apply IH. exact Hsorted.
Qed.

Lemma solver_search_selection_pure__search :
  forall n F A_arr A_inst next M,
  solver_search_selection_state n F A_arr A_inst next M ->
  Zlength (mt_lim (ms_core M)) < n /\
  enqueue_input n (lit_neg_c (next + next)) (ms_qtail M)
    (mt_assigns (ms_core M)) (mt_levels (ms_core M))
    (ms_reason_words M) (mt_trail (ms_core M)).
Proof.
  intros n F A_arr A_inst next M Hsel.
  unfold solver_search_selection_state in Hsel.
  destruct Hsel as (Hweak & Hprop & Hwatch & Hreasonless & Hpending &
    Hdrain & Hseed & Hmodel & Hdecay & Htwo & Hnext & Hunassigned & Hheap).
  pose proof (msw_trail_wf Hweak) as Hwf.
  pose proof (msw_shape Hweak) as Hshape.
  assert (Hnext_notin : ~ In next (map lit_var_c (mt_trail (ms_core M)))).
  { intro Hin. apply (proj2 (mtw_assigned_iff Hwf next Hnext)) in Hin.
    contradiction. }
  assert (Htrail_forall : Forall (fun v => 0 <= v < n)
      (map lit_var_c (mt_trail (ms_core M)))).
  { apply Forall_map. pose proof (mtw_trail_lits Hwf) as Hlits. revert Hlits.
    apply Forall_impl. intros l Hl. apply lit_var_c_in_range. exact Hl. }
  assert (Htrail_lt : Zlength (mt_trail (ms_core M)) < n).
  { assert (Hmap_lt : Zlength (map lit_var_c (mt_trail (ms_core M))) < n).
    { apply NoDup_Forall_range_missing_length_lt__search
        with (x := next).
      - exact (mtw_n_nonneg Hwf).
      - exact (mtw_trail_nodup Hwf).
      - exact Htrail_forall.
      - exact Hnext.
      - exact Hnext_notin. }
    rewrite Zlength_map_Z in Hmap_lt. exact Hmap_lt. }
  assert (Hlim_le : Zlength (mt_lim (ms_core M)) <=
      Zlength (mt_trail (ms_core M))).
  { assert (Hincl : incl (mt_lim (ms_core M))
        (Zseq 0 (Z.to_nat (Zlength (mt_trail (ms_core M)))))).
    { intros y Hy.
      pose proof (mtw_lim_range Hwf) as Hrange.
      rewrite Forall_forall in Hrange.
      pose proof (Hrange y Hy) as HyR.
      replace y with (0 + y) by lia.
      apply In_Zseq_offset.
      rewrite Z2Nat.id by apply Zlength_nonneg. exact HyR. }
    pose proof (NoDup_incl_length
      (strict_sorted_NoDup__search _ (mtw_lim_sorted Hwf))
      Hincl) as Hlen.
    rewrite Zseq_length in Hlen.
    rewrite Zlength_correct in Hlen.
    rewrite Nat2Z.id in Hlen.
    rewrite !Zlength_correct. apply Nat2Z.inj_le. exact Hlen. }
  split; [lia|].
  unfold enqueue_input.
  assert (Hlitwf : lit_wf_c n (lit_neg_c (next + next))).
  { apply lit_neg_c_wf. unfold lit_wf_c. lia. }
  assert (Hvar : lit_var_c (lit_neg_c (next + next)) = next).
  { rewrite lit_var_c_neg. unfold lit_var_c.
    replace (next + next) with (next * 2) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite Hvar.
  unfold solver_shape in Hshape.
  rewrite <- (msw_size Hweak) in Hshape.
  split; [exact Hlitwf|].
  repeat split; try tauto; try lia.
  pose proof (mtw_cells Hwf) as Hcells. revert Hcells.
  apply Forall_impl. intros x Hx. unfold lbool_cell in Hx.
  destruct Hx as [Hx|[Hx|Hx]]; subst x; lia.
Qed.

Lemma stable_view_decision_assign__search :
  forall old new x b,
    stable_view old ->
    assigns_one old new x b (current_level old + 1) None ->
    current_level new = current_level old + 1 ->
    stable_view new.
Proof.
  intros old new x b [Hground Hclosed] Hstep Hcur.
  split.
  - eapply grounded_at_assigns_one; [exact Hground|exact Hstep|].
    left. reflexivity.
  - destruct Hstep as
    [Hxnone [Hxassign [Hxlevel [Hxreason [[rx [Hxrank Hdeps]]
      [Hother Hdb]]]]]].
    destruct Hclosed as [Hcur0 [Hlevels Hdecisions]].
    split; [rewrite Hcur; lia|]. split.
    + intros y bv dy Hyassign Hylevel.
      destruct (Z.eq_dec y x) as [->|Hyx].
      * rewrite Hxlevel in Hylevel. inversion Hylevel. subst dy.
        rewrite Hcur. lia.
      * destruct (Hother y Hyx) as [Hay [Hly _]].
        rewrite Hay in Hyassign. rewrite Hly in Hylevel.
        rewrite Hcur. pose proof (Hlevels y bv dy Hyassign Hylevel). lia.
    + intros dy Hdy.
      destruct (Z.eq_dec dy (current_level old + 1)) as [->|Hdne].
      * exists x. split; [exists b; exact Hxassign|].
        split; [exact Hxlevel|exact Hxreason].
      * assert (Hdyold : 0 < dy <= current_level old) by (rewrite Hcur in Hdy; lia).
        destruct (Hdecisions dy Hdyold) as
          [y [[bv Hyassign] [Hylevel Hyreason]]].
        assert (Hyx : y <> x).
        { intro Heq. subst y. rewrite Hxnone in Hyassign. discriminate. }
        destruct (Hother y Hyx) as [Hay [Hly [Hry _]]].
        exists y. split.
        -- exists bv. rewrite Hay. exact Hyassign.
        -- split; [rewrite Hly; exact Hylevel|rewrite Hry; exact Hyreason].
Qed.

Lemma assump_true_at_root_decide__search : forall n t l root a,
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  assump_true_at_root t root a ->
  assump_true_at_root (mt_decide t l) root a.
Proof.
  intros n t l root a Hwf Hl Hfresh [Htrue Hlevel].
  destruct (satisfied_literal_push n t l (mt_lim t ++ [Zlength (mt_trail t)]) a Hwf Hl Hfresh Htrue)
    as [Htrue' Hlevel'].
  split; [exact Htrue'|].
  change (Znth (literal_var a) (mt_levels (mt_push t l (mt_lim t ++ [Zlength (mt_trail t)]))) 0 <= root).
  rewrite Hlevel'. exact Hlevel.
Qed.

Lemma root_satisfied_decide__search : forall n t l c,
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  root_satisfied t c -> root_satisfied (mt_decide t l) c.
Proof.
  intros n t l c Hwf Hl Hfresh [a [Hin [Htrue Hlevel]]].
  destruct (satisfied_literal_push n t l (mt_lim t ++ [Zlength (mt_trail t)]) a
    Hwf Hl Hfresh Htrue) as [Htrue' Hlevel'].
  exists a. split; [exact Hin|]. split; [exact Htrue'|].
  unfold mt_decide. rewrite Hlevel'. exact Hlevel.
Qed.

Lemma minisat_watch_frontier_decide__search : forall n db t l,
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 = 0 ->
  mt_qhead t = Zlength (mt_trail t) ->
  minisat_watch_frontier n db (mt_assigns t) (mt_trail t) (mt_qhead t) ->
  minisat_watch_frontier n db
    (mt_assigns (mt_decide t l)) (mt_trail (mt_decide t l))
    (mt_qhead (mt_decide t l)).
Proof.
  intros n db t l Hwf Hl Hfresh Hq Hfront.
  exact (minisat_watch_frontier_enqueue_nodrain n db t l Hwf Hl Hfresh Hfront).
Qed.

Lemma msolver_assume_assigns_one__search : forall n M l,
  mtrail_wf n (ms_core M) -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  assigns_one (msolver_view n M) (msolver_view n (msolver_assume M l))
    (lit_var_c l) (lit_pol l) (Zlength (mt_lim (ms_core M)) + 1) None.
Proof.
  intros n M l Hwf Hl Hfresh.
  unfold msolver_view, msolver_assume, msolver_db. simpl.
  eapply view_of_decide_assign.
  - exact Hwf.
  - exact Hl.
  - exact Hfresh.
  - intros y Hy. apply sat_function_update_neq. congruence.
  - apply sat_function_update_eq.
Qed.

Lemma reason_edges_decision_assign :
  forall old new x b d (P : Z -> clause -> Prop),
    assigns_one old new x b d None ->
    (forall y c, reason_of old y = Some c -> P y c) ->
    forall y c, reason_of new y = Some c -> P y c.
Proof.
  intros old new x b d P Hstep Hold y c Hy.
  destruct Hstep as [_ [_ [_ [Hxreason [_ [Hother _]]]]]].
  destruct (Z.eq_dec y x) as [->|Hyx].
  - rewrite Hxreason in Hy. discriminate.
  - destruct (Hother y Hyx) as [_ [_ [Hry _]]].
    apply (Hold y c). rewrite <- Hry. exact Hy.
Qed.

Lemma reasons_entailed_decision_assign__search :
  forall F old new x b d,
    assigns_one old new x b d None ->
    reasons_entailed F old -> reasons_entailed F new.
Proof. intros F old new x b d Hstep Hold.
  exact (reason_edges_decision_assign old new x b d (fun _ c => entails_clause F c) Hstep Hold). Qed.

Lemma reasons_var_injective_decision_assign__search :
  forall old new x b d,
    assigns_one old new x b d None ->
    reasons_var_injective old -> reasons_var_injective new.
Proof. intros old new x b d Hstep Hold.
  exact (reason_edges_decision_assign old new x b d (fun _ c => clause_var_injective c) Hstep Hold). Qed.

Lemma reasons_match_assume_core : forall n M l,
  solver_shape M ->
  n = ms_size M ->
  reasons_match n (ms_core M) (msolver_db M) (ms_reason_words M)
    (ms_reason_of M) ->
  lit_wf_c n l ->
  reasons_match n (ms_core (msolver_assume M l))
    (msolver_db (msolver_assume M l))
    (ms_reason_words (msolver_assume M l))
    (ms_reason_of (msolver_assume M l)).
Proof.
  intros n M l Hshape Hsize Hreasons Hl v Hv.
  pose proof (Hreasons v Hv) as Hold.
  unfold msolver_assume, msolver_db. cbn [ms_core ms_reason_words ms_reason_of ms_prob ms_learnt].
  assert (Htarget : 0 <= lit_var_c l < Zlength (ms_reason_words M)).
  { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
  assert (Hvr : 0 <= v < Zlength (ms_reason_words M)).
  { unfold solver_shape in Hshape. lia. }
  destruct (Z.eq_dec v (lit_var_c l)) as [->|Hne].
  - rewrite Znth_replace_Znth_Same by exact Htarget.
    rewrite sat_function_update_eq. reflexivity.
  - rewrite Znth_replace_Znth_Diff by (try assumption; congruence).
    rewrite sat_function_update_neq by congruence.
    unfold reason_word_ok in Hold |- *.
    destruct (Z.eqb (Znth v (ms_reason_words M) 0) 0); [exact Hold|].
    destruct Hold as [Hassigned Hdecode]. split.
    + unfold mt_decide, mt_push. cbn [mt_assigns].
      assert (Hta : 0 <= lit_var_c l < Zlength (mt_assigns (ms_core M))).
      { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
      assert (Hva : 0 <= v < Zlength (mt_assigns (ms_core M))).
      { unfold solver_shape in Hshape. lia. }
      rewrite Znth_replace_Znth_Diff; try assumption; congruence.
    + assert (Htrail : trail_lit_of (mt_decide (ms_core M) l) v =
          trail_lit_of (ms_core M) v).
      { unfold trail_lit_of, mt_decide, mt_push. cbn [mt_assigns].
        assert (Hta : 0 <= lit_var_c l < Zlength (mt_assigns (ms_core M))).
        { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
        assert (Hva : 0 <= v < Zlength (mt_assigns (ms_core M))).
        { unfold solver_shape in Hshape. lia. }
        rewrite Znth_replace_Znth_Diff; try assumption; congruence. }
      rewrite Htrail. exact Hdecode.
Qed.

Lemma reasons_match_assume__search : forall n F A_arr A_inst M l,
  msolver_inv_weak n F A_arr A_inst M -> lit_wf_c n l ->
  reasons_match n (ms_core (msolver_assume M l))
    (msolver_db (msolver_assume M l))
    (ms_reason_words (msolver_assume M l))
    (ms_reason_of (msolver_assume M l)).
Proof.
  intros n F A_arr A_inst M l Hinv Hl.
  exact (reasons_match_assume_core n M l
    (msw_shape Hinv) (msw_size Hinv) (msw_reasons_mem Hinv) Hl).
Qed.

Lemma reason_head_ok_assume_core : forall n M l,
  solver_shape M ->
  n = ms_size M ->
  reason_head_ok M ->
  lit_wf_c n l ->
  reason_head_ok (msolver_assume M l).
Proof.
  intros n M l Hshape Hsize Hhead Hl.
  unfold reason_head_ok in *.
  unfold msolver_assume, msolver_db. cbn [ms_size ms_reason_words ms_prob ms_learnt].
  intros v co Hv Htag Hnz Hin.
  assert (Htarget : 0 <= lit_var_c l < Zlength (ms_reason_words M)).
  { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
  assert (Hvr : 0 <= v < Zlength (ms_reason_words M)).
  { unfold solver_shape in Hshape. lia. }
  destruct (Z.eq_dec v (lit_var_c l)) as [->|Hne].
  - rewrite Znth_replace_Znth_Same in Hnz by exact Htarget. contradiction.
  - rewrite Znth_replace_Znth_Diff in Htag, Hnz, Hin;
      try assumption; try congruence.
    eapply Hhead; eassumption.
Qed.

Lemma reason_head_ok_assume__search : forall n F A_arr A_inst M l,
  msolver_inv_weak n F A_arr A_inst M -> lit_wf_c n l ->
  reason_head_ok (msolver_assume M l).
Proof.
  intros n F A_arr A_inst M l Hinv Hl.
  exact (reason_head_ok_assume_core n M l
    (msw_shape Hinv) (msw_size Hinv) (msw_reason_head Hinv) Hl).
Qed.

Lemma binary_reason_same_level_assume_core : forall n M l,
  solver_shape M ->
  n = ms_size M ->
  mtrail_wf n (ms_core M) ->
  binary_reason_same_level M ->
  reasons_match n (ms_core M) (msolver_db M) (ms_reason_words M)
    (ms_reason_of M) ->
  stable_view (msolver_view n M) ->
  lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  binary_reason_same_level (msolver_assume M l).
Proof.
  intros n M l Hshape Hsize Htrailwf Hrbin Hrmem Hstable Hl Hfresh.
  eapply binary_reason_same_level_replace_core with
    (M := M) (l := l) (c := 0)
    (level := Zlength (mt_lim (ms_core M) ++ [Zlength (mt_trail (ms_core M))]));
    try eassumption; try reflexivity.
  left; reflexivity.
Qed.

Lemma binary_reason_same_level_assume__search :
  forall n F A_arr A_inst M l,
    msolver_inv_weak n F A_arr A_inst M -> lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    binary_reason_same_level (msolver_assume M l).
Proof.
  intros n F A_arr A_inst M l Hinv Hl Hfresh.
  exact (binary_reason_same_level_assume_core n M l
    (msw_shape Hinv) (msw_size Hinv) (msw_trail_wf Hinv) (msw_reason_bin Hinv)
    (msw_reasons_mem Hinv) (msw_stable Hinv) Hl Hfresh).
Qed.

Lemma db_complete_assume_core : forall n F M l,
  db_complete F M ->
  mtrail_wf n (ms_core M) ->
  lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  db_complete F (msolver_assume M l).
Proof.
  intros n F M l Hdbc Htwf Hl Hfresh C HC.
  destruct (Hdbc C HC) as [[C' [Hin Hperm]]|Hroot].
  - left. exists C'. split; [|exact Hperm].
    unfold msolver_assume. cbn [ms_prob]. exact Hin.
  - right. unfold msolver_assume. cbn [ms_core].
    eapply root_satisfied_decide__search;
      [exact Htwf|exact Hl|exact Hfresh|exact Hroot].
Qed.

Lemma db_complete_assume__search : forall n F A_arr A_inst M l,
  msolver_inv_weak n F A_arr A_inst M -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  db_complete F (msolver_assume M l).
Proof.
  intros n F A_arr A_inst M l Hinv Hl Hfresh.
  exact (db_complete_assume_core n F M l
    (msw_db_complete Hinv) (msw_trail_wf Hinv) Hl Hfresh).
Qed.

Lemma current_reasonless_assume_core : forall n M l,
  solver_shape M ->
  n = ms_size M ->
  mtrail_wf n (ms_core M) ->
  current_reasonless_earliest n M ->
  lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  current_reasonless_earliest n (msolver_assume M l).
Proof.
  intros n M l Hshape Hsize Htrailwf Hold Hl Hfresh.
  pose proof (msolver_assume_assigns_one__search n M l
    Htrailwf Hl Hfresh) as Hassign.
  destruct Hassign as
    [Hxnone [Hxassign [Hxlevel [Hxreason [[rx [Hxrank Hdeps]] [Hother Hdb]]]]]].
  unfold current_reasonless_earliest in Hold |- *.
  intros d Hrange v Hlevel Hword.
  unfold msolver_assume, mt_decide, mt_push in Hrange.
  cbn [ms_root_level ms_core mt_lim] in Hrange.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hrange.
  destruct (Z.eq_dec v (lit_var_c l)) as [->|Hvne].
  - rewrite Hxlevel in Hlevel. inversion Hlevel. subst d.
    split.
    + unfold msolver_assume. cbn [ms_reason_of]. apply sat_function_update_eq.
    + unfold msolver_view, msolver_assume. cbn [ms_core].
      rewrite view_of_rank. unfold mt_decide.
      rewrite (trail_pos_push_new n (ms_core M) l
        (mt_lim (ms_core M) ++
          (Zlength (mt_trail (ms_core M)) :: nil))
        Htrailwf Hl Hfresh).
      f_equal. f_equal.
    unfold msolver_assume, mt_decide, mt_push. cbn [ms_core mt_lim].
    rewrite app_Znth2 by lia.
    replace (Zlength (mt_lim (ms_core M)) + 1 - 1 -
      Zlength (mt_lim (ms_core M))) with 0 by lia.
    simpl.
    rewrite Znth0_cons.
    rewrite Zlength_correct, Nat2Z.id. reflexivity.
  - destruct (Hother v Hvne) as [Ha [Hlev [Hreason Hrank]]].
    rewrite Hlev in Hlevel.
    assert (Hv : 0 <= v < n).
    { unfold msolver_view, view_of in Hlevel. cbn [level_of] in Hlevel.
      destruct (trail_pos (ms_core M) v) as [k|] eqn:Hpos;
        cbn [option_map] in Hlevel; [|discriminate].
      apply find_var_pos_some_in in Hpos.
      eapply trail_var_range; eassumption. }
    assert (Hdold : d <= Zlength (mt_lim (ms_core M))).
    { unfold msolver_view, view_of in Hlevel. cbn [level_of] in Hlevel.
      destruct (trail_pos (ms_core M) v) as [k|] eqn:Hpos;
        cbn [option_map] in Hlevel; [|discriminate].
      inversion Hlevel. subst d. apply prop_level_processed_level_le. }
    assert (Hvr : 0 <= v < Zlength (ms_reason_words M)).
    { unfold solver_shape in Hshape. lia. }
    assert (Htarget : 0 <= lit_var_c l < Zlength (ms_reason_words M)).
    { apply lit_var_c_in_range in Hl. unfold solver_shape in Hshape. lia. }
    unfold msolver_assume in Hword. cbn [ms_reason_words] in Hword.
    rewrite Znth_replace_Znth_Diff in Hword;
      [|exact Htarget|exact Hvr|congruence].
    destruct (Hold d ltac:(lia) v Hlevel Hword) as [Hr Hrk].
    split.
    + unfold msolver_assume. cbn [ms_reason_of].
      rewrite sat_function_update_neq by congruence. exact Hr.
    + rewrite Hrank.
      unfold msolver_assume, mt_decide, mt_push. cbn [ms_core mt_lim].
      rewrite app_Znth1 by (unfold solver_shape in Hshape; lia). exact Hrk.
Qed.

Lemma current_reasonless_assume__search :
  forall n F A_arr A_inst M l,
    msolver_inv_weak n F A_arr A_inst M ->
    current_reasonless_earliest n M ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    current_reasonless_earliest n (msolver_assume M l).
Proof.
  intros n F A_arr A_inst M l Hinv Hold Hl Hfresh.
  exact (current_reasonless_assume_core n M l
    (msw_shape Hinv) (msw_size Hinv) (msw_trail_wf Hinv) Hold Hl Hfresh).
Qed.

Lemma msolver_assume_prop_watch__search :
  forall n M l,
    mtrail_wf n (ms_core M) ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    mt_qhead (ms_core M) = Zlength (mt_trail (ms_core M)) ->
    prop_level (ms_core M) ->
    minisat_watch_frontier n (msolver_db M) (mt_assigns (ms_core M))
      (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
    prop_level (ms_core (msolver_assume M l)) /\
    minisat_watch_frontier n
      (msolver_db (msolver_assume M l))
      (mt_assigns (ms_core (msolver_assume M l)))
      (mt_trail (ms_core (msolver_assume M l)))
      (mt_qhead (ms_core (msolver_assume M l))).
Proof.
  intros n M l Htrailwf Hlit Hfresh Hqhead Hprop Hwatch.
  split.
  - unfold msolver_assume. cbn [ms_core].
    apply prop_level_decide; [exact Hprop|exact Hqhead].
  - unfold msolver_assume, msolver_db. cbn [ms_core ms_prob ms_learnt].
    eapply minisat_watch_frontier_decide__search;
      [exact Htrailwf|exact Hlit|exact Hfresh|exact Hqhead|exact Hwatch].
Qed.

Lemma solver_search_decision_pure__search :
  forall n F A_arr A_inst next M,
  solver_search_selection_state n F A_arr A_inst next M ->
  enqueue_input n (lit_neg_c (next + next)) (ms_qtail M)
    (mt_assigns (ms_core M)) (mt_levels (ms_core M))
    (ms_reason_words M) (mt_trail (ms_core M)) ->
  Zlength (mt_lim (ms_core M)) < n ->
  solver_search_decision_transition n F A_arr A_inst M next
    (msolver_assume M (lit_neg_c (next + next))).
Proof.
  intros n F A_arr A_inst next M Hsel Henq Hlevelroom.
  destruct Hsel as
    (Hweak & Hprop & Hwatch & Hreasonless & Hpending & Hdrain &
     Hseed & Hmodel & Hdecay & Htwice & Hnext & Hfresh & Hheap).
  pose proof (msw_shape Hweak) as Hshape.
  pose proof (msw_trail_wf Hweak) as Htrailwf.
  pose proof (msw_size Hweak) as Hsize.
  pose proof (msw_root_range Hweak) as Hrootrange.
  unfold enqueue_input in Henq.
  destruct Henq as [Hlit [Htwice' [Haslen [Hlvlen [Hrslen
    [Htrlen [Hqrange [Hroom Hcells]]]]]]]].
  set (l := lit_neg_c (next + next)).
  assert (Hvar : lit_var_c l = next).
  { unfold l. rewrite lit_var_c_neg. unfold lit_var_c.
    replace (next + next) with (next * 2) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (Hfreshl : Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0)
    by (rewrite Hvar; exact Hfresh).
  assert (Hroomcap : ms_qtail M < ms_cap M).
  { specialize (Hroom Hfreshl). unfold solver_shape in Hshape. lia. }
  assert (Htrailnew : mtrail_wf n (ms_core (msolver_assume M l))).
  { unfold msolver_assume. cbn [ms_core].
    apply mtrail_wf_decide; assumption. }
  assert (Hassign := msolver_assume_assigns_one__search n M l
    Htrailwf Hlit Hfreshl).
  assert (Hsizenew : n = ms_size (msolver_assume M l)) by exact Hsize.
  assert (Hweaknew : msolver_inv_weak n F A_arr A_inst
      (msolver_assume M l)).
  { refine {| msw_size := Hsizenew; msw_n_range := msw_n_range Hweak;
      msw_shape := solver_shape_assume__search M l Hshape Hroomcap Hpending;
      msw_F_wf := msw_F_wf Hweak; msw_A_wf := msw_A_wf Hweak;
      msw_trail_wf := Htrailnew;
      msw_level_bound := _; msw_root_range := _;
      msw_assumptions := _; msw_assump_incl := msw_assump_incl Hweak;
      msw_assump_sat := _;
      msw_stable := _; msw_reasons_ent := _; msw_reasons_inj := _;
      msw_trail_impl := _; msw_db_wf := msw_db_wf Hweak;
      msw_db_matches := msw_db_matches Hweak;
      msw_db_implied := msw_db_implied Hweak;
      msw_db_complete := db_complete_assume__search n F A_arr A_inst M l
        Hweak Hlit Hfreshl;
      msw_learnt_db := msw_learnt_db Hweak; msw_prob_db := msw_prob_db Hweak;
      msw_binary_out := msw_binary_out Hweak;
      msw_reasons_mem := reasons_match_assume__search n F A_arr A_inst M l Hweak Hlit;
      msw_reason_head := reason_head_ok_assume__search n F A_arr A_inst M l Hweak Hlit;
      msw_reason_bin := binary_reason_same_level_assume__search n F A_arr A_inst M l
        Hweak Hlit Hfreshl;
      msw_wmap_exact := msw_wmap_exact Hweak; msw_tags_clear := msw_tags_clear Hweak;
      msw_heap_wf := msw_heap_wf Hweak;
      msw_cla_inc_nonnegative := msw_cla_inc_nonnegative Hweak;
      msw_seed := msw_seed Hweak |}.
    - unfold msolver_assume, mt_decide, mt_push. cbn [ms_core mt_lim].
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    - unfold msolver_assume, mt_decide, mt_push. cbn [ms_root_level ms_core mt_lim].
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    - unfold msolver_assume. cbn [ms_root_level ms_core].
      rewrite (decisions_upto_decide_low n (ms_core M) l (ms_root_level M)
        Htrailwf ltac:(lia)). exact (msw_assumptions Hweak).
    - pose proof (msw_assump_sat Hweak) as HF. revert HF.
      apply Forall_impl. intros a Ha.
      unfold msolver_assume. cbn [ms_root_level ms_core].
      eapply assump_true_at_root_decide__search; eauto.
    - eapply stable_view_decision_assign__search; [exact (msw_stable Hweak)|exact Hassign|].
      unfold msolver_view, msolver_assume, view_of, mt_decide, mt_push.
      cbn [current_level ms_core mt_lim].
      rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity.
    - eapply reasons_entailed_decision_assign__search; eauto using msw_reasons_ent.
    - eapply reasons_var_injective_decision_assign__search; eauto using msw_reasons_inj.
    - unfold msolver_assume. cbn [ms_core].
      eapply trail_implied_decision; eauto using msw_trail_impl.
  }
  assert (Hqhead : mt_qhead (ms_core M) = Zlength (mt_trail (ms_core M)))
    by lia.
  destruct (msolver_assume_prop_watch__search n M l
    Htrailwf Hlit Hfreshl Hqhead Hprop Hwatch) as [Hpropnew Hwatchnew].
  assert (Hreasonnew : current_reasonless_earliest n
      (msolver_assume M l)).
  { eapply current_reasonless_assume__search;
      [exact Hweak|exact Hreasonless|exact Hlit|exact Hfreshl]. }
  assert (Hheapnew : propagation_heap_ready n (msolver_assume M l)).
  { right. unfold msolver_assume, mt_decide, mt_push.
    cbn [ms_core mt_lim mt_qhead ms_qtail mt_assigns mt_trail msolver_heap].
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    split; [lia|]. split; [lia|].
    assert (Hcov : heap_covers_except n (msolver_heap M)
      (replace_Znth (lit_var_c l) (lit_sig l) (mt_assigns (ms_core M)))
      (mt_trail (ms_core M) ++ (l :: nil)) (mt_qhead (ms_core M)) next).
    { eapply heap_covers_except_assume; [exact Hheap|lia| |].
      - intros v Hv Hvassigned.
        assert (Hvne : v <> lit_var_c l).
        { intro E. subst v. rewrite Hfreshl in Hvassigned. contradiction. }
        rewrite Znth_replace_Znth_Diff; [exact Hvassigned| | |congruence].
        + apply lit_var_c_in_range in Hlit. rewrite (mtw_assigns_len Htrailwf). exact Hlit.
        + rewrite (mtw_assigns_len Htrailwf). exact Hv.
      - intros i Hi. rewrite app_Znth1. reflexivity. lia. }
    assert (Hfocus : lit_var_c
      (Znth (mt_qhead (ms_core M))
        (mt_trail (ms_core M) ++ (l :: nil)) 0) = next).
    { rewrite app_Znth2 by lia.
      replace (mt_qhead (ms_core M) - Zlength (mt_trail (ms_core M)))
        with 0 by lia.
      rewrite Znth0_cons. exact Hvar. }
    rewrite Hfocus. exact Hcov. }
  unfold solver_search_decision_transition.
  split; [reflexivity|]. split.
  - split; [exact Hpending|].
    refine {| msp_weak := Hweaknew; msp_prop_level := Hpropnew;
      msp_watch_frontier := Hwatchnew; msp_heap_ready := Hheapnew;
      msp_reasonless_current := Hreasonnew |}.
  - split.
    + change (msolver_seed_shadow M). exact Hseed.
    + split.
      * change (ms_model M = nil). exact Hmodel.
      * split.
        -- change (msat_fp32_positive_finite (ms_cla_decay M)). exact Hdecay.
        -- reflexivity.
Qed.

Lemma assume_post_refold__search :
  forall wl s asg lvl l n cap qtail assigns levels reasons trail lim M,
  n = ms_size M -> cap = ms_cap M -> qtail = ms_qtail M ->
  assigns = mt_assigns (ms_core M) -> levels = mt_levels (ms_core M) ->
  reasons = ms_reason_words M -> trail = mt_trail (ms_core M) ->
  lim = mt_lim (ms_core M) ->
  solver_shape M -> ms_qtail M < ms_cap M ->
  ms_capacity_root_propagation_pending M = 0 ->
  mt_qhead (ms_core M) = ms_qtail M ->
  Znth (lit_var_c l) assigns 0 = 0 ->
  assume_post_at s asg lvl l n cap qtail assigns levels reasons trail lim **
  solver_assume_frame_wl s M wl
  |-- solver_rep_levels_wl_at s (msolver_assume M l) wl lvl.
Proof.
  intros wl.
  msat_assume_post_open.
  - destruct Hsame as [Hsame _]. rewrite Hfresh in Hsame. pose proof (lit_sig_nonzero l). lia.
  - destruct Hconflict as [Hne _]. contradiction.
  - destruct Hnew as
      [Hz [_ [Hassigns' [Hlevels' [Hreasons' [Htrail' Hqtail']]]]]].
    subst assigns'. subst levels'. subst reasons'. subst trail'. subst qtail'.
    unfold solver_assume_frame_wl, solver_enqueue_frame_with_scalars_wl,
      solver_enqueue_cells_at.
    Intros act opos tgs.
    unfold solver_rep_levels_wl_at.
    Exists act asg opos rsn trl tgs.
    msat_assume_post_close Hdrain Htrailq.
    cbn.
    cancel.
    rewrite Hdrain.
    rewrite Htrailq.
    (* Re-normalize architecture aliases introduced by the representation
   unfolds before closing the entailment. *)
    unfold DoubleArray.seg, IntArray.seg, CharArray.seg, PtrArray.seg,
      StoreDoubleAsElement.storeA, store_double, bits_of_double_value.
    cbn.
    msat_entailer_with lia.
Qed.

(** ===== group: solver_simplify ===== *)
Lemma solver_selected_db_in_any__simplify : forall type M p co,
  In (p, co) (solver_selected_db type M) ->
  In (p, co) (msolver_db M).
Proof.
  intros type M p co Hin.
  unfold solver_selected_db in Hin.
  unfold msolver_db.
  destruct (Z.eqb type 0) eqn:Htype.
  - apply in_or_app. left. exact Hin.
  - apply in_or_app. right. exact Hin.
Qed.

Lemma solver_simplify_pre_split__simplify :
  forall s n F A_arr M lvl wl,
    solver_simplify_pre_at s n F A_arr M lvl wl |--
      EX asg : Z,
        “ msolver_inv_assuming_strong n F A_arr A_arr M ” &&
        “ Zlength (mt_lim (ms_core M)) = 0 ” &&
        “ ms_capacity_root_propagation_pending M = 0 ” &&
        “ msolver_seed_shadow M ” &&
        Veci.rep &(s # "solver_t" ->ₛ "trail_lim")
          (mt_lim (ms_core M)) **
        solver_simplify_lim_frame_at s M asg lvl wl.
Proof.
  intros s n F A_arr M lvl wl.
  unfold solver_simplify_pre_at, solver_rep_levels_wl_at,
    solver_nonlevel_rep, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_simplify_lim_frame_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at, solver_vecs_rep, solver_vecs_without_lim_rep.
  Intros act asg opos rsn trl tgs.
  Exists asg act opos rsn trl tgs.
  msat_entailer_with int_auto.
Qed.

Lemma solver_simplify_lim_join_rep_levels__simplify :
  forall s M asg lvl wl,
    Veci.rep &(s # "solver_t" ->ₛ "trail_lim")
      (mt_lim (ms_core M)) **
    solver_simplify_lim_frame_at s M asg lvl wl |--
    solver_rep_levels_wl_at s M wl lvl.
Proof.
  intros s M asg lvl wl.
  unfold solver_rep_levels_wl_at, solver_nonlevel_rep,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_simplify_lim_frame_at,
    solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at, solver_vecs_rep,
    solver_vecs_without_lim_rep.
  Intros act opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  msat_entailer_with lia.
Qed.

Lemma solver_rep_levels_assigns_split__simplify :
  forall s M lvl wl,
    solver_rep_levels_wl_at s M wl lvl |--
      EX asg : Z, solver_rep_assigns_levels_at s M asg lvl wl.
Proof.
  intros s M lvl wl.
  unfold solver_rep_levels_wl_at, solver_rep_assigns_levels_at, solver_rep_at,
    solver_nonlevel_rep.
  Intros act asg opos rsn trl tgs.
  Exists asg act opos rsn trl tgs.
  msat_entailer_with lia.
Qed.

Lemma solver_rep_assigns_simplify_control_split__simplify :
  forall s M asg lvl wl,
    solver_rep_assigns_levels_at s M asg lvl wl |--
      EX rsn : Z,
        &(s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
        &(s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
        &(s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
        &(s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
        solver_simplify_control_frame_at s M asg lvl rsn wl.
Proof.
  intros s M asg lvl wl.
  unfold solver_rep_assigns_levels_at, solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_simplify_control_frame_at,
    solver_simplify_control_scalars_frame, solver_scalars_rep,
    solver_var_arrays_rep, solver_levels_slice_at.
  Intros act opos rsn trl tgs.
  Exists rsn act opos trl tgs.
  msat_entailer_with lia.
Qed.

Lemma solver_simplify_control_join_rep_assigns__simplify :
  forall s M asg lvl rsn wl,
    &(s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
    &(s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
    &(s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
    &(s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
    solver_simplify_control_frame_at s M asg lvl rsn wl |--
    solver_rep_assigns_levels_at s M asg lvl wl.
Proof.
  intros s M asg lvl rsn wl.

  unfold solver_rep_assigns_levels_at, solver_simplify_control_frame_at.
  Intros act opos trl tgs.
  Exists act opos rsn trl tgs.
  unfold solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_simplify_control_scalars_frame, solver_scalars_rep,
    solver_var_arrays_rep, solver_levels_slice_at.
  msat_entailer_with lia.
Qed.

Lemma solver_simplify_control_join_rep_reasons__simplify :
  forall s M asg lvl rsn wl,
    &(s # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core M) **
    &(s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
    &(s # "solver_t" ->ₛ "simpdb_props") # Int |-> ms_simpdb_props M **
    &(s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
    solver_simplify_control_frame_at s M asg lvl rsn wl |--
    solver_rep_reasons_levels_wl_at s M rsn lvl wl.
Proof.
  intros s M asg lvl rsn wl.

  unfold solver_rep_reasons_levels_wl_at, solver_simplify_control_frame_at.
  Intros act opos trl tgs.
  Exists act asg opos trl tgs.
  unfold solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_simplify_control_scalars_frame, solver_scalars_rep,
    solver_var_arrays_rep, solver_levels_slice_at.
  msat_entailer_with lia.
Qed.

Lemma clause_remove_ready_of_inv__simplify :
  forall n F A_arr A_inst M c co,
    msolver_inv n F A_arr A_inst M ->
    In (c, co) (msolver_db M) ->
    clause_remove_ready n c (co_lits co)
      (ms_wm M) (ms_stats M).
Proof.
  intros n F A_arr A_inst M c co Hinv Hin.
  pose proof (msi_weak Hinv) as Hweak.
  pose proof (msw_db_wf Hweak) as Hdb.
  pose proof (msw_wmap_exact Hweak) as Hwm.
  pose proof (proj1 Hwm) as Hwm_len.
  pose proof (msw_shape Hweak) as Hshape.
  pose proof (msw_size Hweak) as Hsize.
  assert (Hobj : obj_wf n co).
  { eapply db_wf_obj; eassumption. }
  destruct Hobj as [Hlen [Hlit Hnodup]].
  assert (Hdistinct :
    lit_var_c (co_watch0 co) <> lit_var_c (co_watch1 co)).
  { unfold co_watch0, co_watch1.
    destruct (co_lits co) as [|a xs] eqn:Hlits.
    - change (2 <= 0) in Hlen. lia.
    - destruct xs as [|b xs].
      + change (2 <= 1) in Hlen. lia.
      + inversion Hnodup as [|x l Hnot Htail].
        intro Heq. apply Hnot. simpl. left.
        simpl in Heq. symmetry. exact Heq. }
  assert (Hwatch0 :
    In (clause_watch_word c (co_lits co) (co_watch1 co))
      (Znth (lit_neg_c (co_watch0 co)) (ms_wm M) nil)).
  { unfold clause_watch_word.
    destruct (2 <? Zlength (co_lits co)) eqn:Hmore.
    - apply Z.ltb_lt in Hmore.
      eapply wmap_present_real0; eauto; lia.
    - apply Z.ltb_ge in Hmore.
      eapply wmap_present_bin0; eauto; lia. }
  assert (Hwatch1 :
    In (clause_watch_word c (co_lits co) (co_watch0 co))
      (Znth (lit_neg_c (co_watch1 co)) (ms_wm M) nil)).
  { unfold clause_watch_word.
    destruct (2 <? Zlength (co_lits co)) eqn:Hmore.
    - apply Z.ltb_lt in Hmore.
      eapply wmap_present_real1; eauto; lia.
    - apply Z.ltb_ge in Hmore.
      eapply wmap_present_bin1; eauto; lia. }
  unfold clause_remove_ready.
  repeat split; try assumption.
  - unfold solver_shape in Hshape. lia.
Qed.

Lemma solver_rep_reasons_simplify_open :
  forall s M db_type reasons lvl wl,
    mt_lim (ms_core M) = [] ->
    solver_rep_reasons_levels_wl_at s M reasons lvl wl |--
      EX asg : Z,
        Vecp.rep (solver_selected_vec s db_type)
          (db_words (solver_selected_db db_type M)) **
        clause_db_rep (solver_selected_db db_type M) **
        &(s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
        CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
        Veci.rep &(s # "solver_t" ->ₛ "trail_lim") [] **
        solver_simplify_db_rest_at s db_type M reasons lvl wl asg.
Proof.
  intros s M db_type reasons lvl wl Hlim.
  unfold solver_rep_reasons_levels_wl_at.
  Intros act asg opos trl tgs. Exists asg.
  unfold solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_simplify_db_rest_at, solver_simplify_clause_frame_at,
    solver_selected_vec, solver_selected_db,
    solver_other_db_vec_rep, solver_other_clause_db_rep,
    solver_wlists_handle, solver_scalars_rep, clause_new_scalars_frame,
    solver_vecs_rep, solver_trail_array_rep, solver_levels_slice_at, db_words.
  Exists act opos trl tgs.
  destruct (Z.eqb db_type 0); cbn; rewrite Hlim; (Intros; cancel).
Qed.

Lemma solver_selected_clause_focus__simplify :
  forall type M p co,
    (type = 0 \/ type = 1) ->
    In (p, co) (solver_selected_db type M) ->
    clause_db_rep (solver_selected_db type M) |--
      MiniSatClause.rep p (co_learnt co) (co_lits co) **
      clause_db_pair_remainder
        (solver_selected_prob_db type M)
        (solver_selected_learnt_db type M)
        p (co_learnt co) (co_lits co).
Proof.
  intros type M p co Htype Hin.
  destruct Htype as [Htype | Htype]; subst type.
  - unfold solver_selected_db in Hin |- *.
    simpl in Hin |- *.
    apply in_split in Hin.
    destruct Hin as [pre [post Hsplit]].
    pose proof (clause_db_rep_app_elim pre ((p, co) :: post)) as Happ.
    rewrite <- Hsplit in Happ.
    sep_apply Happ.
    rewrite clause_db_rep_cons.
    unfold clause_db_pair_remainder.
    unfold solver_selected_prob_db, solver_selected_learnt_db.
    simpl.
    Left.
    Exists co pre post.
    cbn [clause_db_rep].
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - unfold solver_selected_db in Hin |- *.
    simpl in Hin |- *.
    apply in_split in Hin.
    destruct Hin as [pre [post Hsplit]].
    pose proof (clause_db_rep_app_elim pre ((p, co) :: post)) as Happ.
    rewrite <- Hsplit in Happ.
    sep_apply Happ.
    rewrite clause_db_rep_cons.
    unfold clause_db_pair_remainder.
    unfold solver_selected_prob_db, solver_selected_learnt_db.
    simpl.
    Right.
    Exists co pre post.
    cbn [clause_db_rep].
    msat_entailer_with lia.
Qed.

Lemma solver_simplify_compaction_lookup__simplify :
  forall type M words i j,
    0 <= j -> j <= i -> i < Zlength words ->
    solver_simplify_db_compaction_inv type M words i j ->
    exists co,
      (type = 0 \/ type = 1) /\
      In (Znth i words 0, co) (solver_selected_db type M).
Proof.
  intros type M words i j Hj Hji Hi Hcompact.
  unfold solver_simplify_db_compaction_inv in Hcompact.
  destruct Hcompact as [Htype [_ [_ [_ Hmap]]]].
  assert (Hinsuffix :
    In (Znth i words 0) (sublist i (Zlength words) words)).
  { assert (Heq : Znth i words 0 =
        Znth 0 (sublist i (Zlength words) words) 0).
    { rewrite Znth_sublist by lia. f_equal. }
    rewrite Heq.
    apply Znth_In.
    rewrite Zlength_sublist by lia. lia. }
  assert (Hinmap :
    In (Znth i words 0) (map fst (solver_selected_db type M))).
  { rewrite Hmap. apply in_or_app. right. exact Hinsuffix. }
  apply in_map_iff in Hinmap.
  destruct Hinmap as [[p co] [Hp Hin]].
  simpl in Hp. subst p.
  exists co. split; assumption.
Qed.

Lemma root_satisfied_perm__simplify : forall t c c',
  Permutation c c' -> root_satisfied t c -> root_satisfied t c'.
Proof.
  intros t c c' Hperm [l [Hin [Heval Hlevel]]].
  exists l. split; [ | split ]; try assumption.
  eapply Permutation_in; eassumption.
Qed.

Lemma clause_simplify_result_root_satisfied__simplify :
  forall n t lits,
    mtrail_wf n t ->
    Zlength (mt_lim t) = 0 ->
    Forall (lit_wf_c n) lits ->
    clause_simplify_result lits (mt_assigns t) 1 ->
    root_satisfied t (lits_denote lits).
Proof.
  intros n t lits Htrail Hlim Hlits Hresult.
  destruct Hresult as [[_ [i [Hi Hvalue]]] | [Hbad _]]; [|lia].
  set (packed := Znth i lits 0).
  assert (Hpacked : lit_wf_c n packed).
  { unfold packed. eapply Forall_Znth_elim; eassumption. }
  assert (Hrange : 0 <= lit_var_c packed < n)
    by (apply lit_var_c_in_range; exact Hpacked).
  assert (Hsig : packed_lit_satisfying_value packed = lit_sig packed).
  { unfold packed_lit_satisfying_value, lit_sign_c, lit_sig.
    destruct (Z.odd packed); reflexivity. }
  exists (lit_denote packed). split.
  - unfold lits_denote. apply in_map. unfold packed.
    apply Znth_In. exact Hi.
  - split.
    + assert (Heval :
        eval_partial_literal (assigns_pv (mt_assigns t))
          (lit_denote packed) = Some true).
      { apply lit_true_iff.
        - exact (proj1 Hpacked).
        - rewrite <- Hsig. exact Hvalue. }
      unfold eval_partial_literal in Heval |- *.
      rewrite mt_pv_nonneg by (rewrite lit_var_c_denote; lia).
      exact Heval.
    + rewrite lit_var_c_denote.
      assert (Hassigned : Znth (lit_var_c packed) (mt_assigns t) 0 <> 0).
      { unfold packed. rewrite Hvalue.
        unfold packed_lit_satisfying_value, lit_sign_c.
        destruct (Z.odd (Znth i lits 0)); discriminate. }
      apply (proj1 (mtw_assigned_iff Htrail (lit_var_c packed) Hrange))
        in Hassigned.
      apply in_map_iff in Hassigned.
      destruct Hassigned as [trail_lit [Hvar Hintrail]].
      destruct (In_Znth_index (mt_trail t) trail_lit Hintrail)
        as [k [Hk Htrail_lit]].
      pose proof (mtw_levels_agree Htrail k Hk) as Hlevel.
      unfold trail_var in Hlevel. rewrite Htrail_lit, Hvar in Hlevel.
      assert (Hlimnil : mt_lim t = []).
      { destruct (mt_lim t) as [|a rest] eqn:Hlimcase; [reflexivity |].
        rewrite Zlength_cons in Hlim.
        pose proof (Zlength_nonneg rest). lia. }
      unfold level_of_index in Hlevel. rewrite Hlimnil in Hlevel.
      cbn in Hlevel. exact Hlevel.
Qed.

Lemma db_wf_prob_split_fresh__simplify :
  forall n M pre post p co,
    db_wf n (msolver_db M) ->
    ms_prob M = pre ++ (p, co) :: post ->
    ~ In p (map fst pre).
Proof.
  intros n M pre post p co [Hkeys _] Hsplit.
  assert (Hprob : NoDup (map fst (ms_prob M))).
  { eapply NoDup_app_remove_r. unfold msolver_db in Hkeys.
    rewrite map_app in Hkeys. exact Hkeys. }
  rewrite Hsplit, map_app in Hprob. cbn [map] in Hprob.
  eapply NoDup_middle_fresh__reducedb. exact Hprob.
Qed.

Lemma solver_simplify_db_compaction_inv_remove__simplify :
  forall n F A_arr A_inst type M words i j c wm stats,
    msolver_inv_weak n F A_arr A_inst M ->
    solver_simplify_db_compaction_inv type M words i j ->
    i < Zlength words ->
    c = Znth i words 0 ->
    solver_simplify_db_compaction_inv type
      (msolver_remove_clause M (solver_selected_is_learnt type) c wm stats)
      words (i + 1) j.
Proof.
  intros n F A_arr A_inst type M words i j c wm stats
    Hweak Hinv Hi Hc.
  unfold solver_simplify_db_compaction_inv in Hinv |- *.
  destruct Hinv as [Htype [Hj0 [Hji [HiN Hdb]]]].
  assert (Htail : sublist i (Zlength words) words =
      Znth i words 0 :: sublist (i + 1) (Zlength words) words).
  { rewrite (sublist_split i (Zlength words) (i + 1) words) by lia.
    rewrite (sublist_single 0 i words) by lia. reflexivity. }
  destruct Htype as [Ht | Ht]; subst type.
  - unfold solver_selected_db in Hdb. cbn in Hdb.
    assert (Hnd : NoDup (map fst (ms_prob M))).
    { pose proof (proj1 (msw_db_wf Hweak)) as Hkeys.
      unfold msolver_db in Hkeys. rewrite map_app in Hkeys.
      eapply NoDup_app_remove_r. exact Hkeys. }
    assert (Hfresh : ~ In c (sublist 0 j words)).
    { rewrite Hdb, Htail in Hnd. rewrite Hc.
      eapply NoDup_middle_fresh__reducedb. exact Hnd. }
    assert (Hmap :
      map fst (db_remove_ptr c (ms_prob M)) =
        sublist 0 j words ++ sublist (i + 1) (Zlength words) words).
    { eapply map_fst_db_remove_ptr_split__reducedb.
      - rewrite Hdb, Htail, Hc. reflexivity.
      - exact Hfresh. }
    repeat split; try lia.
    unfold solver_selected_db, solver_selected_is_learnt.
    cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ]. exact Hmap.
  - unfold solver_selected_db in Hdb. cbn in Hdb.
    assert (Hnd : NoDup (map fst (ms_learnt M))).
    { pose proof (proj1 (msw_db_wf Hweak)) as Hkeys.
      unfold msolver_db in Hkeys. rewrite map_app in Hkeys.
      eapply NoDup_app_remove_l. exact Hkeys. }
    assert (Hfresh : ~ In c (sublist 0 j words)).
    { rewrite Hdb, Htail in Hnd. rewrite Hc.
      eapply NoDup_middle_fresh__reducedb. exact Hnd. }
    assert (Hmap :
      map fst (db_remove_ptr c (ms_learnt M)) =
        sublist 0 j words ++ sublist (i + 1) (Zlength words) words).
    { eapply map_fst_db_remove_ptr_split__reducedb.
      - rewrite Hdb, Htail, Hc. reflexivity.
      - exact Hfresh. }
    repeat split; try lia.
    unfold solver_selected_db, solver_selected_is_learnt.
    cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ]. exact Hmap.
Qed.

Lemma prob_db_delete_middle__simplify :
  forall pre post e,
    prob_db (pre ++ e :: post) -> prob_db (pre ++ post).
Proof.
  intros pre post e H. unfold prob_db in *.
  apply Forall_delete_middle with (x := e). exact H.
Qed.

Lemma solver_shape_remove_problem__simplify :
  forall M p wm stats,
    solver_shape M ->
    Zlength wm = 2 * ms_size M ->
    Zlength stats = 11 ->
    solver_shape (msolver_remove_clause M false p wm stats).
Proof. msat_shape_remove_clause. Qed.

Theorem msolver_inv_weak_remove_problem__simplify :
  forall n F A_arr A_inst M c co pre post wm stats,
    msolver_inv_weak n F A_arr A_inst M ->
    ms_prob M = pre ++ (c, co) :: post ->
    ~ In c (map fst pre) ->
    clause_remove_result c (co_lits co) (ms_wm M) wm ->
    Zlength stats = 11 ->
    clause_unlocked_words c (ms_reason_words M) ->
    root_satisfied (ms_core M) (denote_obj co) ->
    msolver_inv_weak n F A_arr A_inst
      (msolver_remove_clause M false c wm stats).
Proof.
  intros n F A_arr A_inst M c co pre post wm stats
    Hinv Hsplit Hfresh Hremove Hstats Hunlocked Hremoved.
  set (M' := msolver_remove_clause M false c wm stats).
  set (fullpost := post ++ ms_learnt M).
  assert (HoldDB : msolver_db M = pre ++ (c, co) :: fullpost).
  { unfold fullpost, msolver_db. rewrite Hsplit.
    rewrite <- app_assoc. reflexivity. }
  assert (HnewDB : msolver_db M' = pre ++ fullpost).
  { unfold M', fullpost, msolver_db, msolver_remove_clause,
           msolver_propagation_overlay, msolver_propagation_update. cbn.
    rewrite Hsplit, db_remove_ptr_split__reducedb by exact Hfresh.
    rewrite app_assoc. reflexivity. }
  assert (HnewProb : ms_prob M' = pre ++ post).
  { unfold M', msolver_remove_clause, msolver_propagation_overlay, msolver_propagation_update. cbn.
    rewrite Hsplit, db_remove_ptr_split__reducedb by exact Hfresh.
    reflexivity. }
  eapply msolver_inv_weak_remove_clause_core
    with (co := co) (pre := pre) (post := fullpost).
  - exact Hinv.
  - exact HoldDB.
  - exact HnewDB.
  - exact Hremove.
  - exact Hunlocked.
  - unfold M'. apply solver_shape_remove_problem__simplify;
      [exact (msw_shape Hinv) | | exact Hstats].
    rewrite (clause_remove_result_length__reducedb
      c (co_lits co) (ms_wm M) wm Hremove).
    apply solver_shape_wm_len. exact (msw_shape Hinv).
  - pose proof (msw_db_matches Hinv) as H.
    unfold db_matches_cnf in H |- *.
    change (Forall (fun d => exists d0, In d0 F /\ Permutation d d0)
      (db_clauses (db_remove_ptr c (ms_prob M)))).
    rewrite Hsplit,
      db_remove_ptr_split__reducedb by exact Hfresh.
    rewrite Hsplit in H.
    destruct (db_clauses_delete_middle__reducedb
                pre post (c, co)) as [Hold Hnew].
    rewrite Hnew. eapply Forall_delete_middle.
    rewrite <- Hold. exact H.
  - pose proof (msw_db_implied Hinv) as H.
    unfold db_implied in H |- *.
    cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ]. exact H.
  - change (db_complete F M').
    pose proof (msw_db_complete Hinv) as Hcomplete.
    unfold db_complete in Hcomplete |- *.
    intros d Hd. specialize (Hcomplete d Hd).
    destruct Hcomplete as [[d' [Hin Hperm]] | Hroot]; [|right; exact Hroot].
    rewrite Hsplit in Hin.
    destruct (db_clauses_delete_middle__reducedb
                pre post (c, co)) as [Hold Hnew].
    rewrite Hold in Hin. apply in_app_or in Hin.
    destruct Hin as [Hinpre | Hinrest].
    + left. exists d'. split; [|exact Hperm].
      rewrite HnewProb, Hnew. apply in_or_app. left. exact Hinpre.
    + cbn in Hinrest. destruct Hinrest as [Heq | Hinpost].
      * right. subst d'.
        eapply root_satisfied_perm__simplify;
          [exact Hperm | exact Hremoved].
      * left. exists d'. split; [|exact Hperm].
        rewrite HnewProb, Hnew. apply in_or_app. right. exact Hinpost.
  - cbn [M' msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msw_learnt_db Hinv).
  - change (prob_db (db_remove_ptr c (ms_prob M))).
    rewrite Hsplit,
      db_remove_ptr_split__reducedb by exact Hfresh.
    eapply prob_db_delete_middle__simplify.
    pose proof (msw_prob_db Hinv) as H. rewrite Hsplit in H. exact H.
Qed.

Theorem msolver_inv_remove_problem__simplify :
  forall n F A_arr A_inst M c co pre post wm stats,
    msolver_inv n F A_arr A_inst M ->
    ms_prob M = pre ++ (c, co) :: post ->
    ~ In c (map fst pre) ->
    clause_remove_result c (co_lits co) (ms_wm M) wm ->
    Zlength stats = 11 ->
    clause_unlocked_words c (ms_reason_words M) ->
    root_satisfied (ms_core M) (denote_obj co) ->
    msolver_inv n F A_arr A_inst
      (msolver_remove_clause M false c wm stats).
Proof.
  intros n F A_arr A_inst M c co pre post wm stats
    Hinv Hsplit Hfresh Hremove Hstats Hunlocked Hremoved.
  constructor.
  - eapply msolver_inv_weak_remove_problem__simplify;
      [exact (msi_weak Hinv) | exact Hsplit | exact Hfresh |
       exact Hremove | exact Hstats | exact Hunlocked | exact Hremoved].
  - cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact (msi_prop_level Hinv).
  - change (minisat_watch_frontier n
      (msolver_db (msolver_remove_clause M false c wm stats))
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M))).
    assert (HoldDB :
      msolver_db M = pre ++ (c, co) :: (post ++ ms_learnt M)).
    { unfold msolver_db. rewrite Hsplit.
      rewrite <- app_assoc. reflexivity. }
    assert (HnewDB :
      msolver_db (msolver_remove_clause M false c wm stats) =
        pre ++ (post ++ ms_learnt M)).
    { unfold msolver_db, msolver_remove_clause, msolver_propagation_overlay, msolver_propagation_update.
      cbn. rewrite Hsplit,
        db_remove_ptr_split__reducedb by exact Hfresh.
      rewrite app_assoc. reflexivity. }
    rewrite HnewDB.
    eapply minisat_watch_frontier_delete_middle__reducedb.
    rewrite <- HoldDB. exact (msi_watch_frontier Hinv).
  - cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update msolver_heap].
    exact (msi_heap_covers Hinv).
  - pose proof (msi_reasonless_current Hinv) as H.
    unfold current_reasonless_earliest, msolver_view, view_of in H |- *.
    cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ] in H |- *.
    exact H.
Qed.


Lemma solver_simplify_keep_compaction_inv__simplify :
  forall type M words i j,
    solver_simplify_db_compaction_inv type M words i j ->
    0 <= j -> j <= i -> i < Zlength words ->
    solver_simplify_db_compaction_inv type M
      (solver_simplify_keep_words words i j) (i + 1) (j + 1).
Proof.
  intros type M words i j Hinv Hj0 Hji HiN.
  unfold solver_simplify_db_compaction_inv in Hinv |- *.
  unfold solver_simplify_keep_words.
  destruct Hinv as [Htype [Hj0' [Hji' [HiN' Hdb]]]].
  assert (Hlen : Zlength (replace_Znth j (Znth i words 0) words) =
      Zlength words) by (rewrite Zlength_replace_Znth; lia).
  repeat split; try assumption; try lia.
  assert (Hprefix :
    sublist 0 (j + 1) (replace_Znth j (Znth i words 0) words) =
      sublist 0 j words ++ (Znth i words 0 :: nil)).
  { rewrite (replace_Znth_split j (Znth i words 0) words) by lia.
    set (A := sublist 0 j words).
    set (B := sublist (j + 1) (Zlength words) words).
    replace (A ++ Znth i words 0 :: B)
      with ((A ++ (Znth i words 0 :: nil)) ++ B)
      by (rewrite <- app_assoc; reflexivity).
    replace (j + 1)
      with (Zlength (A ++ (Znth i words 0 :: nil))).
    - rewrite sublist_app_exact1. reflexivity.
    - subst A. rewrite Zlength_app, Zlength_cons, Zlength_nil.
      rewrite Zlength_sublist by lia. lia. }
  assert (Hsuffix :
    sublist (i + 1) (Zlength words)
      (replace_Znth j (Znth i words 0) words) =
    sublist (i + 1) (Zlength words) words).
  { rewrite (replace_Znth_split j (Znth i words 0) words) by lia.
    set (A := sublist 0 j words).
    set (B := sublist (j + 1) (Zlength words) words).
    replace (A ++ Znth i words 0 :: B)
      with ((A ++ (Znth i words 0 :: nil)) ++ B)
      by (rewrite <- app_assoc; reflexivity).
    rewrite (sublist_split_app_r (i + 1) (Zlength words) (j + 1)
      (A ++ (Znth i words 0 :: nil)) B).
    - subst B. rewrite Zsublist_Zsublist by lia.
      replace (i + 1 - (j + 1) + (j + 1)) with (i + 1) by lia.
      replace (Zlength words - (j + 1) + (j + 1))
        with (Zlength words) by lia.
      reflexivity.
    - subst A. rewrite Zlength_app, Zlength_cons, Zlength_nil.
      rewrite Zlength_sublist by lia. lia.
    - lia. }
  assert (Htail : sublist i (Zlength words) words =
      (Znth i words 0 :: nil) ++
        sublist (i + 1) (Zlength words) words).
  { rewrite (sublist_split i (Zlength words) (i + 1) words) by lia.
    rewrite (sublist_single 0 i words) by lia. reflexivity. }
  rewrite Hlen, Hprefix, Hsuffix.
  rewrite Htail in Hdb.
  rewrite app_assoc in Hdb.
  exact Hdb.
Qed.

(** ===== group: solver_solve ===== *)
Lemma strict_sorted_bounded_length__solve :
  forall l L, 0 <= L -> strict_sorted l ->
    Forall (fun b => 0 <= b < L) l -> Zlength l <= L.
Proof.
  intros l L HL Hsorted Hrange.
  assert (Hnodup : NoDup l).
  { clear Hrange HL L. revert Hsorted.
    induction l as [|a l IH]; intro Hsorted.
    - constructor.
    - simpl in Hsorted. destruct Hsorted as [Hall Hsorted].
      constructor.
      + intro Hin. rewrite Forall_forall in Hall.
        specialize (Hall a Hin). lia.
      + apply IH. exact Hsorted. }
  rewrite Zlength_correct.
  apply NoDup_Z_bounded_length.
  - exact HL.
  - exact Hnodup.
  - intros x Hx. rewrite Forall_forall in Hrange. apply Hrange. exact Hx.
Qed.

Lemma reasons_match_assume_assuming__solve : forall n F A_arr A_proc M l,
  msolver_inv_assuming n F A_arr A_proc M -> lit_wf_c n l ->
  reasons_match n (ms_core (msolver_assume M l))
    (msolver_db (msolver_assume M l))
    (ms_reason_words (msolver_assume M l))
    (ms_reason_of (msolver_assume M l)).
Proof.
  intros n F A_arr A_proc M l Hinv Hl.
  exact (reasons_match_assume_core n M l
    (msa_shape Hinv) (msa_size Hinv) (msa_reasons_mem Hinv) Hl).
Qed.

Lemma reason_head_ok_assume_assuming__solve : forall n F A_arr A_proc M l,
  msolver_inv_assuming n F A_arr A_proc M -> lit_wf_c n l ->
  reason_head_ok (msolver_assume M l).
Proof.
  intros n F A_arr A_proc M l Hinv Hl.
  exact (reason_head_ok_assume_core n M l
    (msa_shape Hinv) (msa_size Hinv) (msa_reason_head Hinv) Hl).
Qed.

Lemma binary_reason_same_level_assume_assuming__solve :
  forall n F A_arr A_proc M l,
    msolver_inv_assuming n F A_arr A_proc M -> lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    binary_reason_same_level (msolver_assume M l).
Proof.
  intros n F A_arr A_proc M l Hinv Hl Hfresh.
  exact (binary_reason_same_level_assume_core n M l
    (msa_shape Hinv) (msa_size Hinv) (msa_trail_wf Hinv) (msa_reason_bin Hinv)
    (msa_reasons_mem Hinv) (msa_stable Hinv) Hl Hfresh).
Qed.

Lemma db_complete_assume_assuming__solve : forall n F A_arr A_proc M l,
  msolver_inv_assuming n F A_arr A_proc M -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  db_complete F (msolver_assume M l).
Proof.
  intros n F A_arr A_proc M l Hinv Hl Hfresh.
  exact (db_complete_assume_core n F M l
    (msa_db_complete Hinv) (msa_trail_wf Hinv) Hl Hfresh).
Qed.

Lemma current_reasonless_earliest_assume__solve :
  forall n F A_arr A_proc M l,
    msolver_inv_assuming n F A_arr A_proc M ->
    current_reasonless_earliest n M ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    current_reasonless_earliest n (msolver_assume M l).
Proof.
  intros n F A_arr A_proc M l Hinv Hold Hl Hfresh.
  exact (current_reasonless_assume_core n M l
    (msa_shape Hinv) (msa_size Hinv) (msa_trail_wf Hinv) Hold Hl Hfresh).
Qed.

Lemma assumption_prefix_snoc__solve : forall raw k,
  0 <= k < Zlength raw ->
  assumption_prefix raw (k + 1) =
  assumption_prefix raw k ++ (lit_denote (Znth k raw 0) :: nil).
Proof.
  intros raw k Hk. unfold assumption_prefix.
  rewrite (sublist_split 0 (k + 1) k raw) by lia.
  rewrite (sublist_single 0 k raw) by lia.
  rewrite lits_denote_app. reflexivity.
Qed.

Lemma assumption_fresh_transition_intro__solve :
  forall n F A_arr raw k M,
  msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) M ->
  assumption_fresh_ready n raw k M ->
  msolver_seed_shadow M ->
  ms_capacity_root_propagation_pending M = 0 ->
  A_arr = assumption_prefix raw (Zlength raw) ->
  Forall (lit_wf_c n) raw ->
  0 <= k -> k < Zlength raw ->
  assumption_fresh_transition n F A_arr raw k M
    (msolver_assume M (Znth k raw 0)).
Proof.
  intros n F A_arr raw k M Hstrong Hready Hseed Hpending
    Harr Hrawwf Hk0 Hklt.
  pose proof (msas_weak Hstrong) as Hweak.
  pose proof (msas_prop_level Hstrong) as Hprop.
  pose proof (msas_watch_frontier Hstrong) as Hwatch.
  pose proof (msas_heap_covers Hstrong) as Hheap.
  pose proof (msas_reasonless_current Hstrong) as Hreasonless.
  pose proof (msa_shape Hweak) as Hshape.
  pose proof (msa_trail_wf Hweak) as Htrailwf.
  pose proof (msa_size Hweak) as Hsize.
  unfold assumption_fresh_ready in Hready.
  destruct Hready as [Hsize' [Hdrain [Hfresh [Hlevelroom Henq]]]].
  unfold enqueue_input in Henq.
  destruct Henq as [Hlit [Htwice [Haslen [Hlvlen [Hrslen
    [Htrlen [Hqrange [Hroom Hcells]]]]]]]].
  set (l := Znth k raw 0).
  assert (Hfreshl : Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0)
    by exact Hfresh.
  assert (Hroomcap : ms_qtail M < ms_cap M).
  { specialize (Hroom Hfreshl). unfold solver_shape in Hshape. lia. }
  assert (Htrailnew : mtrail_wf n (ms_core (msolver_assume M l))).
  { unfold msolver_assume. cbn [ms_core].
    apply mtrail_wf_decide; assumption. }
  assert (Hassign := msolver_assume_assigns_one__search n M l
    Htrailwf Hlit Hfreshl).
  assert (Hsizenew : n = ms_size (msolver_assume M l)) by exact Hsize.
  assert (Hprefix : assumption_prefix raw (k + 1) =
      assumption_prefix raw k ++ (lit_denote l :: nil)).
  { unfold l. apply assumption_prefix_snoc__solve. lia. }
  assert (Hweaknew : msolver_inv_assuming n F A_arr
      (assumption_prefix raw (k + 1)) (msolver_assume M l)).
  { refine {| msa_size := Hsizenew; msa_n_range := msa_n_range Hweak;
      msa_shape := solver_shape_assume__search M l Hshape Hroomcap Hpending;
      msa_F_wf := msa_F_wf Hweak; msa_A_wf := msa_A_wf Hweak;
      msa_trail_wf := Htrailnew;
      msa_level_bound := _;
      msa_decisions := _; msa_proc_incl := _; msa_proc_sat := _;
      msa_stable := _; msa_reasons_ent := _; msa_reasons_inj := _;
      msa_trail_impl := _; msa_db_wf := msa_db_wf Hweak;
      msa_db_matches := msa_db_matches Hweak;
      msa_db_implied := msa_db_implied Hweak;
      msa_db_complete := db_complete_assume_assuming__solve
        n F A_arr (assumption_prefix raw k) M l Hweak Hlit Hfreshl;
      msa_learnt_db := msa_learnt_db Hweak; msa_prob_db := msa_prob_db Hweak;
      msa_binary_out := msa_binary_out Hweak;
      msa_reasons_mem := reasons_match_assume_assuming__solve
        n F A_arr (assumption_prefix raw k) M l Hweak Hlit;
      msa_reason_head := reason_head_ok_assume_assuming__solve
        n F A_arr (assumption_prefix raw k) M l Hweak Hlit;
      msa_reason_bin := binary_reason_same_level_assume_assuming__solve
        n F A_arr (assumption_prefix raw k) M l Hweak Hlit Hfreshl;
      msa_wmap_exact := msa_wmap_exact Hweak; msa_tags_clear := msa_tags_clear Hweak;
      msa_heap_wf := msa_heap_wf Hweak;
      msa_cla_inc_nonnegative := msa_cla_inc_nonnegative Hweak;
      msa_seed := msa_seed Hweak |}.
    - unfold msolver_assume, mt_decide, mt_push. cbn [ms_core mt_lim].
      rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    - destruct (msa_decisions Hweak) as [A_inst [Hdec Hincl]].
      exists (A_inst ++ (lit_denote l :: nil)). split.
      + unfold msolver_assume. cbn [ms_core].
        replace (Zlength (mt_lim (mt_decide (ms_core M) l))) with
          (Zlength (mt_lim (ms_core M)) + 1) by
          (unfold mt_decide, mt_push; cbn [mt_lim];
           rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
        rewrite (decisions_upto_decide_top n (ms_core M) l Htrailwf).
        rewrite Hdec. reflexivity.
      + rewrite Hprefix. intros a Ha.
        rewrite in_app_iff in Ha |- *. destruct Ha as [Ha|Ha];
          [left; apply Hincl; exact Ha|right; exact Ha].
    - rewrite Hprefix. intros a Ha.
      rewrite in_app_iff in Ha. destruct Ha as [Ha|Ha].
      + apply (msa_proc_incl Hweak) in Ha. exact Ha.
      + simpl in Ha. destruct Ha as [<-|[]].
        rewrite Harr. unfold assumption_prefix, lits_denote.
        apply in_map.
        replace (sublist 0 (Zlength raw) raw) with raw by
          (symmetry; apply sublist_self; reflexivity).
        apply Znth_In. lia.
    - rewrite Hprefix. apply Forall_app. split.
      + pose proof (msa_proc_sat Hweak) as Hold. revert Hold.
        apply Forall_impl. intros a Ha.
        unfold msolver_assume. cbn [ms_core].
        destruct (assump_true_at_root_decide__search n
          (ms_core M) l (Zlength (mt_lim (ms_core M))) a
          Htrailwf Hlit Hfreshl Ha) as [Htrue Hlevel].
        split; [exact Htrue|].
        eapply Z.le_trans; [exact Hlevel|].
        unfold mt_decide, mt_push. cbn [mt_lim].
        rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      + constructor; [|constructor].
        destruct Hassign as
          [Hxnone [Hxassign [Hxlevel [Hxreason [[rx [Hxrank Hdeps]] [Hother Hdb]]]]]].
        unfold assump_true_at_root. split.
        * rewrite lit_denote_satisfying. apply eval_satisfying_literal_true.
          change (assignment (msolver_view n (msolver_assume M l))
            (lit_var_c l) = Some (lit_pol l)). exact Hxassign.
        * rewrite lit_var_c_denote.
          unfold msolver_assume, mt_decide, mt_push.
          cbn [ms_core mt_levels mt_lim].
          rewrite Znth_replace_Znth_Same.
          2: { apply lit_var_c_in_range in Hlit.
               rewrite (mtw_levels_len Htrailwf). exact Hlit. }
          reflexivity.
    - eapply stable_view_decision_assign__search;
        [exact (msa_stable Hweak)|exact Hassign|].
      unfold msolver_view, msolver_assume, view_of, mt_decide, mt_push.
      cbn [current_level ms_core mt_lim].
      rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity.
    - eapply reasons_entailed_decision_assign__search;
        eauto using msa_reasons_ent.
    - eapply reasons_var_injective_decision_assign__search;
        eauto using msa_reasons_inj.
    - unfold msolver_assume. cbn [ms_core].
      eapply trail_implied_decision; eauto using msa_trail_impl.
  }
  assert (Hqhead : mt_qhead (ms_core M) = Zlength (mt_trail (ms_core M)))
    by lia.
  destruct (msolver_assume_prop_watch__search n M l
    Htrailwf Hlit Hfreshl Hqhead Hprop Hwatch) as [Hpropnew Hwatchnew].
  assert (Hreasonnew : current_reasonless_earliest n
      (msolver_assume M l)).
  { eapply current_reasonless_earliest_assume__solve;
      [exact Hweak|exact Hreasonless|exact Hlit|exact Hfreshl]. }
  assert (Hheapnew : heap_covers n (msolver_heap (msolver_assume M l))
      (mt_assigns (ms_core (msolver_assume M l)))
      (mt_trail (ms_core (msolver_assume M l)))
      (mt_qhead (ms_core (msolver_assume M l)))).
  { unfold msolver_assume, mt_decide, mt_push.
    cbn [msolver_heap ms_core mt_assigns mt_trail mt_qhead].
    eapply heap_covers_enqueue; [exact Hheap|lia| |].
    - intros v Hv Hvassigned.
      destruct (Z.eq_dec v (lit_var_c l)) as [->|Hvne].
      + rewrite Znth_replace_Znth_Same;
          [apply lit_sig_nonzero|].
        apply lit_var_c_in_range in Hlit. rewrite (mtw_assigns_len Htrailwf). lia.
      + rewrite Znth_replace_Znth_Diff;
          [exact Hvassigned| | |congruence].
        * apply lit_var_c_in_range in Hlit. rewrite (mtw_assigns_len Htrailwf).
          exact Hlit.
        * rewrite (mtw_assigns_len Htrailwf). exact Hv.
    - intros i Hi. rewrite app_Znth1; reflexivity || lia.
  }
  unfold assumption_fresh_transition. fold l.
  split; [reflexivity|]. split.
  - split; [change (ms_capacity_root_propagation_pending M = 0); exact Hpending|].
    refine {| msap_weak := Hweaknew; msap_prop_level := Hpropnew;
      msap_watch_frontier := Hwatchnew; msap_heap_ready := or_introl Hheapnew;
      msap_reasonless_current := Hreasonnew |}.
  - change (msolver_seed_shadow M). exact Hseed.
Qed.

Lemma assume_post_refold_assigns_levels__solve :
  forall wl s asg lvl l n cap qtail assigns levels reasons trail lim M,
  n = ms_size M -> cap = ms_cap M -> qtail = ms_qtail M ->
  assigns = mt_assigns (ms_core M) -> levels = mt_levels (ms_core M) ->
  reasons = ms_reason_words M -> trail = mt_trail (ms_core M) ->
  lim = mt_lim (ms_core M) ->
  solver_shape M -> ms_qtail M < ms_cap M ->
  ms_capacity_root_propagation_pending M = 0 ->
  mt_qhead (ms_core M) = ms_qtail M ->
  Znth (lit_var_c l) assigns 0 = 0 ->
  assume_post_at s asg lvl l n cap qtail assigns levels reasons trail lim **
  solver_assume_frame_wl s M wl
  |-- solver_rep_assigns_levels_at s (msolver_assume M l) asg lvl wl.
Proof.
  intros wl s asg lvl l n cap qtail assigns levels reasons trail lim M
    Hn Hcap Hq Hassigns Hlevels Hreasons Htrail Hlim
    Hshape Hroom Hpending Hdrain Hfresh.
  subst n. subst cap. subst qtail. subst assigns. subst levels.
  subst reasons. subst trail. subst lim.
  assert (Htrailq : Zlength (mt_trail (ms_core M)) = ms_qtail M).
  { unfold solver_shape in Hshape. tauto. }
  unfold assume_post_at.
  assert (Hshapenew : solver_shape (msolver_assume M l)).
  { eapply solver_shape_assume__search; eauto. }
  unfold enqueue_post_at. Intros qtail' assigns' levels' reasons' trail'.
  unfold enqueue_state_at. Intros rsn trl.
  unfold enqueue_transition in *.
  match goal with
  | Ht : _ \/ (_ \/ _) |- _ =>
      destruct Ht as [Hsame | [Hconflict | Hnew]]
  end.
  - destruct Hsame as [Hsame _]. rewrite Hfresh in Hsame.
    pose proof (lit_sig_nonzero l). lia.
  - destruct Hconflict as [Hne _]. contradiction.
  - destruct Hnew as
      [Hz [_ [Hassigns' [Hlevels' [Hreasons' [Htrail' Hqtail']]]]]].
    subst assigns'. subst levels'. subst reasons'. subst trail'. subst qtail'.
    unfold solver_assume_frame_wl, solver_enqueue_frame_with_scalars_wl, solver_enqueue_cells_at.
    Intros act opos tgs.
    unfold solver_rep_assigns_levels_at, solver_rep_at.
    Exists act opos rsn trl tgs.
    unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_assume_scalars_frame,
      solver_vecs_without_lim_rep, msolver_assume.
    unfold solver_fp_rep, solver_scalars_rep, solver_vecs_rep,
      solver_var_arrays_rep, solver_trail_array_rep,
      solver_levels_slice_at.
    try rewrite Hdrain.
    try rewrite Htrailq.
    (* Reduce record projections after unfolding representations, which
   introduces the projection redexes; this keeps records out of unification. *)
    cbn [mt_decide mt_push ms_size ms_cap ms_qtail ms_capacity_pending_qhead
      ms_capacity_root_propagation_pending ms_core ms_root_level
      ms_reason_words ms_reason_of ms_prob ms_learnt ms_binary ms_binary_lits ms_wm ms_activity
      ms_orderpos ms_order ms_model
      ms_tags ms_tagged ms_stack ms_var_inc
      ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed ms_progress
      ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats].
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
    cbn.
    cancel.
    rewrite Hdrain.
    rewrite Htrailq.
    unfold DoubleArray.seg, IntArray.seg, CharArray.seg, PtrArray.seg,
      StoreDoubleAsElement.storeA, store_double, bits_of_double_value.
    cbn.
    msat_entailer_with lia.
Qed.

Lemma assumption_root_install_intro__solve :
  forall n F A_arr M,
  msolver_inv_assuming_strong n F A_arr A_arr M ->
  ms_capacity_root_propagation_pending M = 0 ->
  msolver_seed_shadow M ->
  assumption_root_install n F A_arr M
    (msolver_set_root M (Zlength (mt_lim (ms_core M))))
    (decisions_upto (ms_core M) (Zlength (mt_lim (ms_core M)))).
Proof.
  intros n F A_arr M Hstrong Hpending Hseed.
  pose proof (msas_weak Hstrong) as Hweak.
  set (L := Zlength (mt_lim (ms_core M))).
  set (Mroot := msolver_set_root M L).
  set (A_inst := decisions_upto (ms_core M) L).
  assert (Hroot_shape : solver_shape Mroot).
  { pose proof (msa_shape Hweak) as Hshape.
    unfold solver_shape in Hshape |- *.
    unfold Mroot, msolver_set_root, msolver_core_heap_update.
    cbn in *.
    pose proof (Zlength_nonneg (mt_lim (ms_core M))).
    tauto. }
  assert (Hroot_weak : msolver_inv_weak n F A_arr A_inst Mroot).
  { constructor; cbn [Mroot msolver_set_root msolver_core_heap_update].
    - exact (msa_size Hweak).
    - exact (msa_n_range Hweak).
    - exact Hroot_shape.
    - exact (msa_F_wf Hweak).
    - exact (msa_A_wf Hweak).
    - exact (msa_trail_wf Hweak).
    - exact (msa_level_bound Hweak).
    - unfold Mroot, L, msolver_set_root, msolver_core_heap_update. cbn.
      pose proof (Zlength_nonneg (mt_lim (ms_core M))). lia.
    - unfold Mroot, A_inst, msolver_set_root, msolver_core_heap_update. cbn.
      reflexivity.
    - destruct (msa_decisions Hweak) as [A0 [Hdec Hincl]].
      unfold Mroot, A_inst, L, msolver_set_root, msolver_core_heap_update. cbn.
      rewrite Hdec. exact Hincl.
    - unfold Mroot, L, msolver_set_root, msolver_core_heap_update. cbn.
      exact (msa_proc_sat Hweak).
    - exact (msa_stable Hweak).
    - exact (msa_reasons_ent Hweak).
    - exact (msa_reasons_inj Hweak).
    - exact (msa_trail_impl Hweak).
    - exact (msa_db_wf Hweak).
    - exact (msa_db_matches Hweak).
    - exact (msa_db_implied Hweak).
    - exact (msa_db_complete Hweak).
    - exact (msa_learnt_db Hweak).
    - exact (msa_prob_db Hweak).
    - exact (msa_binary_out Hweak).
    - exact (msa_reasons_mem Hweak).
    - exact (msa_reason_head Hweak).
    - exact (msa_reason_bin Hweak).
    - exact (msa_wmap_exact Hweak).
    - exact (msa_tags_clear Hweak).
    - exact (msa_heap_wf Hweak).
    - exact (msa_cla_inc_nonnegative Hweak).
    - exact (msa_seed Hweak). }
  assert (Hroot_inv : msolver_inv n F A_arr A_inst Mroot).
  { constructor; cbn [Mroot msolver_set_root msolver_core_heap_update].
    - exact Hroot_weak.
    - exact (msas_prop_level Hstrong).
    - exact (msas_watch_frontier Hstrong).
    - exact (msas_heap_covers Hstrong).
    - unfold current_reasonless_earliest.
      intros d Hd. exfalso.
      unfold Mroot, L, msolver_set_root, msolver_core_heap_update in Hd.
      cbn in Hd. lia. }
  unfold assumption_root_install.
  repeat apply conj.
  - unfold A_inst, L. reflexivity.
  - unfold Mroot, L. reflexivity.
  - exact Hroot_inv.
  - unfold solver_at_root, Mroot, L, msolver_set_root,
      msolver_core_heap_update. cbn. reflexivity.
  - unfold Mroot, msolver_set_root, msolver_core_heap_update. cbn.
    exact Hpending.
  - unfold Mroot, msolver_set_root, msolver_core_heap_update. cbn.
    exact Hseed.
Qed.

Lemma sort_Znth_in__solve : forall db origin current k,
  learnt_sort_segment_domain db origin ->
  Permutation origin current ->
  0 <= k < Zlength current ->
  In (Znth k current 0) (db_words db).
Proof.
  intros db origin current k Hdomain Hperm Hk.
  unfold learnt_sort_segment_domain in Hdomain.
  rewrite Forall_forall in Hdomain.
  apply Hdomain.
  eapply Permutation_in.
  - apply Permutation_sym. exact Hperm.
  - apply Znth_In. exact Hk.
Qed.

Lemma sort_Znth_in_sep__solve : forall db origin current k P,
  learnt_sort_segment_domain db origin ->
  Permutation origin current ->
  0 <= k < Zlength current ->
  P |-- “ In (Znth k current 0) (db_words db) ”.
Proof.
  intros db origin current k P Hdomain Hperm Hk.
  pose proof (sort_Znth_in__solve
    db origin current k Hdomain Hperm Hk).
  msat_entailer_with lia.
Qed.

Lemma replace_znth_swap_form__solve :
  forall (l1 l2 l3 : list Z) (xi xj : Z),
  replace_Znth (Zlength l1 + 1 + Zlength l2) xi
    (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
  l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with (l1 := l1)
    (l2 := (xi :: l2 ++ xj :: l3)) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := Z) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (H0 : replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
               xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with (l1 := l1)
    (l2 := (xj :: l2 ++ xj :: l3)) by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := Z)
    (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := (xj :: l3)) by lia.
  rewrite (replace_Znth_nothing (A := Z) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3) by reflexivity.
  rewrite H1. reflexivity.
Qed.

Lemma permutation_swap_znth_lt__solve : forall
    (l : list Z) i j d,
  0 <= i /\ i < j /\ j < Zlength l ->
  Permutation l
    (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros l i j d (Hi & Hij & Hj).
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  { subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi0. reflexivity. }
  assert (Hj_lr : (nj < List.length lr)%nat).
  { subst nj lr ni. rewrite length_skipn.
    rewrite Zlength_correct in Hj. lia. }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  { subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{ subst nj lr ni. rewrite Heqxj0. unfold Znth. rewrite nth_skipn.
        assert (Hnat :
          (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
        { apply Nat2Z.inj. rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
          rewrite !Z2Nat.id by lia. lia. }
        rewrite Nat.add_comm, Hnat. reflexivity. }
    reflexivity. }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  { rewrite Hsplit_j in Hsplit_i. exact Hsplit_i. }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3)
    by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{ subst l1 ni. rewrite Zlength_correct, length_firstn.
      rewrite Zlength_correct in Hj. rewrite Nat.min_l by lia. lia. }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{ subst l1 l2 lr ni nj. rewrite !Zlength_correct.
      rewrite !length_firstn, length_skipn.
      rewrite Zlength_correct in Hj. lia. }
  rewrite replace_znth_swap_form__solve.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head. apply perm_swap.
    + apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma selectionsort_swap_perm__solve : forall
    (l : list Z) i j,
  0 <= i < Zlength l ->
  i <= j < Zlength l ->
  Permutation l
    (replace_Znth j (Znth i l 0) (replace_Znth i (Znth j l 0) l)).
Proof.
  intros l i j Hi Hj.
  destruct (Z.eq_dec i j) as [-> | Hne].
  - rewrite replace_Znth_Znth by lia.
    rewrite replace_Znth_Znth by lia.
    apply Permutation_refl.
  - apply permutation_swap_znth_lt__solve. lia.
Qed.

Lemma learnt_sort_key_in__solve : forall
    db activities p co a,
  learnt_sort_key db activities p co a ->
  In p (db_words db).
Proof.
  induction db as [|[q cq] db IH]; intros activities p co a Hkey;
    destruct activities as [|aq activities]; simpl in *; try contradiction.
  destruct Hkey as [[-> [_ _]] | Hkey].
  - left. reflexivity.
  - right. eapply IH; eauto.
Qed.

Lemma learnt_sort_key_unique__solve : forall
    db activities p co1 co2 a1 a2,
  NoDup (db_words db) ->
  learnt_sort_key db activities p co1 a1 ->
  learnt_sort_key db activities p co2 a2 ->
  co1 = co2 /\ a1 = a2.
Proof.
  induction db as [|[q cq] db IH];
    intros activities p co1 co2 a1 a2 Hnodup Hkey1 Hkey2;
    destruct activities as [|aq activities]; simpl in *; try contradiction.
  inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
  destruct Hkey1 as [[Hp1 [Hco1 Ha1]] | Hkey1];
    destruct Hkey2 as [[Hp2 [Hco2 Ha2]] | Hkey2].
  - subst. split; reflexivity.
  - subst. exfalso. apply Hnotin.
    eapply learnt_sort_key_in__solve; eauto.
  - subst. exfalso. apply Hnotin.
    eapply learnt_sort_key_in__solve; eauto.
  - eapply IH; eauto.
Qed.

Lemma learnt_sort_key_nonnegative__solve : forall
    db activities p co a,
  Forall msat_fp32_nonnegative activities ->
  learnt_sort_key db activities p co a ->
  msat_fp32_nonnegative a.
Proof.
  induction db as [|[q cq] db IH]; intros activities p co a Hnonneg Hkey;
    destruct activities as [|aq activities]; simpl in *; try contradiction.
  inversion Hnonneg as [|? ? Ha Hnonneg']; subst.
  destruct Hkey as [[_ [_ ->]] | Hkey].
  - exact Ha.
  - eapply IH; eauto.
Qed.

Lemma learnt_cmp_stop_refl__solve : forall
    db activities x,
  learnt_sort_context db activities ->
  learnt_cmp_stop db activities x x.
Proof.
  intros db activities x Hcontext Hlt.
  unfold learnt_cmp_lt in Hlt.
  destruct Hlt as
    (cox & coy & ax & ay & Hkeyx & Hkeyy & Hlong & Hlast).
  unfold learnt_sort_context in Hcontext.
  destruct Hcontext as (Hnodup & _ & Hnonneg).
  pose proof (learnt_sort_key_unique__solve
    db activities x cox coy ax ay Hnodup Hkeyx Hkeyy) as [Hco Ha].
  subst coy ay.
  destruct Hlast as [Hbinary | Hflt].
  - lia.
  - pose proof (learnt_sort_key_nonnegative__solve
      db activities x cox ax Hnonneg Hkeyx) as Hax.
    pose proof (MSatFloatFacts.fp32_nonnegative_eq_refl ax Hax) as Heq.
    unfold fp32_eq, fp32_lt in *. congruence.
Qed.

Lemma sortrnd_initial_partition__solve : forall
    db activities origin k,
  learnt_sort_context db activities ->
  learnt_sort_segment_domain db origin ->
  0 <= k < Zlength origin ->
  sortrnd_partition_inv db activities origin origin (Zlength origin)
    (Znth k origin 0) (-1) (Zlength origin).
Proof.
  intros db activities origin k Hcontext Hdomain Hk.
  pose proof (sort_Znth_in__solve
    db origin origin k Hdomain (Permutation_refl origin) Hk) as Hin.
  pose proof (learnt_cmp_stop_refl__solve
    db activities (Znth k origin 0) Hcontext) as Hstop.
  unfold sortrnd_partition_inv.
  split; [exact Hdomain|].
  split; [exact Hcontext|].
  split; [exact Hin|].
  split; [apply Permutation_refl|].
  split; [reflexivity|].
  split; [lia|].
  split; [lia|].
  exists k, k. repeat split; try assumption; lia.
Qed.

(** ===== group: sortrnd ===== *)
Lemma learnt_sort_segment_domain_perm__sortrnd : forall db l1 l2,
  Permutation l1 l2 ->
  learnt_sort_segment_domain db l1 -> learnt_sort_segment_domain db l2.
Proof.
  intros db l1 l2 Hperm Hdom.
  unfold learnt_sort_segment_domain in *.
  rewrite Forall_forall in *.
  intros x Hx.
  apply Hdom.
  eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hx].
Qed.

Lemma learnt_sort_segment_domain_Znth__sortrnd : forall db l i,
  learnt_sort_segment_domain db l -> 0 <= i < Zlength l ->
  In (Znth i l 0) (db_words db).
Proof.
  intros db l i Hdom Hi.
  apply (Forall_Znth_elim _ _ _ 0 i Hdom Hi).
Qed.

Lemma learnt_cmp_result_neg_not_stop__sortrnd : forall db acts x y r,
  learnt_cmp_result db acts x y r -> r < 0 ->
  ~ learnt_cmp_stop db acts x y.
Proof.
  intros db acts x y r Hcmp Hr Hstop.
  destruct Hcmp as [[Heq Hlt] | [Heq Hstop']].
  - apply Hstop. exact Hlt.
  - lia.
Qed.

Lemma learnt_cmp_result_nonneg_stop__sortrnd : forall db acts x y r,
  learnt_cmp_result db acts x y r -> r >= 0 ->
  learnt_cmp_stop db acts x y.
Proof.
  intros db acts x y r Hcmp Hr.
  destruct Hcmp as [[Heq Hlt] | [Heq Hstop]].
  - lia.
  - exact Hstop.
Qed.

Lemma perm_move_in__sortrnd : forall (A : Type) (d a : A)
    (l : list A) (k : nat),
  (k < List.length l)%nat ->
  Permutation (a :: l) (nth k l d :: replace_nth k l a).
Proof.
  intros A d a l.
  induction l as [|b l' IH]; intros k Hk; simpl in Hk.
  - exfalso. inversion Hk.
  - destruct k as [|k']; simpl.
    + apply perm_swap.
    + eapply Permutation_trans; [apply perm_swap |].
      eapply Permutation_trans.
      * apply perm_skip. apply (IH k'). lia.
      * apply perm_swap.
Qed.

Lemma perm_swap_nth__sortrnd : forall (A : Type) (d : A)
    (l : list A) (i j : nat),
  (i < List.length l)%nat -> (j < List.length l)%nat ->
  Permutation l
    (replace_nth j (replace_nth i l (nth j l d)) (nth i l d)).
Proof.
  intros A d l.
  induction l as [|a l' IH]; intros i j Hi Hj; simpl in Hi, Hj.
  - exfalso. inversion Hi.
  - destruct i as [|i']; destruct j as [|j']; simpl.
    + apply Permutation_refl.
    + apply perm_move_in__sortrnd. lia.
    + apply perm_move_in__sortrnd. lia.
    + apply perm_skip. apply IH; lia.
Qed.

Lemma perm_swap_Znth__sortrnd : forall (l : list Z) (i j : Z),
  0 <= i < Zlength l -> 0 <= j < Zlength l ->
  Permutation l
    (replace_Znth j (Znth i l 0)
       (replace_Znth i (Znth j l 0) l)).
Proof.
  intros l i j Hi Hj.
  rewrite Zlength_correct in Hi, Hj.
  unfold replace_Znth, Znth.
  apply (perm_swap_nth__sortrnd Z 0 l
           (Z.to_nat i) (Z.to_nat j)); lia.
Qed.

Lemma sortrnd_left_scan_step__sortrnd :
  forall db acts origin cur size pivot i j r,
  sortrnd_partition_inv db acts origin cur size pivot (i - 1) j ->
  learnt_cmp_result db acts (Znth i cur 0) pivot r ->
  r < 0 ->
  Zlength cur = size -> 0 <= i -> i < size -> 0 < j -> j <= size ->
  i + 1 < Zlength cur /\
  sortrnd_partition_inv db acts origin cur (Zlength cur) pivot i j.
Proof.
  intros db acts origin cur size pivot i j r Hinv Hcmp Hr Hlen
         Hi0 Hilt Hj0 Hjle.
  unfold sortrnd_partition_inv in Hinv.
  destruct Hinv as
    [Hdom [Hctx [Hpiv [Hperm [Hcl [Hij [Hjr [L [R Hex]]]]]]]]].
  destruct Hex as
    [[HLlo HLhi] [HLj [[HRlo HRhi] [HstopL HstopR]]]].
  assert (HLne : L <> i).
  { intro Heq. subst L.
    exact (learnt_cmp_result_neg_not_stop__sortrnd
             _ _ _ _ _ Hcmp Hr HstopL). }
  split; [lia |].
  unfold sortrnd_partition_inv.
  split; [exact Hdom |].
  split; [exact Hctx |].
  split; [exact Hpiv |].
  split; [exact Hperm |].
  split; [reflexivity |].
  split; [lia |].
  split; [lia |].
  exists L, R.
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; assumption.
Qed.

Lemma sortrnd_left_scan_entry__sortrnd :
  forall db acts origin cur size pivot i j,
  sortrnd_partition_inv db acts origin cur size pivot i j ->
  Zlength cur = size ->
  i + 1 < Zlength cur /\
  sortrnd_partition_inv db acts origin cur (Zlength cur) pivot i j.
Proof.
  intros db acts origin cur size pivot i j Hinv Hlen.
  pose proof Hinv as Hinv'.
  unfold sortrnd_partition_inv in Hinv.
  destruct Hinv as
    [Hdom [Hctx [Hpiv [Hperm [Hcl [Hij [Hjr [L [R Hex]]]]]]]]].
  destruct Hex as
    [[HLlo HLhi] [HLj [[HRlo HRhi] [HstopL HstopR]]]].
  split; [lia |].
  rewrite Hlen. exact Hinv'.
Qed.

Lemma sortrnd_right_scan_step__sortrnd :
  forall db acts origin cur size pivot i j r,
  sortrnd_right_scan_inv db acts origin cur size pivot i (j + 1) ->
  learnt_cmp_result db acts pivot (Znth j cur 0) r ->
  r < 0 ->
  Zlength cur = size -> 0 <= j -> j < size ->
  0 <= j - 1 /\
  sortrnd_right_scan_inv db acts origin cur (Zlength cur) pivot i j.
Proof.
  intros db acts origin cur size pivot i j r Hinv Hcmp Hr Hlen
         Hj0 Hjlt.
  unfold sortrnd_right_scan_inv in Hinv.
  destruct Hinv as
    [Hdom [Hctx [Hpiv [Hperm [Hcl [Hi [Hj [HstopI
      [R [HR HstopR]]]]]]]]]].
  assert (HRne : R <> j).
  { intro Heq. subst R.
    exact (learnt_cmp_result_neg_not_stop__sortrnd
             _ _ _ _ _ Hcmp Hr HstopR). }
  split; [lia |].
  unfold sortrnd_right_scan_inv.
  split; [exact Hdom |].
  split; [exact Hctx |].
  split; [exact Hpiv |].
  split; [exact Hperm |].
  split; [reflexivity |].
  split; [lia |].
  split; [lia |].
  split; [exact HstopI |].
  exists R. split; [lia | exact HstopR].
Qed.

Lemma sortrnd_right_scan_entry__sortrnd :
  forall db acts origin cur size pivot i j r,
  sortrnd_partition_inv db acts origin cur size pivot (i - 1) j ->
  learnt_cmp_result db acts (Znth i cur 0) pivot r ->
  r >= 0 ->
  Zlength cur = size -> 0 <= i -> i < size -> 0 < j -> j <= size ->
  sortrnd_right_scan_inv db acts origin cur (Zlength cur) pivot i j.
Proof.
  intros db acts origin cur size pivot i j r Hinv Hcmp Hr Hlen
         Hi0 Hilt Hj0 Hjle.
  unfold sortrnd_partition_inv in Hinv.
  destruct Hinv as
    [Hdom [Hctx [Hpiv [Hperm [Hcl [Hij [Hjr [L [R Hex]]]]]]]]].
  destruct Hex as
    [[HLlo HLhi] [HLj [[HRlo HRhi] [HstopL HstopR]]]].
  unfold sortrnd_right_scan_inv.
  split; [exact Hdom |].
  split; [exact Hctx |].
  split; [exact Hpiv |].
  split; [exact Hperm |].
  split; [reflexivity |].
  split; [lia |].
  split; [lia |].
  split.
  - exact (learnt_cmp_result_nonneg_stop__sortrnd
             _ _ _ _ _ Hcmp Hr).
  - exists R. split; [lia | exact HstopR].
Qed.

Lemma sortrnd_swap_preserves_partition_inv__sortrnd :
  forall db acts origin cur size pivot i j r,
  sortrnd_right_scan_inv db acts origin cur size pivot i (j + 1) ->
  learnt_cmp_result db acts pivot (Znth j cur 0) r ->
  r >= 0 -> i < j ->
  Zlength cur = size -> 0 <= i -> i < size -> 0 <= j -> j < size ->
  sortrnd_partition_inv db acts origin
    (replace_Znth j (Znth i cur 0)
       (replace_Znth i (Znth j cur 0) cur))
    size pivot i j.
Proof.
  intros db acts origin cur size pivot i j r Hinv Hcmp Hr Hij Hlen
         Hi0 Hilt Hj0 Hjlt.
  unfold sortrnd_right_scan_inv in Hinv.
  destruct Hinv as
    [Hdom [Hctx [Hpiv [Hperm [Hcl [Hi [Hj [HstopI
      [R [HR HstopR]]]]]]]]]].
  set (cur' := replace_Znth j (Znth i cur 0)
                 (replace_Znth i (Znth j cur 0) cur)).
  assert (Hlen' : Zlength cur' = Zlength cur).
  { unfold cur'. rewrite Zlength_replace_Znth, Zlength_replace_Znth.
    reflexivity. }
  assert (Hatj : Znth j cur' 0 = Znth i cur 0).
  { unfold cur'. apply Znth_replace_Znth_Same.
    rewrite Zlength_replace_Znth. lia. }
  assert (Hati : Znth i cur' 0 = Znth j cur 0).
  { unfold cur'.
    rewrite Znth_replace_Znth_Diff
      by (rewrite ?Zlength_replace_Znth; lia).
    apply Znth_replace_Znth_Same. lia. }
  unfold sortrnd_partition_inv.
  split; [exact Hdom |].
  split; [exact Hctx |].
  split; [exact Hpiv |].
  split.
  { eapply Permutation_trans; [exact Hperm |].
    unfold cur'. apply perm_swap_Znth__sortrnd; lia. }
  split; [lia |].
  split; [lia |].
  split; [lia |].
  exists j, i.
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split.
  - rewrite Hatj. exact HstopI.
  - rewrite Hati.
    exact (learnt_cmp_result_nonneg_stop__sortrnd
             _ _ _ _ _ Hcmp Hr).
Qed.

Lemma clause_db_rep_learnt_to_sort__sortrnd : forall db,
  learnt_db db ->
  clause_db_rep db |--
    EX activities : list fp32,
      “ Zlength activities = Zlength db /\
        Forall msat_fp32_nonnegative activities ” &&
      learnt_sort_rep db activities.
Proof.
  intros db. induction db as [|[p co] db IH]; intros Hlearnt.
  - cbn [clause_db_rep]. Exists (@nil fp32).
    cbn [learnt_sort_rep]. (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - inversion Hlearnt as [|e rest Htag Htail]; subst.
    cbn in Htag.
    cbn [clause_db_rep].
    unfold MiniSatClause.rep.
    cbn [fst snd].
    rewrite Htag.
    unfold activity_state.
    Intros a.
    sep_apply (IH Htail).
    Intros activities.
    Exists (a :: activities).
    cbn [learnt_sort_rep]. rewrite Htag.
    split_pure_spatial.
    + cancel. cancel.
    + split_pures.
      * dump_pre_spatial. split.
        -- rewrite !Zlength_cons. lia.
        -- constructor; [exact H0 | exact (proj2 H1)].
      * dump_pre_spatial. split; [reflexivity | split; [lia | split; [lia | exact H0]]].
Qed.

Lemma learnt_sort_rep_to_clause_db__sortrnd : forall db activities,
  learnt_sort_rep db activities |-- clause_db_rep db.
Proof.
  intros db. induction db as [|[p co] db IH]; intros activities.
  - destruct activities; cbn [learnt_sort_rep clause_db_rep].
    + cancel emp.
    + apply coq_prop_False_left. tauto.
  - destruct activities as [|a activities].
    + cbn [learnt_sort_rep]. apply coq_prop_False_left. tauto.
    + cbn [learnt_sort_rep]. Intros_p Hhead.
      destruct Hhead as [Htag [Hp [Hmod Hnonneg]]].
      sep_apply (IH activities).
      cbn [clause_db_rep fst snd].
      unfold MiniSatClause.rep.
      rewrite Htag.
      unfold activity_state.
      Exists a.
      split_pure_spatial.
      * cancel (clause_db_rep db).
        cancel (clause_hdr_addr p # Int |-> clause_hdr_word true (Zlength (co_lits co))).
        cancel (clause_act_addr p (Zlength (co_lits co)) # Float |-> a).
        cancel (IntArray.seg (clause_lits_addr p) 0 (Zlength (co_lits co)) (co_lits co)).
      * split_pures; dump_pre_spatial.
        -- pose proof (Zlength_nonneg (co_lits co)). lia.
        -- exact Hnonneg.
Qed.

