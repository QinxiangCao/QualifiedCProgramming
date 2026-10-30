From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Export
  solver_qcp_analysis_lib
  solver_qcp_state_search_lib
  solver_qcp_solver_propagate_lib.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** ===== group: other facts ===== *)
Lemma clause_hdr_word_nonneg_entail :
  forall (A : Type) (H : Assertion) (learnt : bool) (lits : list A),
    H |-- “ 0 <= clause_hdr_word learnt (Zlength lits) ”.
Proof.
  intros A H learnt lits.
  apply derivable1s_coq_prop_r.
  apply clause_hdr_word_nonneg.
  apply Zlength_nonneg.
Qed.

Lemma minisat_base_watch_completed_same_fields__api_reentry : forall M M',
  msolver_db M' = msolver_db M ->
  mt_assigns (ms_core M') = mt_assigns (ms_core M) ->
  mt_levels (ms_core M') = mt_levels (ms_core M) ->
  mt_trail (ms_core M') = mt_trail (ms_core M) ->
  mt_qhead (ms_core M') = mt_qhead (ms_core M) ->
  minisat_base_watch_completed M -> minisat_base_watch_completed M'.
Proof.
  intros M M' Hdb Ha Hl Ht Hq.
  unfold minisat_base_watch_completed. rewrite Hdb, Ha, Hl, Ht, Hq. trivial.
Qed.

Lemma minisat_base_watch_completed_except_same_fields__api_reentry : forall M M' p,
  msolver_db M' = msolver_db M ->
  mt_assigns (ms_core M') = mt_assigns (ms_core M) ->
  mt_levels (ms_core M') = mt_levels (ms_core M) ->
  mt_trail (ms_core M') = mt_trail (ms_core M) ->
  mt_qhead (ms_core M') = mt_qhead (ms_core M) ->
  minisat_base_watch_completed_except M p -> minisat_base_watch_completed_except M' p.
Proof.
  intros M M' p Hdb Ha Hl Ht Hq.
  unfold minisat_base_watch_completed_except. rewrite Hdb, Ha, Hl, Ht, Hq. trivial.
Qed.

Lemma minisat_base_scan_completed_close__api_reentry : forall M focus,
  minisat_base_watch_completed_except M focus ->
  minisat_base_scan_completed M focus nil ->
  minisat_base_watch_completed M.
Proof.
  intros M focus Hexcept Hscan owner co Hin.
  destruct (Hexcept owner co Hin) as [Hleft Hright].
  split; intros Hprocessed Hzero.
  - destruct (Z.eq_dec (lit_neg_c (co_watch0 co)) focus) as [Heq|Hneq].
    + assert (Hfocuszero : Znth (lit_var_c focus) (mt_levels (ms_core M)) 0 = 0).
      { rewrite <- Heq, lit_var_c_neg. exact Hzero. }
      exact (proj1 (Hscan
        (if 3 <=? Zlength (co_lits co) then owner else tag_of_lit (co_watch1 co))
        ltac:(intro H; inversion H) Hfocuszero owner co Hin) Heq eq_refl).
    + exact (Hleft Hneq Hprocessed Hzero).
  - destruct (Z.eq_dec (lit_neg_c (co_watch1 co)) focus) as [Heq|Hneq].
    + assert (Hfocuszero : Znth (lit_var_c focus) (mt_levels (ms_core M)) 0 = 0).
      { rewrite <- Heq, lit_var_c_neg. exact Hzero. }
      exact (proj2 (Hscan
        (if 3 <=? Zlength (co_lits co) then owner else tag_of_lit (co_watch0 co))
        ltac:(intro H; inversion H) Hfocuszero owner co Hin) Heq eq_refl).
    + exact (Hright Hneq Hprocessed Hzero).
Qed.

Lemma minisat_resident_false_same_fields__api_reentry : forall M M',
  msolver_db M' = msolver_db M ->
  mt_assigns (ms_core M') = mt_assigns (ms_core M) ->
  minisat_resident_false_clause M -> minisat_resident_false_clause M'.
Proof.
  intros M M' Hdb Hassign [owner [co [Hin Hfalse]]].
  exists owner, co. rewrite Hdb, Hassign. auto.
Qed.

Lemma minisat_resident_false_scan_finish__api_reentry : forall M inspect,
  minisat_resident_false_clause M ->
  minisat_resident_false_clause (msolver_propagation_scan_finish M inspect).
Proof.
  intros M inspect. apply minisat_resident_false_same_fields__api_reentry;
    reflexivity.
Qed.

Lemma minisat_propagation_reuse_scan_finish__api_reentry :
  forall n entry M p confl inspect,
    minisat_propagation_reuse_scan entry M p confl nil ->
    (confl <> 0 -> level_of (msolver_view n M) (lit_var_c p) =
      Some (Zlength (mt_lim (ms_core M)))) ->
    minisat_propagation_reuse_loop n entry
      (msolver_propagation_scan_finish M inspect) confl.
Proof.
  intros n entry M p confl inspect [Hcomplete [Hresident Hconflict]] Hlevel.
  split.
  - intro Hentry. destruct (Hcomplete Hentry) as [Hexcept Hpending]. split.
    + intro Hzero.
      eapply minisat_base_watch_completed_same_fields__api_reentry;
        try reflexivity.
      apply minisat_base_scan_completed_close__api_reentry with (focus:=p);
        [exact Hexcept|exact (Hpending Hzero)].
    + intro Hnonzero. exists p. split.
      * exact (Hlevel Hnonzero).
      * eapply minisat_base_watch_completed_except_same_fields__api_reentry;
          try reflexivity; exact Hexcept.
  - split; intro H.
    + apply minisat_resident_false_scan_finish__api_reentry. exact (Hresident H).
    + apply minisat_resident_false_scan_finish__api_reentry. exact (Hconflict H).
Qed.

(** * Solver bundle joins.
    Keep scalar, floating-point and vector state folded when joining a
    remainder with its missing field. This reduces entailment cancellation
    work compared with unfolding both sides to individual cells. *)

Lemma scalars_rep_cla_inc_stats_eq : forall s M ci st,
  solver_scalars_rep s (msolver_with_cla_inc_stats M ci st)
  = solver_scalars_rep s M.
Proof. intros. reflexivity. Qed.

Lemma vecs_rep_cla_inc_stats_eq : forall s M ci st,
  solver_vecs_rep s (msolver_with_cla_inc_stats M ci st)
  = solver_vecs_rep s M.
Proof. intros. reflexivity. Qed.

Lemma fp_rep_cla_inc_stats_eq : forall s M st,
  solver_fp_rep s (msolver_with_cla_inc_stats M (ms_cla_inc M) st)
  = solver_fp_rep s M.
Proof. intros. reflexivity. Qed.

Lemma fp_rep_set_root_eq : forall s M r,
  solver_fp_rep s (msolver_set_root M r) = solver_fp_rep s M.
Proof. intros. reflexivity. Qed.

Lemma vecs_rep_set_root_eq : forall s M r,
  solver_vecs_rep s (msolver_set_root M r) = solver_vecs_rep s M.
Proof. intros. reflexivity. Qed.

Lemma join_scalars_set_root : forall s M r,
  &( s # "solver_t" ->ₛ "root_level") # Int |-> r **
  solver_scalars_without_root_rep s M
  |-- solver_scalars_rep s (msolver_set_root M r).
Proof.
  intros. unfold solver_scalars_rep, solver_scalars_without_root_rep,
    msolver_set_root, msolver_core_heap_update. cbn. msat_entailer_with lia.
Qed.

Lemma analyze_frame_join : forall s M wl,
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "var_inc") # Double |-> ms_var_inc M **
  &( s # "solver_t" ->ₛ "cla_inc") # Float |-> ms_cla_inc M **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
           (db_words (ms_learnt M)) **
  Veci.rep &( s # "solver_t" ->ₛ "tagged") (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack") (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "order") (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
           (mt_lim (ms_core M)) **
  &( s # "solver_t" ->ₛ "stats" .ₛ "max_literals")
    # UInt64 |-> stats_max_literals (ms_stats M) **
  &( s # "solver_t" ->ₛ "stats" .ₛ "tot_literals")
    # UInt64 |-> stats_tot_literals (ms_stats M) **
  solver_analyze_frame s M wl
  |-- solver_scalars_rep s M ** solver_fp_rep s M ** solver_vecs_rep s M **
      stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M) **
      &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
      (EX asg : Z,
         &( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
         &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
         CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
         solver_char_tail asg (ms_size M) (ms_cap M) **
         wlists_rep wl (ms_size M) (ms_wm M)).
Proof. msat_analyze_frame_bridge p wl asg. Qed.


Lemma propagation_normalized_conflict_scan_facts :
  forall (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (Mscan : msolver) (co : clause_obj)
         (scan_current p watch0 false_lit a0 a1 : Z) (tail : list Z),
  solver_propagation_weak n F A_arr K Mscan ->
  In (scan_current, co) (msolver_db Mscan) ->
  co_lits co = a0 :: a1 :: tail ->
  Forall (lit_wf_c n) (a0 :: a1 :: tail) ->
  Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 <> 0 ->
  Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 <> lit_sig watch0 ->
  propagation_replacement_scan_inv n Mscan false_lit
    (propagation_normalized_clause watch0 false_lit (a0 :: a1 :: tail))
    (Zlength (propagation_normalized_clause watch0 false_lit
       (a0 :: a1 :: tail))) ->
  false_lit = lit_neg_c p ->
  real_watch_pair p (a0 :: a1 :: tail) ->
  watch0 + false_lit =
    Znth 0 (a0 :: a1 :: tail) 0 + Znth 1 (a0 :: a1 :: tail) 0 ->
  sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail) = tail
  /\ Permutation (watch0 :: false_lit :: tail) (a0 :: a1 :: tail)
  /\ ((a0 = false_lit /\ watch0 = a1) \/ (a1 = false_lit /\ watch0 = a0))
  /\ lit_false (mt_assigns (ms_core Mscan)) watch0
  /\ Forall (lit_false (mt_assigns (ms_core Mscan)))
       (watch0 :: false_lit :: tail)
  /\ Forall (lit_false (mt_assigns (ms_core Mscan))) (a0 :: a1 :: tail)
  /\ Forall (fun l => eval_partial_literal (mt_pv (ms_core Mscan)) l =
       Some false) (denote_obj co)
  /\ (forall v, 0 <= v < n ->
       Znth v (ms_reason_words Mscan) 0 <> scan_current)
  /\ (forall l,
       Permutation (entry_watchers (scan_current, co) l)
         (entry_watchers
            (scan_current, clause_obj_with_lits co
               (watch0 :: false_lit :: tail)) l)).
Proof.
  intros n F A_arr K Mscan co scan_current p watch0 false_lit a0 a1 tail.
  intros Hweak Hin Hlits Hall Hassigned Hnotsig.
  intros Hscan_inv Hfalse_lit Hwatch_pair Hwatch_sum.
  assert (Hdbwf : db_wf n (msolver_db Mscan)).
  { unfold solver_propagation_weak in Hweak.
    destruct Hweak as [_ Hweak]. destruct K.
    - exact (msw_db_wf Hweak).
    - exact (msa_db_wf Hweak). }
  assert (Htrailwf_old : mtrail_wf n (ms_core Mscan)).
  { unfold solver_propagation_weak in Hweak.
    destruct Hweak as [_ Hweak]. destruct K;
      [exact (msw_trail_wf Hweak)|exact (msa_trail_wf Hweak)]. }
  assert (Hstable_old : stable_view (msolver_view n Mscan)).
  { unfold solver_propagation_weak in Hweak.
    destruct Hweak as [_ Hweak]. destruct K;
      [exact (msw_stable Hweak)|exact (msa_stable Hweak)]. }
  assert (Hreasons_old : reasons_match n (ms_core Mscan)
      (msolver_db Mscan) (ms_reason_words Mscan) (ms_reason_of Mscan)).
  { unfold solver_propagation_weak in Hweak.
    destruct Hweak as [_ Hweak]. destruct K;
      [exact (msw_reasons_mem Hweak)|exact (msa_reasons_mem Hweak)]. }
  assert (Htail : sublist 2 (Zlength (a0 :: a1 :: tail))
      (a0 :: a1 :: tail) = tail).
  { replace (a0 :: a1 :: tail) with ((a0 :: a1 :: nil) ++ tail)
      by reflexivity.
    assert (Hrange : 2 <= 2 <=
        Zlength ((a0 :: a1 :: nil) ++ tail)).
    { split; [lia|]. rewrite Zlength_app.
      change (2 <= 2 + Zlength tail).
      pose proof (Zlength_nonneg tail). lia. }
    rewrite (sublist_split_app_r 2
      (Zlength ((a0 :: a1 :: nil) ++ tail)) 2
      (a0 :: a1 :: nil) tail ltac:(reflexivity) Hrange).
    replace (Zlength ((a0 :: a1 :: nil) ++ tail) - 2)
      with (Zlength tail) by
      (rewrite Zlength_app, !Zlength_cons, Zlength_nil; lia).
    apply sublist_self. reflexivity. }
  assert (Hwatchcases :
      (a0 = false_lit /\ watch0 = a1) \/
      (a1 = false_lit /\ watch0 = a0)).
  { unfold real_watch_pair in Hwatch_pair.
    rewrite !Znth0_cons in Hwatch_pair, Hwatch_sum.
    rewrite !Znth_cons in Hwatch_pair, Hwatch_sum by lia.
    replace (1 - 1) with 0 in Hwatch_pair, Hwatch_sum by lia.
    rewrite !Znth0_cons in Hwatch_pair, Hwatch_sum.
    destruct Hwatch_pair as [Hw | Hw].
    - left. rewrite <- Hfalse_lit in Hw. split; [exact Hw|lia].
    - right. rewrite <- Hfalse_lit in Hw. split; [exact Hw|lia]. }
  assert (Hperm : Permutation
      (propagation_normalized_clause watch0 false_lit
        (a0 :: a1 :: tail)) (a0 :: a1 :: tail)).
  { unfold propagation_normalized_clause. rewrite Htail.
    destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    - subst a0 watch0. apply perm_swap.
    - subst a1 watch0. reflexivity. }
  unfold propagation_normalized_clause in Hperm. rewrite Htail in Hperm.
  assert (Hnew_eq : propagation_normalized_clause watch0 false_lit
      (a0 :: a1 :: tail) = watch0 :: false_lit :: tail).
  { unfold propagation_normalized_clause. rewrite Htail. reflexivity. }
  assert (Hwatch0_false :
      lit_false (mt_assigns (ms_core Mscan)) watch0).
  { assert (Hwatchwf : lit_wf_c n watch0).
    {
      rewrite Forall_forall in Hall.
      destruct Hwatchcases as [[_ Hw] | [_ Hw]]; rewrite Hw;
        apply Hall; simpl; auto. }
    pose proof (lit_var_c_in_range n watch0 Hwatchwf) as Hvr.
    pose proof (Forall_Znth_elim Z lbool_cell
      (mt_assigns (ms_core Mscan)) 0 (lit_var_c watch0)
      (mtw_cells Htrailwf_old) ltac:(rewrite (mtw_assigns_len
        Htrailwf_old); exact Hvr)) as Hcell.
    unfold lit_false. unfold lbool_cell in Hcell.
    destruct Hcell as [Hcell | [Hcell | Hcell]];
      destruct (lit_sig_values watch0) as [Hsig | Hsig];
      rewrite Hcell, Hsig in *; lia. }
  assert (Hnew_false : Forall (lit_false (mt_assigns (ms_core Mscan)))
      (watch0 :: false_lit :: tail)).
  { unfold propagation_replacement_scan_inv in Hscan_inv.
    destruct Hscan_inv as [Hkrange [Hnewwf [Hslot [Hfalse Hrestfalse]]]].
    rewrite Hnew_eq in Hkrange, Hnewwf, Hslot, Hrestfalse.
    constructor; [exact Hwatch0_false|].
    constructor; [exact Hfalse|].
    rewrite Forall_forall. intros x Hx.
    destruct (In_Znth_index tail x Hx) as [j [Hj Hval]].
    rewrite <- Hval.
    specialize (Hrestfalse (j + 2)).
    assert (Hjr : 2 <= j + 2 <
        Zlength (watch0 :: false_lit :: tail)).
    { rewrite !Zlength_cons. lia. }
    specialize (Hrestfalse Hjr).
    rewrite !Znth_cons in Hrestfalse by lia.
    replace (j + 2 - 1 - 1) with j in Hrestfalse by lia.
    exact Hrestfalse. }
  assert (Hold_false :
      Forall (lit_false (mt_assigns (ms_core Mscan)))
        (a0 :: a1 :: tail)).
  { eapply Forall_of_perm; [exact Hperm|exact Hnew_false]. }
  assert (Hden_false :
      Forall (fun l => eval_partial_literal (mt_pv (ms_core Mscan)) l =
        Some false) (denote_obj co)).
  { unfold denote_obj. rewrite Hlits.
    rewrite Forall_forall. intros l Hl.
    unfold lits_denote in Hl.
    apply in_map_iff in Hl as [x [<- Hx]].
    assert (Hx0 : 0 <= x).
    { rewrite Forall_forall in Hall. specialize (Hall x Hx).
      destruct Hall. lia. }
    rewrite Forall_forall in Hold_false.
    pose proof (proj1 (lit_false_iff (mt_assigns (ms_core Mscan)) x Hx0)
      (Hold_false x Hx)) as Heval.
    unfold eval_partial_literal in Heval |- *.
    rewrite lit_var_c_denote.
    rewrite mt_pv_nonneg by
      (apply lit_var_c_nonneg with (n := n);
       rewrite Forall_forall in Hall; exact (Hall x Hx)).
    unfold assigns_pv, assigns_val in Heval.
    rewrite lit_var_c_denote in Heval.
    exact Heval. }
  assert (Hno_reason_ptr : forall v, 0 <= v < n ->
      Znth v (ms_reason_words Mscan) 0 <> scan_current).
  { eapply no_live_reason_owner_false_clause__propagate_dbu;
      [ exact Hdbwf | exact Htrailwf_old | exact Hstable_old
      | exact Hreasons_old | exact Hin | exact Hden_false ]. }
  assert (Hentry_perm : forall l,
      Permutation (entry_watchers (scan_current, co) l)
        (entry_watchers (scan_current,
           clause_obj_with_lits co (watch0 :: false_lit :: tail)) l)).
  { intros l. destruct Hwatchcases as [[Ha0 Hw] | [Ha1 Hw]].
    - subst a0. subst watch0.
      unfold entry_watchers, co_watch0, co_watch1,
        clause_obj_with_lits. rewrite Hlits. cbn.
      apply Permutation_app_comm.
    - subst a1. subst watch0.
      unfold entry_watchers, co_watch0, co_watch1,
        clause_obj_with_lits. rewrite Hlits. cbn.
      reflexivity. }
  repeat split;
    [ exact Htail | exact Hperm | exact Hwatchcases | exact Hwatch0_false
    | exact Hnew_false | exact Hold_false | exact Hden_false
    | exact Hno_reason_ptr | exact Hentry_perm ].
Qed.


(** * Variable-count growth. *)


Lemma lit_wf_c_mono : forall n n' l,
  n <= n' -> lit_wf_c n l -> lit_wf_c n' l.
Proof. unfold lit_wf_c. intros. lia. Qed.

Lemma obj_wf_mono : forall n n' co,
  n <= n' -> obj_wf n co -> obj_wf n' co.
Proof.
  intros n n' co Hle [Hlen [Hall Hnd]].
  split; [exact Hlen | split; [| exact Hnd]].
  eapply Forall_impl; [| exact Hall].
  intros a Ha. eapply lit_wf_c_mono; eauto.
Qed.

Lemma db_wf_mono : forall n n' db,
  n <= n' -> db_wf n db -> db_wf n' db.
Proof.
  intros n n' db Hle [Hnd [Heven Hall]].
  split; [exact Hnd | split; [exact Heven |]].
  eapply Forall_impl; [| exact Hall].
  intros e He. eapply obj_wf_mono; eauto.
Qed.

Lemma literal_wf_mono : forall n n' l,
  n <= n' -> literal_wf n l -> literal_wf n' l.
Proof. unfold literal_wf, var_in_range. intros. lia. Qed.

Lemma cnf_wf_mono : forall n n' F,
  n <= n' -> cnf_wf n F -> cnf_wf n' F.
Proof.
  intros n n' F Hle [Hn Hall].
  split; [lia |].
  eapply Forall_impl; [| exact Hall].
  intros c Hc. eapply Forall_impl; [| exact Hc].
  intros l Hl. eapply literal_wf_mono; eauto.
Qed.


(* NOT monotone: mtrail_wf pins Zlength (mt_assigns t) = n        *)
(*     exactly, so raising n needs a real EXTENSION operation --      *)
(*     which is what solver_setnvars' realloc+initialise loop does.   *)


Definition mtrail_add_var (t : mtrail) : mtrail :=
  {| mt_assigns := mt_assigns t ++ (0 :: nil);
     mt_levels  := mt_levels t ++ (0 :: nil);
     mt_trail   := mt_trail t;
     mt_lim     := mt_lim t;
     mt_qhead   := mt_qhead t |}.

Lemma trail_var_lt : forall n t l,
  mtrail_wf n t -> In l (mt_trail t) -> 0 <= lit_var_c l < n.
Proof.
  intros n t l H Hin.
  apply (trail_var_range n t). exact H. apply in_map. exact Hin.
Qed.

Lemma new_var_not_on_trail : forall n t,
  mtrail_wf n t -> ~ In n (map lit_var_c (mt_trail t)).
Proof.
  intros n t H Hin.
  pose proof (trail_var_range n t n H Hin). lia.
Qed.

Lemma mtrail_wf_add_var : forall n t,
  mtrail_wf n t -> mtrail_wf (n + 1) (mtrail_add_var t).
Proof.
  intros n t H.
  pose proof (mtw_n_nonneg H)     as Hn.
  pose proof (mtw_assigns_len H)  as Hal.
  pose proof (mtw_levels_len H)   as Hll.
  pose proof (mtw_cells H)        as Hce.
  pose proof (mtw_qhead_range H)  as Hqh.
  pose proof (mtw_trail_bound H)  as Htb.
  pose proof (mtw_trail_lits H)   as Htl.
  pose proof (mtw_trail_nodup H)  as Hnd.
  pose proof (mtw_trail_true H)   as Htt.
  pose proof (mtw_lim_sorted H)   as Hls.
  pose proof (mtw_lim_range H)    as Hlr.
  pose proof (mtw_levels_agree H) as Hla.
  pose proof (mtw_assigned_iff H) as Hai.
  constructor; simpl.
  - lia.
  - rewrite Zlength_app, Hal. rewrite Zlength_cons, Zlength_nil. lia.
  - rewrite Zlength_app, Hll. rewrite Zlength_cons, Zlength_nil. lia.
  - apply Forall_app. split; [exact Hce |].
    constructor; [| constructor]. unfold lbool_cell. right; left; reflexivity.
  - exact Hqh.
  - lia.
  - eapply Forall_impl; [| exact Htl].
    intros a Ha. eapply lit_wf_c_mono; [| exact Ha]. lia.
  - exact Hnd.
  - rewrite Forall_forall. intros l Hin.
    rewrite Forall_forall in Htt. specialize (Htt l Hin).
    pose proof (trail_var_lt n t l H Hin) as Hv.
    rewrite app_Znth1 by lia. exact Htt.
  - exact Hls.
  - exact Hlr.
  - intros i Hi. unfold trail_var. simpl.
    assert (Hin : In (Znth i (mt_trail t) 0) (mt_trail t))
      by (apply Znth_In; lia).
    pose proof (trail_var_lt n t _ H Hin) as Hv.
    rewrite app_Znth1 by lia.
    apply Hla. exact Hi.
  - intros v Hv.
    destruct (Z_lt_dec v n) as [Hlt | Hge].
    + rewrite app_Znth1 by lia. apply Hai. lia.
    + assert (v = n) by lia. subst v.
      rewrite app_Znth2 by lia.
      rewrite Hal, Z.sub_diag, Znth0_cons.
      split; [intros Hc; exfalso; apply Hc; reflexivity |].
      intros Hc. exfalso. eapply new_var_not_on_trail; eauto.
Qed.


Definition heap_add_var (n : Z) (h : mheap) : mheap :=
  {| mh_heap    := mh_heap h ++ (n :: nil);
     mh_orderpos := mh_orderpos h ++ (Zlength (mh_heap h) :: nil) |}.

Lemma heap_wf_add_var : forall n h,
  0 <= n -> heap_wf n h -> heap_wf (n + 1) (heap_add_var n h).
Proof.
  intros n h Hn [Hlen [Hnd [Hbnd [Hpos Hinv]]]].
  pose proof (Zlength_nonneg (mh_heap h)) as Hhn.
  assert (Hnotin : ~ In n (mh_heap h)).
  { rewrite Forall_forall in Hbnd. intros Hc. specialize (Hbnd n Hc). lia. }
  unfold heap_add_var, heap_wf. cbn [mh_heap mh_orderpos]. repeat split.
  - rewrite Zlength_app, Hlen, Zlength_cons, Zlength_nil. lia.
  - apply NoDup_snoc; assumption.
  - apply Forall_app. split.
    + eapply Forall_impl; [| exact Hbnd].
      intros a Ha. cbv beta in Ha |- *. lia.
    + constructor; [lia | constructor].
  - (* orderpos entry is absent, or points at its own heap slot *)
    intros v Hv. rewrite Zlength_app, Zlength_cons, Zlength_nil.
    destruct (Z_lt_dec v n) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      destruct (Hpos v ltac:(lia)) as [Habs | [Hr Hh]].
      * left. exact Habs.
      * right. split; [lia |]. rewrite app_Znth1 by lia. exact Hh.
    + assert (v = n) by lia. subst v.
      rewrite app_Znth2 by lia. rewrite Hlen, Z.sub_diag, Znth0_cons.
      right. split; [lia |].
      rewrite app_Znth2 by lia. rewrite Z.sub_diag, Znth0_cons. reflexivity.
  - (* the heap/orderpos inverse, at every slot including the new one *)
    intros i Hi. rewrite Zlength_app, Zlength_cons, Zlength_nil in Hi.
    destruct (Z_lt_dec i (Zlength (mh_heap h))) as [Hlt | Hge].
    + (* resolve the INNER heap lookup first, or rewrite targets the outer one *)
      assert (Hin1 : Znth i (mh_heap h ++ (n :: nil)) (-1)
                     = Znth i (mh_heap h) (-1))
        by (apply app_Znth1; lia).
      rewrite Hin1.
      assert (Hin : In (Znth i (mh_heap h) (-1)) (mh_heap h))
        by (apply Znth_In; lia).
      rewrite Forall_forall in Hbnd. specialize (Hbnd _ Hin).
      rewrite app_Znth1 by lia. apply Hinv. lia.
    + assert (i = Zlength (mh_heap h)) by lia. subst i.
      assert (Hin2 : Znth (Zlength (mh_heap h)) (mh_heap h ++ (n :: nil)) (-1) = n).
      { rewrite app_Znth2 by lia. rewrite Z.sub_diag. apply Znth0_cons. }
      rewrite Hin2.
      rewrite app_Znth2 by lia. rewrite Hlen, Z.sub_diag, Znth0_cons.
      reflexivity.
Qed.


(* The solver_setnvars model layer.  *)


Lemma Znth_zero_singleton : forall i, Znth i (0 :: nil) 0 = 0.
Proof.
  intros i. unfold Znth. destruct (Z.to_nat i) as [|k]; [reflexivity |].
  destruct k; reflexivity.
Qed.

Lemma mt_pv_add_var : forall t, mt_pv (mtrail_add_var t) = mt_pv t.
Proof.
  intros t. apply functional_extensionality. intros v.
  unfold mt_pv, assigns_pv, assigns_val, mtrail_add_var.
  cbn [mt_assigns].
  destruct (0 <=? v)%Z eqn:Hv; [| reflexivity].
  apply Z.leb_le in Hv.
  destruct (Z_lt_dec v (Zlength (mt_assigns t))) as [Hlt | Hge].
  - rewrite app_Znth1 by lia. reflexivity.
  - rewrite app_Znth2 by lia. rewrite Znth_zero_singleton.
    rewrite (Znth_zero_past_end__order_select (mt_assigns t) v) by lia.
    reflexivity.
Qed.

Lemma trail_pos_add_var : forall t v,
  trail_pos (mtrail_add_var t) v = trail_pos t v.
Proof. reflexivity. Qed.

Lemma co_watch_wf : forall n co,
  obj_wf n co ->
  lit_wf_c n (co_watch0 co) /\ lit_wf_c n (co_watch1 co).
Proof.
  intros n co [Hlen [Hall _]].
  unfold co_watch0, co_watch1.
  rewrite Forall_forall in Hall.
  split; apply Hall; apply Znth_In; lia.
Qed.

Lemma entry_watchers_out_of_range : forall n e l,
  obj_wf n (snd e) -> 2 * n <= l -> entry_watchers e l = nil.
Proof.
  intros n [p co] l Hwf Hl. simpl in Hwf.
  destruct (co_watch_wf n co Hwf) as [Hw0 Hw1].
  apply lit_neg_c_wf in Hw0. apply lit_neg_c_wf in Hw1.
  unfold lit_wf_c in Hw0, Hw1.
  unfold entry_watchers.
  destruct (lit_neg_c (co_watch0 co) =? l)%Z eqn:E0.
  { apply Z.eqb_eq in E0. lia. }
  destruct (lit_neg_c (co_watch1 co) =? l)%Z eqn:E1.
  { apply Z.eqb_eq in E1. lia. }
  reflexivity.
Qed.

(* The two literals of a fresh variable watch nothing: no installed clause
   can mention them, because every clause is well-formed below the OLD
   variable count.  This is what makes the two fresh vecp_new buckets
   satisfy wmap_exact. *)

Lemma expected_watchers_out_of_range : forall n db l,
  db_wf n db -> 2 * n <= l -> expected_watchers db l = nil.
Proof.
  intros n db l [_ [_ Hall]] Hl.
  unfold expected_watchers.
  induction db as [| e db IH]; [reflexivity |].
  inversion Hall as [| e' db' He Hdb]; subst.
  simpl. rewrite (entry_watchers_out_of_range n e l He Hl). simpl.
  apply IH. exact Hdb.
Qed.


Definition msolver_add_var (M : msolver) (a0 : fp64) : msolver := {|
  ms_size           := ms_size M + 1;
  ms_cap            := ms_cap M;
  ms_qtail          := ms_qtail M;
  ms_capacity_pending_qhead := ms_capacity_pending_qhead M;
  ms_capacity_root_propagation_pending :=
    ms_capacity_root_propagation_pending M;
  ms_core           := mtrail_add_var (ms_core M);
  ms_root_level     := ms_root_level M;
  ms_reason_words   := ms_reason_words M ++ (0 :: nil);
  ms_reason_of      := fun x => if Z.eqb x (ms_size M)
                                then None else ms_reason_of M x;
  ms_prob           := ms_prob M;
  ms_learnt         := ms_learnt M;
  ms_binary         := ms_binary M;
  ms_binary_lits    := ms_binary_lits M;
  ms_wm             := ms_wm M ++ (nil :: nil :: nil);
  ms_activity       := ms_activity M ++ (a0 :: nil);
  ms_orderpos       := ms_orderpos M ++ (Zlength (ms_order M) :: nil);
  ms_order          := ms_order M ++ (ms_size M :: nil);
  ms_model          := ms_model M;
  ms_tags           := ms_tags M ++ (0 :: nil);
  ms_tagged         := ms_tagged M;
  ms_stack          := ms_stack M;
  ms_var_inc        := ms_var_inc M;
  ms_var_decay      := ms_var_decay M;
  ms_cla_inc        := ms_cla_inc M;
  ms_cla_decay      := ms_cla_decay M;
  ms_random_seed    := ms_random_seed M;
  ms_progress       := ms_progress M;
  ms_simpdb_assigns := ms_simpdb_assigns M;
  ms_simpdb_props   := ms_simpdb_props M;
  ms_verbosity      := ms_verbosity M;
  ms_stats          := ms_stats M
|}.

(* ---- projections: what the operation does to each derived structure ---- *)

Lemma msolver_add_var_core : forall M a0,
  ms_core (msolver_add_var M a0) = mtrail_add_var (ms_core M).
Proof. reflexivity. Qed.

Lemma msolver_add_var_heap : forall M a0,
  msolver_heap (msolver_add_var M a0) = heap_add_var (ms_size M) (msolver_heap M).
Proof. reflexivity. Qed.

Lemma msolver_add_var_db : forall M a0,
  msolver_db (msolver_add_var M a0) = msolver_db M.
Proof. reflexivity. Qed.

Lemma msolver_add_var_clauses : forall M a0,
  msolver_clauses (msolver_add_var M a0) = msolver_clauses M.
Proof. reflexivity. Qed.

Lemma msolver_add_var_size : forall M a0,
  ms_size (msolver_add_var M a0) = ms_size M + 1.
Proof. reflexivity. Qed.


Lemma msolver_view_add_var : forall n n' M a0,
  mtrail_wf (ms_size M) (ms_core M) ->
  msolver_view n (msolver_add_var M a0) = msolver_view n' M.
Proof.
  intros n n' M a0 Hwf.
  unfold msolver_view. rewrite msolver_add_var_core, msolver_add_var_clauses.
  cbn [ms_reason_of msolver_add_var].
  unfold view_of. f_equal.
  - apply mt_pv_add_var.
  - apply functional_extensionality. intros x.
    rewrite trail_pos_add_var.
    destruct (trail_pos (ms_core M) x) eqn:Ex; [| reflexivity].
    destruct (Z.eqb x (ms_size M)) eqn:Ev; [| reflexivity].
    apply Z.eqb_eq in Ev. subst x.
    exfalso.
    assert (Hnone : trail_pos (ms_core M) (ms_size M) = None).
    { apply trail_pos_none_iff.
      apply (new_var_not_on_trail (ms_size M) (ms_core M) Hwf). }
    rewrite Ex in Hnone. discriminate.
Qed.

(* ---- solver_shape: the eight length fields the C reallocs ------------- *)

(** [ms_cap] is untouched, so growth needs capacity already in hand -- which
    is exactly what the capacity loop and its eight reallocs establish before
    the per-variable loop runs.  The [2*(size+1) <= INT_MAX] side condition
    cannot be derived from [ms_cap <= INT_MAX] and must be supplied; in the C
    it follows from the caller's [maxvar+1] bound. *)

Lemma solver_shape_add_var : forall M a0,
  solver_shape M ->
  ms_size M < ms_cap M ->
  2 * (ms_size M + 1) <= INT_MAX ->
  solver_shape (msolver_add_var M a0).
Proof.
  intros M a0 Hsh Hcap Hint.
  unfold solver_shape in *.
  cbn [ms_size ms_cap ms_qtail ms_capacity_pending_qhead
       ms_capacity_root_propagation_pending ms_core ms_root_level
       ms_reason_words ms_orderpos ms_activity ms_tags ms_wm
       ms_binary ms_binary_lits ms_stats msolver_add_var] in *.
  cbn [mt_assigns mt_levels mt_trail mt_qhead mt_lim mtrail_add_var] in *.
  rewrite !Zlength_app.
  change (Zlength (0 :: nil)) with 1.
  change (Zlength (a0 :: nil)) with 1.
  change (Zlength (Zlength (ms_order M) :: nil)) with 1.
  change (Zlength (@nil Z :: @nil Z :: nil)) with 2.
  change (Zlength (4 :: 4 :: nil)) with 2.
  repeat split; try tauto; try lia.
Qed.

(* ---- facts that read only the trail and the level boundaries ---------- *)

Lemma decisions_upto_add_var : forall t d,
  decisions_upto (mtrail_add_var t) d = decisions_upto t d.
Proof. reflexivity. Qed.

Lemma trail_implied_add_var : forall F t,
  trail_implied F t -> trail_implied F (mtrail_add_var t).
Proof. intros F t H. exact H. Qed.

(* ---- the analysis scratch --------------------------------------------- *)

Lemma solver_tags_clear_add_var : forall M a0,
  solver_tags_clear M -> solver_tags_clear (msolver_add_var M a0).
Proof.
  intros M a0 [Htags Htagged]. unfold solver_tags_clear.
  cbn [ms_tags ms_tagged msolver_add_var]. split; [| exact Htagged].
  rewrite Forall_app. split; [exact Htags |].
  constructor; constructor.
Qed.

(* ---- the watcher table ------------------------------------------------- *)

Lemma wmap_exact_add_var : forall n db wm,
  0 <= n ->
  db_wf n db ->
  wmap_exact n db wm ->
  wmap_exact (n + 1) db (wm ++ (nil :: nil :: nil)).
Proof.
  intros n db wm Hn Hdb [Hlen Hperm].
  unfold wmap_exact. split.
  - rewrite Zlength_app. change (Zlength (@nil Z :: @nil Z :: nil)) with 2. lia.
  - intros l Hl.
    destruct (Z_lt_dec l (2 * n)) as [Hlt | Hge].
    + rewrite app_Znth1 by lia. apply Hperm. lia.
    + rewrite app_Znth2 by lia.
      rewrite (expected_watchers_out_of_range n db l Hdb) by lia.
      assert (Hcase : l - Zlength wm = 0 \/ l - Zlength wm = 1) by lia.
      destruct Hcase as [E | E]; rewrite E; apply Permutation_refl.
Qed.

(* ---- level-indexed facts: unchanged below the old count --------------- *)

Lemma assump_true_at_root_add_var : forall n t root a,
  Zlength (mt_levels t) = n ->
  literal_wf n a ->
  assump_true_at_root t root a ->
  assump_true_at_root (mtrail_add_var t) root a.
Proof.
  intros n t root a Hlen Hwf [Hev Hlev].
  unfold assump_true_at_root in *.
  rewrite mt_pv_add_var.
  split; [exact Hev |].
  cbn [mt_levels mtrail_add_var].
  rewrite app_Znth1 by (unfold literal_wf, var_in_range in Hwf; lia).
  exact Hlev.
Qed.

Lemma root_satisfied_add_var : forall n t c,
  Zlength (mt_levels t) = n ->
  Forall (literal_wf n) c ->
  root_satisfied t c ->
  root_satisfied (mtrail_add_var t) c.
Proof.
  intros n t c Hlen Hwf [l [Hin [Hev Hlev]]].
  unfold root_satisfied. exists l.
  rewrite mt_pv_add_var.
  split; [exact Hin |]. split; [exact Hev |].
  cbn [mt_levels mtrail_add_var].
  rewrite Forall_forall in Hwf. specialize (Hwf l Hin).
  rewrite app_Znth1 by (unfold literal_wf, var_in_range in Hwf; lia).
  exact Hlev.
Qed.

(* ---- reasons ----------------------------------------------------------- *)

Lemma reason_word_ok_add_var : forall t v db w r,
  0 <= v < Zlength (mt_assigns t) ->
  reason_word_ok t v db w r ->
  reason_word_ok (mtrail_add_var t) v db w r.
Proof.
  intros t v db w r Hv H.
  unfold reason_word_ok, trail_lit_of in *.
  cbn [mt_assigns mtrail_add_var].
  assert (Heq : Znth v (mt_assigns t ++ (0 :: nil)) 0 = Znth v (mt_assigns t) 0)
    by (apply app_Znth1; lia).
  rewrite Heq. exact H.
Qed.

(** Below the old count nothing moved; AT the new variable the reason word is
    the appended 0 and the ghost reason is [None], which is exactly what
    [reason_word_ok] demands of a null word. *)

Lemma reasons_match_add_var : forall n t db words r,
  Zlength words = n ->
  Zlength (mt_assigns t) = n ->
  reasons_match n t db words r ->
  reasons_match (n + 1) (mtrail_add_var t) db (words ++ (0 :: nil))
                (fun x => if Z.eqb x n then None else r x).
Proof.
  intros n t db words r Hw Ha H v Hv.
  destruct (Z.eq_dec v n) as [-> | Hne].
  - rewrite app_Znth2 by lia. rewrite Znth_zero_singleton.
    rewrite Z.eqb_refl. unfold reason_word_ok. cbn. reflexivity.
  - rewrite app_Znth1 by lia.
    assert (Hb : (v =? n)%Z = false) by (apply Z.eqb_neq; exact Hne).
    rewrite Hb.
    apply reason_word_ok_add_var; [lia |].
    apply H. lia.
Qed.

Lemma reason_head_ok_add_var : forall M a0,
  Zlength (ms_reason_words M) = ms_size M ->
  reason_head_ok M -> reason_head_ok (msolver_add_var M a0).
Proof.
  intros M a0 Hlen H v co Hv Htag Hnz Hin.
  cbn [ms_size ms_reason_words msolver_add_var] in Hv, Htag, Hnz, Hin |- *.
  destruct (Z.eq_dec v (ms_size M)) as [-> | Hne].
  - rewrite app_Znth2 in Hnz by lia. rewrite Znth_zero_singleton in Hnz.
    exfalso. apply Hnz. reflexivity.
  - rewrite app_Znth1 in Htag, Hnz, Hin by lia.
    apply (H v co); [lia | exact Htag | exact Hnz | exact Hin].
Qed.

Lemma binary_reason_same_level_add_var : forall M a0,
  Zlength (ms_reason_words M) = ms_size M ->
  Zlength (mt_levels (ms_core M)) = ms_size M ->
  binary_reason_same_level M ->
  binary_reason_same_level (msolver_add_var M a0).
Proof.
  intros M a0 Hw Hl H v Hv Htag.
  cbn [ms_size ms_reason_words ms_core msolver_add_var] in Hv, Htag |- *.
  destruct (Z.eq_dec v (ms_size M)) as [-> | Hne].
  - rewrite app_Znth2 in Htag by lia. rewrite Znth_zero_singleton in Htag.
    unfold is_tag in Htag. cbn in Htag. discriminate.
  - rewrite app_Znth1 in Htag |- * by lia.
    destruct (H v ltac:(lia) Htag) as (Hwf & Hlev & Hne2).
    split; [| split].
    + apply (lit_wf_c_mono (ms_size M)); [lia | exact Hwf].
    + cbn [mt_levels mtrail_add_var].
      pose proof (lit_var_c_in_range _ _ Hwf) as Hr.
      rewrite app_Znth1 by lia.
      rewrite app_Znth1 by lia.
      exact Hlev.
    + exact Hne2.
Qed.


Theorem msolver_inv_weak_add_var : forall n F A_arr A_inst M a0,
  msolver_inv_weak n F A_arr A_inst M ->
  ms_size M < ms_cap M ->
  2 * (n + 1) <= INT_MAX ->
  msolver_inv_weak (n + 1) F A_arr A_inst (msolver_add_var M a0).
Proof.
  intros n F A_arr A_inst M a0 HI Hcap Hint.
  pose proof (msw_size HI) as Hsize. subst n.
  pose proof (msw_n_range HI) as Hn.
  pose proof (msw_shape HI) as Hsh.
  pose proof (msw_trail_wf HI) as Htw.
  pose proof (msw_F_wf HI) as HF.
  pose proof (msw_db_wf HI) as Hdb.
  assert (Hal : Zlength (mt_assigns (ms_core M)) = ms_size M)
    by exact (mtw_assigns_len Htw).
  assert (Hll : Zlength (mt_levels (ms_core M)) = ms_size M)
    by exact (mtw_levels_len Htw).
  assert (Hrw : Zlength (ms_reason_words M) = ms_size M)
    by (unfold solver_shape in Hsh; tauto).
  constructor.
  - (* msw_size *) reflexivity.
  - (* msw_n_range *) lia.
  - (* msw_shape *) apply solver_shape_add_var; assumption.
  - (* msw_F_wf *) apply (cnf_wf_mono (ms_size M)); [lia | exact HF].
  - (* msw_A_wf *)
    pose proof (msw_A_wf HI) as HA. rewrite Forall_forall in HA |- *.
    intros a Hin. apply (literal_wf_mono (ms_size M)); [lia | apply HA; exact Hin].
  - (* msw_trail_wf *) apply mtrail_wf_add_var. exact Htw.
  - (* msw_level_bound *) pose proof (msw_level_bound HI). cbn. lia.
  - (* msw_root_range *) exact (msw_root_range HI).
  - (* msw_assumptions *)
    rewrite msolver_add_var_core, decisions_upto_add_var.
    exact (msw_assumptions HI).
  - (* msw_assump_incl *) exact (msw_assump_incl HI).
  - (* msw_assump_sat *)
    pose proof (msw_A_wf HI) as HA. pose proof (msw_assump_sat HI) as HS.
    rewrite Forall_forall in HA, HS |- *. intros a Hin.
    rewrite msolver_add_var_core.
    apply (assump_true_at_root_add_var (ms_size M));
      [exact Hll | apply HA; exact Hin | apply HS; exact Hin].
  - (* msw_stable *)
    rewrite (msolver_view_add_var (ms_size M + 1) (ms_size M) M a0 Htw).
    exact (msw_stable HI).
  - (* msw_reasons_ent *)
    rewrite (msolver_view_add_var (ms_size M + 1) (ms_size M) M a0 Htw).
    exact (msw_reasons_ent HI).
  - (* msw_reasons_inj *)
    rewrite (msolver_view_add_var (ms_size M + 1) (ms_size M) M a0 Htw).
    exact (msw_reasons_inj HI).
  - (* msw_trail_impl *)
    rewrite msolver_add_var_core.
    apply trail_implied_add_var. exact (msw_trail_impl HI).
  - (* msw_db_wf *)
    rewrite msolver_add_var_db.
    apply (db_wf_mono (ms_size M)); [lia | exact Hdb].
  - (* msw_db_matches *) exact (msw_db_matches HI).
  - (* msw_db_implied *) exact (msw_db_implied HI).
  - (* msw_db_complete *)
    pose proof (msw_db_complete HI) as HC. intros c HcF.
    destruct (HC c HcF) as [Hleft | Hright]; [left; exact Hleft |].
    right. rewrite msolver_add_var_core.
    apply (root_satisfied_add_var (ms_size M)); [exact Hll | | exact Hright].
    destruct HF as [_ HFf]. rewrite Forall_forall in HFf. apply HFf. exact HcF.
  - (* msw_learnt_db *) exact (msw_learnt_db HI).
  - (* msw_prob_db *) exact (msw_prob_db HI).
  - (* msw_binary_out *) exact (msw_binary_out HI).
  - (* msw_reasons_mem *)
    rewrite msolver_add_var_core, msolver_add_var_db.
    apply (reasons_match_add_var (ms_size M)); [exact Hrw | exact Hal |].
    exact (msw_reasons_mem HI).
  - (* msw_reason_head *) apply reason_head_ok_add_var;
      [exact Hrw | exact (msw_reason_head HI)].
  - (* msw_reason_bin *) apply binary_reason_same_level_add_var;
      [exact Hrw | exact Hll | exact (msw_reason_bin HI)].
  - (* msw_wmap_exact *)
    rewrite msolver_add_var_db.
    apply wmap_exact_add_var; [lia | exact Hdb | exact (msw_wmap_exact HI)].
  - (* msw_tags_clear *) apply solver_tags_clear_add_var.
    exact (msw_tags_clear HI).
  - (* msw_heap_wf *)
    rewrite msolver_add_var_heap.
    apply heap_wf_add_var; [lia | exact (msw_heap_wf HI)].
  - (* msw_cla_inc_nonnegative *) exact (msw_cla_inc_nonnegative HI).
  - (* msw_seed *) exact (msw_seed HI).
Qed.


(*  The four fields the STRONG bundle adds over the weak one.            *)

Lemma prop_level_add_var : forall t,
  prop_level t -> prop_level (mtrail_add_var t).
Proof. intros t H. exact H. Qed.

(** A processed literal sits on the trail below [qhead], and every trail
    literal is [lit_wf_c n] -- so the fresh variable can never be processed
    and the processed set does not grow with the count.  Only this direction
    is needed: [watch_frontier] is a NEGATED conjunction, so shrinking the
    set it is stated over preserves it. *)

Lemma minisat_processed_add_var : forall n t l,
  mtrail_wf n t ->
  minisat_processed (n + 1) (mt_assigns t ++ (0 :: nil))
                    (mt_trail t) (mt_qhead t) l ->
  minisat_processed n (mt_assigns t) (mt_trail t) (mt_qhead t) l.
Proof.
  intros n t l Hwf [packed [Hwfp [Hden [Htrue [i [Hi Hidx]]]]]].
  assert (Hin : In packed (mt_trail t)).
  { rewrite <- Hidx. apply Znth_In.
    pose proof (mtw_qhead_range Hwf). lia. }
  pose proof (proj1 (Forall_forall _ _) (mtw_trail_lits Hwf) _ Hin) as Hn.
  pose proof (lit_var_c_in_range n packed Hn) as Hvr.
  exists packed. split; [exact Hn | split; [exact Hden | split]].
  - unfold lit_true in *. rewrite app_Znth1 in Htrue;
      [exact Htrue | rewrite (mtw_assigns_len Hwf); lia].
  - exists i. split; [exact Hi | exact Hidx].
Qed.

Lemma minisat_watch_frontier_add_var : forall n db t,
  mtrail_wf n t ->
  minisat_watch_frontier n db (mt_assigns t) (mt_trail t) (mt_qhead t) ->
  minisat_watch_frontier (n + 1) db (mt_assigns t ++ (0 :: nil))
                         (mt_trail t) (mt_qhead t).
Proof.
  intros n db t Hwf H.
  unfold minisat_watch_frontier, watch_frontier in *.
  eapply Forall_impl; [| exact H].
  intros o Ho [H1 H2]. apply Ho.
  split; eapply minisat_processed_add_var; eauto.
Qed.

(** The fresh variable IS pushed into the heap, so its [orderpos] entry is a
    real index and the "not in the heap" hypothesis is false there.  Below the
    old count both lists are read through [app_Znth1]. *)

Lemma heap_covers_add_var : forall n h assigns trail qhead,
  Zlength (mh_orderpos h) = n ->
  Zlength assigns = n ->
  heap_covers n h assigns trail qhead ->
  heap_covers (n + 1) (heap_add_var n h) (assigns ++ (0 :: nil)) trail qhead.
Proof.
  intros n h assigns trail qhead Hlo Hla H v Hv Hpos.
  cbn [mh_orderpos heap_add_var] in Hpos.
  destruct (Z.eq_dec v n) as [-> | Hne].
  - exfalso. rewrite app_Znth2 in Hpos by lia.
    rewrite Hlo, Z.sub_diag in Hpos.
    rewrite Znth0_cons in Hpos.
    pose proof (Zlength_nonneg (mh_heap h)). lia.
  - rewrite app_Znth1 in Hpos by lia.
    rewrite app_Znth1 by lia.
    apply H; [lia | exact Hpos].
Qed.

(** [level_of] is [option_map _ (trail_pos ...)], so [Some d] means the
    variable is ON THE TRAIL -- which bounds it below the OLD count.  The view
    itself is unchanged, so both the hypothesis and the rank conclusion are
    literally the old ones. *)

Lemma current_reasonless_earliest_add_var : forall n M a0,
  mtrail_wf (ms_size M) (ms_core M) ->
  Zlength (ms_reason_words M) = ms_size M ->
  current_reasonless_earliest n M ->
  current_reasonless_earliest (n + 1) (msolver_add_var M a0).
Proof.
  intros n M a0 Hwf Hrw H d Hd v Hlev Hword.
  cbn [ms_root_level ms_core ms_reason_words ms_reason_of
       msolver_add_var] in Hd, Hlev, Hword |- *.
  cbn [mt_lim mtrail_add_var] in Hd |- *.
  rewrite (msolver_view_add_var (n + 1) n M a0 Hwf) in Hlev |- *.
  assert (Hk : exists k, trail_pos (ms_core M) v = Some k).
  { unfold msolver_view, view_of in Hlev. cbn in Hlev.
    destruct (trail_pos (ms_core M) v) as [k |] eqn:E;
      [exists k; reflexivity | discriminate Hlev]. }
  destruct Hk as [k Hk].
  pose proof (trail_pos_some_var_range__search
                _ _ _ _ Hwf Hk) as Hvr.
  rewrite app_Znth1 in Hword by lia.
  destruct (H d Hd v Hlev Hword) as [Hr Hrank].
  split; [| exact Hrank].
  replace (v =? ms_size M)%Z with false
    by (symmetry; apply Z.eqb_neq; lia).
  exact Hr.
Qed.


Theorem msolver_inv_add_var : forall n F A_arr A_inst M a0,
  msolver_inv n F A_arr A_inst M ->
  ms_size M < ms_cap M ->
  2 * (n + 1) <= INT_MAX ->
  msolver_inv (n + 1) F A_arr A_inst (msolver_add_var M a0).
Proof.
  intros n F A_arr A_inst M a0 HI Hcap Hint.
  pose proof (msi_size HI) as Hsize. subst n.
  pose proof (msi_trail_wf HI) as Htw.
  pose proof (msi_shape HI) as Hsh.
  assert (Hop : Zlength (ms_orderpos M) = ms_size M)
    by (unfold solver_shape in Hsh; tauto).
  assert (Hal : Zlength (mt_assigns (ms_core M)) = ms_size M)
    by exact (mtw_assigns_len Htw).
  assert (Hrw : Zlength (ms_reason_words M) = ms_size M)
    by (unfold solver_shape in Hsh; tauto).
  constructor.
  - exact (msolver_inv_weak_add_var _ _ _ _ _ a0
             (msi_weak HI) Hcap Hint).
  - cbn [ms_core msolver_add_var].
    exact (prop_level_add_var _ (msi_prop_level HI)).
  - rewrite msolver_add_var_db.
    cbn [ms_core msolver_add_var].
    cbn [mt_assigns mt_trail mt_qhead mtrail_add_var].
    exact (minisat_watch_frontier_add_var _ _ _ Htw (msi_watch_frontier HI)).
  - rewrite msolver_add_var_heap.
    cbn [ms_core msolver_add_var].
    cbn [mt_assigns mt_trail mt_qhead mtrail_add_var].
    apply heap_covers_add_var;
      [ cbn [mh_orderpos msolver_heap]; exact Hop
      | exact Hal
      | exact (msi_heap_covers HI) ].
  - exact (current_reasonless_earliest_add_var _ _ a0 Htw Hrw
             (msi_reasonless_current HI)).
Qed.


(*  The [order_update] sift, composed on top of the push.                *)

(*  The C ends each iteration with                                       *)
(*      veci_push(&s->order,var);                <- [msolver_add_var]     *)
(*      order_update(s, var);                    <- the sift, HERE        *)


Lemma heap_covers_membership_transport :
  forall n h1 h2 assigns trail qhead,
  (forall u, 0 <= u < n ->
     (Znth u (mh_orderpos h1) (-1) = -1 <-> Znth u (mh_orderpos h2) (-1) = -1)) ->
  heap_covers n h1 assigns trail qhead ->
  heap_covers n h2 assigns trail qhead.
Proof.
  intros n h1 h2 assigns trail qhead Hiff H v Hv Hpos.
  apply H; [exact Hv | exact (proj2 (Hiff v Hv) Hpos)].
Qed.

Lemma msolver_inv_heap_project :
  forall n F A_arr A_inst M orderpos order,
  msolver_inv n F A_arr A_inst M ->
  heap_wf (ms_size M) (heap_of_lists order orderpos) ->
  heap_covers (ms_size M) (heap_of_lists order orderpos)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
  msolver_inv n F A_arr A_inst
    (msolver_heap_project M orderpos order).
Proof.
  intros n F A_arr A_inst M orderpos order HI Hwf Hcovers.
  pose proof (msi_size HI) as Hsize.
  assert (Hwf_n : heap_wf n (heap_of_lists order orderpos))
    by (rewrite Hsize; exact Hwf).
  assert (Hcovers_n : heap_covers n (heap_of_lists order orderpos)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M)) (mt_qhead (ms_core M)))
    by (rewrite Hsize; exact Hcovers).
  assert (Hshape1 : solver_shape
    (msolver_heap_project M orderpos order)).
  { apply solver_shape_heap_project__canceluntil_cap.
    - exact (msi_shape HI).
    - exact (heap_wf_orderpos_length (ms_size M)
               (heap_of_lists order orderpos) Hwf). }
  pose proof (msi_weak HI) as Hweak.
  assert (Hweak1 : msolver_inv_weak n F A_arr A_inst
    (msolver_heap_project M orderpos order)).
  { destruct Hweak.
    constructor;
      unfold msolver_heap_project, msolver_core_heap_update in *;
      simpl in *; try assumption. }
  constructor.
  - exact Hweak1.
  - unfold msolver_heap_project, msolver_core_heap_update. simpl.
    exact (msi_prop_level HI).
  - unfold msolver_heap_project, msolver_core_heap_update. simpl.
    exact (msi_watch_frontier HI).
  - unfold msolver_heap_project, msolver_core_heap_update. simpl.
    exact Hcovers_n.
  - unfold msolver_heap_project, msolver_core_heap_update. simpl.
    exact (msi_reasonless_current HI).
Qed.


Theorem msolver_inv_add_var_sift :
  forall n F A_arr A_inst M a0 order1 orderpos1,
  msolver_inv n F A_arr A_inst M ->
  ms_size M < ms_cap M ->
  2 * (n + 1) <= INT_MAX ->
  order_update_post (n + 1) (ms_size M)
    (ms_order M ++ (ms_size M :: nil))
    (ms_orderpos M ++ (Zlength (ms_order M) :: nil))
    order1 orderpos1 ->
  msolver_inv (n + 1) F A_arr A_inst
    (msolver_heap_project (msolver_add_var M a0)
                          orderpos1 order1).
Proof.
  intros n F A_arr A_inst M a0 order1 orderpos1 HI Hcap Hint Hupd.
  pose proof (msi_size HI) as Hsize.
  pose proof (msolver_inv_add_var _ _ _ _ _ a0 HI Hcap Hint) as HI1.
  destruct Hupd as (Hpre & Hwf1 & Hperm & Hsame).
  apply msolver_inv_heap_project.
  - exact HI1.
  - rewrite msolver_add_var_size, <- Hsize. exact Hwf1.
  - rewrite msolver_add_var_size, <- Hsize.
    apply (heap_covers_membership_transport _
             (heap_of_lists (ms_order M ++ (ms_size M :: nil))
                            (ms_orderpos M ++ (Zlength (ms_order M) :: nil)))).
    + cbn [mh_orderpos heap_of_lists]. exact Hsame.
    + pose proof (msi_heap_covers HI1) as Hc.
      rewrite msolver_add_var_heap in Hc.
      cbn [ms_core msolver_add_var] in Hc |- *.
      exact Hc.
Qed.

Definition msolver_set_cap (M : msolver) (c : Z) : msolver :=
  msolver_propagation_update M (c) (ms_qtail M) (ms_capacity_root_propagation_pending M) (ms_core M)
    (ms_reason_words M) (ms_reason_of M) (ms_prob M) (ms_learnt M) (ms_binary_lits M) (ms_wm M)
    (ms_simpdb_props M) (ms_stats M).

Lemma msolver_set_cap_size : forall M c, ms_size (msolver_set_cap M c) = ms_size M.
Proof. reflexivity. Qed.

Lemma msolver_set_cap_cap : forall M c, ms_cap (msolver_set_cap M c) = c.
Proof. reflexivity. Qed.

Lemma msolver_set_cap_core : forall M c, ms_core (msolver_set_cap M c) = ms_core M.
Proof. reflexivity. Qed.

Lemma solver_shape_set_cap : forall M c,
  solver_shape M -> ms_cap M <= c -> c <= INT_MAX ->
  solver_shape (msolver_set_cap M c).
Proof.
  intros M c Hsh Hle Hmax.
  unfold solver_shape, msolver_set_cap, msolver_propagation_update in *; cbn in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; try assumption; try lia.
Qed.

Theorem msolver_inv_set_cap : forall n F A_arr A_inst M c,
  msolver_inv n F A_arr A_inst M ->
  ms_cap M <= c -> c <= INT_MAX ->
  msolver_inv n F A_arr A_inst (msolver_set_cap M c).
Proof.
  intros n F A_arr A_inst M c HI Hle Hmax.
  destruct HI as [Hw Hpl Hwf Hhc Hrc].
  constructor; [ | exact Hpl | exact Hwf | exact Hhc | exact Hrc ].
  destruct Hw. constructor; try assumption.
  apply solver_shape_set_cap; assumption.
Qed.


Lemma wlists_rep_add_var : forall base n wm,
  0 <= n ->
  wlists_rep base n wm **
  Vecp.rep (Vecp.slot base (2 * n)) nil **
  Vecp.rep (Vecp.slot base (2 * n + 1)) nil
  |-- wlists_rep base (n + 1) (wm ++ (nil :: nil :: nil)).
Proof.
  intros base n wm Hn. unfold wlists_rep. Intros_p Hwm.
  assert (Hwm' : Zlength (wm ++ (nil :: nil :: nil)) = 2 * (n + 1))
    by (rewrite Zlength_app, !Zlength_cons, Zlength_nil; lia).
  sep_apply (VecpArray.seg_single base (2 * n) nil).
  sep_apply (VecpArray.seg_single base (2 * n + 1) nil).
  sep_apply (VecpArray.full_to_seg base (2 * n) wm).
  replace (2 * n + 1 + 1) with (2 * (n + 1)) by lia.
  sep_apply (VecpArray.seg_merge_to_seg base (2 * n) (2 * n + 1) (2 * (n + 1))
    (nil :: nil) (nil :: nil) ltac:(lia)).
  sep_apply (VecpArray.seg_merge_to_seg base 0 (2 * n) (2 * (n + 1)) wm
    ((nil :: nil) ++ (nil :: nil)) ltac:(lia)).
  sep_apply (VecpArray.seg_to_full base (2 * (n + 1)) (wm ++ (nil :: nil) ++ (nil :: nil))).
  msat_entailer_with lia.
Qed.


(* The growth-path representation.                                      *)


(** Variable growth also owns the unbuilt watcher-table tail. One
    existential binds [wl] across [solver_rep_at] and [solver_wlists_tail], retaining
    their shared base address when the live representation is folded. *)

Definition solver_rep_growable (s : Z) (M : msolver) : Assertion :=
  EX wl act asg opos rsn lvl trl tgs : Z,
    solver_rep_at s M wl act asg opos rsn lvl trl tgs **
    solver_wlists_tail wl (2 * ms_size M) (2 * ms_cap M).


(* Opening the growth bundle.                                           *)


Definition setnvars_frame_at (s : Z) (M : msolver) : Assertion :=
  (&( s # "solver_t" ->ₛ "qhead")          # Int |-> mt_qhead (ms_core M) **
   &( s # "solver_t" ->ₛ "root_level")     # Int |-> ms_root_level M **
   &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |-> ms_simpdb_assigns M **
   &( s # "solver_t" ->ₛ "simpdb_props")   # Int |-> ms_simpdb_props M **
   &( s # "solver_t" ->ₛ "verbosity")      # Int |-> ms_verbosity M) **
  (&( s # "solver_t" ->ₛ "var_inc")           # Double |-> ms_var_inc M **
   &( s # "solver_t" ->ₛ "var_decay")         # Double |-> ms_var_decay M **
   &( s # "solver_t" ->ₛ "cla_inc")           # Float  |-> ms_cla_inc M **
   &( s # "solver_t" ->ₛ "cla_decay")         # Float  |-> ms_cla_decay M **
   &( s # "solver_t" ->ₛ "random_seed")       # Double |-> ms_random_seed M **
   &( s # "solver_t" ->ₛ "progress_estimate") # Double |-> ms_progress M) **
  (Vecp.rep &( s # "solver_t" ->ₛ "clauses")
            (map fst (ms_prob M)) **
   Vecp.rep &( s # "solver_t" ->ₛ "learnts")
            (map fst (ms_learnt M)) **
   Veci.rep &( s # "solver_t" ->ₛ "tagged")    (ms_tagged M) **
   Veci.rep &( s # "solver_t" ->ₛ "stack")     (ms_stack M) **
   Veci.rep &( s # "solver_t" ->ₛ "trail_lim")
            (mt_lim (ms_core M)) **
   Veci.rep &( s # "solver_t" ->ₛ "model")     (ms_model M)) **
  &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
  binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
  clause_db_rep (ms_prob M) **
  clause_db_rep (ms_learnt M) **
  stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).

Definition setnvars_open_at (s : Z) (M : msolver)
    (wl act asg opos rsn lvl trl tgs : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "size")  # Int |-> ms_size M **
  &( s # "solver_t" ->ₛ "cap")   # Int |-> ms_cap M **
  (* qtail is READ (not written): the trail realloc shim takes it as its live-prefix
     argument, and QCP cannot read through the opaque frame. *)
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  (&( s # "solver_t" ->ₛ "wlists")   # Ptr |-> wl **
   &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
   &( s # "solver_t" ->ₛ "assigns")  # Ptr |-> asg **
   &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
   &( s # "solver_t" ->ₛ "reasons")  # Ptr |-> rsn **
   &( s # "solver_t" ->ₛ "levels")   # Ptr |-> lvl **
   &( s # "solver_t" ->ₛ "trail")    # Ptr |-> trl **
   &( s # "solver_t" ->ₛ "tags")     # Ptr |-> tgs) **
  (DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
   solver_double_tail act (ms_size M) (ms_cap M) **
   CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
   solver_char_tail asg (ms_size M) (ms_cap M) **
   IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
   solver_int_tail opos (ms_size M) (ms_cap M) **
   PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
   solver_ptr_tail rsn (ms_size M) (ms_cap M) **
   IntArray.seg lvl 0 (ms_size M) (mt_levels (ms_core M)) **
   solver_int_tail lvl (ms_size M) (ms_cap M) **
   CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
   solver_char_tail tgs (ms_size M) (ms_cap M)) **
  solver_trail_array_rep M trl **
  wlists_rep wl (ms_size M) (ms_wm M) **
  solver_wlists_tail wl (2 * ms_size M) (2 * ms_cap M) **
  Veci.rep &( s # "solver_t" ->ₛ "order") (ms_order M).

Lemma setnvars_open : forall s Mg,
  solver_rep_growable s Mg
  |-- EX wl act asg opos rsn lvl trl tgs : Z,
        “ solver_shape Mg ” &&
        (setnvars_open_at s Mg wl act asg opos rsn lvl trl tgs **
         setnvars_frame_at s Mg).
Proof.
  intros s Mg. unfold solver_rep_growable.
  Intros wl act asg opos rsn lvl trl tgs.
  Exists wl act asg opos rsn lvl trl tgs.
  unfold solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
         solver_scalars_rep, solver_vecs_rep, solver_fp_rep,
         setnvars_open_at, setnvars_frame_at.
  msat_entailer_with lia.
Qed.

(** Bundle the qtail cell, eight array bases and their array/watch resources.
    Size and capacity stay exposed because the loop reads and writes them.
    Parameter [sz] tracks the initialization cursor for the six size-indexed
    arrays and fresh watch slots. The trail pair stays inline so strategy
    rule 62 emits the exact loop-body atoms. *)
Definition setnvars_arrays_at (s : Z) (M : msolver) (sz : Z)
    (wl act asg opos rsn lvl trl tgs : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "qtail") # Int |-> ms_qtail M **
  &( s # "solver_t" ->ₛ "wlists")   # Ptr |-> wl **
  &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
  &( s # "solver_t" ->ₛ "assigns")  # Ptr |-> asg **
  &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
  &( s # "solver_t" ->ₛ "reasons")  # Ptr |-> rsn **
  &( s # "solver_t" ->ₛ "levels")   # Ptr |-> lvl **
  &( s # "solver_t" ->ₛ "trail")    # Ptr |-> trl **
  &( s # "solver_t" ->ₛ "tags")     # Ptr |-> tgs **
  DoubleArray.seg act 0 sz (ms_activity M) **
  solver_double_tail act sz (ms_cap M) **
  CharArray.seg asg 0 sz (mt_assigns (ms_core M)) **
  solver_char_tail asg sz (ms_cap M) **
  IntArray.seg opos 0 sz (ms_orderpos M) **
  solver_int_tail opos sz (ms_cap M) **
  PtrArray.seg rsn 0 sz (ms_reason_words M) **
  solver_ptr_tail rsn sz (ms_cap M) **
  IntArray.seg lvl 0 sz (mt_levels (ms_core M)) **
  solver_int_tail lvl sz (ms_cap M) **
  CharArray.seg tgs 0 sz (ms_tags M) **
  solver_char_tail tgs sz (ms_cap M) **
  IntArray.seg trl 0 (ms_qtail M) (mt_trail (ms_core M)) **
  solver_int_tail trl (ms_qtail M) (ms_cap M) **
  wlists_rep wl sz (ms_wm M) **
  solver_wlists_tail wl (2 * sz) (2 * ms_cap M).

Lemma setnvars_open_arrays : forall s Mg,
  solver_rep_growable s Mg
  |-- EX wl act asg opos rsn lvl trl tgs : Z,
        “ solver_shape Mg ” &&
        (&( s # "solver_t" ->ₛ "size") # Int |-> ms_size Mg **
         &( s # "solver_t" ->ₛ "cap")  # Int |-> ms_cap Mg **
         setnvars_arrays_at s Mg (ms_size Mg) wl act asg opos rsn lvl trl tgs **
         Veci.rep &( s # "solver_t" ->ₛ "order") (ms_order Mg) **
         setnvars_frame_at s Mg).
Proof.
  intros s Mg. sep_apply setnvars_open.
  Intros wl act asg opos rsn lvl trl tgs.
  Exists wl act asg opos rsn lvl trl tgs.
  unfold setnvars_open_at, setnvars_arrays_at, solver_trail_array_rep.
  msat_entailer_with lia.
Qed.

Definition setnvars_core_equiv (M0 M : msolver) : Prop :=
  mt_qhead (ms_core M) = mt_qhead (ms_core M0) /\
  mt_lim   (ms_core M) = mt_lim   (ms_core M0) /\
  ms_qtail M = ms_qtail M0 /\
  ms_capacity_pending_qhead M = ms_capacity_pending_qhead M0 /\
  ms_capacity_root_propagation_pending M =
    ms_capacity_root_propagation_pending M0 /\
  ms_root_level M = ms_root_level M0 /\
  ms_prob M = ms_prob M0 /\ ms_learnt M = ms_learnt M0 /\
  ms_binary M = ms_binary M0 /\ ms_binary_lits M = ms_binary_lits M0 /\
  ms_model M = ms_model M0 /\
  ms_tagged M = ms_tagged M0 /\
  ms_stack M = ms_stack M0 /\
  ms_var_inc M = ms_var_inc M0 /\ ms_var_decay M = ms_var_decay M0 /\
  ms_cla_inc M = ms_cla_inc M0 /\ ms_cla_decay M = ms_cla_decay M0 /\
  ms_random_seed M = ms_random_seed M0 /\ ms_progress M = ms_progress M0 /\
  ms_simpdb_assigns M = ms_simpdb_assigns M0 /\
  ms_simpdb_props M = ms_simpdb_props M0 /\
  ms_verbosity M = ms_verbosity M0 /\ ms_stats M = ms_stats M0.

Lemma setnvars_frame_at_congr : forall s M0 M,
  setnvars_core_equiv M0 M ->
  setnvars_frame_at s M = setnvars_frame_at s M0.
Proof.
  intros s M0 M H. unfold setnvars_core_equiv in H.
  unfold setnvars_frame_at.
  destruct H as (Hqh & Hlm & Hqt & Hcp & Hcr & Hrl & Hpb & Hlr
                 & Hbi & Hbl & Hmo & Htg & Hst
                 & Hvi & Hvd & Hci & Hcd & Hrs & Hpr & Hsa & Hsp & Hvb & Hstats).
  rewrite ?Hqh, ?Hlm, ?Hqt, ?Hcp, ?Hcr, ?Hrl, ?Hpb, ?Hlr,
          ?Hbi, ?Hbl, ?Hmo, ?Htg, ?Hst, ?Hvi, ?Hvd,
          ?Hci, ?Hcd, ?Hrs, ?Hpr, ?Hsa, ?Hsp, ?Hvb, ?Hstats.
  reflexivity.
Qed.


(* Glue: the frame survives every step solver_setnvars takes.           *)


Lemma setnvars_core_equiv_refl : forall M, setnvars_core_equiv M M.
Proof. intros M. unfold setnvars_core_equiv. repeat split; reflexivity. Qed.

Lemma setnvars_core_equiv_trans : forall M0 M1 M2,
  setnvars_core_equiv M0 M1 -> setnvars_core_equiv M1 M2 ->
  setnvars_core_equiv M0 M2.
Proof.
  intros M0 M1 M2 H01 H12. unfold setnvars_core_equiv in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; etransitivity; eassumption.
Qed.

Lemma setnvars_core_equiv_set_cap : forall M c,
  setnvars_core_equiv M (msolver_set_cap M c).
Proof.
  intros M c. unfold setnvars_core_equiv, msolver_set_cap, msolver_propagation_update.
  repeat split; reflexivity.
Qed.

Lemma setnvars_core_equiv_add_var_sift : forall M a0 orderpos1 order1,
  setnvars_core_equiv M
    (msolver_heap_project (msolver_add_var M a0) orderpos1 order1).
Proof.
  intros M a0 orderpos1 order1.
  unfold setnvars_core_equiv, msolver_heap_project, msolver_core_heap_update,
         msolver_add_var, mtrail_add_var.
  repeat split; reflexivity.
Qed.

Lemma setnvars_frame_at_add_var_sift : forall s M a0 orderpos1 order1,
  setnvars_frame_at s
    (msolver_heap_project (msolver_add_var M a0) orderpos1 order1)
  = setnvars_frame_at s M.
Proof.
  intros. apply setnvars_frame_at_congr.
  apply setnvars_core_equiv_add_var_sift.
Qed.

Lemma setnvars_frame_at_set_cap : forall s M c,
  setnvars_frame_at s (msolver_set_cap M c) = setnvars_frame_at s M.
Proof.
  intros. apply setnvars_frame_at_congr. apply setnvars_core_equiv_set_cap.
Qed.

Lemma order_update_pre_add_var : forall n F A_arr A_inst M,
  msolver_inv n F A_arr A_inst M ->
  ms_size M < ms_cap M ->
  2 * (n + 1) <= INT_MAX ->
  order_update_pre (n + 1) (ms_size M)
    (ms_order M ++ (ms_size M :: nil))
    (ms_orderpos M ++ (Zlength (ms_order M) :: nil)).
Proof.
  intros n F A_arr A_inst M HI Hcap Hint.
  set (a0 := Z_to_fp64 0).
  pose proof (msi_size HI) as Hsize.
  pose proof (msw_shape (msi_weak HI)) as Hsh.
  unfold solver_shape in Hsh.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assert (Hopl : Zlength (ms_orderpos M) = ms_size M) by assumption.
  pose proof (msolver_inv_add_var _ _ _ _ _ a0 HI Hcap Hint) as HI1.
  pose proof (msw_heap_wf (msi_weak HI1)) as Hwf.
  unfold order_update_pre. split; [ | split ].
  - exact Hwf.
  - lia.
  - rewrite app_Znth2 by lia. rewrite Hopl.
    replace (ms_size M - ms_size M) with 0 by lia.
    cbn. pose proof (Zlength_nonneg (ms_order M)). lia.
Qed.


Definition setnvars_bound (n0 var n : Z) : Prop := var = n0 \/ var <= n.

Lemma setnvars_bound_entry : forall n0 n, setnvars_bound n0 n0 n.
Proof. intros. left. reflexivity. Qed.

Lemma setnvars_bound_step : forall n0 var n,
  var < n -> setnvars_bound n0 (var + 1) n.
Proof. intros n0 var n H. right. lia. Qed.

Lemma setnvars_bound_exit : forall n0 var n,
  setnvars_bound n0 var n -> n <= var -> var = n \/ var = n0.
Proof. intros n0 var n [H | H] Hge; [ right | left ]; lia. Qed.

(** Appending one element to a DoubleArray prefix.  [seg_unfold] in ArrayLibCore
    is CONS-shaped, so the snoc direction is built from [seg_single] +
    [seg_merge_to_seg].  Only [DoubleArray] needs it: `.strategies` carries
    Int/Ptr/Char undef_seg rules that rejoin their written cell automatically,
    and there is no DoubleArray rule. *)

Lemma dseg_snoc : forall (l : list fp64) p lo n v,
  lo <= n ->
  DoubleArray.seg p lo n l ** (p + n * sizeof ( DOUBLE )) # Double |-> v
  |-- DoubleArray.seg p lo (n + 1) (l ++ (v :: nil)).
Proof.
  intros l p lo n v H.
  sep_apply (DoubleArray.seg_single p n v).
  sep_apply (DoubleArray.seg_merge_to_seg p lo n (n + 1) l (v :: nil)
               ltac:(lia)).
  msat_entailer_with lia.
Qed.


(* Projection tables for the two growth operations.                     *)

(* QCP's matcher is SYNTACTIC -- there is no congruence closure -- so    *)
(* once a loop-invariant witness is instantiated with a CONSTRUCTED      *)
(* model the right-hand side reads [ms_activity (msolver_set_cap M c)]   *)
(* while the heap still reads [ms_activity M], and nothing cancels.      *)
(* Both models are record literals, so every entry below is             *)
(* [reflexivity]; stating them is what turns that reduction into a       *)
(* rewrite the entailer can drive.                                      *)


Lemma msolver_set_cap_qtail : forall M c,
  ms_qtail (msolver_set_cap M c) = ms_qtail M.
Proof. reflexivity. Qed.

Lemma msolver_set_cap_activity : forall M c,
  ms_activity (msolver_set_cap M c) = ms_activity M.
Proof. reflexivity. Qed.

Lemma msolver_set_cap_tags : forall M c,
  ms_tags (msolver_set_cap M c) = ms_tags M.
Proof. reflexivity. Qed.

Lemma msolver_set_cap_reason_words : forall M c,
  ms_reason_words (msolver_set_cap M c) = ms_reason_words M.
Proof. reflexivity. Qed.

Lemma msolver_set_cap_orderpos : forall M c,
  ms_orderpos (msolver_set_cap M c) = ms_orderpos M.
Proof. reflexivity. Qed.

Lemma msolver_set_cap_order : forall M c,
  ms_order (msolver_set_cap M c) = ms_order M.
Proof. reflexivity. Qed.

Lemma msolver_set_cap_wm : forall M c,
  ms_wm (msolver_set_cap M c) = ms_wm M.
Proof. reflexivity. Qed.

(* ---- the growth step: append one variable, then re-point the heap ---- *)

Lemma mt_assigns_add_var : forall t,
  mt_assigns (mtrail_add_var t) = mt_assigns t ++ (0 :: nil).
Proof. reflexivity. Qed.

Lemma mt_levels_add_var : forall t,
  mt_levels (mtrail_add_var t) = mt_levels t ++ (0 :: nil).
Proof. reflexivity. Qed.

Lemma mt_trail_add_var : forall t,
  mt_trail (mtrail_add_var t) = mt_trail t.
Proof. reflexivity. Qed.

Lemma msolver_sift_size : forall M a0 op o1,
  ms_size (msolver_heap_project (msolver_add_var M a0) op o1)
  = ms_size M + 1.
Proof. reflexivity. Qed.

Lemma msolver_sift_cap : forall M a0 op o1,
  ms_cap (msolver_heap_project (msolver_add_var M a0) op o1) = ms_cap M.
Proof. reflexivity. Qed.

Lemma msolver_sift_qtail : forall M a0 op o1,
  ms_qtail (msolver_heap_project (msolver_add_var M a0) op o1)
  = ms_qtail M.
Proof. reflexivity. Qed.

Lemma msolver_sift_core : forall M a0 op o1,
  ms_core (msolver_heap_project (msolver_add_var M a0) op o1)
  = mtrail_add_var (ms_core M).
Proof. reflexivity. Qed.

Lemma msolver_sift_reason_words : forall M a0 op o1,
  ms_reason_words (msolver_heap_project (msolver_add_var M a0) op o1)
  = ms_reason_words M ++ (0 :: nil).
Proof. reflexivity. Qed.

Lemma msolver_sift_tags : forall M a0 op o1,
  ms_tags (msolver_heap_project (msolver_add_var M a0) op o1)
  = ms_tags M ++ (0 :: nil).
Proof. reflexivity. Qed.

Lemma msolver_sift_activity : forall M a0 op o1,
  ms_activity (msolver_heap_project (msolver_add_var M a0) op o1)
  = ms_activity M ++ (a0 :: nil).
Proof. reflexivity. Qed.

Lemma msolver_sift_wm : forall M a0 op o1,
  ms_wm (msolver_heap_project (msolver_add_var M a0) op o1)
  = ms_wm M ++ (nil :: nil :: nil).
Proof. reflexivity. Qed.

Lemma msolver_sift_orderpos : forall M a0 op o1,
  ms_orderpos (msolver_heap_project (msolver_add_var M a0) op o1) = op.
Proof. reflexivity. Qed.

Lemma msolver_sift_order : forall M a0 op o1,
  ms_order (msolver_heap_project (msolver_add_var M a0) op o1) = o1.
Proof. reflexivity. Qed.

Lemma problem_clause_cert_pending : forall n F M words,
  problem_clause_cert n F M words -> problem_clause_pending_cert n F M words.
Proof.
  intros n F M words H. unfold problem_clause_cert in H.
  unfold problem_clause_pending_cert. tauto.
Qed.

Lemma clause_install_cert_of_pending : forall n F M words sel,
  0 <= sel <= 1 ->
  clause_install_pending_cert n F M words (solver_selected_is_learnt sel) ->
  clause_install_cert n (cn_F F words sel) M words (solver_selected_is_learnt sel).
Proof.
  intros n F M words sel Hb H.
  assert (sel = 0 \/ sel = 1) as [-> | ->] by lia.
  - rewrite sel_learnt_prob in *. rewrite cn_F_prob.
    unfold clause_install_cert, clause_install_pending_cert in *; cbv iota in *.
    unfold problem_clause_pending_cert in H. unfold problem_clause_cert.
    destruct H as (H1 & H2 & H3 & H4).
    repeat split; try assumption.
    apply in_or_app. right. left. reflexivity.
  - rewrite sel_learnt_learnt in *. rewrite cn_F_learnt.
    unfold clause_install_cert, clause_install_pending_cert in *; cbv iota in *.
    exact H.
Qed.

Lemma clause_install_pending_cert_wf : forall n F M words b,
  clause_install_pending_cert n F M words b ->
  1 <= Zlength words /\ Forall (lit_wf_c n) words /\ NoDup (map lit_var_c words).
Proof.
  intros n F M words b H. unfold clause_install_pending_cert in H. destruct b.
  - unfold record_clause_cert, record_ready_cert in H. tauto.
  - unfold problem_clause_pending_cert in H.
    destruct H as (H1 & H2 & H3 & _). split; [ | split ]; [lia | assumption | assumption].
Qed.


(** ===== group: generic clause installation ===== *)

(* The INSTALL step, generalised.                                         *)

(* [msolver_inv_install_learnt] and [msolver_inv_install_problem] are      *)
(* proved, and they take DIFFERENT hypotheses -- the learnt side wants     *)
(* [entails_clause] and an unassigned head, the problem side wants only    *)
(* that the two watched literals are not both processed.  The pending      *)
(* certificate supplies exactly the right one on each arm.                *)


Lemma clause_install_pending_cert_install :
  forall n F M c words lb b,
  clause_install_pending_cert n F M words lb ->
  clause_install_pending_cert n F (msolver_install_clause M c words b) words lb.
Proof.
  intros n F M c words lb b H.
  unfold clause_install_pending_cert in *. destruct lb.
  - unfold record_clause_cert, record_ready_cert in *.
    rewrite ms_core_install.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
    do 6 (split; [assumption |]).
    intros Hlen. unfold solver_at_root in *.
    rewrite ms_core_install, ms_root_level_install. exact (H7 Hlen).
  - unfold problem_clause_pending_cert in *.
    rewrite ms_core_install. exact H.
Qed.

Lemma clause_install_cert_install_gen :
  forall n F M c words sel,
    0 <= sel <= 1 ->
    clause_install_pending_cert n F M words (solver_selected_is_learnt sel) ->
    clause_install_cert n (cn_F F words sel)
      (msolver_install_clause M c words (solver_selected_is_learnt sel))
      words (solver_selected_is_learnt sel).
Proof.
  intros n F M c words sel Hb H.
  apply clause_install_cert_of_pending; [assumption |].
  apply clause_install_pending_cert_install. exact H.
Qed.

(* The pending certificate's problem arm says EVERY literal is unassigned;
   [minisat_processed_unassigned] turns that into "not processed" for the
   first watched literal, which is all [msolver_inv_install_problem] needs. *)
Lemma pending_head_unassigned :
  forall n F M words i,
    0 <= i < Zlength words ->
    problem_clause_pending_cert n F M words ->
    Znth (lit_var_c (Znth i words 0)) (mt_assigns (ms_core M)) 0 = 0.
Proof.
  intros n F M words i Hi H. unfold problem_clause_pending_cert in H.
  destruct H as (_ & _ & _ & Hall).
  exact (Forall_Znth_elim Z
    (fun l => Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0)
    words 0 i Hall Hi).
Qed.

Lemma msolver_inv_install_gen :
  forall n F A_arr A_inst M c words sel,
    0 <= sel <= 1 ->
    msolver_inv n F A_arr A_inst M ->
    clause_allocator_fresh M c ->
    clause_install_pending_cert n F M words (solver_selected_is_learnt sel) ->
    2 <= Zlength words ->
    lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
    0 <= lit_neg_c (Znth 0 words 0) < 2 * n ->
    0 <= lit_neg_c (Znth 1 words 0) < 2 * n ->
    msolver_inv n (cn_F F words sel) A_arr A_inst
      (msolver_install_clause M c words (solver_selected_is_learnt sel)).
Proof.
  intros n F A_arr A_inst M c words sel Hb Hinv Hfresh Hcert Hlen Hne H0 H1.
  assert (sel = 0 \/ sel = 1) as [-> | ->] by lia.
  - rewrite sel_learnt_prob in *. rewrite cn_F_prob.
    unfold clause_install_pending_cert in Hcert; cbv iota in Hcert.
    pose proof (pending_head_unassigned n F M words 0 ltac:(lia) Hcert) as Hun0.
    unfold problem_clause_pending_cert in Hcert.
    destruct Hcert as (Hc1 & Hc2 & Hc3 & _).
    change (msolver_install_clause M c words false)
      with (msolver_install_problem_clause M c words).
    apply msolver_inv_install_problem; try assumption.
    intros [Hp0 _]. revert Hp0.
    apply minisat_processed_unassigned. exact Hun0.
  - rewrite sel_learnt_learnt in *. rewrite cn_F_learnt.
    unfold clause_install_pending_cert in Hcert; cbv iota in Hcert.
    unfold record_clause_cert, record_ready_cert in Hcert.
    destruct Hcert as (_ & Hc2 & Hc3 & Hent & Hhead & _ & _).
    apply msolver_inv_install_learnt; assumption.
Qed.


(** * [solver_addclause]. *)

Lemma lit_var_eq_adjacent : forall x y,
  0 <= x -> x < y -> lit_var_c x = lit_var_c y -> y = lit_neg_c x.
Proof.
  intros x y Hx Hlt Heq. unfold lit_var_c in Heq.
  pose proof (Z.div_mod x 2 ltac:(lia)) as Hx2.
  pose proof (Z.div_mod y 2 ltac:(lia)) as Hy2.
  pose proof (Z.mod_pos_bound x 2 ltac:(lia)) as Hxm.
  pose proof (Z.mod_pos_bound y 2 ltac:(lia)) as Hym.
  assert (Hxe : x mod 2 = 0) by lia.
  assert (Hy1 : y = x + 1) by lia.
  rewrite lit_neg_c_even; [lia |].
  apply Z.even_spec. exists (x / 2). lia.
Qed.


(* "No element is the negation of its immediate predecessor" --           *)
(*      exactly what addclause's tautology test rejects.                  *)


Fixpoint no_adjacent_complement (l : list Z) : Prop :=
  match l with
  | nil => True
  | x :: rest =>
      match rest with
      | nil => True
      | y :: _ => y <> lit_neg_c x
      end /\ no_adjacent_complement rest
  end.

Lemma strict_sorted_head_le : forall x r y,
  strict_sorted (x :: r) -> In y (x :: r) -> x <= y.
Proof.
  intros x r y [Hall _] [-> | Hin]; [lia |].
  rewrite Forall_forall in Hall. pose proof (Hall y Hin). lia.
Qed.


Lemma strict_sorted_nodup_vars : forall l,
  Forall (fun x => 0 <= x) l ->
  strict_sorted l ->
  no_adjacent_complement l ->
  NoDup (map lit_var_c l).
Proof.
  induction l as [|x rest IH]; intros Hnn Hs Hna; simpl.
  - constructor.
  - inversion Hnn as [|? ? Hx Hnn']; subst.
    destruct Hs as [Hall Hs'].
    destruct Hna as [Hhead Hna'].
    constructor.
    + (* lit_var_c x does not reappear later *)
      intro Hin. apply in_map_iff in Hin as [y [Hvar Hiny]].
      rewrite Forall_forall in Hall.
      pose proof (Hall y Hiny) as Hxy.
      pose proof (lit_var_eq_adjacent x y Hx Hxy (eq_sym Hvar)) as Hyneg.
      (* x is even, so lit_neg_c x = x + 1: y is the SMALLEST thing above x, *)
      (* hence the head of rest -- which the tautology test excluded.        *)
      destruct rest as [|y0 r]; [inversion Hiny |].
      pose proof (strict_sorted_head_le y0 r y Hs' Hiny) as Hy0y.
      pose proof (Hall y0 (or_introl eq_refl)) as Hxy0.
      assert (Hy1 : y = x + 1).
      { rewrite Hyneg. apply lit_neg_c_even.
        pose proof (Z.div_mod x 2 ltac:(lia)).
        pose proof (Z.mod_pos_bound x 2 ltac:(lia)).
        pose proof (Z.div_mod y 2 ltac:(lia)).
        pose proof (Z.mod_pos_bound y 2 ltac:(lia)).
        unfold lit_var_c in Hvar. apply Z.even_spec. exists (x / 2). lia. }
      assert (y0 = y) by lia.
      subst y0. exact (Hhead Hyneg).
    + apply IH; assumption.
Qed.


(* The insertion sort.  *)
(*      Note the sort is NON-strict (the C shifts only while `*(j-1) *)
(*      > l`, so equal elements are kept and the sort is stable);         *)
(*      duplicates are removed later, by the dedup loop.                  *)


Fixpoint sorted_le (l : list Z) : Prop :=
  match l with
  | nil => True
  | x :: rest => Forall (fun y => x <= y) rest /\ sorted_le rest
  end.

(* [zinsert x l] places x AFTER every element <= x and BEFORE the first
   element > x -- exactly where the inner loop's shift-while-greater stops. *)
Fixpoint zinsert (x : Z) (l : list Z) : list Z :=
  match l with
  | nil => x :: nil
  | y :: r => if Z.ltb x y then x :: y :: r else y :: zinsert x r
  end.

Lemma zinsert_perm : forall x l, Permutation (x :: l) (zinsert x l).
Proof.
  intros x l; induction l as [|y r IH]; simpl.
  - apply Permutation_refl.
  - destruct (Z.ltb x y) eqn:E.
    + apply Permutation_refl.
    + eapply Permutation_trans; [apply perm_swap |].
      apply perm_skip. exact IH.
Qed.

Lemma zinsert_In : forall x l z, In z (zinsert x l) -> z = x \/ In z l.
Proof.
  intros x l z Hin.
  apply Permutation_in with (l' := x :: l) in Hin.
  - destruct Hin as [-> | Hin]; [left; reflexivity | right; exact Hin].
  - apply Permutation_sym, zinsert_perm.
Qed.

Lemma zinsert_sorted : forall x l, sorted_le l -> sorted_le (zinsert x l).
Proof.
  intros x l; induction l as [|y r IH]; intros Hs; simpl.
  - split; [constructor | exact I].
  - destruct Hs as [Hall Hs].
    destruct (Z.ltb x y) eqn:E.
    + apply Z.ltb_lt in E. simpl. split; [| split; assumption].
      constructor; [lia |].
      rewrite Forall_forall in *. intros z Hz. pose proof (Hall z Hz). lia.
    + apply Z.ltb_ge in E. split; [| apply IH; exact Hs].
      rewrite Forall_forall. intros z Hz.
      apply zinsert_In in Hz as [-> | Hz]; [lia |].
      rewrite Forall_forall in Hall. exact (Hall z Hz).
Qed.


(* Growing the dedup output on the right -- the loop's keep step.         *)


Lemma no_adjacent_complement_snoc : forall l y,
  no_adjacent_complement l ->
  (l = nil \/ y <> lit_neg_c (last l 0)) ->
  no_adjacent_complement (l ++ y :: nil).
Proof.
  induction l as [|x r IH]; intros y Hna Hlast; simpl.
  - split; [exact I | exact I].
  - destruct Hna as [Hhd Hna].
    destruct Hlast as [Hnil | Hy]; [discriminate Hnil |].
    destruct r as [|z r'].
    + simpl in Hy |- *. split; [exact Hy | split; exact I].
    + simpl app. split.
      * exact Hhd.
      * apply IH; [exact Hna | right]. exact Hy.
Qed.


(* The stats bump.                                                        *)

(*   addclause ends with  s->stats.clauses++;  s->stats.clauses_literals  *)
(*   += j - begin.  Those are indices 5 and 6 of [ms_stats] (stats_rep,   *)
(*   in [solver_qcp_model.v]), and the fields are uint64, so the           *)
(*   [record_stats_update] idiom applies verbatim at the                  *)
(*   problem-clause indices: [MiniSatTarget.lo64] WRAPS, which is why no  *)
(*   overflow precondition is required   *)


Definition addclause_stats_update (words stats : list Z) : list Z :=
  stats_set_clauses_literals (MiniSatTarget.lo64 (stats_clauses_literals stats + Zlength words)) (stats_set_clauses
  (MiniSatTarget.lo64 (stats_clauses stats + 1)) stats).

Definition msolver_addclause_finish (M : msolver) (words : list Z) : msolver :=
  msolver_with_cla_inc_stats M (ms_cla_inc M)
    (addclause_stats_update words (ms_stats M)).

Lemma addclause_finish_size : forall M words,
  ms_size (msolver_addclause_finish M words) = ms_size M.
Proof. intros. reflexivity. Qed.

Lemma addclause_finish_cap : forall M words,
  ms_cap (msolver_addclause_finish M words) = ms_cap M.
Proof. intros. reflexivity. Qed.

Lemma addclause_finish_stats : forall M words,
  ms_stats (msolver_addclause_finish M words)
  = addclause_stats_update words (ms_stats M).
Proof. intros. reflexivity. Qed.


(* The three loop invariants, as pure predicates.                         *)

(*   Corpus idiom (selectionsort in solver_qcp.c): the relational content *)
(*   lives in                                                             *)
(*   a named predicate so the `Inv Assert' stays short and every cut can  *)
(*   restate it as ONE conjunct -- which matters because a cut drops      *)
(*   hypotheses wholesale.                                                *)


Definition addclause_sort_outer_inv
    (n maxvar : Z) (input sorted rest : list Z) : Prop :=
  Permutation (sorted ++ rest) input /\
  sorted_le sorted /\
  Forall (fun x => 0 <= x) (sorted ++ rest) /\
  Forall (lit_wf_c n) (sorted ++ rest) /\
  0 <= maxvar /\ maxvar < n /\
  Forall (fun x => lit_var_c x <= maxvar) sorted.

(* Mid-shift the array is  pre ++ [hole] ++ suf ++ rest : the element being
   inserted lives in the local `l' and its old slot has been overwritten by
   a copy of its left neighbour.  [zinsert] describes the loop's EXIT, not
   this state, so the hole is spelled explicitly. *)
Definition addclause_sort_inner_inv
    (l : Z) (sorted pre suf : list Z) : Prop :=
  sorted = pre ++ suf /\
  sorted_le sorted /\
  Forall (fun y => l < y) suf.

Definition addclause_dedup_inv
    (n : Z) (assigns input kept : list Z) (lst : Z) : Prop :=
  Forall (fun x => In x input) kept /\
  strict_sorted kept /\
  no_adjacent_complement kept /\
  Forall (fun x => 0 <= x) kept /\
  Forall (lit_wf_c n) kept /\
  Forall (fun x => Znth (lit_var_c x) assigns 0 = 0) kept /\
  Forall (fun x => x <= lst) kept /\
  lst = last kept (-2) /\
  (0 - 2) <= lst.

Lemma last_snoc_Z : forall (l : list Z) x d, last (l ++ x :: nil) d = x.
Proof.
  induction l as [|a r IH]; intros x d; simpl; [reflexivity|].
  destruct (r ++ x :: nil) eqn:E.
  - destruct r; simpl in E; discriminate E.
  - rewrite <- E. apply IH.
Qed.

(* The dedup loop's KEEP branch.  The guard it runs under is exactly
   `*i <> last' and `*i <> lit_neg(last)' and `values[var] = 0'; sortedness
   of the input turns `<>' into `>', which is what makes the single
   comparison against the predecessor a COMPLETE duplicate test. *)
Lemma addclause_dedup_step : forall n assigns input kept lst x,
  addclause_dedup_inv n assigns input kept lst ->
  In x input ->
  lst < x ->
  x <> lit_neg_c lst ->
  0 <= x ->
  lit_wf_c n x ->
  Znth (lit_var_c x) assigns 0 = 0 ->
  addclause_dedup_inv n assigns input (kept ++ x :: nil) x.
Proof.
  intros n assigns input kept lst x Hinv Hin Hlt Hneg Hx Hwf Hass.
  destruct Hinv as (Hmem & Hss & Hna & H0 & Hwfk & Hasgk & Hle & Hlast & Hlst).
  assert (Hltall : Forall (fun y => y < x) kept).
  { rewrite Forall_forall in Hle |- *. intros y Hy. specialize (Hle y Hy). lia. }
  unfold addclause_dedup_inv. repeat split.
  - apply Forall_app; split; [exact Hmem | constructor; [exact Hin | constructor]].
  - apply strict_sorted_snoc; assumption.
  - apply no_adjacent_complement_snoc; [exact Hna |].
    destruct kept as [|a rest]; [left; reflexivity | right].
    assert (Hd : last (a :: rest) 0 = last (a :: rest) (-2)).
    { pose proof (@app_removelast_last Z (a :: rest) (-2)
        ltac:(discriminate)) as Heq.
      rewrite Heq at 1. rewrite last_snoc_Z. reflexivity. }
    rewrite Hd, <- Hlast. exact Hneg.
  - apply Forall_app; split; [exact H0 | constructor; [exact Hx | constructor]].
  - apply Forall_app; split; [exact Hwfk | constructor; [exact Hwf | constructor]].
  - apply Forall_app; split; [exact Hasgk | constructor; [exact Hass | constructor]].
  - apply Forall_app; split.
    + rewrite Forall_forall in Hle |- *. intros y Hy. specialize (Hle y Hy). lia.
    + constructor; [lia | constructor].
  - symmetry. apply last_snoc_Z.
  - lia.
Qed.

Lemma addclause_dedup_cert : forall n M input kept lst,
  addclause_dedup_inv n (mt_assigns (ms_core M)) input kept lst ->
  2 <= Zlength kept ->
  2 <= Zlength kept /\
  Forall (lit_wf_c n) kept /\
  NoDup (map lit_var_c kept) /\
  Forall (fun l => Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0) kept.
Proof.
  intros n M input kept lst Hinv Hlen.
  destruct Hinv as (_ & Hss & Hna & H0 & Hwf & Hasg & _ & _ & _).
  split; [exact Hlen |].
  split; [exact Hwf |].
  split; [apply strict_sorted_nodup_vars; assumption | exact Hasg].
Qed.

Lemma zinsert_split : forall l pre suf,
  Forall (fun y => y <= l) pre ->
  Forall (fun y => l < y) suf ->
  zinsert l (pre ++ suf) = pre ++ l :: suf.
Proof.
  induction pre as [|a r IH]; intros suf Hpre Hsuf; simpl app.
  - destruct suf as [|b s]; [reflexivity |].
    inversion Hsuf as [|? ? Hb ?]; subst.
    cbn [zinsert].
    replace (Z.ltb l b) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  - inversion Hpre as [|? ? Ha Hr]; subst.
    cbn [zinsert].
    replace (Z.ltb l a) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite IH by assumption. reflexivity.
Qed.

(* Processing a prefix may delete duplicates and literals false in every
   model of F; it must preserve the clause represented by that prefix. *)
Definition addclause_prefix_equiv (F : cnf) (processed kept : list Z) : Prop :=
  forall rho, models rho F ->
    (clause_satisfied rho (lits_denote processed) <->
     clause_satisfied rho (lits_denote kept)).

Lemma addclause_root_true : forall n F t l,
  mtrail_wf n t -> trail_implied F t -> Zlength (mt_lim t) = 0 ->
  lit_wf_c n l -> lit_true (mt_assigns t) l ->
  entails_clause F [lit_denote l].
Proof.
  intros n F t l Hwf Himpl Hroot Hl Htrue.
  destruct (mtrail_wf_trail_covers n t Hwf l Hl Htrue)
    as [i [Hi Heq]].
  assert (Hdec : decisions_are t nil).
  { unfold decisions_are. rewrite Hroot.
    reflexivity. }
  pose proof (trail_implied_at_root F t nil Himpl Hdec i Hi) as Hent.
  rewrite Heq in Hent. unfold cnf_with_units in Hent.
  simpl map in Hent. rewrite app_nil_r in Hent. exact Hent.
Qed.

Lemma addclause_root_false : forall n F t l,
  mtrail_wf n t -> trail_implied F t -> Zlength (mt_lim t) = 0 ->
  lit_wf_c n l -> lit_false (mt_assigns t) l ->
  forall rho, models rho F -> eval_literal rho (lit_denote l) = false.
Proof.
  intros n F t l Hwf Himpl Hroot Hl Hfalse rho HF.
  pose proof (addclause_root_true n F t (lit_neg_c l) Hwf Himpl Hroot
    (lit_neg_c_wf n l Hl) (lit_false_neg_true (mt_assigns t) l Hfalse))
    as Hent.
  destruct (Hent rho HF) as [a [[Ha | Ha] Hval]]; [subst a | contradiction].
  rewrite lit_denote_neg in Hval by (destruct Hl; lia).
  rewrite eval_literal_neg in Hval.
  destruct (eval_literal rho (lit_denote l)); simpl in *; congruence.
Qed.

Lemma addclause_assigned_false : forall n t l,
  mtrail_wf n t -> lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns t) 0 <> 0 ->
  Znth (lit_var_c l) (mt_assigns t) 0 <> lit_sig l ->
  lit_false (mt_assigns t) l.
Proof.
  intros n t l Hwf Hl Hnz Hnt.
  pose proof (lit_var_c_in_range n l Hl) as Hr.
  assert (Hcell : lbool_cell (Znth (lit_var_c l) (mt_assigns t) 0)).
  { eapply Forall_Znth_elim; [exact (mtw_cells Hwf) |].
    rewrite (mtw_assigns_len Hwf). exact Hr. }
  unfold lbool_cell in Hcell. unfold lit_false.
  destruct Hcell as [Hcell | [Hcell | Hcell]];
    destruct (lit_sig_values l) as [Hsig | Hsig]; lia.
Qed.

Lemma addclause_satisfied_snoc : forall rho words l,
  clause_satisfied rho (lits_denote (words ++ [l])) <->
  clause_satisfied rho (lits_denote words) \/
  eval_literal rho (lit_denote l) = true.
Proof.
  intros rho words l. rewrite lits_denote_app.
  unfold clause_satisfied. simpl lits_denote.
  split.
  - intros [a [Hin Ha]]. apply in_app_iff in Hin.
    destruct Hin as [Hin | [Hin | Hin]].
    + left. exists a. auto.
    + subst a. right. exact Ha.
    + contradiction.
  - intros [[a [Hin Ha]] | Ha].
    + exists a. split; [apply in_app_iff; left; exact Hin | exact Ha].
    + exists (lit_denote l). split;
        [apply in_app_iff; right; simpl; auto | exact Ha].
Qed.

Lemma addclause_prefix_nil : forall F,
  addclause_prefix_equiv F nil nil.
Proof. intros F rho HF. reflexivity. Qed.

Lemma addclause_prefix_keep : forall F processed kept l,
  addclause_prefix_equiv F processed kept ->
  addclause_prefix_equiv F (processed ++ [l]) (kept ++ [l]).
Proof.
  intros F processed kept l H rho HF.
  rewrite !addclause_satisfied_snoc, (H rho HF). reflexivity.
Qed.

Lemma addclause_prefix_duplicate : forall F processed kept l,
  addclause_prefix_equiv F processed kept -> In l kept ->
  addclause_prefix_equiv F (processed ++ [l]) kept.
Proof.
  intros F processed kept l H Hin rho HF.
  rewrite addclause_satisfied_snoc, (H rho HF).
  split; [intros [Hs | Hv] | intro Hs; left; exact Hs].
  - exact Hs.
  - exists (lit_denote l). split; [apply lits_denote_in; exact Hin | exact Hv].
Qed.

Lemma addclause_prefix_false : forall F processed kept l,
  addclause_prefix_equiv F processed kept ->
  (forall rho, models rho F -> eval_literal rho (lit_denote l) = false) ->
  addclause_prefix_equiv F (processed ++ [l]) kept.
Proof.
  intros F processed kept l H Hfalse rho HF.
  rewrite addclause_satisfied_snoc, (H rho HF), (Hfalse rho HF).
  split; [intros [Hs | Hbad]; [exact Hs | discriminate] | auto].
Qed.

Lemma addclause_prefix_permutation : forall F sorted input kept,
  Permutation sorted input -> addclause_prefix_equiv F sorted kept ->
  addclause_prefix_equiv F input kept.
Proof.
  intros F sorted input kept Hp H rho HF.
  assert (Hp' : Permutation (lits_denote sorted) (lits_denote input)).
  { unfold lits_denote. apply Permutation_map. exact Hp. }
  split.
  - intro Hin. apply (proj1 (H rho HF)).
    eapply clause_satisfied_perm; [apply Permutation_sym; exact Hp' | exact Hin].
  - intro Hkept. eapply clause_satisfied_perm; [exact Hp' |].
    apply (proj2 (H rho HF)). exact Hkept.
Qed.

(* Equality with the sentinel is essential: an empty retained list must not
   make an unrelated literal look like a duplicate. *)
Lemma addclause_last_member : forall kept lst,
  lst = last kept (-2) -> 0 <= lst -> In lst kept.
Proof.
  intros kept lst Hlast Hnonneg.
  destruct kept as [|a rest]; [simpl in Hlast; lia |].
  pose proof (@app_removelast_last Z (a :: rest) (-2) ltac:(discriminate)) as H.
  rewrite <- Hlast in H. rewrite H at 1.
  apply in_app_iff. right. simpl. auto.
Qed.

Lemma addclause_root_satisfied_input : forall F input l,
  In l input -> entails_clause F [lit_denote l] ->
  entails_clause F (lits_denote input).
Proof.
  intros F input l Hin Hent rho HF.
  destruct (Hent rho HF) as [a [[Ha | Ha] Hv]]; [subst a | contradiction].
  exists (lit_denote l). split; [apply lits_denote_in; exact Hin | exact Hv].
Qed.

Lemma addclause_dedup_complement : forall n assigns input kept lst l,
  addclause_dedup_inv n assigns input kept lst ->
  In l input -> 0 <= l -> l = lit_neg_c lst ->
  forall rho, clause_satisfied rho (lits_denote input).
Proof.
  intros n assigns input kept lst l Hded Hl Hl0 Hneg.
  destruct Hded as
    (Hmem & Hsort & Hcomp & Hnonneg & Hwf & Hun & Hle & Hlast & Hbound).
  assert (Hprev : In lst kept).
  { destruct kept as [|a rest].
    - simpl in Hlast. subst lst. change (l = -1) in Hneg. lia.
    - pose proof (@app_removelast_last Z (a :: rest) (-2)
        ltac:(discriminate)) as Heq.
      rewrite <- Hlast in Heq. rewrite Heq at 1.
      apply in_app_iff. right. simpl. auto. }
  rewrite Forall_forall in Hmem, Hnonneg.
  intro rho. destruct (eval_literal rho (lit_denote lst)) eqn:Ev.
  - exists (lit_denote lst). split.
    + apply lits_denote_in. exact (Hmem lst Hprev).
    + exact Ev.
  - exists (lit_denote l). split; [apply lits_denote_in; exact Hl |].
    rewrite Hneg, lit_denote_neg by exact (Hnonneg lst Hprev).
    rewrite eval_literal_neg, Ev. reflexivity.
Qed.

Lemma addclause_models_append : forall rho F words,
  models rho (F ++ [lits_denote words]) <->
  models rho F /\ clause_satisfied rho (lits_denote words).
Proof.
  intros rho F words. unfold models. rewrite Forall_app.
  split.
  - intros [HF HC]. inversion HC; subst. auto.
  - intros [HF HC]. split; [exact HF | constructor; [exact HC | constructor]].
Qed.

Lemma addclause_install_equiv : forall F input kept,
  addclause_prefix_equiv F input kept ->
  forall rho, models rho (F ++ [lits_denote kept]) <->
              models rho (F ++ [lits_denote input]).
Proof.
  intros F input kept H rho. rewrite !addclause_models_append.
  split; intros [HF HC]; split; [exact HF | | exact HF |].
  - apply (proj2 (H rho HF)). exact HC.
  - apply (proj1 (H rho HF)). exact HC.
Qed.

Lemma addclause_entailed_equiv : forall F input,
  entails_clause F (lits_denote input) ->
  forall rho, models rho F <-> models rho (F ++ [lits_denote input]).
Proof.
  intros F input H rho. rewrite addclause_models_append.
  split; [intro HF; split; [exact HF | apply H; exact HF] | tauto].
Qed.

Lemma addclause_formula_wf : forall old_n n F input,
  cnf_wf old_n F -> Forall (lit_wf_c n) input ->
  cnf_wf (Z.max old_n n) (F ++ [lits_denote input]).
Proof.
  intros old_n n F input HF HI.
  pose proof (cnf_wf_mono old_n (Z.max old_n n) F (Z.le_max_l _ _) HF)
    as [HN HFW].
  split; [exact HN |]. apply Forall_app. split; [exact HFW |].
  constructor; [| constructor].
  pose proof (lits_denote_wf n input HI) as HW.
  eapply Forall_impl; [| exact HW]. intros l Hl.
  eapply literal_wf_mono; [apply Z.le_max_r | exact Hl].
Qed.

Lemma addclause_empty_unsat : forall N F input,
  cnf_wf N (F ++ [lits_denote input]) ->
  addclause_prefix_equiv F input nil ->
  cnf_unsat N (F ++ [lits_denote input]).
Proof.
  intros N F input Hwf Heq. split; [exact Hwf |].
  intros rho Hbounded Hmodel. apply addclause_models_append in Hmodel.
  destruct Hmodel as [HF HC].
  destruct (proj1 (Heq rho HF) HC) as [l [Hin Hv]]. exact Hin.
Qed.

Definition addclause_transition
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (M0 : msolver) (input : list Z) (ret : Z)
    (M' : msolver) (cur : list Z) (F' : cnf) : Prop :=
  Zlength cur = Zlength input /\
  ms_size M0 <= ms_size M' /\
  ms_cap M0 <= ms_cap M' /\
  2 * ms_cap M' <= INT_MAX /\
  ((Zlength (mt_lim (ms_core M0)) = 0 /\
    ms_capacity_root_propagation_pending M0 = 0 /\
    msolver_seed_shadow M0) ->
   (Zlength (mt_lim (ms_core M')) = 0 /\
    ms_capacity_root_propagation_pending M' = 0 /\
    msolver_seed_shadow M')) /\
  ((ret = 0 /\ F' = F /\
    msolver_inv (ms_size M') F A_arr A_inst M' /\
    cnf_unsat (Z.max (ms_size M0) n) (F ++ [lits_denote input])) \/
   (ret = 1 /\ msolver_inv (ms_size M') F' A_arr A_inst M' /\
    forall rho, models rho F' <-> models rho (F ++ [lits_denote input]))).


(* The inner loop stops at the FIRST predecessor that is <= l.  Sortedness
   then upgrades that single comparison to a bound over the whole prefix --
   which is the [Forall] that [zinsert_split] needs. *)

Lemma sorted_le_last_bound : forall l x d,
  sorted_le l -> l <> nil -> last l d <= x -> Forall (fun y => y <= x) l.
Proof.
  induction l as [|a r IH]; intros x d Hs Hne Hlast; [constructor|].
  destruct Hs as [Hall Hs].
  destruct r as [|b r'].
  - simpl in Hlast. constructor; [lia | constructor].
  - assert (Hlr : last (b :: r') d <= x) by (simpl in Hlast |- *; exact Hlast).
    assert (Hrest : Forall (fun y => y <= x) (b :: r'))
      by (apply (IH x d); [exact Hs | discriminate | exact Hlr]).
    constructor; [| exact Hrest].
    inversion Hrest as [|? ? Hb ?]; subst.
    rewrite Forall_forall in Hall. specialize (Hall b (or_introl eq_refl)). lia.
Qed.


Lemma signed_last_nbits_8_small : forall x,
  0 <= x <= 127 -> signed_last_nbits x 8 = x.
Proof.
  intros x H. unfold signed_last_nbits.
  rewrite Z.mod_small by (change (2 ^ 8) with 256; lia).
  change (2 ^ (8 - 1)) with 128.
  destruct (Coqlib.zlt x 128) as [Hlt | Hge]; [reflexivity | lia].
Qed.

Lemma signed_last_nbits_8_lit_sign : forall x,
  signed_last_nbits (lit_sign_c x) 8 = lit_sign_c x.
Proof.
  intros x. apply signed_last_nbits_8_small.
  pose proof (lit_sign_c_range x). lia.
Qed.


Lemma Forall_lit_wf_Znth : forall n l i,
  Forall (lit_wf_c n) l -> 0 <= i < Zlength l -> lit_wf_c n (Znth i l 0).
Proof.
  intros n l i H Hi. rewrite Forall_forall in H. apply H.
  apply Znth_In. lia.
Qed.

Lemma lit_wf_c_bounds : forall n l, lit_wf_c n l -> 0 <= l /\ l < 2 * n.
Proof. unfold lit_wf_c. intros n l H. lia. Qed.


Lemma signed_last_nbits_8_one_minus_lit_sign : forall x,
  signed_last_nbits (1 - lit_sign_c x) 8 = 1 - lit_sign_c x.
Proof.
  intros x. apply signed_last_nbits_8_small.
  pose proof (lit_sign_c_range x). lia.
Qed.

(* C's pointer subtraction divides the byte difference by the element size and
   QCP spells that with [Z.quot].  [lia] has no theory for [÷] at all, so the
   dedup exit's [j - begin != 1] tells it nothing until this is applied. *)
Lemma quot_mul_four : forall q, (q * 4) ÷ 4 = q.
Proof. intros q. apply Z.quot_mul. lia. Qed.

Lemma addclause_dedup_install_cert : forall n F M input kept lst,
  addclause_dedup_inv n (mt_assigns (ms_core M)) input kept lst ->
  2 <= Zlength kept ->
  clause_install_pending_cert n F M kept (solver_selected_is_learnt 0).
Proof.
  intros n F M input kept lst Hinv Hlen.
  rewrite sel_learnt_prob.
  unfold clause_install_pending_cert, problem_clause_pending_cert.
  exact (addclause_dedup_cert n M input kept lst Hinv Hlen).
Qed.


Lemma setnvars_core_equiv_pending : forall M0 M,
  setnvars_core_equiv M0 M ->
  ms_capacity_root_propagation_pending M0 = 0 ->
  ms_capacity_root_propagation_pending M = 0.
Proof.
  intros M0 M He H0. unfold setnvars_core_equiv in He.
  decompose [and] He. congruence.
Qed.

Lemma setnvars_core_equiv_seed_shadow : forall M0 M,
  setnvars_core_equiv M0 M ->
  msolver_seed_shadow M0 -> msolver_seed_shadow M.
Proof.
  intros M0 M He Hs. unfold setnvars_core_equiv in He.
  unfold msolver_seed_shadow in *.
  destruct Hs as [z [Hz Hok]]. exists z.
  decompose [and] He. split; [congruence | exact Hok].
Qed.

Lemma setnvars_core_equiv_root_summary : forall M0 M,
  setnvars_core_equiv M0 M ->
  (Zlength (mt_lim (ms_core M0)) = 0 /\
   ms_capacity_root_propagation_pending M0 = 0 /\ msolver_seed_shadow M0) ->
  (Zlength (mt_lim (ms_core M)) = 0 /\
   ms_capacity_root_propagation_pending M = 0 /\ msolver_seed_shadow M).
Proof.
  intros M0 M He [Hlim [Hpending Hseed]].
  split.
  - pose proof He as Hfields. unfold setnvars_core_equiv in Hfields.
    decompose [and] Hfields. congruence.
  - split.
    + eapply setnvars_core_equiv_pending; eauto.
    + eapply setnvars_core_equiv_seed_shadow; eauto.
Qed.

Lemma addclause_stats_update_Zlength : forall words st,
  Zlength (addclause_stats_update words st) = Zlength st.
Proof.
  intros words st. unfold addclause_stats_update, stats_set_clauses, stats_set_clauses_literals.
  rewrite !Zlength_replace_Znth. reflexivity.
Qed.

Lemma solver_shape_addclause_finish : forall M words,
  solver_shape M -> solver_shape (msolver_addclause_finish M words).
Proof.
  intros M words H. unfold solver_shape.
  rewrite addclause_finish_stats, addclause_stats_update_Zlength.
  exact H.
Qed.

Lemma addclause_finish_levels : forall s M words lvl,
  solver_levels_slice_at s (msolver_addclause_finish M words) lvl
  = solver_levels_slice_at s M lvl.
Proof. reflexivity. Qed.

Lemma addclause_finish_nonlevel_at :
  forall s M words wl act asg opos rsn trl tgs,
  solver_nonlevel_rep_at s (msolver_addclause_finish M words)
    wl act asg opos rsn trl tgs
  = solver_scalars_rep s M **
    solver_fp_rep s M **
    solver_vecs_rep s M **
    (&( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
     &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
     &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
     &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
     &( s # "solver_t" ->ₛ "reasons") # Ptr |-> rsn **
     &( s # "solver_t" ->ₛ "trail") # Ptr |-> trl **
     &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
     &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
    (DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
     solver_double_tail act (ms_size M) (ms_cap M) **
     CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
     solver_char_tail asg (ms_size M) (ms_cap M) **
     IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
     solver_int_tail opos (ms_size M) (ms_cap M) **
     PtrArray.seg rsn 0 (ms_size M) (ms_reason_words M) **
     solver_ptr_tail rsn (ms_size M) (ms_cap M) **
     CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
     solver_char_tail tgs (ms_size M) (ms_cap M)) **
    solver_trail_array_rep M trl **
    wlists_rep wl (ms_size M) (ms_wm M) **
    clause_db_rep (ms_prob M) **
    clause_db_rep (ms_learnt M) **
    binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
    stats_rep &( s # "solver_t" ->ₛ "stats")
      (addclause_stats_update words (ms_stats M)).
Proof. reflexivity. Qed.

Lemma stats_rep_open_dotted : forall s st,
  stats_rep &( s # "solver_t" ->ₛ "stats") st
  |-- &( s # "solver_t" ->ₛ "stats" .ₛ "starts") # UInt64 |-> stats_starts st **
      &( s # "solver_t" ->ₛ "stats" .ₛ "decisions") # UInt64 |-> stats_decisions st **
      &( s # "solver_t" ->ₛ "stats" .ₛ "propagations") # UInt64 |-> stats_propagations st **
      &( s # "solver_t" ->ₛ "stats" .ₛ "inspects") # UInt64 |-> stats_inspects st **
      &( s # "solver_t" ->ₛ "stats" .ₛ "conflicts") # UInt64 |-> stats_conflicts st **
      &( s # "solver_t" ->ₛ "stats" .ₛ "clauses") # UInt64 |-> stats_clauses st **
      &( s # "solver_t" ->ₛ "stats" .ₛ "clauses_literals") # UInt64 |-> stats_clauses_literals st **
      &( s # "solver_t" ->ₛ "stats" .ₛ "learnts") # UInt64 |-> stats_learnts st **
      &( s # "solver_t" ->ₛ "stats" .ₛ "learnts_literals") # UInt64 |-> stats_learnts_literals st **
      &( s # "solver_t" ->ₛ "stats" .ₛ "max_literals") # UInt64 |-> stats_max_literals st **
      &( s # "solver_t" ->ₛ "stats" .ₛ "tot_literals") # UInt64 |-> stats_tot_literals st.
Proof.
  intros s st.
  set (p := &( s # "solver_t" ->ₛ "stats")).
  stats_dot_bridge s p.
  unfold stats_rep. msat_entailer_with lia.
Qed.


Lemma replace_nth_twice_gen : forall {A} n (l : list A) a b,
  replace_nth n (replace_nth n l a) b = replace_nth n l b.
Proof.
  induction n; intros l a b; destruct l as [|x xs]; simpl; auto.
  f_equal. apply IHn.
Qed.

Lemma replace_Znth_twice : forall {A} (l : list A) i (a b : A),
  replace_Znth i b (replace_Znth i a l) = replace_Znth i b l.
Proof.
  intros A l i a b. unfold replace_Znth. apply replace_nth_twice_gen.
Qed.


Lemma replace_nth_hole : forall {A} (pre : list A) junk tl x,
  replace_nth (List.length pre) (pre ++ junk :: tl) x = pre ++ x :: tl.
Proof.
  induction pre as [|h t IH]; intros junk tl x; simpl; [reflexivity|].
  f_equal. apply IH.
Qed.

Lemma replace_Znth_hole : forall {A} (pre : list A) junk tl x,
  replace_Znth (Zlength pre) x (pre ++ junk :: tl) = pre ++ x :: tl.
Proof.
  intros A pre junk tl x. unfold replace_Znth.
  rewrite Zlength_correct, Nat2Z.id. apply replace_nth_hole.
Qed.

(* At the insertion write, [zinsert_split] identifies the rebuilt sorted
   prefix. Its [Forall (y <= l) pre] premise comes from either an empty
   prefix or the loop's stopping comparison. *)
Lemma addclause_sort_insert_outer :
  forall n maxvar input pre suf rest l,
  addclause_sort_outer_inv n maxvar input (pre ++ suf) (l :: rest) ->
  addclause_sort_inner_inv l (pre ++ suf) pre suf ->
  Forall (fun y => y <= l) pre ->
  lit_var_c l <= maxvar ->
  addclause_sort_outer_inv n maxvar input (pre ++ l :: suf) rest.
Proof.
  intros n maxvar input pre suf rest l Houter Hinner Hprele Hlv.
  unfold addclause_sort_outer_inv in Houter.
  destruct Houter as (Hperm & Hsort & Hnn & Hwf & Hm0 & Hmn & Hvar).
  unfold addclause_sort_inner_inv in Hinner.
  destruct Hinner as (Heq & Hsort2 & Hsuf).
  rewrite <- (zinsert_split l pre suf Hprele Hsuf).
  assert (Hp : Permutation (zinsert l (pre ++ suf) ++ rest)
                           ((pre ++ suf) ++ l :: rest)).
  { transitivity ((l :: (pre ++ suf)) ++ rest).
    - apply Permutation_app_tail. symmetry. apply zinsert_perm.
    - simpl. apply Permutation_middle. }
  unfold addclause_sort_outer_inv.
  split; [ rewrite Hp; exact Hperm | ].
  split; [ apply zinsert_sorted; exact Hsort | ].
  split; [ rewrite Hp; exact Hnn | ].
  split; [ rewrite Hp; exact Hwf | ].
  split; [ exact Hm0 | ]. split; [ exact Hmn | ].
  apply Forall_forall. intros z Hz.
  apply zinsert_In in Hz. destruct Hz as [->|Hz]; [exact Hlv|].
  rewrite Forall_forall in Hvar. apply Hvar. exact Hz.
Qed.

(* The `*(j-1) <= l' BREAK exit needs [Forall (y <= l) pre], which the inner
   invariant does not record -- it is established only at the break, from the
   fact that [pre] is a sorted prefix whose LAST element is the one compared. *)

Lemma sorted_le_app_l : forall l1 l2, sorted_le (l1 ++ l2) -> sorted_le l1.
Proof.
  induction l1 as [|a r IH]; intros l2 H; [exact I|].
  simpl in H |- *. destruct H as [Hall Hs]. split.
  - rewrite Forall_forall in Hall |- *. intros y Hy.
    apply Hall, in_or_app. left. exact Hy.
  - exact (IH l2 Hs).
Qed.

(* Stated at [length s] rather than [length l - 1]: nat subtraction is what makes
   the induction step fight [simpl], which reduces the index and then no rewrite
   matches. *)
Lemma nth_length_last : forall (s : list Z) a d,
  nth (List.length s) (a :: s) d = last (a :: s) d.
Proof.
  induction s as [|b r IH]; intros a d; [reflexivity|]. simpl. apply IH.
Qed.

Lemma Znth_pred_app_last : forall (pre tl : list Z) d,
  pre <> nil -> Znth (Zlength pre - 1) (pre ++ tl) d = last pre d.
Proof.
  intros pre tl d Hne. destruct pre as [|a r]; [contradiction|].
  unfold Znth. rewrite Zlength_correct.
  replace (Z.of_nat (List.length (a :: r)) - 1) with (Z.of_nat (List.length r))
    by (simpl List.length; lia).
  rewrite Nat2Z.id.
  rewrite app_nth1 by (simpl List.length; lia).
  apply nth_length_last.
Qed.

Lemma addclause_dedup_inv_nil : forall n assigns input,
  addclause_dedup_inv n assigns input nil (0 - 2).
Proof.
  intros n assigns input. unfold addclause_dedup_inv.
  simpl. repeat split; try constructor; lia.
Qed.

(* Inner-loop ESTABLISHMENT (`j = i'): the element about to be inserted is the
   HEAD of the unsorted remainder, and the sorted prefix becomes [pre] with an
   empty [suf]. *)

Lemma Znth_app_hd : forall (pre : list Z) x r d,
  Znth (Zlength pre) (pre ++ x :: r) d = x.
Proof.
  intros pre x r d. unfold Znth. rewrite Zlength_correct, Nat2Z.id.
  rewrite app_nth2 by lia.
  replace (List.length pre - List.length pre)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma addclause_sort_outer_maxvar_mono :
  forall n m1 m2 input sorted rest,
  addclause_sort_outer_inv n m1 input sorted rest ->
  m1 <= m2 -> 0 <= m2 -> m2 < n ->
  addclause_sort_outer_inv n m2 input sorted rest.
Proof.
  intros n m1 m2 input sorted rest H Hle H0 Hn.
  unfold addclause_sort_outer_inv in *.
  destruct H as (Hperm & Hsort & Hnn & Hwf & Hm0 & Hmn & Hvar).
  repeat split; try assumption.
  rewrite Forall_forall in Hvar |- *. intros y Hy.
  specialize (Hvar y Hy). lia.
Qed.

(* Inner-loop SHIFT step (`*j = *(j-1); j--'): the hole moves one slot left, so
   the split point of [pre ++ suf] moves but the LIST ITSELF is unchanged --
   which is why the invariant survives with no reasoning about sortedness. *)

Lemma removelast_app_last : forall (pre : list Z) tl,
  pre <> nil -> removelast pre ++ last pre 0 :: tl = pre ++ tl.
Proof.
  intros pre tl Hne.
  transitivity ((removelast pre ++ (last pre 0 :: nil)) ++ tl).
  - rewrite <- app_assoc. reflexivity.
  - rewrite <- (app_removelast_last 0 Hne). reflexivity.
Qed.

Lemma Zlength_removelast : forall (l : list Z),
  l <> nil -> Zlength (removelast l) = Zlength l - 1.
Proof.
  intros l Hne.
  assert (E : Zlength l = Zlength (removelast l ++ (last l 0 :: nil)))
    by (rewrite <- (app_removelast_last 0 Hne); reflexivity).
  rewrite E, Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma replace_nth_same : forall {A} (n : nat) (l : list A) (d : A),
  (n < List.length l)%nat -> replace_nth n l (nth n l d) = l.
Proof.
  induction n as [|n IH]; intros [|a r] d H; simpl in H |- *;
    try lia; try reflexivity.
  f_equal. apply IH. lia.
Qed.

Lemma replace_Znth_same : forall {A} (i : Z) (l : list A) (d : A),
  0 <= i < Zlength l -> replace_Znth i (Znth i l d) l = l.
Proof.
  intros A i l d [H1 H2]. unfold replace_Znth, Znth.
  apply replace_nth_same.
  rewrite Zlength_correct in H2. lia.
Qed.


Lemma ms_cap_install_clause : forall M c words b,
  ms_cap (msolver_install_clause M c words b) = ms_cap M.
Proof. reflexivity. Qed.

Lemma sublist_app_exact2 : forall {A} (l1 l2 : list A),
  sublist (Zlength l1) (Zlength (l1 ++ l2)) (l1 ++ l2) = l2.
Proof.
  intros A l1 l2.
  pose proof (Zlength_nonneg l1) as N1. pose proof (Zlength_nonneg l2) as N2.
  rewrite (sublist_split_app_r (Zlength l1) (Zlength (l1 ++ l2)) (Zlength l1) l1 l2);
    [ | reflexivity | rewrite Zlength_app; lia ].
  rewrite Z.sub_diag, Zlength_app.
  apply sublist_self. lia.
Qed.


Lemma app_nil_of_Zlength : forall {A} (l r : list A),
  Zlength (l ++ r) = Zlength l -> r = nil.
Proof.
  intros A l r H. rewrite Zlength_app in H.
  destruct r as [|x r']; [reflexivity|].
  pose proof (Zlength_nonneg r'). rewrite Zlength_cons in H. lia.
Qed.

Lemma lit_wf_c_of_var_bound : forall maxvar m l,
  0 <= l -> lit_var_c l <= maxvar -> maxvar + 1 <= m -> lit_wf_c m l.
Proof.
  unfold lit_wf_c, lit_var_c. intros maxvar m l H0 Hv Hm.
  split; [ assumption | ].
  destruct (Z.le_gt_cases (2 * (maxvar + 1)) l) as [Hc | Hc]; [ exfalso | lia ].
  assert (maxvar + 1 <= l / 2) by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.


Lemma ac_Znth_In : forall {A} (l : list A) (d : A) i,
  0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l d i Hi. unfold Znth. apply nth_In.
  rewrite Zlength_correct in Hi. lia.
Qed.

Lemma hd_sublist_app : forall (l : list Z),
  1 <= Zlength l -> Znth 0 l 0 :: sublist 1 (Zlength l) l = l.
Proof.
  intros [|a r] H; [ rewrite Zlength_nil in H; lia | ].
  pose proof (Zlength_nonneg r).
  rewrite sublist_cons2 by (rewrite Zlength_cons; lia).
  rewrite Zlength_cons.
  (* both indices arrive as unreduced subtractions, and Zlength_cons emits
     [Z.succ _], not [_ + 1] *)
  replace (1 - 1) with 0 by lia.
  replace (Z.succ (Zlength r) - 1) with (Zlength r) by lia.
  rewrite (sublist_self r (Zlength r)) by reflexivity.
  unfold Znth. reflexivity.
Qed.

Lemma addclause_sort_outer_init : forall n input,
  1 <= Zlength input ->
  Forall (lit_wf_c n) input ->
  addclause_sort_outer_inv n (lit_var_c (Znth 0 input 0)) input
    (Znth 0 input 0 :: nil) (sublist 1 (Zlength input) input).
Proof.
  intros n input Hlen Hwf.
  assert (Hin : In (Znth 0 input 0) input) by (apply ac_Znth_In; lia).
  assert (Hx : lit_wf_c n (Znth 0 input 0))
    by (rewrite Forall_forall in Hwf; apply Hwf, Hin).
  unfold lit_wf_c in Hx.
  assert (Happ : (Znth 0 input 0 :: nil) ++ sublist 1 (Zlength input) input = input)
    by (simpl; apply hd_sublist_app; lia).
  unfold addclause_sort_outer_inv. rewrite Happ.
  split; [ apply Permutation_refl | ].
  split; [ simpl; split; [ constructor | exact I ] | ].
  split.
  { rewrite Forall_forall in *. intros y Hy.
    specialize (Hwf y Hy). unfold lit_wf_c in Hwf. lia. }
  split; [ exact Hwf | ].
  split; [ unfold lit_var_c; apply Z.div_pos; lia | ].
  split; [ unfold lit_var_c; apply Z.div_lt_upper_bound; lia | ].
  constructor; [ lia | constructor ].
Qed.


(*   [missing_i_merge_to_seg] states its cell as [storeA x n a], which    *)
(*   for IntArray unfolds to [(x + n * sizeof ( INT )) # Int |-> a].  A   *)
(*   read of [*begin] emits the cell at the BARE address instead, so at n *)
(*   = 0 the two are equal but not syntactically unifiable and sep_apply  *)
(*   refuses. Normalise once here rather than at each use site.           *)


Lemma int_head_merge : forall x hi (l : list Z),
  0 < hi -> 0 < Zlength l ->
  x # Int |-> Znth 0 l 0 ** IntArray.missing_i x 0 0 hi l
  |-- IntArray.seg x 0 hi l.
Proof.
  intros x hi l Hhi Hl.
  pose proof (IntArray.missing_i_merge_to_seg x 0 0 hi (Znth 0 l 0) l
                ltac:(lia)) as Hm.
  cbn beta in Hm.
  replace (x + 0 * sizeof ( INT )) with x in Hm by lia.
  rewrite Z.sub_0_r in Hm.
  rewrite replace_Znth_same in Hm by lia.
  exact Hm.
Qed.


Lemma addclause_dedup_enqueue_input :
  forall F A_arr A_inst M input kept tl lst,
  msolver_inv (ms_size M) F A_arr A_inst M ->
  addclause_dedup_inv (ms_size M) (mt_assigns (ms_core M)) input kept lst ->
  1 <= Zlength kept ->
  enqueue_input (ms_size M) (Znth 0 (kept ++ tl) 0) (ms_qtail M)
    (mt_assigns (ms_core M)) (mt_levels (ms_core M)) (ms_reason_words M)
    (mt_trail (ms_core M)).
Proof.
  intros F A_arr A_inst M input kept tl lst Hinv Hded Hk.
  pose proof (msi_weak Hinv) as Hweak.
  pose proof (msw_shape Hweak) as Hshape.
  pose proof (msw_trail_wf Hweak) as Htrail.
  pose proof (msw_size Hweak) as Hsize.
  pose proof (msi_shape Hinv) as Hsh2.
  destruct Hded as (Hin & Hss & Hnac & Hpos & Hwf & Hun & Hle & Hlast & Hlst).
  assert (Hhd : Znth 0 (kept ++ tl) 0 = Znth 0 kept 0).
  { destruct kept as [|a r]; [ rewrite Zlength_nil in Hk; lia | reflexivity ]. }
  rewrite Hhd.
  assert (Hinhd : In (Znth 0 kept 0) kept) by (apply ac_Znth_In; lia).
  assert (Hwfhd : lit_wf_c (ms_size M) (Znth 0 kept 0))
    by (rewrite Forall_forall in Hwf; apply Hwf, Hinhd).
  assert (Hv : 0 <= lit_var_c (Znth 0 kept 0) < ms_size M)
    by (apply lit_var_c_in_range; exact Hwfhd).
  (* the head literal is UNASSIGNED (that is why the dedup loop kept it), so
     its variable is absent from the trail; with the trail's NoDup and range
     that forces the trail strictly shorter than the variable count -- i.e.
     there is room to enqueue. *)
  assert (Hun0 : Znth (lit_var_c (Znth 0 kept 0)) (mt_assigns (ms_core M)) 0 = 0)
    by (rewrite Forall_forall in Hun; apply Hun, Hinhd).
  assert (Hnotin : ~ In (lit_var_c (Znth 0 kept 0))
                       (map lit_var_c (mt_trail (ms_core M)))).
  { intro Hin2. apply (proj2 (mtw_assigned_iff Htrail _ Hv)) in Hin2.
    contradiction. }
  assert (Htf : Forall (fun v => 0 <= v < ms_size M)
                  (map lit_var_c (mt_trail (ms_core M)))).
  { apply Forall_map. pose proof (mtw_trail_lits Htrail) as Hl. revert Hl.
    apply Forall_impl. intros l Hl. apply lit_var_c_in_range. exact Hl. }
  assert (Hlt : Zlength (mt_trail (ms_core M)) < ms_size M).
  { assert (Hm : Zlength (map lit_var_c (mt_trail (ms_core M))) < ms_size M).
    { apply NoDup_Forall_range_missing_length_lt__search
        with (x := lit_var_c (Znth 0 kept 0));
      [ exact (mtw_n_nonneg Htrail) | exact (mtw_trail_nodup Htrail)
      | exact Htf | exact Hv | exact Hnotin ]. }
    rewrite Zlength_map_Z in Hm. exact Hm. }
  pose proof (mtw_trail_bound Htrail) as Hbound.
  unfold enqueue_input.
  unfold solver_shape in Hshape, Hsh2.
  decompose [and] Hshape.
  unfold lit_wf_c in Hwfhd.
  repeat split; try assumption; try lia.
  eapply Forall_impl; [ | exact (mtw_cells Htrail) ].
  unfold lbool_cell. intros ? ?. lia.
Qed.


(*   A named predicate rather than an inline [Forall (fun x => In x l)]:  *)
(*   annotations have no lambda syntax.                                   *)


Definition all_from (input l : list Z) : Prop := Forall (fun x => In x input) l.

Lemma all_from_of_Permutation : forall input l,
  Permutation l input -> all_from input l.
Proof.
  intros input l Hp. unfold all_from. rewrite Forall_forall.
  intros x Hx. eapply Permutation_in; eauto.
Qed.

Lemma all_from_Znth : forall input l i,
  all_from input l -> 0 <= i < Zlength l -> In (Znth i l 0) input.
Proof.
  intros input l i H Hi. unfold all_from in H.
  rewrite Forall_forall in H. apply H, ac_Znth_In, Hi.
Qed.


Definition all_ge (lst : Z) (l : list Z) : Prop := Forall (fun y => lst <= y) l.

Lemma all_ge_sentinel : forall n l, Forall (lit_wf_c n) l -> all_ge (0 - 2) l.
Proof.
  intros n l H. unfold all_ge. rewrite Forall_forall in H |- *.
  intros x Hx. specialize (H x Hx). unfold lit_wf_c in H. lia.
Qed.

Lemma sorted_le_app_r : forall l1 l2, sorted_le (l1 ++ l2) -> sorted_le l2.
Proof.
  induction l1 as [|a r IH]; intros l2 H; [exact H|].
  simpl in H. destruct H as [_ Hs]. exact (IH l2 Hs).
Qed.

Lemma sorted_le_sublist : forall l lo hi,
  0 <= lo -> lo <= hi -> hi <= Zlength l ->
  sorted_le l -> sorted_le (sublist lo hi l).
Proof.
  intros l lo hi Hlo Hlohi Hhi Hs.
  rewrite <- (sublist_self l (Zlength l)) in Hs by reflexivity.
  rewrite (sublist_split 0 (Zlength l) hi l) in Hs by lia.
  apply sorted_le_app_l in Hs.
  rewrite (sublist_split 0 hi lo l) in Hs by lia.
  apply sorted_le_app_r in Hs. exact Hs.
Qed.

Lemma sublist_peel_hd : forall (l : list Z) k n,
  0 <= k -> k < n -> n <= Zlength l ->
  sublist k n l = Znth k l 0 :: sublist (k + 1) n l.
Proof.
  intros l k n Hk Hkn Hn.
  rewrite (sublist_split k n (k + 1) l) by lia.
  (* [d] is an EXPLICIT section argument of listlib Length.v, and
     [sublist_single] mentions it (in [Znth n l d]) so section discharge
     prepends it -- unlike [sublist_split], whose statement does not. *)
  rewrite (sublist_single 0 k l) by lia. reflexivity.
Qed.

Lemma all_ge_head : forall lst l k n,
  0 <= k -> k < n -> n <= Zlength l ->
  all_ge lst (sublist k n l) -> lst <= Znth k l 0.
Proof.
  intros lst l k n Hk Hkn Hn H. unfold all_ge in H.
  rewrite sublist_peel_hd in H by lia. inversion H; assumption.
Qed.

Lemma all_ge_tail : forall lst l k n,
  0 <= k -> k < n -> n <= Zlength l ->
  all_ge lst (sublist k n l) -> all_ge lst (sublist (k + 1) n l).
Proof.
  intros lst l k n Hk Hkn Hn H. unfold all_ge in H.
  rewrite sublist_peel_hd in H by lia. inversion H; assumption.
Qed.

Lemma all_ge_of_sorted : forall l k n,
  sorted_le l -> 0 <= k -> k < n -> n <= Zlength l ->
  all_ge (Znth k l 0) (sublist (k + 1) n l).
Proof.
  intros l k n Hs Hk Hkn Hn.
  assert (Hsub : sorted_le (sublist k n l)) by (apply sorted_le_sublist; auto; lia).
  rewrite sublist_peel_hd in Hsub by lia.
  simpl in Hsub. destruct Hsub as [Hall _]. unfold all_ge. exact Hall.
Qed.

Lemma sublist_tail_of : forall (l : list Z) q n hd tl,
  0 <= q -> q < n -> n <= Zlength l ->
  sublist q n l = hd :: tl -> tl = sublist (q + 1) n l.
Proof.
  intros l q n hd tl Hq Hqn Hn Heq.
  rewrite sublist_peel_hd in Heq by lia. inversion Heq. reflexivity.
Qed.


Lemma Znth_buffer_eq_src : forall kept tail src q n k,
  Zlength kept = q -> tail = sublist q n src ->
  0 <= q -> q <= k -> k < n -> n <= Zlength src ->
  Znth k (kept ++ tail) 0 = Znth k src 0.
Proof.
  intros kept tail src q n k Hq Ht Hq0 Hqk Hkn Hn.
  rewrite app_Znth2 by lia. rewrite Hq, Ht.
  rewrite (Znth_sublist 0 q (k - q) n src) by lia.
  f_equal. lia.
Qed.

Lemma dedup_keep_bound : forall kept tail src q n k lst,
  Zlength kept = q -> tail = sublist q n src ->
  0 <= q -> q <= k -> k < n -> n <= Zlength src ->
  all_ge lst (sublist k n src) ->
  Znth k (kept ++ tail) 0 <> lst ->
  lst < Znth k (kept ++ tail) 0.
Proof.
  intros kept tail src q n k lst Hq Ht Hq0 Hqk Hkn Hn Hge Hne.
  rewrite (Znth_buffer_eq_src kept tail src q n k) by assumption.
  rewrite (Znth_buffer_eq_src kept tail src q n k) in Hne by assumption.
  pose proof (all_ge_head lst src k n ltac:(lia) Hkn Hn Hge). lia.
Qed.

Lemma dedup_keep_all_ge : forall kept tail src q n k,
  Zlength kept = q -> tail = sublist q n src -> sorted_le src ->
  0 <= q -> q <= k -> k < n -> n <= Zlength src ->
  all_ge (Znth k (kept ++ tail) 0) (sublist (k + 1) n src).
Proof.
  intros kept tail src q n k Hq Ht Hs Hq0 Hqk Hkn Hn.
  rewrite (Znth_buffer_eq_src kept tail src q n k) by assumption.
  apply all_ge_of_sorted; [ exact Hs | lia | lia | lia ].
Qed.


Lemma Permutation_Zlength_Z : forall (l1 l2 : list Z),
  Permutation l1 l2 -> Zlength l1 = Zlength l2.
Proof.
  intros l1 l2 H. rewrite !Zlength_correct.
  f_equal. apply Permutation_length, H.
Qed.


Lemma keep_forall : forall (P : Z -> Prop) kept junk tl x,
  Forall P (kept ++ junk :: tl) -> P x -> Forall P (kept ++ x :: tl).
Proof.
  intros P kept junk tl x H Hx.
  apply Forall_app in H. destruct H as [Hk Ht].
  inversion Ht; subst.
  apply Forall_app; split; [ exact Hk | constructor; assumption ].
Qed.

Lemma keep_all_from : forall input kept junk tl x,
  all_from input (kept ++ junk :: tl) -> In x input ->
  all_from input (kept ++ x :: tl).
Proof.
  intros input kept junk tl x H Hx. unfold all_from in *.
  eapply keep_forall; eassumption.
Qed.


Lemma msolver_inv_addclause_finish : forall n F A_arr A_inst M words,
  msolver_inv n F A_arr A_inst M ->
  msolver_inv n F A_arr A_inst (msolver_addclause_finish M words).
Proof.
  intros n F A_arr A_inst M words H.
  destruct H as [Hw Hpl Hwf Hhc Hrc].
  constructor; try assumption.
  destruct Hw; constructor; try assumption.
  apply solver_shape_addclause_finish; assumption.
Qed.


Lemma stats_rep_addclause_fold : forall s st words,
  Zlength st = 11 ->
  &( s # "solver_t" ->ₛ "stats" .ₛ "starts")           # UInt64 |-> stats_starts st **
  &( s # "solver_t" ->ₛ "stats" .ₛ "decisions")        # UInt64 |-> stats_decisions st **
  &( s # "solver_t" ->ₛ "stats" .ₛ "propagations")     # UInt64 |-> stats_propagations st **
  &( s # "solver_t" ->ₛ "stats" .ₛ "inspects")         # UInt64 |-> stats_inspects st **
  &( s # "solver_t" ->ₛ "stats" .ₛ "conflicts")        # UInt64 |-> stats_conflicts st **
  &( s # "solver_t" ->ₛ "stats" .ₛ "clauses")
    # UInt64 |-> MiniSatTarget.lo64 (stats_clauses st + 1) **
  &( s # "solver_t" ->ₛ "stats" .ₛ "clauses_literals")
    # UInt64 |-> MiniSatTarget.lo64 (stats_clauses_literals st + Zlength words) **
  &( s # "solver_t" ->ₛ "stats" .ₛ "learnts")          # UInt64 |-> stats_learnts st **
  &( s # "solver_t" ->ₛ "stats" .ₛ "learnts_literals") # UInt64 |-> stats_learnts_literals st **
  &( s # "solver_t" ->ₛ "stats" .ₛ "max_literals")     # UInt64 |-> stats_max_literals st **
  &( s # "solver_t" ->ₛ "stats" .ₛ "tot_literals")     # UInt64 |-> stats_tot_literals st
  |-- stats_rep &( s # "solver_t" ->ₛ "stats")
        (addclause_stats_update words st).
Proof.
  intros s st words H11.
  set (sp := &( s # "solver_t" ->ₛ "stats")).
  stats_dot_bridge s sp.
  unfold stats_rep, addclause_stats_update, stats_set_clauses, stats_set_clauses_literals.
  unfold stats_starts, stats_decisions, stats_propagations,
    stats_inspects, stats_conflicts, stats_clauses, stats_clauses_literals,
    stats_learnts, stats_learnts_literals, stats_max_literals, stats_tot_literals.
  rewrite (Znth_replace_Znth_Same 0) by (rewrite ?Zlength_replace_Znth; lia).
  rewrite !(Znth_replace_Znth_Diff 0) by (rewrite ?Zlength_replace_Znth; lia).
  rewrite (Znth_replace_Znth_Same 0) by (rewrite ?Zlength_replace_Znth; lia).
  rewrite !(Znth_replace_Znth_Diff 0) by (rewrite ?Zlength_replace_Znth; lia).
  msat_entailer_with ltac:(rewrite ?Zlength_replace_Znth; lia).
Qed.


Lemma ulnb64_lo64 : forall x, unsigned_last_nbits x 64 = MiniSatTarget.lo64 x.
Proof. intros x. unfold MiniSatTarget.lo64, MiniSatTarget.two64,
                       unsigned_last_nbits. reflexivity. Qed.

(* The engine truncates the pointer difference before adding it, the model does
   not.  No range reasoning is needed to reconcile them: [lo64] is [mod 2^64],
   and mod absorbs an inner mod on either summand. *)
Lemma lo64_add_idem : forall a b,
  MiniSatTarget.lo64 (a + MiniSatTarget.lo64 b) = MiniSatTarget.lo64 (a + b).
Proof.
  intros a b. unfold MiniSatTarget.lo64. apply Zplus_mod_idemp_r.
Qed.

(* ---- unit-arm support: db and F growth, root vacuity, assigns_one ---- *)
Lemma db_matches_cnf_app_r : forall (F G : cnf) M,
  db_matches_cnf F M -> db_matches_cnf (F ++ G) M.
Proof.
  intros F G M H. unfold db_matches_cnf in *.
  rewrite List.Forall_forall in H |- *.
  intros c Hc. destruct (H c Hc) as [c0 [Hin Hperm]].
  exists c0. split; [apply in_or_app; left; exact Hin | exact Hperm].
Qed.

Lemma db_implied_app_r : forall (F G : cnf) M,
  db_implied F M -> db_implied (F ++ G) M.
Proof.
  intros F G M H. unfold db_implied in *.
  rewrite List.Forall_forall in H |- *.
  intros c Hc. apply entails_clause_app_r. exact (H c Hc).
Qed.

Lemma current_reasonless_earliest_no_levels : forall n M,
  Zlength (mt_lim (ms_core M)) = 0 ->
  0 <= ms_root_level M ->
  current_reasonless_earliest n M.
Proof.
  intros n M Hlim Hroot d Hd. exfalso. rewrite Hlim in Hd. lia.
Qed.

Lemma assigns_one_enqueue_fresh_null : forall n F A_arr A_inst M l c,
  msolver_inv_weak n F A_arr A_inst M ->
  lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  assigns_one (msolver_view n M)
    (msolver_view n (msolver_enqueue_fresh M l c None))
    (lit_var_c l) (lit_pol l) (Zlength (mt_lim (ms_core M))) None.
Proof.
  intros n F A_arr A_inst M l c Hinv Hl Hfresh.
  unfold msolver_view, msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update, msolver_db.
  cbn [ms_core ms_reason_of ms_prob ms_learnt].
  eapply view_of_assign.
  - exact (msw_trail_wf Hinv).
  - exact Hl.
  - exact Hfresh.
  - intros y Hy. apply sat_function_update_neq.
    intro Heq. apply Hy. symmetry. exact Heq.
  - apply sat_function_update_eq.
  - intros C k HC Hk. discriminate HC.
Qed.

(* The unit clause never enters the database, so [root_satisfied] is the ONLY available disjunct of
   [db_complete], and [root_satisfied] demands level 0.  This is the field that
   forces the decision-level-0 precondition. *)
Lemma db_complete_unit_enqueue : forall n F A_arr A_inst M l c reason,
  msolver_inv_weak n F A_arr A_inst M ->
  lit_wf_c n l ->
  Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
  Zlength (mt_lim (ms_core M)) = 0 ->
  db_complete (F ++ ((lit_denote l :: nil) :: nil))
              (msolver_enqueue_fresh M l c reason).
Proof.
  intros n F A_arr A_inst M l c reason Hinv Hl Hfresh Hlim0 C HC.
  apply in_app_or in HC. destruct HC as [Hold | Hnew].
  - exact (db_complete_enqueue_fresh__record
             n F A_arr A_inst M l c reason Hinv Hl Hfresh C Hold).
  - destruct Hnew as [Heq | Hbad]; [subst C | destruct Hbad].
    right.
    unfold msolver_enqueue_fresh, msolver_propagation_overlay, msolver_propagation_update.
    cbn [ms_core].
    pose proof (lit_var_c_in_range n l Hl) as Hrange.
    pose proof (msw_trail_wf Hinv) as Htwf.
    pose proof (mtw_assigns_len Htwf) as Halen.
    pose proof (mtw_levels_len Htwf) as Hllen.
    exists (lit_denote l).
    split; [left; reflexivity |].
    split.
    + unfold eval_partial_literal.
      rewrite lit_var_c_denote.
      rewrite mt_pv_nonneg by lia.
      unfold mt_enqueue, mt_push. cbn [mt_assigns].
      rewrite Znth_replace_Znth_Same by lia.
      rewrite lbool_val_lit_sig.
      unfold lit_denote, lit_pol. destruct (Z.odd l); reflexivity.
    + rewrite lit_var_c_denote.
      unfold mt_enqueue, mt_push. cbn [mt_levels].
      rewrite Znth_replace_Znth_Same by lia.
      exact Hlim0.
Qed.

Lemma msolver_inv_addclause_unit_enqueue :
  forall n F A_arr A_inst M l,
    msolver_inv n F A_arr A_inst M ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    Zlength (mt_lim (ms_core M)) = 0 ->
    ms_qtail M < ms_cap M ->
    ms_capacity_root_propagation_pending M = 0 ->
    msolver_inv n (F ++ ((lit_denote l :: nil) :: nil)) A_arr A_inst
      (msolver_enqueue_fresh M l 0 None).
Proof.
  intros n F A_arr A_inst M l Hinv Hl Hfresh Hlim0 Hroom Hpend.
  pose proof (msi_weak Hinv) as Hweak.
  pose proof (msw_trail_wf Hweak) as Htrailwf.
  pose proof (msw_shape Hweak) as Hshape.
  pose proof (msw_root_range Hweak) as Hrr.
  pose proof (assigns_one_enqueue_fresh_null n F A_arr A_inst M l 0
                Hweak Hl Hfresh) as Hassign.
  assert (Hshape' : solver_shape (msolver_enqueue_fresh M l 0 None)).
  { eapply solver_shape_enqueue_fresh__record;
      [exact Hshape|exact Hroom|exact Hpend]. }
  assert (Htrailimpl : trail_implied (F ++ ((lit_denote l :: nil) :: nil))
                          (mt_enqueue (ms_core M) l)).
  { eapply trail_implied_unit with (rc := (lit_denote l :: nil)).
    - exact Htrailwf.
    - apply trail_implied_app_r. exact (msw_trail_impl Hweak).
    - apply entails_clause_in. apply in_or_app. right. left. reflexivity.
    - left. reflexivity.
    - intros k Hk Hne. destruct Hk as [Hk|[]]. subst. contradiction. }
  assert (Hweak' : msolver_inv_weak n (F ++ ((lit_denote l :: nil) :: nil))
                     A_arr A_inst (msolver_enqueue_fresh M l 0 None)).
  { constructor.
    - cbn. exact (msw_size Hweak).
    - exact (msw_n_range Hweak).
    - exact Hshape'.
    - apply cnf_wf_app_one; [exact (msw_F_wf Hweak)|].
      constructor; [apply lit_denote_wf; exact Hl | constructor].
    - exact (msw_A_wf Hweak).
    - cbn. eapply mtrail_wf_enqueue; [exact Htrailwf|exact Hl|exact Hfresh].
    - cbn. exact (msw_level_bound Hweak).
    - cbn. exact (msw_root_range Hweak).
    - cbn. rewrite (decisions_upto_enqueue n (ms_core M) l) by exact Htrailwf.
      exact (msw_assumptions Hweak).
    - exact (msw_assump_incl Hweak).
    - cbn. rewrite List.Forall_forall. intros a Ha.
      pose proof (msw_assump_sat Hweak) as Hassump.
      rewrite List.Forall_forall in Hassump.
      eapply assump_true_at_root_enqueue__record;
        [exact Htrailwf|exact Hl|exact Hfresh|exact (Hassump a Ha)].
    - eapply stable_view_assigns_one__record.
      + exact (msw_stable Hweak).
      + exact Hassign.
      + reflexivity.
      + split; [apply Zlength_nonneg|reflexivity].
      + left. reflexivity.
    - eapply reasons_entailed_assigns_one__record.
      + exact Hassign.
      + apply reasons_entailed_app_r. exact (msw_reasons_ent Hweak).
      + left. reflexivity.
    - eapply reasons_var_injective_assigns_one__record;
        [exact Hassign|exact (msw_reasons_inj Hweak)|left; reflexivity].
    - cbn. exact Htrailimpl.
    - cbn. exact (msw_db_wf Hweak).
    - cbn. apply db_matches_cnf_app_r. exact (msw_db_matches Hweak).
    - cbn. apply db_implied_app_r. exact (msw_db_implied Hweak).
    - eapply db_complete_unit_enqueue;
        [exact Hweak|exact Hl|exact Hfresh|exact Hlim0].
    - cbn. exact (msw_learnt_db Hweak).
    - cbn. exact (msw_prob_db Hweak).
    - cbn. exact (msw_binary_out Hweak).
    - eapply reasons_match_enqueue_fresh__record;
        [exact Hweak|exact Hl|exact Hfresh|left; split; reflexivity].
    - eapply reason_head_ok_enqueue_fresh__record;
        [exact Hweak|exact Hl|left; reflexivity].
    - eapply binary_reason_same_level_enqueue_fresh__record;
        [exact Hweak|exact Hl|exact Hfresh|left; reflexivity].
    - cbn. exact (msw_wmap_exact Hweak).
    - cbn. exact (msw_tags_clear Hweak).
    - cbn. exact (msw_heap_wf Hweak).
    - cbn. exact (msw_cla_inc_nonnegative Hweak).
    - cbn. exact (msw_seed Hweak). }
  constructor.
  - exact Hweak'.
  - cbn. apply prop_level_enqueue. exact (msi_prop_level Hinv).
  - cbn. eapply minisat_watch_frontier_enqueue_nodrain;
      [exact Htrailwf|exact Hl|exact Hfresh|exact (msi_watch_frontier Hinv)].
  - cbn. eapply heap_covers_enqueue_fresh__record;
      [exact Htrailwf|exact Hl|exact (msi_heap_covers Hinv)].
  - apply current_reasonless_earliest_no_levels.
    + cbn. unfold mt_enqueue, mt_push. cbn [mt_lim]. exact Hlim0.
    + cbn. lia.
Qed.

Lemma singleton_of_Zlength_one : forall (l : list Z),
  Zlength l = 1 -> l = Znth 0 l 0 :: nil.
Proof.
  intros [|a [|b r]] H.
  - rewrite Zlength_nil in H. lia.
  - reflexivity.
  - rewrite !Zlength_cons in H.
    pose proof (Zlength_nonneg r). lia.
Qed.

Definition addclause_stats_open_frame_wl_at
    (s : Z) (M : msolver) (wl lvl : Z) : Assertion :=
  “ solver_shape M ” &&
  ((EX act asg opos rsn trl tgs : Z,
      solver_nonlevel_rep_nostats_at s M wl act asg opos rsn trl tgs) **
   solver_levels_slice_at s M lvl).

Definition solver_assigns_focus_frame_wl_at
    (s : Z) (M : msolver) (wl lvl : Z) : Assertion :=
  solver_without_assigns_frame_wl_at
    s M wl lvl (solver_scalars_rep s M) (solver_vecs_rep s M).

Lemma solver_rep_growable_of_wl : forall s M wl lvl,
  solver_rep_levels_wl_at s M wl lvl **
  solver_wlists_tail wl (2 * ms_size M) (2 * ms_cap M)
  |-- solver_rep_growable s M.
Proof.
  intros s M wl lvl. unfold solver_rep_levels_wl_at, solver_rep_growable,
    solver_rep_at.
  Intros. Intros act asg opos rsn trl tgs.
  Exists wl act asg opos rsn lvl trl tgs. msat_entailer_with lia.
Qed.


Lemma solver_rep_growable_to_wl : forall s M,
  solver_rep_growable s M
  |-- EX wl : Z, EX lvl : Z, solver_rep_levels_wl_at s M wl lvl **
      solver_wlists_tail wl (2 * ms_size M) (2 * ms_cap M).
Proof.
  intros s M. unfold solver_rep_levels_wl_at, solver_rep_growable, solver_rep_at.
  Intros wl act asg opos rsn lvl trl tgs.
  Exists wl lvl. cancel.
  Exists act asg opos rsn trl tgs. msat_entailer_with lia.
Qed.


Lemma addclause_stats_close_wl_finish : forall s M words wl lvl,
  solver_shape M ->
  addclause_stats_open_frame_wl_at s M wl lvl **
  stats_rep &( s # "solver_t" ->ₛ "stats")
            (addclause_stats_update words (ms_stats M))
  |-- solver_rep_levels_wl_at s (msolver_addclause_finish M words) wl lvl.
Proof.
  intros s M words wl lvl Hsh.
  pose proof (solver_shape_addclause_finish M words Hsh) as Hsh'.
  unfold solver_rep_levels_wl_at, addclause_stats_open_frame_wl_at.
  rewrite addclause_finish_levels.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]). Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  rewrite addclause_finish_nonlevel_at.
  unfold solver_nonlevel_rep_nostats_at.
  msat_entailer_with lia.
Qed.

Lemma addclause_stats_open_wl_noshape : forall s M wl lvl,
  solver_rep_levels_wl_at s M wl lvl
  |-- addclause_stats_open_frame_wl_at s M wl lvl **
      stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).
Proof.
  intros s M wl lvl.
  unfold solver_rep_levels_wl_at, addclause_stats_open_frame_wl_at,
         solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  Intros. Intros act asg opos rsn trl tgs.
  cancel. Exists act asg opos rsn trl tgs. msat_entailer_with lia.
Qed.

Lemma solver_assigns_focus_close_levels_wl : forall s M asg wl lvl,
  &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
  CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
  solver_char_tail asg (ms_size M) (ms_cap M) **
  solver_assigns_focus_frame_wl_at s M wl lvl
  |-- solver_rep_levels_wl_at s M wl lvl.
Proof.
  intros s M asg wl lvl.
  unfold solver_rep_levels_wl_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
  solver_assigns_focus_frame_wl_at, solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
  Intros act opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  msat_entailer_with lia.
Qed.

Lemma solver_assigns_focus_open_wl : forall s M wl lvl,
  solver_rep_levels_wl_at s M wl lvl
  |-- EX asg : Z,
      &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
      CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
      solver_char_tail asg (ms_size M) (ms_cap M) **
      solver_assigns_focus_frame_wl_at s M wl lvl.
Proof.
  intros s M wl lvl.
  unfold solver_rep_levels_wl_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
  solver_assigns_focus_frame_wl_at, solver_without_assigns_frame_wl_at, solver_without_assigns_cells_at.
  Intros act asg opos rsn trl tgs.
  Exists asg. Exists act opos rsn trl tgs.
  msat_entailer_with lia.
Qed.

Lemma solver_rep_growable_focus_open_wl : forall s M,
  solver_rep_growable s M |-- EX asg : Z, EX lvl : Z, EX wl : Z,
    &( s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
    CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
    solver_char_tail asg (ms_size M) (ms_cap M) **
    solver_assigns_focus_frame_wl_at s M wl lvl **
    solver_wlists_tail wl (2 * ms_size M) (2 * ms_cap M).
Proof.
  intros s M. sep_apply solver_rep_growable_to_wl. Intros wl lvl.
  sep_apply solver_assigns_focus_open_wl. Intros asg.
  Exists asg lvl wl. msat_entailer_with lia.
Qed.


Lemma solver_analyze_frame_stats_len : forall s M wl,
  solver_analyze_frame s M wl |-- “ Zlength (ms_stats M) = 11 ”.
Proof.
  intros s M wl.
  unfold solver_analyze_frame, solver_analyze_frame_cells, stats_analyze_frame.
  Intros asg. msat_entailer_with ltac:(lia).
Qed.


(** The CLOSE direction of [solver_rep_reasons_simplify_open]:
    the simplify compaction exit re-assembles the reasons/levels view from the
    database it just rewrote. *)
Lemma solver_rep_reasons_simplify_close_0__simplify :
  forall s M reasons lvl wl asg,
  mt_lim (ms_core M) = (@nil Z) ->
  solver_shape M ->
  Vecp.rep (solver_selected_vec s 0)
    (db_words (solver_selected_db 0 M)) **
  clause_db_rep (solver_selected_db 0 M) **
  &(s # "solver_t" ->ₛ "assigns") # Ptr |-> asg **
  CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
  Veci.rep &(s # "solver_t" ->ₛ "trail_lim") (@nil Z) **
  solver_simplify_db_rest_at s 0 M reasons lvl wl asg
  |-- solver_rep_reasons_levels_wl_at s M reasons lvl wl.
Proof.
  intros s M reasons lvl wl asg Hlim Hshape.
  unfold solver_rep_reasons_levels_wl_at.
  unfold solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_simplify_db_rest_at,
  solver_simplify_clause_frame_at,
    solver_selected_vec, solver_selected_db,
    solver_other_db_vec_rep, solver_other_clause_db_rep,
    solver_wlists_handle, solver_scalars_rep, clause_new_scalars_frame,
    solver_vecs_rep, solver_trail_array_rep, solver_levels_slice_at,
    db_words.
  Intros act opos trl tgs.
  Exists act asg opos trl tgs.
  cbn. rewrite Hlim. msat_entailer_with lia.
Qed.

(** ===== group: generic list and address facts ===== *)


Lemma msat_map_lit_var_c_in_range : forall (n : Z) (l : list Z),
  Forall (lit_wf_c n) l ->
  forall x, In x (map lit_var_c l) -> 0 <= x < n.
Proof.
  intros n l Hwf x Hx. apply in_map_iff in Hx.
  destruct Hx as [y [<- Hy]].
  apply (lit_var_c_in_range n y).
  rewrite Forall_forall in Hwf. exact (Hwf y Hy).
Qed.

Lemma msat_map_lit_var_c_snoc_in_range :
  forall (n : Z) (l : list Z) (a : Z),
  Forall (lit_wf_c n) l -> 0 <= a < n ->
  forall x, In x (map lit_var_c l ++ a :: nil) -> 0 <= x < n.
Proof.
  intros n l a Hwf Ha x Hx. apply in_app_or in Hx.
  destruct Hx as [Hx | [Hx | []]].
  - exact (msat_map_lit_var_c_in_range n l Hwf x Hx).
  - subst x. exact Ha.
Qed.

Lemma msat_cons_list_var_bounded :
  forall (n a : Z) (l : list Z),
  0 <= a < n -> Forall (fun v => 0 <= v < n) l ->
  forall x, In x (a :: l) -> 0 <= x < n.
Proof.
  intros n a l Ha Hl x [<- | Hin]; [exact Ha|].
  rewrite Forall_forall in Hl. exact (Hl x Hin).
Qed.

Lemma msat_binary_watch_write_after :
  forall (dst : Z) (copied memory : list Z) (default k : Z),
  0 <= dst ->
  dst + Zlength copied <= k ->
  k < Zlength memory ->
  Znth k (binary_watch_write dst copied memory) default =
  Znth k memory default.
Proof.
  intros dst copied. revert dst.
  induction copied as [|a copied IH];
    intros dst memory default k Hdst Hafter Hk.
  - simpl. reflexivity.
  - simpl. rewrite Zlength_cons in Hafter.
    replace (Z.succ (Zlength copied)) with
      (1 + Zlength copied) in Hafter by lia.
    rewrite IH by (try rewrite Zlength_replace_Znth; lia).
    pose proof (Zlength_nonneg copied) as Hcopied_nonneg.
    rewrite Znth_replace_Znth_Diff by
      (try rewrite Zlength_replace_Znth; lia).
    reflexivity.
Qed.

Lemma msat_binary_watch_write_snoc :
  forall (dst : Z) (copied : list Z) (x : Z) (memory : list Z),
  binary_watch_write dst (copied ++ x :: nil) memory =
  replace_Znth (dst + Zlength copied) x
    (binary_watch_write dst copied memory).
Proof.
  intros dst copied. revert dst.
  induction copied as [|a copied IH]; intros dst x memory.
  - simpl. rewrite Zlength_nil. replace (dst + 0) with dst by lia.
    reflexivity.
  - simpl. rewrite IH, Zlength_cons.
    replace (Z.succ (Zlength copied)) with (1 + Zlength copied) by lia.
    replace (dst + 1 + Zlength copied)
      with (dst + (1 + Zlength copied)) by lia.
    reflexivity.
Qed.

Lemma msat_ptrarray_seg_split_middle :
  forall (x lo hi : Z) (pre : list Z) (current : Z) (suffix : list Z),
  hi = lo + Zlength pre + 1 + Zlength suffix ->
  PtrArray.seg x lo hi (pre ++ current :: suffix) |--
    PtrArray.seg x lo (lo + Zlength pre) pre **
    PtrArray.seg x (lo + Zlength pre) (lo + Zlength pre + 1)
      (current :: nil) **
    PtrArray.seg x (lo + Zlength pre + 1) hi suffix.
Proof.
  intros x lo hi pre. revert x lo hi.
  induction pre as [|a pre IH]; intros x lo hi current suffix Hhi.
  - simpl in Hhi. subst hi.
    simpl.
    rewrite !Zlength_nil.
    replace (lo + 0) with lo by lia.
    replace (lo + 0 + 1) with (lo + 1) by lia.
    PtrArray.ArraySimplify.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - rewrite Zlength_cons in Hhi. subst hi. simpl.
    PtrArray.ArraySimplify.
    replace (lo + Z.succ (Zlength pre) + 1 + Zlength suffix) with
      (lo + 1 + Zlength pre + 1 + Zlength suffix) by lia.
    sep_apply (IH x (lo + 1)
      (lo + 1 + Zlength pre + 1 + Zlength suffix)
      current suffix ltac:(lia)).
    rewrite Zlength_cons.
    replace (lo + Z.succ (Zlength pre)) with
      (lo + 1 + Zlength pre) by lia.
    replace (lo + Z.succ (Zlength pre) + 1) with
      (lo + 1 + Zlength pre + 1) by lia.
    PtrArray.ArraySimplify.
    msat_entailer_with ltac:(lia).
Qed.

Lemma msat_stats_rep_open_decisions : forall (p : Z) (st : list Z),
  stats_rep p st |--
    stats_without_decisions_rep p st **
    &(p # "stats_t" ->ₛ "decisions") # UInt64 |-> stats_decisions st.
Proof.
  intros p st. unfold stats_rep, stats_without_decisions_rep.
  msat_entailer_with ltac:(lia).
Qed.

Lemma msat_stats_rep_open_analyze : forall (p : Z) (st : list Z),
  stats_rep p st |--
    stats_analyze_frame p st **
    &(p # "stats_t" ->ₛ "max_literals") # UInt64 |-> stats_max_literals st **
    &(p # "stats_t" ->ₛ "tot_literals") # UInt64 |-> stats_tot_literals st.
Proof.
  intros p st. unfold stats_rep, stats_analyze_frame.
  msat_entailer_with ltac:(lia).
Qed.

Lemma msat_stats_analyze_frame_close :
  forall (p : Z) (st : list Z) (Q : Assertion),
  (&(p # "stats_t" ->ₛ "max_literals") # UInt64 |-> stats_max_literals st **
   &(p # "stats_t" ->ₛ "tot_literals") # UInt64 |-> stats_tot_literals st **
   Q ** stats_analyze_frame p st) |-- Q ** stats_rep p st.
Proof.
  intros p st Q. unfold stats_analyze_frame, stats_rep.
  msat_entailer_with ltac:(lia).
Qed.

(* A non-empty character segment owns storage, so its base address is a valid,
   hence non-negative, pointer. *)
Lemma msat_chararray_seg_base_nonneg :
  forall (x n : Z) (l : list Z),
  0 < n -> CharArray.seg x 0 n l |-- “ 0 <= x ”.
Proof.
  intros x n l Hn.
  prop_apply (CharArray.seg_Zlength x 0 n l).
  Intros.
  destruct l as [|a l].
  - simpl in *.
    unfold CharArray.seg.
    simpl.
    entailer_with ltac:(lia).
  - unfold CharArray.seg.
    simpl.
    sep_apply (valid_store_char (x + 0) a).
    entailer_with ltac:(lia).
    unfold valid_object, Arch.valid_object, Arch.valid_addr_range in *.
    fold addr_max_unsigned in *. simpl_nonptr_sizeof.
    lia.
Qed.

(* Anything stored in an int cell is a representable signed 32-bit value. *)
Lemma msat_int_cell_le_max_signed : forall (p v : Z),
  p # Int |-> v |-- “ v <= Int.max_signed ”.
Proof.
  intros p v.
  prop_apply (valid_store_int p).
  Intros.
  msat_entailer_with ltac:(lia).
Qed.

(* The clause-database representation depends on the entry list only up to
   permutation. *)
Lemma msat_clause_db_rep_perm : forall (d1 d2 : dbmap),
  Permutation d1 d2 -> clause_db_rep d1 |-- clause_db_rep d2.
Proof.
  intros d1 d2 Hperm. induction Hperm as
    [|x d1 d2 Hperm IH|x y d|d1 d2 d3 H12 H23 IH12 IH23].
  - simpl. cancel.
  - simpl. sep_apply IH; cancel.
  - simpl. cancel.
  - sep_apply_r_atomic IH23. exact H23.
Qed.

Lemma msat_clause_fields_to_rep :
  forall (n : Z) (db : dbmap) (c : Z) (co : clause_obj)
         (lits : list Z) (activity : fp32),
  db_wf n db ->
  In (c, co) db ->
  co_lits co = lits ->
  co_learnt co = msat_true ->
  msat_fp32_nonnegative activity ->
  (clause_hdr_addr c # Int |-> clause_hdr_word msat_true (Zlength lits) **
   clause_act_addr c (Zlength lits) # Float |-> activity **
   IntArray.seg (clause_lits_addr c) 0 (Zlength lits) lits)
  |-- MiniSatClause.rep c (co_learnt co) (co_lits co).
Proof.
  intros n db c co lits activity Hwf Hin Hlits Hlearnt Hactivity.
  rewrite Hlits, Hlearnt.
  unfold msat_true.
  unfold MiniSatClause.rep, activity_state.
  Exists activity.
  pose proof (db_wf_ptr_pos n db c co Hwf Hin) as Hpos.
  pose proof (db_wf_even n db c co Hwf Hin) as Heven.
  pose proof (Zlength_nonneg lits) as Hlen.
  pose proof (clause_ptr_mod2 c Heven) as Hmod.
  msat_entailer_with ltac:(lia).
Qed.


Lemma msat_msolver_view_level_cell : forall (n : Z) (M : msolver),
  mtrail_wf n (ms_core M) ->
  forall v d, level_of (msolver_view n M) v = Some d ->
    Znth v (mt_levels (ms_core M)) 0 = d.
Proof.
  intros n M Hwf v d Hlevel.
  cbn [msolver_view view_of level_of] in Hlevel.
  destruct (trail_pos (ms_core M) v) as [k|] eqn:Hpos; [|discriminate].
  injection Hlevel as <-.
  rewrite <- (trail_pos_var _ _ _ Hpos).
  apply (mtw_levels_agree Hwf).
  split; [lia|exact (trail_pos_bound _ _ _ Hpos)].
Qed.

Lemma msat_db_entry_swap_mem_cases :
  forall (db db' pre post : dbmap) (c : Z) (co co' : clause_obj),
  db = pre ++ (c, co) :: post ->
  db' = pre ++ (c, co') :: post ->
  forall q obj, In (q, obj) db' -> In (q, obj) db \/ (q, obj) = (c, co').
Proof.
  intros db db' pre post c co co' Hold Hnew q obj Hq. rewrite Hnew in Hq.
  destruct (in_app_or _ _ _ Hq) as [Hpre | Hcons].
  - left. rewrite Hold. apply in_or_app. left. exact Hpre.
  - destruct Hcons as [Heq | Hpost].
    + right. symmetry. exact Heq.
    + left. rewrite Hold. apply in_or_app. right. simpl. right.
      exact Hpost.
Qed.

Lemma msat_db_entry_swap_mem_fwd :
  forall (db db' pre post : dbmap) (c : Z) (co co' : clause_obj),
  db = pre ++ (c, co) :: post ->
  db' = pre ++ (c, co') :: post ->
  forall q obj, q <> c -> In (q, obj) db -> In (q, obj) db'.
Proof.
  intros db db' pre post c co co' Hold Hnew q obj Hne Hq.
  rewrite Hold in Hq. rewrite Hnew.
  destruct (in_app_or _ _ _ Hq) as [Hpre | Hcons].
  - apply in_or_app. left. exact Hpre.
  - destruct Hcons as [Heq | Hpost].
    + inversion Heq. exfalso. apply Hne. auto.
    + apply in_or_app. right. simpl. right. exact Hpost.
Qed.

Lemma msat_db_entry_swap_mem_bwd :
  forall (db db' : dbmap) (c : Z) (co' : clause_obj),
  (forall q obj, In (q, obj) db' ->
     In (q, obj) db \/ (q, obj) = (c, co')) ->
  forall q obj, q <> c -> In (q, obj) db' -> In (q, obj) db.
Proof.
  intros db db' c co' Hcases q obj Hneq Hlookup.
  destruct (Hcases q obj Hlookup) as [Hin | Heq]; [exact Hin|].
  inversion Heq. exfalso. apply Hneq. assumption.
Qed.

Lemma msat_db_entry_swap_expected_watchers :
  forall (db db' pre post : dbmap) (c : Z) (co co' : clause_obj),
  db = pre ++ (c, co) :: post ->
  db' = pre ++ (c, co') :: post ->
  (forall l, Permutation (entry_watchers (c, co) l)
     (entry_watchers (c, co') l)) ->
  forall l, Permutation (expected_watchers db l) (expected_watchers db' l).
Proof.
  intros db db' pre post c co co' Hold Hnew Hentry l.
  rewrite Hold, Hnew.
  rewrite !expected_watchers_app.
  rewrite !expected_watchers_cons.
  apply Permutation_app_head. apply Permutation_app_tail. apply Hentry.
Qed.

Lemma msat_analyze_start_learnt_incl :
  forall (a : cdcl_view) (k : Z) (C : clause) (l : literal),
  In l (analyze_start_learnt a (sublist 0 k C)) -> In l C.
Proof.
  intros a k C l Hl. unfold analyze_start_learnt in Hl.
  apply filter_In in Hl. destruct Hl as [Hl _].
  unfold sublist in Hl. cbn in Hl.
  rewrite <- (firstn_skipn (Z.to_nat k) C).
  apply in_or_app. left. exact Hl.
Qed.

Lemma msat_cons_map_literal_var_bounded :
  forall (n : Z) (C L : clause) (lcur : literal),
  (forall l, In l C -> literal_wf n l) ->
  In lcur C ->
  (forall l, In l L -> In l C) ->
  forall u, In u (literal_var lcur :: map literal_var L) -> 0 <= u < n.
Proof.
  intros n C L lcur HwfC Hlcur HinLC u Hu. destruct Hu as [<-|Hu].
  - pose proof (HwfC lcur Hlcur) as Hw.
    unfold literal_wf, var_in_range in Hw. exact Hw.
  - apply in_map_iff in Hu. destruct Hu as [l [<- Hl]].
    pose proof (HwfC l (HinLC l Hl)) as Hw.
    unfold literal_wf, var_in_range in Hw. exact Hw.
Qed.

Lemma msat_reason_target_stack_var_range :
  forall (n : Z) (M : msolver) (stack : list Z),
  n = ms_size M ->
  (forall v, In v stack -> exists p C, reason_target_wf n M v p C) ->
  forall x, In x stack -> 0 <= x < n.
Proof.
  intros n M stack Hsize Htargets x Hin.
  destruct (Htargets x Hin) as [p0 [C0 Htarget]].
  unfold reason_target_wf in Htarget. rewrite Hsize. tauto.
Qed.

(** ===== group: remaining facts ===== *)

Lemma propagation_watch_scan_rest_head__propagate :
  forall source_words retained moved rest garbage watch_memory ii jj
         raw_prefix scan_current raw_suffix,
    propagation_watch_scan_physical
      source_words retained moved rest garbage watch_memory ii jj ->
    watch_memory = raw_prefix ++ scan_current :: raw_suffix ->
    Zlength raw_prefix = ii ->
    rest = scan_current :: raw_suffix.
Proof.
  intros source_words retained moved rest garbage watch_memory ii jj
    raw_prefix scan_current raw_suffix Hphys Hwatch Hpre.
  unfold propagation_watch_scan_physical in Hphys.
  destruct Hphys as [Hperm [Hmem [Hkept [Hkg Hlen]]]].
  assert (Hconcat : raw_prefix ++ scan_current :: raw_suffix =
      (retained ++ garbage) ++ rest).
  { rewrite <- Hwatch. rewrite Hmem. rewrite app_assoc. reflexivity. }
  apply app_eq_app in Hconcat as [[m [Hm Htail]]|[m [Hm Htail]]].
  - assert (HZ : Zlength m = 0).
    { rewrite Hm in Hpre. rewrite Zlength_app, Hkg in Hpre. lia. }
    destruct m as [|a m];
      [exact Htail
      | exfalso; rewrite Zlength_cons in HZ; pose proof (Zlength_nonneg m); lia].
  - assert (HZ : Zlength m = 0).
    { rewrite Hm in Hkg. rewrite Zlength_app, Hpre in Hkg. lia. }
    destruct m as [|a m];
      [symmetry; simpl in Htail; exact Htail
      | exfalso; rewrite Zlength_cons in HZ; pose proof (Zlength_nonneg m); lia].
Qed.

Lemma solver_propagation_weak_core_facts__propagate :
  forall n F A_arr K M,
    solver_propagation_weak n F A_arr K M ->
    n = ms_size M /\
    solver_shape M /\
    db_wf n (msolver_db M) /\
    wmap_exact n (msolver_db M) (ms_wm M) /\
    mtrail_wf n (ms_core M).
Proof.
  intros n F A_arr K M Hweak.
  unfold solver_propagation_weak in Hweak.
  destruct Hweak as [_ Hweak].
  destruct K as [A_inst | A_proc]; cbn in Hweak.
  - split; [exact (msw_size Hweak)|].
    split; [exact (msw_shape Hweak)|].
    split; [exact (msw_db_wf Hweak)|].
    split; [exact (msw_wmap_exact Hweak)|exact (msw_trail_wf Hweak)].
  - split; [exact (msa_size Hweak)|].
    split; [exact (msa_shape Hweak)|].
    split; [exact (msa_db_wf Hweak)|].
    split; [exact (msa_wmap_exact Hweak)|exact (msa_trail_wf Hweak)].
Qed.

Lemma propagation_scan_current_tag_facts__propagate :
  forall n F A_arr K Mscan p confl retained rest scan_current raw_suffix,
    solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ->
    rest = scan_current :: raw_suffix ->
    is_tag scan_current = msat_true ->
    n = ms_size Mscan /\
    db_wf n (msolver_db Mscan) /\
    lit_wf_c n (tag_lit scan_current).
Proof.
  intros n F A_arr K Mscan p confl retained rest scan_current raw_suffix
    Hsem Hrest Histag.
  unfold solver_propagation_scan_semantics in Hsem.
  destruct Hsem as [Hlive | Hconf].
  - destruct Hlive as [Hc [Hweak [Hlevel [Hheap [Hcov [Hearliest
      [Hlevelof [Hlitp [Hprocessed [Hfront Hfocus]]]]]]]]]].
    pose proof (solver_propagation_weak_core_facts__propagate n F A_arr K Mscan Hweak)
      as [Hnsize [Hshape [Hdb [Hwm Htrailwf]]]].
    unfold minisat_focus_scan_carrier in Hfocus.
    destruct Hfocus as [scanned Hfocus].
    destruct Hfocus as [pending Hfocus].
    destruct Hfocus as [Hcp [Hws [Hwp Hsafe]]].
    assert (HinPending : In scan_current (minisat_focus_words pending)).
    { rewrite Hwp, Hrest. simpl. auto. }
    unfold minisat_focus_words in HinPending.
    apply in_map_iff in HinPending as [c [Cs Hcin]].
    assert (HinTotalC : In c (minisat_focus_contributions (msolver_db Mscan) p)).
    { eapply Permutation_in; [exact Hcp|]. apply in_or_app. right. exact Hcin. }
    assert (HinTotal : In scan_current
        (minisat_focus_words (minisat_focus_contributions (msolver_db Mscan) p))).
    { unfold minisat_focus_words. apply in_map_iff. exists c.
      split; [exact Cs | exact HinTotalC]. }
    rewrite minisat_focus_words_expected in HinTotal.
    unfold lit_wf_c in Hlitp.
    destruct Hwm as [HwmLen HwmExact].
    assert (HinCell : In scan_current (Znth p (ms_wm Mscan) nil)).
    { eapply Permutation_in;
        [apply Permutation_sym; exact (HwmExact p Hlitp)|exact HinTotal]. }
    destruct (wmap_tag_witness n (msolver_db Mscan) (ms_wm Mscan)
      p scan_current Hdb (conj HwmLen HwmExact) Hlitp HinCell Histag)
      as [q [co [Hq [Hlen2 Hpermco]]]].
    pose proof (db_wf_obj n (msolver_db Mscan) q co Hdb Hq) as Hobj.
    assert (Hforall : Forall (lit_wf_c n)
      (cons (lit_neg_c p) (cons (tag_lit scan_current) nil))).
    { eapply Forall_of_perm; [exact Hpermco | exact (proj1 (proj2 Hobj))]. }
    inversion Hforall as [|l0 ls Hhead Htail0].
    inversion Htail0 as [|l1 ls1 Htag Hnil0].
    split; [exact Hnsize | split; [exact Hdb | exact Htag]].
  - destruct Hconf as [Hne [Hnil _]]. exfalso. rewrite Hrest in Hnil. discriminate.
Qed.

Lemma zremove_not_in : forall (x : Z) l, ~ In x l -> zremove x l = l.
Proof.
  intros x l Hnot. induction l as [|a l IH].
  - reflexivity.
  - unfold zremove in *. cbn.
    assert (Ha : Z.eqb a x = false).
    { apply Z.eqb_neq. intro Heq. apply Hnot. left. exact Heq. }
    rewrite Ha. cbn. rewrite IH.
    + reflexivity.
    + intro Hin. apply Hnot. right. exact Hin.
Qed.

Lemma zremove_split : forall (x : Z) l,
  NoDup l -> In x l ->
  exists before after,
    l = before ++ x :: after /\
    zremove x l = before ++ after.
Proof.
  intros x l Hnd Hin.
  destruct (in_split x l Hin) as (before & after & Hl).
  exists before, after. split; [exact Hl |].
  rewrite Hl in Hnd |- *.
  assert (Hnotbefore : ~ In x before).
  {
    intro Hxb.
    pose proof (NoDup_app_disjoint before (x :: after) x Hnd Hxb) as Hd.
    apply Hd. left. reflexivity.
  }
  assert (Hndtail : NoDup (x :: after)).
  { eapply NoDup_app_remove_l. exact Hnd. }
  inversion Hndtail as [|? ? Hnotafter _]; subst.
  pose proof (zremove_not_in x before Hnotbefore) as Hbefore.
  pose proof (zremove_not_in x after Hnotafter) as Hafter.
  unfold zremove in Hbefore, Hafter |- *.
  rewrite filter_app. cbn. rewrite Z.eqb_refl. cbn.
  rewrite Hbefore, Hafter. reflexivity.
Qed.

Lemma Permutation_rotate_snoc :
  forall (prefix tail : list Z) (z : Z),
    Permutation ((prefix ++ tail) ++ (z :: nil))
                ((prefix ++ (z :: nil)) ++ tail).
Proof.
  intros prefix tail z.
  rewrite <- !app_assoc.
  apply Permutation_app_head.
  apply Permutation_app_comm.
Qed.

(* Normalize a nested field address through its already-evaluated base.
   Instantiate [inner] with the field's structure and infer [p] from [eq_refl]. *)
Lemma msat_nested_field_addr_alias :
  forall (base : Z) (outer field inner sub : string) (p : Z),
    p = &( base # outer ->ₛ field ) ->
    &( &( base # outer ->ₛ field ) ->ₛ sub ) = &( p # inner ->ₛ sub ).
Proof.
  intros base outer field inner sub p Hp. subst p. csimpl. reflexivity.
Qed.

Lemma ms_analysis_core_equiv_view :
  forall (n : Z) (M M' : msolver),
    analysis_core_equiv M M' -> msolver_view n M = msolver_view n M'.
Proof.
  intros n M M' Heq. unfold analysis_core_equiv in Heq.
  unfold msolver_view, msolver_clauses, msolver_db. intuition congruence.
Qed.

Lemma ms_analyze_scan_inv_pack :
  forall {n : Z} {F : cnf} {A_arr : list literal}
         {K : solver_propagation_context} {M0 M : msolver} {focus : Z}
         {phase : analyze_resolution_phase} {C : clause} {j ind : Z}
         {S0 R0 : list Z} {learnt0 : clause} {x : Z} {S R : list Z}
         {learnt : clause} {words : list Z} {cnt : Z},
    analyze_clause_scan_inv n F A_arr K M0 M focus phase C j ind S0 R0 learnt0
      x S R learnt words cnt ->
    analysis_cancel_ready n F A_arr K M focus /\
    analysis_tags_exact n (ms_tags M) (ms_tagged M) /\
    Permutation (ms_tagged M) (analyze_tags S R learnt) /\
    cnt = Zlength S /\
    lits_denote (tl words) = learnt /\
    1 <= Zlength words.
Proof.
  intros * Hinv. unfold analyze_clause_scan_inv in Hinv. tauto.
Qed.

Lemma ms_analyze_scan_selected_pack :
  forall {n : Z} {F : cnf} {A_arr : list literal}
         {K : solver_propagation_context} {M0 M : msolver} {focus : Z}
         {phase : analyze_resolution_phase} {C : clause} {j ind : Z}
         {S0 R0 : list Z} {learnt0 : clause} {x : Z} {S R : list Z}
         {learnt : clause} {words : list Z} {cnt : Z},
    phase = AnalyzeSelected ->
    analyze_clause_scan_inv n F A_arr K M0 M focus phase C j ind S0 R0 learnt0
      x S R learnt words cnt ->
    In x S0 /\
    reason_valid (msolver_view n M0) x C /\
    S = resolve_S (msolver_view n M0) x (sublist 1 j C) S0 R0 learnt0 /\
    R = x :: R0 /\
    learnt = resolve_learnt (msolver_view n M0) (sublist 1 j C) S0 R0 learnt0.
Proof.
  intros * Hphase Hinv. unfold analyze_clause_scan_inv in Hinv.
  rewrite Hphase in Hinv. cbn in Hinv. tauto.
Qed.

Lemma ms_analyze_var_untagged :
  forall (n : Z) (tags tagged S R : list Z) (L : clause) (v : Z),
    analysis_tags_exact n tags tagged ->
    Permutation tagged (analyze_tags S R L) ->
    0 <= v < n -> Znth v tags 0 <> 1 ->
    ~ In v (analyze_tags S R L).
Proof.
  intros n tags tagged S R L v Hexact Hperm Hv Hfresh Hin.
  destruct Hexact as [_ [_ [_ [_ Hiff]]]].
  pose proof (Permutation_in v (Permutation_sym Hperm) Hin) as Hintag.
  apply (proj2 (Hiff v Hv)) in Hintag. lia.
Qed.

(* Tagging one fresh variable [v]: the tag word becomes 1 at [v] and [v] is
   appended to the tagged list.  [Znth v tags 0 <> 1] is the C-side branch
   condition that [v] was not tagged before, and it is what keeps the list
   duplicate-free. *)
Lemma ms_analysis_tags_exact_snoc :
  forall (n : Z) (tags tagged : list Z) (v : Z),
    analysis_tags_exact n tags tagged ->
    0 <= v < n ->
    Znth v tags 0 <> 1 ->
    analysis_tags_exact n (replace_Znth v 1 tags) (tagged ++ (v :: nil)).
Proof.
  intros n tags tagged v Htagsold Hv Hfresh.
  destruct Htagsold as [Hlen [Hnd [Hrange [Hcells Hiff]]]].
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - split.
    + apply NoDup_snoc; [exact Hnd|].
      intro Hin. apply (proj2 (Hiff v Hv)) in Hin. lia.
    + split.
      * apply Forall_app. split; [exact Hrange|].
        constructor; [lia|constructor].
      * split.
        -- apply Forall_replace_Znth; [exact Hcells|tauto].
        -- intros u Hu. destruct (Z.eq_dec u v) as [->|Hne].
           ++ rewrite Znth_replace_Znth_Same by (rewrite Hlen; exact Hu).
              split; intro; [apply in_or_app; right; simpl; tauto|reflexivity].
           ++ rewrite Znth_replace_Znth_Diff;
                [|rewrite Hlen; lia|rewrite Hlen; lia|congruence].
              rewrite in_app_iff. simpl. rewrite Hiff by exact Hu.
              split; intro Hin.
              ** left. exact Hin.
              ** destruct Hin as [Hin|Hin]; [exact Hin|].
                 destruct Hin as [Heq|[]]. exfalso. apply Hne. symmetry.
                 exact Heq.
Qed.

Lemma ms_analyze_tags_perm_snoc_s :
  forall (tagged S R : list Z) (L : clause) (v : Z),
    Permutation tagged (analyze_tags S R L) ->
    Permutation (tagged ++ (v :: nil)) (analyze_tags (S ++ (v :: nil)) R L).
Proof.
  intros tagged S R L v Hpermold.
  eapply Permutation_trans.
  - apply Permutation_app_tail. exact Hpermold.
  - unfold analyze_tags.
    change (Permutation ((S ++ R ++ map literal_var L) ++ (v :: nil))
      ((S ++ (v :: nil)) ++ R ++ map literal_var L)).
    replace (S ++ R ++ map literal_var L)
      with (S ++ (R ++ map literal_var L)) by (rewrite app_assoc; reflexivity).
    replace ((S ++ (v :: nil)) ++ R ++ map literal_var L)
      with (S ++ ((v :: nil) ++ (R ++ map literal_var L)))
      by (rewrite !app_assoc; reflexivity).
    pose proof (perm_shuffle (nil : list Z) S (R ++ map literal_var L)
      (v :: nil)) as Hp.
    cbn [app] in Hp. exact Hp.
Qed.

Lemma ms_analyze_sublist_snoc :
  forall (words : list Z) (C : clause) (lo j : Z),
    C = lits_denote words -> 0 <= lo -> lo <= j -> j < Zlength words ->
    sublist lo (j + 1) C = sublist lo j C ++ (lit_denote (Znth j words 0) :: nil).
Proof.
  intros words C lo j HC Hlo Hloj Hj.
  rewrite (sublist_split lo (j + 1) j C) by
    (try rewrite HC, lits_denote_length; lia).
  rewrite (sublist_single (lit_denote 0) j C) by
    (rewrite HC, lits_denote_length; lia).
  f_equal. rewrite HC. unfold lits_denote.
  rewrite (Znth_map Z literal lit_denote words j 0 (lit_denote 0))
    by (split; [lia|exact Hj]). reflexivity.
Qed.

Lemma ms_analyze_tag_step_seed_shadow :
  forall (M : msolver) (tags tagged : list Z)
         (activity : list fp64) (orderpos order : list Z) (var_inc : fp64),
    msolver_seed_shadow M ->
    msolver_seed_shadow (analyze_tag_step_msolver M tags tagged
      activity orderpos order var_inc).
Proof.
  intros M tags tagged activity orderpos order var_inc Hseed.
  apply (proj2 (msolver_seed_shadow_analyze_tag_step M tags tagged
    activity orderpos order var_inc)). exact Hseed.
Qed.

Lemma solver_rep_analyze_at_open : forall s M n rsn lvl trl tgs wl,
  ms_size M = n ->
  solver_rep_analyze_at s M rsn lvl trl tgs wl
  |-- EX act opos : Z,
        “ solver_shape M ” &&
        (solver_analyze_open_at s M n act opos rsn lvl trl tgs wl **
         clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
         binary_scratch_rep (ms_binary M) (ms_binary_lits M)).
Proof.
  intros s Msol n rsn lvl trl tgs wl Hn; subst n.
  unfold solver_rep_analyze_at, solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
  solver_trail_array_rep, solver_levels_slice_at.
  Intros act asg opos. Exists act opos.
  unfold solver_analyze_open_at, solver_analyze_inert_at, solver_analyze_frame, solver_analyze_frame_cells,
  solver_scalars_rep, solver_fp_rep, solver_vecs_rep, db_words.
  set (stats_ptr := &( s # "solver_t" ->ₛ "stats")).
  sep_apply (msat_stats_rep_open_analyze stats_ptr (ms_stats Msol)).
  assert (Hmax : &( s # "solver_t" ->ₛ "stats" .ₛ "max_literals") =
                 &( stats_ptr # "stats_t" ->ₛ "max_literals"))
    by (unfold stats_ptr; csimpl; reflexivity).
  assert (Htot : &( s # "solver_t" ->ₛ "stats" .ₛ "tot_literals") =
                 &( stats_ptr # "stats_t" ->ₛ "tot_literals"))
    by (unfold stats_ptr; csimpl; reflexivity).
  rewrite Hmax, Htot.
  Exists asg.
  msat_entailer_with ltac:(int_auto).
Qed.

Lemma solver_analyze_open_at_rep : forall s M n act opos rsn lvl trl tgs wl,
  solver_shape M -> ms_size M = n ->
  solver_analyze_open_at s M n act opos rsn lvl trl tgs wl **
  clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
  binary_scratch_rep (ms_binary M) (ms_binary_lits M)
  |-- solver_rep_analyze_at s M rsn lvl trl tgs wl.
Proof.
  intros s Msol n act opos rsn lvl trl tgs wl Hshape Hn; subst n.
  unfold solver_analyze_open_at, solver_analyze_inert_at, solver_analyze_frame, solver_analyze_frame_cells.
  Intros asg.
  unfold solver_rep_analyze_at, solver_rep_at. Exists act asg opos.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at, solver_trail_array_rep,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep, db_words.
  set (stats_ptr := &( s # "solver_t" ->ₛ "stats")).
  assert (Hmax : &( s # "solver_t" ->ₛ "stats" .ₛ "max_literals") =
                 &( stats_ptr # "stats_t" ->ₛ "max_literals"))
    by (unfold stats_ptr; csimpl; reflexivity).
  assert (Htot : &( s # "solver_t" ->ₛ "stats" .ₛ "tot_literals") =
                 &( stats_ptr # "stats_t" ->ₛ "tot_literals"))
    by (unfold stats_ptr; csimpl; reflexivity).
  rewrite Hmax, Htot.
  sep_apply (msat_stats_analyze_frame_close stats_ptr (ms_stats Msol)).
  msat_entailer_with ltac:(int_auto).
Qed.

Lemma solver_cancel_pre_open : forall s level M wl,
  solver_cancel_pre s level M wl
  |-- EX act asg opos rsn trl : Z,
        “ solver_shape M /\ mtrail_wf (ms_size M) (ms_core M) /\
          cancel_bound_ready M level /\
          heap_wf (ms_size M) (msolver_heap M) /\
          0 <= level <= Zlength (mt_lim (ms_core M)) ” &&
        solver_cancel_open_at s M act asg opos rsn trl
          (mt_assigns (ms_core M)) (ms_orderpos M) (ms_reason_words M)
          (ms_order M) wl.
Proof.
  intros.
  unfold solver_cancel_pre, solver_cancel_owned, solver_nonlevel_rep.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl.
  unfold solver_cancel_open_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep,
    solver_vecs_rep, solver_trail_array_rep, solver_cancel_frame,
    solver_cancel_undef_tail.
  Exists tgs.
  msat_entailer_with ltac:(int_auto).
Qed.

(** Convert the normalized semantic root back to the actual memory model.
    Only the shape and the vacuous reasonless-level condition mention the
    stale physical root; no equality with a root-reset memory state is used. *)
Lemma solver_query_ready_of_root_rebuild__solve : forall n F M,
  solver_root_rebuild_ready n F M ->
  solver_shape M -> mt_qhead (ms_core M) = ms_qtail M ->
  ms_capacity_root_propagation_pending M = 0 ->
  solver_query_ready n F M.
Proof.
  intros n F M Hready Hshape Hdrain Hpending.
  pose proof (solver_root_rebuild_strong__canceluntil_cap n F M Hready) as Hnorm.
  pose proof (proj1 (proj2 Hready)) as Hlim.
  assert (Hroot : solver_at_root (msolver_set_root M 0)).
  { change (Zlength (mt_lim (ms_core M)) = 0). exact Hlim. }
  pose proof (msolver_inv_weak_assuming n F [] [] (msolver_set_root M 0)
    (msi_weak Hnorm) Hroot) as Hweak_norm.
  assert (Hweak : msolver_inv_assuming n F [] [] M).
  { destruct Hweak_norm. constructor; assumption. }
  unfold solver_query_ready. split.
  - constructor.
    + exact Hweak.
    + exact (msi_prop_level Hnorm).
    + exact (msi_watch_frontier Hnorm).
    + exact (msi_heap_covers Hnorm).
    + assert (Hnonneg : 0 <= ms_root_level M).
      { unfold solver_shape in Hshape. tauto. }
      apply current_reasonless_earliest_no_levels; assumption.
  - split; [exact Hlim|]. split; assumption.
Qed.

Lemma solver_sat_query_ready_empty__solve : forall n F A M,
  solver_sat_cancel_ready n F A M ->
  Zlength (mt_lim (ms_core M)) <= 0 ->
  solver_query_ready n F M /\ msolver_seed_shadow M.
Proof.
  intros n F A M [A_inst [Hinv [Hdrain [Hpending Hseed]]]] Hlen.
  assert (Hlim : Zlength (mt_lim (ms_core M)) = 0)
    by (pose proof (Zlength_nonneg (mt_lim (ms_core M))); lia).
  assert (Hprop : solver_propagation_inv n F A (PropagationStable A_inst) M).
  { split; [exact Hpending|]. apply msolver_inv_propagation_of_strong. exact Hinv. }
  assert (Hcovers : heap_covers (ms_size M) (msolver_heap M)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M)) (mt_qhead (ms_core M))).
  { rewrite <- (msi_size Hinv). exact (msi_heap_covers Hinv). }
  pose proof (solver_propagation_root_ready_empty__canceluntil_cap
    n F A (PropagationStable A_inst) M Hprop Hlim Hcovers) as Hready.
  split; [apply solver_query_ready_of_root_rebuild__solve;
    [exact Hready|exact (msi_shape Hinv)|exact Hdrain|exact Hpending] |exact Hseed].
Qed.

Lemma solver_sat_query_ready_cancel__solve :
  forall n F A M orderpos order,
  solver_sat_cancel_ready n F A M ->
  0 < Zlength (mt_lim (ms_core M)) ->
  heap_wf (ms_size M) (heap_of_lists order orderpos) ->
  incl (ms_order M) order ->
  cancel_reinserted (heap_of_lists order orderpos)
    (mt_trail (ms_core M)) (Znth 0 (mt_lim (ms_core M)) 0)
    (mt_qhead (ms_core M)) ->
  let Mpost := msolver_cancel_project M 0 orderpos order (ms_root_level M) in
  solver_query_ready n F Mpost /\ msolver_seed_shadow Mpost.
Proof.
  intros n F A M orderpos order
    [A_inst [Hinv [Hdrain [Hpending Hseed]]]] Hlim Hheap Hincl Hre.
  assert (Hprop : solver_propagation_inv n F A (PropagationStable A_inst) M).
  { split; [exact Hpending|]. apply msolver_inv_propagation_of_strong. exact Hinv. }
  assert (Hcovers : heap_covers (ms_size M) (msolver_heap M)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M)) (mt_qhead (ms_core M))).
  { rewrite <- (msi_size Hinv). exact (msi_heap_covers Hinv). }
  pose proof (solver_propagation_cancel_root_ready__canceluntil_cap
    n F A (PropagationStable A_inst) M orderpos order
    Hprop Hlim Hheap Hincl Hcovers Hre) as Hready.
  assert (Hshape : solver_shape
    (msolver_cancel_project M 0 orderpos order (ms_root_level M))).
  { apply (solver_shape_cancel_project__search n M 0 orderpos order
      (ms_root_level M)); try assumption.
    - exact (msi_shape Hinv).
    - exact (msi_trail_wf Hinv).
    - lia.
    - exact (proj1 (msi_root_range Hinv)). }
  split.
  - apply solver_query_ready_of_root_rebuild__solve.
    + exact Hready.
    + exact Hshape.
    + reflexivity.
    + exact Hpending.
  - exact Hseed.
Qed.


Lemma solver_base_state_normalized__api_reentry : forall n F M,
  solver_base_state n F M ->
  msolver_inv n F nil nil (msolver_set_root M 0).
Proof.
  intros n F M [Hstrong [Hlim Hpending]].
  apply solver_root_rebuild_strong__canceluntil_cap.
  unfold solver_root_rebuild_ready. split.
  - apply msolver_inv_ctx_root_empty__canceluntil_cap with
      (A_arr := (@nil literal)) (K := PropagationAssuming nil).
    + exact (msas_weak Hstrong).
    + exact Hlim.
  - split; [exact Hlim|]. split.
    + exact (msas_watch_frontier Hstrong).
    + exact (msas_heap_covers Hstrong).
Qed.

(* Root normalization is only a semantic view. The returned base state and
   every spatial assertion continue to describe the physical M. *)
Lemma solver_base_state_of_normalized__api_reentry : forall n F M,
  msolver_inv n F nil nil (msolver_set_root M 0) ->
  solver_shape M ->
  Zlength (mt_lim (ms_core M)) = 0 ->
  ms_capacity_root_propagation_pending M = 0 ->
  solver_base_state n F M.
Proof.
  intros n F M Hnormal Hshape Hlim Hpending.
  assert (Hroot : solver_at_root (msolver_set_root M 0)).
  { change (Zlength (mt_lim (ms_core M)) = 0). exact Hlim. }
  pose proof (msolver_inv_weak_assuming n F nil nil
    (msolver_set_root M 0) (msi_weak Hnormal) Hroot) as Hweak_normal.
  assert (Hweak : msolver_inv_assuming n F nil nil M).
  { destruct Hweak_normal. constructor; assumption. }
  unfold solver_base_state. split.
  - constructor.
    + exact Hweak.
    + exact (msi_prop_level Hnormal).
    + exact (msi_watch_frontier Hnormal).
    + exact (msi_heap_covers Hnormal).
    + apply current_reasonless_earliest_no_levels.
      * exact Hlim.
      * unfold solver_shape in Hshape. tauto.
  - split; assumption.
Qed.


Lemma solver_support_inv_add_var_sift__api_reentry :
  forall n F A_arr A_inst logical_root M a0 order1 orderpos1,
    solver_support_inv n F A_arr A_inst logical_root M ->
    ms_size M < ms_cap M ->
    2 * (n + 1) <= INT_MAX ->
    order_update_post (n + 1) (ms_size M)
      (ms_order M ++ (ms_size M :: nil))
      (ms_orderpos M ++ (Zlength (ms_order M) :: nil))
      order1 orderpos1 ->
    solver_support_inv (n + 1) F A_arr A_inst logical_root
      (msolver_heap_project (msolver_add_var M a0)
        orderpos1 order1).
Proof.
  intros n F A_arr A_inst logical_root M a0 order1 orderpos1
    Hinv Hroom Hbound Hsift.
  unfold solver_support_inv in *.
  change (msolver_inv (n + 1) F A_arr A_inst
    (msolver_heap_project
      (msolver_add_var (msolver_set_root M logical_root) a0)
      orderpos1 order1)).
  apply msolver_inv_add_var_sift; assumption.
Qed.

Lemma solver_support_inv_set_cap__api_reentry :
  forall n F A_arr A_inst logical_root M cap,
    solver_support_inv n F A_arr A_inst logical_root M ->
    ms_cap M <= cap <= INT_MAX ->
    solver_support_inv n F A_arr A_inst logical_root (msolver_set_cap M cap).
Proof.
  intros n F A_arr A_inst logical_root M cap Hinv [Hcap Hmax].
  unfold solver_support_inv in *.
  change (msolver_inv n F A_arr A_inst
    (msolver_set_cap (msolver_set_root M logical_root) cap)).
  apply msolver_inv_set_cap; assumption.
Qed.

(* A logical-root view leaves every physical dimension unchanged. The
   physical root still needs its own two shape conditions, including the
   pending-propagation condition; nonnegativity alone is insufficient. *)
Lemma solver_shape_restore_physical_root__api_reentry :
  forall M logical_root,
    solver_shape (msolver_set_root M logical_root) ->
    0 <= ms_root_level M ->
    (ms_capacity_root_propagation_pending M = 1 -> ms_root_level M = 0) ->
    solver_shape M.
Proof.
  intros M logical_root Hshape Hroot Hpending.
  unfold solver_shape, msolver_set_root, msolver_core_heap_update in *.
  cbn in *. tauto.
Qed.

Lemma setnvars_shape_from_support_view__api_reentry :
  forall M0 M logical_root,
    solver_shape M0 ->
    setnvars_core_equiv M0 M ->
    solver_shape (msolver_set_root M logical_root) ->
    solver_shape M.
Proof.
  intros M0 M logical_root Hshape0 Heq Hshape.
  destruct Heq as [_ [_ [_ [_ [Hpending [Hroot _]]]]]].
  eapply solver_shape_restore_physical_root__api_reentry.
  - exact Hshape.
  - rewrite Hroot. unfold solver_shape in Hshape0. tauto.
  - intros Hp. rewrite Hroot. rewrite Hpending in Hp.
    unfold solver_shape in Hshape0. tauto.
Qed.

Lemma solver_rep_growable_split_wl__api_reentry : forall s M,
  solver_rep_growable s M |--
  EX wl : Z, solver_rep_wl s M wl **
    solver_wlists_tail wl (2 * ms_size M) (2 * ms_cap M).
Proof.
  intros s M. sep_apply solver_rep_growable_to_wl. Intros wl lvl.
  Exists wl. unfold solver_rep_wl. Exists lvl.
  msat_entailer_with lia.
Qed.

Lemma solver_rep_growable_join_wl__api_reentry : forall s M wl,
  solver_rep_wl s M wl **
    solver_wlists_tail wl (2 * ms_size M) (2 * ms_cap M) |--
  solver_rep_growable s M.
Proof.
  intros s M wl. unfold solver_rep_wl. Intros lvl.
  apply solver_rep_growable_of_wl.
Qed.


Lemma solver_support_inv_order_update_pre__api_reentry :
  forall n F A_arr A_inst logical_root M,
    solver_support_inv n F A_arr A_inst logical_root M ->
    ms_size M < ms_cap M ->
    2 * (n + 1) <= INT_MAX ->
    order_update_pre (n + 1) (ms_size M)
      (ms_order M ++ (ms_size M :: nil))
      (ms_orderpos M ++ (Zlength (ms_order M) :: nil)).
Proof.
  intros n F A_arr A_inst logical_root M Hinv Hroom Hbound.
  unfold solver_support_inv in Hinv.
  exact (order_update_pre_add_var n F A_arr A_inst
    (msolver_set_root M logical_root) Hinv Hroom Hbound).
Qed.

(* While focus is being scanned, its own completion is the only exception. *)

Lemma minisat_watch_completed_except_frontier__api_reentry :
  forall n M focus,
    db_wf n (msolver_db M) ->
    minisat_watch_completed_except M focus ->
    minisat_watch_frontier n (msolver_db M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)).
Proof.
  intros n M focus [_ [_ Hobjects]] Hcomplete.
  unfold minisat_watch_frontier, watch_frontier, minisat_watch_occurrences.
  rewrite Forall_forall.
  intros o Ho [Hleft Hright].
  apply in_map_iff in Ho.
  destruct Ho as [[p co] [Ho Hin]]. subst o.
  rewrite Forall_forall in Hobjects.
  pose proof (Hobjects (p, co) Hin) as Hobj.
  cbn in Hobj.
  pose proof (obj_wf_watch0 n co Hobj) as Hw0.
  pose proof (obj_wf_watch1 n co Hobj) as Hw1.
  pose proof (obj_wf_watch_indices_distinct__reducedb n co Hobj)
    as Hdistinct.
  change (minisat_processed n (mt_assigns (ms_core M))
    (mt_trail (ms_core M)) (mt_qhead (ms_core M))
    (literal_neg (lit_denote (co_watch0 co)))) in Hleft.
  change (minisat_processed n (mt_assigns (ms_core M))
    (mt_trail (ms_core M)) (mt_qhead (ms_core M))
    (literal_neg (lit_denote (co_watch1 co)))) in Hright.
  rewrite <- lit_denote_neg in Hleft by (destruct Hw0; lia).
  rewrite <- lit_denote_neg in Hright by (destruct Hw1; lia).
  apply (proj1 (minisat_processed_denote n _ _ _ _
    (lit_neg_c_wf n _ Hw0))) in Hleft.
  apply (proj1 (minisat_processed_denote n _ _ _ _
    (lit_neg_c_wf n _ Hw1))) in Hright.
  assert (Hcontra : forall l,
    lit_true (mt_assigns (ms_core M)) l ->
    processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) (lit_neg_c l) -> False).
  { intros l Htrue [Hneg _].
    eapply lit_true_false_contra; [exact Htrue|].
    unfold lit_true in Hneg.
    rewrite lit_var_c_neg, lit_sig_neg in Hneg.
    exact Hneg. }
  destruct (Hcomplete p co Hin) as [Hclose0 Hclose1].
  destruct (Z.eq_dec (lit_neg_c (co_watch0 co)) focus) as [Heq|Hneq].
  - assert (Hneq1 : lit_neg_c (co_watch1 co) <> focus) by congruence.
    exact (Hcontra _ (proj1 (Hclose1 Hneq1 Hright)) Hleft).
  - exact (Hcontra _ (proj1 (Hclose0 Hneq Hleft)) Hright).
Qed.

(* Full completion implies this exception for every focus, so the same
   lemma also establishes the ordinary frontier.

   The level inequalities are not needed by this propositional lemma. They
   are needed by cancellation: if a processed false watch survives below the
   backjump level, its true partner survives too. *)

Lemma minisat_watch_completed_frontier__api_reentry : forall n M,
  db_wf n (msolver_db M) -> minisat_watch_completed M ->
  minisat_watch_frontier n (msolver_db M)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M))
    (mt_qhead (ms_core M)).
Proof.
  intros n M Hdb Hcomplete.
  apply (minisat_watch_completed_except_frontier__api_reentry n M 0 Hdb).
  intros p co Hin. destruct (Hcomplete p co Hin) as [H0 H1].
  split; intros _ Hprocessed; [apply H0|apply H1]; exact Hprocessed.
Qed.

Lemma minisat_watch_completed_empty_db__api_reentry : forall M,
  msolver_db M = nil -> minisat_watch_completed M.
Proof.
  intros M Hempty p co Hin. rewrite Hempty in Hin. contradiction.
Qed.


Lemma completed_watch_enqueue_fresh__api_reentry :
  forall n t q watch other,
    mtrail_wf n t ->
    lit_wf_c n q -> lit_wf_c n watch -> lit_wf_c n other ->
    Znth (lit_var_c q) (mt_assigns t) 0 = 0 ->
    (processed (mt_assigns t) (mt_trail t) (mt_qhead t)
       (lit_neg_c watch) ->
     lit_true (mt_assigns t) other /\
     Znth (lit_var_c other) (mt_levels t) 0 <=
     Znth (lit_var_c watch) (mt_levels t) 0) ->
    processed (mt_assigns (mt_enqueue t q)) (mt_trail (mt_enqueue t q))
      (mt_qhead (mt_enqueue t q)) (lit_neg_c watch) ->
    lit_true (mt_assigns (mt_enqueue t q)) other /\
    Znth (lit_var_c other) (mt_levels (mt_enqueue t q)) 0 <=
    Znth (lit_var_c watch) (mt_levels (mt_enqueue t q)) 0.
Proof.
  intros n t q watch other Htrail Hq Hwatch Hother Hfresh Hcomplete Hnew.
  pose proof (proj1 (processed_enqueue_fresh_equiv__propagate_dbu
    n t q Htrail Hq Hfresh) (lit_neg_c watch)
    (lit_neg_c_wf n watch Hwatch) Hnew) as Hold.
  destruct (Hcomplete Hold) as [Htrue Hlevel].
  pose proof (processed_fresh_target_different
    (mt_assigns t) (mt_trail t) (mt_qhead t)
    (lit_neg_c watch) q Hold Hfresh) as Hqwatch.
  rewrite lit_var_c_neg in Hqwatch.
  assert (Hqother : lit_var_c q <> lit_var_c other).
  { intro Heq. apply (lit_true_assigned (mt_assigns t) other Htrue).
    rewrite <- Heq. exact Hfresh. }
  pose proof (lit_var_c_in_range n q Hq) as Hqrange.
  pose proof (lit_var_c_in_range n watch Hwatch) as Hwatchrange.
  pose proof (lit_var_c_in_range n other Hother) as Hotherrange.
  unfold mt_enqueue, mt_push. cbn [mt_assigns mt_levels].
  split.
  - unfold lit_true in Htrue |- *.
    rewrite Znth_replace_Znth_Diff
      by (try rewrite (mtw_assigns_len Htrail); assumption).
    exact Htrue.
  - rewrite !Znth_replace_Znth_Diff
      by (try rewrite (mtw_levels_len Htrail); assumption).
    exact Hlevel.
Qed.

Lemma minisat_watch_completed_enqueue_fresh__api_reentry :
  forall n M q reason_word reason_opt,
    db_wf n (msolver_db M) ->
    mtrail_wf n (ms_core M) ->
    lit_wf_c n q ->
    Znth (lit_var_c q) (mt_assigns (ms_core M)) 0 = 0 ->
    minisat_watch_completed M ->
    minisat_watch_completed
      (msolver_enqueue_fresh M q reason_word reason_opt).
Proof.
  intros n M q reason_word reason_opt [_ [_ Hobjects]] Htrail Hq Hfresh Hcomplete.
  intros p co Hin.
  change (In (p, co) (msolver_db M)) in Hin.
  rewrite Forall_forall in Hobjects.
  pose proof (Hobjects (p, co) Hin) as Hobj. cbn in Hobj.
  pose proof (obj_wf_watch0 n co Hobj) as Hw0.
  pose proof (obj_wf_watch1 n co Hobj) as Hw1.
  destruct (Hcomplete p co Hin) as [H0 H1].
  split; intros Hprocessed.
  - eapply (completed_watch_enqueue_fresh__api_reentry
      n (ms_core M) q (co_watch0 co) (co_watch1 co));
      [exact Htrail|exact Hq|exact Hw0|exact Hw1|exact Hfresh|exact H0|exact Hprocessed].
  - eapply (completed_watch_enqueue_fresh__api_reentry
      n (ms_core M) q (co_watch1 co) (co_watch0 co));
      [exact Htrail|exact Hq|exact Hw1|exact Hw0|exact Hfresh|exact H1|exact Hprocessed].
Qed.

Lemma processed_cancel_prefix_level__api_reentry :
  forall n t level l,
    mtrail_wf n t -> lit_wf_c n l ->
    0 <= level < Zlength (mt_lim t) ->
    Znth level (mt_lim t) 0 <= mt_qhead t ->
    processed (mt_assigns (mt_cancel t level))
      (mt_trail (mt_cancel t level)) (mt_qhead (mt_cancel t level)) l ->
    processed (mt_assigns t) (mt_trail t) (mt_qhead t) l /\
    Znth (lit_var_c l) (mt_levels t) 0 <= level.
Proof.
  intros n t level l Hwf Hl Hlevel Hbound Hnew.
  split.
  - apply (proj1 (minisat_processed_denote n _ _ _ l Hl)).
    eapply minisat_processed_cancel_sub__canceluntil_cap;
      [exact Hwf | exact Hlevel | exact Hbound |].
    apply (proj2 (minisat_processed_denote n _ _ _ l Hl)). exact Hnew.
  - destruct Hnew as [_ [i [Hi Hlit]]].
    rewrite mt_cancel_qhead in Hi. rewrite mt_cancel_trail in Hlit.
    pose proof (lim_lt_trail n t level Hwf Hlevel) as Hcut.
    rewrite Znth_ztake in Hlit by lia.
    assert (Hrange : 0 <= i < Zlength (mt_trail t)) by lia.
    pose proof (mtw_levels_agree Hwf i Hrange) as Hcell.
    unfold trail_var in Hcell. rewrite Hlit in Hcell. rewrite Hcell.
    unfold level_of_index.
    destruct (Z_le_gt_dec (count_le i (mt_lim t)) level) as [Hle | Hgt];
      [exact Hle |].
    pose proof (strict_sorted_count_prefix (mt_lim t) i level
      (mtw_lim_sorted Hwf) ltac:(lia)) as Hbefore. lia.
Qed.

Lemma lit_true_cancel_below__api_reentry :
  forall n t level l,
    mtrail_wf n t -> lit_wf_c n l ->
    0 <= level < Zlength (mt_lim t) ->
    lit_true (mt_assigns t) l ->
    Znth (lit_var_c l) (mt_levels t) 0 <= level ->
    lit_true (mt_assigns (mt_cancel t level)) l.
Proof.
  intros n t level l Hwf Hl Hlevel Htrue Hbelow.
  assert (Hvar : 0 <= literal_var (lit_denote l)).
  { rewrite lit_var_c_denote. exact (proj1 (lit_var_c_in_range n l Hl)). }
  assert (Hguard : forall u,
    eval_partial_literal (mt_pv u) (lit_denote l) =
    eval_partial_literal (assigns_pv (mt_assigns u)) (lit_denote l)).
  { intro u. unfold eval_partial_literal, mt_pv.
    rewrite (proj2 (Z.leb_le 0 (literal_var (lit_denote l))) Hvar).
    reflexivity. }
  assert (Hold : Forall (assump_true_at_root t level) [lit_denote l]).
  { constructor; [|constructor]. split.
    - rewrite Hguard. apply (proj1 (lit_true_iff _ l (proj1 Hl))).
      exact Htrue.
    - rewrite lit_var_c_denote. exact Hbelow. }
  pose proof (assump_sat_cancel_at_root__search
    n t level [lit_denote l] Hwf Hlevel Hold) as Hafter.
  inversion Hafter as [|a rest Hsat Hrest]; subst.
  destruct Hsat as [Heval _]. rewrite Hguard in Heval.
  apply (proj2 (lit_true_iff _ l (proj1 Hl))). exact Heval.
Qed.

Lemma processed_dequeue_other__api_reentry :
  forall assigns trail qhead focus l,
    focus = Znth qhead trail 0 -> l <> focus ->
    processed assigns trail (qhead + 1) l ->
    processed assigns trail qhead l.
Proof.
  intros assigns trail qhead focus l Hfocus Hneq [Htrue [i [Hi Hlit]]].
  split; [exact Htrue|]. exists i. split; [|exact Hlit].
  destruct (Z.eq_dec i qhead) as [Heq|Heq]; [subst i; congruence|lia].
Qed.

(* An already assigned literal cannot have a level above the current one.
   Unassigned cells are intentionally excluded because their level is stale. *)
Lemma assigned_level_current_bound__api_reentry :
  forall n t l,
    mtrail_wf n t -> lit_wf_c n l -> lit_true (mt_assigns t) l ->
    Znth (lit_var_c l) (mt_levels t) 0 <= Zlength (mt_lim t).
Proof.
  intros n t l Hwf Hl Htrue.
  destruct (mtrail_wf_trail_covers n t Hwf l Hl Htrue)
    as [i [Hi Hindex]].
  pose proof (mtw_levels_agree Hwf i Hi) as Hlevel.
  unfold trail_var in Hlevel. rewrite Hindex in Hlevel.
  rewrite Hlevel. apply count_le_length.
Qed.

Lemma db_pair_lits_update_forall_clauses__api_reentry :
  forall prob learnt current old_lits new_lits prob' learnt' (P : clause_obj -> Prop),
    db_pair_lits_update prob learnt current old_lits new_lits prob' learnt' ->
    (forall co, In (current,co) (prob ++ learnt) -> co_lits co = old_lits -> P co ->
      P (clause_obj_with_lits co new_lits)) ->
    Forall (fun e => P (snd e)) (prob ++ learnt) ->
    Forall (fun e => P (snd e)) (prob' ++ learnt').
Proof.
  intros prob learnt current old_lits new_lits prob' learnt' P Hupdate Hselected Hall.
  eapply db_pair_lits_update_forall__propagate_dbu;
    [exact Hupdate|exact Hselected|exact Hall].
Qed.

(* Owner-aware form of exact DB replacement, needed because a real watcher
   word is the owner pointer while a binary word encodes its partner. *)
Lemma db_pair_lits_update_all_entries__api_reentry :
  forall prob learnt current old_lits new_lits prob' learnt'
    (P : Z -> clause_obj -> Prop),
    db_pair_lits_update prob learnt current old_lits new_lits prob' learnt' ->
    (forall owner co, In (owner,co) (prob ++ learnt) -> P owner co) ->
    (forall co, In (current,co) (prob ++ learnt) -> co_lits co = old_lits ->
      P current co -> P current (clause_obj_with_lits co new_lits)) ->
    forall owner co, In (owner,co) (prob' ++ learnt') -> P owner co.
Proof.
  intros prob learnt current old_lits new_lits prob' learnt' P Hupdate Hall Hselected.
  assert (Hforall : Forall (fun e => P (fst e) (snd e)) (prob' ++ learnt')).
  { eapply db_pair_lits_update_forall__propagate_dbu;
      [exact Hupdate|exact Hselected|].
    rewrite Forall_forall. intros [owner co] Hin. apply Hall. exact Hin. }
  intros owner co Hin. rewrite Forall_forall in Hforall. exact (Hforall _ Hin).
Qed.

Lemma minisat_false_watch_processed_drained__api_reentry :
  forall n t w,
    mtrail_wf n t ->
    mt_qhead t = Zlength (mt_trail t) ->
    lit_wf_c n w ->
    lit_false (mt_assigns t) w ->
    minisat_processed n (mt_assigns t) (mt_trail t) (mt_qhead t)
      (literal_neg (lit_denote w)).
Proof.
  intros n t w Htrail Hdrained Hw Hfalse.
  pose proof (lit_neg_c_wf n w Hw) as Hnegwf.
  pose proof (lit_false_neg_true (mt_assigns t) w Hfalse) as Htrue.
  destruct (mtrail_wf_trail_covers n t Htrail
    (lit_neg_c w) Hnegwf Htrue) as [i [Hi Hindex]].
  exists (lit_neg_c w). split; [exact Hnegwf|].
  split.
  - rewrite lit_denote_neg by (destruct Hw; lia). reflexivity.
  - split; [exact Htrue|].
    exists i. split; [rewrite Hdrained; exact Hi|exact Hindex].
Qed.

Lemma minisat_drained_frontier_no_resident_false__api_reentry :
  forall n db t p co,
    db_wf n db ->
    mtrail_wf n t ->
    mt_qhead t = Zlength (mt_trail t) ->
    minisat_watch_frontier n db (mt_assigns t) (mt_trail t) (mt_qhead t) ->
    In (p, co) db ->
    ~ clause_false (assigns_pv (mt_assigns t)) (denote_obj co).
Proof.
  intros n db t p co Hdb Htrail Hdrained Hfront Hin Hfalse.
  pose proof (db_wf_obj n db p co Hdb Hin) as Hobj.
  assert (Hwatch : forall w, lit_wf_c n w -> In w (co_lits co) ->
    minisat_processed n (mt_assigns t) (mt_trail t) (mt_qhead t)
      (literal_neg (lit_denote w))).
  { intros w Hw Hinw.
    apply (minisat_false_watch_processed_drained__api_reentry
      n t w Htrail Hdrained Hw).
    apply (proj2 (lit_false_iff (mt_assigns t) w ltac:(destruct Hw; lia))).
    apply Hfalse. apply lits_denote_in. exact Hinw. }
  unfold minisat_watch_frontier, watch_frontier in Hfront.
  rewrite Forall_forall in Hfront.
  apply (Hfront (minisat_occurrence_of_entry (p, co))).
  - unfold minisat_watch_occurrences. apply in_map. exact Hin.
  - split; cbn.
    + apply Hwatch; [exact (obj_wf_watch0 n co Hobj)|exact (obj_wf_watch0_in n co Hobj)].
    + apply Hwatch; [exact (obj_wf_watch1 n co Hobj)|exact (obj_wf_watch1_in n co Hobj)].
Qed.

(* qtail is a separate physical field: solver_shape supplies its existing
   equality with the logical trail length, rather than assuming it silently. *)
Lemma solver_drained_frontier_no_resident_false__api_reentry :
  forall n M p co,
    solver_shape M ->
    db_wf n (msolver_db M) ->
    mtrail_wf n (ms_core M) ->
    mt_qhead (ms_core M) = ms_qtail M ->
    minisat_watch_frontier n (msolver_db M) (mt_assigns (ms_core M))
      (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
    In (p, co) (msolver_db M) ->
    ~ clause_false (assigns_pv (mt_assigns (ms_core M))) (denote_obj co).
Proof.
  intros n M p co Hshape Hdb Htrail Hdrained Hfront Hin.
  eapply minisat_drained_frontier_no_resident_false__api_reentry;
    [exact Hdb|exact Htrail| |exact Hfront|exact Hin].
  rewrite Hdrained. symmetry. unfold solver_shape in Hshape. tauto.
Qed.

(* The existing exact carrier accounts for every pending word. Recover its
   real database owner with wmap_tag_witness, even when two owners emit equal
   tags; a temporary binary scratch object is not used as ownership evidence. *)
Lemma minisat_pending_tag_resident__api_reentry :
  forall n db wm p P kept current rest,
    db_wf n db ->
    wmap_exact n db wm ->
    lit_wf_c n p ->
    minisat_focus_scan_carrier db p P kept (current :: rest) ->
    is_tag current = true ->
    exists owner co, In (owner, co) db /\ Zlength (co_lits co) = 2 /\
      Permutation (co_lits co) [lit_neg_c p; tag_lit current].
Proof.
  intros n db wm p P kept current rest Hdb Hwm Hp Hscan Htag.
  apply (wmap_tag_witness n db wm p current Hdb Hwm Hp); [|exact Htag].
  eapply Permutation_in; [apply Permutation_sym; exact (proj2 Hwm p Hp)|].
  eapply Permutation_in;
    [apply (focus_scan_carrier_words_expected__propagate_dbu
      db p P kept (current :: rest)); exact Hscan|].
  apply in_or_app. right. left. reflexivity.
Qed.

Lemma minisat_pending_binary_conflict_resident__api_reentry :
  forall n db wm p P kept current rest assigns,
    db_wf n db ->
    wmap_exact n db wm ->
    lit_wf_c n p ->
    minisat_focus_scan_carrier db p P kept (current :: rest) ->
    is_tag current = true ->
    lit_true assigns p ->
    lit_false assigns (tag_lit current) ->
    exists owner co, In (owner, co) db /\
      Permutation (co_lits co) [tag_lit current; lit_neg_c p] /\
      clause_false (assigns_pv assigns) (denote_obj co).
Proof.
  intros n db wm p P kept current rest assigns Hdb Hwm Hp Hscan Htag Htrue Hfalse.
  destruct (minisat_pending_tag_resident__api_reentry
    n db wm p P kept current rest Hdb Hwm Hp Hscan Htag)
    as [owner [co [Hin [Hlength Hperm]]]].
  pose proof (db_wf_obj n db owner co Hdb Hin) as Hobj.
  assert (Hcofalse : Forall (fun w => Znth (lit_var_c w) assigns 0 = - lit_sig w)
      (co_lits co)).
  { eapply Forall_of_perm; [apply Permutation_sym; exact Hperm|].
    constructor.
    - rewrite lit_var_c_neg, lit_sig_neg. unfold lit_true in Htrue. lia.
    - constructor; [exact Hfalse|constructor]. }
  exists owner, co. split; [exact Hin|]. split.
  - eapply Permutation_trans; [exact Hperm|apply perm_swap].
  - unfold denote_obj. apply lits_denote_false_iff; [|exact Hcofalse].
    eapply Forall_impl; [|exact (proj1 (proj2 Hobj))].
    intros w Hw. destruct Hw; lia.
Qed.

Lemma propagation_binary_conflict_resident__api_reentry :
  forall n F A_arr K M p confl kept current rest,
    solver_propagation_scan_semantics n F A_arr K M p confl kept (current :: rest) ->
    is_tag current = true ->
    lit_false (mt_assigns (ms_core M)) (tag_lit current) ->
    let M' := msolver_propagation_binary_conflict M (tag_lit current) p in
    exists owner co, In (owner, co) (msolver_db M') /\
      Permutation (co_lits co) (ms_binary_lits M') /\
      clause_false (assigns_pv (mt_assigns (ms_core M'))) (denote_obj co).
Proof.
  intros n F A_arr K M p confl kept current rest Hsem Htag Hfalse M'.
  destruct Hsem as [Hlive|Hdead].
  - destruct Hlive as [Hconfl [Hweak [Hlevel [Hheap [Hcovers [Hearliest
      [Hlevelof [Hp [Hprocessed [Hfront Hfocus]]]]]]]]]].
    pose proof (solver_propagation_weak_core_facts__propagate n F A_arr K M Hweak)
      as [_ [_ [Hdb [Hwm Htrail]]]].
    change (exists owner co, In (owner, co) (msolver_db M) /\
      Permutation (co_lits co) [tag_lit current; lit_neg_c p] /\
      clause_false (assigns_pv (mt_assigns (ms_core M))) (denote_obj co)).
    eapply minisat_pending_binary_conflict_resident__api_reentry;
      [exact Hdb|exact Hwm|exact Hp|exact Hfocus|exact Htag|
       exact (proj1 Hprocessed)|exact Hfalse].
  - destruct Hdead as [_ [Hempty _]]. discriminate Hempty.
Qed.

Lemma db_pair_lits_update_preserves_occurrence__api_reentry :
  forall prob learnt current old_lits new_lits prob' learnt' owner co,
    db_pair_lits_update prob learnt current old_lits new_lits prob' learnt' ->
    Permutation old_lits new_lits ->
    In (owner, co) (prob ++ learnt) ->
    exists co', In (owner, co') (prob' ++ learnt') /\
      Permutation (co_lits co) (co_lits co').
Proof.
  intros prob learnt current old_lits new_lits prob' learnt' owner co
    Hupdate Hperm Hin.
  destruct (db_pair_lits_update_splice__propagate_dbu _ _ _ _ _ _ _ Hupdate)
    as [selected [pre [post [Hold [Hnew Hlits]]]]].
  rewrite Hold in Hin. rewrite Hnew.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - exists co. split; [apply in_or_app; left; exact Hin|apply Permutation_refl].
  - destruct Hin as [Heq|Hin].
    + injection Heq as Howner Hco. subst owner co.
      exists (clause_obj_with_lits selected new_lits). split.
      * apply in_or_app. right. left. reflexivity.
      * cbn. rewrite Hlits. exact Hperm.
    + exists co. split.
      * apply in_or_app. right. right. exact Hin.
      * apply Permutation_refl.
Qed.

Lemma minisat_resident_false_db_update__api_reentry :
  forall M current old_lits new_lits prob' learnt' wm,
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      old_lits new_lits prob' learnt' ->
    Permutation old_lits new_lits ->
    minisat_resident_false_clause M ->
    minisat_resident_false_clause
      (msolver_propagation_db_wmap_update M prob' learnt' wm).
Proof.
  intros M current old_lits new_lits prob' learnt' wm Hupdate Hperm
    [owner [co [Hin Hfalse]]].
  destruct (db_pair_lits_update_preserves_occurrence__api_reentry
    (ms_prob M) (ms_learnt M) current old_lits new_lits prob' learnt'
    owner co Hupdate Hperm Hin) as [co' [Hin' Hperm']].
  exists owner, co'. split; [exact Hin'|].
  eapply clause_false_perm; [unfold denote_obj; apply lits_denote_perm; exact Hperm'|].
  exact Hfalse.
Qed.

(* A false literal has an assigned cell, so a fresh enqueue necessarily
   updates a different variable. This directly preserves every clause cell;
   no total valuation or formula entailment is needed. *)
Lemma lits_false_enqueue_fresh__api_reentry : forall n t words q,
  mtrail_wf n t -> Forall (lit_wf_c n) words -> lit_wf_c n q ->
  Znth (lit_var_c q) (mt_assigns t) 0 = 0 ->
  clause_false (assigns_pv (mt_assigns t)) (lits_denote words) ->
  clause_false (assigns_pv (mt_assigns (mt_enqueue t q))) (lits_denote words).
Proof.
  intros n t words q Htrail Hwords Hq Hfresh Hfalse.
  apply lits_denote_false_iff.
  - eapply Forall_impl; [|exact Hwords]. intros w Hw. destruct Hw; lia.
  - rewrite Forall_forall in Hwords |- *. intros w Hin.
    pose proof (Hwords w Hin) as Hw.
    assert (Hwfals : lit_false (mt_assigns t) w).
    { apply (proj2 (lit_false_iff (mt_assigns t) w (proj1 Hw))).
      apply Hfalse. apply lits_denote_in. exact Hin. }
    assert (Hneq : lit_var_c q <> lit_var_c w).
    { intro Heq. apply (lit_true_assigned (mt_assigns t) (lit_neg_c w)
        (lit_false_neg_true (mt_assigns t) w Hwfals)).
      rewrite lit_var_c_neg, <- Heq. exact Hfresh. }
    unfold mt_enqueue, mt_push. cbn [mt_assigns].
    rewrite Znth_replace_Znth_Diff.
    + exact Hwfals.
    + rewrite (mtw_assigns_len Htrail). exact (lit_var_c_in_range n q Hq).
    + rewrite (mtw_assigns_len Htrail). exact (lit_var_c_in_range n w Hw).
    + exact Hneq.
Qed.

Lemma minisat_resident_false_enqueue_success__api_reentry :
  forall n M q reason_word reason_clause,
    db_wf n (msolver_db M) -> mtrail_wf n (ms_core M) -> lit_wf_c n q ->
    minisat_resident_false_clause M ->
    minisat_resident_false_clause
      (msolver_propagation_enqueue_success M q reason_word reason_clause).
Proof.
  intros n M q reason_word reason_clause Hdb Htrail Hq Hresident.
  unfold msolver_propagation_enqueue_success.
  destruct (Znth (lit_var_c q) (mt_assigns (ms_core M)) 0 =? 0) eqn:Hfresh;
    [|exact Hresident].
  apply Z.eqb_eq in Hfresh.
  destruct Hresident as [owner [co [Hin Hfalse]]].
  pose proof (db_wf_obj n (msolver_db M) owner co Hdb Hin) as Hobj.
  exists owner, co. split; [exact Hin|].
  change (clause_false (assigns_pv (mt_assigns (mt_enqueue (ms_core M) q)))
    (lits_denote (co_lits co))).
  eapply lits_false_enqueue_fresh__api_reentry;
    [exact Htrail|exact (proj1 (proj2 Hobj))|exact Hq|exact Hfresh|exact Hfalse].
Qed.

Lemma minisat_resident_false_scan_begin__api_reentry : forall M simp props,
  minisat_resident_false_clause M ->
  minisat_resident_false_clause (msolver_propagation_scan_begin M simp props).
Proof.
  intros M simp props. apply minisat_resident_false_same_fields__api_reentry;
    reflexivity.
Qed.


Lemma minisat_resident_false_excludes_drained_success__api_reentry : forall n M,
  solver_shape M -> db_wf n (msolver_db M) -> mtrail_wf n (ms_core M) ->
  mt_qhead (ms_core M) = ms_qtail M ->
  minisat_watch_frontier n (msolver_db M) (mt_assigns (ms_core M))
    (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
  minisat_resident_false_clause M -> False.
Proof.
  intros n M Hshape Hdb Htrail Hdrained Hfront [owner [co [Hin Hfalse]]].
  eapply solver_drained_frontier_no_resident_false__api_reentry;
    [exact Hshape|exact Hdb|exact Htrail|exact Hdrained|exact Hfront|exact Hin|exact Hfalse].
Qed.

Lemma minisat_watch_completed_same_fields__api_reentry : forall M M',
  msolver_db M' = msolver_db M ->
  mt_assigns (ms_core M') = mt_assigns (ms_core M) ->
  mt_levels (ms_core M') = mt_levels (ms_core M) ->
  mt_trail (ms_core M') = mt_trail (ms_core M) ->
  mt_qhead (ms_core M') = mt_qhead (ms_core M) ->
  minisat_watch_completed M -> minisat_watch_completed M'.
Proof.
  intros M M' Hdb Ha Hl Ht Hq.
  unfold minisat_watch_completed. rewrite Hdb, Ha, Hl, Ht, Hq. trivial.
Qed.

Lemma assigned_level_nonnegative__api_reentry : forall n t l,
  mtrail_wf n t -> lit_wf_c n l -> lit_true (mt_assigns t) l ->
  0 <= Znth (lit_var_c l) (mt_levels t) 0.
Proof.
  intros n t l Hwf Hl Htrue.
  destruct (mtrail_wf_trail_covers n t Hwf l Hl Htrue) as [i [Hi Hindex]].
  pose proof (mtw_levels_agree Hwf i Hi) as Hlevel.
  unfold trail_var in Hlevel. rewrite Hindex in Hlevel. rewrite Hlevel.
  apply level_of_index_nonneg.
Qed.

Lemma minisat_full_completion_implies_base__api_reentry : forall n M,
  mtrail_wf n (ms_core M) -> db_wf n (msolver_db M) ->
  minisat_watch_completed M -> minisat_base_watch_completed M.
Proof.
  intros n M Hwf Hdb Hfull owner co Hin.
  pose proof (db_wf_obj n (msolver_db M) owner co Hdb Hin) as Hobj.
  destruct (Hfull owner co Hin) as [Hleft Hright]. split; intros Hprocessed Hzero.
  - destruct (Hleft Hprocessed) as [Htrue Hlevel]. split; [exact Htrue|].
    pose proof (assigned_level_nonnegative__api_reentry n (ms_core M)
      (co_watch1 co) Hwf (obj_wf_watch1 n co Hobj) Htrue). lia.
  - destruct (Hright Hprocessed) as [Htrue Hlevel]. split; [exact Htrue|].
    pose proof (assigned_level_nonnegative__api_reentry n (ms_core M)
      (co_watch0 co) Hwf (obj_wf_watch0 n co Hobj) Htrue). lia.
Qed.

Lemma processed_watch_level_zero_at_depth_zero__api_reentry : forall n t,
  mtrail_wf n t -> Zlength (mt_lim t) = 0 -> forall watch,
  lit_wf_c n watch ->
  processed (mt_assigns t) (mt_trail t) (mt_qhead t) (lit_neg_c watch) ->
  Znth (lit_var_c watch) (mt_levels t) 0 = 0.
Proof.
  intros n t Hwf Hdepth watch Hw Hprocessed.
  pose proof (assigned_level_nonnegative__api_reentry n t
    (lit_neg_c watch) Hwf (lit_neg_c_wf n watch Hw) (proj1 Hprocessed)) as Hnonneg.
  pose proof (assigned_level_current_bound__api_reentry n t
    (lit_neg_c watch) Hwf (lit_neg_c_wf n watch Hw) (proj1 Hprocessed)) as Hbound.
  rewrite lit_var_c_neg in Hnonneg, Hbound. lia.
Qed.

Lemma minisat_base_completion_at_depth_zero__api_reentry : forall n M,
  mtrail_wf n (ms_core M) -> db_wf n (msolver_db M) ->
  Zlength (mt_lim (ms_core M)) = 0 ->
  minisat_base_watch_completed M -> minisat_watch_completed M.
Proof.
  intros n M Hwf Hdb Hdepth Hbase owner co Hin.
  pose proof (db_wf_obj n (msolver_db M) owner co Hdb Hin) as Hobj.
  destruct (Hbase owner co Hin) as [Hleft Hright].
  pose proof (processed_watch_level_zero_at_depth_zero__api_reentry
    n (ms_core M) Hwf Hdepth) as Hzero.
  split; intro Hprocessed.
  - pose proof (Hzero (co_watch0 co) (obj_wf_watch0 n co Hobj) Hprocessed) as Hwzero.
    destruct (Hleft Hprocessed Hwzero) as [Htrue Hother]. split; [exact Htrue|lia].
  - pose proof (Hzero (co_watch1 co) (obj_wf_watch1 n co Hobj) Hprocessed) as Hwzero.
    destruct (Hright Hprocessed Hwzero) as [Htrue Hother]. split; [exact Htrue|lia].
Qed.

Lemma base_completed_watch_cancel_zero__api_reentry : forall n t watch other,
  mtrail_wf n t -> lit_wf_c n watch -> lit_wf_c n other ->
  0 < Zlength (mt_lim t) -> Znth 0 (mt_lim t) 0 <= mt_qhead t ->
  (processed (mt_assigns t) (mt_trail t) (mt_qhead t) (lit_neg_c watch) ->
   Znth (lit_var_c watch) (mt_levels t) 0 = 0 ->
   lit_true (mt_assigns t) other /\ Znth (lit_var_c other) (mt_levels t) 0 = 0) ->
  processed (mt_assigns (mt_cancel t 0)) (mt_trail (mt_cancel t 0))
    (mt_qhead (mt_cancel t 0)) (lit_neg_c watch) ->
  lit_true (mt_assigns (mt_cancel t 0)) other /\
  Znth (lit_var_c other) (mt_levels (mt_cancel t 0)) 0 <=
  Znth (lit_var_c watch) (mt_levels (mt_cancel t 0)) 0.
Proof.
  intros n t watch other Hwf Hw Ho Hpositive Hbound Hbase Hnew.
  destruct (processed_cancel_prefix_level__api_reentry n t 0 (lit_neg_c watch)
    Hwf (lit_neg_c_wf n watch Hw) ltac:(lia) Hbound Hnew) as [Hold Hbelow].
  pose proof (assigned_level_nonnegative__api_reentry n t (lit_neg_c watch)
    Hwf (lit_neg_c_wf n watch Hw) (proj1 Hold)) as Hnonneg.
  rewrite lit_var_c_neg in Hbelow,Hnonneg.
  assert (Hzero : Znth (lit_var_c watch) (mt_levels t) 0 = 0) by lia.
  destruct (Hbase Hold Hzero) as [Htrue Hother]. split.
  - eapply lit_true_cancel_below__api_reentry;
      [exact Hwf|exact Ho|lia|exact Htrue|lia].
  - rewrite !mt_cancel_levels. lia.
Qed.

Lemma minisat_base_completion_cancel_zero__api_reentry :
  forall n M orderpos order root,
    mtrail_wf n (ms_core M) -> db_wf n (msolver_db M) ->
    0 < Zlength (mt_lim (ms_core M)) ->
    Znth 0 (mt_lim (ms_core M)) 0 <= mt_qhead (ms_core M) ->
    minisat_base_watch_completed M ->
    minisat_watch_completed (msolver_cancel_project M 0 orderpos order root).
Proof.
  intros n M orderpos order root Hwf Hdb Hpositive Hbound Hbase owner co Hin.
  change (In (owner,co) (msolver_db M)) in Hin.
  pose proof (db_wf_obj n (msolver_db M) owner co Hdb Hin) as Hobj.
  destruct (Hbase owner co Hin) as [Hleft Hright].
  cbn [msolver_cancel_project msolver_core_heap_update ms_core]. split;
    eapply base_completed_watch_cancel_zero__api_reentry; eassumption ||
      (first [exact (obj_wf_watch0 n co Hobj)|exact (obj_wf_watch1 n co Hobj)]).
Qed.

Lemma minisat_base_exception_above_zero__api_reentry : forall M focus,
  0 < Znth (lit_var_c focus) (mt_levels (ms_core M)) 0 ->
  minisat_base_watch_completed_except M focus -> minisat_base_watch_completed M.
Proof.
  intros M focus Hpositive Hexcept owner co Hin.
  destruct (Hexcept owner co Hin) as [Hleft Hright].
  assert (Hdifferent : forall watch,
    Znth (lit_var_c watch) (mt_levels (ms_core M)) 0 = 0 ->
    lit_neg_c watch <> focus).
  { intros watch Hzero Heq. apply (f_equal lit_var_c) in Heq.
    rewrite lit_var_c_neg in Heq. rewrite <- Heq in Hpositive. lia. }
  split; intros Hprocessed Hzero.
  - apply Hleft; [apply Hdifferent; exact Hzero|exact Hprocessed|exact Hzero].
  - apply Hright; [apply Hdifferent; exact Hzero|exact Hprocessed|exact Hzero].
Qed.

Lemma minisat_base_exception_at_depth_zero__api_reentry : forall n M focus,
  mtrail_wf n (ms_core M) -> db_wf n (msolver_db M) ->
  Zlength (mt_lim (ms_core M)) = 0 ->
  minisat_base_watch_completed_except M focus ->
  minisat_watch_completed_except M focus.
Proof.
  intros n M focus Hwf Hdb Hdepth Hbase owner co Hin.
  pose proof (db_wf_obj n (msolver_db M) owner co Hdb Hin) as Hobj.
  destruct (Hbase owner co Hin) as [Hleft Hright].
  pose proof (processed_watch_level_zero_at_depth_zero__api_reentry
    n (ms_core M) Hwf Hdepth) as Hzero.
  split; intros Hneq Hprocessed.
  - pose proof (Hzero (co_watch0 co) (obj_wf_watch0 n co Hobj) Hprocessed) as Hwzero.
    destruct (Hleft Hneq Hprocessed Hwzero) as [Htrue Hother].
    split; [exact Htrue|lia].
  - pose proof (Hzero (co_watch1 co) (obj_wf_watch1 n co Hobj) Hprocessed) as Hwzero.
    destruct (Hright Hneq Hprocessed Hwzero) as [Htrue Hother].
    split; [exact Htrue|lia].
Qed.

Lemma base_completed_watch_enqueue_fresh__api_reentry :
  forall n t q watch other,
    mtrail_wf n t ->
    lit_wf_c n q -> lit_wf_c n watch -> lit_wf_c n other ->
    Znth (lit_var_c q) (mt_assigns t) 0 = 0 ->
    (processed (mt_assigns t) (mt_trail t) (mt_qhead t)
       (lit_neg_c watch) ->
     Znth (lit_var_c watch) (mt_levels t) 0 = 0 ->
     lit_true (mt_assigns t) other /\
     Znth (lit_var_c other) (mt_levels t) 0 = 0) ->
    processed (mt_assigns (mt_enqueue t q)) (mt_trail (mt_enqueue t q))
      (mt_qhead (mt_enqueue t q)) (lit_neg_c watch) ->
    Znth (lit_var_c watch) (mt_levels (mt_enqueue t q)) 0 = 0 ->
    lit_true (mt_assigns (mt_enqueue t q)) other /\
    Znth (lit_var_c other) (mt_levels (mt_enqueue t q)) 0 = 0.
Proof.
  intros n t q watch other Htrail Hq Hwatch Hother Hfresh Hcomplete Hnew Hzero.
  pose proof (proj1 (processed_enqueue_fresh_equiv__propagate_dbu
    n t q Htrail Hq Hfresh) (lit_neg_c watch)
    (lit_neg_c_wf n watch Hwatch) Hnew) as Hold.
  pose proof (processed_fresh_target_different
    (mt_assigns t) (mt_trail t) (mt_qhead t)
    (lit_neg_c watch) q Hold Hfresh) as Hqwatch.
  rewrite lit_var_c_neg in Hqwatch.
  pose proof (lit_var_c_in_range n q Hq) as Hqrange.
  pose proof (lit_var_c_in_range n watch Hwatch) as Hwatchrange.
  pose proof (lit_var_c_in_range n other Hother) as Hotherrange.
  assert (Holdzero : Znth (lit_var_c watch) (mt_levels t) 0 = 0).
  { unfold mt_enqueue, mt_push in Hzero. cbn [mt_levels] in Hzero.
    rewrite Znth_replace_Znth_Diff in Hzero
      by (try rewrite (mtw_levels_len Htrail); assumption).
    exact Hzero. }
  destruct (Hcomplete Hold Holdzero) as [Htrue Hlevel].
  assert (Hqother : lit_var_c q <> lit_var_c other).
  { intro Heq. apply (lit_true_assigned (mt_assigns t) other Htrue).
    rewrite <- Heq. exact Hfresh. }
  unfold mt_enqueue, mt_push. cbn [mt_assigns mt_levels]. split.
  - unfold lit_true in Htrue |- *.
    rewrite Znth_replace_Znth_Diff
      by (try rewrite (mtw_assigns_len Htrail); assumption).
    exact Htrue.
  - rewrite Znth_replace_Znth_Diff
      by (try rewrite (mtw_levels_len Htrail); assumption).
    exact Hlevel.
Qed.

Lemma minisat_base_watch_completed_enqueue_fresh__api_reentry :
  forall n M q reason_word reason_opt,
    db_wf n (msolver_db M) -> mtrail_wf n (ms_core M) ->
    lit_wf_c n q ->
    Znth (lit_var_c q) (mt_assigns (ms_core M)) 0 = 0 ->
    minisat_base_watch_completed M ->
    minisat_base_watch_completed
      (msolver_enqueue_fresh M q reason_word reason_opt).
Proof.
  intros n M q reason_word reason_opt Hdb Hwf Hq Hfresh Hcomplete owner co Hin.
  change (In (owner,co) (msolver_db M)) in Hin.
  pose proof (db_wf_obj n (msolver_db M) owner co Hdb Hin) as Hobj.
  pose proof (obj_wf_watch0 n co Hobj) as Hw0.
  pose proof (obj_wf_watch1 n co Hobj) as Hw1.
  destruct (Hcomplete owner co Hin) as [Hleft Hright].
  cbn [msolver_enqueue_fresh ms_core]. split;
    eapply base_completed_watch_enqueue_fresh__api_reentry; eassumption.
Qed.

Lemma minisat_base_watch_completed_except_enqueue_fresh__api_reentry :
  forall n M focus q reason_word reason_opt,
    db_wf n (msolver_db M) -> mtrail_wf n (ms_core M) ->
    lit_wf_c n q -> Znth (lit_var_c q) (mt_assigns (ms_core M)) 0 = 0 ->
    minisat_base_watch_completed_except M focus ->
    minisat_base_watch_completed_except
      (msolver_enqueue_fresh M q reason_word reason_opt) focus.
Proof.
  intros n M focus q reason_word reason_opt Hdb Hwf Hq Hfresh Hcomplete owner co Hin.
  change (In (owner,co) (msolver_db M)) in Hin.
  pose proof (db_wf_obj n (msolver_db M) owner co Hdb Hin) as Hobj.
  pose proof (obj_wf_watch0 n co Hobj) as Hw0.
  pose proof (obj_wf_watch1 n co Hobj) as Hw1.
  destruct (Hcomplete owner co Hin) as [Hleft Hright].
  cbn [msolver_enqueue_fresh ms_core].
  split; intro Hneq; eapply base_completed_watch_enqueue_fresh__api_reentry;
    try eassumption.
  - apply Hleft. exact Hneq.
  - apply Hright. exact Hneq.
Qed.

Lemma minisat_base_watch_completed_except_enqueue_success__api_reentry :
  forall n M focus q reason_word reason_clause,
    db_wf n (msolver_db M) -> mtrail_wf n (ms_core M) -> lit_wf_c n q ->
    minisat_base_watch_completed_except M focus ->
    minisat_base_watch_completed_except
      (msolver_propagation_enqueue_success M q reason_word reason_clause) focus.
Proof.
  intros n M focus q reason_word reason_clause Hdb Hwf Hq Hcomplete.
  unfold msolver_propagation_enqueue_success.
  destruct (Znth (lit_var_c q) (mt_assigns (ms_core M)) 0 =? 0) eqn:Hfresh;
    [|exact Hcomplete].
  apply Z.eqb_eq in Hfresh.
  change (minisat_base_watch_completed_except
    (msolver_enqueue_fresh M q reason_word (Some reason_clause)) focus).
  eapply minisat_base_watch_completed_except_enqueue_fresh__api_reentry; eassumption.
Qed.

Lemma base_completed_partner_enqueue_fresh__api_reentry : forall n t focus q other,
  mtrail_wf n t -> lit_wf_c n focus -> lit_wf_c n q -> lit_wf_c n other ->
  processed (mt_assigns t) (mt_trail t) (mt_qhead t) focus ->
  Znth (lit_var_c q) (mt_assigns t) 0 = 0 ->
  (Znth (lit_var_c focus) (mt_levels t) 0 = 0 ->
    lit_true (mt_assigns t) other /\ Znth (lit_var_c other) (mt_levels t) 0 = 0) ->
  Znth (lit_var_c focus) (mt_levels (mt_enqueue t q)) 0 = 0 ->
  lit_true (mt_assigns (mt_enqueue t q)) other /\
    Znth (lit_var_c other) (mt_levels (mt_enqueue t q)) 0 = 0.
Proof.
  intros n t focus q other Hwf Hfocus Hq Hother Hprocessed Hfresh Hdone Hzero.
  pose proof (proj2 (processed_enqueue_fresh_equiv__propagate_dbu n t q Hwf Hq Hfresh)
    focus Hfocus Hprocessed) as Hnew.
  eapply (base_completed_watch_enqueue_fresh__api_reentry
    n t q (lit_neg_c focus) other);
    [exact Hwf|exact Hq|apply lit_neg_c_wf; exact Hfocus|exact Hother|exact Hfresh| | |].
  - intros Hold Hlevel. rewrite lit_var_c_neg in Hlevel. apply Hdone. exact Hlevel.
  - rewrite lit_neg_c_involutive. exact Hnew.
  - rewrite lit_var_c_neg. exact Hzero.
Qed.

Lemma learned_tail_positive_watch1__record : forall n M words,
  mtrail_wf n (ms_core M) -> learned_tail_positive n M words ->
  record_watch1_positive M words.
Proof.
  intros n M words Hwf Hpositive Hlen.
  destruct words as [|head [|watch rest]];
    cbn in Hlen; try lia.
  unfold learned_tail_positive in Hpositive; cbn [tl lits_denote] in Hpositive.
  destruct (Forall_inv Hpositive) as [d [Hlevel Hpos]].
  pose proof (level_of_msolver_view_levels__analyze
    n M (literal_var (lit_denote watch)) d Hwf Hlevel) as Harray.
  rewrite lit_var_c_denote in Harray.
  change (0 < Znth (lit_var_c watch) (mt_levels (ms_core M)) 0).
  rewrite Harray. exact Hpos.
Qed.

Lemma record_watch1_positive_cancel__record :
  forall M words level orderpos order root,
  record_watch1_positive M words ->
  record_watch1_positive
    (msolver_cancel_project M level orderpos order root) words.
Proof.
  intros M words level orderpos order root Hpositive.
  exact Hpositive.
Qed.

Lemma minisat_base_completed_install_learnt__record : forall M c words,
  minisat_base_watch_completed M ->
  Znth (lit_var_c (Znth 0 words 0)) (mt_assigns (ms_core M)) 0 = 0 ->
  0 < Znth (lit_var_c (Znth 1 words 0)) (mt_levels (ms_core M)) 0 ->
  minisat_base_watch_completed (msolver_install_learnt_clause M c words).
Proof.
  intros M c words Hbase Hfresh Hpositive owner co Hin.
  rewrite msolver_install_learnt_clause_gen in Hin |- *.
  rewrite msolver_db_install_learnt_eq in Hin.
  rewrite ms_core_install.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - exact (Hbase owner co Hin).
  - destruct Hin as [Heq|[]]. inversion Heq; subst owner co.
    cbn [co_watch0 co_watch1 clause_obj_of]. split.
    + intros [Htrue _] Hzero. exfalso.
      change (lit_true (mt_assigns (ms_core M))
        (lit_neg_c (Znth 0 words 0))) in Htrue.
      unfold lit_true in Htrue. rewrite lit_var_c_neg, Hfresh in Htrue.
      pose proof (lit_sig_nonzero (lit_neg_c (Znth 0 words 0))). congruence.
    + intros Hprocessed Hzero.
      change (Znth (lit_var_c (Znth 1 words 0))
        (mt_levels (ms_core M)) 0 = 0) in Hzero. lia.
Qed.

Lemma record_allocated_base_completion__record :
  forall n F A_arr A_inst entry words c current,
  record_allocated n F A_arr A_inst entry words c current ->
  minisat_base_watch_completed entry -> record_watch1_positive entry words ->
  minisat_base_watch_completed current.
Proof.
  intros n F A_arr A_inst entry words c current Hallocated Hbase Hpositive.
  destruct Hallocated as [Hkind [Hcert _]].
  destruct Hkind as [[Hlen [Hzero ->]]|[Hlen [Hnonzero Hsuccess]]].
  - exact Hbase.
  - destruct Hsuccess as [Hfresh [Hcurrent _]].
    subst current. apply minisat_base_completed_install_learnt__record.
    + exact Hbase.
    + unfold record_clause_cert, record_ready_cert in Hcert.
      destruct Hcert as [_ [_ [_ [_ [Hhead _]]]]]. exact Hhead.
    + exact (Hpositive Hlen).
Qed.

Lemma solver_level_zero_assuming__api_reentry : forall n F A A_inst M,
  msolver_inv n F A A_inst M ->
  Zlength (mt_lim (ms_core M)) = 0 ->
  msolver_inv_assuming_strong n F A A M.
Proof.
  intros n F A A_inst M Hinv Hlim.
  assert (Hatroot : solver_at_root M).
  { pose proof (msi_root_range Hinv). unfold solver_at_root. lia. }
  constructor.
  - apply msolver_inv_weak_assuming with (A_inst := A_inst);
      [exact (msi_weak Hinv)|exact Hatroot].
  - exact (msi_prop_level Hinv).
  - exact (msi_watch_frontier Hinv).
  - exact (msi_heap_covers Hinv).
  - exact (msi_reasonless_current Hinv).
Qed.

Lemma solver_assuming_level_zero_normalized__api_reentry : forall n F A M,
  msolver_inv_assuming_strong n F A A M ->
  Zlength (mt_lim (ms_core M)) = 0 ->
  msolver_inv n F A [] (msolver_set_root M 0).
Proof.
  intros n F A M Hstrong Hlim.
  pose proof (msas_weak Hstrong) as Hweak.
  pose proof (msolver_inv_ctx_root_empty__canceluntil_cap
    n F A (PropagationAssuming A) M Hweak Hlim) as Hempty.
  assert (Hfull : msolver_inv_weak n F A [] (msolver_set_root M 0)).
  { pose proof (msa_A_wf Hweak) as HAwf.
    pose proof (msa_proc_sat Hweak) as Hsat. rewrite Hlim in Hsat.
    destruct Hempty. constructor; try assumption.
    intros a Hin. inversion Hin. }
  constructor.
  - exact Hfull.
  - exact (msas_prop_level Hstrong).
  - exact (msas_watch_frontier Hstrong).
  - exact (msas_heap_covers Hstrong).
  - apply current_reasonless_earliest_no_levels; [exact Hlim|].
    change (0 <= 0). lia.
Qed.

Lemma solver_assuming_level_zero_physical__api_reentry : forall n F A M,
  msolver_inv n F A [] (msolver_set_root M 0) ->
  solver_shape M ->
  Zlength (mt_lim (ms_core M)) = 0 ->
  msolver_inv_assuming_strong n F A A M.
Proof.
  intros n F A M Hnormal Hshape Hlim.
  assert (Hatroot : solver_at_root (msolver_set_root M 0)).
  { change (Zlength (mt_lim (ms_core M)) = 0). exact Hlim. }
  pose proof (msolver_inv_weak_assuming n F A [] (msolver_set_root M 0)
    (msi_weak Hnormal) Hatroot) as Hweak.
  constructor.
  - destruct Hweak. constructor; assumption.
  - exact (msi_prop_level Hnormal).
  - exact (msi_watch_frontier Hnormal).
  - exact (msi_heap_covers Hnormal).
  - apply current_reasonless_earliest_no_levels; [exact Hlim|].
    unfold solver_shape in Hshape. tauto.
Qed.

Lemma solver_installed_assumptions_at_zero__api_reentry : forall n F A A_inst M,
  msolver_inv n F A A_inst M ->
  Zlength (mt_lim (ms_core M)) = 0 -> A_inst = [].
Proof.
  intros n F A A_inst M Hinv Hdepth.
  pose proof (msi_root_range Hinv) as Hrange.
  assert (Hroot : ms_root_level M = 0) by lia.
  pose proof (msw_assumptions (msi_weak Hinv)) as Hinst.
  rewrite Hroot in Hinst. unfold decisions_upto, ztake in Hinst.
  cbn in Hinst. symmetry. exact Hinst.
Qed.

Lemma solver_assuming_zero_stable__api_reentry : forall n F A M,
  msolver_inv_assuming_strong n F A A M ->
  Zlength (mt_lim (ms_core M)) = 0 -> ms_root_level M = 0 ->
  msolver_inv n F A [] M.
Proof.
  intros n F A M Hinv Hdepth Hroot.
  pose proof (solver_assuming_level_zero_normalized__api_reentry
    n F A M Hinv Hdepth) as Hnormal.
  assert (Heq : msolver_set_root M 0 = M).
  { rewrite <- Hroot. destruct M. reflexivity. }
  rewrite Heq in Hnormal. exact Hnormal.
Qed.

Lemma solver_assuming_remove_problem_at_zero__api_reentry :
  forall n F A M c co pre post wm stats,
    msolver_inv_assuming_strong n F A A M ->
    Zlength (mt_lim (ms_core M)) = 0 ->
    ms_prob M = pre ++ (c,co) :: post ->
    ~ In c (map fst pre) ->
    clause_remove_result c (co_lits co) (ms_wm M) wm ->
    Zlength stats = 11 ->
    clause_unlocked_words c (ms_reason_words M) ->
    root_satisfied (ms_core M) (denote_obj co) ->
    msolver_inv_assuming_strong n F A A
      (msolver_remove_clause M false c wm stats).
Proof.
  intros n F A M c co pre post wm stats Hinv Hdepth
    Hsplit Hfresh Hremove Hstats Hunlocked Hsat.
  pose proof (solver_assuming_level_zero_normalized__api_reentry
    n F A M Hinv Hdepth) as Hnormal.
  apply solver_assuming_level_zero_physical__api_reentry.
  - change (msolver_inv n F A []
      (msolver_remove_clause (msolver_set_root M 0) false c wm stats)).
    eapply msolver_inv_remove_problem__simplify;
      [exact Hnormal|exact Hsplit|exact Hfresh|exact Hremove|
       exact Hstats|exact Hunlocked|exact Hsat].
  - apply solver_shape_remove_problem__simplify;
      [exact (msa_shape (msas_weak Hinv))| |exact Hstats].
    rewrite (clause_remove_result_length__reducedb _ _ _ _ Hremove).
    apply solver_shape_wm_len. exact (msa_shape (msas_weak Hinv)).
  - exact Hdepth.
Qed.

Lemma solver_assuming_remove_learnt_at_zero__api_reentry :
  forall n F A M c co pre post wm stats,
    msolver_inv_assuming_strong n F A A M ->
    Zlength (mt_lim (ms_core M)) = 0 ->
    ms_learnt M = pre ++ (c,co) :: post ->
    ~ In c (map fst pre) ->
    clause_remove_result c (co_lits co) (ms_wm M) wm ->
    Zlength stats = 11 ->
    clause_unlocked_words c (ms_reason_words M) ->
    msolver_inv_assuming_strong n F A A
      (msolver_remove_clause M true c wm stats).
Proof.
  intros n F A M c co pre post wm stats Hinv Hdepth
    Hsplit Hfresh Hremove Hstats Hunlocked.
  pose proof (solver_assuming_level_zero_normalized__api_reentry
    n F A M Hinv Hdepth) as Hnormal.
  apply solver_assuming_level_zero_physical__api_reentry.
  - change (msolver_inv n F A []
      (msolver_remove_clause (msolver_set_root M 0) true c wm stats)).
    eapply msolver_inv_remove_learnt__reducedb;
      [exact Hnormal|exact Hsplit|exact Hfresh|exact Hremove|
       exact Hstats|exact Hunlocked].
  - apply solver_shape_remove_clause__reducedb;
      [exact (msa_shape (msas_weak Hinv))| |exact Hstats].
    rewrite (clause_remove_result_length__reducedb _ _ _ _ Hremove).
    apply solver_shape_wm_len. exact (msa_shape (msas_weak Hinv)).
  - exact Hdepth.
Qed.

Lemma solver_assuming_simpdb_update__api_reentry : forall n F A M a p,
  msolver_inv_assuming_strong n F A A M ->
  msolver_inv_assuming_strong n F A A (msolver_simpdb_update M a p).
Proof.
  intros n F A M a p [Hweak Hprop Hfront Hcovers Hreasonless].
  constructor.
  - destruct Hweak; constructor; cbn [msolver_simpdb_update] in *; assumption.
  - exact Hprop.
  - exact Hfront.
  - exact Hcovers.
  - exact Hreasonless.
Qed.

Definition clause_new_stage_ready_root
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry current : msolver) (words : list Z) (sel root : Z) : Prop :=
  solver_shape current /\
  2 <= Zlength words /\ 2 * Zlength words + 1 <= INT_MAX /\
  current = entry /\
  solver_support_inv n F A_arr A_inst root current /\
  ms_capacity_root_propagation_pending current = 0 /\
  msolver_seed_shadow current /\
  clause_install_pending_cert n F (msolver_set_root current root) words
    (solver_selected_is_learnt sel).


Definition clause_new_success_transition_root
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (words : list Z) (c sel root : Z)
    (M' : msolver) : Prop :=
    clause_allocator_fresh entry c /\
    M' = msolver_install_clause entry c words (solver_selected_is_learnt sel) /\
    solver_support_inv n (cn_F F words sel) A_arr A_inst root M' /\
    ms_capacity_root_propagation_pending M' = 0 /\
    msolver_seed_shadow M' /\
    clause_install_cert n (cn_F F words sel) (msolver_set_root M' root)
      words (solver_selected_is_learnt sel).


Lemma msolver_set_root_self__api_reentry : forall M,
  msolver_set_root M (ms_root_level M) = M.
Proof. intros M. destruct M. reflexivity. Qed.


Lemma msolver_set_root_install_clause__api_reentry :
  forall M c words learnt root,
    msolver_set_root (msolver_install_clause M c words learnt) root =
    msolver_install_clause (msolver_set_root M root) c words learnt.
Proof. intros. destruct learnt; reflexivity. Qed.


Lemma msolver_set_root_addclause_finish__api_reentry : forall M words root,
  msolver_set_root (msolver_addclause_finish M words) root =
  msolver_addclause_finish (msolver_set_root M root) words.
Proof. intros. reflexivity. Qed.


Lemma msolver_set_root_enqueue_fresh__api_reentry : forall M l r ro root,
  msolver_set_root (msolver_enqueue_fresh M l r ro) root =
  msolver_enqueue_fresh (msolver_set_root M root) l r ro.
Proof. intros. reflexivity. Qed.


Definition addclause_support_transition
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (input : list Z) (ret : Z)
    (M : msolver) (current : list Z) (F' : cnf) : Prop :=
  addclause_transition n F A_arr A_inst (msolver_set_root entry 0)
    input ret (msolver_set_root M 0) current F' /\
  (minisat_watch_completed entry -> minisat_watch_completed M).


Definition addclause_support_post_at
    (s begin n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (input : list Z) (ret : Z) : Assertion :=
  EX M : msolver, EX current : list Z, EX F' : cnf,
    “ addclause_support_transition n F A_arr A_inst entry input ret
        M current F' ” &&
    (solver_rep_growable s M **
     IntArray.seg begin 0 (Zlength input) current).


Lemma solver_support_inv_addclause_finish__api_reentry :
  forall n F A_arr A_inst root M words,
    solver_support_inv n F A_arr A_inst root M ->
    solver_support_inv n F A_arr A_inst root
      (msolver_addclause_finish M words).
Proof.
  intros n F A_arr A_inst root M words Hinv.
  unfold solver_support_inv in *.
  rewrite msolver_set_root_addclause_finish__api_reentry.
  apply msolver_inv_addclause_finish. exact Hinv.
Qed.


Lemma clause_new_success_root_bounds__api_reentry :
  forall n F A_arr A_inst entry words c sel root M,
    clause_new_success_transition_root n F A_arr A_inst entry words c sel root M ->
    ms_size M = ms_size entry /\ ms_cap M = ms_cap entry.
Proof.
  intros n F A_arr A_inst entry words c sel root M
    (Hfresh & Hinstall & Hinv & Hpending & Hseed & Hcert).
  rewrite Hinstall, ms_size_install, ms_cap_install_clause.
  split; reflexivity.
Qed.


Lemma solver_support_inv_install_clause__api_reentry :
  forall n F A_arr A_inst root M c words sel,
    0 <= sel <= 1 ->
    solver_support_inv n F A_arr A_inst root M ->
    clause_allocator_fresh M c ->
    clause_install_pending_cert n F (msolver_set_root M root) words
      (solver_selected_is_learnt sel) ->
    2 <= Zlength words ->
    lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
    0 <= lit_neg_c (Znth 0 words 0) < 2 * n ->
    0 <= lit_neg_c (Znth 1 words 0) < 2 * n ->
    solver_support_inv n (cn_F F words sel) A_arr A_inst root
      (msolver_install_clause M c words (solver_selected_is_learnt sel)).
Proof.
  intros n F A_arr A_inst root M c words sel
    Hsel Hinv Hfresh Hcert Hlen Hdistinct Hi Hj.
  unfold solver_support_inv in *.
  rewrite msolver_set_root_install_clause__api_reentry.
  apply msolver_inv_install_gen; assumption.
Qed.


Lemma clause_install_cert_at_root__api_reentry :
  forall n F M c words sel root,
    0 <= sel <= 1 ->
    clause_install_pending_cert n F (msolver_set_root M root) words
      (solver_selected_is_learnt sel) ->
    clause_install_cert n (cn_F F words sel)
      (msolver_set_root
        (msolver_install_clause M c words (solver_selected_is_learnt sel)) root)
      words (solver_selected_is_learnt sel).
Proof.
  intros n F M c words sel root Hsel Hcert.
  rewrite msolver_set_root_install_clause__api_reentry.
  apply clause_install_cert_install_gen; assumption.
Qed.


Lemma solver_support_inv_addclause_unit__api_reentry :
  forall n F A_arr A_inst root M l,
    solver_support_inv n F A_arr A_inst root M ->
    lit_wf_c n l ->
    Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 = 0 ->
    Zlength (mt_lim (ms_core M)) = 0 ->
    ms_qtail M < ms_cap M ->
    ms_capacity_root_propagation_pending M = 0 ->
    solver_support_inv n (F ++ [[lit_denote l]]) A_arr A_inst root
      (msolver_enqueue_fresh M l 0 None).
Proof.
  intros n F A_arr A_inst root M l Hinv Hl Hfresh Hdepth Hroom Hpending.
  unfold solver_support_inv in *.
  rewrite msolver_set_root_enqueue_fresh__api_reentry.
  apply msolver_inv_addclause_unit_enqueue; assumption.
Qed.


Lemma addclause_support_post_empty__api_reentry :
  forall s begin n F A_arr A_inst M,
    2 * ms_cap M <= INT_MAX ->
    solver_support_inv (ms_size M) F A_arr A_inst 0 M ->
    solver_rep_growable s M ** IntArray.seg begin 0 (Zlength (@nil Z)) nil |--
    addclause_support_post_at s begin n F A_arr A_inst M nil 0.
Proof.
  intros s begin n F A_arr A_inst M Hcap Hinv.
  unfold addclause_support_post_at. Exists M (@nil Z) F.
  split_pure_spatial; [cancel |].
  dump_pre_spatial. unfold addclause_support_transition.
  split; [unfold addclause_transition | intros H; exact H].
  split; [reflexivity |]. split; [lia |]. split; [lia |].
  split; [exact Hcap |]. split; [intros H; exact H |].
  left. split; [reflexivity |]. split; [reflexivity |].
  split; [exact Hinv |]. apply addclause_empty_unsat.
  - apply addclause_formula_wf;
      [exact (msw_F_wf (msi_weak Hinv)) | constructor].
  - apply addclause_prefix_nil.
Qed.


Lemma minisat_watch_completed_addclause_finish__api_reentry :
  forall M words,
    minisat_watch_completed M ->
    minisat_watch_completed (msolver_addclause_finish M words).
Proof. intros M words Hcomplete. exact Hcomplete. Qed.


Lemma minisat_watch_completed_heap_project__api_reentry :
  forall M orderpos order,
    minisat_watch_completed M ->
    minisat_watch_completed (msolver_heap_project M orderpos order).
Proof.
  intros M orderpos order H. unfold minisat_watch_completed in *.
  exact H.
Qed.


Lemma minisat_watch_completed_set_cap__api_reentry : forall M cap,
  minisat_watch_completed M ->
  minisat_watch_completed (msolver_set_cap M cap).
Proof.
  intros M cap H. unfold minisat_watch_completed in *. exact H.
Qed.


Lemma minisat_watch_completed_add_var__api_reentry :
  forall n M a0,
    mtrail_wf n (ms_core M) ->
    db_wf n (msolver_db M) ->
    minisat_watch_completed M ->
    minisat_watch_completed (msolver_add_var M a0).
Proof.
  intros n M a0 Htrail [_ [_ Hobjs]] Hcomplete.
  assert (Htrue : forall l, lit_wf_c n l ->
    (lit_true (mt_assigns (ms_core M) ++ (0 :: nil)) l <->
     lit_true (mt_assigns (ms_core M)) l)).
  { intros l Hl. unfold lit_true.
    rewrite app_Znth1.
    - reflexivity.
    - rewrite (mtw_assigns_len Htrail).
      exact (lit_var_c_in_range n l Hl). }
  assert (Hprocessed : forall l, lit_wf_c n l ->
    (processed (mt_assigns (ms_core M) ++ (0 :: nil))
       (mt_trail (ms_core M)) (mt_qhead (ms_core M)) l <->
     processed (mt_assigns (ms_core M))
       (mt_trail (ms_core M)) (mt_qhead (ms_core M)) l)).
  { intros l Hl. unfold processed. rewrite (Htrue l Hl). reflexivity. }
  unfold minisat_watch_completed.
  rewrite msolver_add_var_db.
  cbn [ms_core msolver_add_var mt_assigns mt_levels mt_trail mt_qhead
       mtrail_add_var].
  intros p co Hin.
  rewrite Forall_forall in Hobjs.
  pose proof (Hobjs (p, co) Hin) as Hobj. cbn in Hobj.
  pose proof (obj_wf_watch0 n co Hobj) as Hw0.
  pose proof (obj_wf_watch1 n co Hobj) as Hw1.
  pose proof (lit_var_c_in_range n (co_watch0 co) Hw0) as Hvar0.
  pose proof (lit_var_c_in_range n (co_watch1 co) Hw1) as Hvar1.
  rewrite (Hprocessed _ (lit_neg_c_wf n _ Hw0)).
  rewrite (Hprocessed _ (lit_neg_c_wf n _ Hw1)).
  rewrite (Htrue _ Hw0), (Htrue _ Hw1).
  rewrite !app_Znth1 by (rewrite (mtw_levels_len Htrail); lia).
  exact (Hcomplete p co Hin).
Qed.


Lemma minisat_watch_completed_subdatabase__api_reentry : forall M M',
  ms_core M' = ms_core M ->
  incl (msolver_db M') (msolver_db M) ->
  minisat_watch_completed M -> minisat_watch_completed M'.
Proof.
  intros M M' Hcore Hdb Hcomplete p co Hin.
  unfold minisat_watch_completed in Hcomplete.
  rewrite Hcore. apply (Hcomplete p co). apply Hdb. exact Hin.
Qed.

Lemma db_remove_ptr_incl__api_reentry : forall current db,
  incl (db_remove_ptr current db) db.
Proof.
  intros current db. induction db as [|[p co] rest IH]; intros entry Hin; cbn in Hin.
  - contradiction.
  - destruct (Z.eq_dec p current).
    + right. exact Hin.
    + destruct Hin as [Heq|Hin]; [left; exact Heq|].
      right. apply IH. exact Hin.
Qed.

Lemma msolver_remove_clause_db_incl__api_reentry : forall M learnt current wm stats,
  incl (msolver_db (msolver_remove_clause M learnt current wm stats)) (msolver_db M).
Proof.
  intros M learnt current wm stats. destruct learnt; unfold msolver_db; cbn;
    apply incl_app_app; auto using incl_refl, db_remove_ptr_incl__api_reentry.
Qed.

Lemma minisat_watch_completed_remove_clause__api_reentry :
  forall M learnt current wm stats,
    minisat_watch_completed M ->
    minisat_watch_completed (msolver_remove_clause M learnt current wm stats).
Proof.
  intros M learnt current wm stats Hcomplete.
  apply minisat_watch_completed_subdatabase__api_reentry with (M := M).
  - reflexivity.
  - apply msolver_remove_clause_db_incl__api_reentry.
  - exact Hcomplete.
Qed.

Lemma minisat_base_watch_completed_subdatabase__api_reentry : forall M M',
  ms_core M' = ms_core M ->
  incl (msolver_db M') (msolver_db M) ->
  minisat_base_watch_completed M -> minisat_base_watch_completed M'.
Proof.
  intros M M' Hcore Hdb Hcomplete p co Hin.
  unfold minisat_base_watch_completed in Hcomplete.
  rewrite Hcore. apply (Hcomplete p co). apply Hdb. exact Hin.
Qed.

Lemma minisat_base_watch_completed_remove_clause__api_reentry :
  forall M learnt current wm stats,
    minisat_base_watch_completed M ->
    minisat_base_watch_completed (msolver_remove_clause M learnt current wm stats).
Proof.
  intros M learnt current wm stats Hcomplete.
  apply minisat_base_watch_completed_subdatabase__api_reentry with (M := M).
  - reflexivity.
  - apply msolver_remove_clause_db_incl__api_reentry.
  - exact Hcomplete.
Qed.

Lemma minisat_base_watch_completed_reorder_learnts__api_reentry :
  forall M learnt,
    Permutation (ms_learnt M) learnt ->
    minisat_base_watch_completed M ->
    minisat_base_watch_completed (msolver_reorder_learnts M learnt).
Proof.
  intros M learnt Hperm Hcomplete.
  apply minisat_base_watch_completed_subdatabase__api_reentry with (M := M).
  - reflexivity.
  - intros entry Hin. change (In entry (ms_prob M ++ learnt)) in Hin.
    unfold msolver_db. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [Hin|Hin]; [left; exact Hin|right].
    eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hin].
  - exact Hcomplete.
Qed.


Lemma minisat_watch_completed_install_problem__api_reentry :
  forall M current words,
    minisat_watch_completed M ->
    Znth (lit_var_c (Znth 0 words 0)) (mt_assigns (ms_core M)) 0 = 0 ->
    Znth (lit_var_c (Znth 1 words 0)) (mt_assigns (ms_core M)) 0 = 0 ->
    minisat_watch_completed (msolver_install_clause M current words false).
Proof.
  intros M current words Hcomplete Hhead Hnext p co Hin.
  change (In (p, co)
    ((ms_prob M ++ [(current, clause_obj_of words false)]) ++ ms_learnt M)) in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - apply in_app_or in Hin. destruct Hin as [Hin|[Heq|Hin]].
    + apply (Hcomplete p co). unfold msolver_db. apply in_or_app. left. exact Hin.
    + injection Heq as Hcurrent Hco. subst p co.
      split; intros [Htrue _]; exfalso.
      * change (Znth (lit_var_c (lit_neg_c (Znth 0 words 0)))
          (mt_assigns (ms_core M)) 0 = lit_sig (lit_neg_c (Znth 0 words 0))) in Htrue.
        rewrite lit_var_c_neg, Hhead in Htrue.
        exact (lit_sig_nonzero _ (eq_sym Htrue)).
      * change (Znth (lit_var_c (lit_neg_c (Znth 1 words 0)))
          (mt_assigns (ms_core M)) 0 = lit_sig (lit_neg_c (Znth 1 words 0))) in Htrue.
        rewrite lit_var_c_neg, Hnext in Htrue.
        exact (lit_sig_nonzero _ (eq_sym Htrue)).
    + contradiction.
  - apply (Hcomplete p co). unfold msolver_db. apply in_or_app. right. exact Hin.
Qed.


Lemma clause_new_problem_completed__api_reentry :
  forall n F A_arr A_inst entry words c root M,
    clause_new_success_transition_root n F A_arr A_inst entry words c 0 root M ->
    minisat_watch_completed entry -> minisat_watch_completed M.
Proof.
  intros n F A_arr A_inst entry words c root M
    (Hfresh & Hinstall & Hinv & Hpending & Hseed & Hcert)
    Hcomplete.
  change (problem_clause_cert n (F ++ [lits_denote words])
    (msolver_set_root M root) words) in Hcert.
  apply problem_clause_cert_pending in Hcert.
  assert (Hlen : 2 <= Zlength words).
  { unfold problem_clause_pending_cert in Hcert. tauto. }
  pose proof (pending_head_unassigned n (F ++ [lits_denote words])
    (msolver_set_root M root) words 0 ltac:(lia) Hcert) as Hhead.
  pose proof (pending_head_unassigned n (F ++ [lits_denote words])
    (msolver_set_root M root) words 1 ltac:(lia) Hcert) as Hnext.
  rewrite Hinstall in Hhead, Hnext |- *.
  apply minisat_watch_completed_install_problem__api_reentry.
  - exact Hcomplete.
  - exact Hhead.
  - exact Hnext.
Qed.


Lemma base_completed_watch_cancel__api_reentry : forall n t level watch other,
  mtrail_wf n t -> lit_wf_c n watch -> lit_wf_c n other ->
  0 <= level < Zlength (mt_lim t) ->
  Znth level (mt_lim t) 0 <= mt_qhead t ->
  (processed (mt_assigns t) (mt_trail t) (mt_qhead t) (lit_neg_c watch) ->
   Znth (lit_var_c watch) (mt_levels t) 0 = 0 ->
   lit_true (mt_assigns t) other /\ Znth (lit_var_c other) (mt_levels t) 0 = 0) ->
  processed (mt_assigns (mt_cancel t level)) (mt_trail (mt_cancel t level))
    (mt_qhead (mt_cancel t level)) (lit_neg_c watch) ->
  Znth (lit_var_c watch) (mt_levels (mt_cancel t level)) 0 = 0 ->
  lit_true (mt_assigns (mt_cancel t level)) other /\
  Znth (lit_var_c other) (mt_levels (mt_cancel t level)) 0 = 0.
Proof.
  intros n t level watch other Hwf Hw Ho Hlevel Hbound Hbase Hnew Hzero.
  rewrite mt_cancel_levels in Hzero.
  destruct (processed_cancel_prefix_level__api_reentry n t level (lit_neg_c watch)
    Hwf (lit_neg_c_wf n watch Hw) Hlevel Hbound Hnew) as [Hold Hbelow].
  destruct (Hbase Hold Hzero) as [Htrue Hother]. split.
  - exact (lit_true_cancel_below__api_reentry n t level other
      Hwf Ho Hlevel Htrue ltac:(lia)).
  - rewrite mt_cancel_levels. exact Hother.
Qed.

Lemma minisat_base_completion_cancel__api_reentry :
  forall n M level orderpos order root,
  mtrail_wf n (ms_core M) -> db_wf n (msolver_db M) ->
  0 <= level < Zlength (mt_lim (ms_core M)) ->
  Znth level (mt_lim (ms_core M)) 0 <= mt_qhead (ms_core M) ->
  minisat_base_watch_completed M ->
  minisat_base_watch_completed
    (msolver_cancel_project M level orderpos order root).
Proof.
  intros n M level orderpos order root Hwf Hdb Hlevel Hbound Hbase owner co Hin.
  change (In (owner,co) (msolver_db M)) in Hin.
  pose proof (db_wf_obj n (msolver_db M) owner co Hdb Hin) as Hobj.
  destruct (Hbase owner co Hin) as [Hleft Hright]. split.
  - exact (base_completed_watch_cancel__api_reentry n (ms_core M) level
      (co_watch0 co) (co_watch1 co) Hwf (obj_wf_watch0 n co Hobj)
      (obj_wf_watch1 n co Hobj) Hlevel Hbound Hleft).
  - exact (base_completed_watch_cancel__api_reentry n (ms_core M) level
      (co_watch1 co) (co_watch0 co) Hwf (obj_wf_watch1 n co Hobj)
      (obj_wf_watch0 n co Hobj) Hlevel Hbound Hright).
Qed.

Lemma record_enqueue_base_completion__record :
  forall n F A_arr A_inst entry words c current,
  record_allocated n F A_arr A_inst entry words c current ->
  minisat_base_watch_completed entry -> record_watch1_positive entry words ->
  minisat_base_watch_completed (msolver_record_enqueue current words c).
Proof.
  intros n F A_arr A_inst entry words c current Hallocated Hbase Hpositive.
  pose proof (record_allocated_base_completion__record
    n F A_arr A_inst entry words c current Hallocated Hbase Hpositive) as Hcurrent.
  destruct Hallocated as [_ [Hcert [Hinv _]]].
  unfold record_clause_cert, record_ready_cert in Hcert.
  destruct Hcert as [Hlen [Hwords [_ [_ [Hfresh _]]]]].
  unfold msolver_record_enqueue.
  exact (minisat_base_watch_completed_enqueue_fresh__api_reentry
    n current (Znth 0 words 0) c (record_reason_opt words c)
    (msw_db_wf (msi_weak Hinv)) (msw_trail_wf (msi_weak Hinv))
    (Forall_Znth_elim _ _ _ 0 0 Hwords ltac:(lia)) Hfresh Hcurrent).
Qed.

Lemma record_finish_base_completion__record : forall M words c cla_inc,
  minisat_base_watch_completed M ->
  minisat_base_watch_completed (msolver_record_finish M words c cla_inc).
Proof.
  intros M words c cla_inc Hbase.
  unfold msolver_record_finish. destruct (Z.eq_dec c 0); exact Hbase.
Qed.

Lemma record_enqueue_success_intro__record :
  forall n F A_arr A_inst entry words c M,
    record_allocated n F A_arr A_inst entry words c M ->
    record_enqueue_success n F A_arr A_inst entry M words c
      (msolver_record_enqueue M words c).
Proof.
  intros n F A_arr A_inst entry words c M Halloc0.
  pose proof Halloc0 as Halloc.
  destruct Halloc as
    [Hkind [Hcert [Hinv [Hq [Hpending [Hseed Hmodel]]]]]].
  assert (Hcapacity : ms_cap M = ms_cap entry).
  { destruct Hkind as [[_ [_ Hsame]] | [_ [_ Hnew]]].
    - subst M. reflexivity.
    - destruct Hnew as [_ [Hsame _]].
      subst M. reflexivity. }
  unfold record_enqueue_success.
  split.
  - reflexivity.
  - split.
    + eapply msolver_inv_record_enqueue__record. exact Halloc0.
    + split.
      * unfold msolver_record_enqueue, msolver_enqueue_fresh,
          msolver_propagation_overlay, msolver_propagation_update. cbn. exact Hpending.
      * split.
        -- unfold msolver_record_enqueue, msolver_enqueue_fresh,
             msolver_propagation_overlay, msolver_propagation_update. cbn. exact Hseed.
        -- split.
           ++ unfold msolver_record_enqueue, msolver_enqueue_fresh,
                msolver_propagation_overlay, msolver_propagation_update. cbn. exact Hmodel.
           ++ split.
              ** unfold msolver_record_enqueue, msolver_enqueue_fresh,
                   msolver_propagation_overlay, msolver_propagation_update. cbn.
                 eapply record_allocated_cla_decay__record. exact Halloc0.
              ** split; [exact Hcapacity|].
                 intros [Hbase Hpositive].
                 exact (record_enqueue_base_completion__record
                   n F A_arr A_inst entry words c M Halloc0 Hbase Hpositive).
Qed.


Lemma solver_propagation_conflict_base_recovery__api_reentry :
  forall n F A K M focus,
    propagation_cancel_ready n F A K M focus ->
    minisat_watch_conflict_ready n M ->
    minisat_resident_false_clause M ->
    Zlength (mt_lim (ms_core M)) = 0 ->
    solver_base_recovery n F M.
Proof.
  intros n F A K M focus Hready [watch_focus [Hlevel Hbase]] Hfalse Hdepth.
  destruct Hready as [[Hpending Hctx]
    [Hprop [Hfocus_wf [Hprocessed [Hfocus_level
      [Hold_frontier [Hheap_wf [Hcovers Hreason]]]]]]]].
  change (msolver_inv_ctx n F A K M) in Hctx.
  assert (Hdb_trail : db_wf n (msolver_db M) /\ mtrail_wf n (ms_core M)).
  { destruct K as [A_inst|A_proc]; cbn in Hctx.
    - split; [exact (msw_db_wf Hctx)|exact (msw_trail_wf Hctx)].
    - split; [exact (msa_db_wf Hctx)|exact (msa_trail_wf Hctx)]. }
  destruct Hdb_trail as [Hdb Htrail].
  pose proof (minisat_base_exception_at_depth_zero__api_reentry
    n M watch_focus Htrail Hdb Hdepth Hbase) as Hcomplete.
  pose proof (minisat_watch_completed_except_frontier__api_reentry
    n M watch_focus Hdb Hcomplete) as Hfrontier.
  pose proof (msolver_inv_ctx_root_empty__canceluntil_cap
    n F A K M Hctx Hdepth) as Hnormalized.
  assert (Hroot : solver_at_root (msolver_set_root M 0)).
  { change (Zlength (mt_lim (ms_core M)) = 0). exact Hdepth. }
  pose proof (msolver_inv_weak_assuming n F nil nil
    (msolver_set_root M 0) Hnormalized Hroot) as Hweak_normalized.
  assert (Hweak : msolver_inv_assuming n F nil nil M).
  { pose proof (msolver_inv_ctx_shape n F A K M Hctx) as Hshape.
    destruct Hweak_normalized. constructor; assumption. }
  unfold solver_base_recovery, solver_base_state.
  split.
  - split; [constructor; assumption|split; assumption].
  - right. exact Hfalse.
Qed.


Lemma minisat_base_watch_completed_scan_begin__api_reentry :
  forall M p simp props,
    p = Znth (mt_qhead (ms_core M)) (mt_trail (ms_core M)) 0 ->
    minisat_base_watch_completed M ->
    minisat_base_watch_completed_except (msolver_propagation_scan_begin M simp props) p.
Proof.
  intros M p simp props Hp Hcomplete owner co Hin.
  change (In (owner,co) (msolver_db M)) in Hin.
  destruct (Hcomplete owner co Hin) as [Hleft Hright].
  cbn [msolver_propagation_scan_begin msolver_propagation_scan
    msolver_propagation_update ms_core mt_set_qhead mt_assigns mt_levels mt_trail mt_qhead].
  split; intros Hneq Hprocessed Hzero.
  - apply Hleft; [eapply processed_dequeue_other__api_reentry; eassumption|exact Hzero].
  - apply Hright; [eapply processed_dequeue_other__api_reentry; eassumption|exact Hzero].
Qed.

Lemma minisat_base_scan_completed_initial__api_reentry : forall M focus pending,
  incl (expected_watchers (msolver_db M) focus) pending ->
  minisat_base_scan_completed M focus pending.
Proof.
  intros M focus pending Hpending word Habsent Hzero owner co Hin.
  assert (Hword : forall watch other,
    ((watch = co_watch0 co /\ other = co_watch1 co) \/
     (watch = co_watch1 co /\ other = co_watch0 co)) ->
    lit_neg_c watch = focus ->
    word = (if 3 <=? Zlength (co_lits co) then owner else tag_of_lit other) -> False).
  { intros watch other Hpair Hfocus Hvalue. apply Habsent. apply Hpending.
    unfold expected_watchers. apply in_flat_map. exists (owner,co).
    split; [exact Hin|]. unfold entry_watchers.
    destruct Hpair as [[Hw Ho]|[Hw Ho]]; subst watch other;
      apply in_or_app; [left|right]; rewrite Hfocus, Z.eqb_refl;
      left; symmetry; exact Hvalue. }
  split; intros Hfocus Hvalue; exfalso.
  - eapply Hword; [left; split; reflexivity|exact Hfocus|exact Hvalue].
  - eapply Hword; [right; split; reflexivity|exact Hfocus|exact Hvalue].
Qed.

Lemma minisat_base_scan_completed_advance__api_reentry : forall M focus word pending,
  minisat_base_scan_completed M focus (word :: pending) ->
  minisat_base_focus_word_completed M focus word ->
  minisat_base_scan_completed M focus pending.
Proof.
  intros M focus word pending Hold Hword candidate Habsent.
  destruct (Z.eq_dec candidate word) as [Heq|Hneq]; [subst; exact Hword|].
  apply Hold. intros [Heq|Hin]; [congruence|contradiction].
Qed.


Lemma minisat_base_focus_word_completed_binary__api_reentry : forall n M focus word,
  db_wf n (msolver_db M) -> is_tag word = true ->
  (Znth (lit_var_c focus) (mt_levels (ms_core M)) 0 = 0 ->
    lit_true (mt_assigns (ms_core M)) (tag_lit word) /\
    Znth (lit_var_c (tag_lit word)) (mt_levels (ms_core M)) 0 = 0) ->
  minisat_base_focus_word_completed M focus word.
Proof.
  intros n M focus word [_ [Howners Hobjects]] Htag Hpartnerzero Hzero owner co Hin.
  destruct (Hpartnerzero Hzero) as [Htrue Hlevel].
  rewrite Forall_forall in Howners. pose proof (Howners (owner,co) Hin) as [_ Heven].
  assert (Hpartner : forall other,
    word = (if 3 <=? Zlength (co_lits co) then owner else tag_of_lit other) ->
    tag_lit word = other).
  { intros other Hword. destruct (3 <=? Zlength (co_lits co)).
    - subst word. pose proof (even_not_tag owner Heven). congruence.
    - rewrite Hword, tag_lit_of. reflexivity. }
  split; intros Hfocus Hword;
    pose proof (Hpartner _ Hword) as Hsame;
    rewrite <- Hsame; split; assumption.
Qed.

Lemma minisat_base_focus_word_completed_real__api_reentry : forall n M focus word selected,
  db_wf n (msolver_db M) -> is_tag word = false ->
  In (word,selected) (msolver_db M) ->
  (Znth (lit_var_c focus) (mt_levels (ms_core M)) 0 = 0 ->
    lit_neg_c (co_watch0 selected) = focus ->
    lit_true (mt_assigns (ms_core M)) (co_watch1 selected) /\
    Znth (lit_var_c (co_watch1 selected)) (mt_levels (ms_core M)) 0 = 0) ->
  (Znth (lit_var_c focus) (mt_levels (ms_core M)) 0 = 0 ->
    lit_neg_c (co_watch1 selected) = focus ->
    lit_true (mt_assigns (ms_core M)) (co_watch0 selected) /\
    Znth (lit_var_c (co_watch0 selected)) (mt_levels (ms_core M)) 0 = 0) ->
  minisat_base_focus_word_completed M focus word.
Proof.
  intros n M focus word selected Hdb Htag Hselected Hleft Hright Hzero owner co Hin.
  assert (Howner : forall other,
    word = (if 3 <=? Zlength (co_lits co) then owner else tag_of_lit other) -> owner = word).
  { intros other Hword. destruct (3 <=? Zlength (co_lits co)).
    - symmetry. exact Hword.
    - rewrite Hword, is_tag_of in Htag. discriminate. }
  split; intros Hfocus Hword;
    pose proof (Howner _ Hword) as Heq; subst owner;
    pose proof (db_wf_lookup_unique n (msolver_db M) word co selected Hdb Hin Hselected)
      as Hco; subst co; [apply Hleft|apply Hright]; assumption.
Qed.

Lemma minisat_base_scan_completed_enqueue_success__api_reentry :
  forall n M focus pending q reason_word reason_clause,
    db_wf n (msolver_db M) -> mtrail_wf n (ms_core M) ->
    lit_wf_c n focus -> lit_wf_c n q ->
    processed (mt_assigns (ms_core M)) (mt_trail (ms_core M)) (mt_qhead (ms_core M)) focus ->
    minisat_base_scan_completed M focus pending ->
    minisat_base_scan_completed
      (msolver_propagation_enqueue_success M q reason_word reason_clause) focus pending.
Proof.
  intros n M focus pending q reason_word reason_clause Hdb Hwf Hfocus Hq Hprocessed Hscan.
  unfold msolver_propagation_enqueue_success.
  destruct (Znth (lit_var_c q) (mt_assigns (ms_core M)) 0 =? 0) eqn:Hfresh;
    [|exact Hscan].
  apply Z.eqb_eq in Hfresh.
  intros word Habsent Hzero owner co Hin.
  change (In (owner,co) (msolver_db M)) in Hin.
  pose proof (db_wf_obj n (msolver_db M) owner co Hdb Hin) as Hobj.
  cbn [ms_core msolver_propagation_overlay msolver_propagation_update] in Hzero |- *.
  split; intros Htrigger Hword.
  - eapply (base_completed_partner_enqueue_fresh__api_reentry
      n (ms_core M) focus q (co_watch1 co));
      [exact Hwf|exact Hfocus|exact Hq|exact (obj_wf_watch1 n co Hobj)|
       exact Hprocessed|exact Hfresh| |exact Hzero].
    intro Holdzero. exact (proj1 (Hscan word Habsent Holdzero owner co Hin) Htrigger Hword).
  - eapply (base_completed_partner_enqueue_fresh__api_reentry
      n (ms_core M) focus q (co_watch0 co));
      [exact Hwf|exact Hfocus|exact Hq|exact (obj_wf_watch0 n co Hobj)|
       exact Hprocessed|exact Hfresh| |exact Hzero].
    intro Holdzero. exact (proj2 (Hscan word Habsent Holdzero owner co Hin) Htrigger Hword).
Qed.

Lemma propagation_enqueue_partner_base_completed__api_reentry :
  forall n M focus q reason_word reason_clause,
    mtrail_wf n (ms_core M) -> lit_wf_c n focus -> lit_wf_c n q ->
    processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) focus ->
    Znth (lit_var_c focus) (mt_levels (ms_core M)) 0 =
      Zlength (mt_lim (ms_core M)) ->
    (Znth (lit_var_c q) (mt_assigns (ms_core M)) 0 = 0 \/
      lit_true (mt_assigns (ms_core M)) q) ->
    let M' := msolver_propagation_enqueue_success M q reason_word reason_clause in
    Znth (lit_var_c focus) (mt_levels (ms_core M')) 0 = 0 ->
    lit_true (mt_assigns (ms_core M')) q /\
    Znth (lit_var_c q) (mt_levels (ms_core M')) 0 = 0.
Proof.
  intros n M focus q reason_word reason_clause Hwf Hfocus Hq Hprocessed Hlevel Hsuccess.
  unfold msolver_propagation_enqueue_success.
  destruct (Znth (lit_var_c q) (mt_assigns (ms_core M)) 0 =? 0) eqn:Hfresh.
  - apply Z.eqb_eq in Hfresh.
    pose proof (processed_fresh_target_different _ _ _ focus q Hprocessed Hfresh) as Hneq.
    assert (Hqassign : 0 <= lit_var_c q < Zlength (mt_assigns (ms_core M))).
    { rewrite (mtw_assigns_len Hwf). exact (lit_var_c_in_range n q Hq). }
    assert (Hqlevel : 0 <= lit_var_c q < Zlength (mt_levels (ms_core M))).
    { rewrite (mtw_levels_len Hwf). exact (lit_var_c_in_range n q Hq). }
    assert (Hfocuslevel : 0 <= lit_var_c focus < Zlength (mt_levels (ms_core M))).
    { rewrite (mtw_levels_len Hwf). exact (lit_var_c_in_range n focus Hfocus). }
    change (Znth (lit_var_c focus)
      (replace_Znth (lit_var_c q) (Zlength (mt_lim (ms_core M)))
        (mt_levels (ms_core M))) 0 = 0 ->
      lit_true (replace_Znth (lit_var_c q) (lit_sig q) (mt_assigns (ms_core M))) q /\
      Znth (lit_var_c q)
        (replace_Znth (lit_var_c q) (Zlength (mt_lim (ms_core M)))
          (mt_levels (ms_core M))) 0 = 0).
    rewrite Znth_replace_Znth_Diff
      by (first [exact Hqlevel|exact Hfocuslevel|congruence]).
    intro Hzero. split.
    + unfold lit_true. rewrite Znth_replace_Znth_Same by exact Hqassign. reflexivity.
    + rewrite Znth_replace_Znth_Same by exact Hqlevel. lia.
  - apply Z.eqb_neq in Hfresh.
    destruct Hsuccess as [Hzero|Htrue]; [contradiction|].
    intro Hzero. split; [exact Htrue|].
    pose proof (assigned_level_current_bound__api_reentry n (ms_core M) q Hwf Hq Htrue).
    pose proof (assigned_level_nonnegative__api_reentry n (ms_core M) q Hwf Hq Htrue).
    lia.
Qed.

Lemma minisat_base_watch_completed_except_clauses__api_reentry : forall M focus,
  minisat_base_watch_completed_except M focus <->
  Forall (fun e => minisat_base_clause_completed_except (ms_core M) focus (snd e))
    (msolver_db M).
Proof.
  intros M focus. rewrite Forall_forall. split.
  - intros H [owner co] Hin. exact (H owner co Hin).
  - intros H owner co Hin. exact (H (owner,co) Hin).
Qed.

Lemma minisat_base_clause_completed_watch_swap__api_reentry : forall t focus co co',
  ((co_watch0 co' = co_watch0 co /\ co_watch1 co' = co_watch1 co) \/
   (co_watch0 co' = co_watch1 co /\ co_watch1 co' = co_watch0 co)) ->
  minisat_base_clause_completed_except t focus co ->
  minisat_base_clause_completed_except t focus co'.
Proof.
  intros t focus co co' [[Hleft Hright]|[Hleft Hright]] Hcomplete;
    unfold minisat_base_clause_completed_except in *;
    rewrite Hleft, Hright; tauto.
Qed.

Lemma minisat_base_watch_completed_normalize__api_reentry :
  forall M focus current a0 a1 tail other prob' learnt' wm,
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (a0 :: a1 :: tail)
      (propagation_normalized_clause other (lit_neg_c focus) (a0 :: a1 :: tail))
      prob' learnt' ->
    ((a0 = lit_neg_c focus /\ other = a1) \/
     (a1 = lit_neg_c focus /\ other = a0)) ->
    minisat_base_watch_completed_except M focus ->
    minisat_base_watch_completed_except
      (msolver_propagation_db_wmap_update M prob' learnt' wm) focus.
Proof.
  intros M focus current a0 a1 tail other prob' learnt' wm Hupdate Hcases Hcomplete.
  apply minisat_base_watch_completed_except_clauses__api_reentry.
  change (Forall (fun e => minisat_base_clause_completed_except (ms_core M) focus (snd e))
    (prob' ++ learnt')).
  eapply db_pair_lits_update_forall_clauses__api_reentry;
    [exact Hupdate| |apply minisat_base_watch_completed_except_clauses__api_reentry; exact Hcomplete].
  intros co Hin Hwords Hco. eapply minisat_base_clause_completed_watch_swap__api_reentry;
    [|exact Hco].
  unfold co_watch0, co_watch1.
  rewrite Hwords. cbn [clause_obj_with_lits co_lits propagation_normalized_clause].
  destruct Hcases as [[Hfalse Hother]|[Hfalse Hother]];
    [right|left]; subst; split; reflexivity.
Qed.

Lemma minisat_base_clause_completed_migrate__api_reentry :
  forall n t focus co candidate tail,
    obj_wf n co -> co_watch1 co = lit_neg_c focus ->
    lit_true (mt_assigns t) focus ->
    ~ lit_false (mt_assigns t) candidate ->
    minisat_base_clause_completed_except t focus co ->
    minisat_base_clause_completed_except t focus
      (clause_obj_with_lits co (co_watch0 co :: candidate :: tail)).
Proof.
  intros n t focus co candidate tail Hobj Hwatch1 Hfocus Hcandidate [Hleft Hright].
  pose proof (obj_wf_watch_indices_distinct__reducedb n co Hobj) as Hdistinct.
  rewrite Hwatch1, lit_neg_c_involutive in Hdistinct.
  unfold minisat_base_clause_completed_except, co_watch0, co_watch1.
  cbn [clause_obj_with_lits co_lits].
  change ((lit_neg_c (co_watch0 co) <> focus ->
    processed (mt_assigns t) (mt_trail t) (mt_qhead t) (lit_neg_c (co_watch0 co)) ->
    Znth (lit_var_c (co_watch0 co)) (mt_levels t) 0 = 0 ->
    lit_true (mt_assigns t) candidate /\
    Znth (lit_var_c candidate) (mt_levels t) 0 = 0) /\
    (lit_neg_c candidate <> focus ->
    processed (mt_assigns t) (mt_trail t) (mt_qhead t) (lit_neg_c candidate) ->
    Znth (lit_var_c candidate) (mt_levels t) 0 = 0 ->
    lit_true (mt_assigns t) (co_watch0 co) /\
    Znth (lit_var_c (co_watch0 co)) (mt_levels t) 0 = 0)).
  split; intros Hneq Hprocessed Hzero; exfalso.
  - destruct (Hleft Hdistinct Hprocessed Hzero) as [Htrue _].
    rewrite Hwatch1 in Htrue. unfold lit_true in Htrue.
    rewrite lit_var_c_neg, lit_sig_neg in Htrue.
    eapply lit_true_false_contra; [exact Hfocus|exact Htrue].
  - apply Hcandidate. destruct Hprocessed as [Hneg _].
    unfold lit_true in Hneg. rewrite lit_var_c_neg, lit_sig_neg in Hneg.
    exact Hneg.
Qed.

Lemma minisat_base_watch_completed_migrate__api_reentry :
  forall n M focus current other oldtail candidate newtail prob' learnt' wm,
    db_wf n (msolver_db M) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (other :: lit_neg_c focus :: oldtail) (other :: candidate :: newtail)
      prob' learnt' ->
    lit_true (mt_assigns (ms_core M)) focus ->
    ~ lit_false (mt_assigns (ms_core M)) candidate ->
    minisat_base_watch_completed_except M focus ->
    minisat_base_watch_completed_except
      (msolver_propagation_db_wmap_update M prob' learnt' wm) focus.
Proof.
  intros n M focus current other oldtail candidate newtail prob' learnt' wm
    Hdb Hupdate Hfocus Hcandidate Hcomplete.
  apply minisat_base_watch_completed_except_clauses__api_reentry.
  change (Forall (fun e => minisat_base_clause_completed_except (ms_core M) focus (snd e))
    (prob' ++ learnt')).
  eapply db_pair_lits_update_forall_clauses__api_reentry;
    [exact Hupdate| |apply minisat_base_watch_completed_except_clauses__api_reentry; exact Hcomplete].
  intros co Hin Hwords Hco.
  pose proof (db_wf_obj n (msolver_db M) current co Hdb Hin) as Hobj.
  replace other with (co_watch0 co)
    by (unfold co_watch0; rewrite Hwords; reflexivity).
  eapply minisat_base_clause_completed_migrate__api_reentry;
    [exact Hobj|unfold co_watch1; rewrite Hwords; reflexivity|
     exact Hfocus|exact Hcandidate|exact Hco].
Qed.

Lemma minisat_base_focus_word_completed_normalize__api_reentry :
  forall M focus word current a0 a1 tail other prob' learnt' wm,
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (a0 :: a1 :: tail)
      (propagation_normalized_clause other (lit_neg_c focus) (a0 :: a1 :: tail))
      prob' learnt' ->
    ((a0 = lit_neg_c focus /\ other = a1) \/
     (a1 = lit_neg_c focus /\ other = a0)) ->
    minisat_base_focus_word_completed M focus word ->
    minisat_base_focus_word_completed
      (msolver_propagation_db_wmap_update M prob' learnt' wm) focus word.
Proof.
  intros M focus word current a0 a1 tail other prob' learnt' wm
    Hupdate Hcases Hcomplete.
  unfold minisat_base_focus_word_completed in *.
  intro Hzero. specialize (Hcomplete Hzero).
  eapply db_pair_lits_update_all_entries__api_reentry;
    [exact Hupdate|exact Hcomplete|].
  intros co Hin Hwords Hlocal.
  assert (Hlength : Zlength
    (propagation_normalized_clause other (lit_neg_c focus) (a0 :: a1 :: tail)) =
    Zlength (a0 :: a1 :: tail)).
  { apply propagation_normalized_clause_length. rewrite !Zlength_cons.
    pose proof (Zlength_nonneg tail). lia. }
  cbn [clause_obj_with_lits co_lits].
  rewrite Hlength.
  unfold co_watch0, co_watch1 in Hlocal |- *.
  rewrite Hwords in Hlocal.
  cbn [clause_obj_with_lits co_lits propagation_normalized_clause] in *.
  destruct Hcases as [[Hfalse Hother]|[Hfalse Hother]]; subst; tauto.
Qed.

Lemma minisat_base_scan_completed_normalize__api_reentry :
  forall M focus pending current a0 a1 tail other prob' learnt' wm,
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (a0 :: a1 :: tail)
      (propagation_normalized_clause other (lit_neg_c focus) (a0 :: a1 :: tail))
      prob' learnt' ->
    ((a0 = lit_neg_c focus /\ other = a1) \/
     (a1 = lit_neg_c focus /\ other = a0)) ->
    minisat_base_scan_completed M focus pending ->
    minisat_base_scan_completed
      (msolver_propagation_db_wmap_update M prob' learnt' wm) focus pending.
Proof.
  intros M focus pending current a0 a1 tail other prob' learnt' wm
    Hupdate Hcases Hscan word Habsent.
  eapply minisat_base_focus_word_completed_normalize__api_reentry;
    [exact Hupdate|exact Hcases|apply Hscan; exact Habsent].
Qed.

Lemma minisat_base_focus_word_completed_normalized_real__api_reentry :
  forall n M focus current co,
    db_wf n (msolver_db M) -> is_tag current = false ->
    In (current,co) (msolver_db M) -> co_watch1 co = lit_neg_c focus ->
    (Znth (lit_var_c focus) (mt_levels (ms_core M)) 0 = 0 ->
      lit_true (mt_assigns (ms_core M)) (co_watch0 co) /\
      Znth (lit_var_c (co_watch0 co)) (mt_levels (ms_core M)) 0 = 0) ->
    minisat_base_focus_word_completed M focus current.
Proof.
  intros n M focus current co Hdb Hreal Hin Hwatch1 Hpartner.
  pose proof (db_wf_obj n (msolver_db M) current co Hdb Hin) as Hobj.
  pose proof (obj_wf_watch_indices_distinct__reducedb n co Hobj) as Hdistinct.
  rewrite Hwatch1, lit_neg_c_involutive in Hdistinct.
  eapply minisat_base_focus_word_completed_real__api_reentry;
    [exact Hdb|exact Hreal|exact Hin| |].
  - intros Hzero Hfocus. contradiction.
  - intros Hzero Hfocus. apply Hpartner. exact Hzero.
Qed.

Lemma minisat_base_focus_word_completed_migrate__api_reentry :
  forall n M focus word current other oldtail candidate newtail prob' learnt' wm,
    db_wf n (msolver_db M) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (other :: lit_neg_c focus :: oldtail) (other :: candidate :: newtail)
      prob' learnt' ->
    lit_true (mt_assigns (ms_core M)) focus ->
    ~ lit_false (mt_assigns (ms_core M)) candidate ->
    minisat_base_focus_word_completed M focus word ->
    minisat_base_focus_word_completed
      (msolver_propagation_db_wmap_update M prob' learnt' wm) focus word.
Proof.
  intros n M focus word current other oldtail candidate newtail prob' learnt' wm
    Hdb Hupdate Hfocus Hcandidate Hcomplete.
  unfold minisat_base_focus_word_completed in *.
  intro Hzero. specialize (Hcomplete Hzero).
  eapply db_pair_lits_update_all_entries__api_reentry;
    [exact Hupdate|exact Hcomplete|].
  intros co Hin Hwords Hlocal.
  pose proof (db_wf_obj n (msolver_db M) current co Hdb Hin) as Hobj.
  pose proof (obj_wf_watch_indices_distinct__reducedb n co Hobj) as Hother.
  unfold co_watch0, co_watch1 in Hother. rewrite Hwords in Hother.
  change (lit_neg_c other <> lit_neg_c (lit_neg_c focus)) in Hother.
  rewrite lit_neg_c_involutive in Hother.
  assert (Hreplacement : lit_neg_c candidate <> focus).
  { intro Heq. apply Hcandidate. rewrite <- Heq in Hfocus.
    unfold lit_true in Hfocus. rewrite lit_var_c_neg, lit_sig_neg in Hfocus.
    exact Hfocus. }
  cbn [clause_obj_with_lits co_lits co_watch0 co_watch1].
  split; intros Htrigger Hword; contradiction.
Qed.

Lemma minisat_base_scan_completed_migrate__api_reentry :
  forall n M focus pending current other oldtail candidate newtail prob' learnt' wm,
    db_wf n (msolver_db M) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (other :: lit_neg_c focus :: oldtail) (other :: candidate :: newtail)
      prob' learnt' ->
    lit_true (mt_assigns (ms_core M)) focus ->
    ~ lit_false (mt_assigns (ms_core M)) candidate ->
    minisat_base_scan_completed M focus pending ->
    minisat_base_scan_completed
      (msolver_propagation_db_wmap_update M prob' learnt' wm) focus pending.
Proof.
  intros n M focus pending current other oldtail candidate newtail prob' learnt' wm
    Hdb Hupdate Hfocus Hcandidate Hscan query Habsent.
  eapply minisat_base_focus_word_completed_migrate__api_reentry;
    [exact Hdb|exact Hupdate|exact Hfocus|exact Hcandidate|apply Hscan; exact Habsent].
Qed.

Lemma minisat_base_scan_completed_migrate_advance__api_reentry :
  forall n M focus current pending other oldtail candidate newtail prob' learnt' wm,
    db_wf n (msolver_db M) -> db_wf n (prob' ++ learnt') ->
    is_tag current = false ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (other :: lit_neg_c focus :: oldtail) (other :: candidate :: newtail)
      prob' learnt' ->
    lit_true (mt_assigns (ms_core M)) focus ->
    ~ lit_false (mt_assigns (ms_core M)) candidate ->
    minisat_base_scan_completed M focus (current :: pending) ->
    minisat_base_scan_completed
      (msolver_propagation_db_wmap_update M prob' learnt' wm) focus pending.
Proof.
  intros n M focus current pending other oldtail candidate newtail prob' learnt' wm
    Hdb Hdbnew Hreal Hupdate Hfocus Hcandidate Hscan.
  destruct (db_pair_lits_update_selected_before__propagate_dbu
    _ _ _ _ _ _ _ Hupdate) as [oldco [Hold Hwords]].
  pose proof (db_wf_obj n (msolver_db M) current oldco Hdb Hold) as Hobj.
  pose proof (obj_wf_watch_indices_distinct__reducedb n oldco Hobj) as Hother.
  unfold co_watch0, co_watch1 in Hother. rewrite Hwords in Hother.
  change (lit_neg_c other <> lit_neg_c (lit_neg_c focus)) in Hother.
  rewrite lit_neg_c_involutive in Hother.
  assert (Hreplacement : lit_neg_c candidate <> focus).
  { intro Heq. apply Hcandidate. rewrite <- Heq in Hfocus.
    unfold lit_true in Hfocus. rewrite lit_var_c_neg, lit_sig_neg in Hfocus.
    exact Hfocus. }
  eapply minisat_base_scan_completed_advance__api_reentry.
  - eapply minisat_base_scan_completed_migrate__api_reentry;
      [exact Hdb|exact Hupdate|exact Hfocus|exact Hcandidate|exact Hscan].
  - destruct (db_pair_lits_update_selected_owner__propagate_dbu
      _ _ _ _ _ _ _ Hupdate) as [newco [Hin Hnewwords]].
    eapply minisat_base_focus_word_completed_real__api_reentry;
      [exact Hdbnew|exact Hreal|exact Hin| |];
      unfold co_watch0, co_watch1; rewrite Hnewwords; cbn;
      intros Hzero Htrigger; contradiction.
Qed.


Lemma minisat_propagation_reuse_loop_initial__api_reentry : forall n M,
  minisat_propagation_reuse_loop n M M 0.
Proof. intros. unfold minisat_propagation_reuse_loop. intuition congruence. Qed.

Lemma minisat_propagation_reuse_scan_begin__api_reentry :
  forall n entry M p simp props pending,
    minisat_propagation_reuse_loop n entry M 0 ->
    p = Znth (mt_qhead (ms_core M)) (mt_trail (ms_core M)) 0 ->
    incl (expected_watchers (msolver_db M) p) pending ->
    minisat_propagation_reuse_scan entry
      (msolver_propagation_scan_begin M simp props) p 0 pending.
Proof.
  intros n entry M p simp props pending [Hcomplete [Hresident _]] Hp Hpending.
  split.
  - intro Hentry. split.
    + apply minisat_base_watch_completed_scan_begin__api_reentry;
        [exact Hp|exact (proj1 (Hcomplete Hentry) eq_refl)].
    + intro Hzero. apply minisat_base_scan_completed_initial__api_reentry.
      exact Hpending.
  - split.
    + intro Hfalse. apply minisat_resident_false_scan_begin__api_reentry.
      exact (Hresident Hfalse).
    + intro Hnonzero. contradiction.
Qed.


Lemma minisat_propagation_reuse_binary_conflict__api_reentry :
  forall n F A K entry M p kept current pending,
    solver_propagation_scan_semantics n F A K M p 0 kept (current :: pending) ->
    minisat_propagation_reuse_scan entry M p 0 (current :: pending) ->
    is_tag current = true ->
    lit_false (mt_assigns (ms_core M)) (tag_lit current) ->
    ms_binary M <> 0 ->
    minisat_propagation_reuse_scan entry
      (msolver_propagation_binary_conflict M (tag_lit current) p) p (ms_binary M) nil.
Proof.
  intros n F A K entry M p kept current pending Hsem
    [Hcomplete [Hresident Hconflict]] Htag Hfalse Hnonzero.
  destruct (propagation_binary_conflict_resident__api_reentry
    n F A K M p 0 kept current pending Hsem Htag Hfalse)
    as [owner [co [Hin [_ Hcofalse]]]].
  assert (Hnewfalse : minisat_resident_false_clause
    (msolver_propagation_binary_conflict M (tag_lit current) p)).
  { exists owner, co. split; assumption. }
  split.
  - intro Hentry. split.
    + eapply minisat_base_watch_completed_except_same_fields__api_reentry;
        try reflexivity; exact (proj1 (Hcomplete Hentry)).
    + intro Hzero. contradiction.
  - split; intro H; exact Hnewfalse.
Qed.

Lemma minisat_propagation_reuse_normalize__api_reentry :
  forall entry M focus confl pending current a0 a1 tail other prob' learnt' wm,
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (a0 :: a1 :: tail)
      (propagation_normalized_clause other (lit_neg_c focus) (a0 :: a1 :: tail))
      prob' learnt' ->
    ((a0 = lit_neg_c focus /\ other = a1) \/
     (a1 = lit_neg_c focus /\ other = a0)) ->
    minisat_propagation_reuse_scan entry M focus confl pending ->
    minisat_propagation_reuse_scan entry
      (msolver_propagation_db_wmap_update M prob' learnt' wm) focus confl pending.
Proof.
  intros entry M focus confl pending current a0 a1 tail other prob' learnt' wm
    Hupdate Hcases [Hcomplete [Hresident Hconflict]].
  assert (Hperm : Permutation (a0 :: a1 :: tail)
    (propagation_normalized_clause other (lit_neg_c focus) (a0 :: a1 :: tail))).
  { unfold propagation_normalized_clause.
    assert (Htail : sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail) = tail).
    { rewrite sublist_cons2 by
        (rewrite !Zlength_cons; pose proof (Zlength_nonneg tail); lia).
      rewrite sublist_cons2 by
        (rewrite !Zlength_cons; pose proof (Zlength_nonneg tail); lia).
      replace (2 - 1 - 1) with 0 by lia.
      replace (Zlength (a0 :: a1 :: tail) - 1 - 1) with (Zlength tail)
        by (rewrite !Zlength_cons; lia).
      apply sublist_self. reflexivity. }
    rewrite Htail. destruct Hcases as [[Ha Ho]|[Ha Ho]]; subst;
      [apply perm_swap|apply Permutation_refl]. }
  split.
  - intro Hentry. destruct (Hcomplete Hentry) as [Hexcept Hpending]. split.
    + eapply minisat_base_watch_completed_normalize__api_reentry; eassumption.
    + intro Hzero. eapply minisat_base_scan_completed_normalize__api_reentry;
        [exact Hupdate|exact Hcases|exact (Hpending Hzero)].
  - split; intro H.
    + eapply minisat_resident_false_db_update__api_reentry;
        [exact Hupdate|exact Hperm|exact (Hresident H)].
    + eapply minisat_resident_false_db_update__api_reentry;
        [exact Hupdate|exact Hperm|exact (Hconflict H)].
Qed.

Lemma propagation_true_partner_base_completed__api_reentry : forall n t focus other,
  mtrail_wf n t -> lit_wf_c n other ->
  Znth (lit_var_c focus) (mt_levels t) 0 = Zlength (mt_lim t) ->
  lit_true (mt_assigns t) other ->
  Znth (lit_var_c focus) (mt_levels t) 0 = 0 ->
  lit_true (mt_assigns t) other /\ Znth (lit_var_c other) (mt_levels t) 0 = 0.
Proof.
  intros n t focus other Hwf Ho Hcurrent Htrue Hzero. split; [exact Htrue|].
  pose proof (assigned_level_current_bound__api_reentry n t other Hwf Ho Htrue).
  pose proof (assigned_level_nonnegative__api_reentry n t other Hwf Ho Htrue).
  lia.
Qed.

Lemma minisat_propagation_reuse_enqueue__api_reentry :
  forall n entry M focus pending q reason_word reason_clause,
    db_wf n (msolver_db M) -> mtrail_wf n (ms_core M) ->
    lit_wf_c n focus -> lit_wf_c n q ->
    processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) focus ->
    minisat_propagation_reuse_scan entry M focus 0 pending ->
    minisat_propagation_reuse_scan entry
      (msolver_propagation_enqueue_success M q reason_word reason_clause) focus 0 pending.
Proof.
  intros n entry M focus pending q reason_word reason_clause
    Hdb Hwf Hfocus Hq Hprocessed [Hcomplete [Hresident Hconflict]].
  split.
  - intro Hentry. destruct (Hcomplete Hentry) as [Hexcept Hpending]. split.
    + eapply minisat_base_watch_completed_except_enqueue_success__api_reentry; eassumption.
    + intro Hzero. eapply minisat_base_scan_completed_enqueue_success__api_reentry;
        [exact Hdb|exact Hwf|exact Hfocus|exact Hq|exact Hprocessed|exact (Hpending eq_refl)].
  - split.
    + intro Hfalse. eapply minisat_resident_false_enqueue_success__api_reentry;
        [exact Hdb|exact Hwf|exact Hq|exact (Hresident Hfalse)].
    + intro Hnonzero. contradiction.
Qed.

Lemma minisat_propagation_reuse_advance__api_reentry :
  forall entry M focus current pending,
    minisat_propagation_reuse_scan entry M focus 0 (current :: pending) ->
    minisat_base_focus_word_completed M focus current ->
    minisat_propagation_reuse_scan entry M focus 0 pending.
Proof.
  intros entry M focus current pending [Hcomplete [Hresident Hconflict]] Hword.
  split.
  - intro Hentry. destruct (Hcomplete Hentry) as [Hexcept Hpending]. split.
    + exact Hexcept.
    + intro Hzero. eapply minisat_base_scan_completed_advance__api_reentry;
        [exact (Hpending eq_refl)|exact Hword].
  - split; assumption.
Qed.

Lemma minisat_propagation_reuse_migrate__api_reentry :
  forall n entry M focus current pending other oldtail candidate newtail prob' learnt' wm,
    db_wf n (msolver_db M) -> db_wf n (prob' ++ learnt') ->
    is_tag current = false ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (other :: lit_neg_c focus :: oldtail) (other :: candidate :: newtail)
      prob' learnt' ->
    Permutation (other :: lit_neg_c focus :: oldtail) (other :: candidate :: newtail) ->
    lit_true (mt_assigns (ms_core M)) focus ->
    ~ lit_false (mt_assigns (ms_core M)) candidate ->
    minisat_propagation_reuse_scan entry M focus 0 (current :: pending) ->
    minisat_propagation_reuse_scan entry
      (msolver_propagation_db_wmap_update M prob' learnt' wm) focus 0 pending.
Proof.
  intros n entry M focus current pending other oldtail candidate newtail prob' learnt' wm
    Hdb Hdbnew Hreal Hupdate Hperm Hfocus Hcandidate [Hcomplete [Hresident Hconflict]].
  split.
  - intro Hentry. destruct (Hcomplete Hentry) as [Hexcept Hpending]. split.
    + eapply minisat_base_watch_completed_migrate__api_reentry; eassumption.
    + intro Hzero. eapply minisat_base_scan_completed_migrate_advance__api_reentry;
        [exact Hdb|exact Hdbnew|exact Hreal|exact Hupdate|exact Hfocus|exact Hcandidate|
         exact (Hpending eq_refl)].
  - split.
    + intro Hfalse. eapply minisat_resident_false_db_update__api_reentry;
        [exact Hupdate|exact Hperm|exact (Hresident Hfalse)].
    + intro Hnonzero. contradiction.
Qed.

Lemma minisat_propagation_reuse_real_satisfied__api_reentry :
  forall n entry M focus current pending a0 a1 tail other prob' learnt' wm,
    db_wf n (prob' ++ learnt') -> mtrail_wf n (ms_core M) ->
    db_pair_lits_update (ms_prob M) (ms_learnt M) current
      (a0 :: a1 :: tail)
      (propagation_normalized_clause other (lit_neg_c focus) (a0 :: a1 :: tail))
      prob' learnt' ->
    ((a0 = lit_neg_c focus /\ other = a1) \/
     (a1 = lit_neg_c focus /\ other = a0)) ->
    is_tag current = false ->
    Znth (lit_var_c focus) (mt_levels (ms_core M)) 0 =
      Zlength (mt_lim (ms_core M)) ->
    lit_true (mt_assigns (ms_core M)) other ->
    minisat_propagation_reuse_scan entry M focus 0 (current :: pending) ->
    minisat_propagation_reuse_scan entry
      (msolver_propagation_db_wmap_update M prob' learnt' wm) focus 0 pending.
Proof.
  intros n entry M focus current pending a0 a1 tail other prob' learnt' wm
    Hdbnew Hwf Hupdate Hcases Hreal Hcurrent Htrue Hreuse.
  eapply minisat_propagation_reuse_advance__api_reentry.
  - eapply minisat_propagation_reuse_normalize__api_reentry;
      [exact Hupdate|exact Hcases|exact Hreuse].
  - destruct (db_pair_lits_update_selected_owner__propagate_dbu
      _ _ _ _ _ _ _ Hupdate) as [co [Hin Hwords]].
    assert (Hwatch0 : co_watch0 co = other).
    { unfold co_watch0. rewrite Hwords.
      unfold propagation_normalized_clause. reflexivity. }
    assert (Hwatch1 : co_watch1 co = lit_neg_c focus).
    { unfold co_watch1. rewrite Hwords.
      unfold propagation_normalized_clause. reflexivity. }
    pose proof (db_wf_obj n (prob' ++ learnt') current co Hdbnew Hin) as Hobj.
    pose proof (obj_wf_watch0 n co Hobj) as Hotherwf. rewrite Hwatch0 in Hotherwf.
    eapply minisat_base_focus_word_completed_normalized_real__api_reentry;
      [exact Hdbnew|exact Hreal|exact Hin|exact Hwatch1|].
    rewrite Hwatch0.
    apply (propagation_true_partner_base_completed__api_reentry
      n (ms_core M) focus other Hwf Hotherwf Hcurrent Htrue).
Qed.

Lemma minisat_propagation_reuse_resident_conflict__api_reentry :
  forall entry M focus pending owner co,
    minisat_propagation_reuse_scan entry M focus 0 pending ->
    owner <> 0 -> In (owner,co) (msolver_db M) ->
    clause_false (assigns_pv (mt_assigns (ms_core M))) (denote_obj co) ->
    minisat_propagation_reuse_scan entry M focus owner nil.
Proof.
  intros entry M focus pending owner co [Hcomplete [Hresident Hconflict]]
    Hnonzero Hin Hfalse. split.
  - intro Hentry. split; [exact (proj1 (Hcomplete Hentry))|].
    intro Hzero. contradiction.
  - assert (Hresidentnow : minisat_resident_false_clause M).
    { exists owner, co. split; assumption. }
    split; intro H; exact Hresidentnow.
Qed.


Lemma base_completed_watch_decide_fresh__api_reentry :
  forall n t q watch other,
    mtrail_wf n t ->
    lit_wf_c n q -> lit_wf_c n watch -> lit_wf_c n other ->
    Znth (lit_var_c q) (mt_assigns t) 0 = 0 ->
    (processed (mt_assigns t) (mt_trail t) (mt_qhead t)
       (lit_neg_c watch) ->
     Znth (lit_var_c watch) (mt_levels t) 0 = 0 ->
     lit_true (mt_assigns t) other /\
     Znth (lit_var_c other) (mt_levels t) 0 = 0) ->
    processed (mt_assigns (mt_decide t q)) (mt_trail (mt_decide t q))
      (mt_qhead (mt_decide t q)) (lit_neg_c watch) ->
    Znth (lit_var_c watch) (mt_levels (mt_decide t q)) 0 = 0 ->
    lit_true (mt_assigns (mt_decide t q)) other /\
    Znth (lit_var_c other) (mt_levels (mt_decide t q)) 0 = 0.
Proof.
  intros n t q watch other Htrail Hq Hwatch Hother Hfresh Hcomplete Hnew Hzero.
  change (processed (mt_assigns (mt_enqueue t q))
    (mt_trail (mt_enqueue t q)) (mt_qhead (mt_enqueue t q))
    (lit_neg_c watch)) in Hnew.
  pose proof (proj1 (processed_enqueue_fresh_equiv__propagate_dbu
    n t q Htrail Hq Hfresh) (lit_neg_c watch)
    (lit_neg_c_wf n watch Hwatch) Hnew) as Hold.
  pose proof (processed_fresh_target_different
    (mt_assigns t) (mt_trail t) (mt_qhead t)
    (lit_neg_c watch) q Hold Hfresh) as Hqwatch.
  rewrite lit_var_c_neg in Hqwatch.
  pose proof (lit_var_c_in_range n q Hq) as Hqrange.
  pose proof (lit_var_c_in_range n watch Hwatch) as Hwatchrange.
  pose proof (lit_var_c_in_range n other Hother) as Hotherrange.
  assert (Holdzero : Znth (lit_var_c watch) (mt_levels t) 0 = 0).
  { unfold mt_decide, mt_push in Hzero. cbn [mt_levels] in Hzero.
    rewrite Znth_replace_Znth_Diff in Hzero
      by (try rewrite (mtw_levels_len Htrail); assumption).
    exact Hzero. }
  destruct (Hcomplete Hold Holdzero) as [Htrue Hlevel].
  assert (Hqother : lit_var_c q <> lit_var_c other).
  { intro Heq. apply (lit_true_assigned (mt_assigns t) other Htrue).
    rewrite <- Heq. exact Hfresh. }
  unfold mt_decide, mt_push. cbn [mt_assigns mt_levels]. split.
  - unfold lit_true in Htrue |- *.
    rewrite Znth_replace_Znth_Diff
      by (try rewrite (mtw_assigns_len Htrail); assumption).
    exact Htrue.
  - rewrite Znth_replace_Znth_Diff
      by (try rewrite (mtw_levels_len Htrail); assumption).
    exact Hlevel.
Qed.

Lemma minisat_base_watch_completed_assume__api_reentry :
  forall n M q,
    db_wf n (msolver_db M) -> mtrail_wf n (ms_core M) ->
    lit_wf_c n q -> Znth (lit_var_c q) (mt_assigns (ms_core M)) 0 = 0 ->
    minisat_base_watch_completed M ->
    minisat_base_watch_completed (msolver_assume M q).
Proof.
  intros n M q Hdb Hwf Hq Hfresh Hcomplete owner co Hin.
  change (In (owner,co) (msolver_db M)) in Hin.
  pose proof (db_wf_obj n (msolver_db M) owner co Hdb Hin) as Hobj.
  destruct (Hcomplete owner co Hin) as [Hleft Hright].
  cbn [msolver_assume ms_core]. split.
  - exact (base_completed_watch_decide_fresh__api_reentry n (ms_core M)
      q (co_watch0 co) (co_watch1 co) Hwf Hq
      (obj_wf_watch0 n co Hobj) (obj_wf_watch1 n co Hobj) Hfresh Hleft).
  - exact (base_completed_watch_decide_fresh__api_reentry n (ms_core M)
      q (co_watch1 co) (co_watch0 co) Hwf Hq
      (obj_wf_watch1 n co Hobj) (obj_wf_watch0 n co Hobj) Hfresh Hright).
Qed.

Lemma solver_base_completed_cancel_zero__api_reentry :
  forall n F A K M orderpos order,
    solver_propagation_weak n F A K M ->
    prop_level (ms_core M) ->
    heap_covers n (msolver_heap M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) ->
    minisat_base_watch_completed M ->
    msolver_seed_shadow M ->
    0 < Zlength (mt_lim (ms_core M)) ->
    heap_wf n (heap_of_lists order orderpos) ->
    incl (ms_order M) order ->
    cancel_reinserted (heap_of_lists order orderpos)
      (mt_trail (ms_core M)) (Znth 0 (mt_lim (ms_core M)) 0)
      (mt_qhead (ms_core M)) ->
    let Mpost := msolver_cancel_project M 0 orderpos order
      (ms_root_level M) in
    solver_base_recovery n F Mpost /\
    minisat_watch_completed Mpost /\ msolver_seed_shadow Mpost.
Proof.
  intros n F A K M orderpos order [Hpending Hctx]
    Hprop Hcovers Hbase Hseed Hpositive Hheap Hincl Hre.
  change (msolver_inv_ctx n F A K M) in Hctx.
  destruct (msolver_inv_ctx_core_facts n F A K M Hctx)
    as [Hsize [Htrail Hheap_old]].
  pose proof (msolver_inv_ctx_shape n F A K M Hctx) as Hshape.
  assert (Hdb : db_wf n (msolver_db M)).
  { destruct K as [A_inst|A_proc]; cbn in Hctx;
      [exact (msw_db_wf Hctx)|exact (msa_db_wf Hctx)]. }
  assert (Hlevel : 0 <= 0 < Zlength (mt_lim (ms_core M))) by lia.
  assert (Hbound : Znth 0 (mt_lim (ms_core M)) 0 <= mt_qhead (ms_core M)).
  { unfold prop_level in Hprop.
    exact (Forall_Znth_elim _ _ _ 0 0 Hprop Hlevel). }
  assert (Hheap_size : heap_wf (ms_size M) (heap_of_lists order orderpos)).
  { rewrite <- Hsize. exact Hheap. }
  pose proof (msolver_inv_ctx_cancel_zero__canceluntil_cap
    n F A K M orderpos order Hctx Hpositive
    Hheap_size Hincl Hre) as Hnormalized.
  pose proof (minisat_base_completion_cancel_zero__api_reentry
    n M orderpos order (ms_root_level M)
    Htrail Hdb Hpositive Hbound Hbase) as Hcomplete.
  assert (Hshape_post : solver_shape (msolver_cancel_project M 0
    orderpos order (ms_root_level M))).
  { apply (solver_shape_cancel_project__search n M 0 orderpos order
      (ms_root_level M)); try assumption.
    unfold solver_shape in Hshape. tauto. }
  pose proof (minisat_watch_completed_frontier__api_reentry n
    (msolver_cancel_project M 0 orderpos order (ms_root_level M))
    Hdb Hcomplete) as Hfront.
  assert (Hready : solver_root_rebuild_ready n F
    (msolver_cancel_project M 0 orderpos order (ms_root_level M))).
  { split; [exact Hnormalized|]. split; [reflexivity|]. split; [exact Hfront|].
    change (heap_covers n (heap_of_lists order orderpos)
      (mt_assigns (mt_cancel (ms_core M) 0))
      (mt_trail (mt_cancel (ms_core M) 0))
      (mt_qhead (mt_cancel (ms_core M) 0))).
    apply (heap_covers_cancel_project__canceluntil_cap n M 0 orderpos order);
      assumption. }
  assert (Hbase_post : solver_base_state n F
    (msolver_cancel_project M 0 orderpos order (ms_root_level M))).
  { apply solver_base_state_of_normalized__api_reentry.
    - apply solver_root_rebuild_strong__canceluntil_cap. exact Hready.
    - exact Hshape_post.
    - reflexivity.
    - exact Hpending. }
  split; [split; [exact Hbase_post|left; exact Hcomplete]|].
  split; [exact Hcomplete|exact Hseed].
Qed.

Lemma solver_conflict_cancel_zero_base_recovery__api_reentry :
  forall n F A K M focus orderpos order,
    propagation_cancel_ready n F A K M focus ->
    minisat_watch_conflict_ready n M ->
    msolver_seed_shadow M ->
    0 < Zlength (mt_lim (ms_core M)) ->
    heap_wf n (heap_of_lists order orderpos) ->
    incl (ms_order M) order ->
    cancel_reinserted (heap_of_lists order orderpos)
      (mt_trail (ms_core M)) (Znth 0 (mt_lim (ms_core M)) 0)
      (mt_qhead (ms_core M)) ->
    let Mpost := msolver_cancel_project M 0 orderpos order
      (ms_root_level M) in
    solver_base_recovery n F Mpost /\
    minisat_watch_completed Mpost /\ msolver_seed_shadow Mpost.
Proof.
  intros n F A K M focus orderpos order
    [Hweak [Hprop [Hfocus_wf [Hprocessed [Hfocus_level
      [Hfront [Hheap_old [Hcovers Hreason]]]]]]]]
    [watch_focus [Hwatch_level Hexcept]] Hseed Hpositive Hheap Hincl Hre.
  assert (Htrail : mtrail_wf n (ms_core M)).
  { destruct Hweak as [_ Hctx]. destruct K as [A_inst|A_proc];
      [exact (msw_trail_wf Hctx)|exact (msa_trail_wf Hctx)]. }
  pose proof (level_of_msolver_view_levels__analyze n M (lit_var_c watch_focus)
    (Zlength (mt_lim (ms_core M))) Htrail Hwatch_level) as Hlevel.
  assert (Hbase : minisat_base_watch_completed M).
  { apply (minisat_base_exception_above_zero__api_reentry M watch_focus);
      [lia|exact Hexcept]. }
  apply (solver_base_completed_cancel_zero__api_reentry
    n F A K M orderpos order); assumption.
Qed.

Lemma solver_assuming_cancel_zero_base_recovery__api_reentry :
  forall n F A Aproc M orderpos order,
    msolver_inv_assuming_strong n F A Aproc M ->
    ms_capacity_root_propagation_pending M = 0 ->
    minisat_base_watch_completed M ->
    msolver_seed_shadow M ->
    0 < Zlength (mt_lim (ms_core M)) ->
    heap_wf n (heap_of_lists order orderpos) ->
    incl (ms_order M) order ->
    cancel_reinserted (heap_of_lists order orderpos)
      (mt_trail (ms_core M)) (Znth 0 (mt_lim (ms_core M)) 0)
      (mt_qhead (ms_core M)) ->
    let Mpost := msolver_cancel_project M 0 orderpos order
      (ms_root_level M) in
    solver_base_recovery n F Mpost /\
    minisat_watch_completed Mpost /\ msolver_seed_shadow Mpost.
Proof.
  intros n F A Aproc M orderpos order Hstrong Hpending
    Hbase Hseed Hpositive Hheap Hincl Hre.
  apply (solver_base_completed_cancel_zero__api_reentry
    n F A (PropagationAssuming Aproc) M orderpos order).
  - split; [exact Hpending|exact (msas_weak Hstrong)].
  - exact (msas_prop_level Hstrong).
  - exact (msas_heap_covers Hstrong).
  - exact Hbase.
  - exact Hseed.
  - exact Hpositive.
  - exact Hheap.
  - exact Hincl.
  - exact Hre.
Qed.

Lemma solver_assuming_empty_base_recovery__api_reentry :
  forall n F A Aproc M,
    msolver_inv_assuming_strong n F A Aproc M ->
    ms_capacity_root_propagation_pending M = 0 ->
    minisat_base_watch_completed M ->
    msolver_seed_shadow M ->
    Zlength (mt_lim (ms_core M)) <= 0 ->
    solver_base_recovery n F M /\
    minisat_watch_completed M /\ msolver_seed_shadow M.
Proof.
  intros n F A Aproc M Hstrong Hpending Hbase Hseed Hnonpositive.
  assert (Hdepth : Zlength (mt_lim (ms_core M)) = 0).
  { pose proof (Zlength_nonneg (mt_lim (ms_core M))). lia. }
  pose proof (msas_weak Hstrong) as Hweak.
  pose proof (msolver_inv_ctx_root_empty__canceluntil_cap
    n F A (PropagationAssuming Aproc) M Hweak Hdepth) as Hnormalized.
  assert (Hready : solver_root_rebuild_ready n F M).
  { split; [exact Hnormalized|]. split; [exact Hdepth|]. split.
    - exact (msas_watch_frontier Hstrong).
    - exact (msas_heap_covers Hstrong). }
  assert (Hbase_state : solver_base_state n F M).
  { apply solver_base_state_of_normalized__api_reentry.
    - apply solver_root_rebuild_strong__canceluntil_cap. exact Hready.
    - exact (msa_shape Hweak).
    - exact Hdepth.
    - exact Hpending. }
  pose proof (minisat_base_completion_at_depth_zero__api_reentry
    n M (msa_trail_wf Hweak) (msa_db_wf Hweak) Hdepth Hbase) as Hcomplete.
  split; [split; [exact Hbase_state|left; exact Hcomplete]|].
  split; assumption.
Qed.


Definition solver_incremental_ownership_at
    (s : Z) (M : msolver) : Assertion :=
  “ msolver_seed_shadow M /\ 2 * ms_cap M <= INT_MAX ” &&
  solver_rep_growable s M.

Lemma solver_query_ready_completed_reentry__api_reentry : forall n F M,
  solver_query_ready n F M -> minisat_watch_completed M ->
  solver_query_entry n F M /\ solver_query_watch_ready M.
Proof.
  intros n F M Hready Hcompleted. split.
  - left. exact Hready.
  - unfold solver_query_watch_ready.
    destruct Hready as [_ [_ [_ Hpending]]]. split.
    + intros _. exact Hcompleted.
    + intros Hsuspended. rewrite Hpending in Hsuspended. discriminate.
Qed.


(** Successful insertion is closed on base states. The variable count is the
    returned size, not the old query's n. The actual insertion postcondition
    provides the new growth bound and formula equivalence. *)
Lemma solver_addclause_success_base_state__api_reentry :
  forall s begin n input_bound F entry input,
  solver_base_state n F entry -> minisat_watch_completed entry ->
  msolver_seed_shadow entry ->
  addclause_support_post_at s begin input_bound F nil nil entry input 1 |--
  EX M : msolver, EX current : list Z, EX Fnew : cnf,
    “ Zlength current = Zlength input /\
      ms_size entry <= ms_size M /\ ms_cap entry <= ms_cap M /\
      solver_base_state (ms_size M) Fnew M /\ minisat_watch_completed M /\
      (forall rho, models rho Fnew <-> models rho (F ++ (lits_denote input :: nil))) ” &&
    (solver_incremental_ownership_at s M **
     IntArray.seg begin 0 (Zlength input) current).
Proof.
  intros s begin n input_bound F entry input Hbase Hwatch Hseed.
  unfold addclause_support_post_at. Intros M current Fnew.
  match goal with
  | H : addclause_support_transition input_bound F nil nil entry input 1
      M current Fnew |- _ =>
      destruct H as [Htransition Hcompleted]
  end.
  destruct Htransition as [Hlen [Hsize [Hcap [Hbound [Hcontrol Hcases]]]]].
  destruct Hcases as [[Hbad _] | [_ [Hinv Hequiv]]].
  - discriminate Hbad.
  - destruct Hbase as [_ [Hlevel Hpending]].
    specialize (Hcontrol (conj Hlevel (conj Hpending Hseed))).
    destruct Hcontrol as [Hlevel_new [Hpending_new Hseed_new]].
    change (ms_size entry <= ms_size M) in Hsize.
    change (ms_cap entry <= ms_cap M) in Hcap.
    change (2 * ms_cap M <= INT_MAX) in Hbound.
    change (msolver_seed_shadow M) in Hseed_new.
    specialize (Hcompleted Hwatch).
    assert (Hshape_export : solver_rep_growable s M |--
      “ solver_shape M ” && solver_rep_growable s M).
    { unfold solver_rep_growable, solver_rep_at.
      Intros wl act asg opos rsn lvl trl tgs.
      Exists wl act asg opos rsn lvl trl tgs.
      msat_entailer_with ltac:(tauto). }
    sep_apply Hshape_export. Intros.
    assert (Hbase_new : solver_base_state (ms_size M) Fnew M).
    { apply solver_base_state_of_normalized__api_reentry.
      - exact Hinv.
      - assumption.
      - exact Hlevel_new.
      - exact Hpending_new. }
    Exists M current Fnew. unfold solver_incremental_ownership_at.
    msat_entailer_with ltac:(tauto).
Qed.

Lemma solver_simplify_success_query_entry__api_reentry :
  forall s n F entry lvl wl,
  (minisat_watch_completed entry \/ minisat_resident_false_clause entry) ->
  2 * ms_cap entry <= INT_MAX ->
  solver_wlists_tail wl (2 * n) (2 * ms_cap entry) **
  solver_simplify_post_at s n F nil entry lvl 1 wl |--
  EX M : msolver,
    “ ms_size M = n /\ ms_cap M = ms_cap entry /\
      solver_query_ready n F M /\ solver_query_entry n F M /\
      solver_query_watch_ready M ” && solver_incremental_ownership_at s M.
Proof.
  intros s n F entry lvl wl Hcompletion Hbound.
  unfold solver_simplify_post_at, solver_simplify_post_sat_at,
    solver_simplify_post_unsat_at.
  Split.
  - Intros M. Exists M.
    match goal with
    | Hfacts : ms_cap M = ms_cap entry /\
        ms_root_level M = ms_root_level entry /\
        msolver_inv_assuming_strong n F nil nil M /\
        solver_simplify_reuse entry M /\
        Zlength (mt_lim (ms_core M)) = 0 /\
        mt_qhead (ms_core M) = ms_qtail M /\
        ms_capacity_root_propagation_pending M = 0 /\
        msolver_seed_shadow M /\ _ |- _ =>
        destruct Hfacts as [Hcap [Hroot [Hstrong [Hreuse
          [Hlevel [Hdrained [Hpending [Hseed Hrest]]]]]]]]
    end.
    assert (Hsize : ms_size M = n).
    { symmetry. exact (msa_size (msas_weak Hstrong)). }
    assert (Hready : solver_query_ready n F M).
    { unfold solver_query_ready. tauto. }
    pose proof (Hreuse Hcompletion) as Hcompleted.
    destruct (solver_query_ready_completed_reentry__api_reentry
      n F M Hready Hcompleted) as [Hentry Hwatch].
    subst n. rewrite <- Hcap.
    sep_apply solver_rep_growable_of_wl.
    unfold solver_incremental_ownership_at. msat_entailer_with lia.
  - Intros M. Exists M. msat_entailer_with lia.
Qed.

Lemma solver_base_drained_query_ready__api_reentry : forall n F M,
  solver_base_state n F M ->
  mt_qhead (ms_core M) = ms_qtail M ->
  solver_query_ready n F M.
Proof.
  intros n F M [Hstrong [Hdepth Hpending]] Hdrain.
  unfold solver_query_ready. split; [exact Hstrong|].
  split; [exact Hdepth|]. split; assumption.
Qed.

Lemma solver_base_false_unsat__api_reentry : forall n F M A,
  solver_base_state n F M -> minisat_resident_false_clause M ->
  Forall (literal_wf n) A -> cnf_unsat n (cnf_with_units F A).
Proof.
  intros n F M A Hbase [owner [co [Hin Hfalse]]] Hawf.
  pose proof (solver_base_state_normalized__api_reentry n F M Hbase) as Hnormal.
  pose proof (msolver_inv_db_entailed n F nil nil
    (msolver_set_root M 0) (msi_weak Hnormal)) as Hdbent.
  assert (Hent : entails_clause F (denote_obj co)).
  { apply Hdbent. rewrite msolver_view_installed.
    change (In (denote_obj co) (db_clauses (msolver_db M))).
    unfold db_clauses. apply in_map with (f := fun e => denote_obj (snd e)) in Hin.
    exact Hin. }
  pose proof (db_wf_obj n (msolver_db M) owner co
    (msa_db_wf (msas_weak (proj1 Hbase))) Hin) as Hobj.
  pose proof (solver_query_assumptions__solve n F M A (proj1 Hbase) Hawf) as Hstrong.
  eapply assuming_conflict_unsat with (A_proc := nil) (M := M)
    (Cd := denote_obj co).
  - exact (msas_weak Hstrong).
  - exact Hent.
  - exact Hfalse.
  - unfold denote_obj. apply lits_denote_wf. exact (proj1 (proj2 Hobj)).
Qed.

Lemma solver_base_recovery_drained_reentry__api_reentry : forall n F M,
  solver_base_recovery n F M ->
  mt_qhead (ms_core M) = ms_qtail M -> solver_query_reentry n F M.
Proof.
  intros n F M [Hbase [Hcomplete|Hfalse]] Hdrain.
  - left. split; [|exact Hcomplete].
    exact (solver_base_drained_query_ready__api_reentry n F M Hbase Hdrain).
  - right. split; assumption.
Qed.

Lemma solver_base_recovery_false_reentry__api_reentry : forall n F M,
  solver_base_recovery n F M -> minisat_resident_false_clause M ->
  solver_query_reentry n F M.
Proof. intros n F M [Hbase _] Hfalse. right. split; assumption. Qed.

Lemma solver_cancel_project_reentry__api_reentry :
  forall n F M orderpos order root,
  solver_base_recovery n F
    (msolver_cancel_project M 0 orderpos order root) ->
  solver_query_reentry n F
    (msolver_cancel_project M 0 orderpos order root).
Proof.
  intros n F M orderpos order root Hbase.
  apply solver_base_recovery_drained_reentry__api_reentry; [exact Hbase|].
  reflexivity.
Qed.

Lemma solver_query_reentry_base_recovery__api_reentry : forall n F M,
  solver_query_reentry n F M -> solver_base_recovery n F M.
Proof.
  intros n F M [[Hready Hcomplete]|[Hbase Hfalse]].
  - split; [|left; exact Hcomplete].
    destruct Hready as [Hstrong [Hdepth [_ Hpending]]].
    split; [exact Hstrong|split; assumption].
  - split; [exact Hbase|right; exact Hfalse].
Qed.

Lemma solver_query_reentry_public_entry__api_reentry : forall n F M,
  solver_query_reentry n F M -> solver_public_query_entry n F M.
Proof.
  intros n F M [[Hready _]|Hfalse].
  - left. left. exact Hready.
  - right. exact Hfalse.
Qed.

Lemma msolver_resume_pending_ordinary__api_reentry : forall M,
  ms_capacity_root_propagation_pending M = 0 -> msolver_resume_pending M = M.
Proof. intros M Hzero. unfold msolver_resume_pending. rewrite Hzero. reflexivity. Qed.

Lemma msolver_resume_pending_size_cap__api_reentry : forall M,
  ms_size (msolver_resume_pending M) = ms_size M /\
  ms_cap (msolver_resume_pending M) = ms_cap M /\
  ms_model (msolver_resume_pending M) = ms_model M /\
  ms_root_level (msolver_resume_pending M) = ms_root_level M.
Proof.
  intros M. unfold msolver_resume_pending.
  destruct (Z.eqb (ms_capacity_root_propagation_pending M) 1); repeat split; reflexivity.
Qed.

Lemma solver_query_reentry_reusable__api_reentry : forall n F M,
  solver_query_reentry n F M ->
  solver_public_query_entry n F M /\ solver_query_reuse_guard M.
Proof.
  intros n F M Hentry. split.
  - exact (solver_query_reentry_public_entry__api_reentry n F M Hentry).
  - destruct Hentry as [[Hready Hcomplete]|[Hbase Hfalse]].
    + left. destruct Hready as [_ [_ [_ Hpending]]].
      unfold solver_query_watch_ready. split; [intros _; exact Hcomplete|].
      intros Hflag. lia.
    + right. split; [exact (proj2 (proj2 Hbase))|exact Hfalse].
Qed.

Definition solver_storage_undef (s : Z) : Assertion :=
  &( s # "solver_t" ->ₛ "size") # Int |->_ **
  &( s # "solver_t" ->ₛ "cap") # Int |->_ **
  &( s # "solver_t" ->ₛ "qhead") # Int |->_ **
  &( s # "solver_t" ->ₛ "qtail") # Int |->_ **
  &( s # "solver_t" ->ₛ "root_level") # Int |->_ **
  &( s # "solver_t" ->ₛ "simpdb_assigns") # Int |->_ **
  &( s # "solver_t" ->ₛ "simpdb_props") # Int |->_ **
  &( s # "solver_t" ->ₛ "verbosity") # Int |->_ **
  &( s # "solver_t" ->ₛ "var_inc") # Double |->_ **
  &( s # "solver_t" ->ₛ "var_decay") # Double |->_ **
  &( s # "solver_t" ->ₛ "cla_inc") # Float |->_ **
  &( s # "solver_t" ->ₛ "cla_decay") # Float |->_ **
  &( s # "solver_t" ->ₛ "random_seed") # Double |->_ **
  &( s # "solver_t" ->ₛ "progress_estimate") # Double |->_ **
  &( s # "solver_t" ->ₛ "wlists") # Ptr |->_ **
  &( s # "solver_t" ->ₛ "activity") # Ptr |->_ **
  &( s # "solver_t" ->ₛ "assigns") # Ptr |->_ **
  &( s # "solver_t" ->ₛ "orderpos") # Ptr |->_ **
  &( s # "solver_t" ->ₛ "reasons") # Ptr |->_ **
  &( s # "solver_t" ->ₛ "levels") # Ptr |->_ **
  &( s # "solver_t" ->ₛ "trail") # Ptr |->_ **
  &( s # "solver_t" ->ₛ "binary") # Ptr |->_ **
  &( s # "solver_t" ->ₛ "tags") # Ptr |->_ **
  Vecp.shell &( s # "solver_t" ->ₛ "clauses") **
  Vecp.shell &( s # "solver_t" ->ₛ "learnts") **
  Veci.shell &( s # "solver_t" ->ₛ "order") **
  Veci.shell &( s # "solver_t" ->ₛ "trail_lim") **
  Veci.shell &( s # "solver_t" ->ₛ "tagged") **
  Veci.shell &( s # "solver_t" ->ₛ "stack") **
  Veci.shell &( s # "solver_t" ->ₛ "model") **
  &( s # "solver_t" ->ₛ "stats" .ₛ "starts") # UInt64 |->_ **
  &( s # "solver_t" ->ₛ "stats" .ₛ "decisions") # UInt64 |->_ **
  &( s # "solver_t" ->ₛ "stats" .ₛ "propagations") # UInt64 |->_ **
  &( s # "solver_t" ->ₛ "stats" .ₛ "inspects") # UInt64 |->_ **
  &( s # "solver_t" ->ₛ "stats" .ₛ "conflicts") # UInt64 |->_ **
  &( s # "solver_t" ->ₛ "stats" .ₛ "clauses") # UInt64 |->_ **
  &( s # "solver_t" ->ₛ "stats" .ₛ "clauses_literals") # UInt64 |->_ **
  &( s # "solver_t" ->ₛ "stats" .ₛ "learnts") # UInt64 |->_ **
  &( s # "solver_t" ->ₛ "stats" .ₛ "learnts_literals") # UInt64 |->_ **
  &( s # "solver_t" ->ₛ "stats" .ₛ "max_literals") # UInt64 |->_ **
  &( s # "solver_t" ->ₛ "stats" .ₛ "tot_literals") # UInt64 |->_.

(* [ListNotations] is already in scope from the header import above;
   the [list_scope]/[Z_scope] re-opens below are kept because the annotation
   frontend definitions in this API tail read numeric and list literals under
   them and no enclosing Section discharges the header's scope stack here. *)
Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition cnf_nil : cnf := nil.

(** The exact successful constructor state. The allocated binary address is
    a parameter; the two scratch literal cells remain undefined until conflict propagation writes them. *)
Definition solver_initial_core : mtrail := {|
  mt_assigns := []; mt_levels := []; mt_trail := []; mt_lim := [];
  mt_qhead := 0
|}.

Definition solver_initial_model (binary : Z) : msolver := {|
  ms_size := 0; ms_cap := 0; ms_qtail := 0;
  ms_capacity_pending_qhead := 0;
  ms_capacity_root_propagation_pending := 0;
  ms_core := solver_initial_core; ms_root_level := 0;
  ms_reason_words := []; ms_reason_of := fun _ => None;
  ms_prob := []; ms_learnt := []; 
  ms_binary := binary; ms_binary_lits := [];
  ms_wm := []; ms_activity := []; ms_orderpos := [];
  ms_order := []; 
  ms_model := []; 
  ms_tags := []; ms_tagged := []; 
  ms_stack := []; 
  ms_var_inc := Z_to_fp64 1; ms_var_decay := Z_to_fp64 1;
  ms_cla_inc := Z_to_fp32 1; ms_cla_decay := Z_to_fp32 1;
  ms_random_seed := msat_fp64_seed; ms_progress := Z_to_fp64 0;
  ms_simpdb_assigns := 0; ms_simpdb_props := 0; ms_verbosity := 0;
  ms_stats := [0;0;0;0;0;0;0;0;0;0;0]
|}.

Lemma solver_initial_unassigned : forall v,
  mt_pv solver_initial_core v = None.
Proof.
  intros v. unfold mt_pv.
  destruct (Z.leb 0 v) eqn:Hnonneg; [|reflexivity].
  apply Z.leb_le in Hnonneg.
  unfold assigns_pv, assigns_val.
  change (lbool_val (Znth v (@nil Z) 0) = None).
  assert (Hz : Znth v (@nil Z) 0 = 0).
  { apply znth_out_of_bounds; [exact Hnonneg|].
    rewrite Zlength_nil. exact Hnonneg. }
  rewrite Hz. reflexivity.
Qed.

Lemma solver_initial_trail_wf : mtrail_wf 0 solver_initial_core.
Proof.
  constructor.
  - lia.
  - reflexivity.
  - reflexivity.
  - constructor.
  - change (0 <= 0 <= 0). lia.
  - change (0 <= 0). lia.
  - constructor.
  - constructor.
  - constructor.
  - exact I.
  - constructor.
  - intros i Hi. change (0 <= i < 0) in Hi. lia.
  - intros v Hv. lia.
Qed.

Lemma solver_initial_shape : forall binary,
  0 < binary -> Z.even binary = true ->
  solver_shape (solver_initial_model binary).
Proof.
  intros binary Hpositive Heven.
  unfold solver_shape. cbn [solver_initial_model solver_initial_core].
  rewrite !Zlength_nil. repeat rewrite Zlength_cons.
  repeat rewrite Zlength_nil.
  repeat split; try reflexivity; try assumption; try lia;
    try (left; reflexivity); try (intro Hpending; discriminate).
  - change (0 = 1) in H. discriminate.
  - change (binary <> 0). lia.
Qed.

Lemma solver_initial_stable : forall binary,
  stable_view (msolver_view 0 (solver_initial_model binary)).
Proof.
  intros binary. split.
  - intros v b Hassigned.
    change (mt_pv solver_initial_core v = Some b) in Hassigned.
    rewrite solver_initial_unassigned in Hassigned. discriminate.
  - split; [|split].
    + change (0 <= 0). lia.
    + intros v b d Hassigned _.
      change (mt_pv solver_initial_core v = Some b) in Hassigned.
      rewrite solver_initial_unassigned in Hassigned. discriminate.
    + intros d Hd. change (0 < d <= 0) in Hd. lia.
Qed.

Lemma solver_initial_weak : forall binary,
  0 < binary -> Z.even binary = true ->
  msolver_inv_weak 0 [] [] [] (solver_initial_model binary).
Proof.
  intros binary Hpositive Heven. constructor.
  - reflexivity.
  - lia.
  - apply solver_initial_shape; assumption.
  - split; [lia|constructor].
  - constructor.
  - exact solver_initial_trail_wf.
  - change (0 <= 0). lia.
  - change (0 <= 0 <= 0). lia.
  - reflexivity.
  - apply incl_refl.
  - constructor.
  - apply solver_initial_stable.
  - intros v c Hreason. change (None = Some c) in Hreason. discriminate.
  - intros v c Hreason. change (None = Some c) in Hreason. discriminate.
  - intros i l Hi _. change (0 <= i < 0) in Hi. lia.
  - unfold db_wf. cbn [msolver_db solver_initial_model].
    split; [ | split ]; constructor.
  - unfold db_matches_cnf. constructor.
  - unfold db_implied. constructor.
  - intros c Hin. contradiction.
  - unfold learnt_db. constructor.
  - unfold prob_db. constructor.
  - change (~ In binary (@nil Z)). simpl. tauto.
  - intros v Hv. lia.
  - intros v co Hv. change (0 <= v < 0) in Hv. lia.
  - intros v Hv. change (0 <= v < 0) in Hv. lia.
  - split; [reflexivity|]. intros l Hl. lia.
  - unfold solver_tags_clear. split; [constructor|reflexivity].
  - unfold heap_wf. cbn [msolver_heap solver_initial_model].
    split; [reflexivity|]. split; [constructor|].
    split; [constructor|]. split.
    + intros v Hv. lia.
    + intros i Hi. rewrite Zlength_nil in Hi. lia.
  - change (msat_fp32_nonnegative (Z_to_fp32 1)).
    destruct (MSatFloatFacts.Z_to_fp32_i32_positive_finite 1 ltac:(lia))
      as [Hfinite [Hsign Hnonzero]].
    apply MSatFloatFacts.fp32_finite_sign_nonnegative; assumption.
  - change (fp64_isFinite msat_fp64_seed). exact msat_fp64_seed_finite.
Qed.

Lemma solver_initial_inv : forall binary,
  0 < binary -> Z.even binary = true ->
  msolver_inv 0 [] [] [] (solver_initial_model binary).
Proof.
  intros binary Hpositive Heven. constructor.
  - apply solver_initial_weak; assumption.
  - unfold prop_level. constructor.
  - apply minisat_watch_frontier_before_first_dequeue. cbn. lia.
  - intros v Hv. lia.
  - intros d Hd. change (0 < d <= 0) in Hd. lia.
Qed.

Lemma solver_initial_entry : forall binary,
  0 < binary -> Z.even binary = true ->
  solver_normal_root 0 [] (solver_initial_model binary) /\
  msolver_seed_shadow (solver_initial_model binary) /\
  solver_query_watch_ready (solver_initial_model binary).
Proof.
  intros binary Hpositive Heven. split.
  - unfold solver_normal_root. split.
    + apply solver_initial_inv; assumption.
    + unfold solver_at_root. repeat split; reflexivity.
  - split.
    + apply msat_fp64_seed_shadow. reflexivity.
    + unfold solver_query_watch_ready. split.
      * intros _. apply minisat_watch_completed_empty_db__api_reentry.
        reflexivity.
      * intros Hpending. discriminate.
Qed.

Local Open Scope list_scope.
Local Open Scope Z_scope.

Definition solver_initial_layout (s binary : Z) : Assertion :=
  “ s <> 0 /\ 0 < binary /\ binary mod 2 = 0 ” &&
  (solver_scalars_rep s (solver_initial_model binary) **
   solver_fp_rep s (solver_initial_model binary) **
   solver_vecs_rep s (solver_initial_model binary) **
   solver_ptrs_rep s 0 0 0 0 0 0 0 binary 0 **
   stats_rep &( s # "solver_t" ->ₛ "stats") [0;0;0;0;0;0;0;0;0;0;0] **
   binary_scratch_rep binary []).

Lemma solver_initial_layout_growable : forall s binary,
  solver_initial_layout s binary |--
  “ s <> 0 /\ 0 < binary /\ Z.even binary = true ” &&
  solver_rep_growable s (solver_initial_model binary).
Proof.
  intros s binary. unfold solver_initial_layout. Intros.
  assert (Hpositive : 0 < binary) by tauto.
  assert (Heven : Z.even binary = true).
  { apply clause_ptr_even. tauto. }
  pose proof (solver_initial_shape binary Hpositive Heven) as Hshape.
  unfold solver_rep_growable. Exists 0 0 0 0 0 0 0 0.
  unfold solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_levels_slice_at, solver_trail_array_rep, solver_ptrs_rep.
  cbn [solver_initial_model solver_initial_core].
  unfold solver_int_tail, solver_ptr_tail, solver_char_tail,
    solver_double_tail, solver_wlists_tail, solver_array_tail.
  Exists 0 0 0 0 0 0 0 0.
  unfold wlists_rep, clause_db_rep.
  simpl.
  repeat match goal with
  | |- context [DoubleArray.seg ?x ?lo ?hi nil] =>
      rewrite <- (proj2 (DoubleArray.seg_empty x lo hi))
  | |- context [CharArray.seg ?x ?lo ?hi nil] =>
      rewrite <- (proj2 (CharArray.seg_empty x lo hi))
  | |- context [IntArray.seg ?x ?lo ?hi nil] =>
      rewrite <- (proj2 (IntArray.seg_empty x lo hi))
  | |- context [PtrArray.seg ?x ?lo ?hi nil] =>
      rewrite <- (proj2 (PtrArray.seg_empty x lo hi))
  | |- context [DoubleArray.undef_seg ?x ?lo ?lo] =>
      rewrite <- (proj2 (DoubleArray.undef_seg_empty x lo))
  | |- context [CharArray.undef_seg ?x ?lo ?lo] =>
      rewrite <- (proj2 (CharArray.undef_seg_empty x lo))
  | |- context [IntArray.undef_seg ?x ?lo ?lo] =>
      rewrite <- (proj2 (IntArray.undef_seg_empty x lo))
  | |- context [PtrArray.undef_seg ?x ?lo ?lo] =>
      rewrite <- (proj2 (PtrArray.undef_seg_empty x lo))
  | |- context [VecpArray.full ?x ?n nil] =>
      rewrite <- (proj2 (VecpArray.full_empty x n))
  | |- context [VecpArray.undef_seg ?x ?lo ?lo] =>
      rewrite <- (proj2 (VecpArray.undef_seg_empty x lo))
  end.
  msat_entailer_with ltac:(tauto || lia || vec_buf_solve).
Qed.

Lemma solver_initial_layout_result : forall s binary,
  solver_initial_layout s binary |--
  “ s <> 0 ” &&
  (EX M : msolver,
    “ ms_size M = 0 /\ ms_cap M = 0 /\
      solver_normal_root 0 [] M /\ msolver_seed_shadow M /\
      solver_query_watch_ready M ” && solver_rep_growable s M).
Proof.
  intros s binary. sep_apply solver_initial_layout_growable. Intros.
  assert (Hpositive : 0 < binary) by tauto.
  assert (Heven : Z.even binary = true) by tauto.
  pose proof (solver_initial_entry binary Hpositive Heven) as Hentry.
  Exists (solver_initial_model binary).
  apply _derivable1_andp_intros.
  - split_pure_spatial.
    + cancel.
    + split_pures; dump_pre_spatial; solve [tauto | reflexivity].
  - dump_pre_spatial. tauto.
Qed.


(* This fold deliberately retains the generic assumption list A. *)
Definition solver_update_ready (n : Z) (F : cnf) (A : list literal)
    (physical : msolver) : Prop :=
  let M := msolver_resume_pending physical in
  msolver_inv_assuming_strong n F A A M /\
  Zlength (mt_lim (ms_core M)) = 0 /\
  ms_capacity_root_propagation_pending M = 0.

Lemma solver_support_zero_assuming__update_surface : forall n F A I M,
  solver_support_inv n F A I 0 M -> solver_shape M ->
  Zlength (mt_lim (ms_core M)) = 0 ->
  msolver_inv_assuming_strong n F A A M /\ I = nil.
Proof.
  intros n F A I M Hsupport Hshape Hdepth.
  assert (Hatroot : solver_at_root (msolver_set_root M 0)).
  { change (Zlength (mt_lim (ms_core M)) = 0). exact Hdepth. }
  pose proof (msolver_inv_weak_assuming n F A I (msolver_set_root M 0)
    (msi_weak Hsupport) Hatroot) as Hweak_normal.
  assert (Hweak : msolver_inv_assuming n F A A M).
  { destruct Hweak_normal. constructor; assumption. }
  split.
  - constructor.
    + exact Hweak.
    + exact (msi_prop_level Hsupport).
    + exact (msi_watch_frontier Hsupport).
    + exact (msi_heap_covers Hsupport).
    + apply current_reasonless_earliest_no_levels; [exact Hdepth|].
      unfold solver_shape in Hshape. tauto.
  - pose proof (msw_assumptions (msi_weak Hsupport)) as Hinstalled.
    change (decisions_upto (ms_core M) 0 = I) in Hinstalled.
    change (nil = I) in Hinstalled. symmetry. exact Hinstalled.
Qed.

Lemma solver_assuming_zero_support__update_surface : forall n F A M,
  msolver_inv_assuming_strong n F A A M ->
  Zlength (mt_lim (ms_core M)) = 0 ->
  solver_support_inv n F A nil 0 M.
Proof.
  intros n F A M Hstrong Hdepth.
  pose proof (msolver_inv_ctx_root_empty__canceluntil_cap
    n F A (PropagationAssuming A) M (msas_weak Hstrong) Hdepth) as Hweak_base.
  pose proof (msa_A_wf (msas_weak Hstrong)) as HAwf.
  pose proof (msa_proc_sat (msas_weak Hstrong)) as HAsat.
  rewrite Hdepth in HAsat.
  assert (Hweak : msolver_inv_weak n F A nil (msolver_set_root M 0)).
  { destruct Hweak_base. constructor; try assumption.
    intros x Hin. contradiction. }
  unfold solver_support_inv. constructor.
  - exact Hweak.
  - exact (msas_prop_level Hstrong).
  - exact (msas_watch_frontier Hstrong).
  - exact (msas_heap_covers Hstrong).
  - apply current_reasonless_earliest_no_levels.
    + exact Hdepth.
    + change (0 <= 0). lia.
Qed.


Definition cnf_add_clause (F : cnf) (input : list Z) : cnf :=
  F ++ (lits_denote input :: nil).

Lemma solver_base_update_ready__incremental_public : forall n F M,
  solver_base_state n F M -> solver_update_ready n F nil M.
Proof.
  intros n F M Hbase.
  unfold solver_update_ready.
  rewrite (msolver_resume_pending_ordinary__api_reentry
    M (proj2 (proj2 Hbase))).
  exact Hbase.
Qed.

Lemma solver_query_update_ready__incremental_public : forall n F M,
  solver_query_ready n F M -> solver_update_ready n F nil M.
Proof.
  intros n F M [Hstrong [Hdepth [Hdrain Hpending]]].
  apply solver_base_update_ready__incremental_public.
  split; [exact Hstrong|split; assumption].
Qed.

Lemma solver_reentry_update_ready__incremental_public : forall n F M,
  solver_query_reentry n F M -> solver_update_ready n F nil M.
Proof.
  intros n F M Hreentry.
  apply solver_base_update_ready__incremental_public.
  exact (proj1 (solver_query_reentry_base_recovery__api_reentry
    n F M Hreentry)).
Qed.

Lemma solver_completed_query_watch__incremental_public : forall M,
  ms_capacity_root_propagation_pending M = 0 ->
  minisat_watch_completed M -> solver_query_watch_ready M.
Proof.
  intros M Hpending Hcomplete. unfold solver_query_watch_ready.
  split; [intros _; exact Hcomplete|].
  intros Hflag. rewrite Hpending in Hflag. discriminate.
Qed.

Lemma solver_update_completed_resume__incremental_public : forall n F A M,
  solver_update_ready n F A M -> solver_query_watch_ready M ->
  minisat_watch_completed (msolver_resume_pending M).
Proof.
  intros n F A M Hupdate [Hordinary Hsuspended].
  unfold solver_update_ready, msolver_resume_pending in Hupdate.
  unfold msolver_resume_pending.
  destruct (Z.eqb (ms_capacity_root_propagation_pending M) 1) eqn:Hflag.
  - apply Hsuspended. apply Z.eqb_eq. exact Hflag.
  - apply Hordinary. exact (proj2 (proj2 Hupdate)).
Qed.

(* ==== Entry bridges for the solve contract ==== *)


Lemma solver_update_watch_ready_base_completed__api_reentry : forall n F M,
  solver_update_ready n F nil M -> solver_query_watch_ready M ->
  minisat_base_watch_completed (msolver_resume_pending M).
Proof.
  intros n F M Hupd Hwr.
  pose proof (solver_update_completed_resume__incremental_public n F nil M Hupd Hwr)
    as Hfull.
  destruct Hupd as [Hstrong _].
  pose proof (msas_weak Hstrong) as Hweak.
  exact (minisat_full_completion_implies_base__api_reentry n _
           (msa_trail_wf Hweak) (msa_db_wf Hweak) Hfull).
Qed.

(* ==== Entry frame for the incremental solve spec ==== *)

Lemma solver_incremental_update_entry_frame__api_reentry :
  forall s begin finish n F A M,
  “ solver_update_ready n F nil M /\ solver_query_watch_ready M ” &&
  (solver_incremental_ownership_at s M ** assumptions_array n begin finish A) |--
  EX wl : Z,
    “ solver_update_ready n F nil M /\ solver_query_watch_ready M /\
      msolver_seed_shadow M /\ solver_query_reuse_guard M /\
      2 * ms_cap M <= INT_MAX ” &&
    (solver_rep_wl s M wl ** assumptions_array n begin finish A **
     solver_wlists_tail wl (2 * n) (2 * ms_cap M)).
Proof.
  intros s begin finish n F A M. unfold solver_incremental_ownership_at. Intros.
  assert (Hupdate : solver_update_ready n F nil M) by tauto.
  assert (Hwatch : solver_query_watch_ready M) by tauto.
  assert (Hseed : msolver_seed_shadow M) by tauto.
  assert (Hcap : 2 * ms_cap M <= INT_MAX) by tauto.
  assert (Hguard : solver_query_reuse_guard M) by (left; exact Hwatch).
  assert (Hsize : ms_size M = n).
  { destruct (msolver_resume_pending_size_cap__api_reentry M)
      as [Hsz [_ [_ _]]].
    rewrite <- Hsz. symmetry.
    exact (msa_size (msas_weak (proj1 Hupdate))). }
  sep_apply solver_rep_growable_split_wl__api_reentry. Intros wl.
  Exists wl. rewrite Hsize. msat_entailer_with ltac:(tauto).
Qed.

Lemma solver_incremental_common_result_from_expanded__api_reentry :
  forall s begin finish n F A entry ret wl,
  solver_query_reuse_guard entry ->
  2 * ms_cap entry <= INT_MAX ->
  assumptions_array n begin finish A **
  (solver_wlists_tail wl (2 * n) (2 * ms_cap entry) **
   ((“ ret = 1 ” &&
      (EX Msat : msolver,
        “ ms_size Msat = n /\ Zlength (ms_model Msat) = n /\
          model_is_total (ms_model Msat) /\
          models (rho_of_model (ms_model Msat)) F /\
          assumptions_true_under (rho_of_model (ms_model Msat)) A /\
          solver_query_ready n F Msat /\ msolver_seed_shadow Msat /\
          ms_cap Msat = ms_cap entry /\
          (solver_query_reuse_guard entry -> minisat_watch_completed Msat) ” &&
        solver_rep_wl s Msat wl)) ||
    (“ ret = 0 ” &&
      (EX Munsat : msolver,
        “ ms_size Munsat = n /\ cnf_unsat n (cnf_with_units F A) /\
          ms_cap Munsat = ms_cap entry /\
          (solver_query_reuse_guard entry ->
           solver_base_recovery n F Munsat /\ solver_query_reentry n F Munsat /\ msolver_seed_shadow Munsat) ” &&
        solver_rep_wl s Munsat wl)))) |--
  assumptions_array n begin finish A **
  (EX Mout : msolver,
    “ solver_public_query_entry n F Mout /\
      solver_query_reuse_guard Mout /\
      solver_update_ready n F nil Mout /\
      ((ret = 1 /\ solver_query_ready n F Mout /\
        Zlength (ms_model Mout) = n /\ model_is_total (ms_model Mout) /\
        models (rho_of_model (ms_model Mout)) F /\
        assumptions_true_under (rho_of_model (ms_model Mout)) A /\
        ms_capacity_root_propagation_pending Mout = 0 /\
        solver_query_watch_ready Mout) \/
       (ret = 0 /\ cnf_unsat n (cnf_with_units F A) /\
        ms_capacity_root_propagation_pending Mout = 0 /\
        (solver_query_watch_ready Mout \/ cnf_unsat n F))) ” &&
    solver_incremental_ownership_at s Mout).
Proof.
  intros s begin finish n F A entry ret wl Hwatch Hbound.
  cancel. Split.
  - Intros Msat. Exists Msat.
    match goal with
    | Hfacts : ms_size Msat = n /\ Zlength (ms_model Msat) = n /\
        model_is_total (ms_model Msat) /\
        models (rho_of_model (ms_model Msat)) F /\
        assumptions_true_under (rho_of_model (ms_model Msat)) A /\
        solver_query_ready n F Msat /\ msolver_seed_shadow Msat /\
        ms_cap Msat = ms_cap entry /\
        (solver_query_reuse_guard entry -> minisat_watch_completed Msat) |- _ =>
        destruct Hfacts as
          [Hsize [Hlen [Htotal [Hmodels [Hassumptions
            [Hready [Hseed [Hcap Hcompleted]]]]]]]]
    end.
    specialize (Hcompleted Hwatch).
    destruct (solver_query_ready_completed_reentry__api_reentry
      n F Msat Hready Hcompleted) as [Hentry Hwatch_new].
    assert (Hpublic : solver_public_query_entry n F Msat).
    { left. exact Hentry. }
    assert (Hguard : solver_query_reuse_guard Msat).
    { left. exact Hwatch_new. }
    pose proof (solver_query_update_ready__incremental_public
      n F Msat Hready) as Hupdate.
    assert (Hpending_new : ms_capacity_root_propagation_pending Msat = 0)
      by exact (proj2 (proj2 (proj2 Hready))).
    subst n. rewrite <- Hcap.
    sep_apply solver_rep_growable_join_wl__api_reentry.
    unfold solver_incremental_ownership_at. msat_entailer_with ltac:(tauto || lia).
  - Intros Munsat. Exists Munsat.
    match goal with
    | Hfacts : ms_size Munsat = n /\ cnf_unsat n (cnf_with_units F A) /\
        ms_cap Munsat = ms_cap entry /\
        (solver_query_reuse_guard entry ->
         solver_base_recovery n F Munsat /\ solver_query_reentry n F Munsat /\ msolver_seed_shadow Munsat) |- _ =>
        destruct Hfacts as [Hsize [Hunsat [Hcap Hrecovery]]]
    end.
    destruct (Hrecovery Hwatch) as [Hbase [Hreentry Hseed]].
    destruct (solver_query_reentry_reusable__api_reentry
      n F Munsat Hreentry) as [Hpublic Hguard].
    pose proof (solver_reentry_update_ready__incremental_public
      n F Munsat Hreentry) as Hupdate.
    assert (Hpending_new : ms_capacity_root_propagation_pending Munsat = 0)
      by exact (proj2 (proj2 (proj1 Hbase))).
    assert (Halternative :
      solver_query_watch_ready Munsat \/ cnf_unsat n F).
    { destruct Hreentry as [[Hready Hcompleted] | [Hbase_false Hfalse]].
      - left. apply solver_completed_query_watch__incremental_public;
          [exact (proj2 (proj2 (proj2 Hready)))|exact Hcompleted].
      - right.
        pose proof (solver_base_false_unsat__api_reentry n F Munsat nil
          Hbase_false Hfalse (Forall_nil _)) as Hu.
        unfold cnf_with_units in Hu. simpl in Hu.
        rewrite app_nil_r in Hu. exact Hu. }
    subst n. rewrite <- Hcap.
    sep_apply solver_rep_growable_join_wl__api_reentry.
    unfold solver_incremental_ownership_at. msat_entailer_with ltac:(tauto || lia).
Qed.

Local Open Scope Z_scope.

Lemma solver_addclause_zero_base_state__incremental_public :
  forall s begin n input_bound F entry input,
  solver_base_state n F entry -> minisat_watch_completed entry ->
  msolver_seed_shadow entry ->
  addclause_support_post_at s begin input_bound F nil nil entry input 0 |--
  EX M : msolver, EX current : list Z,
    “ Zlength current = Zlength input /\
      ms_size entry <= ms_size M /\
      solver_base_state (ms_size M) F M /\ minisat_watch_completed M /\
      cnf_unsat (Z.max n input_bound) (cnf_add_clause F input) ” &&
    (solver_incremental_ownership_at s M **
     IntArray.seg begin 0 (Zlength input) current).
Proof.
  intros s begin n input_bound F entry input Hbase Hwatch Hseed.
  assert (Hentry_size : ms_size entry = n).
  { symmetry. exact (msa_size (msas_weak (proj1 Hbase))). }
  unfold addclause_support_post_at. Intros M current Fnew.
  match goal with
  | H : addclause_support_transition input_bound F nil nil entry input 0
      M current Fnew |- _ => destruct H as [Htransition Hcompleted]
  end.
  destruct Htransition as [Hlen [Hsize [Hcap [Hbound [Hcontrol Hcases]]]]].
  destruct Hcases as [[_ [Hformula [Hinv Hunsat]]] | [Hbad _]].
  - subst Fnew.
    destruct Hbase as [_ [Hlevel Hpending]].
    specialize (Hcontrol (conj Hlevel (conj Hpending Hseed))).
    destruct Hcontrol as [Hlevel_new [Hpending_new Hseed_new]].
    change (ms_size entry <= ms_size M) in Hsize.
    change (2 * ms_cap M <= INT_MAX) in Hbound.
    change (msolver_seed_shadow M) in Hseed_new.
    change (cnf_unsat (Z.max (ms_size entry) input_bound)
      (cnf_add_clause F input)) in Hunsat.
    rewrite Hentry_size in Hunsat.
    specialize (Hcompleted Hwatch).
    assert (Hshape_export : solver_rep_growable s M |--
      “ solver_shape M ” && solver_rep_growable s M).
    { unfold solver_rep_growable, solver_rep_at.
      Intros wl act asg opos rsn lvl trl tgs.
      Exists wl act asg opos rsn lvl trl tgs.
      msat_entailer_with ltac:(tauto). }
    sep_apply Hshape_export. Intros.
    assert (Hbase_new : solver_base_state (ms_size M) F M).
    { apply solver_base_state_of_normalized__api_reentry.
      - exact Hinv.
      - assumption.
      - exact Hlevel_new.
      - exact Hpending_new. }
    Exists M current. unfold solver_incremental_ownership_at.
    msat_entailer_with ltac:(tauto).
  - discriminate Hbad.
Qed.

Lemma solver_simplify_zero_reusable__incremental_public :
  forall s n F entry lvl wl,
  minisat_watch_completed entry -> 2 * ms_cap entry <= INT_MAX ->
  solver_wlists_tail wl (2 * n) (2 * ms_cap entry) **
  solver_simplify_post_at s n F nil entry lvl 0 wl |--
  EX M : msolver,
    “ ms_size M = n /\ ms_cap M = ms_cap entry /\
      solver_base_state n F M /\ solver_public_query_entry n F M /\
      solver_query_reuse_guard M /\ cnf_unsat n F ” &&
    solver_incremental_ownership_at s M.
Proof.
  intros s n F entry lvl wl Hwatch Hbound.
  unfold solver_simplify_post_at, solver_simplify_post_sat_at,
    solver_simplify_post_unsat_at.
  Split.
  - Intros M. Exists M. msat_entailer_with lia.
  - Intros M.
    match goal with
    | Hfacts : ms_cap M = ms_cap entry /\
        ms_root_level M = ms_root_level entry /\
        msolver_inv_assuming n F nil nil M /\
        Zlength (mt_lim (ms_core M)) = 0 /\
        (minisat_watch_completed entry ->
          solver_base_recovery n F M /\ msolver_seed_shadow M) /\
        cancel_bound_ready M 0 /\
        ms_capacity_root_propagation_pending M = 0 /\
        minisat_resident_false_clause M /\
        cnf_unsat n (cnf_with_units F nil) |- _ =>
        destruct Hfacts as [Hcap [Hroot [Hweak [Hdepth [Hrecovery
          [Hcancel [Hpending [Hfalse Hunsat]]]]]]]]
    end.
    destruct (Hrecovery Hwatch) as [[Hbase Hcompletion] Hseed].
    assert (Hreentry : solver_query_reentry n F M).
    { right. split; assumption. }
    destruct (solver_query_reentry_reusable__api_reentry n F M Hreentry)
      as [Hpublic Hguard].
    assert (Hsize : ms_size M = n).
    { symmetry. exact (msa_size Hweak). }
    unfold cnf_with_units in Hunsat. cbn in Hunsat.
    rewrite app_nil_r in Hunsat.
    Exists M. subst n. rewrite <- Hcap.
    sep_apply solver_rep_growable_of_wl.
    unfold solver_incremental_ownership_at. msat_entailer_with lia.
Qed.

Lemma solver_addclause_result_same_ret__incremental_public :
  forall s begin n input_bound F entry input ret,
  solver_base_state n F entry -> minisat_watch_completed entry ->
  msolver_seed_shadow entry ->
  addclause_support_post_at s begin input_bound F nil nil entry input ret |--
  EX M : msolver, EX current : list Z,
    “ Zlength current = Zlength input /\ n <= ms_size M /\
      solver_query_watch_ready M /\
      ms_capacity_root_propagation_pending M = 0 /\
      ((ret = 1 /\ exists Fnew : cnf,
          solver_update_ready (ms_size M) Fnew nil M /\
          (forall rho, models rho Fnew <-> models rho (cnf_add_clause F input))) \/
       (ret = 0 /\ cnf_unsat (Z.max n input_bound) (cnf_add_clause F input) /\
          solver_update_ready (ms_size M) F nil M)) ” &&
    (solver_incremental_ownership_at s M **
     IntArray.seg begin 0 (Zlength input) current).
Proof.
  intros s begin n input_bound F entry input ret Hbase Hwatch Hseed.
  assert (Hentry_size : ms_size entry = n).
  { symmetry. exact (msa_size (msas_weak (proj1 Hbase))). }
  destruct (Z.eq_dec ret 1) as [-> | Hnot1].
  - sep_apply (solver_addclause_success_base_state__api_reentry
      s begin n input_bound F entry input Hbase Hwatch Hseed).
    Intros M current Fnew.
    match goal with
    | Hfacts : Zlength current = Zlength input /\
        ms_size entry <= ms_size M /\ ms_cap entry <= ms_cap M /\
        solver_base_state (ms_size M) Fnew M /\ minisat_watch_completed M /\ _ |- _ =>
        destruct Hfacts as [Hlen [Hsize [Hcap [Hbase_new [Hcomplete Hequiv]]]]]
    end.
    pose proof (solver_base_update_ready__incremental_public
      (ms_size M) Fnew M Hbase_new) as Hupdate.
    pose proof (solver_completed_query_watch__incremental_public M
      (proj2 (proj2 Hbase_new)) Hcomplete) as Hwatch_new.
    assert (Hsuccess : exists Fnew : cnf,
      solver_update_ready (ms_size M) Fnew nil M /\
      (forall rho, models rho Fnew <-> models rho (cnf_add_clause F input))).
    { exists Fnew. split; assumption. }
    assert (Hpending_new : ms_capacity_root_propagation_pending M = 0)
      by exact (proj2 (proj2 Hbase_new)).
    rewrite Hentry_size in Hsize. Exists M current.
    msat_entailer_with ltac:(tauto).
  - destruct (Z.eq_dec ret 0) as [-> | Hnot0].
    + sep_apply (solver_addclause_zero_base_state__incremental_public
        s begin n input_bound F entry input Hbase Hwatch Hseed).
      Intros M current.
      match goal with
      | Hfacts : Zlength current = Zlength input /\
          ms_size entry <= ms_size M /\ solver_base_state (ms_size M) F M /\
          minisat_watch_completed M /\ _ |- _ =>
          destruct Hfacts as [Hlen [Hsize [Hbase_new [Hcomplete Hunsat]]]]
      end.
      pose proof (solver_base_update_ready__incremental_public
        (ms_size M) F M Hbase_new) as Hupdate.
      pose proof (solver_completed_query_watch__incremental_public M
        (proj2 (proj2 Hbase_new)) Hcomplete) as Hwatch_new.
      assert (Hpending_new : ms_capacity_root_propagation_pending M = 0)
        by exact (proj2 (proj2 Hbase_new)).
      rewrite Hentry_size in Hsize. Exists M current.
      msat_entailer_with ltac:(tauto).
    + unfold addclause_support_post_at. Intros M current Fnew.
      match goal with
      | H : addclause_support_transition input_bound F nil nil entry input ret
          M current Fnew |- _ =>
          destruct H as [[_ [_ [_ [_ [_ Hcases]]]]] _]
      end.
      destruct Hcases as [[Hret _] | [Hret _]]; contradiction.
Qed.

Lemma solver_simplify_result_same_ret__incremental_public :
  forall s n F entry lvl wl ret,
  minisat_watch_completed entry -> 2 * ms_cap entry <= INT_MAX ->
  solver_wlists_tail wl (2 * n) (2 * ms_cap entry) **
  solver_simplify_post_at s n F nil entry lvl ret wl |--
  EX M : msolver,
    “ solver_update_ready n F nil M /\
      ((ret = 1 /\ solver_query_ready n F M /\
          solver_query_reuse_guard M /\
          ms_capacity_root_propagation_pending M = 0 /\
          solver_query_watch_ready M) \/
       (ret = 0 /\ cnf_unsat n F /\ solver_public_query_entry n F M /\
          ms_capacity_root_propagation_pending M = 0 /\
          solver_query_reuse_guard M)) ” &&
    solver_incremental_ownership_at s M.
Proof.
  intros s n F entry lvl wl ret Hwatch Hbound.
  destruct (Z.eq_dec ret 1) as [-> | Hnot1].
  - sep_apply (solver_simplify_success_query_entry__api_reentry
      s n F entry lvl wl (or_introl Hwatch) Hbound).
    Intros M.
    match goal with
    | Hfacts : ms_size M = n /\ ms_cap M = ms_cap entry /\
        solver_query_ready n F M /\ solver_query_entry n F M /\
        solver_query_watch_ready M |- _ =>
        destruct Hfacts as [Hsize [Hcap [Hready [_ Hwatch_new]]]]
    end.
    pose proof (solver_query_update_ready__incremental_public n F M Hready)
      as Hupdate.
    assert (Hguard : solver_query_reuse_guard M) by (left; exact Hwatch_new).
    assert (Hpending_new : ms_capacity_root_propagation_pending M = 0)
      by exact (proj2 (proj2 (proj2 Hready))).
    Exists M. msat_entailer_with ltac:(tauto).
  - destruct (Z.eq_dec ret 0) as [-> | Hnot0].
    + sep_apply (solver_simplify_zero_reusable__incremental_public
        s n F entry lvl wl Hwatch Hbound).
      Intros M.
      match goal with
      | Hfacts : ms_size M = n /\ ms_cap M = ms_cap entry /\
          solver_base_state n F M /\ solver_public_query_entry n F M /\
          solver_query_reuse_guard M /\ cnf_unsat n F |- _ =>
          destruct Hfacts as [Hsize [Hcap [Hbase [Hpublic [Hguard Hunsat]]]]]
      end.
      pose proof (solver_base_update_ready__incremental_public n F M Hbase)
        as Hupdate.
      assert (Hpending_new : ms_capacity_root_propagation_pending M = 0)
        by exact (proj2 (proj2 Hbase)).
      Exists M. msat_entailer_with ltac:(tauto).
    + unfold solver_simplify_post_at, solver_simplify_post_sat_at,
    solver_simplify_post_unsat_at.
      Split;
        Intros M; Exists M; msat_entailer_with lia.
Qed.


(* ===== Public route lemmas ===== *)

Lemma wand_frame_weaken__public : forall (B B' R A : Assertion),
  (B' |-- B) -> (B ** R |-- A) -> B ** R |-- B ** (B' -* A).
Proof.
  intros B B' R A Hweak Hjoin. cancel.
  apply derivable1_wand_sepcon_adjoint.
  sep_apply_l_atomic Hweak. sep_apply_r_atomic Hjoin. cancel.
Qed.

(* [solver_shape] is carried by the ownership footprint itself, so a caller
   who holds only the fold can still read it off. *)
Lemma solver_rep_growable_shape__public : forall s M,
  solver_rep_growable s M |-- “ solver_shape M ” && solver_rep_growable s M.
Proof.
  intros s M. unfold solver_rep_growable, solver_rep_at.
  Intros wl act asg opos rsn lvl trl tgs.
  Exists wl act asg opos rsn lvl trl tgs.
  msat_entailer_with ltac:(tauto).
Qed.

(* solver_nvars: the `size` cell out of the public ownership fold and back. *)
Lemma solver_incremental_size_cell_frame__public : forall s M P Q,
  (P |-- &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M) ->
  (solver_incremental_ownership_at s M |-- Q) ->
  solver_incremental_ownership_at s M |--
  &( s # "solver_t" ->ₛ "size") # Int |-> ms_size M ** (P -* Q).
Proof.
  intros s M P Q HP HQ.
  unfold solver_incremental_ownership_at at 1. Intros.
  unfold solver_rep_growable at 1. Intros wl act asg opos rsn lvl trl tgs.
  unfold solver_rep_at at 1. Intros.
  unfold solver_nonlevel_rep_at at 1. unfold solver_nonlevel_rep_nostats_at at 1.
  sep_apply peel_scalars_size.
  apply wand_frame_weaken__public; [exact HP|].
  sep_apply_r_atomic HQ.
  sep_apply join_scalars_size.
  unfold solver_incremental_ownership_at, solver_rep_growable.
  Exists wl act asg opos rsn lvl trl tgs.
  unfold solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  msat_entailer_with ltac:(tauto).
Qed.

(* Expose the clauses vector of the incremental ownership and restore it. *)
Lemma solver_incremental_clauses_frame__public : forall s M P Q,
  (P |-- solver_clauses_rep s (db_words (ms_prob M))) ->
  (solver_incremental_ownership_at s M |-- Q) ->
  solver_incremental_ownership_at s M |--
  solver_clauses_rep s (db_words (ms_prob M)) ** (P -* Q).
Proof.
  intros s M P Q HP HQ.
  assert (Hfold : Vecp.rep &( s # "solver_t" ->ₛ "clauses") (map fst (ms_prob M))
    |-- solver_clauses_rep s (db_words (ms_prob M)))
    by (unfold solver_clauses_rep, db_words; cancel).
  unfold solver_incremental_ownership_at at 1. Intros.
  unfold solver_rep_growable at 1. Intros wl act asg opos rsn lvl trl tgs.
  unfold solver_rep_at at 1. Intros.
  unfold solver_nonlevel_rep_at at 1. unfold solver_nonlevel_rep_nostats_at at 1.
  unfold solver_vecs_rep at 1.
  sep_apply Hfold.
  cancel.
  match goal with |- ?R |-- ?X -* ?Y => apply (derivable1_wand_sepcon_adjoint R X Y) end.
  sep_apply HP.
  unfold solver_clauses_rep, db_words.
  sep_apply_r_atomic HQ.
  unfold solver_incremental_ownership_at, solver_rep_growable.
  Exists wl act asg opos rsn lvl trl tgs.
  unfold solver_rep_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  unfold solver_vecs_rep.
  msat_entailer_with ltac:(tauto).
Qed.

Lemma peel_stats_conflicts__public : forall p st,
  stats_rep p st |--
  &( p # "stats_t" ->ₛ "conflicts") # UInt64 |-> stats_conflicts st **
  stats_without_conflicts_rep p st.
Proof.
  intros p st. unfold stats_rep, stats_without_conflicts_rep.
  msat_entailer_with ltac:(lia).
Qed.

Lemma join_stats_conflicts__public : forall p st,
  &( p # "stats_t" ->ₛ "conflicts") # UInt64 |-> stats_conflicts st **
  stats_without_conflicts_rep p st |-- stats_rep p st.
Proof.
  intros p st. unfold stats_rep, stats_without_conflicts_rep.
  msat_entailer_with ltac:(lia).
Qed.

(* solver_nconflicts: same shape, with the computed address identity between
   the annotation's dotted [&(s->stats.conflicts)] and [stats_rep]'s
   [&(&(s->stats)->conflicts)]. *)
Lemma solver_incremental_conflicts_cell_frame__public : forall s M P Q,
  (P |-- &( s # "solver_t" ->ₛ "stats" .ₛ "conflicts") # UInt64
         |-> stats_conflicts (ms_stats M)) ->
  (solver_incremental_ownership_at s M |-- Q) ->
  solver_incremental_ownership_at s M |--
  &( s # "solver_t" ->ₛ "stats" .ₛ "conflicts") # UInt64
    |-> stats_conflicts (ms_stats M) ** (P -* Q).
Proof.
  intros s M P Q HP HQ.
  unfold solver_incremental_ownership_at at 1. Intros.
  unfold solver_rep_growable at 1. Intros wl act asg opos rsn lvl trl tgs.
  unfold solver_rep_at at 1. Intros.
  unfold solver_nonlevel_rep_at at 1.
  set (stats_ptr := &( s # "solver_t" ->ₛ "stats")).
  assert (Haddr :
    &( s # "solver_t" ->ₛ "stats" .ₛ "conflicts") =
    &( stats_ptr # "stats_t" ->ₛ "conflicts"))
    by (unfold stats_ptr; csimpl; reflexivity).
  rewrite Haddr. rewrite Haddr in HP.
  sep_apply peel_stats_conflicts__public.
  apply wand_frame_weaken__public; [exact HP|].
  sep_apply join_stats_conflicts__public.
  sep_apply_r_atomic HQ.
  unfold solver_incremental_ownership_at, solver_rep_growable.
  Exists wl act asg opos rsn lvl trl tgs.
  unfold solver_rep_at, solver_nonlevel_rep_at. unfold stats_ptr.
  msat_entailer_with ltac:(tauto).
Qed.

(** Read a cancellation argument without introducing a native snapshot.
    The separating wand retains exactly the original call precondition. *)
Definition solver_cancel_root_frame
    (s level : Z) (M : msolver) (wl : Z) : Assertion :=
  (&( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M) -*
    solver_cancel_pre s level M wl.

Lemma solver_cancel_root_peel : forall s level M wl,
  solver_cancel_pre s level M wl |--
  &( s # "solver_t" ->ₛ "root_level") # Int |-> ms_root_level M **
  solver_cancel_root_frame s level M wl.
Proof.
  intros s level M wl.
  unfold solver_cancel_root_frame.
  unfold solver_cancel_pre at 1. Intros.
  unfold solver_cancel_owned at 1. Intros act asg opos rsn trl tgs.
  unfold solver_nonlevel_rep_at at 1.
  unfold solver_nonlevel_rep_nostats_at at 1. Intros.
  sep_apply peel_scalars_root.
  apply wand_frame_weaken__public; [cancel|].
  sep_apply join_scalars_root.
  unfold solver_cancel_pre, solver_cancel_owned.
  Intros. Exists act asg opos rsn trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  msat_entailer_with ltac:(tauto).
Qed.

(** A freshly allocated clause is owned here before the caller publishes its
    pointer in the selected database.  Both watches have already been appended;
    their capacities can change independently through checked vector growth. *)
Definition clause_new_pending_at_root
    (s begin lvl n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (words : list Z) (c sel wl root : Z) : Assertion :=
  let i0 := lit_neg_c (Znth 0 words 0) in
  let i1 := lit_neg_c (Znth 1 words 0) in
  “ 0 <= sel <= 1 /\ n = ms_size entry /\
    clause_new_stage_ready_root n F A_arr A_inst entry entry words sel root /\
    clause_allocator_fresh entry c /\ i0 <> i1 ” &&
  (Vecp.rep (solver_selected_vec s sel)
      (db_words (solver_selected_db sel entry)) **
    Vecp.rep (Vecp.slot wl i0)
      (Znth i0 (ms_wm entry) nil ++
       (clause_watch_word c words (Znth 1 words 0) :: nil)) **
    Vecp.rep (Vecp.slot wl i1)
      (Znth i1 (ms_wm entry) nil ++
       (clause_watch_word c words (Znth 0 words 0) :: nil)) **
    MiniSatClause.rep c (solver_selected_is_learnt sel) words **
    clause_db_rep (solver_selected_db sel entry) **
    clause_new_transaction_rest_at_gen s wl i0 i1 entry lvl sel **
    &(s # "solver_t" ->ₛ "size") # Int |-> n **
    IntArray.seg begin 0 (Zlength words) words).


(** Intermediate recording state: the semantic database already owns the new
    clause, but its native learned vector still has the caller's old contents.
    All heap resources remain explicit; closing requires the published vector. *)
Definition solver_record_rep_at (s : Z) (M : msolver) (wl lvl : Z)
    (stored : list Z) : Assertion :=
  “ solver_shape M ” &&
  (Vecp.rep &(s # "solver_t" ->ₛ "learnts") stored **
   clause_db_rep (ms_learnt M) **
   clause_new_frame_at s M lvl **
   &(s # "solver_t" ->ₛ "size") # Int |-> ms_size M **
   solver_wlists_handle s wl **
   wlists_rep wl (ms_size M) (ms_wm M)).

Definition solver_record_enqueue_vecs_frame (s : Z) (M : msolver) (stored : list Z) : Assertion :=
  Vecp.rep &( s # "solver_t" ->ₛ "clauses")
    (map fst (ms_prob M)) **
  Vecp.rep &( s # "solver_t" ->ₛ "learnts")
    stored **
  Veci.rep &( s # "solver_t" ->ₛ "tagged")
    (ms_tagged M) **
  Veci.rep &( s # "solver_t" ->ₛ "stack")
    (ms_stack M) **
  Veci.rep &( s # "solver_t" ->ₛ "order")
    (ms_order M) **
  Veci.rep &( s # "solver_t" ->ₛ "model")
    (ms_model M).

Definition solver_record_enqueue_cells_at
    (s : Z) (M : msolver) (wl act opos tgs : Z) (scalars : Assertion) (stored : list Z) : Assertion :=
    scalars ** solver_fp_rep s M **
    solver_record_enqueue_vecs_frame s M stored **
    (&( s # "solver_t" ->ₛ "wlists") # Ptr |-> wl **
     &( s # "solver_t" ->ₛ "activity") # Ptr |-> act **
     &( s # "solver_t" ->ₛ "orderpos") # Ptr |-> opos **
     &( s # "solver_t" ->ₛ "binary") # Ptr |-> ms_binary M **
     &( s # "solver_t" ->ₛ "tags") # Ptr |-> tgs) **
    (DoubleArray.seg act 0 (ms_size M) (ms_activity M) **
     solver_double_tail act (ms_size M) (ms_cap M) **
     IntArray.seg opos 0 (ms_size M) (ms_orderpos M) **
     solver_int_tail opos (ms_size M) (ms_cap M) **
     CharArray.seg tgs 0 (ms_size M) (ms_tags M) **
     solver_char_tail tgs (ms_size M) (ms_cap M)) **
    wlists_rep wl (ms_size M) (ms_wm M) **
    clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M) **
    binary_scratch_rep (ms_binary M) (ms_binary_lits M) **
    stats_rep &( s # "solver_t" ->ₛ "stats") (ms_stats M).


Definition solver_record_enqueue_frame_at (s : Z) (M : msolver) (wl : Z)
    (stored : list Z) : Assertion :=
  EX act opos tgs : Z,
    solver_record_enqueue_cells_at s M wl act opos tgs
      (solver_scalars_without_qtail_rep s M) stored.

Definition record_finish_with_capacity
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry enqueued : msolver) (words : list Z) (c : Z)
    (cla_inc : fp32) (M' : msolver) : Prop :=
  record_finish_success n F A_arr A_inst entry enqueued words c cla_inc M'.
