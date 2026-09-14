Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Import naive_C_Rules.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_goal.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_proof_common.
Local Open Scope sac.

(* ------------------------------------------------------------------ *)
(* Part 4 file index.  C functions covered, in the order their proofs *)
(* appear below, with the wit families each one contributes:          *)
(*   clause_cmp           -- partial_solve, return, which_implies     *)
(*                           wits (12)                                *)
(*   clause_remove        -- partial_solve, which_implies wits (12)   *)
(*   solver_analyze       -- entail, partial_solve, safety,           *)
(*                           which_implies wits (42)                  *)
(*   solver_lit_removable -- which_implies wits (6)                   *)
(*   solver_propagate     -- entail, partial_solve, which_implies     *)
(*                           wits (57)                                *)
(*   solver_reducedb      -- entail, partial_solve, return wits (8)   *)
(*   solver_search        -- entail, which_implies wits (22)          *)
(*   solver_solve         -- entail, return wits (18)                 *)
(* Every proof_of_* below is a VC named in solver_qcp_goal.v; this    *)
(* part contributes no shared (cross-part) declarations.              *)
(* ------------------------------------------------------------------ *)

(* clause_cmp header-word side conditions: the header word is non-negative
   because the word list length is *)
Ltac msat_clause_cmp_hdr_word_nonneg_p4 :=
  Unfold;
  left; intros; apply derivable1s_coq_prop_r;
  apply clause_hdr_word_nonneg;
  apply Zlength_nonneg.

(* clause_remove focus step: hand the watch-list focus lemma its index bound *)
Ltac msat_clause_remove_focus_wlists_p4 :=
  Unfold;
  right; intros;
  apply wlists_rep_focus_at__clause_remove;
  lia.

(* Re-fold the watch-list source hole around the handle the scan carries *)
Ltac msat_propagate_source_hole_close_p4 :=
  Unfold;
  left; intros;
  unfold wlists_source_hole_handle;
  entailer_with ltac:(lia).

(* Index bound of the solver_solve assumption loop: pure arithmetic *)
Ltac msat_solve_assume_bound_lia_p4 := Unfold; intros; lia.

(* Scan watch-memory length side condition: the only pure fact the entailer needs
   is that the pre-state watch-memory list has non-negative length *)
Tactic Notation "msat_propagate_scan_wm_nonneg_p4" ident(wm) :=
  Unfold;
  right; intros; entailer_with ltac:(lia);
  pose proof (Zlength_nonneg wm); lia.

(* The pure conjunct is emitted twice and the tag index reaches the goal as a
   fresh binder, so the offsets are normalised first and the defining equation
   then closes both copies *)
Ltac msat_analyze_learnt_offset_congruence_p4 :=
  aggressive_pre_process;
  dump_pre_spatial;
  rewrite Z.sub_0_r in *;
  congruence.

(* Clause-word range obligations of the learnt scan; the conjunct is sometimes
   emitted twice, so the closer runs on every remaining goal *)
Tactic Notation "msat_analyze_clause_word_int_range_via_wf_p4"
    ident(Hwf) ident(j) ident(cw) ident(Hlit) :=
  Unfold;
  aggressive_pre_process; dump_pre_spatial;
  msat_analyze_close_clause_word_int_range Hwf j cw Hlit.

(* Safety obligations of the analyze clause scan: the tagged-count bound follows
   from the scan invariant, which is taken from the context by shape *)
Ltac msat_analyze_scan_count_bound_p4 :=
  pre_process_default;
  match goal with
  | H : analyze_clause_scan_inv _ _ _ _ _ ?M _ _ _ _ _ _ _ _ _ ?Sc ?Rc ?ls _ ?c
    |- _ => msat_analyze_bound_scan_count_by_tagged H c Sc Rc M ls
  end.

(* The solver_search decision-loop entailments differ only in which retval binder
   the decision transition is stated over, so the transition hypothesis is taken
   by shape; the two learnt-clause witnesses are the arguments *)
Tactic Notation "msat_search_decision_loop_close_p4" ident(lw) ident(lc) :=
  Unfold;
  aggressive_pre_process; unfold solver_search_loop;
  match goal with
  | H : solver_search_decision_transition _ _ _ _ _ _ _ ?Md |- _ =>
      msat_search_reestablish_loop_after_decision H Md lw lc
  end.

(* One compaction step of reduceDB: pick the replaced word list and the unchanged
   model, then discharge the db_compaction_step conjuncts *)
Tactic Notation "msat_reducedb_compaction_step_close_p4"
    ident(i) ident(j) ident(words) ident(Mcur) :=
  Unfold; left; intros;
  entailer_with ltac:(lia);
  Exists (replace_Znth j (Znth (i - 0) words 0) words) Mcur;
  entailer_with ltac:(lia);
  try (unfold db_compaction_step; repeat split; auto).

(* The unit-propagation enqueue obligation of the watch scan, in both the
   moved-watch and the same-watch shape: read the trail well-formedness and the
   size equation out of the scan semantics, take the watched literal's range from
   the replacement invariant, and feed the enqueue_input conjuncts.  The three
   hypotheses are taken from the context by shape *)
Ltac msat_propagate_unit_enqueue_input_p4 :=
  Unfold;
  right; intros;
  match goal with
  | Hshape : solver_shape ?Ms,
    Hsem : solver_propagation_scan_semantics _ _ _ ?K ?Ms _ _ _ _,
    Hinv : propagation_replacement_scan_inv ?n ?Ms _
             (propagation_normalized_clause ?w0 _ _) _ |- _ =>
      destruct Hsem as [Hscan | Hconf]; [ | destruct Hconf as [Hnz _]; lia ];
      destruct Hscan as (_ & Hweak & _);
      unfold solver_propagation_weak in Hweak;
      destruct Hweak as [_ Hweak];
      assert (Hwf : mtrail_wf n (ms_core Ms))
        by (destruct K; cbn in Hweak;
            [exact (msw_trail_wf Hweak) | exact (msa_trail_wf Hweak)]);
      assert (Hn : n = ms_size Ms)
        by (destruct K; cbn in Hweak;
            [exact (msw_size Hweak) | exact (msa_size Hweak)]);
      unfold propagation_replacement_scan_inv in Hinv;
      destruct Hinv as (Hoffset & Hall & _);
      assert (Hwatch : lit_wf_c n w0)
        by (rewrite Forall_forall in Hall; apply Hall;
            unfold propagation_normalized_clause; simpl; auto);
      pose proof Hshape as Hshape0; unfold solver_shape in Hshape0;
      destruct Hshape0 as
        (Hsizecap & Hcapmax & Htwice & Hassignlen & Hlevelslen &
         Hreasonlen & Horderposlen & Hactivitylen & Htagslen & Htraillen &
         Hqheadrange & Hpendingrange & Hrootbit & Hrootpending & Hqtailcap &
         Hwmlen & Hwcapslen & Hbinarylen & Hstatslen & Hrootnonneg &
         Hbinaryne & Hbinaryeven);
      assert (Hroom :
          Znth (lit_var_c w0) (mt_assigns (ms_core Ms)) 0 = 0 ->
          ms_qtail Ms < ms_size Ms)
        by (intros Hz;
            pose proof (lit_var_c_in_range n w0 Hwatch) as Hv;
            assert (Hnin :
                ~ In (lit_var_c w0)
                    (map lit_var_c (mt_trail (ms_core Ms))))
              by (intros Hin;
                  apply (proj2 (mtw_assigned_iff Hwf (lit_var_c w0) Hv)) in Hin;
                  contradiction);
            assert (Hnd : NoDup
                (map lit_var_c (mt_trail (ms_core Ms)) ++
                 cons (lit_var_c w0) nil))
              by (apply NoDup_snoc; [exact (mtw_trail_nodup Hwf) | exact Hnin]);
            pose proof (msat_map_lit_var_c_snoc_in_range n
                (mt_trail (ms_core Ms)) (lit_var_c w0)
                (mtw_trail_lits Hwf) Hv) as Hbounds;
            pose proof (NoDup_Z_bounded_length _ n (mtw_n_nonneg Hwf)
              Hnd Hbounds) as Hlen;
            rewrite length_app, length_map in Hlen; simpl in Hlen;
            rewrite Nat2Z.inj_add in Hlen; simpl in Hlen;
            rewrite <- Zlength_correct in Hlen;
            rewrite Hn in Hlen; lia);
      destruct Hwatch as [Hwatchlo Hwatchhi];
      assert (Hvals : Forall (fun x => -1 <= x <= 1)
          (mt_assigns (ms_core Ms)))
        by (rewrite Forall_forall; intros x Hx;
            pose proof (mtw_cells Hwf) as Hcells;
            rewrite Forall_forall in Hcells; specialize (Hcells x Hx);
            unfold lbool_cell in Hcells; lia);
      repeat split_pures; dump_pre_spatial;
      match goal with
      | |- enqueue_input _ _ _ _ _ _ _ => idtac
      | _ => lia
      end;
      pose proof (mtw_trail_bound Hwf) as Htrailbound;
      unfold enqueue_input; repeat split;
      try exact Htwice;
      try exact Hassignlen;
      try exact Hlevelslen;
      try exact Hreasonlen;
      try exact Htraillen;
      try exact Hroom;
      try exact Hvals;
      lia
  end.

(* UNSAT return of solver_solve: the assumption array is the full prefix of the
   raw list, which is what the return shape asks for *)
Tactic Notation "msat_solve_unsat_return_close_p4" ident(Mfalse) :=
  Unfold;
  right; intros; unfold assumptions_array, solver_unsat_arm_at;
  lazymatch goal with
  | HA : _ = assumption_prefix ?raw (Zlength ?raw) |- _ =>
      msat_solve_close_unsat_return HA raw Mfalse; tauto
  end.

(* Assumption loop of solver_solve: one true assumption is consumed, so the loop
   invariant is re-established one index further on; the advance fact and the
   end-pointer equation are taken from the context by shape *)
Ltac msat_solve_assumption_advance_close_p4 :=
  Unfold; intros;
  lazymatch goal with
  | Hadv : assumption_true_advance _ _ _ ?raw ?k ?Mcur,
    Hend : _ = _ + Zlength ?raw * sizeof ( INT ) |- _ =>
      Left;
      Exists raw (k + 1) Mcur;
      unfold assumption_true_advance in Hadv;
      entailer_with ltac:(lia);
      rewrite Hend;
      entailer_with ltac:(lia)
  end.

(* Return arm of solver_analyze: re-fold the post from the core-equivalence fact,
   whose two models the caller names, and whose final model the witnesses are
   stated over *)
Tactic Notation "msat_analyze_core_equiv_close_p4"
    ident(M0) ident(Mfinal) ident(words_final) ident(cap_final)
    ident(blevel) ident(lits) :=
  Unfold; left; intros;
  lazymatch goal with
  | Hcore : analysis_core_equiv M0 Mfinal |- _ =>
      repeat sep_apply store_ptr_undef_store_ptr;
      repeat sep_apply store_int_undef_store_int;
      let Hreuse := fresh "Hbase_reuse" in
      pose proof (analysis_core_equiv_base_completion__api_reentry
        M0 Mfinal Hcore) as Hreuse;
      unfold solver_analyze_post, veci_rep;
      unfold analysis_core_equiv in Hcore;
      Exists Mfinal words_final cap_final blevel lits;
      unfold veci_rep_at;
      entailer_with ltac:(int_auto); try assumption
  end.

(* Capacity arm of solver_solve: the assumption array is the full prefix of the
   raw list and the prepared capacity preserves the model size, so the capacity
   arm of the post closes on the prepared model *)
Tactic Notation "msat_solve_capacity_arm_close_p4" ident(H) ident(Mcap) :=
  Unfold;
  right;
  intros;
  lazymatch goal with
  | HA : _ = assumption_prefix ?raw (Zlength ?raw),
    HS : ms_size _ = ?n |- _ =>
      unfold solver_prepare_capacity_post;
      Intros Mcap;
      unfold assumptions_array;
      unfold assumption_prefix in HA;
      rewrite sublist_self in HA by reflexivity;
      destruct H as (Hcap & Hroot & Hshadow & Hvariable_cap & Hreuse);
      rewrite HS in Hroot;
      assert (Hsize : ms_size Mcap = n)
        by (eapply solver_operational_root_size; eauto);
      lazymatch type of Hreuse with
      | minisat_base_watch_completed ?prepared -> _ =>
          lazymatch goal with
          | Hentry : solver_query_reuse ?entry prepared |- _ =>
              let Hwatch := fresh "Hpublic_watch" in
              let Hready := fresh "Hquery_ready" in
              assert (Hwatch : solver_query_reuse_guard entry -> solver_query_watch_ready Mcap)
                by (intro Hready; exact (Hreuse (Hentry Hready)))
          end
      end;
      Exists Mcap raw;
      unfold solver_capacity_arm_at;
      entailer_with ltac:(lia)
  end.

(* The two binary-conflict entailments of the propagate watch scan (same-watch
   and moved-watch) share one script: pin the scan-begin model, take the
   conflict-free arm of the scan semantics, recover the physical watch-list
   layout around the inspected slot, and close the binary clause store.  The
   hypotheses are taken from the context by shape; the binders the goal is
   stated over are handed in by the call site.  The scan-semantics hypothesis is
   destructed through a copy so that the folded original stays in the context -
   the final entailer discharges one of its side conditions from it *)
Tactic Notation "msat_propagate_scan_binary_ready_p4"
    ident(Mentry) ident(Mscan) ident(rv2) ident(rv3) ident(rv4)
    ident(rv6) ident(scan_current) ident(ii) ident(jj) ident(confl)
    ident(retained) ident(garbage) ident(rest) ident(tagged_memory)
    ident(raw_prefix) ident(raw_suffix) :=
  Unfold;
  entailer_with ltac:(lia);
  left;
  intros;
  assert (Hscanbegin :
    msolver_propagation_scan_begin Mentry (ms_simpdb_props Mscan)
      (Znth 2 (ms_stats Mscan) 0) = Mscan) by congruence;
  rewrite Hscanbegin;
  (* the tagged-literal equation is picked by its shape, not by the generated name it
     carries in the goal file. *)
  lazymatch goal with
  | Hrv : rv2 = tag_lit _ |- _ => repeat rewrite replace_Znth_Znth in Hrv
  end;
  subst rv2;
  subst rv3;
  subst rv4;
  subst scan_current;
  lazymatch goal with
  | Hsem : solver_propagation_scan_semantics
             ?n ?F ?A ?K ?M ?p ?cfl ?kept ?rst,
    Hphysical : propagation_watch_scan_physical
                  ?source ?kept2 ?moved ?rst2 ?grb ?memory ?i0 ?j0,
    Hlt : ii < Zlength ?source2 |- _ =>
      assert (Hconfl0 : confl = 0)
        by (unfold solver_propagation_scan_semantics in Hsem;
            destruct Hsem as [[Hzero _] | [_ [Hrest0 _]]];
            [ exact Hzero
            | subst rest;
              unfold propagation_watch_scan_physical in Hphysical;
              destruct Hphysical as [_ [Hmemory [_ [Hprefix Hlength]]]];
              rewrite app_nil_r in Hmemory;
              rewrite Hmemory, Hprefix in Hlength;
              rewrite <- Hlength in Hlt;
              exfalso; exact (Z.lt_irrefl ii Hlt) ])
  end;
  subst confl;
  lazymatch goal with
  | Hsem : solver_propagation_scan_semantics
             ?n ?F ?A ?K ?M ?p 0 ?kept ?rst,
    Hphysical : propagation_watch_scan_physical
                  ?source ?kept2 ?moved ?rst2 ?grb ?memory ?i0 ?j0,
    Hupdate : ?tecm = replace_Znth ii (Znth ii tagged_memory 0) tagged_memory,
    Htag : tagged_memory = replace_Znth jj (Znth ii tagged_memory 0) ?wm,
    Hwatch : ?wm = raw_prefix ++ Znth ii tagged_memory 0 :: raw_suffix,
    Hrawlen : Zlength raw_prefix = ii,
    Hretval6 : rv6 = lit_neg_c ?lp,
    Hbinarylen : Zlength (ms_binary_lits Mscan) = 2 |- _ =>
      pose proof Hsem as Hsem_arm;
      unfold solver_propagation_scan_semantics in Hsem_arm;
      destruct Hsem_arm as [Hlive | Hconflict];
      [ destruct Hlive as
          [_ [Hweak [Hprop_level [Hheap_ready
             [Hheap_covers [Hreasonless [Hcurrent_level Hscan_tail]]]]]]];
        pose proof Hphysical as Hphysical_live;
        unfold propagation_watch_scan_physical in Hphysical_live;
        destruct Hphysical_live as
          [Hscan_inv [Hmemory [Hkept_len [Hprefix_len Hmemory_len]]]];
        assert (Hii0 : 0 <= ii) by (rewrite <- Hprefix_len; apply Zlength_nonneg);
        assert (Hjj0 : 0 <= jj) by (rewrite <- Hkept_len; apply Zlength_nonneg);
        assert (Hjjii : jj <= ii)
          by (rewrite <- Hkept_len, <- Hprefix_len, Zlength_app;
              pose proof (Zlength_nonneg garbage); lia);
        assert (Hconcat :
          raw_prefix ++ Znth ii tagged_memory 0 :: raw_suffix =
            (retained ++ garbage) ++ rest)
          by (rewrite <- Hwatch; rewrite Hmemory, app_assoc; reflexivity);
        assert (Hrest : rest = Znth ii tagged_memory 0 :: raw_suffix)
          by (apply app_eq_app in Hconcat as [[m [Hm Htail]] | [m [Hm Htail]]];
              [ assert (HZ : Zlength m = 0)
                  by (rewrite Hm in Hrawlen;
                      rewrite Zlength_app, Hprefix_len in Hrawlen; lia);
                destruct m as [|a m];
                [ exact Htail
                | exfalso; rewrite Zlength_cons in HZ;
                  pose proof (Zlength_nonneg m); lia ]
              | assert (HZ : Zlength m = 0)
                  by (rewrite Hm in Hprefix_len;
                      rewrite Zlength_app, Hrawlen in Hprefix_len; lia);
                destruct m as [|a m];
                [ symmetry; simpl in Htail; exact Htail
                | exfalso; rewrite Zlength_cons in HZ;
                  pose proof (Zlength_nonneg m); lia ] ]);
        entailer_with ltac:(lia);
        Exists (replace_Znth (1 - 0) rv6 (ms_binary_lits Mscan))
               (clause_lits_addr (ms_binary Mscan));
        entailer_with ltac:(int_auto);
        [ unfold IntArray.full, IntArray.seg, store_array;
          entailer_with ltac:(lia);
          rewrite Hupdate; rewrite replace_Znth_Znth; reflexivity
        | rewrite Hupdate; rewrite replace_Znth_Znth; exact Htag
        | unfold propagation_binary_conflict_scan_ready;
          split; [assumption|];
          split; [exact Hheap_covers|];
          split; [exact Hreasonless|];
          split; [exact Hcurrent_level|];
          split; [assumption|];
          split; [assumption|];
          split; [lia|];
          split; [assumption|];
          split; lia
        | replace (1 - 0) with 1 by lia;
          rewrite Znth_replace_Znth_Same by lia; exact Hretval6
        | rewrite Zlength_replace_Znth; exact Hbinarylen ]
      | destruct Hconflict as [Hnonzero _];
        exfalso; apply Hnonzero; reflexivity ]
  end.

(* Both binary-conflict scan VCs land on the same four residual goals once the scratch
   cells have been re-spelled: the copy progress with nothing copied yet, the untouched
   second scratch literal, the tagged literal just written, and the scratch length.  The
   goal is selected by its own shape and every fact is handed in, so the tactic never
   mentions a name the goal file generated; both call sites run it under an `all:` selector,
   which also states that exactly those four goals are left. *)
Tactic Notation "msat_binary_copy_start_close_p4"
    ident(raw_suffix) constr(Hmemory) constr(Hprefix) constr(Htagged)
    constr(Hscratch_lit) constr(Hretval) constr(Hcurrent) constr(Hscratch_len) :=
  lazymatch goal with
  | |- context [binary_watch_copy_progress] =>
      unfold binary_watch_copy_progress;
      exists nil, raw_suffix;
      split; [exact Hmemory|];
      split; [exact Hprefix|];
      split; [lia|];
      split; [reflexivity|];
      split; [rewrite Zlength_nil; lia|];
      split; [rewrite Zlength_nil; lia|];
      split;
      [ simpl; exact Htagged
      | rewrite Htagged, Zlength_replace_Znth; reflexivity ]
  | |- Znth _ _ _ = lit_neg_c _ =>
      rewrite Znth_replace_Znth_Diff by lia; exact Hscratch_lit
  | |- Znth _ _ _ = tag_lit _ =>
      rewrite Znth_replace_Znth_Same by lia;
      rewrite Hretval, Hcurrent; reflexivity
  | |- Zlength _ = _ =>
      rewrite Zlength_replace_Znth; exact Hscratch_len
  end.


(* The two `stop_alias` return VCs of clause_cmp share their whole script and differ only
   in which library rule closes them (the activity-first and the header-first case), so the
   rule is passed in and everything else is written once. *)
Tactic Notation "msat_clause_cmp_alias_stop_p4"
    ident(y_pre) ident(x_pre) ident(x_activity) ident(db) ident(activities)
    ident(x_words) constr(rule) :=
  Unfold; left; intros; subst y_pre;
  bind_fact ( 0 < x_pre ) as H_x_pre;
  bind_fact ( x_pre % 2 = 0 ) as H_x_pre_2;
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative;
  (* the three facts are handed to the rule by `assumption`: a tactic body may not spell
     a hypothesis name that its own `bind_fact` has just introduced. *)
  assert (Hxmod : x_pre mod 2 = 0)
    by (apply rem_two_mod_two__clause_cmp; assumption);
  unfold msat_true;
  apply (rule db activities x_pre x_words x_activity); assumption.


(* Replace one spatial atom inside a separating-conjunction context by [emp] and
   return the residual assertion.  The analyze close-up peels the atoms it
   cancels by hand out of the pre-condition one at a time with this. *)
Ltac msat_sep_replace_atom_with_emp_p4 atom P :=
  lazymatch P with
  | context C [atom] =>
      let R := context C [emp] in constr:(R)
  end.

(* Close an entailment whose left-hand side is the nest of [emp] residuals left
   behind by the peeling above.  The six undef tails, the [stack] vector and
   the two literal counters arrive as one folded sub-conjunction
   ([solver_analyze_inert_at]), so after the peel the residual is a TREE of
   [emp]s rather than a right-nested chain: both branches of every [**] are
   walked and the recursion bottoms out on [reflexivity] at each [emp] leaf.  The leaf test has to be [reflexivity] and
   not a goal pattern -- at this point the conclusion is stated over
   [Syntax.sepcon], which the [**] notation of this file does not match.
   [n] is a depth bound passed as a constr, e.g.
   [msat_collapse_emp_sepcon_tree_p4 (8%nat)]. *)
Ltac msat_collapse_emp_sepcon_tree_p4 n :=
  lazymatch n with
  | O => reflexivity
  | S ?n' =>
      first
        [ reflexivity
        | transitivity (emp ** emp);
          [ apply derivable1s_sepcon_proper;
            [ msat_collapse_emp_sepcon_tree_p4 n'
            | msat_collapse_emp_sepcon_tree_p4 n' ]
          | apply derivable1_sepcon_emp_l ] ]
  end.


(* The backward-scan loop invariant carries a `cancel_ready` witness whose weak-solver
   component fixes both the shape of the analysed model and the well-formedness of its
   clause database.  Both facts come out of the same two destructurings, so they are
   derived together here instead of twice inside the VC proof.  The two length equations
   are the `ms_stats` / `ms_activity` conjuncts of `solver_shape` that the invariant itself
   does not carry: the VC reads them off the frame it is holding. *)
Lemma analyze_backward_scan_shape_db_p4 :
  forall anz_n anz_F anz_A_arr K Mdone anz_focus words_done cnt ind Sdone Rdone
    learnt_done,
    analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mdone anz_focus words_done cnt
      ind Sdone Rdone learnt_done ->
    Zlength (ms_stats Mdone) = 11 ->
    Zlength (ms_activity Mdone) = anz_n ->
    solver_shape Mdone /\ db_wf anz_n (msolver_db Mdone).
Proof.
  intros anz_n anz_F anz_A_arr K Mdone anz_focus words_done cnt ind Sdone Rdone
    learnt_done Hscan Hstats Hactivity.
  unfold analyze_backward_scan_inv in Hscan.
  destruct Hscan as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Hlits_done
    [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  split.
  {
    destruct Hready as
      (Mbase & Hcancel & Hequiv & Hheap & Hcovers & Hreasonless & Hfocus & Hcla).
    destruct Hcancel as [[Hpending Hweak] Hcancel_rest].
    destruct K as [A_inst | A_proc]; cbn in Hweak.
    - pose proof (msw_size Hweak) as Hsize.
      pose proof (msw_shape Hweak) as Hshape0.
      unfold analysis_core_equiv in Hequiv;
        unfold solver_shape in Hshape0 |- *;
        unfold heap_wf, msolver_heap in Hheap; cbn in Hheap;
        unfold analysis_tags_exact in Htags;
        intuition (try congruence; try lia).
    - pose proof (msa_size Hweak) as Hsize.
      pose proof (msa_shape Hweak) as Hshape0.
      unfold analysis_core_equiv in Hequiv;
        unfold solver_shape in Hshape0 |- *;
        unfold heap_wf, msolver_heap in Hheap; cbn in Hheap;
        unfold analysis_tags_exact in Htags;
        intuition (try congruence; try lia).
  }
  {
    destruct Hready as [Mbase [Hcancel [Hequiv _]]].
    destruct Hcancel as [Hweak0 _].
    destruct Hweak0 as [_ Hinv].
    assert (Hdb0 : db_wf anz_n (msolver_db Mbase)).
    { destruct K; cbn in Hinv.
      - exact (msw_db_wf Hinv).
      - exact (msa_db_wf Hinv). }
    unfold analysis_core_equiv in Hequiv.
    destruct Hequiv as
      (_ & _ & _ & _ & _ & _ & _ & Hprob & Hlearnt & _).
    unfold msolver_db in *. rewrite Hprob, Hlearnt. exact Hdb0.
  }
Qed.

(* The clause the backward scan is focused on is either the binary clause or a member of
   one of the two clause databases; in every case the four cells the scan holds fold back
   into `clause_db_rep` of both databases plus the binary clause.  The two database arms
   differ only in which of `ms_prob`/`ms_learnt` is decomposed.  The pointer bound is the
   one fact the VC gets from the frame rather than from the databases. *)
Lemma analysis_focus_clause_db_close_p4 :
  forall anz_n Mdone c is_learnt2 clause_words2 lits,
    db_wf anz_n (msolver_db Mdone) ->
    solver_shape Mdone ->
    0 <= ms_binary Mdone ->
    clause_lits_pointer c lits ->
    clause_hdr_addr c # Int |-> clause_hdr_word is_learnt2
        (Zlength clause_words2) **
    activity_state c is_learnt2 **
    IntArray.seg lits 0 (Zlength clause_words2) clause_words2 **
    analysis_clause_remainder Mdone c is_learnt2 clause_words2
    |-- clause_db_rep (ms_prob Mdone) **
        clause_db_rep (ms_learnt Mdone) **
        MiniSatClause.rep (ms_binary Mdone) false (ms_binary_lits Mdone).
Proof.
  intros anz_n Mdone c is_learnt2 clause_words2 lits Hdb Hshape Hbinary_nonneg
    H_clause_lits_pointer.
    unfold clause_lits_pointer in H_clause_lits_pointer. subst lits.
    unfold analysis_clause_remainder.
    Split.
    - Intros_p Hbinary.
      destruct Hbinary as [Hc [Htag Hwords_binary]].
      subst c is_learnt2 clause_words2.
      unfold MiniSatClause.rep.
      entailer_with ltac:(lia).
      + apply Zlength_nonneg.
      + pose proof (solver_shape_binary_nonnull Mdone Hshape). lia.
      + apply clause_ptr_mod2. unfold solver_shape in Hshape. tauto.
    - Intros_p Hreal.
      unfold clause_db_pair_remainder.
      Split.
      + Intros co pre post.
        destruct H as [Hdecomp [Hwords_co Htag]].
        assert (Hin : In (c, co) (msolver_db Mdone)).
        { unfold msolver_db. rewrite Hdecomp.
          apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
        assert (Hpos : 0 < c) by (eapply db_wf_ptr_pos; eauto).
        assert (Heven : Z.even c = true) by (eapply db_wf_even; eauto).
        rewrite Hdecomp.
        transitivity
          ((clause_db_rep pre ** clause_db_rep ((c, co) :: post)) **
           (clause_db_rep (ms_learnt Mdone) **
            MiniSatClause.rep (ms_binary Mdone) false
              (ms_binary_lits Mdone))).
        * rewrite clause_db_rep_cons.
          unfold MiniSatClause.rep.
          cbn [fst snd]. rewrite Htag, Hwords_co.
          entailer_with ltac:(lia).
          -- apply Zlength_nonneg.
          -- apply clause_ptr_mod2. exact Heven.
        * sep_apply (clause_db_rep_app_intro pre ((c, co) :: post)).
          entailer_with ltac:(lia).
      + Intros co pre post.
        destruct H as [Hdecomp [Hwords_co Htag]].
        assert (Hin : In (c, co) (msolver_db Mdone)).
        { unfold msolver_db. rewrite Hdecomp.
          apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
        assert (Hpos : 0 < c) by (eapply db_wf_ptr_pos; eauto).
        assert (Heven : Z.even c = true) by (eapply db_wf_even; eauto).
        rewrite Hdecomp.
        transitivity
          ((clause_db_rep pre ** clause_db_rep ((c, co) :: post)) **
           (clause_db_rep (ms_prob Mdone) **
            MiniSatClause.rep (ms_binary Mdone) false
              (ms_binary_lits Mdone))).
        * rewrite clause_db_rep_cons.
          unfold MiniSatClause.rep.
          cbn [fst snd]. rewrite Htag, Hwords_co.
          entailer_with ltac:(lia).
          -- apply Zlength_nonneg.
          -- apply clause_ptr_mod2. exact Heven.
        * sep_apply (clause_db_rep_app_intro pre ((c, co) :: post)).
          msat_manual_entailer_with ltac:(lia).
Qed.

(* While the analyze loop runs, `max_literals` and `tot_literals` are held as separate
   cells beside the rest of the statistics block; folding the three back together is all
   that is needed to rebuild `stats_rep`. *)
Lemma analyze_stats_frame_close_p4 :
  forall s Mdone,
    stats_analyze_frame &(s # "solver_t" ->ₛ "stats")
        (ms_stats Mdone) **
    &(s # "solver_t" ->ₛ "stats" .ₛ "max_literals") # UInt64
      |-> Znth 9 (ms_stats Mdone) 0 **
    &(s # "solver_t" ->ₛ "stats" .ₛ "tot_literals") # UInt64
      |-> Znth 10 (ms_stats Mdone) 0
    |-- stats_rep &(s # "solver_t" ->ₛ "stats") (ms_stats Mdone).
Proof.
  intros s Mdone.
    unfold stats_analyze_frame, stats_rep.
    entailer_with ltac:(lia).
    csimpl.
    msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== clause_cmp partial_solve wits (4 proofs) ===== *)
Lemma proof_of_clause_cmp_partial_solve_wit_2_pure : clause_cmp_partial_solve_wit_2_pure.
Proof.
  msat_clause_cmp_hdr_word_nonneg_p4.
Qed.

Lemma proof_of_clause_cmp_partial_solve_wit_3_pure : clause_cmp_partial_solve_wit_3_pure.
Proof.
  msat_clause_cmp_hdr_word_nonneg_p4.
Qed.

Lemma proof_of_clause_cmp_partial_solve_wit_4_pure : clause_cmp_partial_solve_wit_4_pure.
Proof.
  msat_clause_cmp_hdr_word_nonneg_p4.
Qed.

Lemma proof_of_clause_cmp_partial_solve_wit_5_pure : clause_cmp_partial_solve_wit_5_pure.
Proof.
  msat_clause_cmp_hdr_word_nonneg_p4.
Qed.

(* ===== clause_cmp return wits (7 proofs) ===== *)
Lemma proof_of_clause_cmp_return_wit_1 : clause_cmp_return_wit_1.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( retval_2 = 2 ) as H_retval_2.
  bind_fact ( retval_2 = clause_hdr_word msat_true (Zlength y_words) ÷ 2 ) as H_retval_2_2.
  bind_fact ( retval > 2 ) as H_retval.
  bind_fact ( retval = clause_hdr_word msat_true (Zlength x_words) ÷ 2 ) as H_retval_3.
  bind_fact ( 0 < x_pre ) as H_x_pre.
  bind_fact ( x_pre % 2 = 0 ) as H_x_pre_2.
  bind_fact ( 0 < y_pre ) as H_y_pre.
  bind_fact ( y_pre % 2 = 0 ) as H_y_pre_2.
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative.
  bind_fact ( msat_fp32_nonnegative y_activity ) as H_msat_fp32_nonnegative_2.
  pose proof (clause_hdr_word_quot2__clause_cmp true (Zlength y_words)
    (Zlength_nonneg y_words)) as Hylen0.
  pose proof (clause_hdr_word_quot2__clause_cmp true (Zlength x_words)
    (Zlength_nonneg x_words)) as Hxlen0.
  unfold msat_true in H_retval_2_2, H_retval_3.
  apply Z.gt_lt in H_retval.
  assert (Hylen : Zlength y_words = 2).
  { rewrite <- Hylen0.
    transitivity retval_2.
    - symmetry. exact H_retval_2_2.
    - exact H_retval_2. }
  assert (Hxlen : 2 < Zlength x_words).
  { rewrite <- Hxlen0, <- H_retval_3. exact H_retval. }
  assert (Hxmod : x_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_x_pre_2. }
  assert (Hymod : y_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_y_pre_2. }
  unfold msat_true.
  exact (learnt_cmp_result_lt_two_yx_headers__clause_cmp
    db activities x_pre x_words x_activity
    y_pre y_words y_activity
    H_x_pre Hxmod H_msat_fp32_nonnegative H_y_pre Hymod H_msat_fp32_nonnegative_2
    Hxlen (or_introl Hylen)).
Qed.

Lemma proof_of_clause_cmp_return_wit_2 : clause_cmp_return_wit_2.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( fp32_lt retval_3 retval_4 ) as H_fp32_lt.
  bind_fact ( msat_fp32_same retval_4 y_activity ) as H_msat_fp32_same.
  bind_fact ( msat_fp32_same retval_3 x_activity ) as H_msat_fp32_same_2.
  bind_fact ( retval_2 = clause_hdr_word msat_true (Zlength y_words) ÷ 2 ) as H_retval_2.
  bind_fact ( retval > 2 ) as H_retval.
  bind_fact ( retval = clause_hdr_word msat_true (Zlength x_words) ÷ 2 ) as H_retval_3.
  bind_fact ( 0 < x_pre ) as H_x_pre.
  bind_fact ( x_pre % 2 = 0 ) as H_x_pre_2.
  bind_fact ( 0 < y_pre ) as H_y_pre.
  bind_fact ( y_pre % 2 = 0 ) as H_y_pre_2.
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative.
  bind_fact ( msat_fp32_nonnegative y_activity ) as H_msat_fp32_nonnegative_2.
  pose proof (clause_hdr_word_quot2__clause_cmp true (Zlength x_words)
    (Zlength_nonneg x_words)) as Hxlen0.
  unfold msat_true in H_retval_2, H_retval_3.
  apply Z.gt_lt in H_retval.
  assert (Hxlen : 2 < Zlength x_words).
  { rewrite <- Hxlen0, <- H_retval_3. exact H_retval. }
  assert (Hxmod : x_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_x_pre_2. }
  assert (Hymod : y_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_y_pre_2. }
  unfold msat_fp32_same in H_msat_fp32_same, H_msat_fp32_same_2.
  subst retval_4 retval_3.
  unfold msat_true.
  exact (learnt_cmp_result_lt_two_activity_first__clause_cmp
    db activities x_pre x_words x_activity
    y_pre y_words y_activity
    H_x_pre Hxmod H_msat_fp32_nonnegative H_y_pre Hymod H_msat_fp32_nonnegative_2
    Hxlen (or_intror H_fp32_lt)).
Qed.

Lemma proof_of_clause_cmp_return_wit_3 : clause_cmp_return_wit_3.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( fp32_lt retval_3 retval_4 ) as H_fp32_lt.
  bind_fact ( msat_fp32_same retval_4 x_activity ) as H_msat_fp32_same.
  bind_fact ( msat_fp32_same retval_3 x_activity ) as H_msat_fp32_same_2.
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative.
  unfold msat_fp32_same in H_msat_fp32_same, H_msat_fp32_same_2.
  subst retval_4 retval_3.
  pose proof (MSatFloatFacts.fp32_nonnegative_eq_refl
    x_activity H_msat_fp32_nonnegative) as Heq.
  unfold fp32_lt, fp32_eq in H_fp32_lt, Heq.
  congruence.
Qed.

Lemma proof_of_clause_cmp_return_wit_4 : clause_cmp_return_wit_4.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( fp32_ge retval_3 retval_4 ) as H_fp32_ge.
  bind_fact ( msat_fp32_same retval_4 y_activity ) as H_msat_fp32_same.
  bind_fact ( msat_fp32_same retval_3 x_activity ) as H_msat_fp32_same_2.
  bind_fact ( retval_2 <> 2 ) as H_retval_2.
  bind_fact ( retval_2 = clause_hdr_word msat_true (Zlength y_words) ÷ 2 ) as H_retval_2_2.
  bind_fact ( retval = clause_hdr_word msat_true (Zlength x_words) ÷ 2 ) as H_retval.
  bind_fact ( 0 < x_pre ) as H_x_pre.
  bind_fact ( x_pre % 2 = 0 ) as H_x_pre_2.
  bind_fact ( 0 < y_pre ) as H_y_pre.
  bind_fact ( y_pre % 2 = 0 ) as H_y_pre_2.
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative.
  bind_fact ( msat_fp32_nonnegative y_activity ) as H_msat_fp32_nonnegative_2.
  pose proof (clause_hdr_word_quot2__clause_cmp true (Zlength y_words)
    (Zlength_nonneg y_words)) as Hylen0.
  unfold msat_true in H_retval_2_2, H_retval.
  assert (Hynotbinary : Zlength y_words <> 2).
  { intros Hylen.
    apply H_retval_2.
    transitivity (clause_hdr_word true (Zlength y_words) ÷ 2).
    - exact H_retval_2_2.
    - transitivity (Zlength y_words); assumption. }
  assert (Hxmod : x_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_x_pre_2. }
  assert (Hymod : y_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_y_pre_2. }
  unfold msat_fp32_same in H_msat_fp32_same, H_msat_fp32_same_2.
  subst retval_4 retval_3.
  unfold msat_true.
  exact (learnt_cmp_result_stop_two_activity_first__clause_cmp
    db activities x_pre x_words x_activity
    y_pre y_words y_activity
    H_x_pre Hxmod H_msat_fp32_nonnegative H_y_pre Hymod H_msat_fp32_nonnegative_2
    (or_intror (conj Hynotbinary H_fp32_ge))).
Qed.

Lemma proof_of_clause_cmp_return_wit_5 : clause_cmp_return_wit_5.
Proof.
  msat_clause_cmp_alias_stop_p4 y_pre x_pre x_activity db activities x_words
    learnt_cmp_result_stop_alias_activity_first__clause_cmp.
Qed.

Lemma proof_of_clause_cmp_return_wit_6 : clause_cmp_return_wit_6.
Proof.
  msat_clause_cmp_alias_stop_p4 y_pre x_pre x_activity db activities x_words
    learnt_cmp_result_stop_alias_header_first__clause_cmp.
Qed.

Lemma proof_of_clause_cmp_return_wit_7 : clause_cmp_return_wit_7.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( retval <= 2 ) as H_retval.
  bind_fact ( retval = clause_hdr_word msat_true (Zlength x_words) ÷ 2 ) as H_retval_2.
  bind_fact ( 0 < x_pre ) as H_x_pre.
  bind_fact ( x_pre % 2 = 0 ) as H_x_pre_2.
  bind_fact ( 0 < y_pre ) as H_y_pre.
  bind_fact ( y_pre % 2 = 0 ) as H_y_pre_2.
  bind_fact ( msat_fp32_nonnegative x_activity ) as H_msat_fp32_nonnegative.
  bind_fact ( msat_fp32_nonnegative y_activity ) as H_msat_fp32_nonnegative_2.
  pose proof (clause_hdr_word_quot2__clause_cmp true (Zlength x_words)
    (Zlength_nonneg x_words)) as Hxlen0.
  unfold msat_true in H_retval_2.
  assert (Hxshort : Zlength x_words <= 2).
  { rewrite <- Hxlen0, <- H_retval_2. exact H_retval. }
  assert (Hxmod : x_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_x_pre_2. }
  assert (Hymod : y_pre mod 2 = 0).
  { apply rem_two_mod_two__clause_cmp. exact H_y_pre_2. }
  unfold msat_true.
  exact (learnt_cmp_result_stop_two_xy_headers__clause_cmp
    db activities x_pre x_words x_activity
    y_pre y_words y_activity
    H_x_pre Hxmod H_msat_fp32_nonnegative H_y_pre Hymod H_msat_fp32_nonnegative_2
    (or_introl Hxshort)).
Qed.

(* ===== clause_cmp which_implies wits (1 proofs) ===== *)
Lemma proof_of_clause_cmp_which_implies_wit_1 : clause_cmp_which_implies_wit_1.
Proof.
  Unfold.
  intros activities db x y Hx Hy.
  destruct (Z.eq_dec x y) as [Heq | Hneq].
  - subst y.
    sep_apply (learnt_sort_rep_focus_one__clause_cmp db activities x Hx).
    Intros xlits xa.
    unfold learnt_clause_snapshot_raw.
    Left. Exists xlits xa.
    entailer_with ltac:(int_auto).
    rewrite Z.rem_mod_nonneg by lia. tauto.
  - sep_apply (learnt_sort_rep_focus_two__clause_cmp
      db activities x y Hx Hy Hneq).
    Intros xlits ylits xa ya.
    unfold learnt_clause_snapshot_raw.
    Right. Exists ylits xlits ya xa.
    entailer_with ltac:(int_auto);
      rewrite Z.rem_mod_nonneg by lia; tauto.
Qed.

(* ===== clause_remove partial_solve wits (9 proofs) ===== *)
Lemma proof_of_clause_remove_partial_solve_wit_23_pure : clause_remove_partial_solve_wit_23_pure.
Proof.
  naive_C_Rules.aggressive_pre_process.
  msat_clause_hdr_word_bounds_pure clause_words is_learnt.
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_25_pure : clause_remove_partial_solve_wit_25_pure.
Proof.
  aggressive_pre_process;
  bind_fact ( retval_8 = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval_8;
  bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready;
  unfold clause_remove_ready in H_clause_remove_ready;
  destruct H_clause_remove_ready as
    (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1);
  dump_pre_spatial.
  (* The RHS emits five pure goals that are reordered, partly duplicated copies of three
     distinct statements, so each script below is `try`-guarded and dispatches by shape
     rather than by bullet position.  The dispatch runs on every one of them, hence `all:`. *)
  all: (try (rewrite Zlength_replace_Znth by lia; exact Hwm));
    (try exact Hcaps).
  all: (assert (Hne : lit_neg_c (Znth 1 clause_words 0) <>
                     lit_neg_c (Znth 0 clause_words 0)) by
    (intro Heq; apply Hvars;
     apply (f_equal lit_var_c) in Heq;
     rewrite !lit_var_c_neg in Heq; symmetry; exact Heq));
    (rewrite Znth_replace_Znth_Diff
    by (rewrite ?Hwm; try lia; congruence)).
  all: (assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg);
    (assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; exact Hsize));
    (rewrite zdiv_equiv in H_retval_8 by lia);
    (rewrite clause_hdr_word_div2 in H_retval_8 by exact Hsize).
  all: (assert (Hb : (2 <? Zlength clause_words)%Z = true)
    by (apply Z.ltb_lt; lia));
    (unfold clause_watch_word in Hin1);
    (rewrite Hb in Hin1).
  (* the watch index reaches the goal as the fresh binder the symbolic executor
     bound to `lit_neg_c (Znth 1 clause_words 0)`; pick it by shape.  A `match goal`
     pattern may not name context variables, so the pattern uses wildcards; only the
     watch index satisfies both halves. *)
  all: (match goal with
       | H : ?v = lit_neg_c _ |- context [ Znth ?v _ nil ] => rewrite H
       end);
    (exact Hin1).
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_26_pure : clause_remove_partial_solve_wit_26_pure.
Proof.
  aggressive_pre_process.
  all: (bind_fact ( retval_10 = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval_10);
    (bind_fact ( clause_remove_ready n c_pre clause_words wm caps stats0 ) as H_clause_remove_ready);
    (unfold clause_remove_ready in H_clause_remove_ready);
    (destruct H_clause_remove_ready as
    (Hlen & Hforall & Hvars & Hwm & Hcaps & Hstats & Hin0 & Hin1)).
  (* The RHS emits five pure goals that are reordered and partly duplicated copies of four
     statements, and the two membership goals have become the same obligation, so dispatch
     by shape rather than by bullet position.  A `match goal` pattern below may not name
     context variables, hence the wildcards. *)
  all: (dump_pre_spatial);
    (try (rewrite Zlength_replace_Znth by lia; exact Hwm));
    (try exact Hcaps).
  all: (match goal with
       | H : ?v = tag_of_lit _ |- context [ vecp_remove_member ?v _ ] =>
           rewrite H
       end);
    (assert (Hne : lit_neg_c (Znth 1 clause_words 0) <>
                     lit_neg_c (Znth 0 clause_words 0)) by
    (intro Heq; apply Hvars;
     apply (f_equal lit_var_c) in Heq;
     rewrite !lit_var_c_neg in Heq; symmetry; exact Heq));
    (rewrite Znth_replace_Znth_Diff
    by (rewrite ?Hwm; try lia; congruence)).
  all: (assert (Hsize : 0 <= Zlength clause_words) by apply Zlength_nonneg);
    (assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
    by (apply clause_hdr_word_nonneg; exact Hsize));
    (rewrite zdiv_equiv in H_retval_10 by lia);
    (rewrite clause_hdr_word_div2 in H_retval_10 by exact Hsize).
  all: (assert (Hb : (2 <? Zlength clause_words)%Z = false)
    by (apply Z.ltb_ge; lia));
    (unfold clause_watch_word in Hin1);
    (rewrite Hb in Hin1);
    (match goal with
       | H : ?v = lit_neg_c _ |- context [ Znth ?v _ nil ] => rewrite H
       end);
    (exact Hin1).
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_27_pure : clause_remove_partial_solve_wit_27_pure.
Proof.
  aggressive_pre_process;
  dump_pre_spatial; apply clause_hdr_word_nonneg; apply Zlength_nonneg.
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_28_pure : clause_remove_partial_solve_wit_28_pure.
Proof.
  aggressive_pre_process;
  dump_pre_spatial; apply clause_hdr_word_nonneg; apply Zlength_nonneg.
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_29_pure : clause_remove_partial_solve_wit_29_pure.
Proof.
  aggressive_pre_process;
  dump_pre_spatial; apply clause_hdr_word_nonneg; apply Zlength_nonneg.
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_30_pure : clause_remove_partial_solve_wit_30_pure.
Proof.
  aggressive_pre_process;
  dump_pre_spatial; apply clause_hdr_word_nonneg; apply Zlength_nonneg.
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_31_pure : clause_remove_partial_solve_wit_31_pure.
Proof.
  aggressive_pre_process;
  dump_pre_spatial; apply clause_hdr_word_nonneg; apply Zlength_nonneg.
Qed.

Lemma proof_of_clause_remove_partial_solve_wit_32_pure : clause_remove_partial_solve_wit_32_pure.
Proof.
  aggressive_pre_process;
  dump_pre_spatial; apply clause_hdr_word_nonneg; apply Zlength_nonneg.
Qed.

(* ===== clause_remove which_implies wits (3 proofs) ===== *)
Lemma proof_of_clause_remove_which_implies_wit_1 : clause_remove_which_implies_wit_1.
Proof.
  unfold clause_remove_which_implies_wit_1, clause_remove_open_at.
  Unfold.
  right. intros.
  unfold clause_remove_pre. Intros_p Hpre.
  unfold MiniSatClause.rep. Intros_p Hclause.

  entailer_with ltac:(int_auto).
  destruct Hclause as [_ [Hpos Hmod]].
  rewrite Z.rem_mod_nonneg by lia. exact Hmod.
Qed.

Lemma proof_of_clause_remove_which_implies_wit_2 : clause_remove_which_implies_wit_2.
Proof.
  msat_clause_remove_focus_wlists_p4.
Qed.

Lemma proof_of_clause_remove_which_implies_wit_3 : clause_remove_which_implies_wit_3.
Proof.
  msat_clause_remove_focus_wlists_p4.
Qed.

(* ===== solver_analyze entail wits (11 proofs) ===== *)
Lemma proof_of_solver_analyze_entail_wit_31 : solver_analyze_entail_wit_31.
Proof.
  Unfold.
  intros.
  subst retval.
  bind_fact ( analysis_tags_exact anz_n (ms_tags Mstats) (ms_tagged Mstats) ) as H_analysis_tags_exact.
  assert (Htag_size :
    &(s_pre # "solver_t" ->ₛ "tagged" .ₛ "size") =
      veci_size_addr (&(s_pre # "solver_t" ->ₛ "tagged"))) by
    (unfold veci_size_addr; csimpl; reflexivity).
  assert (Htag_cap :
    &(s_pre # "solver_t" ->ₛ "tagged" .ₛ "cap") =
      veci_cap_addr (&(s_pre # "solver_t" ->ₛ "tagged"))) by
    (unfold veci_cap_addr; csimpl; reflexivity).
  assert (Htag_ptr :
    &(s_pre # "solver_t" ->ₛ "tagged" .ₛ "ptr") =
      veci_ptr_addr (&(s_pre # "solver_t" ->ₛ "tagged"))) by
    (unfold veci_ptr_addr; csimpl; reflexivity).
  sep_apply_l_atomic (store_int_undef_store_int (&( "j")) j).
  sep_apply_l_atomic (store_uint_undef_store_uint (&( "minl")) minl_v).
  destruct (Z.eq_dec (Zlength (ms_tagged Mstats)) 0) as [Hzero | Hnonzero].
  - Right. Exists (ms_tags Mstats).
    unfold veci_rep_at.
    rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr.
    entailer_with ltac:(lia).
    apply analyze_clear_start__analyze. exact H_analysis_tags_exact.
  - assert (Hpositive : 0 < Zlength (ms_tagged Mstats)) by lia.
    pose proof (analysis_tags_exact_index_range__analyze
      anz_n (ms_tags Mstats) (ms_tagged Mstats) 0 H_analysis_tags_exact ltac:(lia)) as Hhead.
    Left. Exists (ms_tags Mstats).
    unfold veci_rep_at.
    rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr.
    entailer_with ltac:(lia).
    apply analyze_clear_start__analyze. exact H_analysis_tags_exact.
Qed.

Lemma proof_of_solver_analyze_entail_wit_32 : solver_analyze_entail_wit_32.
Proof.
  Unfold.
  intros.
    bind_fact ( analyze_clear_loop_inv anz_n i (ms_tagged Mstats) (ms_tags Mstats) tags_now_2 ) as
      H_analyze_clear_loop_inv.
  replace (i - 0) with i in * by lia.
  assert (Hstep : analyze_clear_loop_inv anz_n (i + 1)
    (ms_tagged Mstats) (ms_tags Mstats)
    (replace_Znth (Znth i (ms_tagged Mstats) 0) 0 tags_now_2)).
  { eapply analyze_clear_step__analyze; eauto. }
  assert (Htag_size :
    &(s_pre # "solver_t" ->ₛ "tagged" .ₛ "size") =
      veci_size_addr (&(s_pre # "solver_t" ->ₛ "tagged"))) by
    (unfold veci_size_addr; csimpl; reflexivity).
  assert (Htag_cap :
    &(s_pre # "solver_t" ->ₛ "tagged" .ₛ "cap") =
      veci_cap_addr (&(s_pre # "solver_t" ->ₛ "tagged"))) by
    (unfold veci_cap_addr; csimpl; reflexivity).
  assert (Htag_ptr :
    &(s_pre # "solver_t" ->ₛ "tagged" .ₛ "ptr") =
      veci_ptr_addr (&(s_pre # "solver_t" ->ₛ "tagged"))) by
    (unfold veci_ptr_addr; csimpl; reflexivity).
  destruct (Z.eq_dec (i + 1) (Zlength (ms_tagged Mstats))) as [Heq | Hneq].
  - Right. Exists (replace_Znth (Znth i (ms_tagged Mstats) 0) 0 tags_now_2).
    sep_apply_l_atomic (CharArray.missing_i_merge_to_seg
      tags 0 (Znth i (ms_tagged Mstats) 0) anz_n 0 tags_now_2).
    entailer_with ltac:(lia).
    rewrite Z.sub_0_r.
    unfold veci_rep_at.
    rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr.
    entailer_with ltac:(lia).
  - assert (Hlt : i + 1 < Zlength (ms_tagged Mstats)) by lia.
    pose proof (analysis_tags_exact_index_range__analyze
      anz_n (ms_tags Mstats) (ms_tagged Mstats) (i + 1)
      ltac:(unfold analyze_clear_loop_inv in H_analyze_clear_loop_inv; tauto) ltac:(lia)) as Hnext.
    Left. Exists (replace_Znth (Znth i (ms_tagged Mstats) 0) 0 tags_now_2).
    sep_apply_l_atomic (CharArray.missing_i_merge_to_seg
      tags 0 (Znth i (ms_tagged Mstats) 0) anz_n 0 tags_now_2).
    entailer_with ltac:(lia).
    rewrite Z.sub_0_r.
    unfold veci_rep_at.
    rewrite <- Htag_size, <- Htag_cap, <- Htag_ptr.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_33 : solver_analyze_entail_wit_33.
Proof.
  Unfold.
  right; intros.
  entailer_with ltac:(lia).
  eapply analyze_clear_done__analyze; eauto.
Qed.

Lemma proof_of_solver_analyze_entail_wit_34 : solver_analyze_entail_wit_34.
Proof.
  Unfold.
  left; intros.
  bind_fact ( retval = lit_var_c (Znth (1 - 0) words_compact 0) ) as H_retval.
  unfold analyze_max_loop_inv in *.
  unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  entailer_with ltac:(lia).
  - apply store_ptr_undef_store_ptr.
  - rewrite H_retval. change (1 - 0) with 1.
    replace (lit_var_c (Znth 1 words_compact 0) - 0)
      with (lit_var_c (Znth 1 words_compact 0)) by lia.
    reflexivity.
  - intros k Hk. assert (k = 1) by lia. subst k.
    rewrite H_retval. change (1 - 0) with 1.
    replace (lit_var_c (Znth 1 words_compact 0) - 0)
      with (lit_var_c (Znth 1 words_compact 0)) by lia.
    lia.
Qed.

Lemma proof_of_solver_analyze_entail_wit_35_1 : solver_analyze_entail_wit_35_1.
Proof.
  Unfold.
  left; intros.
  bind_fact ( retval = lit_var_c (Znth (i - 0) words_compact 0) ) as H_retval.
  bind_fact ( Znth (retval_3 - 0) (mt_levels (ms_core Mclear)) 0 > max ) as H_Znth.
  bind_fact ( retval_3 = lit_var_c (Znth (i - 0) words_compact 0) ) as H_retval_3.
  bind_fact ( analyze_max_loop_inv anz_n Mclear words_compact i max_i max ) as H_analyze_max_loop_inv.
  unfold analyze_max_loop_inv in *.
  destruct H_analyze_max_loop_inv as [Hi [Hmi [Hwf [Hmaxeq Hmaxbound]]]].
  replace (i - 0) with i in H_retval, H_retval_3 by lia.
  rewrite H_retval_3 in H_Znth.
  replace (lit_var_c (Znth i words_compact 0) - 0)
    with (lit_var_c (Znth i words_compact 0)) in H_Znth by lia.
  unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  entailer_with ltac:(lia).
  - rewrite H_retval.
    replace (lit_var_c (Znth i words_compact 0) - 0)
      with (lit_var_c (Znth i words_compact 0)) by lia.
    reflexivity.
  - intros k Hk.
    destruct (Z.lt_ge_cases k i) as [Hlt | Hge].
    + pose proof (Hmaxbound k ltac:(lia)) as Hb.
      rewrite H_retval.
      replace (lit_var_c (Znth i words_compact 0) - 0)
        with (lit_var_c (Znth i words_compact 0)) by lia.
      lia.
    + assert (k = i) by lia. subst k.
      rewrite H_retval.
      replace (lit_var_c (Znth i words_compact 0) - 0)
        with (lit_var_c (Znth i words_compact 0)) by lia.
      lia.
Qed.

Lemma proof_of_solver_analyze_entail_wit_35_2 : solver_analyze_entail_wit_35_2.
Proof.
  Unfold.
  left; intros.
  bind_fact ( Znth (retval_2 - 0) (mt_levels (ms_core Mclear)) 0 <= max ) as H_Znth.
  bind_fact ( retval_2 = lit_var_c (Znth (i - 0) words_compact 0) ) as H_retval_2.
  bind_fact ( analyze_max_loop_inv anz_n Mclear words_compact i max_i max ) as H_analyze_max_loop_inv.
  unfold analyze_max_loop_inv in *.
  destruct H_analyze_max_loop_inv as [Hi [Hmi [Hwf [Hmaxeq Hmaxbound]]]].
  replace (i - 0) with i in H_retval_2 by lia.
  rewrite H_retval_2 in H_Znth.
  replace (lit_var_c (Znth i words_compact 0) - 0)
    with (lit_var_c (Znth i words_compact 0)) in H_Znth by lia.
  unfold veci_rep_at, veci_size_addr, veci_cap_addr, veci_ptr_addr.
  entailer_with ltac:(lia).
  intros k Hk.
  destruct (Z.lt_ge_cases k i) as [Hlt | Hge].
  - apply Hmaxbound. lia.
  - assert (k = i) by lia. subst k. exact H_Znth.
Qed.

Lemma proof_of_solver_analyze_entail_wit_36 : solver_analyze_entail_wit_36.
Proof.
  Unfold.
  left; intros.
  replace (1 - 0) with 1 by lia.
  replace (max_i - 0) with max_i by lia.
  Exists (Zlength words_compact)
    (replace_Znth max_i (Znth 1 words_compact 0)
      (replace_Znth 1 (Znth max_i words_compact 0) words_compact))
    cap_done.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_37_1 : solver_analyze_entail_wit_37_1.
Proof.
  Unfold.
  right; intros.
  bind_fact ( analyze_max_loop_inv anz_n Mclear words_compact i max_i max ) as H_analyze_max_loop_inv.
  bind_fact ( Forall (lit_wf_c anz_n) words_compact ) as H_Forall.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mclear anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_clause_cert anz_n anz_F Mclear words_compact ) as H_analyze_clause_cert.
  assert (Hi : i = Zlength words_compact) by lia.
  assert (Hj : 1 <= max_i < Zlength words_compact) by lia.
  subst words_sw.
  set (sw := replace_Znth max_i (Znth 1 words_compact 0)
    (replace_Znth 1 (Znth max_i words_compact 0) words_compact)).
  assert (Hperm : Permutation sw words_compact).
  { subst sw. apply swap_Znth_one_perm. exact Hj. }
  assert (Hlen : Zlength sw = Zlength words_compact).
  { apply Zlength_perm_eq. exact Hperm. }
  assert (Hwf : Forall (lit_wf_c anz_n) sw).
  { eapply Permutation_Forall; [|exact H_Forall].
    apply Permutation_sym. exact Hperm. }
  assert (Hhead : Znth 0 sw 0 = Znth 0 words_compact 0).
  { subst sw. apply swap_Znth_one_head__analyze. exact Hj. }
  assert (Hcert : analyze_clause_cert anz_n anz_F Mclear sw).
  { eapply analyze_clause_cert_perm_head__analyze;
      eauto; unfold analyze_max_loop_inv in H_analyze_max_loop_inv; lia. }
  assert (Hnodup : NoDup (map lit_var_c sw)).
  { pose proof Hcert as Hcert_copy.
    unfold analyze_clause_cert, uip_exit_cert in Hcert_copy.
    destruct Hcert_copy as [[_ [Hnd _]] _].
    rewrite map_literal_var_lits_denote in Hnd. exact Hnd. }
  assert (Hwftrail : mtrail_wf anz_n (ms_core Mclear)).
  { eapply analysis_cancel_ready_trail_wf__analyze; eauto. }
  assert (Hlenle : Zlength sw <= anz_n).
  { pose proof (msat_map_lit_var_c_in_range anz_n sw Hwf) as Hall.
    pose proof (NoDup_Z_bounded_length _ anz_n (mtw_n_nonneg Hwftrail)
      Hnodup Hall) as Hle.
    rewrite length_map in Hle. rewrite Zlength_correct. exact Hle. }
  assert (Hback : analyze_backjump_cert anz_n Mclear sw
    (Z.max (ms_root_level Mclear) max)).
  { subst sw. exact (analyze_backjump_swap_complete__analyze
      anz_n anz_F anz_A_arr K Mclear anz_focus words_compact i max_i max
      Hi H_analysis_cancel_ready H_analyze_max_loop_inv H_analyze_clause_cert). }
  Exists (Z.max (ms_root_level Mclear) max).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_37_2 : solver_analyze_entail_wit_37_2.
Proof.
  Unfold.
  right; intros.
  bind_fact ( analyze_clause_cert anz_n anz_F Mclear words_compact ) as H_analyze_clause_cert.
  assert (Hlen : Zlength words_compact = 1) by lia.
  pose proof (analyze_backjump_singleton__analyze
    anz_n anz_F Mclear words_compact Hlen H_analyze_clause_cert) as [Hnodup Hback].
  Exists (ms_root_level Mclear).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_entail_wit_38_1 : solver_analyze_entail_wit_38_1.
Proof.
  msat_analyze_core_equiv_close_p4 M0 Mfinal words_final cap_final blevel lits.
Qed.

Lemma proof_of_solver_analyze_entail_wit_38_2 : solver_analyze_entail_wit_38_2.
Proof.
  msat_analyze_core_equiv_close_p4 M0 Mfinal words_final cap_final blevel lits.
Qed.

(* ===== solver_analyze partial_solve wits (13 proofs) ===== *)
Lemma proof_of_solver_analyze_partial_solve_wit_4_pure : solver_analyze_partial_solve_wit_4_pure.
Proof.
  Unfold.
  left; intros.
  sep_apply_l_atomic
    (veci_rep_bounds__analyze learnt_pre z_nil anz_learnt_cap).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_82_learnt_pure : solver_analyze_partial_solve_wit_82_learnt_pure.
Proof.
  aggressive_pre_process.
  all: bind_fact ( Forall (lit_wf_c anz_n) clause_words2 ) as H_Forall.
  (* The pure conjunct is emitted twice, and the index reaches the goal already substituted
     (`Znth (1 - 0) ...`) while the Forall elimination still speaks of `j`; `subst j` puts
     the two spellings back on the same atom. *)
  all: (dump_pre_spatial);
    (assert (Hr : 0 <= j - 0 < Zlength clause_words2) by lia);
    (pose proof (sat_shared_lib.Forall_Znth_elim Z (solver_qcp_model.lit_wf_c anz_n)
    clause_words2 0 (j - 0) H_Forall Hr) as Hlit);
    (unfold solver_qcp_model.lit_wf_c in Hlit);
    (try subst j);
    (lia).
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_83_learnt_pure : solver_analyze_partial_solve_wit_83_learnt_pure.
Proof.
  msat_analyze_clause_word_int_range_via_wf_p4 Hwf j clause_words2 Hlit.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_88_learnt_pure : solver_analyze_partial_solve_wit_88_learnt_pure.
Proof.
  msat_analyze_learnt_offset_congruence_p4.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_89_learnt_pure : solver_analyze_partial_solve_wit_89_learnt_pure.
Proof.
  msat_analyze_learnt_offset_congruence_p4.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_90_learnt_pure : solver_analyze_partial_solve_wit_90_learnt_pure.
Proof.
  msat_analyze_learnt_offset_congruence_p4.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_91_learnt_pure : solver_analyze_partial_solve_wit_91_learnt_pure.
Proof.
  msat_analyze_learnt_offset_congruence_p4.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_92_learnt_pure : solver_analyze_partial_solve_wit_92_learnt_pure.
Proof.
  msat_analyze_clause_word_int_range_via_wf_p4 Hwf j clause_words2 Hlit.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_93_learnt_pure : solver_analyze_partial_solve_wit_93_learnt_pure.
Proof.
  msat_analyze_clause_word_int_range_via_wf_p4 Hwf j clause_words2 Hlit.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_94_learnt_pure : solver_analyze_partial_solve_wit_94_learnt_pure.
Proof.
  msat_analyze_clause_word_int_range_via_wf_p4 Hwf j clause_words2 Hlit.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_95_learnt_pure : solver_analyze_partial_solve_wit_95_learnt_pure.
Proof.
  msat_analyze_clause_word_int_range_via_wf_p4 Hwf j clause_words2 Hlit.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_100_learnt_pure : solver_analyze_partial_solve_wit_100_learnt_pure.
Proof.
  msat_analyze_clause_word_int_range_via_wf_p4 Hwf j clause_words2 Hlit.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_101_learnt_pure : solver_analyze_partial_solve_wit_101_learnt_pure.
Proof.
  (* release-fix 5.4b: extract the capacity bound ONCE, before the pure RHS
     is split.  The shipped text split first and re-walked the ~50-atom
     context per conjunct, and paid aggressive_pre_process's trailing
     `try solve [cancel]' on a goal no cancel can close. *)
  Unfold.
  right.
  intros.
  prop_apply_p (veci_rep_bounds__canceluntil_cap
    (&( s_pre # "solver_t" ->ₛ "tagged"))
    (solver_qcp_model.ms_tagged Mscan)
    (solver_qcp_model.ms_tagged_cap Mscan)).
  Intros_p Hcap.
  split_pures;
  dump_pre_spatial;
  destruct Hcap as [[Hlen_nonneg Hlen_cap] [Hcap_pos Hcap_max]]; lia.
Qed.

(* ===== solver_analyze safety wits (5 proofs) ===== *)
Lemma proof_of_solver_analyze_safety_wit_4 : solver_analyze_safety_wit_4.
Proof.
  pre_process_default.
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K M0 anz_focus ) as H_analysis_cancel_ready.
  destruct H_analysis_cancel_ready as [Mentry [Hcancel [Hequiv Hrest]]].
  destruct Hcancel as [[Hpending Hweak] Hcancel_rest].
  destruct K; cbn in Hweak.
  - pose proof (msw_shape Hweak) as Hshape.
    unfold solver_shape in Hshape.
    unfold analysis_core_equiv in Hequiv.
    assert (Hbounds :
      ms_qtail M0 - 1 <= INT_MAX /\ INT_MIN <= ms_qtail M0 - 1) by lia.
    entailer_with ltac:(lia).
  - pose proof (msa_shape Hweak) as Hshape.
    unfold solver_shape in Hshape.
    unfold analysis_core_equiv in Hequiv.
    assert (Hbounds :
      ms_qtail M0 - 1 <= INT_MAX /\ INT_MIN <= ms_qtail M0 - 1) by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_safety_wit_25 : solver_analyze_safety_wit_25.
Proof.
  pre_process_default.
  bind_fact ( Permutation (ms_tagged Mcur_2) (analyze_tags S0 R0 learnt0) ) as H_Permutation.
  pose proof (Zlength_perm_eq Z _ _ H_Permutation) as Hlen.
  unfold analyze_tags in Hlen.
  rewrite !Zlength_app in Hlen.
  pose proof (Zlength_nonneg R0).
  pose proof (Zlength_nonneg (map literal_var learnt0)).
  assert (Hbounds : cnt + 1 <= INT_MAX /\ INT_MIN <= cnt + 1) by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_safety_wit_70_learnt : solver_analyze_safety_wit_70_learnt.
Proof.
  msat_analyze_scan_count_bound_p4.
Qed.

Lemma proof_of_solver_analyze_safety_wit_71_learnt : solver_analyze_safety_wit_71_learnt.
Proof.
  msat_analyze_scan_count_bound_p4.
Qed.

Lemma proof_of_solver_analyze_safety_wit_72_learnt : solver_analyze_safety_wit_72_learnt.
Proof.
  msat_analyze_scan_count_bound_p4.
Qed.

(* ===== solver_analyze which_implies wits (13 proofs) ===== *)
Lemma proof_of_solver_analyze_which_implies_wit_16 : solver_analyze_which_implies_wit_16.
Proof.
  LLM_pre_process ltac:(lia).
    bind_fact ( analyze_clause_scan_inv anz_n anz_F anz_A_arr K Mact Mscan anz_focus phase Ccur j ind S0 R0 learnt0 x
      Sscan Rscan learnt_scan words_scan cnt ) as H_analyze_clause_scan_inv.
  bind_fact ( 0 <= lit_var_c q ) as H_lit_var_c.
  bind_fact ( lit_var_c q < anz_n ) as H_lit_var_c_2.
  pose proof H_analyze_clause_scan_inv as Hinv.
  unfold analyze_clause_scan_inv in H_analyze_clause_scan_inv.
  destruct H_analyze_clause_scan_inv as [Hready Hrest].
  destruct Hrest as (Hcore & Hind & Hroot & Hwf & Hj & Hjbound & Hcnt & Hwords_bound &
      Hlearnt & Htags & Hperm & Hphase).
  unfold analysis_tags_exact in Htags.
  destruct Htags as [Htags_len [Hnodup [Hrange [Hbits Hexact]]]].
  assert (Hnotin : ~ In (lit_var_c q) (ms_tagged Mscan)).
  { intro Hin.
    pose proof (proj2 (Hexact (lit_var_c q) (conj H_lit_var_c H_lit_var_c_2)) Hin) as Hone.
    lia. }
  assert (Hcons_nodup : NoDup (lit_var_c q :: ms_tagged Mscan)).
  { constructor; assumption. }
  pose proof (msat_cons_list_var_bounded anz_n (lit_var_c q) (ms_tagged Mscan)
    (conj H_lit_var_c H_lit_var_c_2) Hrange) as Hbounded.
  assert (Htagged : Zlength (ms_tagged Mscan) < anz_n).
  { pose proof (NoDup_Z_bounded_length
      (lit_var_c q :: ms_tagged Mscan) anz_n ltac:(lia) Hcons_nodup Hbounded)
      as Hlen.
    rewrite Zlength_correct. simpl in Hlen. lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_17 : solver_analyze_which_implies_wit_17.
Proof.
  unfold solver_analyze_which_implies_wit_17, solver_analyze_open_at.  Unfold.
  right.
  intros.
    bind_fact ( analyze_backward_scan_inv anz_n anz_F anz_A_arr K Mdone anz_focus words_done cnt ind Sdone Rdone
      learnt_done ) as H_analyze_backward_scan_inv.
  bind_fact ( clause_lits_pointer c lits ) as H_clause_lits_pointer.
  pose proof H_analyze_backward_scan_inv as Hscan.
  unfold analyze_backward_scan_inv in Hscan.
  destruct Hscan as
    [Hready [Hainv [Hcnt [Hcntpos [Hind [Hwords [Hroot [Hlits_done
    [Htags [Hperm [HSrank [HRrank Hex]]]]]]]]]]]].
  assert (Hstats_keep :
    solver_analyze_frame s Mdone anz_wl |--
      “ Zlength (ms_stats Mdone) = 11 ” &&
      solver_analyze_frame s Mdone anz_wl).
  {
    unfold solver_analyze_frame, solver_analyze_frame_cells, stats_analyze_frame.
    Intros asg. Exists asg. entailer_with ltac:(lia).
  }
  sep_apply Hstats_keep.
  Intros_p Hstats.
  prop_apply (DoubleArray.seg_Zlength activity_ptr_done 0 anz_n
    (ms_activity Mdone)).
  Intros_p Hactivity_raw.
  assert (Hactivity : Zlength (ms_activity Mdone) = anz_n) by lia.
  destruct (analyze_backward_scan_shape_db_p4 _ _ _ _ _ _ _ _ _ _ _ _
    H_analyze_backward_scan_inv Hstats Hactivity) as [Hshape Hdb].
  pose proof (proj1 (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mdone anz_focus Hready)) as Hsize.
  unfold solver_analyze_frame at 1.
  cbv [solver_analyze_frame_cells].
  Intros asg.
  assert (Hbinary_nonneg_keep :
    (&(s # "solver_t" ->ₛ "binary")) # Ptr |-> ms_binary Mdone |--
      “ 0 <= ms_binary Mdone ” &&
      (&(s # "solver_t" ->ₛ "binary")) # Ptr |-> ms_binary Mdone).
  (* `store_ptr` carries the arch address bound `addr_max_unsigned`, which micromega cannot
     delta-reduce, so the [lia] supplied to [entailer_with] cannot reach the range
     side-condition until `unfold_arch` has exposed it. *)
  { unfold store_ptr, valid_ptr_value. unfold_arch. entailer_with ltac:(lia). }
  sep_apply Hbinary_nonneg_keep.
  Intros_p Hbinary_nonneg.
  pose proof (analysis_focus_clause_db_close_p4 anz_n Mdone c is_learnt2
    clause_words2 lits Hdb Hshape Hbinary_nonneg H_clause_lits_pointer)
    as Hfocus_close.
  pose proof (analyze_stats_frame_close_p4 s Mdone) as Hstats_close.
  (* The left-hand side carries the six undef tails, the [stack] vector and
     the two literal counters inside [solver_analyze_inert_at].  The peel below
     names [max_literals] and [tot_literals] as atoms, so the bundle is opened
     here -- after every [sep_apply] / [prop_apply] above, which see it as one
     more opaque atom exactly as they see [solver_analyze_frame]. *)
  unfold solver_analyze_inert_at.
  set (AH := clause_hdr_addr c # Int |->
    clause_hdr_word is_learnt2 (Zlength clause_words2)).
  set (AA := activity_state c is_learnt2).
  set (AS := IntArray.seg lits 0 (Zlength clause_words2) clause_words2).
  set (AR := analysis_clause_remainder Mdone c is_learnt2 clause_words2).
  set (ST := stats_analyze_frame &(s # "solver_t" ->ₛ "stats") (ms_stats Mdone)).
  set (SM := &(s # "solver_t" ->ₛ "stats" .ₛ "max_literals")
    # UInt64 |-> stats_max_literals (ms_stats Mdone)).
  set (SO := &(s # "solver_t" ->ₛ "stats" .ₛ "tot_literals")
    # UInt64 |-> stats_tot_literals (ms_stats Mdone)).
  lazymatch goal with
  | |- ?P |-- _ =>
      let R1 := msat_sep_replace_atom_with_emp_p4 AH P in
      let R2 := msat_sep_replace_atom_with_emp_p4 AA R1 in
      let R3 := msat_sep_replace_atom_with_emp_p4 AS R2 in
      let R4 := msat_sep_replace_atom_with_emp_p4 AR R3 in
      let R5 := msat_sep_replace_atom_with_emp_p4 ST R4 in
      let R6 := msat_sep_replace_atom_with_emp_p4 SM R5 in
      let R7 := msat_sep_replace_atom_with_emp_p4 SO R6 in
      pose (analyze_close_rest := R7);
      transitivity
        (((((AH ** AA) ** AS) ** AR) ** ((ST ** SM) ** SO)) ** R7)
  end.
  - apply (proj2 (__derivable1_provable _ _)).
    msat_theory_cancel.
    apply (proj1 (__derivable1_provable _ _)).
    (* Cancellation leaves the inserted [emp] residuals on the right. *)
    do 5 (transitivity (emp ** emp);
      [ apply derivable1_sepcon_emp_r | f_equiv ]).
  - transitivity
      (((clause_db_rep (ms_prob Mdone) **
          clause_db_rep (ms_learnt Mdone) **
          MiniSatClause.rep (ms_binary Mdone) false
            (ms_binary_lits Mdone)) **
         stats_rep &(s # "solver_t" ->ₛ "stats")
           (ms_stats Mdone)) ** analyze_close_rest).
    + apply derivable1s_sepcon_proper.
      * apply derivable1s_sepcon_proper.
        -- exact Hfocus_close.
        -- exact Hstats_close.
      * reflexivity.
    + apply _derivable1_andp_intros.
      * apply derivable1s_coq_prop_r. lia.
      * apply _derivable1_andp_intros.
        -- apply derivable1s_coq_prop_r. lia.
        -- unfold solver_rep_analyze_at, solver_rep_at.
        Exists activity_ptr_done asg orderpos_ptr_done.
        unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
          solver_scalars_rep, solver_fp_rep, solver_vecs_rep,
          solver_trail_array_rep.
        lazymatch goal with
        | |- _ |-- (?ShapePart && ?Spatial) ** ?Extra =>
            transitivity (Spatial ** Extra)
        end.
        ++ unfold analyze_close_rest.
           rewrite Hsize.
           unfold db_words.
           apply (proj2 (__derivable1_provable _ _)).
           msat_theory_cancel.
           apply (proj1 (__derivable1_provable _ _)).
           msat_collapse_emp_sepcon_tree_p4 (8%nat).
        ++ apply derivable1s_sepcon_proper;
           [ apply _derivable1_andp_intros;
             [ apply derivable1s_coq_prop_r; exact Hshape
             | reflexivity ]
           | reflexivity ].
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_18 : solver_analyze_which_implies_wit_18.
Proof.
  left; intros.
  lazymatch goal with
  | Hsize : ms_size ?Msol = ?n |-
      solver_rep_analyze_at ?s ?Msol ?reasons ?levels ?trail ?tags ?wl |-- _ =>
      sep_apply (solver_rep_analyze_at_open
        s Msol n reasons levels trail tags wl Hsize)
  end.
  Intros activity orderpos.
  Exists activity orderpos.
  unfold msat_false.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_22 : solver_analyze_which_implies_wit_22.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mcur anz_focus ) as H_analysis_cancel_ready.
    bind_fact ( level_of (msolver_view anz_n Mcur) (lit_var_c q) = Some (current_level (msolver_view anz_n Mcur)) ) as
      H_level_of.
  pose proof H_analysis_cancel_ready as H_analysis_cancel_ready_folded.
  pose proof H_level_of as H_level_of_folded.
  destruct H_analysis_cancel_ready as [M0 [Hready [Hequiv Hrest]]].
  destruct Hready as [[Hpending Hweak] Hready].
  assert (Hwf0 : mtrail_wf anz_n (ms_core M0)).
  { destruct K as [A_inst | A_proc]; cbn in Hweak.
    - exact (msw_trail_wf Hweak).
    - exact (msa_trail_wf Hweak). }
  destruct Hequiv as [_ [_ [_ [Hcore _]]]].
  assert (Hwf : mtrail_wf anz_n (ms_core Mcur)).
  { rewrite Hcore. exact Hwf0. }
  unfold msolver_view, view_of in H_level_of.
  cbn in H_level_of.
  destruct (trail_pos (ms_core Mcur) (lit_var_c q)) as [k|] eqn:Hpos;
    cbn in H_level_of; [|discriminate].
  inversion H_level_of as [Hlevel].
  assert (Hresult :
    Znth (lit_var_c q) (mt_levels (ms_core Mcur)) 0 =
      Zlength (mt_lim (ms_core Mcur))).
  { rewrite <- (trail_pos_var (ms_core Mcur) (lit_var_c q) k Hpos).
    rewrite (mtw_levels_agree Hwf (Z.of_nat k)).
    - exact Hlevel.
    - split; [lia|]. eapply trail_pos_bound. exact Hpos. }
  entailer_with ltac:(lia).
  - replace (lit_var_c q - 0) with (lit_var_c q) by lia.
    lia.
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_9 : solver_analyze_which_implies_wit_9.
Proof. exact proof_of_solver_analyze_which_implies_wit_22. Qed.

Lemma proof_of_solver_analyze_which_implies_wit_24 : solver_analyze_which_implies_wit_24.
Proof.
  LLM_pre_process ltac:(lia).
    bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p ) as
      H_analyze_resolution_loop_inv.
  pose proof H_analyze_resolution_loop_inv as Hinv.
  destruct Hinv as [_ [_ [_ [_ [Htags Hphase]]]]].
  destruct Htags as [Htagslen [Hnodup [Hrange [Hcells Hiff]]]].
  assert (Hv : 0 <= lit_var_c q < anz_n) by lia.
  assert (Hnotin : ~ In (lit_var_c q) (ms_tagged Mcur)).
  { intro Hin.
    pose proof (proj2 (Hiff (lit_var_c q) Hv) Hin) as Htag.
    lia. }
  assert (Hnodup' : NoDup (lit_var_c q :: ms_tagged Mcur)).
  { constructor; assumption. }
  pose proof (msat_cons_list_var_bounded anz_n (lit_var_c q) (ms_tagged Mcur)
    Hv Hrange) as Hrange'.
  pose proof (NoDup_Z_bounded_length
    (lit_var_c q :: ms_tagged Mcur) anz_n ltac:(lia) Hnodup' Hrange') as Hlen.
  assert (Hlt : Zlength (ms_tagged Mcur) < anz_n).
  { rewrite Zlength_correct. cbn in Hlen. lia. }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_7 : solver_analyze_which_implies_wit_7.
Proof. exact proof_of_solver_analyze_which_implies_wit_24. Qed.

Lemma proof_of_solver_analyze_which_implies_wit_25 : solver_analyze_which_implies_wit_25.
Proof.
  LLM_pre_process ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_6 : solver_analyze_which_implies_wit_6.
Proof. exact proof_of_solver_analyze_which_implies_wit_25. Qed.

Lemma proof_of_solver_analyze_which_implies_wit_26 : solver_analyze_which_implies_wit_26.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analysis_cancel_ready anz_n anz_F anz_A_arr K Mcur anz_focus ) as H_analysis_cancel_ready.
  bind_fact ( reason_target_wf anz_n Mcur x c Ccur ) as H_reason_target_wf.
  bind_fact ( level_of (msolver_view anz_n Mcur) x = Some (current_level (msolver_view anz_n Mcur)) ) as H_level_of.
  bind_fact ( is_tag c = msat_true ) as H_is_tag.
  bind_fact ( q = tag_lit c ) as H_q.
  pose proof H_analysis_cancel_ready as H_analysis_cancel_ready_folded.
  pose proof H_reason_target_wf as H_reason_target_wf_folded.
  pose proof H_level_of as H_level_of_folded.
  pose proof H_is_tag as H_is_tag_folded.
  pose proof H_q as H_q_folded.
  unfold msat_true in H_is_tag.
  subst q.
  destruct H_reason_target_wf as
    [Hxrange [Hword [Hnonzero [Hreason Htarget]]]].
  destruct Htarget as
    [[Htag [Hpositive Hqwf]] |
     [co [Hnottag [Hnotbin [Hin HC]]]]].
  2: { rewrite H_is_tag in Hnottag. discriminate. }
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mcur anz_focus H_analysis_cancel_ready) as [Hsize [Hmatch Hbinary]].
  assert (Hxn : 0 <= x < anz_n) by lia.
  assert (Htagword :
    is_tag (Znth x (ms_reason_words Mcur) 0) = true).
  { rewrite <- Hword. exact Htag. }
  destruct (Hbinary x Hxrange Htagword) as
    [Hqwf' [Hsame Hneq]].
  rewrite <- Hword in Hsame, Hneq.
  assert (Hqrange : 0 <= lit_var_c (tag_lit c) < anz_n).
  { apply lit_var_c_in_range. exact Hqwf. }
  pose proof (Hmatch x Hxn) as Hok.
  rewrite <- Hword in Hok.
  pose proof (reason_word_ok_tag
    (ms_core Mcur) x (msolver_db Mcur) c (ms_reason_of Mcur x)
    Hpositive Htag Hok) as HCshape.
  rewrite Hreason in HCshape. inversion HCshape as [HCeq].
  subst Ccur.
  pose proof H_analysis_cancel_ready as Hreadycopy.
  destruct Hreadycopy as [M0 [Hcancel [Hequiv Hrest]]].
  destruct Hcancel as [[Hpending Hweak] Hcancelrest].
  assert (Hinvpair :
    mtrail_wf anz_n (ms_core M0) /\
    stable_view (msolver_view anz_n M0)).
  { destruct K as [A_inst | A_proc]; cbn in Hweak.
    - split; [exact (msw_trail_wf Hweak) | exact (msw_stable Hweak)].
    - split; [exact (msa_trail_wf Hweak) | exact (msa_stable Hweak)]. }
  destruct Hinvpair as [Hwf0 Hstable0].
  destruct Hequiv as
    [Esize [_ [_ [Ecore [_ [Ewords [Ereason [Eprob [Elearnt Erest]]]]]]]]].
  assert (Hwf : mtrail_wf anz_n (ms_core Mcur)).
  { rewrite Ecore. exact Hwf0. }
  assert (Hview : msolver_view anz_n Mcur = msolver_view anz_n M0).
  { unfold msolver_view, msolver_clauses, msolver_db.
    rewrite Ecore, Ereason, Eprob, Elearnt. reflexivity. }
  assert (Hstable : stable_view (msolver_view anz_n Mcur)).
  { rewrite Hview. exact Hstable0. }
  pose proof H_level_of_folded as Hlevelx.
  unfold msolver_view, view_of in Hlevelx.
  cbn in Hlevelx.
  destruct (trail_pos (ms_core Mcur) x) as [kx|] eqn:Hposx;
    cbn in Hlevelx; [|discriminate].
  inversion Hlevelx as [Hidxx].
  destruct (assignment (msolver_view anz_n Mcur) x) as [b|] eqn:Hassign.
  2: {
    change (mt_pv (ms_core Mcur) x = None) in Hassign.
    apply (proj1 (view_unassigned_iff anz_n (ms_core Mcur) x Hwf)) in Hassign.
    rewrite Hposx in Hassign. discriminate. }
  destruct Hstable as [Hground Hclosed].
  destruct (Hground x b Hassign) as
    [d [rx [Hld [Hrank Hreason_valid]]]].
  destruct Hreason_valid as
    [Hnone | [C' [Hreason' Hvalid]]].
  { unfold msolver_view, view_of in Hnone. cbn in Hnone.
    rewrite Hposx in Hnone. cbn in Hnone.
    rewrite Hreason in Hnone. discriminate. }
  unfold msolver_view, view_of in Hreason'. cbn in Hreason'.
  rewrite Hposx in Hreason'. cbn in Hreason'.
  rewrite Hreason in Hreason'. inversion Hreason'. subst C'.
  destruct Hvalid as
    [b' [d' [rx' [Hassign' [Hlevel' [Hrank' [Hhead Hothers]]]]]]].
  specialize (Hothers
    (literal_neg (lit_denote (tag_lit c)))
    ltac:(simpl; tauto) ltac:(rewrite literal_var_neg, lit_var_c_denote;
      exact Hneq)).
  destruct Hothers as [Heval [dq [rq [Hlevelq [Hrankq Horder]]]]].
  pose proof Hlevelq as Hlevelq_idx.
  rewrite literal_var_neg, lit_var_c_denote in Hlevelq_idx.
  unfold msolver_view, view_of in Hlevelq_idx.
  cbn in Hlevelq_idx.
  destruct (trail_pos (ms_core Mcur) (lit_var_c (tag_lit c)))
    as [kq|] eqn:Hposq; cbn in Hlevelq_idx; [|discriminate].
  inversion Hlevelq_idx as [Hidxq].
  assert (Hxarray :
    Znth x (mt_levels (ms_core Mcur)) 0 =
      Zlength (mt_lim (ms_core Mcur))).
  { rewrite <- (trail_pos_var (ms_core Mcur) x kx Hposx).
    rewrite (mtw_levels_agree Hwf (Z.of_nat kx)).
    - exact Hidxx.
    - split; [lia|]. eapply trail_pos_bound. exact Hposx. }
  assert (Hqarray :
    Znth (lit_var_c (tag_lit c)) (mt_levels (ms_core Mcur)) 0 = dq).
  { rewrite <- (trail_pos_var
      (ms_core Mcur) (lit_var_c (tag_lit c)) kq Hposq).
    rewrite (mtw_levels_agree Hwf (Z.of_nat kq)).
    - exact Hidxq.
    - split; [lia|]. eapply trail_pos_bound. exact Hposq. }
  assert (Hdq : dq = Zlength (mt_lim (ms_core Mcur))) by lia.
  rewrite Hdq in Hlevelq.
  rewrite literal_var_neg, lit_var_c_denote in Hlevelq.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_5 : solver_analyze_which_implies_wit_5.
Proof. exact proof_of_solver_analyze_which_implies_wit_26. Qed.

Lemma proof_of_solver_analyze_which_implies_wit_27 : solver_analyze_which_implies_wit_27.
Proof.
  LLM_pre_process ltac:(lia).
    bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p ) as
      H_analyze_resolution_loop_inv.
  bind_fact ( is_tag c = msat_true ) as H_is_tag.
  pose proof H_analyze_resolution_loop_inv as H_analyze_resolution_loop_inv_folded.
  unfold msat_true in H_is_tag.
  destruct H_analyze_resolution_loop_inv as
    [Hready [Hind [Hwords [Hroot [Htags Hphase]]]]].
  destruct phase.
  - cbn in Hphase.
    destruct Hphase as
      [Hp [Hcnt [Hqtail [Hcert [Hconflict [Htagged Hlearnt]]]]]].
    pose proof Hready as Hreadycopy.
    destruct Hreadycopy as [M0 [Hcancel [Hequiv Hrest]]].
    destruct Hcancel as [[Hpending Hweak] Hcancelrest].
    assert (Hshape_db :
      solver_shape M0 /\ db_wf anz_n (msolver_db M0)).
    { destruct K as [A_inst | A_proc]; cbn in Hweak.
      - split; [exact (msw_shape Hweak) | exact (msw_db_wf Hweak)].
      - split; [exact (msa_shape Hweak) | exact (msa_db_wf Hweak)]. }
    destruct Hshape_db as [Hshape0 Hdb0].
    destruct Hequiv as
      [Esize [_ [_ [Ecore [_ [Ewords [Ereason
        [Eprob [Elearnt [_ [_ [Ebinary Erest]]]]]]]]]]]].
    assert (Hbinary_not_tag : is_tag (ms_binary Mcur) = false).
    { rewrite Ebinary. apply solver_shape_binary_not_tag. exact Hshape0. }
    assert (Hdb : db_wf anz_n (msolver_db Mcur)).
    { unfold msolver_db in *. rewrite Eprob, Elearnt. exact Hdb0. }
    destruct Hconflict as
      [[Hc [HC Hout]] | [co [Hnotbin [Hin HC]]]].
    + subst c. rewrite Hbinary_not_tag in H_is_tag. discriminate.
    + pose proof (db_wf_even anz_n (msolver_db Mcur) c co Hdb Hin) as Heven.
      pose proof (even_not_tag c Heven) as Hnottag.
      rewrite H_is_tag in Hnottag. discriminate.
  - cbn in Hphase.
    destruct Hphase as [S [R [learnt [x Hphase]]]].
    destruct Hphase as (Hpnot & Hx & HxS & Htrail & Hrank & Hmax & Hlit & Hcnt &
        Hcntpos & Hc & Hreason & Htarget & Hfocus & Hvalid & Hent & HCwf & HCnodup &
        Hainv & Hlearnt & Hperm).
    pose proof Hainv as Hainv'.
    destruct Hainv' as [_ [_ [HS Hainvrest]]].
    rewrite Forall_forall in HS.
    pose proof (HS x HxS) as Hxlevel.
    Exists R learnt x S.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_4 : solver_analyze_which_implies_wit_4.
Proof. exact proof_of_solver_analyze_which_implies_wit_27. Qed.

(* ===== solver_lit_removable which_implies wits (6 proofs) ===== *)
Lemma proof_of_solver_lit_removable_which_implies_wit_14 : solver_lit_removable_which_implies_wit_14.
Proof.
  pre_process_default.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( removable_reason_focus lrm_n M0 v c Cnext ) as H_removable_reason_focus.
  bind_fact ( is_tag c = msat_false ) as H_is_tag.
  pose proof H_removable_reason_focus as Hfocus.
  unfold removable_reason_focus, reason_target_wf in H_removable_reason_focus.
  destruct H_removable_reason_focus as [Hv [Hp [Hnonzero [Hreason [Htagged | Hreal]]]]].
  - destruct Htagged as [Htag _]. unfold msat_false in H_is_tag. congruence.
  - destruct Hreal as [co [Htag [Hnotbinary [Hin HC]]]].
    destruct
      (analysis_cancel_ready_db_binary__lit_removable
        lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready) as [Hdb Hbinary_out].
    pose proof (db_wf_obj lrm_n (msolver_db M0) c co Hdb Hin) as Hobj.
    destruct Hobj as [Hobj_len [Hwords Hnodup]].
    pose proof
      (clause_hdr_word_div2 (co_learnt co) (Zlength (co_lits co))
        (Zlength_nonneg (co_lits co))) as Hhdr.
    pose proof
      (clause_hdr_word_nonneg (co_learnt co) (Zlength (co_lits co))
        (Zlength_nonneg (co_lits co))) as Hhdr_nonneg.
    assert (Hhdrq :
      clause_hdr_word (co_learnt co) (Zlength (co_lits co)) ÷ 2 =
      Zlength (co_lits co)).
    { rewrite Z.quot_div_nonneg by lia. exact Hhdr. }
    unfold denote_obj in HC.
    sep_apply
      (clause_db_pair_focus_from_member__lit_removable
        (ms_prob M0) (ms_learnt M0) c co Hin).
    unfold MiniSatClause.rep at 1.
    Exists (co_learnt co) (co_lits co).
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_15 : solver_lit_removable_which_implies_wit_15.
Proof.
  pre_process_default.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
    bind_fact ( removable_reason_scan_inv lrm_n M0 l_pre minl_pre (ms_tagged M0) done_scan stack_scan tags_scan
      tagged_scan Cnext v c i ) as H_removable_reason_scan_inv.
  destruct (analysis_cancel_ready_reason_core
    lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus H_analysis_cancel_ready) as [Hsize _].
  pose proof
    (removable_scan_stack_strict__lit_removable
      lrm_n M0 l_pre minl_pre (ms_tagged M0) done_scan stack_scan
      tags_scan tagged_scan Cnext v c i H_removable_reason_scan_inv Hsize) as Hstrict.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_16 : solver_lit_removable_which_implies_wit_16.
Proof.
  Unfold.
  right.
  intros n clause_words i.
  intros.
  bind_fact ( Forall (lit_wf_c n) clause_words ) as H_Forall.
  bind_fact ( 0 <= i ) as H_i.
  bind_fact ( i < Zlength clause_words ) as H_i_2.
  pose proof (Forall_Znth_elim Z (lit_wf_c n) clause_words 0 i
    H_Forall (conj H_i H_i_2)) as Hlit.
  pose proof (lit_var_c_in_range n (Znth i clause_words 0) Hlit) as Hrange.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_17 : solver_lit_removable_which_implies_wit_17.
Proof.
  pre_process_default.
  bind_fact ( analysis_cancel_ready lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus ) as H_analysis_cancel_ready.
  bind_fact ( analysis_tags_exact lrm_n tags_scan tagged_scan ) as H_analysis_tags_exact.
  bind_fact ( 0 <= v ) as H_v.
  bind_fact ( v < lrm_n ) as H_v_2.
  bind_fact ( Znth v tags_scan 0 = 0 ) as H_Znth.
  bind_fact ( Znth v (ms_reason_words M0) 0 <> 0 ) as H_Znth_2.
  destruct
    (analysis_cancel_ready_reason_target__lit_removable
      lrm_n lrm_F lrm_A_arr lrm_K M0 lrm_focus v H_analysis_cancel_ready (conj H_v H_v_2) H_Znth_2)
    as [Cpush Htarget].
  pose proof
    (analysis_tags_exact_untagged_strict__lit_removable
      lrm_n tags_scan tagged_scan v H_analysis_tags_exact (conj H_v H_v_2) H_Znth)
    as Hstrict.
  Exists Cpush.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_19 : solver_lit_removable_which_implies_wit_19.
Proof.
  Unfold.
  right.
  intros.
  subst lits_refold.
  bind_fact ( c_refold % 2 = 0 ) as H_c_refold.
  unfold MiniSatClause.rep.
  pose proof (Zlength_nonneg clause_words).
  assert (Hmod : c_refold mod 2 = 0).
  { apply Z.mod_divide; [lia |].
    apply Z.rem_divide; [lia | exact H_c_refold]. }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_lit_removable_which_implies_wit_20 : solver_lit_removable_which_implies_wit_20.
Proof.
  Unfold.
  right.
  intros.
  subst lits.
  bind_fact ( c % 2 = 0 ) as H_c.
  unfold MiniSatClause.rep.
  pose proof (Zlength_nonneg clause_words).
  assert (Hmod : c mod 2 = 0).
  { apply Z.mod_divide; [lia |].
    apply Z.rem_divide; [lia | exact H_c]. }
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_propagate entail wits (16 proofs) ===== *)
Lemma proof_of_solver_propagate_entail_wit_5_1_scan_move : solver_propagate_entail_wit_5_1_scan_move.
Proof.
  unfold solver_propagate_entail_wit_5_1_scan_move.
  unfold stats_propagations, stats_inspects.
  Unfold.
  entailer_with ltac:(lia).
  left.
  intros.
  subst retval_2.
  subst retval_3.
  subst retval_4.
  subst scan_current.
  lazymatch goal with
  | Hsem : solver_propagation_scan_semantics
             ?n ?F ?A ?K ?M ?p ?confl ?kept ?rest |- _ =>
      pose proof Hsem as Hsem0
  end.
  lazymatch goal with
  | Hphysical : propagation_watch_scan_physical
                  ?source ?kept ?moved ?rest ?garbage ?memory ?ii ?jj |- _ =>
      pose proof Hphysical as Hphysical0
  end.
  lazymatch goal with
  | Hlt : ii < Zlength ?source |- _ => pose proof Hlt as Hlt0
  end.
  assert (Hconfl0 : confl = 0).
  { unfold solver_propagation_scan_semantics in Hsem0.
    destruct Hsem0 as [[Hconfl0 _] | [_ [Hrest0 _]]].
    - exact Hconfl0.
    - subst rest.
      unfold propagation_watch_scan_physical in Hphysical0.
      destruct Hphysical0 as [_ [Hmemory [_ [Hprefix Hlength]]]].
      rewrite app_nil_r in Hmemory.
      rewrite Hmemory, Hprefix in Hlength.
      rewrite <- Hlength in Hlt0.
      exfalso. exact (Z.lt_irrefl ii Hlt0). }
  subst confl.
  lazymatch goal with
  | Hsem : solver_propagation_scan_semantics _ _ _ _ _ _ 0 _ _ |- _ =>
      unfold solver_propagation_scan_semantics in Hsem;
      destruct Hsem as [Hlive | Hconflict];
      [ destruct Hlive as
          [_ [Hweak [Hprop_level [Hheap_ready
             [Hheap_covers [Hreasonless [Hcurrent_level Hscan_tail]]]]]]]
      | destruct Hconflict as [Hnonzero _];
        exfalso; apply Hnonzero; reflexivity ]
  end.
  lazymatch goal with
  | Hupdate : tagged_enqueue_conflict_memory =
                replace_Znth ii (Znth ii tagged_memory 0) tagged_memory |- _ =>
      pose proof Hupdate as Hupdate0
  end.
  lazymatch goal with
  | Htag : tagged_memory =
             replace_Znth jj (Znth ii tagged_memory 0) watch_memory |- _ =>
      pose proof Htag as Htag0
  end.
  lazymatch goal with
  | Hwatch : watch_memory =
      raw_prefix ++ Znth ii tagged_memory 0 :: raw_suffix |- _ =>
      pose proof Hwatch as Hwatch0
  end.
  lazymatch goal with
  | Hrawlen : Zlength raw_prefix = ii |- _ =>
      pose proof Hrawlen as Hrawlen0
  end.
  lazymatch goal with
  | Hretval6 : retval_6 = lit_neg_c p |- _ =>
      pose proof Hretval6 as Hretval60
  end.
  lazymatch goal with
  | Hbinarylen : Zlength (ms_binary_lits Mscan) = 2 |- _ =>
      pose proof Hbinarylen as Hbinarylen0
  end.
  pose proof Hphysical0 as Hphysical_live.
  unfold propagation_watch_scan_physical in Hphysical_live.
  destruct Hphysical_live as
    [Hscan_inv [Hmemory [Hkept_len [Hprefix_len Hmemory_len]]]].
  assert (Hii0 : 0 <= ii).
  { rewrite <- Hprefix_len. apply Zlength_nonneg. }
  assert (Hjj0 : 0 <= jj).
  { rewrite <- Hkept_len. apply Zlength_nonneg. }
  assert (Hjjii : jj <= ii).
  { rewrite <- Hkept_len, <- Hprefix_len, Zlength_app.
    pose proof (Zlength_nonneg garbage). lia. }
  assert (Hconcat :
    raw_prefix ++ Znth ii tagged_memory 0 :: raw_suffix =
      (retained ++ garbage) ++ rest).
  { rewrite <- Hwatch0. rewrite Hmemory, app_assoc. reflexivity. }
  assert (Hrest : rest = Znth ii tagged_memory 0 :: raw_suffix).
  { apply app_eq_app in Hconcat as [[m [Hm Htail]] | [m [Hm Htail]]].
    - assert (HZ : Zlength m = 0).
      { rewrite Hm in Hrawlen0. rewrite Zlength_app, Hprefix_len in Hrawlen0.
        lia. }
      destruct m as [|a m].
      + exact Htail.
      + exfalso. rewrite Zlength_cons in HZ.
        pose proof (Zlength_nonneg m). lia.
    - assert (HZ : Zlength m = 0).
      { rewrite Hm in Hprefix_len. rewrite Zlength_app, Hrawlen0 in Hprefix_len.
        lia. }
      destruct m as [|a m].
      + symmetry. simpl in Htail. exact Htail.
      + exfalso. rewrite Zlength_cons in HZ.
        pose proof (Zlength_nonneg m). lia. }
  entailer_with ltac:(lia).
  Exists (replace_Znth (1 - 0) retval_6 (ms_binary_lits Mscan))
         (clause_lits_addr (ms_binary Mscan)).
  entailer_with ltac:(int_auto).
  unfold IntArray.full, IntArray.seg, store_array.
  entailer_with ltac:(lia).
  - rewrite !replace_Znth_Znth.
    entailer_with ltac:(lia).
  - rewrite Hupdate0.
    rewrite replace_Znth_Znth.
    reflexivity.
  - rewrite Hupdate0.
    rewrite replace_Znth_Znth.
    exact Htag0.
  - unfold propagation_binary_conflict_scan_ready.
    split; [assumption|].
    split; [exact Hheap_covers|].
    split; [exact Hreasonless|].
    split; [exact Hcurrent_level|].
    split; [assumption|].
    split; [assumption|].
    split; [lia|].
    split; [assumption|].
    split; lia.
  - replace (1 - 0) with 1 by lia.
    rewrite Znth_replace_Znth_Same by lia. exact Hretval60.
  - rewrite Zlength_replace_Znth. exact Hbinarylen0.
Qed.

Lemma proof_of_solver_propagate_entail_wit_5_2_scan_move : solver_propagate_entail_wit_5_2_scan_move.
Proof.
  unfold solver_propagate_entail_wit_5_2_scan_move.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_binary_ready_p4 Mentry Mscan retval_2 retval_3 retval_4 retval_6 scan_current ii jj
    confl retained garbage rest tagged_memory raw_prefix raw_suffix.
Qed.

Lemma proof_of_solver_propagate_entail_wit_6_1_scan_same : solver_propagate_entail_wit_6_1_scan_same.
Proof.
  unfold solver_propagate_entail_wit_6_1_scan_same.
  unfold stats_propagations, stats_inspects.
  Unfold.
  entailer_with ltac:(lia).
  left.
  intros.
  bind_fact ( retval_6 = lit_neg_c p ) as H_retval_6.
  bind_fact ( Zlength (ms_binary_lits Mscan) = 2 ) as H_Zlength.
  bind_fact ( tagged_enqueue_conflict_memory = replace_Znth ii (Znth ii tagged_memory 0) tagged_memory )
      as H_tagged_enqueue_conflict_memory.
  bind_fact ( retval_2 = tag_lit (Znth ii (replace_Znth ii (Znth ii tagged_memory 0) (replace_Znth ii (Znth ii
      tagged_memory 0) tagged_memory)) 0) )
      as H_retval_2.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( is_tag scan_current = msat_true ) as H_is_tag.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength_2.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest )
      as H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj )
      as H_propagation_watch_scan_physical.
  bind_fact ( simp_count = ms_simpdb_props Mscan ) as H_simp_count.
  bind_fact ( prop_count = Znth 2 (ms_stats Mscan) 0 ) as H_prop_count.
  (* The enqueue arguments arrive spelled logically; restore the LHS spelling first, because
     cancellation is syntactic and will not fire across the two forms. *)
  rewrite !replace_Znth_Znth in H_retval_2.
  rewrite H_Znth in H_retval_2.
  subst retval_2.
  subst retval_3.
  subst retval_4.
  (* physical scan decomposition, kept as a copy so H_propagation_watch_scan_physical survives *)
  pose proof H_propagation_watch_scan_physical as Hphys.
  unfold propagation_watch_scan_physical in Hphys.
  destruct Hphys as [Hscan_inv [Hmemory [Hkept_len [Hprefix_len Hmemory_len]]]].
  assert (Hconfl : confl = 0).
  { pose proof H_solver_propagation_scan_semantics as Hsem0.
    unfold solver_propagation_scan_semantics in Hsem0.
    destruct Hsem0 as [[Hc _] | [_ [Hrest0 _]]].
    - exact Hc.
    - subst rest.
      rewrite app_nil_r in Hmemory.
      rewrite Hmemory, Hprefix_len in Hmemory_len.
      lia. }
  subst confl.
  assert (Hconcat :
    raw_prefix ++ scan_current :: raw_suffix = (retained ++ garbage) ++ rest).
  { rewrite <- H_watch_memory. rewrite Hmemory, app_assoc. reflexivity. }
  assert (Hrest : rest = scan_current :: raw_suffix).
  { apply app_eq_app in Hconcat as [[m [Hm Htail]] | [m [Hm Htail]]].
    - assert (HZ : Zlength m = 0).
      { rewrite Hm in H_Zlength_2. rewrite Zlength_app, Hprefix_len in H_Zlength_2.
        lia. }
      destruct m as [|a m].
      + exact Htail.
      + exfalso. rewrite Zlength_cons in HZ.
        pose proof (Zlength_nonneg m). lia.
    - assert (HZ : Zlength m = 0).
      { rewrite Hm in Hprefix_len. rewrite Zlength_app, H_Zlength_2 in Hprefix_len.
        lia. }
      destruct m as [|a m].
      + symmetry. simpl in Htail. exact Htail.
      + exfalso. rewrite Zlength_cons in HZ.
        pose proof (Zlength_nonneg m). lia. }
  pose proof H_solver_propagation_scan_semantics as Hsem.
  unfold solver_propagation_scan_semantics in Hsem.
  destruct Hsem as [Hlive | Hconflict];
  [ destruct Hlive as
      [_ [Hweak [Hprop_level [Hheap_ready [Hheap_covers
         [Hreasonless [Hcurrent_level Hscan_tail]]]]]]]
  | destruct Hconflict as [Hnonzero _];
    exfalso; apply Hnonzero; reflexivity ].
  entailer_with ltac:(lia).
  Exists (replace_Znth (1 - 0) retval_6 (ms_binary_lits Mscan))
    (clause_lits_addr (ms_binary Mscan)).
  entailer_with ltac:(lia).
  (* Normalize the one spatial residue, then dispatch each pure predicate
     to its own fact. Every remaining goal must match one of these cases. *)
  all: lazymatch goal with
       | |- _ |-- _ =>
           unfold IntArray.full, IntArray.seg, store_array;
           entailer_with ltac:(int_auto)
       | _ => idtac
       end.
  all: lazymatch goal with
       | |- clause_lits_pointer _ _ =>
           unfold clause_lits_pointer; reflexivity
       | |- Znth _ (replace_Znth _ _ _) _ = _ =>
           replace (1 - 0) with 1 by lia;
           rewrite Znth_replace_Znth_Same by lia; exact H_retval_6
       | |- Znth _ _ _ = _ =>
           rewrite H_tagged_enqueue_conflict_memory, replace_Znth_Znth;
           exact H_Znth
       | |- _ = replace_Znth _ _ _ =>
           rewrite H_tagged_enqueue_conflict_memory, replace_Znth_Znth;
           exact H_tagged_memory
       | |- Zlength _ = _ =>
           rewrite Zlength_replace_Znth; exact H_Zlength
       | |- propagation_binary_conflict_scan_ready _ _ _ _ _ _ _ _ =>
           unfold propagation_binary_conflict_scan_ready;
           split; [exact H_is_tag|];
           split; [exact Hheap_covers|];
           split; [exact Hreasonless|];
           split; [exact Hcurrent_level|];
           split; [exact H_simp_count|];
           split; [exact H_prop_count|];
           split; [lia|]; split; [lia|]; split; lia
       end.
Qed.

Lemma proof_of_solver_propagate_entail_wit_6_2_scan_same : solver_propagate_entail_wit_6_2_scan_same.
Proof.
  unfold solver_propagate_entail_wit_6_2_scan_same.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_binary_ready_p4 Mentry Mscan retval_2 retval_3 retval_4 retval_6 scan_current ii jj
    confl retained garbage rest tagged_memory raw_prefix raw_suffix.
Qed.

Lemma proof_of_solver_propagate_entail_wit_7_scan_move : solver_propagate_entail_wit_7_scan_move.
Proof.
  unfold solver_propagate_entail_wit_7_scan_move.
  unfold stats_inspects.
  Unfold.
  entailer_with ltac:(lia).
  left.
  intros.
  bind_fact ( retval_2 = tag_lit (Znth ii (replace_Znth ii (Znth ii tagged_enqueue_conflict_memory 0)
      tagged_enqueue_conflict_memory) 0) )
      as H_retval_2.
  bind_fact ( scratch_base0 = clause_lits_addr (ms_binary Mscan) ) as H_scratch_base0.
  bind_fact ( Znth ii tagged_enqueue_conflict_memory 0 = scan_current ) as H_Znth.
  bind_fact ( confl = ms_binary Mscan ) as H_confl.
  bind_fact ( Zlength scratch_contents = 2 ) as H_Zlength.
  bind_fact ( Znth 1 scratch_contents 0 = lit_neg_c p ) as H_Znth_2.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength_2.
  bind_fact ( tagged_enqueue_conflict_memory = replace_Znth jj scan_current watch_memory )
      as H_tagged_enqueue_conflict_memory.
  rewrite <- H_scratch_base0.
  rewrite H_confl.
  rewrite replace_Znth_Znth in H_retval_2.
  rewrite replace_Znth_Znth.
  entailer_with ltac:(lia).
  Exists tagged_enqueue_conflict_memory (jj + 1) (ii + 1)
         (replace_Znth 0 retval_2 scratch_contents) scratch_base0.
  entailer_with ltac:(lia).
  unfold IntArray.full, IntArray.seg, store_array.
  entailer_with ltac:(lia).
  all: msat_binary_copy_start_close_p4 raw_suffix H_watch_memory H_Zlength_2
       H_tagged_enqueue_conflict_memory H_Znth_2 H_retval_2 H_Znth H_Zlength.
Qed.

Lemma proof_of_solver_propagate_entail_wit_8_scan_same : solver_propagate_entail_wit_8_scan_same.
Proof.
  unfold solver_propagate_entail_wit_8_scan_same.
  unfold stats_inspects.
  Unfold.
  entailer_with ltac:(lia).
  left.
  intros.
  bind_fact ( retval_2 = tag_lit (Znth ii (replace_Znth ii (Znth ii tagged_enqueue_conflict_memory 0)
      tagged_enqueue_conflict_memory) 0) )
      as H_retval_2.
  bind_fact ( scratch_base0 = clause_lits_addr (ms_binary Mscan) ) as H_scratch_base0.
  bind_fact ( Znth ii tagged_enqueue_conflict_memory 0 = scan_current ) as H_Znth.
  bind_fact ( confl = ms_binary Mscan ) as H_confl.
  bind_fact ( Zlength scratch_contents = 2 ) as H_Zlength.
  bind_fact ( Znth 1 scratch_contents 0 = lit_neg_c p ) as H_Znth_2.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength_2.
  bind_fact ( tagged_enqueue_conflict_memory = replace_Znth jj scan_current watch_memory )
      as H_tagged_enqueue_conflict_memory.
  rewrite replace_Znth_Znth in H_retval_2.
  rewrite replace_Znth_Znth.
  entailer_with ltac:(lia).
  Exists tagged_enqueue_conflict_memory (jj + 1) (ii + 1)
         (replace_Znth 0 retval_2 scratch_contents) scratch_base0.
  entailer_with ltac:(lia).
  unfold IntArray.full, IntArray.seg, store_array.
  entailer_with ltac:(lia).
  (* The two sides spell the same addresses differently (confl vs ms_binary, scratch_base0
     vs clause_lits_addr, `0 - 0` vs `0`), so the binary-clause scratch cells do not cancel
     until the first goal has re-spelled them. *)
  { rewrite H_confl, H_scratch_base0.
    replace (0 - 0) with 0 by lia.
    entailer_with ltac:(lia). }
  all: msat_binary_copy_start_close_p4 raw_suffix H_watch_memory H_Zlength_2
       H_tagged_enqueue_conflict_memory H_Znth_2 H_retval_2 H_Znth H_Zlength.
Qed.

Lemma proof_of_solver_propagate_entail_wit_9_1_scan_move : solver_propagate_entail_wit_9_1_scan_move.
Proof.
  unfold solver_propagate_entail_wit_9_1_scan_move.
  unfold stats_inspects.
  Unfold.
  left.
  intros.
  subst copy_dst_2.
    bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
    bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src_2 copy_src_2
      copy_memory_2 ) as H_binary_watch_copy_progress.
  assert (Hcursor : copy_src_2 < Zlength source_words).
  { change (sizeof (PTR)) with ptr_size_Z in *. solve_arch. }
  assert (Hwatch_len : Zlength watch_memory = Zlength source_words).
  { pose proof H_propagation_watch_scan_physical as Hphysical_len.
    unfold propagation_watch_scan_physical in Hphysical_len.
    tauto. }
  assert (Hcursor_words : copy_src_2 < Zlength watch_memory) by lia.
  pose proof msat_binary_watch_write_snoc as Hwrite_app.
  pose proof msat_binary_watch_write_endpoint as Hwrite_endpoint.
  assert (Hprogress_next :
    binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix
      ii jj (copy_src_2 + 1) (copy_src_2 + 1) copy_memory_2).
  { unfold binary_watch_copy_progress in H_binary_watch_copy_progress |- *.
    destruct H_binary_watch_copy_progress as [copied [copy_rest
      [Hwords [Hkept [Hbounds [Hsuffix
        [Hsrc [Hdst [Hmemory Hmemory_len]]]]]]]]].
    destruct copy_rest as [|x copy_rest].
    - rewrite Hwords, Hsuffix, app_nil_r, !Zlength_app,
        Zlength_cons, Hkept in Hcursor_words.
      rewrite Hsrc in Hcursor_words. lia.
    - assert (Hii_jj : ii = jj) by lia.
      pose proof (Zlength_nonneg copied) as Hcopied_nonneg.
      assert (Hnext_words : Znth copy_src_2 watch_memory 0 = x).
      { rewrite Hwords, app_Znth2 by (rewrite Hkept, Hsrc; lia).
        rewrite Hsrc, Hkept.
        replace (ii + 1 + Zlength copied - ii) with
          (1 + Zlength copied) by lia.
        rewrite Znth_cons by lia.
        replace (1 + Zlength copied - 1) with
          (Zlength copied) by lia.
        rewrite Hsuffix, app_Znth2 by lia.
        replace (Zlength copied - Zlength copied) with 0 by lia.
        reflexivity. }
      assert (Hnext_memory : Znth copy_src_2 copy_memory_2 0 = x).
      { rewrite Hmemory.
        pose proof
          (Hwrite_endpoint (jj + 1) copied
            (replace_Znth jj scan_current watch_memory) 0)
          as Hendpoint.
        rewrite Hdst.
        rewrite Hendpoint by
          (try rewrite Zlength_replace_Znth; lia).
        rewrite Znth_replace_Znth_Diff by lia.
        rewrite Hdst in Hnext_words.
        exact Hnext_words. }
      exists (copied ++ (x :: nil)), copy_rest.
      split; [exact Hwords|].
      split; [exact Hkept|].
      split; [exact Hbounds|].
      split.
      { rewrite Hsuffix, <- app_assoc. simpl. reflexivity. }
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      split.
      { rewrite Hwrite_app, <- Hmemory.
        replace (jj + 1 + Zlength copied) with copy_src_2 by lia.
        rewrite <- Hnext_memory, replace_Znth_Znth. reflexivity. }
      exact Hmemory_len. }
  Exists copy_memory_2 (copy_src_2 + 1) (copy_src_2 + 1)
         scratch_lits_2 scratch_base_2.
  (* The written cell arrives unfolded: the LHS array carrier is `cell ** PtrArray.missing_i`
     rather than a refolded `PtrArray.full`, so the hole has to be merged back explicitly
     before the entailer can cancel the two sides. *)
  try change (sizeof (PTR)) with ptr_size_Z.
  fold_arch.
  sep_apply_l_atomic
    (PtrArray.missing_i_merge_to_full begin copy_src_2 (Zlength source_words)
      (Znth copy_src_2 copy_memory_2 0) copy_memory_2);
  rewrite ?replace_Znth_Znth;
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_entail_wit_9_2_scan_move : solver_propagate_entail_wit_9_2_scan_move.
Proof.
  unfold solver_propagate_entail_wit_9_2_scan_move.
  unfold stats_inspects.
  Unfold.
  entailer_with ltac:(lia).
  right.
  intros.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj )
      as H_propagation_watch_scan_physical.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src_2 copy_dst_2
      copy_memory_2 )
      as H_binary_watch_copy_progress.
  assert (Hcursor : copy_src_2 < Zlength source_words).
  { change (sizeof (PTR)) with ptr_size_Z in *. solve_arch. }
  assert (Hwatch_len : Zlength watch_memory = Zlength source_words).
  { pose proof H_propagation_watch_scan_physical as Hphysical_len.
    unfold propagation_watch_scan_physical in Hphysical_len.
    tauto. }
  assert (Hcursor_words : copy_src_2 < Zlength watch_memory) by lia.
  pose proof msat_binary_watch_write_snoc as Hwrite_app.
  pose proof msat_binary_watch_write_after as Hwrite_after.
  assert (Hprogress_next :
    binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix
      ii jj (copy_src_2 + 1) (copy_dst_2 + 1)
      (replace_Znth copy_dst_2
        (Znth copy_src_2 copy_memory_2 0) copy_memory_2)).
  { unfold binary_watch_copy_progress in H_binary_watch_copy_progress |- *.
    destruct H_binary_watch_copy_progress as [copied [copy_rest
      [Hwords [Hkept [Hbounds [Hsuffix
        [Hsrc [Hdst [Hmemory Hmemory_len]]]]]]]]].
    destruct copy_rest as [|x copy_rest].
    - rewrite Hwords, Hsuffix, app_nil_r, !Zlength_app,
        Zlength_cons, Hkept in Hcursor_words.
      rewrite Hsrc in Hcursor_words. lia.
    - pose proof (Zlength_nonneg copied) as Hcopied_nonneg.
      assert (Hnext_words : Znth copy_src_2 watch_memory 0 = x).
      { rewrite Hwords, app_Znth2 by (rewrite Hkept, Hsrc; lia).
        rewrite Hsrc, Hkept.
        replace (ii + 1 + Zlength copied - ii) with
          (1 + Zlength copied) by lia.
        rewrite Znth_cons by lia.
        replace (1 + Zlength copied - 1) with
          (Zlength copied) by lia.
        rewrite Hsuffix, app_Znth2 by lia.
        replace (Zlength copied - Zlength copied) with 0 by lia.
        reflexivity. }
      assert (Hnext_memory : Znth copy_src_2 copy_memory_2 0 = x).
      { rewrite Hmemory.
        rewrite Hwrite_after by
          (try rewrite Zlength_replace_Znth; lia).
        rewrite Znth_replace_Znth_Diff by lia.
        exact Hnext_words. }
      exists (copied ++ (x :: nil)), copy_rest.
      split; [exact Hwords|].
      split; [exact Hkept|].
      split; [exact Hbounds|].
      split.
      { rewrite Hsuffix, <- app_assoc. simpl. reflexivity. }
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      split.
      { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      split.
      { rewrite Hwrite_app, <- Hmemory, Hdst, Hnext_memory.
        reflexivity. }
      rewrite Zlength_replace_Znth. exact Hmemory_len. }
  assert (Hcopy_len : Zlength copy_memory_2 = Zlength source_words).
  { pose proof H_binary_watch_copy_progress as Hcopy_carrier.
    unfold binary_watch_copy_progress in Hcopy_carrier.
    destruct Hcopy_carrier as [copied0 [rest0
      [_ [_ [_ [_ [_ [_ [_ Hmemory_len0]]]]]]]]].
    lia. }
  Exists (replace_Znth copy_dst_2
            (Znth copy_src_2 copy_memory_2 0) copy_memory_2)
         (copy_dst_2 + 1) (copy_src_2 + 1)
         scratch_lits_2 scratch_base_2.
  entailer_with ltac:(lia).
  sep_apply PtrArray.full_to_seg.
  sep_apply (PtrArray.seg_merge_to_full begin 0
    (copy_dst_2 + 1) (copy_src_2 + 1)); try lia.
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (copy_src_2 + 1 - 0) with (copy_src_2 + 1) by lia.
  sep_apply PtrArray.full_to_seg.
  (* `full_to_seg` re-introduces the base offset as `begin + 0 * ptr_size_Z`, which no longer
     matches the earlier `replace` on `sizeof (PTR)`.  Normalise by arithmetic instead of
     naming the stride at all: `0 * n = 0` for any `n`, so this survives any pointer width. *)
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  sep_apply (PtrArray.seg_merge_to_full begin 0
    (copy_src_2 + 1) (Zlength source_words)); try lia.
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  entailer_with ltac:(lia).
  rewrite (replace_Znth_split 0
    (Znth copy_src_2 copy_memory_2 0) copy_dst_2 copy_memory_2) by lia.
  rewrite app_Znth2 by (rewrite Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia.
  replace (copy_src_2 - (copy_dst_2 + 1) -
    (copy_src_2 - (copy_dst_2 + 1))) with 0 by lia.
  rewrite Znth0_cons.
  rewrite replace_Znth_app_r by
    (rewrite Zlength_sublist by lia; lia).
  rewrite replace_Znth_nothing by
    (rewrite Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia.
  replace (copy_dst_2 - (copy_dst_2 - 0)) with 0 by lia.
  simpl [replace_Znth].
  assert (Htail :
    sublist (copy_dst_2 + 1) (Zlength copy_memory_2) copy_memory_2 =
    (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 ++
      (Znth copy_src_2 copy_memory_2 0 :: nil)) ++
    sublist (copy_src_2 + 1) (Zlength copy_memory_2) copy_memory_2).
  { rewrite (sublist_split (copy_dst_2 + 1)
      (Zlength copy_memory_2) (copy_src_2 + 1) copy_memory_2) by lia.
    rewrite (sublist_split (copy_dst_2 + 1)
      (copy_src_2 + 1) copy_src_2 copy_memory_2) by lia.
    rewrite (sublist_single 0 copy_src_2 copy_memory_2) by lia.
    reflexivity. }
  rewrite <- Hcopy_len, Htail.
  rewrite <- !app_assoc.
  (* `reflexivity` would close this up to conversion -- `replace_Znth` computes -- but
     `begin + 0` is not convertible to `begin` for a symbolic base, so the offset has to be
     rewritten away first. *)
  rewrite ?Z.add_0_r.
  reflexivity.
Qed.

Lemma proof_of_solver_propagate_entail_wit_10_binary_conflict : solver_propagate_entail_wit_10_binary_conflict.
Proof.
  unfold solver_propagate_entail_wit_10_binary_conflict.
  unfold stats_propagations.
  aggressive_pre_process.
    bind_fact ( propagation_binary_conflict_exit n F A_arr K M0 Mentry Mscan Mroute p scan_current confl source_words
      retained moved rest copy_memory garbage_route retained_route ) as H_propagation_binary_conflict_exit.
    bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( ws = vecp_slot wlists_entry p ) as H_ws.
  unfold propagation_binary_conflict_exit in H_propagation_binary_conflict_exit.
  destruct H_propagation_binary_conflict_exit as [Hshape [Hseed [Hframe [Hfront
    [Htransition [Hstep [Hsem [Hphysical Hconfl]]]]]]]].
  unfold propagation_scan_conflict_step in Hstep.
  destruct Hstep as [Hretained Hphysical_step].
  unfold propagation_watch_scan_physical in Hphysical.
  destruct Hphysical as [Hinv_final
    [Hmemory_final [Hkept_final [Hprefix_final Hmemory_final_length]]]].
  unfold wlist_scan_inv in Hinv_final.
  assert (Hretained_bound : Zlength retained_route <= Zlength source_words).
  { pose proof (Zlength_perm_eq _ _ _ Hinv_final) as Hlen.
    rewrite !Zlength_app in Hlen. cbn in Hlen.
    pose proof (Zlength_nonneg moved). lia. }
  pose proof (Zlength_nonneg retained_route) as Hretained_nonneg.
  unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
  destruct H_propagation_watch_scan_physical as [Hinv_old
    [Hmemory_old [Hkept_old [Hprefix_old Hmemory_old_length]]]].
  unfold wlist_scan_inv in Hinv_old.
  assert (Hsource_positive : 0 < Zlength source_words).
  { pose proof (Zlength_perm_eq _ _ _ Hinv_old) as Hlen.
    rewrite H_rest in Hlen.
    rewrite !Zlength_app in Hlen.
    rewrite Zlength_cons in Hlen. cbn in Hlen.
    pose proof (Zlength_nonneg retained).
    pose proof (Zlength_nonneg moved).
    pose proof (Zlength_nonneg raw_suffix). lia. }
  Left.
  Exists s_trail s_reasons (Znth 2 (ms_stats Mroute) 0)
    (ms_simpdb_props Mroute)
    scan_caps_pre scan_wcap scan_caps_post scan_wm_pre scan_wm_post
    retained_route source_words moved garbage_route copy_memory
    (Zlength source_words) (Zlength retained_route)
    retained_route (@nil Z) Mentry.
  Exists Mroute levels_entry.
  split_pure_spatial.
  - rewrite <- H_ws.
    unfold solver_propagation_scan_arrays_noqh_at.
    set_String_name. sepcon_assoc_change. sepcon_cancel.
  - split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try tauto;
      try (rewrite app_nil_r; reflexivity); try lia.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_1_scan_same : solver_propagate_entail_wit_11_1_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_1_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_2_scan_same : solver_propagate_entail_wit_11_2_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_2_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_3_scan_same : solver_propagate_entail_wit_11_3_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_3_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_4_scan_same : solver_propagate_entail_wit_11_4_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_4_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_5_scan_same : solver_propagate_entail_wit_11_5_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_5_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_11_6_scan_same : solver_propagate_entail_wit_11_6_scan_same.
Proof.
  unfold solver_propagate_entail_wit_11_6_scan_same.
  unfold stats_propagations, stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.

Lemma proof_of_solver_propagate_entail_wit_30_2_real_migrated : solver_propagate_entail_wit_30_2_real_migrated.
Proof.
  unfold solver_propagate_entail_wit_30_2_real_migrated.
  unfold stats_propagations, stats_inspects.
  Unfold.
  aggressive_pre_process.
  Right.
  Exists trl_next rsn_next simp_count_next prop_count_next
    next_caps_pre next_wcap next_caps_post next_wm_pre next_wm_post
    logical_next source_words_next moved_next garbage_next memory_next
    ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  subst lvl_next.
  split_pure_spatial.
  - unfold solver_propagation_scan_core_at, stats_propagate_scan.
    cbn -[ptr_size_Z Znth].
    set_String_name. sepcon_assoc_change. sepcon_cancel. subst_all_strings.
    csimpl. intros m Hm. exact Hm.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

(* ===== solver_propagate partial_solve wits (29 proofs) ===== *)
Lemma proof_of_solver_propagate_partial_solve_wit_49_scan_move_pure :
  solver_propagate_partial_solve_wit_49_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_49_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_52_scan_same_pure :
  solver_propagate_partial_solve_wit_52_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_52_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_71_scan_same_pure :
  solver_propagate_partial_solve_wit_71_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_71_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_73_scan_move_pure :
  solver_propagate_partial_solve_wit_73_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_73_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_75_scan_same_pure :
  solver_propagate_partial_solve_wit_75_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_75_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_128_scan_same_pure :
  solver_propagate_partial_solve_wit_128_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_128_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_129_scan_same_pure :
  solver_propagate_partial_solve_wit_129_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_129_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_130_scan_move_pure :
  solver_propagate_partial_solve_wit_130_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_130_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_131_scan_move_pure :
  solver_propagate_partial_solve_wit_131_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_131_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_132_scan_same_pure :
  solver_propagate_partial_solve_wit_132_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_132_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_133_scan_same_pure :
  solver_propagate_partial_solve_wit_133_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_133_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_nonneg_p4 scan_wm_pre.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_255_scan_move_pure :
  solver_propagate_partial_solve_wit_255_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_255_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right.
  intros.
  bind_fact ( Znth (retval_3 - 0) (mt_assigns (ms_core Mscan)) 0 = 0 + 0 - 1 ) as H_Znth.
  rewrite Z.sub_0_r in H_Znth.
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_257_scan_same_pure :
  solver_propagate_partial_solve_wit_257_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_257_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right.
  intros.
  subst retval_5.
  subst retval_4.
  bind_fact ( Znth (retval_3 - 0) (mt_assigns (ms_core Mscan)) 0 = 0 + 0 - 1 ) as H_Znth.
  bind_fact ( retval_2 = lit_sign_c (Znth 0 clause_contents 0) ) as H_retval_2.
  rewrite Z.sub_0_r in H_Znth.
  (* This obligation carries the `sign <> 0` arm of the scan test; there is no equation for the
     sign, so it is the disequality together with the 0/1 range facts that lets `lia` pin it
     to 1. *)
  assert (Hsign : lit_sign_c (Znth 0 clause_contents 0) = 1) by lia.
  rewrite H_retval_2, Hsign.
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_259_scan_move_pure :
  solver_propagate_partial_solve_wit_259_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_259_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right.
  intros.
  bind_fact ( Znth (retval_3 - 0) (mt_assigns (ms_core Mscan)) 0 = 0 + 0 - 1 ) as H_Znth.
  rewrite Z.sub_0_r in H_Znth.
  assert (Hsign : retval_2 = 1) by lia.
  rewrite Hsign.
  rewrite H_Znth.
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_263_scan_move_pure :
  solver_propagate_partial_solve_wit_263_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_263_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right.
  intros.
  subst retval_5.
  subst retval_4.
  bind_fact ( Znth (retval_3 - 0) (mt_assigns (ms_core Mscan)) 0 = 0 + 0 - 1 ) as H_Znth.
  rewrite Z.sub_0_r in H_Znth.
  (* The RHS is spelled with the named result `retval_2` rather than with
     `lit_sign_c (Znth _ clause_contents 0)`, and the literal read here is watch slot 1, not
     slot 0; the range hypotheses still pin the sign to 1, so `lia` proves it on `retval_2`. *)
  assert (Hsign : retval_2 = 1) by lia.
  rewrite Hsign.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_267_scan_same_pure :
  solver_propagate_partial_solve_wit_267_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_267_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right.
  intros.
  subst retval_5.
  subst retval_4.
  bind_fact ( Znth (retval_3 - 0) (mt_assigns (ms_core Mscan)) 0 = 0 + 0 - 1 ) as H_Znth.
  rewrite Z.sub_0_r in H_Znth.
  assert (Hsign : retval_2 = 1) by lia.
  rewrite Hsign.
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_271_scan_move_pure :
  solver_propagate_partial_solve_wit_271_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_271_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right.
  intros.
  bind_fact ( Znth (retval_3 - 0) (mt_assigns (ms_core Mscan)) 0 = 0 + 0 - 1 ) as H_Znth.
  rewrite Z.sub_0_r in H_Znth.
  assert (Hsign : retval_2 = 1) by lia.
  rewrite Hsign.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_448_capacity_copy_pure :
  solver_propagate_partial_solve_wit_448_capacity_copy_pure.
Proof.
  pose proof msat_chararray_seg_base_nonneg as Hchar.
  aggressive_pre_process.
  all: (repeat match goal with
    | H : propagation_capacity_target_facts _ _ _ _ _ _ _ _ |- _ =>
        destruct H as [Hd [Hidx Hcap]]
    end);
    (repeat match goal with
    | H : propagation_destination_index _ _ _ |- _ =>
        destruct H as [Hhole [Htarget Hneq]]
    end).
  all: (try (assert (Hsize : 0 < ms_size Mscan) by lia;
    unfold solver_propagation_scan_arrays_noqh_at,
      solver_propagation_scan_core_at in *;
    sep_apply_l_atomic (Hchar assigns_entry (ms_size Mscan)
      (mt_assigns (ms_core Mscan)) Hsize);
    entailer_with ltac:(lia)));
    (try entailer_with ltac:(lia));
    (try (unfold solver_propagation_scan_arrays_noqh_at,
      solver_propagation_scan_core_at in *; entailer_with ltac:(lia))).
  all: (try (subst logical_words));
    ((unfold propagation_scan_slot; msat_manual_entailer_with ltac:(lia))).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_449_capacity_copy_pure :
  solver_propagate_partial_solve_wit_449_capacity_copy_pure.
Proof.
  aggressive_pre_process.
  all: (bind_fact ( copy_src <= Zlength source_words ) as H_copy_src);
    (repeat match goal with
    | H : propagation_capacity_abort_state _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        destruct H as [HM [Hcert [Hinv [Hshadow [Hcap [Hwatch
          [Hq [Hshape [Hwm Hcaps]]]]]]]]]
    end);
    (repeat match goal with
    | H : propagation_capacity_abort_certified _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        destruct H as [Htrans Hcap2]
    end).
  all: (repeat match goal with
    | H : propagation_capacity_abort_transition _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        destruct H as [Hafter Hinv2]
    end);
    (try (subst M_after; cbn [msolver_propagation_abort msolver_propagation_update mt_set_qhead] in *)).
  (* Every sentence past this point runs on all the pure goals the RHS emitted,
     so the script is cut into `all:`-selected sentences, not one giant sentence. *)
  all: (repeat match goal with
    | H : propagation_capacity_target_facts _ _ _ _ _ _ _ _ |- _ =>
        destruct H as [Hdest [Hidx Hcapidx]]
    end);
    (try (unfold propagation_scan_open in H_copy_src;
    destruct H_copy_src as [Hshape0 [Hseed0 [Hcaller0 Hrest0]]]));
    (try (unfold propagation_caller_frame in Hcaller0;
    destruct Hcaller0 as (Hlim0 & Hroot0 & Hmodel0 & Hdecay0 & Hcap0))).
  all: try (unfold propagation_destination_index;
    cbn [msolver_propagation_abort msolver_propagation_update ];
    unfold propagation_destination_index in Hidx;
    destruct Hidx as [Hhole [Htarget Hneq]];
    repeat split; try assumption;
    try lia).
  all: (try (unfold solver_shape in Hshape0 |- *;
    cbn [msolver_propagation_abort msolver_propagation_update ] in *;
    intuition lia));
    (try (match goal with
    | Hshape : solver_shape _ |- _ =>
        unfold solver_shape in Hshape;
        cbn [msolver_propagation_abort msolver_propagation_update ] in Hshape;
        tauto
    end)).
  all: (repeat match goal with
    | H : solver_propagation_inv _ _ _ _ _ |- _ =>
        unfold solver_propagation_inv in H;
        destruct H as [Hpending Hpropinv]
    end);
    (try (cbn [msolver_propagation_abort msolver_propagation_update mt_set_qhead] in *; assumption)).
  all: (try (unfold propagation_caller_frame;
    cbn [msolver_propagation_abort msolver_propagation_update mt_set_qhead];
    repeat split; assumption));
    (try solve [
    pose proof H_copy_src as HscanX;
    unfold propagation_scan_open in HscanX;
    destruct HscanX as [_ [_ [HcallerX _]]];
    unfold propagation_caller_frame in HcallerX;
    cbn [msolver_propagation_abort msolver_propagation_update mt_set_qhead] in *;
    intuition
  ]).
  all: try solve [
    match goal with
    | Hscan : propagation_scan_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        let HscanX := fresh "HscanX" in
        pose proof Hscan as HscanX;
        unfold propagation_scan_open in HscanX;
        destruct HscanX as [_ [_ [HcallerX _]]];
        unfold propagation_caller_frame in HcallerX;
        cbn [msolver_propagation_abort msolver_propagation_update mt_set_qhead] in *;
        intuition
    end
  ].
  all: (try (repeat split; assumption));
    (entailer_with ltac:(lia)).
  (* The abort-state wmap bound is spelled as `(j - begin) / sizeof(PTR)`, so `j` has to be
     put back to its loop-index equation before the syntactic match below finds a pattern. *)
  all: (match goal with
       | Hj : ?x = _ |- context [ ?x - _ ] => rewrite Hj
       end);
    (reflexivity).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_458_scan_same_pure :
  solver_propagate_partial_solve_wit_458_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_458_scan_same_pure.
  unfold stats_propagations.
  Unfold.
  right. intros.
  bind_fact ( Znth ii migration_post_memory 0 = scan_current ) as H_Znth.
    bind_fact ( Zlength (wlists_split_target_words (Zlength scan_wm_pre) (lit_neg_c candidate) scan_wm_pre scan_wm_post)
      < destination_cap ) as H_Zlength.
  bind_fact ( retval_3 = lit_neg_c candidate ) as H_retval_3.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength_2.
 repeat split_pures; dump_pre_spatial;
  try reflexivity;
  try exact H_Znth;
  try apply Zlength_nonneg;
  (* The destination slot is spelled `wlists_split_target_words p retval_3`; the two bound
     equations put it back into the `Zlength scan_wm_pre` / `lit_neg_c candidate` spelling
     that the capacity hypothesis uses, which is what the final `lia` needs. *)
  rewrite H_retval_3, <- H_Zlength_2.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    clear - H_Zlength. lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_459_scan_same_pure :
  solver_propagate_partial_solve_wit_459_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_459_scan_same_pure.
  unfold stats_propagations.
  Unfold.
  right. intros.
  bind_fact ( Znth ii migration_post_memory 0 = scan_current ) as H_Znth.
  bind_fact ( retval_3 = lit_neg_c candidate ) as H_retval_3.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength.
  rewrite H_retval_3, H_Znth, <- H_Zlength.
  msat_manual_entailer_with ltac:(assumption).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_460_scan_same_pure :
  solver_propagate_partial_solve_wit_460_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_460_scan_same_pure.
  unfold stats_propagations.
  Unfold.
  right. intros.
    bind_fact ( Znth (retval_2 - 0) (mt_assigns (ms_core Mscan)) 0 = signed_last_nbits (signed_last_nbits retval 8 +
      signed_last_nbits retval 8 - 1) 8 ) as H_Znth.
  bind_fact ( retval = lit_sign_c candidate ) as H_retval.
  bind_fact ( candidate = Znth (offset - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0 ) as H_candidate.
  assert (Hsign :
      signed_last_nbits
        (signed_last_nbits retval 8 + signed_last_nbits retval 8 - 1) 8 =
      2 * lit_sign_c candidate - 1).
  { rewrite H_retval. unfold lit_sign_c.
    destruct (Z.odd candidate); reflexivity. }
  assert (Hcandidate : candidate =
      Znth offset
        (propagation_normalized_clause watch0 false_lit clause_contents) 0).
  { rewrite H_candidate. unfold propagation_normalized_clause.
    rewrite Znth_cons by lia.
    rewrite Znth_cons by lia.
    replace (offset - 1 - 1) with (offset - 2) by lia.
    reflexivity. }
  assert (Hassign :
      Znth retval_2 (mt_assigns (ms_core Mscan)) 0 = 2 * retval - 1).
  { rewrite Z.sub_0_r in H_Znth.
    rewrite H_Znth, Hsign, H_retval. reflexivity. }
  assert (Hsign2 :
      signed_last_nbits
        (signed_last_nbits retval 8 + signed_last_nbits retval 8 - 1) 8 =
      2 * retval - 1).
  { rewrite Hsign, H_retval. reflexivity. }
  repeat split_pures; dump_pre_spatial.
  (* Five residual pure goals: the sign identity twice, the candidate re-spelling, and
     the assignment identity twice. *)
  - exact Hsign2.
  - exact Hsign2.
  - exact Hcandidate.
  - exact Hassign.
  - exact Hassign.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_464_unit_move_pure :
  solver_propagate_partial_solve_wit_464_unit_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_464_unit_move_pure.
  unfold stats_propagations.
  msat_propagate_unit_enqueue_input_p4.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_465_unit_same_pure :
  solver_propagate_partial_solve_wit_465_unit_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_465_unit_same_pure.
  unfold stats_propagations.
  msat_propagate_unit_enqueue_input_p4.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_469_unit_move_pure :
  solver_propagate_partial_solve_wit_469_unit_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_469_unit_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right. intros.
    bind_fact ( propagation_replacement_scan_inv n Mscan false_lit (propagation_normalized_clause watch0 false_lit
      clause_contents) (Zlength clause_contents) ) as H_propagation_replacement_scan_inv.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength.
  bind_fact ( false_lit = lit_neg_c p ) as H_false_lit.
  assert (Hlen :
      Zlength (propagation_normalized_clause watch0 false_lit
        clause_contents) = Zlength clause_contents).
  { apply propagation_normalized_clause_length. lia. }
  repeat split_pures; dump_pre_spatial;
  try rewrite H_Zlength;
  try rewrite <- H_false_lit;
  rewrite Hlen;
  exact H_propagation_replacement_scan_inv.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_470_unit_same_pure :
  solver_propagate_partial_solve_wit_470_unit_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_470_unit_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right. intros.
    bind_fact ( propagation_replacement_scan_inv n Mscan false_lit (propagation_normalized_clause watch0 false_lit
      clause_contents) (Zlength clause_contents) ) as H_propagation_replacement_scan_inv.
  assert (Hlen :
      Zlength (propagation_normalized_clause watch0 false_lit
        clause_contents) = Zlength clause_contents).
  { apply propagation_normalized_clause_length. lia. }
  repeat split_pures; dump_pre_spatial;
  (* Assumes the RHS already spells the watch index as `false_lit` and the frontier as `p`;
     only the normalized-clause length fold is left to do. *)
  rewrite Hlen;
  exact H_propagation_replacement_scan_inv.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_482_real_migrated_pure :
  solver_propagate_partial_solve_wit_482_real_migrated_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_482_real_migrated_pure.
  unfold stats_propagations.
  Unfold.
  right. intros.
  bind_fact ( propagation_real_migrated_physical_alias wlists_entry (Zlength scan_wm_pre) (lit_neg_c candidate) scan_current
      destination_index (vecp_slot wlists_entry (lit_neg_c (Znth (offset - 2) (sublist 2 (Zlength clause_contents)
      clause_contents) 0))) scan_wm_pre scan_wm_post (wlists_split_target_words (Zlength scan_wm_pre) (lit_neg_c (Znth
      (offset - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0)) scan_wm_pre scan_wm_post +:: Znth
      (Zlength raw_prefix) migration_post_memory 0) ) as H_propagation_real_migrated_physical_alias.
  bind_fact ( migration_post_memory = replace_Znth ii (Znth ii candidate_post_memory 0) candidate_post_memory ) as
      H_migration_post_memory.
  bind_fact ( Znth ii migration_post_memory 0 = scan_current ) as H_Znth.
  bind_fact ( Zlength (wlists_split_target_words (Zlength scan_wm_pre) (lit_neg_c candidate) scan_wm_pre
      scan_wm_post) < destination_cap ) as H_Zlength.
  bind_fact ( propagation_destination_index (2 * ms_size Mscan) (Zlength scan_wm_pre) (lit_neg_c candidate) ) as
      H_propagation_destination_index.
  bind_fact ( retval_3 = lit_neg_c candidate ) as H_retval_3.
  bind_fact ( Znth (retval_2 - 0) (mt_assigns (ms_core Mscan)) 0 <> signed_last_nbits (signed_last_nbits retval 8
      + signed_last_nbits retval 8 - 1) 8 ) as H_Znth_2.
  bind_fact ( retval_2 = lit_var_c candidate ) as H_retval_2.
  bind_fact ( retval = lit_sign_c candidate ) as H_retval.
  bind_fact ( candidate = Znth (offset - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0 ) as H_candidate.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength_2.
  bind_fact ( candidate_post_memory = watch_memory ) as H_candidate_post_memory.
  bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth_3.
  bind_fact ( logical_words = retained ++ rest ) as H_logical_words.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength_3.
  bind_fact ( false_lit = lit_neg_c p ) as H_false_lit.
  bind_fact ( stop = lits + Zlength clause_contents * sizeof ( INT ) ) as H_stop.
  bind_fact ( k = lits + offset * sizeof ( INT ) ) as H_k.
  assert (Hidx : 0 <= offset - 2 < Zlength (sublist 2 (Zlength clause_contents) clause_contents)).
  { rewrite Zlength_sublist by lia. lia. }
  assert (HcandZ :
      Znth (offset - 2)
        (replace_Znth (offset - 2) candidate
          (sublist 2 (Zlength clause_contents) clause_contents)) 0 =
      candidate).
  { apply Znth_replace_Znth_Same. exact Hidx. }
  assert (Hsig :
      signed_last_nbits
        (signed_last_nbits retval 8 + signed_last_nbits retval 8 - 1) 8 =
      2 * lit_sign_c candidate - 1).
  { rewrite H_retval. unfold lit_sign_c.
    destruct (Z.odd candidate); reflexivity. }
  assert (Hassign :
      Znth (lit_var_c candidate) (mt_assigns (ms_core Mscan)) 0 <>
      2 * lit_sign_c candidate - 1).
  { rewrite <- Hsig, <- H_retval_2. replace retval_2 with (retval_2 - 0) by lia. exact H_Znth_2. }
  assert (Hlayout : propagation_scan_candidate_layout
      scan_current lits
      (lits + Zlength clause_contents * sizeof(INT))
      (lits + offset * sizeof(INT)) offset (lit_neg_c p) p candidate
      (2 * lit_sign_c candidate - 1) clause_contents).
  { unfold propagation_scan_candidate_layout. repeat split;
      try reflexivity; try assumption; lia. }
  assert (Hslot : propagation_scan_slot Mscan p scan_wm_pre logical_words
      scan_wm_post scan_caps_pre scan_wcap scan_caps_post).
  { unfold propagation_scan_slot. repeat split; assumption. }
  assert (Hdest_p : propagation_destination_index (2 * ms_size Mscan) p (lit_neg_c candidate)).
  { rewrite <- H_Zlength_3. exact H_propagation_destination_index. }
  assert (Halias_p : propagation_real_migrated_physical_alias wlists_entry
      p (lit_neg_c candidate) scan_current (lit_neg_c candidate)
      (vecp_slot wlists_entry (lit_neg_c candidate)) scan_wm_pre scan_wm_post
      (wlists_split_target_words p (lit_neg_c candidate)
        scan_wm_pre scan_wm_post ++ cons scan_current nil)).
  { constructor; reflexivity. }
  (* The migrated watcher cell is spelled through `watch_memory` and `retval_3` rather than
     `candidate_post_memory` / `lit_neg_c candidate`; the two asserts below re-spell it. *)
  assert (Hwm0 : Znth ii watch_memory 0 = scan_current).
  { rewrite <- H_candidate_post_memory. exact H_Znth_3. }
  assert (Hwm : Znth ii (replace_Znth ii (Znth ii watch_memory 0) watch_memory) 0 = scan_current).
  { rewrite replace_Znth_Znth. exact Hwm0. }
  (* The twelve pure leaves follow the generated conclusion's order. *)
  repeat split_pures; dump_pre_spatial.
  - rewrite HcandZ. reflexivity.
  - exact Hwm0.
  - exact Hwm.
  - rewrite HcandZ, H_stop, H_k, H_false_lit. exact Hlayout.
  - rewrite HcandZ. exact Hassign.
  - rewrite HcandZ. exact Hdest_p.
  - rewrite HcandZ, H_retval_3, Hwm. exact Halias_p.
  - exact Hslot.
  - rewrite Hwm, <- H_Zlength_3, Zlength_app, Zlength_cons, Zlength_nil.
    clear - H_Zlength. lia.
  - apply Zlength_nonneg.
  - rewrite HcandZ, Hwm. exact Halias_p.
  - rewrite HcandZ, H_stop, H_k, H_false_lit. exact Hlayout.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_491_pure : solver_propagate_partial_solve_wit_491_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_491_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right; intros.
  assert (H_retval : retval = retval_2) by lia.
  bind_fact ( (begin + jj * sizeof ( PTR ) - begin) ÷ sizeof ( PTR ) = jj ) as H_begin.
  bind_fact ( retval_2 = begin ) as H_retval_2.
  bind_fact ( j = begin + jj * sizeof ( PTR ) ) as H_j.
  msat_propagate_close_watch_cursor_bounds H_retval H_begin H_retval_2 begin retained;
  (* The RHS spells the scan cursor as the raw pointer difference `(j - begin) / sizeof(PTR)`
     rather than as `jj`; folding `j` back to its defining equation lets the same quotient
     cancellation the tactic already takes as an argument finish the goal. *)
  rewrite H_j; rewrite !H_begin; lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_492_pure : solver_propagate_partial_solve_wit_492_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_492_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right; intros.
  assert (H_retval : retval = retval_2) by lia.
  bind_fact ( (begin + jj * sizeof ( PTR ) - begin) ÷ sizeof ( PTR ) = jj ) as H_begin.
  bind_fact ( retval_2 = begin ) as H_retval_2.
  bind_fact ( j = begin + jj * sizeof ( PTR ) ) as H_j.
  msat_propagate_close_watch_cursor_bounds H_retval H_begin H_retval_2 begin retained;
  (* The RHS cursor is spelled as the local `j` instead of its defining expression
     `begin + jj * sizeof(PTR)`; the bound equation carries that definition. *)
  rewrite H_j; rewrite !H_begin; lia.
Qed.

(* ===== solver_propagate which_implies wits (12 proofs) ===== *)
Lemma proof_of_solver_propagate_which_implies_wit_1 : solver_propagate_which_implies_wit_1.
Proof.
  unfold solver_propagate_which_implies_wit_1.
  unfold solver_propagate_open_at, stats_propagations, stats_inspects.
  Unfold.
  left. intros.
  unfold solver_propagate_pre, solver_rep_assigns_levels_at.
  Intros act opos rsn trl tgs.
  unfold solver_rep_at.
  Intros.
  destruct H as [Hinv Hseed].
  pose proof H0 as Hshape.
  assert (Htrail : Zlength (mt_trail (ms_core M0)) = ms_qtail M0).
  { unfold solver_shape in Hshape. tauto. }
  assert (Hqhead : 0 <= mt_qhead (ms_core M0) <= ms_qtail M0).
  { unfold solver_shape in Hshape. tauto. }
  assert (Hsize : 0 <= ms_size M0 <= ms_cap M0).
  { unfold solver_shape in Hshape. tauto. }
  assert (Hqtail_size : ms_qtail M0 <= ms_size M0).
  { pose proof Hinv as Hinv_bounds.
    destruct K as [A_inst | A_proc].
    - destruct Hinv_bounds as [_ Hprop].
      destruct Hprop as [Hweak _ _ _ _].
      pose proof (mtw_trail_bound (msw_trail_wf Hweak)) as Hbound.
      pose proof (msw_size Hweak) as Hnsize.
      lia.
    - destruct Hinv_bounds as [_ Hprop].
      destruct Hprop as [Hweak _ _ _ _].
      pose proof (mtw_trail_bound (msa_trail_wf Hweak)) as Hbound.
      pose proof (msa_size Hweak) as Hnsize.
      lia. }
  Exists rsn trl.
  entailer_with ltac:(lia).
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_scalars_rep, solver_vecs_rep, solver_trail_array_rep,
    solver_binary_rep, solver_propagate_frame, stats_rep,
    stats_propagate_frame.
  unfold stats_propagations, stats_inspects.
  Exists act opos tgs.
  entailer_with ltac:(lia).
  cancel.
  csimpl.
  cancel.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_40 : solver_propagate_which_implies_wit_40.
Proof.
  msat_propagate_source_hole_close_p4.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_41 : solver_propagate_which_implies_wit_41.
Proof.
  Unfold.
  right. intros.
  unfold propagation_int_missing.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_42 : solver_propagate_which_implies_wit_42.
Proof.
  msat_propagate_source_hole_close_p4.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_43 : solver_propagate_which_implies_wit_43.
Proof.
  Unfold.
  right. intros.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( ms_wm Mscan = scan_wm_pre ++ logical_words :: scan_wm_post ) as H_ms_wm.
  bind_fact ( ms_wcaps Mscan = scan_caps_pre ++ scan_wcap :: scan_caps_post ) as H_ms_wcaps.
  unfold solver_shape in H_solver_shape.
  rewrite H_ms_wm, H_ms_wcaps in H_solver_shape.
  rewrite !Zlength_app, !Zlength_cons in H_solver_shape.
  entailer_with ltac:(lia); intuition (try lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_44 : solver_propagate_which_implies_wit_44.
Proof.
  Unfold.
  left. intros.
    bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan (Zlength scan_wm_pre) confl retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact ( real_watch_pair (Zlength scan_wm_pre) clause_contents ) as H_real_watch_pair.
  bind_fact ( candidate = Znth (offset - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0 ) as H_candidate.
  assert (Hdestination_of_contents :
      clause_db_pair_contents (ms_prob Mscan) (ms_learnt Mscan)
        scan_current clause_contents ->
      propagation_destination_index (2 * ms_size Mscan)
        (Zlength scan_wm_pre) (lit_neg_c candidate)).
  { intro Hcontents.
    assert (Hp : lit_wf_c n (Zlength scan_wm_pre)).
    { destruct H_solver_propagation_scan_semantics as [Hlive | Hconf].
      - destruct Hlive as (_ & _ & _ & _ & _ & _ & _ & Hp & _).
        exact Hp.
      - destruct Hconf as (_ & _ & Hcancel & _).
        unfold propagation_cancel_ready in Hcancel. tauto. }
    assert (Hweak : solver_propagation_weak n F A_arr K Mscan).
    { destruct H_solver_propagation_scan_semantics as [Hlive | Hconf].
      - destruct Hlive as (_ & Hweak & _). exact Hweak.
      - destruct Hconf as (_ & _ & Hcancel & _).
        exact (proj1 Hcancel). }
    assert (Hshape_db : n = ms_size Mscan /\
        db_wf n (msolver_db Mscan)).
    { unfold solver_propagation_weak in Hweak.
      destruct Hweak as [_ Hweak].
      destruct K as [A_inst | A_proc]; cbn in Hweak.
      - split; [exact (msw_size Hweak) | exact (msw_db_wf Hweak)].
      - split; [exact (msa_size Hweak) | exact (msa_db_wf Hweak)]. }
    destruct Hshape_db as [Hsize Hdb].
    destruct Hcontents as [co [Hin Hco]].
    change (In (scan_current, co) (msolver_db Mscan)) in Hin.
    pose proof (db_wf_obj n (msolver_db Mscan) scan_current co Hdb Hin)
      as Hobj.
    unfold obj_wf in Hobj. rewrite Hco in Hobj.
    destruct Hobj as [Hlen [Hall Hnodup]].
    assert (Hcandidate_at : candidate = Znth offset clause_contents 0).
    { rewrite H_candidate.
      rewrite (Znth_sublist 0 2 (offset - 2) (Zlength clause_contents)
        clause_contents) by lia.
      replace (offset - 2 + 2) with offset by lia. reflexivity. }
    subst candidate.
    assert (Hcandidate_wf : lit_wf_c n (Znth offset clause_contents 0)).
    { apply (Forall_Znth_elim Z (lit_wf_c n) clause_contents 0 offset Hall).
      lia. }
    assert (Hdistinct_at : forall w,
        0 <= w < 2 ->
        Znth w clause_contents 0 = lit_neg_c (Zlength scan_wm_pre) ->
        lit_var_c (Znth offset clause_contents 0) <>
        lit_var_c (lit_neg_c (Zlength scan_wm_pre))).
    { intros w Hw Hwatched.
      pose proof (list_Znth_split 0 clause_contents offset ltac:(lia))
        as Hsplit.
      pose proof Hnodup as Hnodup_split.
      rewrite Hsplit, map_app in Hnodup_split. simpl in Hnodup_split.
      assert (Hinprefix :
          In (lit_var_c (lit_neg_c (Zlength scan_wm_pre)))
            (map lit_var_c (sublist 0 offset clause_contents))).
      { apply in_map.
        assert (Hprefix_value :
            Znth w (sublist 0 offset clause_contents) 0 =
            lit_neg_c (Zlength scan_wm_pre)).
        { rewrite Znth_sublist0 by lia. exact Hwatched. }
        rewrite <- Hprefix_value.
        apply Znth_In. rewrite Zlength_sublist by lia. lia. }
      pose proof (NoDup_app_disjoint
        (map lit_var_c (sublist 0 offset clause_contents))
        (lit_var_c (Znth offset clause_contents 0) ::
         map lit_var_c
           (sublist (offset + 1) (Zlength clause_contents) clause_contents))
        (lit_var_c (lit_neg_c (Zlength scan_wm_pre)))
        Hnodup_split Hinprefix) as Hnotin.
      intro Heq. apply Hnotin. simpl. left. exact Heq. }
    assert (Hcandidate_distinct :
        lit_var_c (Znth offset clause_contents 0) <>
        lit_var_c (lit_neg_c (Zlength scan_wm_pre))).
    { destruct H_real_watch_pair as [Hwatch | Hwatch].
      - apply (Hdistinct_at 0); [lia | exact Hwatch].
      - apply (Hdistinct_at 1); [lia | exact Hwatch]. }
    pose proof (lit_neg_c_wf n (Znth offset clause_contents 0)
      Hcandidate_wf) as Htarget.
    unfold propagation_destination_index.
    split; [destruct Hp; lia |]. split.
    - rewrite <- Hsize. rewrite Hcandidate_at. exact Htarget.
    - intro Heq. apply Hcandidate_distinct.
      rewrite Hcandidate_at in Heq.
      rewrite lit_var_c_neg. rewrite <- Heq. rewrite lit_var_c_neg.
      reflexivity. }
  unfold clause_db_pair_frame at 1. Intros is_learnt.
  unfold clause_db_pair_remainder at 1. Split.
  - Intros co pre post. coq_prop_lift.
    destruct H as [Hprob [Hlits Hlearnt]].
    assert (Hcontents : clause_db_pair_contents
        (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents).
    { exists co. split; [|exact Hlits].
      apply in_or_app. left. rewrite Hprob.
      apply in_or_app. right. simpl. auto. }
    specialize (Hdestination_of_contents Hcontents).
    unfold clause_db_pair_frame. Exists is_learnt.
    unfold clause_db_pair_remainder. Left. Exists co pre post.
    entailer_with ltac:(lia).
  - Intros co pre post. coq_prop_lift.
    destruct H as [Hlearntdb [Hlits Hlearnt]].
    assert (Hcontents : clause_db_pair_contents
        (ms_prob Mscan) (ms_learnt Mscan) scan_current clause_contents).
    { exists co. split; [|exact Hlits].
      apply in_or_app. right. rewrite Hlearntdb.
      apply in_or_app. right. simpl. auto. }
    specialize (Hdestination_of_contents Hcontents).
    unfold clause_db_pair_frame. Exists is_learnt.
    unfold clause_db_pair_remainder. Right. Exists co pre post.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_45 : solver_propagate_which_implies_wit_45.
Proof.
  Unfold.
  left. intros.
    bind_fact ( propagation_destination_index (2 * ms_size Mscan) (Zlength scan_wm_pre) (lit_neg_c candidate) ) as
      H_propagation_destination_index.
  bind_fact ( Zlength scan_caps_pre = Zlength scan_wm_pre ) as H_Zlength.
  bind_fact ( Zlength scan_caps_post = Zlength scan_wm_post ) as H_Zlength_2.
  pose proof wlists_rep_from_split_at__clause_new as Hdecompose.
  unfold wlists_source_hole_handle, wlists_destination_handle.
  subst destination.
  unfold propagation_destination_index in H_propagation_destination_index.
  destruct H_propagation_destination_index as [Hhole [Htarget Hdistinct]].
  unfold wlists_split_except_two, wlists_split_target_words,
    wlists_split_target_cap.
  destruct (Z.ltb (lit_neg_c candidate) (Zlength scan_wm_pre))
    eqn:Hside.
  - apply Z.ltb_lt in Hside.
    assert (Hpre_split := list_Znth_split nil scan_wm_pre
      (lit_neg_c candidate) ltac:(lia)).
    assert (Hcap_split := list_Znth_split 1 scan_caps_pre
      (lit_neg_c candidate) ltac:(rewrite H_Zlength; lia)).
    rewrite Hpre_split, Hcap_split at 1.
    sep_apply (Hdecompose wlists_entry 0
      (sublist 0 (lit_neg_c candidate) scan_wm_pre)
      (Znth (lit_neg_c candidate) scan_wm_pre nil)
      (sublist (lit_neg_c candidate + 1) (Zlength scan_wm_pre)
        scan_wm_pre)
      (sublist 0 (lit_neg_c candidate) scan_caps_pre)
      (Znth (lit_neg_c candidate) scan_caps_pre 1)
      (sublist (lit_neg_c candidate + 1) (Zlength scan_caps_pre)
        scan_caps_pre)
      ltac:(rewrite !Zlength_sublist by (rewrite ?H_Zlength; lia); lia)).
    rewrite !Zlength_sublist by (rewrite ?H_Zlength; lia).
    rewrite H_Zlength.
    replace (0 + (lit_neg_c candidate - 0)) with (lit_neg_c candidate)
      by lia.
    replace (0 + (lit_neg_c candidate - 0) + 1) with
      (lit_neg_c candidate + 1) by lia.
    entailer_with ltac:(lia).
  - apply Z.ltb_ge in Hside.
    assert (Hstrict : Zlength scan_wm_pre < lit_neg_c candidate) by lia.
    set (k := lit_neg_c candidate - Zlength scan_wm_pre - 1).
    assert (Hkrange : 0 <= k < Zlength scan_wm_post).
    { subst k. lia. }
    assert (Hcaprange : 0 <= k < Zlength scan_caps_post).
    { rewrite H_Zlength_2. exact Hkrange. }
    assert (Hpost_split := list_Znth_split nil scan_wm_post k Hkrange).
    assert (Hcap_split := list_Znth_split 1 scan_caps_post k Hcaprange).
    rewrite Hpost_split, Hcap_split at 1.
    sep_apply (Hdecompose wlists_entry (Zlength scan_wm_pre + 1)
      (sublist 0 k scan_wm_post) (Znth k scan_wm_post nil)
      (sublist (k + 1) (Zlength scan_wm_post) scan_wm_post)
      (sublist 0 k scan_caps_post) (Znth k scan_caps_post 1)
      (sublist (k + 1) (Zlength scan_caps_post) scan_caps_post)
      ltac:(rewrite !Zlength_sublist by (rewrite ?H_Zlength_2; lia); lia)).
    subst k. rewrite !Zlength_sublist by (rewrite ?H_Zlength_2; lia).
    replace (lit_neg_c candidate - Zlength scan_wm_pre - 1 + 1) with
      (lit_neg_c candidate - Zlength scan_wm_pre) by lia.
    replace (Zlength scan_wm_pre + 1 +
      (lit_neg_c candidate - Zlength scan_wm_pre - 1 - 0)) with
      (lit_neg_c candidate) by lia.
    replace (Zlength scan_wm_pre + 1 +
      (lit_neg_c candidate - Zlength scan_wm_pre - 1 - 0) + 1) with
      (lit_neg_c candidate + 1) by lia.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_46 : solver_propagate_which_implies_wit_46.
Proof.
  Unfold.
  left. intros.
  unfold wlists_destination_handle.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_47 : solver_propagate_which_implies_wit_47.
Proof.
  Unfold.
  right. intros.
    bind_fact ( vector_capacity_exhausted (Zlength (wlists_split_target_words (Zlength scan_wm_pre)
      (lit_neg_c candidate) scan_wm_pre scan_wm_post))
      (wlists_split_target_cap (Zlength scan_wm_pre) (lit_neg_c candidate) scan_caps_pre scan_caps_post) ) as
      H_vector_capacity_exhausted.
  unfold vector_capacity_exhausted, minisat_max_growable_cap in H_vector_capacity_exhausted.
  entailer_with ltac:(lia); lia.
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_49 : solver_propagate_which_implies_wit_49.
Proof.
  Unfold.
  left. intros.
  bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth.
  bind_fact ( Zlength candidate_post_memory = Zlength source_words ) as H_Zlength.
  assert (Heq : jj = ii) by lia. subst jj.
  unfold propagation_ptr_segment.
  prop_apply (PtrArray.seg_Zlength begin 0 ii
    (sublist 0 ii candidate_post_memory)). Intros.
  prop_apply (PtrArray.seg_Zlength begin (ii + 1)
    (Zlength source_words)
    (sublist (ii + 1) (Zlength source_words) candidate_post_memory)).
  Intros.
  assert (Hii0 : 0 <= ii).
  { pose proof (Zlength_nonneg (sublist 0 ii candidate_post_memory)); lia. }
  assert (Hiin : ii + 1 <= Zlength source_words).
  { pose proof (Zlength_nonneg
      (sublist (ii + 1) (Zlength source_words)
        candidate_post_memory)); lia. }
  sep_apply (PtrArray.seg_single begin ii
    (Znth ii candidate_post_memory 0)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    (sublist 0 ii candidate_post_memory)
    (Znth ii candidate_post_memory 0 :: nil)); [|lia].
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words)
    (sublist 0 ii candidate_post_memory ++
      (Znth ii candidate_post_memory 0 :: nil))
    (sublist (ii + 1) (Zlength source_words)
      candidate_post_memory)); [|lia].
  replace (begin + 0 * ptr_size_Z) with begin by lia.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  rewrite <- H_Zlength.
  rewrite <- app_assoc. simpl.
  rewrite <- (list_Znth_split 0 candidate_post_memory ii) by lia.
  rewrite <- H_Znth.
  rewrite replace_Znth_Znth.
  replace (begin + 0) with begin by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_71 : solver_propagate_which_implies_wit_71.
Proof.
  Unfold.
  left. intros.
  bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth.
  bind_fact ( Zlength candidate_post_memory = Zlength source_words ) as H_Zlength.
  unfold propagation_ptr_segment.
  prop_apply (PtrArray.seg_Zlength begin 0 jj
    (sublist 0 jj candidate_post_memory)). Intros.
  prop_apply (PtrArray.seg_Zlength begin (jj + 1) ii
    (sublist (jj + 1) ii candidate_post_memory)). Intros.
  prop_apply (PtrArray.seg_Zlength begin (ii + 1)
    (Zlength source_words)
    (sublist (ii + 1) (Zlength source_words) candidate_post_memory)).
  Intros.
  assert (Hjj0 : 0 <= jj).
  { pose proof (Zlength_nonneg (sublist 0 jj candidate_post_memory)); lia. }
  assert (Hjjii : jj + 1 <= ii).
  { pose proof (Zlength_nonneg
      (sublist (jj + 1) ii candidate_post_memory)); lia. }
  assert (Hiin : ii + 1 <= Zlength source_words).
  { pose proof (Zlength_nonneg
      (sublist (ii + 1) (Zlength source_words)
        candidate_post_memory)); lia. }
  sep_apply (PtrArray.seg_single begin jj scan_current).
  sep_apply (PtrArray.seg_single begin ii scan_current).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 jj (jj + 1)
    (sublist 0 jj candidate_post_memory)
    (scan_current :: nil)); [|lia].
  sep_apply (PtrArray.seg_merge_to_seg begin 0 (jj + 1) ii
    (sublist 0 jj candidate_post_memory ++ (scan_current :: nil))
    (sublist (jj + 1) ii candidate_post_memory)); [|lia].
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    ((sublist 0 jj candidate_post_memory ++ (scan_current :: nil)) ++
      sublist (jj + 1) ii candidate_post_memory)
    (scan_current :: nil)); [|lia].
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words)
    (((sublist 0 jj candidate_post_memory ++ (scan_current :: nil)) ++
      sublist (jj + 1) ii candidate_post_memory) ++
      (scan_current :: nil))
    (sublist (ii + 1) (Zlength source_words)
      candidate_post_memory)); [|lia].
  replace (begin + 0 * ptr_size_Z) with begin by lia.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  rewrite <- H_Zlength.
  assert (Hsuffix_len : Zlength
      (sublist (jj + 1) (Zlength candidate_post_memory)
        candidate_post_memory) =
      Zlength candidate_post_memory - (jj + 1)).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hsuffix_range :
      0 <= ii - jj - 1 <
        Zlength (sublist (jj + 1) (Zlength candidate_post_memory)
          candidate_post_memory)).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hsuffix := list_Znth_split 0
    (sublist (jj + 1) (Zlength candidate_post_memory)
      candidate_post_memory) (ii - jj - 1) Hsuffix_range).
  rewrite (replace_Znth_split 0 scan_current jj candidate_post_memory)
    by lia.
  rewrite Hsuffix.
  rewrite Hsuffix_len.
  rewrite !Zsublist_Zsublist by lia.
  rewrite Znth_sublist by lia.
  replace (ii - jj - 1 + (jj + 1)) with ii by lia.
  replace (ii - jj - 1 + 1 + (jj + 1)) with (ii + 1) by lia.
  replace (Zlength candidate_post_memory - (jj + 1) + (jj + 1)) with
    (Zlength candidate_post_memory) by lia.
  rewrite H_Znth.
  simpl. rewrite <- !app_assoc.
  replace (begin + 0) with begin by lia.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_which_implies_wit_50 : solver_propagate_which_implies_wit_50.
Proof.
 exact proof_of_solver_propagate_which_implies_wit_71.
Qed.

(* ===== solver_reducedb entail wits (3 proofs) ===== *)
Lemma proof_of_solver_reducedb_entail_wit_5_2 : solver_reducedb_entail_wit_5_2.
Proof.
  msat_reducedb_compaction_step_close_p4 i j words Mcur.
Qed.

Lemma proof_of_solver_reducedb_entail_wit_5_3 : solver_reducedb_entail_wit_5_3.
Proof.
  msat_reducedb_compaction_step_close_p4 i j words Mcur.
Qed.

Lemma proof_of_solver_reducedb_entail_wit_5_4 : solver_reducedb_entail_wit_5_4.
Proof.
  msat_reducedb_compaction_step_close_p4 i j words Mcur.
Qed.

(* ===== solver_reducedb partial_solve wits ===== *)


Lemma proof_of_solver_reducedb_partial_solve_wit_7_pure : solver_reducedb_partial_solve_wit_7_pure.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( retval = Zlength (db_words (ms_learnt M0)) ) as H_retval.
  bind_fact ( msolver_inv n F A_arr A_inst M0 ) as H_msolver_inv.
  entailer_with ltac:(lia).
  - apply MSatFloatFacts.fp32_count_limit_of_div.
    + split; lia.
    + exact (msi_cla_inc_nonnegative H_msolver_inv).
  - rewrite H_retval.
    apply MSatFloatFacts.fp32_count_limit_of_div.
    + split; lia.
    + exact (msi_cla_inc_nonnegative H_msolver_inv).
Qed.

Lemma proof_of_solver_reducedb_partial_solve_wit_9_pure : solver_reducedb_partial_solve_wit_9_pure.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( i < retval ÷ 2 ) as H_i.
  unfold vecp_rep_at.
  entailer_with lia;
  (* The RHS keeps both `i < retval` and `i < Zlength words` as separate goals; `retval` is the
     halved header word, so proving `i < retval` once through `Z.quot_le_upper_bound`
     discharges both spellings. *)
  assert (Hlt : i < retval) by
    (apply (Z.lt_le_trans _ (Z.quot retval 2) _);
     [ exact H_i | apply Z.quot_le_upper_bound; lia ]);
  lia.
Qed.

Lemma proof_of_solver_reducedb_partial_solve_wit_11_pure : solver_reducedb_partial_solve_wit_11_pure.
Proof.
  msat_reducedb_hdr_word_range_pure.
Qed.

Lemma proof_of_solver_reducedb_partial_solve_wit_15_pure : solver_reducedb_partial_solve_wit_15_pure.
Proof.
  msat_reducedb_first_lit_bounds_pure.
Qed.

(* ===== solver_reducedb return wits (1 proofs) ===== *)
Lemma proof_of_solver_reducedb_return_wit_1 : solver_reducedb_return_wit_1.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( Zlength (sublist 0 j words) = j ) as H_Zlength.
  bind_fact ( msolver_inv n F A_arr A_inst Mcur ) as H_msolver_inv.
  bind_fact ( db_compaction_inv Mcur words i j ) as H_db_compaction_inv.
  unfold solver_reducedb_post_at.
  Exists Mcur.
  entailer_with ltac:(lia).
  unfold solver_rep_levels_wl_at.
  unfold solver_db_mutation_frame_at.
  Intros act asg opos trl tgs.
  Exists act asg opos reasons_ptr trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  entailer_with ltac:(lia).
- unfold db_compaction_inv in H_db_compaction_inv.
  destruct H_db_compaction_inv as [_ [_ [_ Hwords]]].
  assert (Hi : i = Zlength words) by lia.
  rewrite Hi in Hwords.
  rewrite (Zsublist_nil words (Zlength words) (Zlength words) ltac:(lia)) in Hwords.
  simpl in Hwords.
  unfold solver_scalars_rep, solver_fp_rep, solver_vecs_rep.
  rewrite Hwords.
  rewrite app_nil_r.
  rewrite H_Zlength.
  unfold clause_new_scalars_frame, clause_new_vecs_frame.
  cancel.
  unfold vecp_rep at 3.
  Exists learnts.
  unfold vecp_rep_at.
  entailer_with ltac:(lia).
  unfold vecp_size_addr, vecp_cap_addr, vecp_ptr_addr.
  rewrite H_Zlength.
  cancel.
  assert (Hsize :
    &( s_pre # "solver_t" ->ₛ "learnts" .ₛ "size") =
    &(&( s_pre # "solver_t" ->ₛ "learnts") ->ₛ "size"))
    by (csimpl; reflexivity).
  assert (Hcap :
    &( s_pre # "solver_t" ->ₛ "learnts" .ₛ "cap") =
    &(&( s_pre # "solver_t" ->ₛ "learnts") ->ₛ "cap"))
    by (csimpl; reflexivity).
  assert (Hptr :
    &( s_pre # "solver_t" ->ₛ "learnts" .ₛ "ptr") =
    &(&( s_pre # "solver_t" ->ₛ "learnts") ->ₛ "ptr"))
    by (csimpl; reflexivity).
  rewrite Hsize, Hcap, Hptr.
  rewrite (msat_nested_field_addr_alias s_pre "solver_t" "learnts" "vecp_t" "size" _ eq_refl),
          (msat_nested_field_addr_alias s_pre "solver_t" "learnts" "vecp_t" "cap" _ eq_refl),
          (msat_nested_field_addr_alias s_pre "solver_t" "learnts" "vecp_t" "ptr" _ eq_refl).
  cancel.
- exact (msi_shape H_msolver_inv).
Qed.

(* ===== solver_search entail wits (12 proofs) ===== *)
Lemma proof_of_solver_search_entail_wit_10_1 : solver_search_entail_wit_10_1.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_2 : solver_search_entail_wit_10_2.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_3 : solver_search_entail_wit_10_3.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_4 : solver_search_entail_wit_10_4.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_5 : solver_search_entail_wit_10_5.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_6 : solver_search_entail_wit_10_6.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_7 : solver_search_entail_wit_10_7.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_8 : solver_search_entail_wit_10_8.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_9 : solver_search_entail_wit_10_9.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_10 : solver_search_entail_wit_10_10.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_11 : solver_search_entail_wit_10_11.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

Lemma proof_of_solver_search_entail_wit_10_12 : solver_search_entail_wit_10_12.
Proof.
  msat_search_decision_loop_close_p4 learnt_words learnt_cap.
Qed.

(* ===== solver_search which_implies wits (10 proofs) ===== *)
Lemma proof_of_solver_search_which_implies_wit_17 : solver_search_which_implies_wit_17.
Proof.
  Unfold.
  right. intros.
  bind_fact ( analysis_cancel_ready n F A_arr (PropagationStable A_inst) Manalyzed focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_backjump_cert n Manalyzed words blevel ) as H_analyze_backjump_cert.
  unfold solver_rep_levels_wl_at at 1.
  Intros act asg opos rsn trl tgs.
  pose proof H_analysis_cancel_ready as Hready.
  unfold analysis_cancel_ready in Hready.
  destruct Hready as
    [Mbase [Hcancel [Hequiv [Hheap [Hcovers [Hcurrent [Hfocus Hcla]]]]]]].
  destruct Hcancel as
    [Hweak [Hprop [Hfocuswf [Hprocessed [Hlevel
      [Hfront [Hheapbase [Hcovbase Hreason]]]]]]]].
  destruct Hweak as [_ Hinv].
  assert (Esize : ms_size Manalyzed = ms_size Mbase).
  { unfold analysis_core_equiv in Hequiv. tauto. }
  assert (Ecore : ms_core Manalyzed = ms_core Mbase).
  { unfold analysis_core_equiv in Hequiv. tauto. }
  assert (Eroot : ms_root_level Manalyzed = ms_root_level Mbase).
  { unfold analysis_core_equiv in Hequiv. tauto. }
  assert (Hwf : mtrail_wf (ms_size Manalyzed) (ms_core Manalyzed)).
  { rewrite Esize, Ecore, <- (msw_size Hinv).
    exact (msw_trail_wf Hinv). }
  assert (Hprop_cur : prop_level (ms_core Manalyzed)).
  { rewrite Ecore. exact Hprop. }
  assert (Hsize : ms_size Manalyzed = n).
  { rewrite Esize. symmetry. exact (msw_size Hinv). }
  assert (Hheap_cur : heap_wf (ms_size Manalyzed) (msolver_heap Manalyzed)).
  { rewrite Hsize. exact Hheap. }
  destruct H_analyze_backjump_cert as
    [Hwords [Hbeq [Hrootle [Hblevel [Hfocuslevel Htail]]]]].
  assert (Hrootnonneg : 0 <= ms_root_level Manalyzed).
  { rewrite Eroot. exact (proj1 (msw_root_range Hinv)). }
  assert (Hblevel_range :
      0 <= blevel < Zlength (mt_lim (ms_core Manalyzed))).
  { lia. }
  assert (Hbound :
      Znth blevel (mt_lim (ms_core Manalyzed)) 0 <=
        mt_qhead (ms_core Manalyzed)).
  { eapply Forall_Znth_elim; [exact Hprop_cur|exact Hblevel_range]. }
  assert (Hcancelbound : cancel_bound_ready Manalyzed blevel).
  { right. exact Hbound. }
  unfold solver_cancel_pre, solver_cancel_owned.
  Exists act asg opos rsn trl tgs.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_18 : solver_search_which_implies_wit_18.
Proof.
  Unfold.
  right. intros.
  bind_fact ( analysis_cancel_ready n F A_arr (PropagationStable A_inst) Manalyzed focus ) as H_analysis_cancel_ready.
  bind_fact ( analyze_clause_cert n F Manalyzed words ) as H_analyze_clause_cert.
  bind_fact ( analyze_backjump_cert n Manalyzed words blevel ) as H_analyze_backjump_cert.
  bind_fact ( msolver_seed_shadow Manalyzed ) as H_msolver_seed_shadow.
  bind_fact ( ms_model Manalyzed = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Manalyzed) ) as H_msat_fp32_positive_finite.
  bind_fact ( ms_model Mcur = nil ) as H_ms_model_2.
  bind_fact ( msat_fp32_same (ms_cla_decay Manalyzed) (ms_cla_decay Mcur) ) as H_msat_fp32_same.
  unfold solver_cancel_post.
  Split.
  - Intros.
    destruct H_analyze_backjump_cert as [Hlen [Hleveldef [Hrootle [Hlevel Hrest]]]].
    entailer_with ltac:(lia).
  - Intros orderpos order order_cap.
    destruct H as (Hlevel & Hcap & Hheap & Hincl & Hreinserted).
    set (Mback := msolver_cancel_project Manalyzed blevel
      orderpos order order_cap (ms_root_level Manalyzed)).
    Exists Mback.
    split_pure_spatial.
    + unfold Mback.
      sep_apply (solver_cancel_project_join_rep_levels_at s Manalyzed levels
        blevel orderpos order order_cap (ms_root_level Manalyzed) search_wl).
      entailer_with ltac:(lia).
    + unfold solver_cancel_owned.
      Intros act asg opos rsn trl tgs.
      bind_fact (solver_shape Mback) as Hshape_back.
      pose proof H_analysis_cancel_ready as Hreadycopy.
      destruct Hreadycopy as [Morigin [Hcancel0 [Hequiv Hreadyrest]]].
      destruct Hcancel0 as [[Hpending0 Hweak0] Hcancelrest].
      destruct Hreadyrest as [Hheap_cur Hreadyrest].
      assert (Hsize_cur : n = ms_size Manalyzed).
      { pose proof Hequiv as Hequiv_size.
        unfold analysis_core_equiv in Hequiv_size.
        destruct Hequiv_size as [Esize _].
        rewrite Esize. exact (msw_size Hweak0). }
      assert (Horderpos_cur :
          Zlength (ms_orderpos Manalyzed) = ms_size Manalyzed).
      { pose proof (proj1 Hheap_cur) as Horderpos_n.
        unfold msolver_heap in Horderpos_n; simpl in Horderpos_n.
        rewrite Horderpos_n. exact Hsize_cur. }
      assert (Hshape_cur : solver_shape Manalyzed).
      { eapply solver_shape_before_cancel_project__search
          with (M0 := Morigin) (level := blevel) (orderpos := orderpos)
            (order := order) (order_cap := order_cap)
            (root := ms_root_level Manalyzed).
        - exact Hequiv.
        - exact (msw_shape Hweak0).
        - exact Horderpos_cur.
        - exact Hshape_back. }
      assert (Hweak_cur : msolver_inv_weak n F A_arr A_inst Manalyzed).
      { eapply analysis_cancel_ready_weak__search; eauto. }
      destruct (analysis_cancel_ready_cancel_facts__search
        n F A_arr A_inst Manalyzed focus H_analysis_cancel_ready) as
        [Hpending [Hprop [Hfocuswf [Hfocuslevel
          [Hfront [Hcovers Hreasonless]]]]]].
      destruct H_analyze_backjump_cert as
        [Hlen [Hleveldef [Hrootle [Hblevel [Hheadlevel Htaillevels]]]]].
      assert (Hweak_back : msolver_inv_weak n F A_arr A_inst Mback).
      { unfold Mback.
        eapply msolver_inv_weak_cancel_below__search;
          eauto. }
      assert (Htrail : mtrail_wf n (ms_core Manalyzed)).
      { exact (msw_trail_wf Hweak_cur). }
      assert (Hprop_back : prop_level (ms_core Mback)).
      { unfold Mback. eapply prop_level_cancel; eauto. }
      assert (Hwatch_back : minisat_watch_frontier n (msolver_db Mback)
          (mt_assigns (ms_core Mback)) (mt_trail (ms_core Mback))
          (mt_qhead (ms_core Mback))).
      { unfold Mback. simpl.
        eapply minisat_watch_frontier_cancel_current_level; eauto. }
      assert (Hbound : Znth blevel (mt_lim (ms_core Manalyzed)) 0 <=
          mt_qhead (ms_core Manalyzed)).
      { eapply Forall_Znth_elim; [exact Hprop|lia]. }
      assert (Hheap_back : heap_covers n (msolver_heap Mback)
          (mt_assigns (ms_core Mback)) (mt_trail (ms_core Mback))
          (mt_qhead (ms_core Mback))).
      { unfold Mback. simpl.
        eapply heap_covers_cancel_project__canceluntil_cap; eauto.
        rewrite <- Hsize_cur in Hheap. exact Hheap. }
      assert (Hreasonless_back : current_reasonless_earliest n Mback).
      { unfold Mback.
        eapply current_reasonless_cancel_project__search;
          eauto. }
      assert (Hinv_back : msolver_inv n F A_arr A_inst Mback).
      { constructor; assumption. }
      assert (Hrecord : record_ready_cert n F Mback words).
      { unfold Mback.
        eapply record_ready_cert_cancel_project__search
          with (A_inst := A_inst) (focus := focus).
        - exact Hweak_cur.
        - exact H_analysis_cancel_ready.
        - exact H_analyze_clause_cert.
        - repeat split; assumption.
        - reflexivity. }
      assert (Hqtail : mt_qhead (ms_core Mback) = ms_qtail Mback).
      { unfold Mback, msolver_cancel_project, msolver_core_heap_update.
        simpl. reflexivity. }
      assert (Hpending_back :
          ms_capacity_root_propagation_pending Mback = 0).
      { unfold Mback, msolver_cancel_project, msolver_core_heap_update.
        simpl. exact Hpending. }
      assert (Hseed_back : msolver_seed_shadow Mback).
      { unfold Mback, msolver_seed_shadow, msolver_cancel_project,
          msolver_core_heap_update in *; simpl in *; exact H_msolver_seed_shadow. }
      assert (Hmodel_back : ms_model Mback = ms_model Mcur).
      { unfold Mback, msolver_cancel_project, msolver_core_heap_update.
        simpl. rewrite H_ms_model, H_ms_model_2. reflexivity. }
      assert (Hdecay_back :
          msat_fp32_positive_finite (ms_cla_decay Mback)).
      { unfold Mback, msolver_cancel_project, msolver_core_heap_update.
        simpl. exact H_msat_fp32_positive_finite. }
      assert (Hdecay_eq : ms_cla_decay Mback = ms_cla_decay Mcur).
      { unfold Mback, msolver_cancel_project, msolver_core_heap_update.
        simpl. unfold msat_fp32_same in H_msat_fp32_same. exact H_msat_fp32_same. }
      assert (Hpositive : record_watch1_positive Mback words).
      { unfold Mback. apply record_watch1_positive_cancel__record.
        apply (learned_tail_positive_watch1__record n Manalyzed words Htrail).
        exact (proj2 (proj2 H_analyze_clause_cert)). }
      lazymatch goal with
      | Hreuse : solver_search_reuse ?entry Manalyzed |- _ =>
          assert (Hreuse_back : solver_search_reuse entry Mback)
            by (intro Hbase; unfold Mback;
                exact (minisat_base_completion_cancel__api_reentry
                  n Manalyzed blevel orderpos order order_cap
                  (ms_root_level Manalyzed) Htrail (msw_db_wf Hweak_cur)
                  Hlevel Hbound (Hreuse Hbase)))
      end.
      assert (Hbackjump :
          solver_search_backjump_ready n F A_arr A_inst Mcur Mback words).
      { unfold solver_search_backjump_ready, record_clause_cert.
        exact (conj Hinv_back (conj Hrecord (conj Hpositive
          (conj Hqtail (conj Hpending_back (conj Hseed_back
            (conj Hmodel_back (conj Hdecay_back Hdecay_eq)))))))). }
      msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_19 : solver_search_which_implies_wit_19.
Proof.
  Unfold.
  right. intros.
  bind_fact ( solver_search_backjump_ready n F A_arr A_inst Mcur Mback words ) as H_solver_search_backjump_ready.
  unfold solver_search_backjump_ready in H_solver_search_backjump_ready.
  destruct H_solver_search_backjump_ready as
    [Hinv [Hrecord [Hpositive [Hqtail [Hpending [Hseed [Hmodel [Hdecay Hdecay_eq]]]]]]]].
  unfold solver_record_pre_at, veci_rep.
  Intros learnt_ptr.
  Exists learnt_ptr.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_20 : solver_search_which_implies_wit_20.
Proof.
  Unfold.
  right. intros.
  bind_fact ( ms_model Mback = nil ) as H_ms_model.
  unfold solver_record_post_at.
  Split.
  - Intros Mrecord.
    entailer_with ltac:(lia).
  - Intros Mrecord_cap.
    match goal with
    | Hpost : solver_internal_capacity_ready n F A_arr A_inst Mrecord_cap /\ _ |- _ =>
        destruct Hpost as (Hready & Hmodel & Hcap & Hreuse)
    end.
    assert (Hmodel_nil : ms_model Mrecord_cap = (@nil Z))
      by (rewrite Hmodel; exact H_ms_model).
    bind_fact (record_watch1_positive Mback words) as Hpositive.
    lazymatch goal with
    | Hentry : solver_search_reuse ?entry Mback |- _ =>
        assert (Hreuse_out : solver_search_reuse entry Mrecord_cap)
          by (intro Hbase; apply Hreuse; split;
              [exact (Hentry Hbase)|exact Hpositive])
    end.
    Exists Mrecord_cap.
    msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_search_which_implies_wit_21 : solver_search_which_implies_wit_21.
Proof.
  Unfold.
  right. intros.
  bind_fact ( ms_model Mback = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mback) ) as H_msat_fp32_positive_finite.
  unfold solver_record_post_at.
  Split.
  - Intros Mrecord.
    match goal with
    | Hpost : msolver_inv n F A_arr A_inst Mrecord /\ _ |- _ =>
        destruct Hpost as (Hinv & Hpending & Hseed & Hmodel & Hdecay & Hcap & Hreuse)
    end.
    assert (Hmodel_nil : ms_model Mrecord = (@nil Z))
      by (rewrite Hmodel; exact H_ms_model).
    assert (Hdecay_pos : msat_fp32_positive_finite (ms_cla_decay Mrecord))
      by (rewrite Hdecay; exact H_msat_fp32_positive_finite).
    bind_fact (record_watch1_positive Mback words) as Hpositive.
    lazymatch goal with
    | Hentry : solver_search_reuse ?entry Mback |- _ =>
        assert (Hreuse_out : solver_search_reuse entry Mrecord)
          by (intro Hbase; apply Hreuse; split;
              [exact (Hentry Hbase)|exact Hpositive])
    end.
    Exists Mrecord.
    entailer_with ltac:(int_auto).
  - Intros Mrecord_cap.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_22 : solver_search_which_implies_wit_22.
Proof.
  Unfold.
  right. intros.
  unfold solver_rep_levels_wl_at, solver_cancel_owned,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_search_decay_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_fp_rep,
    solver_fp_without_decay_incs_rep.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  msat_manual_entailer_with ltac:(assumption).
Qed.

Lemma proof_of_solver_search_which_implies_wit_23 : solver_search_which_implies_wit_23.
Proof.
  Unfold.
  right. intros.
  bind_fact ( msolver_inv n F A_arr A_inst Mrecord ) as H_msolver_inv.
  bind_fact ( ms_capacity_root_propagation_pending Mrecord = 0 ) as H_ms_capacity_root_propagation_pending.
  unfold solver_search_loop.
  pose (Mnew := msolver_runtime_update Mrecord (ms_model Mrecord) var_inc_now var_decay_now
    cla_inc_now cla_decay_now (ms_progress Mrecord) (ms_stats Mrecord)).
  assert (Hweak : msolver_inv_weak n F A_arr A_inst Mnew).
  { destruct (msi_weak H_msolver_inv). constructor; assumption. }
  assert (Hinv : msolver_inv n F A_arr A_inst Mnew).
  { constructor.
    - exact Hweak.
    - exact (msi_prop_level H_msolver_inv).
    - exact (msi_watch_frontier H_msolver_inv).
    - exact (msi_heap_covers H_msolver_inv).
    - exact (msi_reasonless_current H_msolver_inv). }
  assert (Hprop :
    solver_propagation_inv n F A_arr (PropagationStable A_inst) Mnew).
  { split; [exact H_ms_capacity_root_propagation_pending|].
    apply msolver_inv_propagation_of_strong. exact Hinv. }
  lazymatch goal with
  | Hentry : solver_search_reuse ?entry Mrecord |- _ =>
      assert (Hreuse_new : solver_search_reuse entry Mnew)
        by (change (solver_search_reuse entry Mrecord); exact Hentry)
  end.
  Exists Mnew. Exists words. Exists cap_after.
  unfold solver_search_decay_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_fp_without_decay_incs_rep,
    solver_rep_levels_wl_at, solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep,
    solver_trail_array_rep, solver_levels_slice_at.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  unfold Mnew, msolver_runtime_update. cbn [ms_size ms_cap ms_qtail ms_capacity_pending_qhead
    ms_capacity_root_propagation_pending ms_core ms_root_level
    ms_reason_words ms_reason_of ms_prob ms_learnt ms_prob_cap
    ms_learnt_cap ms_binary ms_binary_lits ms_wm ms_wcaps ms_activity
    ms_orderpos ms_order ms_order_cap ms_lim_cap ms_model ms_model_cap
    ms_tags ms_tagged ms_tagged_cap ms_stack ms_stack_cap ms_var_inc
    ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed ms_progress
    ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats].
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_24 : solver_search_which_implies_wit_24.
Proof.
  Unfold.
  right. intros.
  bind_fact ( ms_model Mcur = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mcur) ) as H_msat_fp32_positive_finite.
  unfold solver_propagate_post.
  Split.
  - Split.
    + Intros Mstable.
      match goal with
      | Hx : solver_propagation_inv _ _ _ _ Mstable /\ _ |- _ =>
          destruct Hx as [Hprop [Hcaller [Hreuse [Hseed Hdrain]]]]
      end.
      assert (Hinv : msolver_inv n F A_arr A_inst Mstable).
      { eapply solver_propagation_drained_strong.
        - exact Hprop.
        - exact Hdrain. }
      unfold solver_propagation_inv in Hprop.
      destruct Hprop as [Hpending Hprop_inv].
      destruct Hcaller as [_ [_ [Hmodel_eq [Hdecay_eq Hcap]]]].
      lazymatch goal with
      | Hentry : solver_search_reuse ?entry Mcur |- _ =>
          assert (Hreuse_stable : solver_search_reuse entry Mstable)
            by (intro Hbase; exact (proj1 Hreuse (Hentry Hbase)))
      end.
      assert (Hmodel : ms_model Mstable = (@nil Z)).
      { rewrite Hmodel_eq. exact H_ms_model. }
      assert (Hdecay :
          msat_fp32_positive_finite (ms_cla_decay Mstable)).
      { rewrite Hdecay_eq. exact H_msat_fp32_positive_finite. }
      Exists Mstable.
      entailer_with ltac:(lia).
    + Intros Mconflict p focus C.
      entailer_with ltac:(lia).
  - Intros.
    msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_search_which_implies_wit_26 : solver_search_which_implies_wit_26.
Proof.
  Unfold.
  right. intros.
  bind_fact ( msolver_inv n F A_arr A_inst Mstable ) as H_msolver_inv.
  bind_fact ( mt_qhead (ms_core Mstable) = ms_qtail Mstable ) as H_mt_qhead.
  bind_fact ( ms_capacity_root_propagation_pending Mstable = 0 ) as H_ms_capacity_root_propagation_pending.
  bind_fact ( msolver_seed_shadow Mstable ) as H_msolver_seed_shadow.
  bind_fact ( ms_model Mstable = nil ) as H_ms_model.
  bind_fact ( msat_fp32_positive_finite (ms_cla_decay Mstable) ) as H_msat_fp32_positive_finite.
  pose (Mnew := msolver_runtime_update Mstable (ms_model Mstable) (ms_var_inc Mstable) (ms_var_decay Mstable)
    (ms_cla_inc Mstable) (ms_cla_decay Mstable) progress_now (ms_stats Mstable)).

  assert (Hweak : msolver_inv_weak n F A_arr A_inst Mnew).
  { destruct (msi_weak H_msolver_inv). constructor; assumption. }
  assert (Hinv : msolver_inv n F A_arr A_inst Mnew).
  { constructor.
    - exact Hweak.
    - exact (msi_prop_level H_msolver_inv).
    - exact (msi_watch_frontier H_msolver_inv).
    - exact (msi_heap_covers H_msolver_inv).
    - exact (msi_reasonless_current H_msolver_inv). }
  lazymatch goal with
  | Hentry : solver_search_reuse ?entry Mstable |- _ =>
      assert (Hreuse_new : solver_search_reuse entry Mnew)
        by (change (solver_search_reuse entry Mstable); exact Hentry)
  end.
  Exists Mnew.
  unfold solver_search_progress_frame_at,
    solver_rep_assigns_levels_at, solver_rep_at,
    solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    clause_new_scalars_frame, solver_scalars_rep,
    solver_fp_rep, solver_fp_without_progress_rep, solver_vecs_rep,
    solver_trail_array_rep.
  Intros act opos rsn trl tgs.
  Exists act opos rsn trl tgs.
  unfold Mnew, msolver_runtime_update. cbn [ms_size ms_cap ms_qtail ms_capacity_pending_qhead
    ms_capacity_root_propagation_pending ms_core ms_root_level
    ms_reason_words ms_reason_of ms_prob ms_learnt ms_prob_cap
    ms_learnt_cap ms_binary ms_binary_lits ms_wm ms_wcaps ms_activity
    ms_orderpos ms_order ms_order_cap ms_lim_cap ms_model ms_model_cap
    ms_tags ms_tagged ms_tagged_cap ms_stack ms_stack_cap ms_var_inc
    ms_var_decay ms_cla_inc ms_cla_decay ms_random_seed ms_progress
    ms_simpdb_assigns ms_simpdb_props ms_verbosity ms_stats].
  repeat lazymatch goal with
  | |- _ |-- _ && _ => apply _derivable1_andp_intros
  end;
  lazymatch goal with
  | |- _ |-- “ _ ” =>
      apply dump_spatial_left;
      solve
        [ lia | exact Hreuse_new | exact Hinv | exact H_mt_qhead
        | exact H_ms_capacity_root_propagation_pending
        | exact H_msolver_seed_shadow | exact H_ms_model
        | exact H_msat_fp32_positive_finite | exact (msi_shape Hinv) ]
  | |- _ |-- _ =>
      msat_cancel_sound; change (emp |-- emp); reflexivity
  end.
Qed.

Lemma proof_of_solver_search_which_implies_wit_28 : solver_search_which_implies_wit_28.
Proof.
  Unfold.
  right. intros.
  bind_fact ( msolver_inv n F A_arr A_inst Mprogress ) as H_msolver_inv.
  bind_fact ( mt_qhead (ms_core Mprogress) = ms_qtail Mprogress ) as H_mt_qhead.
  assert (Hshape : solver_shape Mprogress).
  { exact (msi_shape H_msolver_inv). }
  pose proof (msi_size H_msolver_inv) as Hsize.
  assert (Htrail :
      mtrail_wf (ms_size Mprogress) (ms_core Mprogress)).
  { rewrite <- Hsize. exact (msi_trail_wf H_msolver_inv). }
  assert (Hheap :
      heap_wf (ms_size Mprogress) (msolver_heap Mprogress)).
  { rewrite <- Hsize. exact (msi_heap_wf H_msolver_inv). }
  assert (Hrange :
      0 <= ms_root_level Mprogress <=
        Zlength (mt_lim (ms_core Mprogress))).
  { exact (msi_root_range H_msolver_inv). }
  assert (Htrail_len :
      Zlength (mt_trail (ms_core Mprogress)) = ms_qtail Mprogress).
  { unfold solver_shape in Hshape. tauto. }
  assert (Hcancel :
      cancel_bound_ready Mprogress (ms_root_level Mprogress)).
  { unfold cancel_bound_ready.
    destruct (Z_lt_le_dec (ms_root_level Mprogress)
      (Zlength (mt_lim (ms_core Mprogress)))) as [Hlt | Hge].
    - right.
      pose proof (lim_lt_trail (ms_size Mprogress)
        (ms_core Mprogress) (ms_root_level Mprogress) Htrail
        (conj (proj1 Hrange) Hlt)) as Hlim.
      rewrite Htrail_len in Hlim.
      rewrite <- H_mt_qhead in Hlim.
      lia.
    - left. exact Hge. }
  unfold solver_search_root_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells, solver_cancel_pre, solver_cancel_owned,
    solver_cancel_owned, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep,
    solver_scalars_without_root_rep,
    solver_vecs_rep, solver_vecs_without_lim_rep.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  msat_manual_entailer_with ltac:(first [assumption | lia]).
Qed.

(* ===== solver_solve entail wits (8 proofs) ===== *)
Lemma proof_of_solver_solve_entail_wit_7_3 : solver_solve_entail_wit_7_3.
Proof.
  msat_solve_capacity_arm_close_p4 H Mcap.
Qed.

Lemma proof_of_solver_solve_entail_wit_7_4 : solver_solve_entail_wit_7_4.
Proof.
  msat_solve_capacity_arm_close_p4 H Mcap.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_1 : solver_solve_entail_wit_8_1.
Proof.
  msat_solve_assume_bound_lia_p4.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_2 : solver_solve_entail_wit_8_2.
Proof.
  msat_solve_assume_bound_lia_p4.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_3 : solver_solve_entail_wit_8_3.
Proof.
  msat_solve_assume_bound_lia_p4.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_4 : solver_solve_entail_wit_8_4.
Proof.
  msat_solve_assume_bound_lia_p4.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_5 : solver_solve_entail_wit_8_5.
Proof.
  msat_solve_assumption_advance_close_p4.
Qed.

Lemma proof_of_solver_solve_entail_wit_8_6 : solver_solve_entail_wit_8_6.
Proof.
  msat_solve_assumption_advance_close_p4.
Qed.

(* ===== solver_solve return wits (10 proofs) ===== *)
Lemma proof_of_solver_solve_return_wit_1 : solver_solve_return_wit_1.
Proof.
  Unfold; right; intros.
  unfold solver_unsat_arm_at. Intros. Exists Munsat_2.
  msat_manual_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_solve_return_wit_2 : solver_solve_return_wit_2.
Proof.
  Unfold; right; intros.
  unfold solver_sat_arm_at. Intros.
  assert (Hsaved : ms_size Msat_2 = n_solver_solve_spec /\
    model_saved n_solver_solve_spec F_solver_solve_spec A_arr_solver_solve_spec Msat_2)
    by tauto.
  apply (proj1 (sat_arm_unfolded_iff n_solver_solve_spec F_solver_solve_spec
    A_arr_solver_solve_spec Msat_2)) in Hsaved.
  Exists Msat_2. msat_manual_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_solve_return_wit_3 : solver_solve_return_wit_3.
Proof.
  Unfold; right; intros.
  unfold solver_capacity_arm_at, solver_at_start_or_restart.
  Intros. Exists Mcap. msat_manual_entailer_with ltac:(tauto).
Qed.

Lemma proof_of_solver_solve_return_wit_4 : solver_solve_return_wit_4.
Proof.
  msat_solve_unsat_return_close_p4 Mfalse_unsat.
Qed.

Lemma proof_of_solver_solve_return_wit_5 : solver_solve_return_wit_5.
Proof.
  msat_solve_unsat_return_close_p4 Mfalse_unsat.
Qed.

Lemma proof_of_solver_solve_return_wit_6 : solver_solve_return_wit_6.
Proof.
  msat_solve_unsat_return_close_p4 Mfalse_unsat.
Qed.

Lemma proof_of_solver_solve_return_wit_7 : solver_solve_return_wit_7.
Proof.
  msat_solve_unsat_return_close_p4 Mfalse_unsat.
Qed.

Lemma proof_of_solver_solve_return_wit_8 : solver_solve_return_wit_8.
Proof. exact proof_of_solver_solve_return_wit_3. Qed.

Lemma proof_of_solver_solve_return_wit_13 : solver_solve_return_wit_13.
Proof.
  Unfold. left; intros.
  rename M_solver_solve_spec into M0.
  unfold solver_unsat_arm_at.
  Intros.
  match goal with
  | H : ms_size Mconf = _ /\ _ |- _ =>
      destruct H as (Hsize & Hunsat & Hcap & Hguarded)
  end.
  Exists Mconf.
  entailer_with ltac:(tauto || lia).
Qed.

Lemma proof_of_solver_solve_return_wit_14 : solver_solve_return_wit_14.
Proof. exact proof_of_solver_solve_return_wit_3. Qed.
