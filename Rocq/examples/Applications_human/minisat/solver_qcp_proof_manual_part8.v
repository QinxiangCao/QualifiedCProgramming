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

(* solver_qcp_proof_manual_part8.v -- hand-written proofs of the manual-lane
   verification conditions of the MiniSat port, part 8 of 9.  The nine part
   files partition the manual lane of solver_qcp_goal.v and are mutually
   independent: each one compiles on its own once solver_qcp_lib.vo,
   solver_qcp_goal.vo, solver_qcp_proof_auto.vo and solver_qcp_proof_common.vo
   are built.  Proofs are grouped by the C function whose VCs they discharge,
   in file order, one `===== <family> wits (N proofs) =====` banner per
   family. The families held by this part are clause_remove,
   clause_simplify, order_select, order_unassigned, solver_analyze,
   solver_canceluntil_capacity, solver_prepare_public_capacity_exit,
   solver_propagate, solver_record, solver_reducedb, solver_search,
   solver_simplify and solver_solve. *)

(* ---------- part-local proof tactics ----------
   Each of the tactics below is the shared body of a family of VCs that this
   file discharges the same way; the call sites keep only the arguments that
   actually differ.  They are part-local (suffix [_p8]) because
   solver_qcp_goal_check.v Includes every part into one module, so two parts
   may not define the same tactic name; the cross-part families live in
   solver_qcp_proof_common.v instead.  A hypothesis produced by symexec is
   located by its STATEMENT (a [match goal] shape, the same convention as
   [bind_fact]) rather than by the position symexec emitted it in. *)

(* The spatial arm must close completely. Mixed pure goals may continue in
   the caller, which keeps its entire suffix inside a transactional branch. *)
Ltac msat_frame_entailer_with_p8 tac :=
  let finish_spatial :=
    ltac:(Intros; msat_cancel_sound;
          change (emp |-- emp); reflexivity) in
  first
    [ solve [finish_spatial]
    | split_pure_spatial;
      [ solve [finish_spatial]
      | entailer_with tac ]
    | entailer_with tac ].

(* The literal-bound side conditions of the analyze loop: the reason target is
   well-formed, so its shape disjunct is either a real clause (whose watched
   literal carries the bound) or a tagged one, and the tag equation refutes the
   second arm. *)
Ltac msat_analyze_reason_target_lit_bound_p8 :=
  Unfold; left; intros;
  match goal with
  | Hrtw : reason_target_wf _ _ _ ?cc _,
    Htag : is_tag ?cc = msat_true |- _ =>
      unfold reason_target_wf in Hrtw;
      destruct Hrtw as [_ [_ [_ [_ Hshape]]]];
      destruct Hshape as [[_ [_ Hlit]] | [co [Hnot_tag _]]];
      [ unfold lit_wf_c in Hlit; entailer_with ltac:(lia); lia
      | rewrite Htag in Hnot_tag; discriminate ]
  end.

(* The child-index bounds of the order-heap sift loop.  The variable count and
   the heap-before snapshot come out of the sift invariant; only the heap size
   is not mentioned there, so it is the single argument. *)
Tactic Notation "msat_order_select_sift_child_bound_p8" ident(sz) :=
  Unfold; left; intros;
  match goal with
  | Hs : order_select_sift_inv ?nn _ _ _ _ ?hb _ _ _ _ _ |- _ =>
      msat_order_select_bound_sift_child_index Hs nn sz hb
  end.

(* The watcher-scan `same`/`move` write-back obligations: the goal is that the
   slot just written still reads back the value that was written, which follows
   from the two replace_Znth lemmas once the tagged-memory equation is used. *)
Ltac msat_propagate_scan_replace_same_p8 :=
  pre_process_default; split_pures; dump_pre_spatial; try lia;
  match goal with
  | H : ?tm = replace_Znth _ _ _ |- context [ ?tm ] => rewrite H
  end;
  rewrite replace_Znth_replace_Znth_Same by lia;
  rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia);
  reflexivity.

(* The capacity-exit stack bounds: unfold the trail vector one level and read
   the bound off its own representation predicate. *)
Ltac msat_prepare_capacity_exit_veci_bound_p8 :=
  aggressive_pre_process;
  unfold veci_rep at 1; Intros stack_ptr;
  unfold veci_rep_at at 1; Intros_p Hstack_bounds;
  dump_pre_spatial; lia.

(* The reduce-database loop steps that keep the word array unchanged: hand the
   same words and the same model back. *)
Tactic Notation "msat_reducedb_entail_keep_words_p8" ident(ws) ident(Mnext) :=
  Unfold; left; intros; Exists ws Mnext; entailer_with ltac:(lia).

(* The reduce-database compaction step: the surviving prefix is the word array
   with slot [j] overwritten by slot [i]. *)
Tactic Notation "msat_reducedb_compaction_step_exists_p8"
    ident(jj) ident(ii) ident(ws) ident(Mcur) :=
  Unfold; left; intros;
  Exists (replace_Znth jj (Znth (ii - 0) ws 0) ws) Mcur;
  entailer_with ltac:(lia);
  try (unfold db_compaction_step; repeat split; auto).

(* The length obligations of a binary-clause `keep` transition: both writes are
   in range, so the two replace_Znth lengths collapse to the original one.  The
   opener stays at the call site: [LLM_pre_process] shelves its side goals, and
   a `;` inside this body would not reach them -- the call sites use `all:`. *)
Tactic Notation "msat_propagate_binary_keep_length_p8" ident(tm) :=
  split_pures; try entailer_with lia;
  symmetry; apply Znth_replace_Znth_Same;
  rewrite !Zlength_replace_Znth; subst tm;
  rewrite !Zlength_replace_Znth; lia.

(* The clause_simplify safety checks on the header word: the header is
   non-negative and bounded by INT_MAX, and the retval equation divides it. *)
Ltac msat_clause_simplify_hdr_word_safety_p8 :=
  aggressive_pre_process;
  match goal with
  | Hlim : clause_hdr_word ?isl (Zlength ?cw) <= 2147483647,
    Hrv : ?rv = clause_hdr_word ?isl (Zlength ?cw) ÷ 2 |- _ =>
      dump_pre_spatial;
      assert (Hhdr : 0 <= clause_hdr_word isl (Zlength cw))
        by (apply clause_hdr_word_nonneg; apply Zlength_nonneg);
      rewrite zdiv_equiv in Hrv by lia;
      rewrite clause_hdr_word_div2 in Hrv by apply Zlength_nonneg;
      unfold clause_hdr_word in Hlim;
      destruct isl; lia
  end.

(* The entailment closing a decision literal's enqueue: the shared closer in
   proof_common wants the negated literal, its variable and the model, all of
   which are pinned by the selection-state hypothesis. *)
Ltac msat_search_decision_lit_var_entail_p8 :=
  Unfold; left; intros;
  match goal with
  | H2 : ?r2 = lit_neg_c ?rw,
    H7 : ?rw = ?rv + ?rv,
    He : enqueue_input _ _ _ _ _ _ _,
    Hs : solver_search_selection_state _ _ _ _ ?rv ?Ms |- _ =>
      msat_search_close_decision_lit_var_entail H2 H7 He Hs r2 rv Ms
  end.

(* The pure conjuncts of the same enqueue step, which additionally need the
   trail-limit bound. *)
Ltac msat_search_decision_lit_var_conjuncts_p8 :=
  Unfold; left; intros;
  match goal with
  | H2 : ?r2 = lit_neg_c ?rw,
    H7 : ?rw = ?rv + ?rv,
    HZ : Zlength (mt_lim (ms_core ?Ms)) < _,
    He : enqueue_input _ _ _ _ _ _ _,
    Hs : solver_search_selection_state _ _ _ _ ?rv ?Ms |- _ =>
      msat_search_close_decision_lit_var_conjuncts HZ He Hs r2 rv H2 H7
  end.

(* The decision-variable range obligations: open the twelve-way selection-state
   bundle and take the range conjunct out of it. *)
Ltac msat_search_selection_state_range_p8 :=
  Unfold; left; intros;
  match goal with
  | Hs : solver_search_selection_state _ _ _ _ _ _ |- _ =>
      unfold solver_search_selection_state in Hs;
      destruct Hs as [Hinv Hrest1];
      destruct Hrest1 as [Hlevel Hrest2];
      destruct Hrest2 as [Hwatch Hrest3];
      destruct Hrest3 as [Hreason Hrest4];
      destruct Hrest4 as [Hpending Hrest5];
      destruct Hrest5 as [Hqtail Hrest6];
      destruct Hrest6 as [Hseed Hrest7];
      destruct Hrest7 as [Hmodel Hrest8];
      destruct Hrest8 as [Hfinite Hrest9];
      destruct Hrest9 as [H2n Hrest10];
      destruct Hrest10 as [Hrange Hrest11];
      destruct Hrest11 as [Hnth Hheap];
      destruct Hrange as [Hretval7 Hretval7_lt];
      entailer_with ltac:(lia)
  end.

(* The tagged-word bound at the scan cursor: the slot at [ii] holds the value
   just written, which the enqueue input states is a well-formed literal.  Only
   the cursor is not recoverable from the hypotheses. *)
Tactic Notation "msat_propagate_scan_same_tagged_bound_p8" ident(ii) :=
  Unfold; right; intros;
  match goal with
  | Hq : enqueue_input _ _ _ _ _ _ _,
    Htm : ?tm = replace_Znth _ ?sc _,
    Hst : is_tag ?sc = msat_true,
    Hsp : 0 <= ?sc |- _ =>
      assert (Hii1 : 0 <= ii < Zlength (replace_Znth ii sc tm))
        by (rewrite Zlength_replace_Znth, Htm, Zlength_replace_Znth; lia);
      rewrite (Znth_replace_Znth_Same 0 (replace_Znth ii sc tm) ii sc Hii1);
      assert (Htw : tagged_word sc) by (unfold tagged_word; exact Hst);
      assert (Hnn : 0 <= sc) by exact Hsp;
      destruct Hq as [Hwf [Hn2 _]];
      unfold lit_wf_c in Hwf;
      entailer_with ltac:(lia)
  end.

(* The watch-map index bounds while the scan sits inside the map: the split of
   [ms_wm] gives the length of the two sides, and the solver shape gives the
   length of the whole. *)
Ltac msat_propagate_scan_wm_split_bound_p8 :=
  pre_process_default;
  match goal with
  | Hsh : solver_shape ?Ms,
    Hsp : ms_wm ?Ms = ?pre ++ _ :: ?post |- _ =>
      split_pures; entailer_with ltac:(lia); try lia;
      unfold solver_shape in Hsh;
      assert (Hms : Zlength (ms_wm Ms) = 2 * ms_size Ms) by tauto;
      assert (Hpre : 0 <= Zlength pre) by apply Zlength_nonneg;
      assert (Hpost : 0 <= Zlength post) by apply Zlength_nonneg;
      assert (Hwm : Zlength (ms_wm Ms) = Zlength pre + 1 + Zlength post)
        by (rewrite Hsp; rewrite Zlength_app; rewrite Zlength_cons; lia);
      lia
  end.

(* The replacement candidate's lower bound: the candidate is the clause literal
   at the scan offset, and the scan invariant carries [Forall (lit_wf_c n)] over
   the normalised clause. *)
Ltac msat_propagate_replacement_candidate_p8 :=
  Unfold; right; intros;
  match goal with
  | Hc : ?cand = Znth (?off - 2) (sublist 2 (Zlength ?cc) ?cc) 0,
    Hinv : propagation_replacement_scan_inv ?n _ _ ?nc ?off |- _ =>
      destruct Hinv as [Hk [Hwf [Hfalse [Hlit Htail]]]];
      assert (Hwf_c : lit_wf_c n (Znth off nc 0))
        by (apply (Forall_Znth_elim Z (lit_wf_c n) nc 0 off Hwf);
            unfold propagation_normalized_clause;
            rewrite !Zlength_cons, Zlength_sublist by lia;
            lia);
      unfold propagation_normalized_clause in Hwf_c;
      rewrite !Znth_cons, Znth_sublist in Hwf_c by lia;
      assert (Hcand : 0 <= cand)
        by (rewrite Hc, Znth_sublist by lia;
            replace (off - 2 + 2) with off by lia;
            replace (off - 1 - 1 + 2) with off in Hwf_c by lia;
            exact (proj1 Hwf_c));
      entailer_with ltac:(lia)
  end.

(* The `which_implies` that focuses the clause at the compaction cursor: find
   the word in the learnt-clause suffix, take its clause object out of the
   database, refold the remainder into [clause_db_pair_remainder], and hand the
   caller the clause representation plus its activity cell.  The trailing
   [msat_fp32_count_limit] match covers the variant of this VC that also has to
   return the activity-limit's non-negativity; where that hypothesis is absent
   the [try] makes it a no-op. *)
Ltac msat_reducedb_focus_head_clause_p8 :=
  Unfold; left; intros;
  match goal with
  | Hdc : db_compaction_inv ?Mc ?ws ?i ?j,
    Hmi : msolver_inv ?n _ _ _ ?Mc |- _ =>
      let cco := fresh "co" in
      let cp := fresh "p" in
      let hinl := fresh "Hinlearnt" in
      let hvar := fresh "Hvar" in
      let htwo := fresh "Htwo" in
      let cpre := fresh "pre" in
      let cpost := fresh "post" in
      let hlearnt := fresh "Hlearnt" in
      let act := fresh "activity" in
      ( assert (Hcomp := Hdc);
        destruct Hcomp as [Hj0 [Hji [Hi Hwords]]];
        assert (Hsuffix : In (Znth (i - 0) ws 0)
          (sublist i (Zlength ws) ws))
          by (replace (Znth (i - 0) ws 0) with
                (Znth 0 (sublist i (Zlength ws) ws) 0);
              [ apply Znth_In; rewrite Zlength_sublist by lia; lia
              | symmetry; rewrite Znth_sublist by lia; f_equal; lia ]);
        assert (Hptr : In (Znth (i - 0) ws 0) (map fst (ms_learnt Mc)))
          by (rewrite Hwords; apply in_or_app; right; exact Hsuffix);
        apply in_map_iff in Hptr;
        destruct Hptr as [[cp cco] [Hp hinl]];
        simpl in Hp; subst cp;
        assert (Hin : In (Znth (i - 0) ws 0, cco) (msolver_db Mc))
          by (unfold msolver_db; apply in_or_app; right; exact hinl);
        assert (Hobj : obj_wf n cco)
          by (eapply db_wf_obj; [ exact (msi_db_wf Hmi) | exact Hin ]);
        destruct Hobj as [Hlen [Hwf Hnd]];
        assert (Htag : co_learnt cco = true)
          by (pose proof (msi_learnt_db Hmi) as hlearnt;
              unfold learnt_db in hlearnt;
              rewrite Forall_forall in hlearnt;
              specialize (hlearnt (Znth (i - 0) ws 0, cco) hinl);
              simpl in hlearnt; exact hlearnt);
        assert (Hsize : n = ms_size Mc) by exact (msi_size Hmi);
        assert (Hlit : lit_wf_c n (Znth 0 (co_lits cco) 0))
          by (apply obj_wf_watch0; repeat split; assumption);
        assert (hvar : 0 <= lit_var_c (Znth 0 (co_lits cco) 0) /\
          lit_var_c (Znth 0 (co_lits cco) 0) < n)
          by (apply lit_var_c_in_range; exact Hlit);
        assert (Hvarsize : lit_var_c (Znth 0 (co_lits cco) 0) < ms_size Mc)
          by (rewrite <- Hsize; exact (proj2 hvar));
        destruct (in_split _ _ hinl) as [cpre [cpost Hsplit]];
        assert (Hfocus :
          clause_db_rep (cpre ++ (Znth (i - 0) ws 0, cco) :: cpost) |--
          MiniSatClause.rep (Znth (i - 0) ws 0) true (co_lits cco) **
          clause_db_pair_remainder db_nil
            (cpre ++ (Znth (i - 0) ws 0, cco) :: cpost)
            (Znth (i - 0) ws 0) true (co_lits cco))
          by (sep_apply (clause_db_rep_app_elim cpre
                ((Znth (i - 0) ws 0, cco) :: cpost));
              change (clause_db_rep cpre **
                (MiniSatClause.rep (Znth (i - 0) ws 0) (co_learnt cco)
                   (co_lits cco) ** clause_db_rep cpost) |--
                MiniSatClause.rep (Znth (i - 0) ws 0) true (co_lits cco) **
                clause_db_pair_remainder db_nil
                  (cpre ++ (Znth (i - 0) ws 0, cco) :: cpost)
                  (Znth (i - 0) ws 0) true (co_lits cco));
              rewrite Htag at 1;
              unfold clause_db_pair_remainder;
              Right; Exists cco cpre cpost;
              unfold db_nil; entailer_with ltac:(int_auto));
        rewrite Hsplit at 1;
        sep_apply Hfocus;
        unfold MiniSatClause.rep at 1;
        coq_prop_lift;
        apply coq_prop_andp_left;
        intros [Hlen0 [Hposw Heven]];
        unfold activity_state at 1;
        Intros act;
        assert (Hhdr : clause_hdr_word true (Zlength (co_lits cco)) / 2 =
          Zlength (co_lits cco))
          by (apply clause_hdr_word_div2; exact Hlen0);
        assert (Hrem : Znth (i - 0) ws 0 % 2 = 0)
          by (assert (htwo : (2 : Z) <> 0) by lia;
              apply (proj2 (Z.rem_divide _ 2 htwo));
              apply (proj1 (Z.mod_divide _ 2 htwo));
              exact Heven);
        assert (Hquot : clause_hdr_word msat_true (Zlength (co_lits cco)) ÷ 2 =
          Zlength (co_lits cco))
          by (unfold msat_true;
              rewrite zdiv_equiv;
              [ exact Hhdr | unfold clause_hdr_word; lia | lia ]);
        Exists (co_lits cco) act;
        entailer_with ltac:(int_auto);
        try (match goal with
             | Hcl : msat_fp32_count_limit _ ?el |- _ =>
                 assert (Hextra : msat_fp32_nonnegative el) by (apply Hcl; lia);
                 try exact Hextra
             end);
        try (rewrite Hsplit; unfold msat_true; entailer_with ltac:(lia)) )
  end.

(* The key/semantics obligations of a binary-clause `keep` transition: the
   scan's physical invariant pins the rest of the watcher list to the slot the
   cursor is standing on, both candidate writes read that slot back unchanged,
   and the scan semantics hold with a null conflict.  One VC of the family asks
   for each of those facts, which is what the closing menu selects between. *)
Ltac msat_propagate_binary_keep_scan_key_p8 :=
  pre_process_default; split_pures; entailer_with lia;
  match goal with
  | Hwm : ?wm = ?rp ++ ?sc :: ?rs,
    Hrp : Zlength ?rp = ?ii,
    Htag : is_tag ?sc = msat_true,
    Hphys : propagation_watch_scan_physical _ ?ret _ ?rst _ ?wm ?ii ?jj,
    Hsem : solver_propagation_scan_semantics ?n ?F ?Aa ?K ?Ms ?p ?cf ?ret ?rst,
    Hreuse : minisat_propagation_reuse_scan ?entry ?Ms ?p ?cf ?rst
    |- _ =>
      assert (Hrest : rst = sc :: rs)
        by (eapply propagation_watch_scan_rest_head__propagate;
            [ exact Hphys | exact Hwm | exact Hrp ]);
      unfold propagation_watch_scan_physical in Hphys;
      destruct Hphys as [Hinv [Hmem [Hkept [Hkg Hlen]]]];
      assert (Hii : 0 <= ii < Zlength wm) by lia;
      assert (Hjj : 0 <= jj < Zlength wm) by lia;
      assert (Hkeyi : Znth ii (replace_Znth ii sc wm) 0 = sc)
        by (apply Znth_replace_Znth_Same; exact Hii);
      assert (Hkeyj : Znth ii (replace_Znth jj sc wm) 0 = sc)
        by (destruct (Z.eq_dec jj ii) as [Heq|Hne];
            [ rewrite Heq; exact Hkeyi
            | rewrite (Znth_replace_Znth_Diff 0 wm jj ii sc Hjj Hii Hne);
              rewrite Hwm; rewrite app_Znth2 by lia; rewrite Hrp;
              replace (ii - ii) with 0 by lia; reflexivity ]);
      assert (Hcf_zero : cf = 0)
        by (destruct Hsem as [[Hc _] | [_ [Hnil _]]];
            [ exact Hc | rewrite Hrest in Hnil; discriminate ]);
      assert (Hreuse0 : minisat_propagation_reuse_scan entry Ms p 0 rst)
        by (rewrite <- Hcf_zero; exact Hreuse);
      unfold solver_propagation_scan_semantics in Hsem;
      assert (Hsem0 : solver_propagation_scan_semantics n F Aa K Ms p 0 ret rst)
        by (destruct Hsem as [Hlive | Hconf];
            [ destruct Hlive as [Hc Hrestsem];
              unfold solver_propagation_scan_semantics; left; split;
              [ reflexivity | exact Hrestsem ]
            | destruct Hconf as [_ [Hnil _]]; exfalso;
              rewrite Hrest in Hnil; discriminate ]);
      first [ exact Hrest
            | rewrite Hkeyi; exact Hrest
            | rewrite Hkeyj; exact Hrest
            | unfold tagged_word; rewrite Hkeyi; exact Htag
            | unfold tagged_word; rewrite Hkeyj; exact Htag
            | exact Hsem0
            | exact Hreuse0
            | solve [unfold minisat_propagation_reuse_scan in *; tauto]
            | match goal with
              | Hbeg : ?M = msolver_propagation_scan_begin _ _ _ |- _ =>
                  rewrite <- Hbeg; first [exact Hsem0 | exact Hreuse0 |
                    solve [unfold minisat_propagation_reuse_scan in *; tauto]]
              end ]
  end.

(* Focus the learnt-clause arm of a solver_reducedb which-implies obligation: bind the five
   loop facts under the caller's names, split the clause-db pair, discharge the empty-db arm,
   and refold the head learnt clause.  Shared by solver_reducedb_which_implies_wit_4/_wit_8. *)
Tactic Notation "msat_reducedb_focus_learnt_p8" constr(n) constr(F) constr(A_arr)
    constr(A_inst) constr(Mc) constr(i) constr(ws) ident(lts) constr(ltsv) constr(act)
    ident(Hinv) ident(Hfp) ident(Hpos) ident(Hev) ident(Hne) :=
  bind_fact ( msolver_inv n F A_arr A_inst Mc ) as Hinv;
  bind_fact ( msat_fp32_nonnegative act ) as Hfp;
  bind_fact ( 0 < Znth (i - 0) ws 0 ) as Hpos;
  bind_fact ( Znth (i - 0) ws 0 % 2 = 0 ) as Hev;
  bind_fact ( Znth (lit_var_c (Znth (0 - 0) ltsv 0) - 0) (ms_reason_words Mc) 0
              <> Znth (i - 0) ws 0 ) as Hne;
      unfold clause_db_pair_remainder;
      set_String_name;
      repeat rewrite orp_sepcon_left_equiv;
      repeat rewrite orp_sepcon_right_equiv;
      repeat rewrite orp_sepcon_left_equiv;
      apply derivable1_orp_elim;
      subst_all_strings;
      [ Intros co pre post;
        unfold db_nil in *;
        match goal with
        | Hc : _ /\ _ |- _ =>
            destruct Hc as [Hdb [Hlits Htag]];
            symmetry in Hdb;
            apply app_eq_nil in Hdb;
            destruct Hdb as [_ Hfalse];
            discriminate Hfalse
        end
      | let cco := fresh "co" in
        let cpre := fresh "pre" in
        let cpost := fresh "post" in
        ( Intros cco cpre cpost;
          match goal with
          | Hc : _ /\ _ |- _ =>
          destruct Hc as [Hdb [Hlits Htag]];
          subst lts;
          assert (Hinlearnt : In (Znth (i - 0) ws 0, cco) (ms_learnt Mc))
            by (rewrite Hdb; apply in_or_app; right; simpl; auto);
          assert (Hin : In (Znth (i - 0) ws 0, cco) (msolver_db Mc))
            by (unfold msolver_db; apply in_or_app; right; exact Hinlearnt);
          assert (Hobj : obj_wf n cco)
            by (eapply db_wf_obj; [ exact (msi_db_wf Hinv) | exact Hin ]);
          destruct Hobj as [Hlen [Hwf Hnd]];
          assert (Hdistinct : lit_var_c (Znth 0 (co_lits cco) 0) <>
                              lit_var_c (Znth 1 (co_lits cco) 0))
            by (destruct (co_lits cco) as [|a xs] eqn:Hco;
                [ change (2 <= 0) in Hlen; lia
                | destruct xs as [|b xs];
                  [ change (2 <= 1) in Hlen; lia
                  | inversion Hnd as [|x l Hnot Htail];
                    let heq := fresh "Heq" in
                    ( intro heq; apply Hnot; simpl; left; simpl in heq;
                      symmetry; exact heq ) ] ]);
          assert (Hshape := msi_shape Hinv);
          assert (Hsize : n = ms_size Mc) by exact (msi_size Hinv);
          assert (Hdim : 0 <= ms_size Mc /\ ms_size Mc <= ms_cap Mc /\
            2 * ms_size Mc <= INT_MAX /\ Zlength (ms_stats Mc) = 11)
            by (unfold solver_shape in Hshape; tauto);
          assert (Hreasonlen := solver_shape_reasons_len Mc Hshape);
          assert (Hwmlen := solver_shape_wm_len Mc Hshape);
          assert (Hwcapslen := solver_shape_wcaps_len Mc Hshape);
          assert (Hwatch0 : In (clause_watch_word (Znth (i - 0) ws 0)
            (co_lits cco) (Znth 1 (co_lits cco) 0))
            (Znth (lit_neg_c (Znth 0 (co_lits cco) 0)) (ms_wm Mc) nil))
            by (unfold clause_watch_word;
                destruct (Z.ltb 2 (Zlength (co_lits cco))) eqn:Hbig;
                [ apply Z.ltb_lt in Hbig;
                  assert (Hthree : 3 <= Zlength (co_lits cco)) by lia;
                  exact (wmap_present_real0 n (msolver_db Mc) (ms_wm Mc)
                    (Znth (i - 0) ws 0) cco (msi_db_wf Hinv)
                    (msi_wmap_exact Hinv) Hin Hthree)
                | apply Z.ltb_ge in Hbig;
                  assert (Htwo : Zlength (co_lits cco) = 2) by lia;
                  exact (wmap_present_bin0 n (msolver_db Mc) (ms_wm Mc)
                    (Znth (i - 0) ws 0) cco (msi_db_wf Hinv)
                    (msi_wmap_exact Hinv) Hin Htwo) ]);
          assert (Hwatch1 : In (clause_watch_word (Znth (i - 0) ws 0)
            (co_lits cco) (Znth 0 (co_lits cco) 0))
            (Znth (lit_neg_c (Znth 1 (co_lits cco) 0)) (ms_wm Mc) nil))
            by (unfold clause_watch_word;
                destruct (Z.ltb 2 (Zlength (co_lits cco))) eqn:Hbig;
                [ apply Z.ltb_lt in Hbig;
                  assert (Hthree : 3 <= Zlength (co_lits cco)) by lia;
                  exact (wmap_present_real1 n (msolver_db Mc) (ms_wm Mc)
                    (Znth (i - 0) ws 0) cco (msi_db_wf Hinv)
                    (msi_wmap_exact Hinv) Hin Hthree)
                | apply Z.ltb_ge in Hbig;
                  assert (Htwo : Zlength (co_lits cco) = 2) by lia;
                  exact (wmap_present_bin1 n (msolver_db Mc) (ms_wm Mc)
                    (Znth (i - 0) ws 0) cco (msi_db_wf Hinv)
                    (msi_wmap_exact Hinv) Hin Htwo) ]);
          assert (Hunlocked : clause_unlocked_words (Znth (i - 0) ws 0)
            (ms_reason_words Mc))
            by (assert (Hreason0 : Znth (lit_var_c (co_watch0 cco))
                  (ms_reason_words Mc) 0 <> Znth (i - 0) ws 0)
                  by (unfold co_watch0; rewrite Z.sub_0_r in Hne; exact Hne);
                eapply solver_simplify_head_unlocked;
                [ exact (msi_weak Hinv) | exact Hin | exact Hreason0 ]);
          unfold clause_remove_pre, solver_wlists_handle,
            clause_remove_ready, clause_unlocked_words;
          Right; Exists cco cpre cpost;
          entailer_with ltac:(lia);
          try assumption;
          try (rewrite <- Hsize; assumption);
          eapply clause_rep_refold__reducedb;
          try lia;
          try exact Hpos;
          try exact Hfp;
          try exact (rem_zero_mod_zero__reducedb _
            (Z.lt_le_incl _ _ Hpos) Hev)
          end ) ].

(* Close a solver_solve "assignment cell is not INT_MIN" safety obligation: pick the strong
   assuming-invariant out of the context and hand its four arguments to the shared closer.
   Shared by solver_solve_safety_wit_18 and solver_solve_safety_wit_19. *)
Tactic Notation "msat_solve_assign_cell_not_int_min_p8" ident(rv) :=
  match goal with
  | Hs : msolver_inv_assuming_strong _ _ _ (assumption_prefix ?raw ?k) ?Mc |- _ =>
      msat_solve_close_assign_cell_not_int_min Hs raw k Mc rv
  end.

(* The clause_simplify scan step that finds a satisfied literal and leaves the loop.
   Pull the scan invariant apart and turn the halved header word back into the literal
   count; then (first goal) merge the single-cell view of slot [ii] back into the full
   literal array of the clause at [cp], and (second goal) exhibit [ii] as the satisfying
   position.  The two callers differ only in the polarity of the sign test: [cellval] is
   the assignment value the tested literal must carry and [hpol] the sign fact.  The
   five facts the body binds are named through [fresh] so that the callers need not
   pass hypothesis names: an [in H] clause is checked when the tactic is DEFINED. *)
Tactic Notation "msat_clause_simplify_scan_exit_p8" ident(nn) ident(ii) ident(cw)
    ident(asg) ident(isl) ident(rv) ident(rv2) ident(rv3) ident(clit) ident(cval)
    ident(lts) ident(cp) ident(aptr) constr(cellval) uconstr(hpol) :=
  let hcell := fresh "H_cell" in
  let hpolarity := fresh "H_polarity" in
  let hsign := fresh "H_sign" in
  let hhalf := fresh "H_hdr_half" in
  let hinv := fresh "H_scan_inv" in
  ( aggressive_pre_process;
      bind_fact ( Znth rv3 (replace_Znth (lit_var_c clit) cval asg) 0 = cellval ) as hcell;
      bind_fact ( hpol ) as hpolarity;
      bind_fact ( rv2 = lit_sign_c clit ) as hsign;
      bind_fact ( rv = clause_hdr_word isl (Zlength cw) ÷ 2 ) as hhalf;
      bind_fact ( clause_simplify_scan_inv nn cw asg ii ) as hinv;
      unfold clause_simplify_scan_inv in hinv;
      destruct hinv as (Hi & Halen & Hlits & Hcells & Hprefix);
      assert (Hhdr : 0 <= clause_hdr_word isl (Zlength cw))
        by (apply clause_hdr_word_nonneg; apply Zlength_nonneg);
      rewrite zdiv_equiv in hhalf by lia;
      rewrite clause_hdr_word_div2 in hhalf by apply Zlength_nonneg;
    [ subst lts rv3 cval clit;
      rewrite replace_Znth_Znth by lia;
      sep_apply_l_atomic
        (IntArray.missing_i_merge_to_full
          (clause_lits_addr cp) ii (Zlength cw) (Znth ii cw 0) cw);
      [ dump_pre_spatial; lia
      | rewrite replace_Znth_Znth by lia;
        sep_apply_l_atomic (CharArray.full_to_seg aptr nn asg);
        entailer_with ltac:(int_auto) ]
    | unfold clause_simplify_result, packed_lit_satisfying_value;
      left; split; [reflexivity|];
      exists ii; split; [lia|];
      subst rv3 cval clit;
      rewrite replace_Znth_Znth in hcell by lia;
      unfold lit_sign_c in hpolarity, hsign |- *;
      destruct (Z.odd (Znth ii cw 0)); simpl in *; lia ] ).

(* The clause_simplify scan step that keeps scanning: the same prelude as the exit step,
   then (first goal) merge the single-cell view of slot [ii] back into the literal array
   [lts], and (second goal) re-establish the scan invariant one position further -- [ii]
   is the only position the old prefix property does not already cover.  [cellval] and
   [hpol] carry the polarity of the sign test, the only difference between the callers.
   The five facts the body binds are named through [fresh] so that the callers need not
   pass hypothesis names: an [in H] clause is checked when the tactic is DEFINED. *)
Tactic Notation "msat_clause_simplify_scan_step_p8" ident(nn) ident(ii) ident(cw)
    ident(asg) ident(isl) ident(rv) ident(rv2) ident(rv3) ident(clit) ident(cval)
    ident(lts) ident(aptr) constr(cellval) uconstr(hpol) :=
  let hcell := fresh "H_cell" in
  let hpolarity := fresh "H_polarity" in
  let hsign := fresh "H_sign" in
  let hhalf := fresh "H_hdr_half" in
  let hinv := fresh "H_scan_inv" in
  ( aggressive_pre_process;
      bind_fact ( Znth rv3 (replace_Znth (lit_var_c clit) cval asg) 0 <> cellval ) as hcell;
      bind_fact ( hpol ) as hpolarity;
      bind_fact ( rv2 = lit_sign_c clit ) as hsign;
      bind_fact ( rv = clause_hdr_word isl (Zlength cw) ÷ 2 ) as hhalf;
      bind_fact ( clause_simplify_scan_inv nn cw asg ii ) as hinv;
      unfold clause_simplify_scan_inv in hinv;
      destruct hinv as (Hi & Halen & Hlits & Hcells & Hprefix);
      assert (Hhdr : 0 <= clause_hdr_word isl (Zlength cw))
        by (apply clause_hdr_word_nonneg; apply Zlength_nonneg);
      rewrite zdiv_equiv in hhalf by lia;
      rewrite clause_hdr_word_div2 in hhalf by apply Zlength_nonneg;
    [ subst rv3 cval clit;
      rewrite replace_Znth_Znth by lia;
      sep_apply_l_atomic
        (IntArray.missing_i_merge_to_full lts ii (Zlength cw) (Znth ii cw 0) cw);
      [ dump_pre_spatial; lia
      | rewrite replace_Znth_Znth by lia;
        sep_apply_l_atomic (CharArray.full_to_seg aptr nn asg);
        entailer_with ltac:(int_auto) ]
    | unfold clause_simplify_scan_inv;
      repeat split; auto; try lia;
      intros j Hj;
      destruct (Z.lt_ge_cases j ii) as [Hji | Hji];
      [ apply Hprefix; lia
      | assert (j = ii) by lia; subst j;
        subst rv3 cval clit;
        rewrite replace_Znth_Znth in hcell by lia;
        unfold packed_lit_satisfying_value, lit_sign_c in hpolarity, hsign |- *;
        destruct (Z.odd (Znth ii cw 0)); simpl in *; lia ] ] ).

(* Close a clause-pointer alignment side condition from the evenness fact that the
   caller derived from the clause's tag word.  The fact is located by its shape, so
   the tactic can be called from a nested arm that does not know its name. *)
Ltac msat_analyze_clause_ptr_even_p8 :=
  match goal with
  | He : Z.even _ = true |- _ => apply clause_ptr_mod2; exact He
  end.

(* One side of the analyze clause-database focus: the focused clause [cc] sits in the
   partner list of [other_db], so split that list around it, refold it as a
   MiniSatClause.rep and put the two halves back.  [Mc] is the solver model. *)
Tactic Notation "msat_analyze_clause_db_side_p8" ident(cc) ident(Mc) constr(other_db) :=
  let cco := fresh "co" in
  let cpre := fresh "pre" in
  let cpost := fresh "post" in
  ( Intros cco cpre cpost;
    match goal with
    | Hd : _ = _ ++ _ :: _ /\ _ /\ _ |- _ =>
        destruct Hd as [Hdecomp [Hlits Htag]];
        rewrite Hdecomp;
        transitivity
          ((clause_db_rep cpre ** clause_db_rep ((cc, cco) :: cpost)) **
          (clause_db_rep other_db **
           MiniSatClause.rep (ms_binary Mc) msat_false (ms_binary_lits Mc)));
        [ rewrite clause_db_rep_cons;
          unfold MiniSatClause.rep;
          cbn [fst snd]; rewrite Htag, Hlits;
          entailer_with ltac:(int_auto);
          [ apply Zlength_nonneg | msat_analyze_clause_ptr_even_p8 ]
        | sep_apply (clause_db_rep_app_intro cpre ((cc, cco) :: cpost));
          entailer_with ltac:(lia) ]
    end ).

(* Focus the analysis remainder of model [Mc] on the clause [cc] once its tag word says
   it is a real clause: derive the evenness of the clause pointer from the tag, split
   the remainder into its binary and real arms, and discharge the two real arms
   (problem db, learnt db) with the shared side tactic.  Only the binary arm differs
   between the callers, so it is the single tactic argument. *)
Tactic Notation "msat_analyze_focus_clause_db_p8" ident(cc) ident(Mc) tactic3(binary_arm) :=
  let htag := fresh "H_is_tag" in
  ( bind_fact ( is_tag cc = msat_false ) as htag;
    entailer_with ltac:(lia);
    assert (Heven : Z.even cc = true)
      by (rewrite <- Z.negb_odd;
          unfold is_tag, msat_false in htag;
          rewrite htag; reflexivity);
    unfold analysis_clause_remainder;
    Split;
    [ binary_arm
    | Intros_p Hreal;
      unfold clause_db_pair_remainder;
      Split;
      [ msat_analyze_clause_db_side_p8 cc Mc (ms_learnt Mc)
      | msat_analyze_clause_db_side_p8 cc Mc (ms_prob Mc) ] ] ).


(* ===== solver_simplify delete-step helpers (used by which_implies_wit_13) ===== *)
(* The simplify loop's spatial remainder does not see a clause deletion: the
   removal rewrites only the selected database, while [solver_simplify_db_rest_at]
   reads the size, the watcher table (now [wm']), the reason array, the statistics
   (now [stats']) and the frame of the *other* database, none of which the
   selected-side removal touches.  The [type]/[from_learnt] pair is constrained
   because the frame keeps the database the loop is not walking. *)
Lemma msat_simplify13_db_rest_after_remove_p8 :
  forall s type b Mcur c wm' stats' reasons lvl wl asg,
    (type = 0 /\ b = false) \/ (type = 1 /\ b = true) ->
    solver_simplify_db_rest_at s type
      (msolver_remove_clause Mcur b c wm' stats') reasons lvl wl asg =
    (&(s # "solver_t" ->ₛ "size") # Int |-> ms_size Mcur **
     solver_wlists_handle s wl **
     wlists_rep wl (ms_size Mcur) wm' (ms_wcaps Mcur) **
     &(s # "solver_t" ->ₛ "reasons") # Ptr |-> reasons **
     PtrArray.seg reasons 0 (ms_size Mcur) (ms_reason_words Mcur) **
     PtrArray.undef_seg reasons (ms_size Mcur) (ms_cap Mcur) **
     stats_rep &(s # "solver_t" ->ₛ "stats") stats' **
     solver_simplify_clause_frame_at s type Mcur asg lvl).
Proof.
  intros s type b Mcur c wm' stats' reasons lvl wl asg Htype.
  unfold solver_simplify_db_rest_at, solver_simplify_clause_frame_at,
    clause_new_scalars_frame, solver_fp_rep, solver_other_db_vec_rep,
    solver_levels_slice_at, solver_other_clause_db_rep.
  destruct Htype as [[-> ->] | [-> ->]];
    cbn [msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ]; reflexivity.
Qed.

(* Everything the compaction loop has to re-establish about the successor state
   once the successor is known to satisfy the solver invariant.  The trail, the
   queue head, the pending-propagation flag, the seed shadow, the model and the
   clause-decay factor are inherited field by field from [Mcur], and the
   compaction invariant advances by one slot; the deletion arm of
   [solver_simplify_compaction_step] then assembles them.  Shared by the
   problem-database and the learnt-database arms of the delete step. *)
Lemma msat_simplify13_delete_step_from_inv_p8 :
  forall n F A_arr type b Mcur words i jcur wm' stats',
    b = solver_selected_is_learnt type ->
    msolver_inv_assuming_strong n F A_arr A_arr Mcur ->
    msolver_inv_assuming_strong n F A_arr A_arr
      (msolver_remove_clause Mcur b (Znth i words 0) wm' stats') ->
    Zlength (mt_lim (ms_core Mcur)) = 0 ->
    mt_qhead (ms_core Mcur) = ms_qtail Mcur ->
    ms_capacity_root_propagation_pending Mcur = 0 ->
    msolver_seed_shadow Mcur ->
    solver_simplify_db_compaction_inv type Mcur words i jcur ->
    i < Zlength words ->
    solver_simplify_compaction_step n F A_arr type Mcur words i jcur
      (msolver_remove_clause Mcur b (Znth i words 0) wm' stats') words jcur.
Proof.
  intros n F A_arr type b Mcur words i jcur wm' stats'
    Hb H_msolver_inv Hinvnext H_Zlength H_mt_qhead
    H_ms_capacity_root_propagation_pending H_msolver_seed_shadow
    H_solver_simplify_db_compaction_inv H_i.
  pose proof (solver_assuming_level_zero_normalized__api_reentry
    n F A_arr Mcur H_msolver_inv H_Zlength) as Hnormal.
  subst b.
  set (Mnext := msolver_remove_clause Mcur (solver_selected_is_learnt type)
    (Znth i words 0) wm' stats').
  assert (Hlimnext : Zlength (mt_lim (ms_core Mnext)) = 0).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact H_Zlength. }
  assert (Hqnext : mt_qhead (ms_core Mnext) = ms_qtail Mnext).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact H_mt_qhead. }
  assert (Hpendingnext :
      ms_capacity_root_propagation_pending Mnext = 0).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact H_ms_capacity_root_propagation_pending. }
  assert (Hseednext : msolver_seed_shadow Mnext).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    exact H_msolver_seed_shadow. }
  assert (Hmodelnext : ms_model Mnext = ms_model Mcur).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    reflexivity. }
  assert (Hdecaynext : ms_cla_decay Mnext = ms_cla_decay Mcur).
  { cbn [Mnext msolver_remove_clause msolver_propagation_overlay msolver_propagation_update ].
    reflexivity. }
  assert (Hcompnext : solver_simplify_db_compaction_inv type Mnext
      words (i + 1) jcur).
  { unfold Mnext.
    exact (solver_simplify_db_compaction_inv_remove__simplify
      n F A_arr (@nil literal) type (msolver_set_root Mcur 0) words i jcur
      (Znth i words 0) wm' stats' (msi_weak Hnormal)
      H_solver_simplify_db_compaction_inv H_i eq_refl). }
  unfold solver_simplify_compaction_step.
  split.
  - right. split; [reflexivity |]. split; [reflexivity |].
    exists wm', stats'. unfold solver_simplify_delete_transition.
    split.
    + unfold Mnext. reflexivity.
    + split; [exact Hinvnext |].
      split; [exact Hlimnext |].
      split; [exact Hqnext |].
      split; [exact Hpendingnext |].
      exact Hseednext.
  - split; [exact Hinvnext |].
    split; [exact Hlimnext |].
    split; [exact Hqnext |].
    split; [exact Hpendingnext |].
    split; [exact Hseednext |].
    split; [exact Hmodelnext |].
    split; [exact Hdecaynext | exact Hcompnext].
Qed.

(* The database bookkeeping of one delete step of the simplify compaction loop.
   The split the caller owns exposes an entry at the pointer the loop is looking
   at, so key uniqueness identifies it with the clause the lookup returned, the
   prefix cannot mention that pointer again, and [db_remove_ptr] therefore leaves
   exactly the split with the entry dropped.  The problem arm additionally has to
   show the removed clause is satisfied at the root before
   [msolver_inv_remove_problem__simplify] applies; the learnt arm removes an
   unlocked learnt clause and needs no such obligation. *)
Lemma msat_simplify13_delete_arm_facts_p8 :
  forall n F A_arr type b Mcur words i jcur co co1 pre post wm' stats',
    (type = 0 /\ b = false) \/ (type = 1 /\ b = true) ->
    msolver_inv_assuming_strong n F A_arr A_arr Mcur ->
    solver_selected_db type Mcur = pre ++ (Znth i words 0, co1) :: post ->
    db_lookup (solver_selected_db type Mcur) (Znth i words 0) co ->
    clause_simplify_result (co_lits co) (mt_assigns (ms_core Mcur)) 1 ->
    Zlength (mt_lim (ms_core Mcur)) = 0 ->
    mt_qhead (ms_core Mcur) = ms_qtail Mcur ->
    ms_capacity_root_propagation_pending Mcur = 0 ->
    msolver_seed_shadow Mcur ->
    solver_simplify_db_compaction_inv type Mcur words i jcur ->
    i < Zlength words ->
    clause_remove_result (Znth i words 0) (co_lits co) (ms_wm Mcur) wm' ->
    Zlength stats' = 11 ->
    clause_unlocked_words (Znth i words 0) (ms_reason_words Mcur) ->
    co1 = co /\
    solver_selected_db type
      (msolver_remove_clause Mcur b (Znth i words 0) wm' stats') = pre ++ post /\
    solver_simplify_compaction_step n F A_arr type Mcur words i jcur
      (msolver_remove_clause Mcur b (Znth i words 0) wm' stats') words jcur.
Proof.
  intros n F A_arr type b Mcur words i jcur co co1 pre post wm' stats'
    Htype H_msolver_inv Hsplit H_db_lookup H_clause_simplify_result
    H_Zlength H_mt_qhead H_ms_capacity_root_propagation_pending
    H_msolver_seed_shadow H_solver_simplify_db_compaction_inv H_i
    Hremove Hstats Hunlocked.
  assert (Hmain : co1 = co /\
      solver_selected_db type
        (msolver_remove_clause Mcur b (Znth i words 0) wm' stats')
        = pre ++ post /\
      msolver_inv_assuming_strong n F A_arr A_arr
        (msolver_remove_clause Mcur b (Znth i words 0) wm' stats')).
  { destruct Htype as [[-> ->] | [-> ->]].
    - unfold solver_selected_db in Hsplit, H_db_lookup.
      simpl in Hsplit, H_db_lookup.
      assert (Hin1 : In (Znth i words 0, co1) (msolver_db Mcur)).
      { unfold msolver_db. apply in_or_app. left. rewrite Hsplit.
        apply in_or_app. right. left. reflexivity. }
      assert (Hinco : In (Znth i words 0, co) (msolver_db Mcur)).
      { unfold db_lookup in H_db_lookup. unfold msolver_db.
        apply in_or_app. left. exact H_db_lookup. }
      assert (Heq : co1 = co).
      { eapply db_wf_lookup_unique.
        - exact (msa_db_wf (msas_weak H_msolver_inv)).
        - exact Hin1.
        - exact Hinco. }
      subst co1.
      assert (Hfresh : ~ In (Znth i words 0) (map fst pre)).
      { eapply db_wf_prob_split_fresh__simplify.
        - exact (msa_db_wf (msas_weak H_msolver_inv)).
        - exact Hsplit. }
      assert (Hobj : obj_wf n co).
      { eapply db_wf_obj.
        - exact (msa_db_wf (msas_weak H_msolver_inv)).
        - exact Hinco. }
      assert (Hroot : root_satisfied (ms_core Mcur) (denote_obj co)).
      { unfold denote_obj.
        eapply clause_simplify_result_root_satisfied__simplify.
        - exact (msa_trail_wf (msas_weak H_msolver_inv)).
        - exact H_Zlength.
        - exact (proj1 (proj2 Hobj)).
        - exact H_clause_simplify_result. }
      split; [reflexivity |]. split.
      { unfold solver_selected_db, msolver_remove_clause,
          msolver_propagation_overlay, msolver_propagation_update.
        cbn. rewrite Hsplit.
        apply db_remove_ptr_split__reducedb. exact Hfresh. }
      { eapply solver_assuming_remove_problem_at_zero__api_reentry.
        - exact H_msolver_inv.
        - exact H_Zlength.
        - exact Hsplit.
        - exact Hfresh.
        - exact Hremove.
        - exact Hstats.
        - exact Hunlocked.
        - exact Hroot. }
    - unfold solver_selected_db in Hsplit, H_db_lookup.
      simpl in Hsplit, H_db_lookup.
      assert (Hin1 : In (Znth i words 0, co1) (msolver_db Mcur)).
      { unfold msolver_db. apply in_or_app. right. rewrite Hsplit.
        apply in_or_app. right. left. reflexivity. }
      assert (Hinco : In (Znth i words 0, co) (msolver_db Mcur)).
      { unfold db_lookup in H_db_lookup. unfold msolver_db.
        apply in_or_app. right. exact H_db_lookup. }
      assert (Heq : co1 = co).
      { eapply db_wf_lookup_unique.
        - exact (msa_db_wf (msas_weak H_msolver_inv)).
        - exact Hin1.
        - exact Hinco. }
      subst co1.
      assert (Hfresh : ~ In (Znth i words 0) (map fst pre)).
      { eapply db_wf_learnt_split_fresh__reducedb.
        - exact (msa_db_wf (msas_weak H_msolver_inv)).
        - exact Hsplit. }
      split; [reflexivity |]. split.
      { unfold solver_selected_db, msolver_remove_clause,
          msolver_propagation_overlay, msolver_propagation_update.
        cbn. rewrite Hsplit.
        apply db_remove_ptr_split__reducedb. exact Hfresh. }
      { eapply solver_assuming_remove_learnt_at_zero__api_reentry.
        - exact H_msolver_inv.
        - exact H_Zlength.
        - exact Hsplit.
        - exact Hfresh.
        - exact Hremove.
        - exact Hstats.
        - exact Hunlocked. } }
  destruct Hmain as [Heq [Hdbnext Hinvnext]].
  split; [exact Heq |]. split; [exact Hdbnext |].
  eapply msat_simplify13_delete_step_from_inv_p8;
    [ | exact H_msolver_inv | exact Hinvnext | exact H_Zlength
    | exact H_mt_qhead | exact H_ms_capacity_root_propagation_pending
    | exact H_msolver_seed_shadow
    | exact H_solver_simplify_db_compaction_inv | exact H_i ].
  destruct Htype as [[-> ->] | [-> ->]]; reflexivity.
Qed.

(* ===== clause_remove which_implies wits (1 proofs) ===== *)
Lemma proof_of_clause_remove_which_implies_wit_4 : clause_remove_which_implies_wit_4.
Proof.
  Unfold.
  right. intros.
  subst lits.
  bind_fact ( c % 2 = 0 ) as H_c.
  prop_apply (IntArray.seg_valid (clause_lits_addr c) 2
    (Zlength clause_words)
    (sublist 2 (Zlength clause_words) clause_words)).
  Intros.
  replace (clause_lits_addr c + 0 * sizeof(INT))
    with (clause_lits_addr c) by lia.
  replace (clause_lits_addr c + 1 * sizeof(INT))
    with (clause_lits_addr c + sizeof(INT)) by lia.
  sep_apply (intarray_refold_first_two__clause_remove
    (clause_lits_addr c) clause_words ltac:(lia)).
  sep_apply (IntArray.seg_to_undef_seg (clause_lits_addr c) 0
    (Zlength clause_words) clause_words).
  sep_apply store_int_undef_store_int.
  sep_apply activity_state_undef.
  unfold MiniSatClause.owned.
  entailer_with ltac:(lia).
  rewrite Z.rem_mod_nonneg in H_c by lia.
  exact H_c.
Qed.

(* ===== clause_simplify entail wits (6 proofs) ===== *)
Lemma proof_of_clause_simplify_entail_wit_1 : clause_simplify_entail_wit_1.
Proof.
  aggressive_pre_process;
    pose proof (Zlength_nonneg clause_words) as H_clause_words_nonneg;
    try exact H_clause_words_nonneg.
  bind_fact ( Zlength assigns0 = n ) as H_Zlength;
    try solve [entailer_with ltac:(lia)].
  unfold clause_simplify_scan_inv.
  rewrite H_Zlength.
  repeat split; auto; intros; lia.
Qed.

Lemma proof_of_clause_simplify_entail_wit_3_1 : clause_simplify_entail_wit_3_1.
Proof.
  msat_clause_simplify_scan_exit_p8 n i clause_words assigns0 is_learnt retval retval_2
    retval_3 current_lit current_value lits c_pre assigns_ptr ( 0 + 0 - 1 ) ( retval_2 <> 0 ).
Qed.

Lemma proof_of_clause_simplify_entail_wit_3_2 : clause_simplify_entail_wit_3_2.
Proof.
  msat_clause_simplify_scan_exit_p8 n i clause_words assigns0 is_learnt retval retval_2
    retval_3 current_lit current_value lits c_pre assigns_ptr ( 1 + 1 - 1 ) ( retval_2 = 0 ).
Qed.

Lemma proof_of_clause_simplify_entail_wit_4_1 : clause_simplify_entail_wit_4_1.
Proof.
  msat_clause_simplify_scan_step_p8 n i clause_words assigns0 is_learnt retval retval_2
    retval_3 current_lit current_value lits assigns_ptr ( 0 + 0 - 1 ) ( retval_2 <> 0 ).
Qed.

Lemma proof_of_clause_simplify_entail_wit_4_2 : clause_simplify_entail_wit_4_2.
Proof.
  msat_clause_simplify_scan_step_p8 n i clause_words assigns0 is_learnt retval retval_2
    retval_3 current_lit current_value lits assigns_ptr ( 1 + 1 - 1 ) ( retval_2 = 0 ).
Qed.

Lemma proof_of_clause_simplify_entail_wit_5 : clause_simplify_entail_wit_5.
Proof.
  aggressive_pre_process.
  bind_fact ( retval = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval.
  bind_fact ( clause_simplify_scan_inv n clause_words assigns0 i ) as H_clause_simplify_scan_inv;
    unfold clause_simplify_scan_inv in H_clause_simplify_scan_inv;
    destruct H_clause_simplify_scan_inv as (Hi & Halen & Hlits & Hcells & Hprefix);
    assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
      by (apply clause_hdr_word_nonneg; apply Zlength_nonneg);
    rewrite zdiv_equiv in H_retval by lia;
    rewrite clause_hdr_word_div2 in H_retval by apply Zlength_nonneg.
  unfold clause_simplify_result.
  right. split; [reflexivity|].
  intros j Hj. apply Hprefix. lia.
Qed.

(* ===== clause_simplify partial_solve wits (3 proofs) ===== *)
Lemma proof_of_clause_simplify_partial_solve_wit_4_pure : clause_simplify_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process;
    dump_pre_spatial;
    apply clause_hdr_word_nonneg;
    apply Zlength_nonneg.
Qed.

Lemma proof_of_clause_simplify_partial_solve_wit_5_pure : clause_simplify_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process;
    bind_fact ( retval = clause_hdr_word is_learnt (Zlength clause_words) ÷ 2 ) as H_retval;
    bind_fact ( clause_simplify_scan_inv n clause_words assigns0 i ) as H_clause_simplify_scan_inv;
    unfold clause_simplify_scan_inv in H_clause_simplify_scan_inv;
    destruct H_clause_simplify_scan_inv as (Hi & Halen & Hlits & Hcells & Hprefix);
    assert (Hhdr : 0 <= clause_hdr_word is_learnt (Zlength clause_words))
      by (apply clause_hdr_word_nonneg; apply Zlength_nonneg);
    rewrite zdiv_equiv in H_retval by lia;
    rewrite clause_hdr_word_div2 in H_retval by apply Zlength_nonneg;
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_clause_simplify_partial_solve_wit_6_pure : clause_simplify_partial_solve_wit_6_pure.
Proof.
  msat_clause_simplify_lit_range_pure.
Qed.

(* ===== clause_simplify safety wits (2 proofs) ===== *)
Lemma proof_of_clause_simplify_safety_wit_11 : clause_simplify_safety_wit_11.
Proof.
  msat_clause_simplify_hdr_word_safety_p8.
Qed.

Lemma proof_of_clause_simplify_safety_wit_12 : clause_simplify_safety_wit_12.
Proof.
  msat_clause_simplify_hdr_word_safety_p8.
Qed.

(* ===== order_select safety wits (6 proofs) ===== *)
Lemma proof_of_order_select_safety_wit_30 : order_select_safety_wit_30.
Proof.
  msat_order_select_sift_child_bound_p8 size.
Qed.

Lemma proof_of_order_select_safety_wit_31 : order_select_safety_wit_31.
Proof.
  msat_order_select_sift_child_bound_p8 size.
Qed.

Lemma proof_of_order_select_safety_wit_34 : order_select_safety_wit_34.
Proof.
  msat_order_select_sift_child_bound_p8 size.
Qed.

Lemma proof_of_order_select_safety_wit_35 : order_select_safety_wit_35.
Proof.
  msat_order_select_sift_child_bound_p8 size.
Qed.

Lemma proof_of_order_select_safety_wit_38 : order_select_safety_wit_38.
Proof.
  msat_order_select_sift_child_bound_p8 size.
Qed.

Lemma proof_of_order_select_safety_wit_39 : order_select_safety_wit_39.
Proof.
  msat_order_select_sift_child_bound_p8 size.
Qed.

(* ===== order_unassigned partial_solve wits (2 proofs) ===== *)
Lemma proof_of_order_unassigned_partial_solve_wit_11_pure : order_unassigned_partial_solve_wit_11_pure.
Proof.
  Unfold; left; intros.
  bind_fact ( Znth (v_pre - 0) orderpos0 0 = -1 ) as H_Znth.
  assert (Hmissing0 : Znth v_pre orderpos0 0 = -1).
  { replace (v_pre - 0) with v_pre in H_Znth by lia. exact H_Znth. }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_unassigned_partial_solve_wit_12_pure : order_unassigned_partial_solve_wit_12_pure.
Proof.
  (* The conjunct [Zlength activity0 = n] was ABSORBED into the first conjunct,
     which now reads [order_update_pre (Zlength activity0) ...]: three goals
     became two.  Rewrite the goal back to [n] and the original script applies. *)
  Unfold; left; intros.
  bind_fact ( Zlength activity0 = n ) as H_Zlength.
  rewrite H_Zlength.
  pose proof (Zlength_nonneg (heap0 ++ v_pre :: nil)) as Hlen_nonneg.
  entailer_with ltac:(lia).
Qed.

(* ===== order_unassigned return wits (1 proofs) ===== *)
Lemma proof_of_order_unassigned_return_wit_3 : order_unassigned_return_wit_3.
Proof.
  Unfold; left; intros.
  msat_order_unassigned_noop_return order_ptr.
Qed.

(* ===== order_unassigned which_implies wits (3 proofs) ===== *)
Lemma proof_of_order_unassigned_which_implies_wit_1 : order_unassigned_which_implies_wit_1.
Proof.
  Unfold; intros.
  bind_fact ( order_unassigned_pre n v order_cap heap0 orderpos0 ) as H_order_unassigned_pre.
  pose proof H_order_unassigned_pre as Hun.
  destruct Hun as (Hwf & Hv & Hcap & Hlen & Htwon).
  pose proof (heap_wf_orderpos_length n
    {| mh_heap := heap0; mh_orderpos := orderpos0 |} Hwf) as Hoplen.
  cbn [mh_orderpos] in Hoplen.
  destruct (Z.eq_dec (Znth v orderpos0 (-1)) (-1))
    as [Hmissing | Hpresent].
  - assert (Hshort : Zlength heap0 < n).
    { apply (heap_wf_missing_length n
        {| mh_heap := heap0; mh_orderpos := orderpos0 |} v).
      + lia.
      + exact Hwf.
      + exact Hv.
      + exact Hmissing. }
    Left. entailer_with ltac:(lia).
  - assert (Hpresent0 : Znth (v - 0) orderpos0 0 <> -1).
    { replace (v - 0) with v by lia.
      rewrite <- (Znth_indep orderpos0 v (-1) 0) by lia.
      exact Hpresent. }
    Right. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_order_unassigned_which_implies_wit_3 : order_unassigned_which_implies_wit_3.
Proof.
  Unfold; left; intros.
  apply IntArray.full_to_seg.
Qed.

Lemma proof_of_order_unassigned_which_implies_wit_4 : order_unassigned_which_implies_wit_4.
Proof.
  Unfold; left; intros.
  bind_fact ( order_unassigned_pre n v order_cap heap0 orderpos0 ) as H_order_unassigned_pre.
  bind_fact ( Znth v orderpos0 0 = -1 ) as H_Znth.
  pose proof H_order_unassigned_pre as Hun.
  destruct Hun as (Hwf & Hv & Hcap & Hlen & Htwon).
  pose proof (heap_wf_orderpos_length n
    {| mh_heap := heap0; mh_orderpos := orderpos0 |} Hwf) as Hoplen.
  cbn [mh_orderpos] in Hoplen.
  assert (Hmissing : Znth v orderpos0 (-1) = -1).
  { rewrite (Znth_indep orderpos0 v (-1) 0) by lia. exact H_Znth. }
  assert (Hinsert : order_heap_wf n (heap0 ++ v :: nil)
      (replace_Znth v (Zlength heap0) orderpos0)).
  { unfold order_heap_wf.
    change (heap_wf n
      {| mh_heap := heap0 ++ v :: nil;
         mh_orderpos := replace_Znth v (Zlength heap0) orderpos0 |}).
    apply (heap_wf_insert n
      {| mh_heap := heap0; mh_orderpos := orderpos0 |} v);
      cbn [mh_heap mh_orderpos]; assumption. }
  assert (Hpresent :
      Znth v (replace_Znth v (Zlength heap0) orderpos0) (-1) <> -1).
  { rewrite Znth_replace_Znth_Same by lia.
    pose proof (Zlength_nonneg heap0). lia. }
  entailer_with ltac:(lia).
  unfold order_update_pre.
  split; [exact Hinsert |].
  split; [exact Hv | exact Hpresent].
Qed.

(* ===== solver_analyze partial_solve wits (13 proofs) ===== *)
Lemma proof_of_solver_analyze_partial_solve_wit_6_pure : solver_analyze_partial_solve_wit_6_pure.
Proof.
  Unfold; left; intros; entailer_with ltac:(lia).
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase_2 c Ccur_2 words_2 cnt ind p )
    as H_analyze_resolution_loop_inv.
  destruct H_analyze_resolution_loop_inv as [Hready _].
  destruct (analysis_cancel_ready_reason_core
    anz_n anz_F anz_A_arr K Mcur anz_focus Hready) as [Hsize _].
  symmetry; exact Hsize.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_8_pure : solver_analyze_partial_solve_wit_8_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_8_pure, solver_analyze_open_at.
  Unfold; left; intros.
  sep_apply (valid_store_ptr (&( "c" )) c).
  (* valid_store_ptr yields [valid_ptr_value c], i.e. [0 <= c /\ c <= addr_max_unsigned], and micromega cannot see
     inside that definition -- without this unfold the entailer leaves [0 <= c] open. *)
  unfold valid_ptr_value in *.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_10_pure : solver_analyze_partial_solve_wit_10_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_10_pure, solver_analyze_open_at.
  Unfold; left; intros.
  bind_fact ( reason_target_wf anz_n Mcur_2 x c Ccur_2 ) as H_reason_target_wf.
  bind_fact ( is_tag c = msat_true ) as H_is_tag.
  unfold reason_target_wf in H_reason_target_wf.
  destruct H_reason_target_wf as [_ [_ [_ [_ Hshape]]]].
  destruct Hshape as [[_ [Hcpos Hlit]] | [co [Hnot_tag _]]].
  - unfold lit_wf_c in Hlit.
    entailer_with ltac:(lia); lia.
  - rewrite H_is_tag in Hnot_tag; discriminate.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_11_pure : solver_analyze_partial_solve_wit_11_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_11_pure, solver_analyze_open_at.
  Unfold; left; intros; entailer_with ltac:(lia).
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase_2 c Ccur words_2 cnt ind p ) as
    H_analyze_resolution_loop_inv.
  exact (proj1 H_analyze_resolution_loop_inv).
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_12_pure : solver_analyze_partial_solve_wit_12_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_12_pure, solver_analyze_open_at.
  msat_analyze_reason_target_lit_bound_p8.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_13_pure : solver_analyze_partial_solve_wit_13_pure.
Proof.
  unfold solver_analyze_partial_solve_wit_13_pure, solver_analyze_open_at.
  msat_analyze_reason_target_lit_bound_p8.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_17_pure : solver_analyze_partial_solve_wit_17_pure.
Proof.
  msat_analyze_reason_target_lit_bound_p8.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_19_pure : solver_analyze_partial_solve_wit_19_pure.
Proof.
  msat_analyze_reason_target_lit_bound_p8.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_21_pure : solver_analyze_partial_solve_wit_21_pure.
Proof.
  Unfold.
  right; intros.
  split_pures;
    dump_pre_spatial; congruence.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_22_pure : solver_analyze_partial_solve_wit_22_pure.
Proof.
  msat_analyze_reason_target_lit_bound_p8.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_24_pure : solver_analyze_partial_solve_wit_24_pure.
Proof.
  msat_analyze_reason_target_lit_bound_p8.
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_25_pure : solver_analyze_partial_solve_wit_25_pure.
Proof.
  Unfold; left; intros.
  assert (Hvec :
    veci_rep &((s_pre) # "solver_t" ->ₛ "tagged")
      (ms_tagged Mcur) (ms_tagged_cap Mcur) |--
    “ 0 <= Zlength (ms_tagged Mcur) <= ms_tagged_cap Mcur /\
      0 < ms_tagged_cap Mcur <= INT_MAX ”).
  { unfold veci_rep. Intros backing. unfold veci_rep_at. entailer_with ltac:(lia). }
  sep_apply Hvec.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_partial_solve_wit_27_pure : solver_analyze_partial_solve_wit_27_pure.
Proof.
  msat_analyze_reason_target_lit_bound_p8.
Qed.

(* ===== solver_analyze which_implies wits (10 proofs) ===== *)
Lemma proof_of_solver_analyze_which_implies_wit_8 : solver_analyze_which_implies_wit_8.
Proof.
  LLM_pre_process ltac:(lia).
  prop_apply (CharArray.full_Zlength tags anz_n
    (replace_Znth (lit_var_c q) 1 (ms_tags Mcur))).
  Exists (replace_Znth (lit_var_c q) 1 (ms_tags Mcur)).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_10 : solver_analyze_which_implies_wit_10.
Proof.
  Unfold. right. intros.
  bind_fact (Mtag = analyze_tag_step_msolver Mcur tags_j tagged_j tagged_cap_j
    activity_j orderpos_j heap_j var_inc_j) as Htag.
  bind_fact (solver_shape Mtag) as Hshape.
  bind_fact (anz_n = ms_size Mtag) as Hsize.
  assert (Hqtail : ms_qtail Mtag = ms_qtail Mcur) by (rewrite Htag; reflexivity).
  replace (ms_prob Mcur) with (ms_prob Mtag) by (rewrite Htag; reflexivity).
  replace (ms_learnt Mcur) with (ms_learnt Mtag) by (rewrite Htag; reflexivity).
  replace (ms_binary Mcur) with (ms_binary Mtag) by (rewrite Htag; reflexivity).
  replace (ms_binary_lits Mcur) with (ms_binary_lits Mtag) by (rewrite Htag; reflexivity).
  unfold msat_false.
  sep_apply (solver_analyze_open_at_rep s Mtag anz_n activity_ptr_loop
    orderpos_ptr_loop reasons levels trail tags anz_wl Hshape (eq_sym Hsize)).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_11 : solver_analyze_which_implies_wit_11.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p ) as
    H_analyze_resolution_loop_inv.
  bind_fact ( is_tag c = msat_false ) as H_is_tag.
  pose proof (analyze_resolution_real_clause_source__analyze
    anz_n anz_F anz_A_arr K Mcur anz_focus phase c Ccur words cnt ind p
    H_analyze_resolution_loop_inv H_is_tag) as Hsource.
  destruct Hsource as
    [[Hbinary [HC Hwf]] | [co [Hbinary [Hin [HC Hwf]]]]].
  - subst c Ccur.
    unfold MiniSatClause.rep at 1.
    Exists false (ms_binary_lits Mcur).
    unfold analysis_clause_remainder.
    Left. entailer_with ltac:(int_auto).
  - unfold msolver_db in Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply in_split in Hin. destruct Hin as [pre [post Hprob]].
      rewrite Hprob.
      sep_apply (clause_db_rep_app_elim pre ((c, co) :: post)).
      rewrite clause_db_rep_cons.
      unfold MiniSatClause.rep at 1.
      Exists (co_learnt co) (co_lits co).
      unfold analysis_clause_remainder.
      Right. unfold clause_db_pair_remainder.
      Left. Exists co pre post. entailer_with ltac:(lia).
      * cbn [fst snd msat_false].
        unfold msat_false.
        set_String_name. sepcon_assoc_change. sepcon_cancel.
    + apply in_split in Hin. destruct Hin as [pre [post Hlearnt]].
      rewrite Hlearnt.
      sep_apply (clause_db_rep_app_elim pre ((c, co) :: post)).
      rewrite clause_db_rep_cons.
      unfold MiniSatClause.rep at 1.
      Exists (co_learnt co) (co_lits co).
      unfold analysis_clause_remainder.
      Right. unfold clause_db_pair_remainder.
      Right. Exists co pre post. entailer_with ltac:(lia).
      * cbn [fst snd msat_false].
        unfold msat_false.
        set_String_name. sepcon_assoc_change. sepcon_cancel.
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_12 : solver_analyze_which_implies_wit_12.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_focus_clause_db_p8 c Mcur ( Intros_p Hb; bind_fact ( is_learnt_now = msat_true ) as Hlt;
    destruct Hb as [Hc [Htag Hlits]]; unfold msat_true, msat_false in Hlt, Htag; congruence ).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_13 : solver_analyze_which_implies_wit_13.
Proof.
  LLM_pre_process ltac:(lia).
  msat_analyze_focus_clause_db_p8 c Mcur ( Intros_p Hb; destruct Hb as [Hc [Htag Hlits]];
    subst c is_learnt_now clause_words; unfold MiniSatClause.rep; entailer_with ltac:(int_auto);
    [ apply Zlength_nonneg | msat_analyze_clause_ptr_even_p8 ] ).
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_14 : solver_analyze_which_implies_wit_14.
Proof.
  unfold solver_analyze_which_implies_wit_14, solver_analyze_open_at.
  LLM_pre_process ltac:(lia).
  bind_fact ( is_tag c = msat_false ) as H_is_tag.
  bind_fact ( analyze_resolution_loop_inv anz_n anz_F anz_A_arr K Mact anz_focus phase c Ccur words cnt ind p ) as
    H_analyze_resolution_loop_inv.
  pose proof (analyze_resolution_real_clause_source__analyze
    anz_n anz_F anz_A_arr K Mact anz_focus phase c Ccur words cnt ind p
    H_analyze_resolution_loop_inv H_is_tag) as Hsource.
  destruct Hsource as
    [[Hbinary [HC Hwf]] | [co [Hbinary [Hin [HC Hwf]]]]].
  - subst c Ccur.
    unfold MiniSatClause.rep at 1.
    Exists false activity_ptr_loop orderpos_ptr_loop (ms_binary_lits Mact).
    unfold analysis_clause_remainder.
    Left. entailer_with ltac:(int_auto).
  - unfold msolver_db in Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply in_split in Hin. destruct Hin as [pre [post Hprob]].
      rewrite Hprob.
      sep_apply (clause_db_rep_app_elim pre ((c, co) :: post)).
      rewrite clause_db_rep_cons.
      unfold MiniSatClause.rep at 1.
      Exists (co_learnt co) activity_ptr_loop orderpos_ptr_loop (co_lits co).
      unfold analysis_clause_remainder.
      Right. unfold clause_db_pair_remainder.
      Left. Exists co pre post. entailer_with ltac:(lia).
      * cbn [fst snd msat_false].
        unfold msat_false.
        set_String_name. sepcon_assoc_change. sepcon_cancel.
    + apply in_split in Hin. destruct Hin as [pre [post Hlearnt]].
      rewrite Hlearnt.
      sep_apply (clause_db_rep_app_elim pre ((c, co) :: post)).
      rewrite clause_db_rep_cons.
      unfold MiniSatClause.rep at 1.
      Exists (co_learnt co) activity_ptr_loop orderpos_ptr_loop (co_lits co).
      unfold analysis_clause_remainder.
      Right. unfold clause_db_pair_remainder.
      Right. Exists co pre post. entailer_with ltac:(lia).
      * cbn [fst snd msat_false].
        unfold msat_false.
        set_String_name. sepcon_assoc_change. sepcon_cancel.
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_15 : solver_analyze_which_implies_wit_15.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( Forall (lit_wf_c anz_n) clause_words2 ) as H_Forall.
  bind_fact ( q = Znth (j - 0) clause_words2 0 ) as H_q.
  entailer_with ltac:(lia);
    replace (j - 0) with j in H_q by lia;
      subst q;
      pose proof (Forall_Znth_elim Z (lit_wf_c anz_n) clause_words2 0 j
        H_Forall ltac:(lia)) as Hwf;
      pose proof (lit_var_c_in_range anz_n (Znth j clause_words2 0) Hwf)
        as Hrange;
      lia.
Qed.

Lemma proof_of_solver_analyze_which_implies_wit_20 : solver_analyze_which_implies_wit_20.
Proof. exact proof_of_solver_analyze_which_implies_wit_12. Qed.

Lemma proof_of_solver_analyze_which_implies_wit_21 : solver_analyze_which_implies_wit_21.
Proof. exact proof_of_solver_analyze_which_implies_wit_11. Qed.

Lemma proof_of_solver_analyze_which_implies_wit_23 : solver_analyze_which_implies_wit_23.
Proof. exact proof_of_solver_analyze_which_implies_wit_8. Qed.

(* ===== solver_canceluntil_capacity entail wits (4 proofs) ===== *)
Lemma proof_of_solver_canceluntil_capacity_entail_wit_2 : solver_canceluntil_capacity_entail_wit_2.
Proof.
  unfold solver_canceluntil_capacity_entail_wit_2, solver_cancel_open_at.
  Unfold.
  right.
  intros.
  bind_fact ( order_unassigned_post (ms_size M0) retval order_cap_now_2 order_now_2 orderpos_now_2 order_cap1 heap1
    orderpos1 ) as H_order_unassigned_post.
  bind_fact ( retval = lit_var_c (Znth (c - 0) (mt_trail (ms_core M0)) 0) ) as H_retval.
  bind_fact ( solver_propagation_inv n F A_arr K M0 ) as H_solver_propagation_inv.
  bind_fact ( capacity_reinsert_loop_inv M0 level_pre c order_cap_now_2 order_now_2 orderpos_now_2 ) as
    H_capacity_reinsert_loop_inv.
  replace (c - 0) with c in H_retval by lia.
  unfold capacity_reinsert_loop_inv in H_capacity_reinsert_loop_inv.
  assert (Hlevel : level_pre = 0) by tauto.
  assert (Hclow : mt_qhead (ms_core M0) - 1 <= c) by tauto.
  assert (Hchigh : c < ms_qtail M0) by tauto.
  assert (Hcaplo : ms_order_cap M0 <= order_cap_now_2) by tauto.
  assert (Hcaphi : order_cap_now_2 <= INT_MAX) by tauto.
  assert (Hcappos : 0 < order_cap_now_2) by tauto.
  assert (Hlen0 : Zlength order_now_2 <= order_cap_now_2) by tauto.
  assert (Hwf0 : heap_wf (ms_size M0)
    (heap_of_lists order_now_2 orderpos_now_2)) by tauto.
  assert (Hincl0 : incl (ms_order M0) order_now_2) by tauto.
  assert (Hre : cancel_reinserted
    (heap_of_lists order_now_2 orderpos_now_2)
    (mt_trail (ms_core M0)) (c + 1) (ms_qtail M0)) by tauto.
  unfold order_unassigned_post, order_heap_wf in H_order_unassigned_post.
  assert (Hwf1 : heap_wf (ms_size M0)
    (heap_of_lists heap1 orderpos1)) by tauto.
  assert (Hcapgrow : order_cap_now_2 <= order_cap1) by tauto.
  assert (Hcapmax : order_cap1 <= INT_MAX) by tauto.
  assert (Hlen1 : Zlength heap1 <= order_cap1) by tauto.
  assert (Hcase :
    (Znth retval orderpos_now_2 (-1) = -1 /\
      Permutation heap1 (order_now_2 ++ retval :: nil)) \/
    (Znth retval orderpos_now_2 (-1) <> -1 /\
      heap1 = order_now_2 /\ orderpos1 = orderpos_now_2 /\
      order_cap1 = order_cap_now_2)) by tauto.
  pose proof (fun i => solver_propagation_trail_var_range__canceluntil_cap
    n F A_arr K M0 i H_solver_propagation_inv) as Hrange.
  assert (Hv : 0 <= retval < ms_size M0).
  { rewrite H_retval. apply Hrange. lia. }
  assert (Hgrowth : incl order_now_2 heap1 /\ In retval heap1).
  { destruct Hcase as [[Hmissing Hperm] |
      [Hpresent [Hheap [Hpos Hcap]]]].
    - split.
      + intros x Hx.
        apply (Permutation_in x (Permutation_sym Hperm)).
        apply in_or_app. left. exact Hx.
      + apply (Permutation_in retval (Permutation_sym Hperm)).
        apply in_or_app. right. simpl. auto.
    - subst heap1. subst orderpos1. subst order_cap1.
      split; [apply incl_refl|].
      apply (proj2 (heap_wf_in_iff (ms_size M0)
        (heap_of_lists order_now_2 orderpos_now_2) retval Hwf0 Hv)).
      exact Hpresent. }
  destruct Hgrowth as [Hincl_growth Htarget].
  assert (Hincl1 : incl (ms_order M0) heap1).
  { intros x Hx. apply Hincl_growth. apply Hincl0. exact Hx. }
  assert (Hcancel : cancel_reinserted
    (heap_of_lists heap1 orderpos1) (mt_trail (ms_core M0))
    (c - 1 + 1) (ms_qtail M0)).
  { unfold cancel_reinserted in *.
    intros i Hi.
    assert (Hvi : 0 <= lit_var_c (Znth i (mt_trail (ms_core M0)) 0) <
      ms_size M0) by (apply Hrange; lia).
    apply (proj1 (heap_wf_in_iff (ms_size M0)
      (heap_of_lists heap1 orderpos1)
      (lit_var_c (Znth i (mt_trail (ms_core M0)) 0)) Hwf1 Hvi)).
    destruct (Z.eq_dec i c) as [-> | Hne].
    - rewrite <- H_retval. exact Htarget.
    - apply Hincl_growth.
      apply (proj2 (heap_wf_in_iff (ms_size M0)
        (heap_of_lists order_now_2 orderpos_now_2)
        (lit_var_c (Znth i (mt_trail (ms_core M0)) 0)) Hwf0 Hvi)).
      apply Hre. lia. }
  Exists order_cap1 heap1 orderpos1.
  unfold capacity_reinsert_loop_inv.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_canceluntil_capacity_entail_wit_3_1 : solver_canceluntil_capacity_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  match goal with
  | H : capacity_reinsert_loop_inv M0 level_pre c order_cap_now
      order_now orderpos_now |- _ => rename H into Hloop
  end.
  match goal with
  | H : solver_propagation_inv n F A_arr K M0 |- _ =>
      rename H into Hinv0
  end.
  match goal with
  | H : solver_capacity_exhausted M0 |- _ => rename H into Hcap0
  end.
  match goal with
  | H : msolver_seed_shadow M0 |- _ => rename H into Hseed0
  end.
  match goal with
  | H : c < mt_qhead (ms_core M0) |- _ => rename H into Hclt
  end.
  unfold capacity_reinsert_loop_inv in Hloop.
  assert (Hlevel : level_pre = 0) by tauto.
  assert (Hclow : mt_qhead (ms_core M0) - 1 <= c) by tauto.
  assert (Hwf : heap_wf (ms_size M0)
    (heap_of_lists order_now orderpos_now)) by tauto.
  assert (Hincl : incl (ms_order M0) order_now) by tauto.
  assert (Hre : cancel_reinserted
    (heap_of_lists order_now orderpos_now)
    (mt_trail (ms_core M0)) (c + 1) (ms_qtail M0)) by tauto.
  assert (Hcovers : heap_covers (ms_size M0)
    (heap_of_lists order_now orderpos_now)
    (mt_assigns (ms_core M0)) (mt_trail (ms_core M0))
    (mt_qhead (ms_core M0))).
  { eapply solver_propagation_reinserted_heap_covers__canceluntil_cap;
      eauto using Hinv0, Hclt. }
  assert (Hprojinv : solver_propagation_inv n F A_arr K
    (msolver_heap_project M0 orderpos_now order_now order_cap_now)).
  { eapply solver_propagation_inv_heap_project__canceluntil_cap; eauto. }
  assert (Hcapproj : solver_capacity_exhausted
    (msolver_heap_project M0 orderpos_now order_now order_cap_now)).
  { unfold solver_capacity_exhausted, msolver_heap_project,
      msolver_core_heap_update in *. simpl in *. exact Hcap0. }
  assert (Hseedproj : msolver_seed_shadow
    (msolver_heap_project M0 orderpos_now order_now order_cap_now)).
  { unfold msolver_seed_shadow, msolver_heap_project,
      msolver_core_heap_update in *. simpl in *. exact Hseed0. }
  pose proof
    (solver_propagation_cancel_pre_zero_pure__canceluntil_cap
      n F A_arr K
      (msolver_heap_project M0 orderpos_now order_now order_cap_now)
      Hprojinv) as Hpre.
  Exists orderpos_now order_now order_cap_now.
  (* The five uninitialised tails arrive folded as
     [solver_cancel_undef_tail M0 ...] on the left; [solver_cancel_pre] on the
     right spells them raw, so open the bundle here. *)
  unfold solver_cancel_pre, solver_cancel_undef_tail.
  entailer_with ltac:(int_auto).
  - unfold solver_cancel_owned,
      solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep, solver_vecs_rep,
      solver_trail_array_rep, solver_cancel_frame.
    Intros tgs.
    Exists activity_ptr assigns_ptr orderpos_ptr reasons_ptr trail_ptr tgs.
    change (solver_fp_rep s_pre M0) with
      (solver_fp_rep s_pre
        (msolver_heap_project M0 orderpos_now order_now order_cap_now)) at 1.
    unfold msolver_heap_project, msolver_core_heap_update.
    cbn.
    entailer_with ltac:(int_auto).
    unfold veci_size_addr, veci_cap_addr, veci_ptr_addr.
    csimpl. entailer_with ltac:(lia).
    unfold solver_fp_rep, DoubleArray.seg, IntArray.seg,
      PtrArray.seg, CharArray.seg, msolver_heap_project,
      msolver_core_heap_update.
    simpl. cancel.
    unfold store_double, bits_of_double_value.
    simpl. entailer_with ltac:(lia).
    (* Convert the array callbacks before commuting the two remaining arrays. *)
    match goal with
    | |- ?P ** ?Q |-- _ => change (P ** Q |-- Q ** P)
    end.
    entailer_with lia.
  - rewrite Hlevel.
    exact (proj1 (proj2 (proj2 Hpre))).
Qed.

Lemma proof_of_solver_canceluntil_capacity_entail_wit_3_2 : solver_canceluntil_capacity_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  bind_fact ( solver_propagation_inv n F A_arr K M0 ) as H_solver_propagation_inv.
  bind_fact ( capacity_reinsert_loop_inv M0 level_pre c order_cap_now order_now orderpos_now ) as
    H_capacity_reinsert_loop_inv.
  exfalso.
  unfold capacity_reinsert_loop_inv in H_capacity_reinsert_loop_inv.
  destruct H_capacity_reinsert_loop_inv as [Hlevel _].
  subst level_pre.
  pose proof
    (solver_propagation_bound_le_qhead__canceluntil_cap
       n F A_arr K M0 H_solver_propagation_inv) as Hbound.
  lia.
Qed.

Lemma proof_of_solver_canceluntil_capacity_entail_wit_3_3 : solver_canceluntil_capacity_entail_wit_3_3.
Proof.
  aggressive_pre_process.
  bind_fact ( solver_propagation_inv n F A_arr K M0 ) as H_solver_propagation_inv.
  pose proof (Zlength_nonneg (mt_lim (ms_core M0))) as Hlen0.
  assert (Hlen : Zlength (mt_lim (ms_core M0)) = 0) by lia.
  assert (Hnil : mt_lim (ms_core M0) = z_nil).
  { destruct (mt_lim (ms_core M0)) as [|b rest] eqn:Hlim;
      [reflexivity|].
    rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg rest). lia. }
  assert (Hproj :
    msolver_heap_project M0 (ms_orderpos M0) (ms_order M0)
      (ms_order_cap M0) = M0).
  { unfold msolver_heap_project, msolver_core_heap_update.
    destruct M0. reflexivity. }
  pose proof (msolver_inv_ctx_of_propagation n F A_arr K M0
    H_solver_propagation_inv) as Hctx.
  destruct (propagation_inv_context_facts__analyze n F A_arr K M0
    H_solver_propagation_inv) as [_ [_ [_ [Hheap _]]]].
  destruct (msolver_inv_ctx_core_facts n F A_arr K M0 Hctx)
    as [Hsize [Htrailwf Hheapwf]].
  pose proof (msolver_inv_ctx_shape n F A_arr K M0 Hctx) as Hshape.
  unfold propagation_heap_ready in Hheap.
  destruct Hheap as [Hcovers | [Hpos _]]; [|rewrite Hlen in Hpos; lia].
  assert (HcoversM :
    heap_covers (ms_size M0) (msolver_heap M0)
      (mt_assigns (ms_core M0)) (mt_trail (ms_core M0))
      (mt_qhead (ms_core M0))).
  { rewrite <- Hsize. exact Hcovers. }
  assert (Hpre :
    solver_shape M0 /\ mtrail_wf (ms_size M0) (ms_core M0) /\
    cancel_bound_ready M0 level_pre /\
    heap_wf (ms_size M0) (msolver_heap M0) /\
    0 <= level_pre <= Zlength (mt_lim (ms_core M0))).
  { split; [exact Hshape|].
    split; [rewrite <- Hsize; exact Htrailwf|].
    split; [left; lia|].
    split; [rewrite <- Hsize; exact Hheapwf|].
    lia. }
  Exists (ms_orderpos M0) (ms_order M0) (ms_order_cap M0).
  rewrite Hproj.
  (* Open the folded undef tails, as in
     [proof_of_solver_canceluntil_capacity_entail_wit_3_1]. *)
  unfold solver_cancel_pre, cancel_bound_ready, solver_cancel_undef_tail.
  entailer_with ltac:(lia).
  - unfold solver_cancel_owned,
      solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep, solver_vecs_rep,
      solver_trail_array_rep, solver_cancel_frame.
    Intros tgs.
    Exists activity_ptr assigns_ptr orderpos_ptr reasons_ptr trail_ptr tgs.
    msat_manual_entailer_with ltac:(int_auto).
Qed.

(* ===== solver_canceluntil_capacity partial_solve wits ===== *)


Lemma proof_of_solver_canceluntil_capacity_partial_solve_wit_8_pure :
  solver_canceluntil_capacity_partial_solve_wit_8_pure.
Proof.
  aggressive_pre_process;
    apply derivable1s_coq_prop_r;
    replace (c - 0) with c by lia; assumption.
Qed.

Lemma proof_of_solver_canceluntil_capacity_partial_solve_wit_9_pure :
  solver_canceluntil_capacity_partial_solve_wit_9_pure.
Proof.
  aggressive_pre_process;
    apply derivable1s_coq_prop_r;
    replace (c - 0) with c in * by lia;
    subst retval; assumption.
Qed.

(* ===== solver_canceluntil_capacity return wits (1 proofs) ===== *)
Lemma proof_of_solver_canceluntil_capacity_return_wit_1 : solver_canceluntil_capacity_return_wit_1.
Proof.
  Unfold.
  left. intros level_pre s_pre wl M K A_arr F n levels_ptr
    order_cap_ready order_ready orderpos_ready Mready; intros.
  subst level_pre.
  bind_fact ( Mready = msolver_heap_project M orderpos_ready order_ready order_cap_ready ) as H_Mready.
  bind_fact ( heap_covers (ms_size Mready) (msolver_heap Mready) (mt_assigns (ms_core Mready)) (mt_trail (ms_core
    Mready)) (mt_qhead (ms_core Mready)) ) as H_heap_covers.
  bind_fact ( solver_propagation_inv n F A_arr K Mready ) as H_solver_propagation_inv.
  bind_fact ( solver_capacity_exhausted Mready ) as H_solver_capacity_exhausted.
  bind_fact ( msolver_seed_shadow Mready ) as H_msolver_seed_shadow.
  assert (Hvariable_cap : ms_cap Mready = ms_cap M).
  { rewrite H_Mready. reflexivity. }
  assert (Hbase_ready : minisat_base_watch_completed M ->
      minisat_base_watch_completed Mready).
  { intro Hbase. rewrite H_Mready. exact Hbase. }
  pose proof (msolver_inv_ctx_of_propagation n F A_arr K Mready
    H_solver_propagation_inv) as Hctx.
  assert (Hweak : solver_propagation_weak n F A_arr K Mready).
  { split; [exact (proj1 H_solver_propagation_inv)|exact Hctx]. }
  destruct (solver_propagation_weak_core_facts__propagate
    n F A_arr K Mready Hweak) as (Hsize & Hshape & Hdb & Hwm & Htrail).
  pose proof (proj1 (proj2 (propagation_inv_context_facts__analyze
    n F A_arr K Mready H_solver_propagation_inv))) as Hprop.
  unfold solver_cancel_post.
  Split.
  - Intros.
    rewrite <- H_Mready in H |- *.
    assert (Hlim : Zlength (mt_lim (ms_core Mready)) = 0).
    { pose proof (Zlength_nonneg (mt_lim (ms_core Mready))). lia. }
    assert (Hready : solver_root_rebuild_ready n F Mready).
    { apply solver_propagation_root_ready_empty__canceluntil_cap
        with (A_arr := A_arr) (K := K); assumption. }
    assert (Hcomplete : minisat_base_watch_completed M ->
        minisat_watch_completed Mready).
    { intro Hbase. exact (minisat_base_completion_at_depth_zero__api_reentry
        n Mready Htrail Hdb Hlim (Hbase_ready Hbase)). }
    unfold solver_cancel_capacity_post.
    Exists Mready.
    split_pure_spatial.
    + apply solver_cancel_join_rep.
    + entailer_with ltac:(lia).
  - Intros orderpos_after order_after order_cap_after.
    rewrite <- H_Mready in H |- *.
    destruct H as (Hlevel & Hcap & Hheap & Hincl & Hre).
    set (Mpost := msolver_cancel_project Mready 0
      orderpos_after order_after order_cap_after (ms_root_level Mready)).
    assert (Hready : solver_root_rebuild_ready n F Mpost).
    { unfold Mpost. apply solver_propagation_cancel_root_ready__canceluntil_cap
        with (A_arr := A_arr) (K := K).
      - exact H_solver_propagation_inv.
      - lia.
      - exact Hcap.
      - exact Hheap.
      - exact Hincl.
      - exact H_heap_covers.
      - exact Hre. }
    assert (Hcapacity : solver_capacity_exhausted Mpost).
    { unfold Mpost, solver_capacity_exhausted, msolver_cancel_project,
        msolver_core_heap_update. simpl. exact H_solver_capacity_exhausted. }
    assert (Hseed : msolver_seed_shadow Mpost).
    { unfold Mpost, msolver_seed_shadow, msolver_cancel_project,
        msolver_core_heap_update. simpl. exact H_msolver_seed_shadow. }
    assert (Hpost_variable_cap : ms_cap Mpost = ms_cap M).
    { change (ms_cap Mready = ms_cap M). exact Hvariable_cap. }
    assert (Hcomplete : minisat_base_watch_completed M ->
        minisat_watch_completed Mpost).
    { intro Hbase. unfold Mpost.
      apply (minisat_base_completion_cancel_zero__api_reentry
        n Mready orderpos_after order_after order_cap_after
        (ms_root_level Mready) Htrail Hdb ltac:(lia)).
      - exact (Forall_Znth_elim _ _ _ 0 0 Hprop Hlevel).
      - exact (Hbase_ready Hbase). }
    unfold solver_cancel_capacity_post.
    Exists Mpost.
    split_pure_spatial.
    + unfold Mpost. apply solver_cancel_project_join_rep.
    + msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_canceluntil_capacity which_implies wits (2 proofs) ===== *)
Lemma proof_of_solver_canceluntil_capacity_which_implies_wit_1 :
  solver_canceluntil_capacity_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  unfold solver_cancel_open_at, solver_prepare_capacity_pre, solver_rep_wl, solver_rep_levels_wl_at,
    solver_cancel_owned, solver_nonlevel_rep_at,
    solver_nonlevel_rep_nostats_at, solver_scalars_rep, solver_vecs_rep,
    solver_trail_array_rep, solver_cancel_frame, solver_cancel_undef_tail.
  Intros levels_ptr activity_ptr assigns_ptr orderpos_ptr reasons_ptr
    trail_ptr tgs.
  Exists levels_ptr activity_ptr assigns_ptr orderpos_ptr reasons_ptr trail_ptr.
  entailer_with ltac:(lia).
  Exists tgs.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_canceluntil_capacity_which_implies_wit_2 : solver_canceluntil_capacity_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  all: (bind_fact ( solver_propagation_inv n F A_arr K M0 ) as H_solver_propagation_inv);
    (bind_fact ( capacity_reinsert_loop_inv M0 level c order_cap_now order_now orderpos_now ) as
      H_capacity_reinsert_loop_inv);
    (bind_fact ( c >= mt_qhead (ms_core M0) ) as H_c);
    (pose proof
      (capacity_reinsert_current_facts__canceluntil_cap
         n F A_arr K M0 level c order_cap_now order_now orderpos_now
         H_solver_propagation_inv H_capacity_reinsert_loop_inv H_c) as Hfacts);
    (try apply derivable1s_coq_prop_r);
    (tauto).
Qed.

(* ===== solver_prepare_public_capacity_exit entail wits (2 proofs) ===== *)
Lemma proof_of_solver_prepare_public_capacity_exit_entail_wit_1_1 : solver_prepare_public_capacity_exit_entail_wit_1_1.
Proof.
  (* Open the capacity-focus bundle and pin every field it fixes.  [qhead < qtail]
     is the first arm of the publication choice, so the flag published here is 1;
     after the substs that hypothesis reads back verbatim as
     [mt_qhead (ms_core M) < ms_qtail M], which is what [assumption] finds. *)
  aggressive_pre_process.
  match goal with
  | Hfocus : solver_cancel_capacity_focus ?n ?F ?M ?qh ?qt
      ?pqh ?pf ?root ?tagged ?stack ?tcap ?scap |- _ =>
      destruct Hfocus as
        [Hready [Hcap [Hseed [Hqh [Hqt [Hpqh [Hpf [Hroot
          [Htagged [Htcap [Hstack Hscap]]]]]]]]]]];
      subst qh; subst qt; subst pqh; subst pf; subst root;
      subst tagged; subst tcap; subst stack; subst scap
  end.
  match goal with
  | Hready : solver_root_rebuild_ready ?n ?F ?M |- _ =>
      assert (Htransition :
        solver_capacity_publication_transition n F M 1) by
        (apply capacity_publication_transition_intro__canceluntil_cap;
         [exact Hready | exact Hcap | exact Hseed |
          unfold solver_capacity_publication_choice; left; split;
          [reflexivity | assumption]])
  end.
  match goal with
  | Hready : solver_root_rebuild_ready ?n ?F ?M |- _ =>
      assert (Hpublished_shape :
        solver_shape (msolver_publish_capacity M 1)) by
        (apply solver_publish_capacity_shape__canceluntil_cap with (n := n)
           (F := F);
         [exact Hready | unfold solver_capacity_publication_choice;
          left; split; [reflexivity | assumption]])
  end.
  (* Both empty-slice length facts read back as [sublist 0 0 _ = nil]. *)
  match goal with
  | Hzero : Zlength (sublist 0 0 ?l) = 0 |- _ =>
      apply Zlength_nil_inv in Hzero
  end.
  match goal with
  | Hzero : Zlength (sublist 0 0 ?l) = 0 |- _ =>
      apply Zlength_nil_inv in Hzero
  end.
  Exists 1.
  entailer_with ltac:(lia).
  repeat match goal with
  | Hnil : sublist 0 0 ?l = (@nil Z) |- _ => rewrite Hnil; clear Hnil
  end.
  assert (Hstack_bounds :
    0 <= Zlength (@nil Z) <= ms_stack_cap Mcancel) by
    (rewrite Zlength_nil; lia).
  assert (Hstack_cap :
    0 < ms_stack_cap Mcancel <= INT_MAX) by lia.
  assert (Htagged_bounds :
    0 <= Zlength (@nil Z) <= ms_tagged_cap Mcancel) by
    (rewrite Zlength_nil; lia).
  assert (Htagged_cap :
    0 < ms_tagged_cap Mcancel <= INT_MAX) by lia.
  sep_apply
    (solver_nested_veci_from_cells__canceluntil_cap
      s_pre "stack" p_2 (@nil Z) (ms_stack_cap Mcancel)
      Hstack_bounds Hstack_cap).
  sep_apply
    (solver_nested_veci_from_cells__canceluntil_cap
      s_pre "tagged" p (@nil Z) (ms_tagged_cap Mcancel)
      Htagged_bounds Htagged_cap).
  apply (publish_capacity_join s_pre Mcancel 1 (ms_qtail Mcancel) wl eq_refl
    Hpublished_shape).
Qed.

Lemma proof_of_solver_prepare_public_capacity_exit_entail_wit_1_2 : solver_prepare_public_capacity_exit_entail_wit_1_2.
Proof.
  (* Open the capacity-focus bundle and pin every field it fixes.  [qhead >= qtail]
     is the second arm of the publication choice, so the flag published here is 0
     and the queue head has caught up with the tail. *)
  aggressive_pre_process.
  match goal with
  | Hfocus : solver_cancel_capacity_focus ?n ?F ?M ?qh ?qt
      ?pqh ?pf ?root ?tagged ?stack ?tcap ?scap |- _ =>
      destruct Hfocus as
        [Hready [Hcap [Hseed [Hqh [Hqt [Hpqh [Hpf [Hroot
          [Htagged [Htcap [Hstack Hscap]]]]]]]]]]];
      subst qh; subst qt; subst pqh; subst pf; subst root;
      subst tagged; subst tcap; subst stack; subst scap
  end.
  pose proof (msw_shape (proj1 Hready)) as Hsource_shape.
  unfold solver_shape, msolver_set_root, msolver_core_heap_update
    in Hsource_shape.
  simpl in Hsource_shape.
  match goal with
  | Hready : solver_root_rebuild_ready _ _ ?M |- _ =>
      assert (Heq : mt_qhead (ms_core M) = ms_qtail M) by lia
  end.
  match goal with
  | Hready : solver_root_rebuild_ready ?n ?F ?M |- _ =>
      assert (Htransition :
        solver_capacity_publication_transition n F M 0) by
        (apply capacity_publication_transition_intro__canceluntil_cap;
         [exact Hready | exact Hcap | exact Hseed |
          unfold solver_capacity_publication_choice; right; split;
          [reflexivity | exact Heq]])
  end.
  match goal with
  | Hready : solver_root_rebuild_ready ?n ?F ?M |- _ =>
      assert (Hpublished_shape :
        solver_shape (msolver_publish_capacity M 0)) by
        (apply solver_publish_capacity_shape__canceluntil_cap with (n := n)
           (F := F);
         [exact Hready | unfold solver_capacity_publication_choice;
          right; split; [reflexivity | exact Heq]])
  end.
  (* Both empty-slice length facts read back as [sublist 0 0 _ = nil]. *)
  match goal with
  | Hzero : Zlength (sublist 0 0 ?l) = 0 |- _ =>
      apply Zlength_nil_inv in Hzero
  end.
  match goal with
  | Hzero : Zlength (sublist 0 0 ?l) = 0 |- _ =>
      apply Zlength_nil_inv in Hzero
  end.
  Exists 0.
  entailer_with ltac:(lia).
  repeat match goal with
  | Hnil : sublist 0 0 ?l = (@nil Z) |- _ => rewrite Hnil; clear Hnil
  end.
  assert (Hstack_bounds :
    0 <= Zlength (@nil Z) <= ms_stack_cap Mcancel) by
    (rewrite Zlength_nil; lia).
  assert (Hstack_cap :
    0 < ms_stack_cap Mcancel <= INT_MAX) by lia.
  assert (Htagged_bounds :
    0 <= Zlength (@nil Z) <= ms_tagged_cap Mcancel) by
    (rewrite Zlength_nil; lia).
  assert (Htagged_cap :
    0 < ms_tagged_cap Mcancel <= INT_MAX) by lia.
  sep_apply
    (solver_nested_veci_from_cells__canceluntil_cap
      s_pre "stack" p_2 (@nil Z) (ms_stack_cap Mcancel)
      Hstack_bounds Hstack_cap).
  sep_apply
    (solver_nested_veci_from_cells__canceluntil_cap
      s_pre "tagged" p (@nil Z) (ms_tagged_cap Mcancel)
      Htagged_bounds Htagged_cap).
  apply (publish_capacity_join s_pre Mcancel 0 (mt_qhead (ms_core Mcancel)) wl Heq
    Hpublished_shape).
Qed.

(* ===== solver_prepare_public_capacity_exit partial_solve wits (4 proofs) ===== *)
Lemma proof_of_solver_prepare_public_capacity_exit_partial_solve_wit_3_pure :
  solver_prepare_public_capacity_exit_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process;
    prop_apply_p
      (veci_rep_bounds__canceluntil_cap
         &(s_pre # "solver_t" ->ₛ "tagged") tagged tagged_cap);
    Intros_p Hcap;
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_solver_prepare_public_capacity_exit_partial_solve_wit_4_pure :
  solver_prepare_public_capacity_exit_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process;
    unfold veci_rep at 1; Intros tagged_ptr;
    unfold veci_rep_at at 1; Intros_p Htagged_bounds;
    dump_pre_spatial; lia.
Qed.

Lemma proof_of_solver_prepare_public_capacity_exit_partial_solve_wit_5_pure :
  solver_prepare_public_capacity_exit_partial_solve_wit_5_pure.
Proof.
  msat_prepare_capacity_exit_veci_bound_p8.
Qed.

Lemma proof_of_solver_prepare_public_capacity_exit_partial_solve_wit_6_pure :
  solver_prepare_public_capacity_exit_partial_solve_wit_6_pure.
Proof.
  msat_prepare_capacity_exit_veci_bound_p8.
Qed.

(* ===== solver_prepare_public_capacity_exit return wits (1 proofs) ===== *)
Lemma proof_of_solver_prepare_public_capacity_exit_return_wit_1 : solver_prepare_public_capacity_exit_return_wit_1.
Proof.
  Unfold. right.
  intros s_pre wl M F n Mcancel published_flag.
  aggressive_pre_process.
  bind_fact ( solver_capacity_publication_transition n F Mcancel published_flag ) as
    H_solver_capacity_publication_transi.
  assert (Hpublished_cap :
    ms_cap (msolver_publish_capacity Mcancel published_flag) = ms_cap M).
  { change (ms_cap Mcancel = ms_cap M). assumption. }
  bind_fact (minisat_base_watch_completed M -> minisat_watch_completed Mcancel)
    as Hcomplete.
  assert (Hwatch : minisat_base_watch_completed M ->
      solver_query_watch_ready (msolver_publish_capacity Mcancel published_flag)).
  { intro Hbase. apply solver_capacity_publication_watch_ready__api_reentry.
    - exact (proj1 H_solver_capacity_publication_transi).
    - exact (Hcomplete Hbase). }
  unfold solver_prepare_capacity_post.
  Exists (msolver_publish_capacity Mcancel published_flag).
  entailer_with ltac:(lia);
    unfold solver_capacity_publication_transition in H_solver_capacity_publication_transi; tauto.
Qed.

(* ===== solver_prepare_public_capacity_exit which_implies wits (1 proofs) ===== *)
Lemma proof_of_solver_prepare_public_capacity_exit_which_implies_wit_1 :
  solver_prepare_public_capacity_exit_which_implies_wit_1.
Proof.
  Unfold.
  left. intros.
  unfold solver_cancel_capacity_post.
  Intros Mcancel.
  unfold solver_rep_wl, solver_rep_levels_wl_at.
  Intros lvl.
  Intros act asg opos rsn trl tgs.
  Exists (mt_qhead (ms_core Mcancel)) (ms_qtail Mcancel)
    (ms_capacity_pending_qhead Mcancel)
    (ms_capacity_root_propagation_pending Mcancel) (ms_root_level Mcancel)
    (ms_tagged Mcancel) (ms_stack Mcancel) (ms_tagged_cap Mcancel) (ms_stack_cap Mcancel) Mcancel.
  split_pure_spatial.
  - unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_scalars_rep, solver_vecs_rep,
      solver_public_capacity_frame, solver_ptrs_rep,
      solver_var_arrays_rep, solver_levels_slice_at.
    Exists act asg opos rsn lvl trl tgs.
    first
      [ solve [msat_frame_entailer_with_p8 ltac:(lia)]
      | entailer_with ltac:(lia) ].
  - unfold solver_cancel_capacity_focus.
    destruct H as [Hready [Hcapacity [Hseed [Hentry_cap Hcomplete]]]].
    split_pures; dump_pre_spatial.
    + exact Hentry_cap.
    + exact Hcomplete.
    + split; [exact Hready |].
      split; [exact Hcapacity |].
      split; [exact Hseed |].
      repeat split; reflexivity.
Qed.

(* ===== solver_propagate partial_solve wits ===== *)
Lemma proof_of_solver_propagate_partial_solve_wit_6_pure : solver_propagate_partial_solve_wit_6_pure.
Proof.
  Unfold.
  right. intros.
  rewrite !Z.sub_0_r.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_9_pure : solver_propagate_partial_solve_wit_9_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_9_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( solver_propagation_inv n F A_arr K M1 ) as H_solver_propagation_inv;
    entailer_with ltac:(lia);
    try lia.
  unfold solver_propagation_inv in H_solver_propagation_inv.
  destruct H_solver_propagation_inv as [_ Hinv].
  destruct K as [A_inst | A_proc]; cbn in Hinv.
  - pose proof (@msp_weak n F A_arr A_inst M1 Hinv) as Hw.
    destruct Hw.
    assumption.
  - pose proof (@msap_weak n F A_arr A_proc M1 Hinv) as Ha.
    destruct Ha.
    assumption.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_17_pure : solver_propagate_partial_solve_wit_17_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_17_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  split_pures;
    entailer_with lia;
    try change (sizeof (PTR)) with ptr_size_Z in *; solve_arch.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_18_pure : solver_propagate_partial_solve_wit_18_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_18_pure.
  unfold stats_propagations, stats_inspects.
  (* Not the scan family: the second disjunct needs the single fact [ii < Zlength source_words], which the loop guard
     supplies only in pointer form (the guard plus the two address equations).  Dividing out the stride is the whole
     content -- [sizeof(PTR)] is an Arch constant and opaque to lia, so it is discharged positive first (solve_arch,
     arch-agnostic: no width is named) and nia then cancels it from [ii * stride < Zlength source_words * stride]. *)
  Unfold.
  right; intros.
  assert (HS : sizeof(PTR) > 0) by (change (sizeof (PTR)) with ptr_size_Z; solve_arch).
  assert (Hii : ii < Zlength source_words) by nia.
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_36_scan_move_pure :
  solver_propagate_partial_solve_wit_36_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_36_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  split_pures;
    entailer_with ltac:(lia);
    try lia;
    try (pose proof (Zlength_nonneg source_words); lia).
  - {
  unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
  destruct H_propagation_watch_scan_physical as [_ [_ [Hjj [Hii Hlen]]]].
  assert (Hj0 : 0 <= jj) by (rewrite <- Hjj; apply Zlength_nonneg).
  assert (Hji : jj <= ii).
  { rewrite <- Hjj.
    rewrite <- Hii.
    rewrite Zlength_app.
    pose proof (Zlength_nonneg garbage) as Hg.
    lia. }
  assert (Hii0 : 0 <= ii < Zlength watch_memory) by lia.
  assert (Hjj0 : 0 <= jj < Zlength watch_memory) by lia.
  assert (Hscan : Znth ii watch_memory 0 = scan_current).
  { rewrite H_watch_memory.
    rewrite app_Znth2 by lia.
    rewrite H_Zlength.
    replace (ii - ii) with 0 by lia.
    reflexivity. }
  rewrite H_tagged_memory.
  destruct (Z.eq_dec ii jj) as [Heq | Hneq].
  + subst ii. rewrite <- Heq.
    apply Znth_replace_Znth_Same; lia.
  + rewrite <- Hscan.
    apply Znth_replace_Znth_Diff;
      [exact Hjj0 | exact Hii0 | intro Heq; apply Hneq; symmetry; exact Heq].
    }
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_37_scan_same_pure :
  solver_propagate_partial_solve_wit_37_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_37_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  (* The RHS carries extra copies of the same conjuncts with [msolver_propagation_scan_begin Mentry simp_count
     prop_count] written out in place of [Mscan].  [rewrite <- H_Mscan] folds them back onto the [Mscan] spelling, at
     which point the endgame closes them as duplicates of conjuncts already discharged. *)
  pre_process_default.
  bind_fact ( is_tag scan_current = msat_true ) as H_is_tag.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength_2.
  bind_fact ( Mscan = msolver_propagation_scan_begin Mentry simp_count prop_count ) as H_Mscan.
  rewrite <- H_Mscan.
  assert (Hcur : Znth ii (replace_Znth ii scan_current watch_memory) 0 = scan_current).
  { apply Znth_replace_Znth_Same. rewrite H_Zlength_2. lia. }
  assert (Hrest : rest = scan_current :: raw_suffix)
    by (eapply propagation_watch_scan_rest_head__propagate;
        [ eassumption | eassumption | eassumption ]).
  assert (Henq : enqueue_input (ms_size Mscan) (tag_lit scan_current)
      (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
      (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
      (mt_trail (ms_core Mscan)))
    by (eapply propagation_scan_current_enqueue_input__propagate; eassumption).
  split_pures;
    entailer_with ltac:(lia);
    try exact Henq;
    try (rewrite Hcur; exact Henq);
    try (unfold solver_shape in H_solver_shape; tauto);
    try (symmetry; apply Znth_replace_Znth_Same; rewrite Zlength_replace_Znth; lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_38_scan_move_pure :
  solver_propagate_partial_solve_wit_38_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_38_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( is_tag scan_current = msat_true ) as H_is_tag.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  bind_fact ( Mscan = msolver_propagation_scan_begin Mentry simp_count prop_count ) as H_Mscan.
  (* [Mscan] is given here as [msolver_propagation_scan_begin Mentry simp_count prop_count], and the RHS carries extra
     copies of the conjuncts spelled that way; the [rewrite <- H_Mscan] just before split_pures collapses them onto the
     [Mscan] spellings.  [enqueue_input] is derived once, as HenqSC, and reused for every residual conjunct, which
     keeps the endgame independent of goal order. *)
  assert (Hrest : rest = scan_current :: raw_suffix)
    by (eapply propagation_watch_scan_rest_head__propagate;
        [ eassumption | eassumption | eassumption ]).
  assert (HenqSC : enqueue_input (ms_size Mscan) (tag_lit scan_current)
      (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
      (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
      (mt_trail (ms_core Mscan)))
    by (eapply propagation_scan_current_enqueue_input__propagate; eassumption).
  rewrite <- H_Mscan.
  split_pures;
    entailer_with ltac:(lia);
    try lia;
    try (unfold solver_shape in H_solver_shape; tauto);
    try (symmetry; apply Znth_replace_Znth_Same; rewrite Zlength_replace_Znth; lia);
    try exact HenqSC;
    try (rewrite <- H_tagged_memory, H_Znth; exact HenqSC).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_40_scan_move_pure :
  solver_propagate_partial_solve_wit_40_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_40_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( is_tag scan_current = msat_true ) as H_is_tag.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  split_pures;
    entailer_with ltac:(lia);
    try lia.
  (* Seven residual goals: bullets 2-5 are pure [solver_shape] projections and bullet 7 is a
     [replace_Znth] identity.  Only bullets 1 and 6 need the scan facts, and the enqueue fact
     alone closes both -- bullet 6 after folding the written memory back to [tagged_memory]
     and reading the scanned cell there as [scan_current]. *)
  - { assert (Hrest : rest = scan_current :: raw_suffix)
        by (eapply propagation_watch_scan_rest_head__propagate;
            [ eassumption | eassumption | eassumption ]).
      assert (Henq : enqueue_input (ms_size Mscan) (tag_lit scan_current)
          (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
          (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
          (mt_trail (ms_core Mscan)))
        by (eapply propagation_scan_current_enqueue_input__propagate; eassumption).
      exact Henq. }
  - unfold solver_shape in H_solver_shape; tauto.
  - unfold solver_shape in H_solver_shape; tauto.
  - unfold solver_shape in H_solver_shape; tauto.
  - unfold solver_shape in H_solver_shape; tauto.
  - { assert (Hrest : rest = scan_current :: raw_suffix)
        by (eapply propagation_watch_scan_rest_head__propagate;
            [ eassumption | eassumption | eassumption ]).
      assert (Henq : enqueue_input (ms_size Mscan) (tag_lit scan_current)
          (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
          (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
          (mt_trail (ms_core Mscan)))
        by (eapply propagation_scan_current_enqueue_input__propagate; eassumption).
      rewrite <- H_tagged_memory, H_Znth. exact Henq. }
  - symmetry. apply Znth_replace_Znth_Same.
    rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_42_scan_move_pure :
  solver_propagate_partial_solve_wit_42_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_42_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  (* [enqueue_input] arrives here as a hypothesis, so only its first two projections are needed instead of a derivation
     out of the scan semantics.  The rest of the site is the doubly-written cell reading back as [scan_current] in both
     of the spellings the RHS uses. *)
  Unfold.
  left; intros.
  bind_fact ( enqueue_input (ms_size Mscan) (tag_lit scan_current) (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
    (mt_levels (ms_core Mscan)) (ms_reason_words Mscan) (mt_trail (ms_core Mscan)) ) as
    H_enqueue_input.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( is_tag scan_current = msat_true ) as H_is_tag.
  bind_fact ( 0 <= scan_current ) as H_scan_current.
  assert (Hii : 0 <= ii < Zlength tagged_memory).
  { rewrite H_tagged_memory, Zlength_replace_Znth. lia. }
  assert (Hs1 : Znth ii (replace_Znth ii scan_current
      (replace_Znth ii scan_current tagged_memory)) 0 = scan_current).
  { apply Znth_replace_Znth_Same. rewrite Zlength_replace_Znth. exact Hii. }
  assert (Hs2 : Znth ii (replace_Znth ii (Znth ii tagged_memory 0)
      (replace_Znth ii (Znth ii tagged_memory 0) tagged_memory)) 0 = scan_current).
  { rewrite H_Znth. exact Hs1. }
  assert (Htw : tagged_word scan_current).
  { unfold tagged_word. rewrite H_is_tag. reflexivity. }
  assert (Hwf : 0 <= tag_lit scan_current < 2 * ms_size Mscan) by exact (proj1 H_enqueue_input).
  assert (H2n : 2 * ms_size Mscan <= INT_MAX) by exact (proj1 (proj2 H_enqueue_input)).
  split_pures;
    entailer_with ltac:(lia);
    rewrite ?Hs1, ?Hs2;
    try exact H_scan_current;
    try exact Htw;
    try lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_43_scan_move_pure :
  solver_propagate_partial_solve_wit_43_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_43_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_split_bound_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_45_scan_same_pure :
  solver_propagate_partial_solve_wit_45_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_45_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_same_tagged_bound_p8 ii.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_46_scan_same_pure :
  solver_propagate_partial_solve_wit_46_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_46_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( ms_wm Mscan = scan_wm_pre ++ logical_words :: scan_wm_post ) as H_ms_wm.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength.
  split_pures.
  all: (entailer_with ltac:(lia));
    (try lia).
  all: (unfold solver_shape in H_solver_shape);
    (assert (Hms : Zlength (ms_wm Mscan) = 2 * ms_size Mscan) by tauto);
    (assert (H2n : 2 * ms_size Mscan <= INT_MAX) by tauto);
    (assert (Hsz : 0 <= ms_size Mscan) by tauto);
    (assert (Hpre : 0 <= Zlength scan_wm_pre) by apply Zlength_nonneg);
    (assert (Hpost : 0 <= Zlength scan_wm_post) by apply Zlength_nonneg);
    (assert (Hwm : Zlength (ms_wm Mscan) = Zlength scan_wm_pre + 1 + Zlength scan_wm_post)
      by (rewrite H_ms_wm; rewrite Zlength_app; rewrite Zlength_cons; lia));
    (rewrite <- H_Zlength);
    (lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_48_scan_move_pure :
  solver_propagate_partial_solve_wit_48_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_48_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_same_tagged_bound_p8 ii.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_51_scan_same_pure :
  solver_propagate_partial_solve_wit_51_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_51_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right. intros.
  bind_fact ( enqueue_input (ms_size Mscan) (tag_lit scan_current) (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
    (mt_levels (ms_core Mscan)) (ms_reason_words Mscan) (mt_trail (ms_core Mscan)) ) as
    H_enqueue_input.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  assert (Hcollapse : replace_Znth ii scan_current tagged_memory = tagged_memory).
  { rewrite <- H_Znth. apply replace_Znth_Znth. }
  rewrite !Hcollapse.
  rewrite H_Znth.
  unfold enqueue_input in H_enqueue_input.
  destruct H_enqueue_input as [Hwf [H2n _]].
  unfold lit_wf_c in Hwf.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_53_scan_move_pure :
  solver_propagate_partial_solve_wit_53_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_53_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right. intros.
  bind_fact ( retval = tag_lit (Znth ii (replace_Znth ii (Znth ii tagged_memory 0) (replace_Znth ii (Znth ii
    tagged_memory 0) tagged_memory)) 0) ) as H_retval.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  rewrite !replace_Znth_Znth in H_retval.
  rewrite !replace_Znth_Znth.
  rewrite H_Znth in H_retval.
  rewrite H_Znth.
  rewrite H_retval.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_54_scan_same_pure :
  solver_propagate_partial_solve_wit_54_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_54_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right. intros.
  subst jj.
  bind_fact ( retval = tag_lit (Znth ii (replace_Znth ii (Znth ii tagged_memory 0) (replace_Znth ii (Znth ii
    tagged_memory 0) tagged_memory)) 0) ) as H_retval.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth ii scan_current watch_memory ) as H_tagged_memory.
  rewrite <- H_tagged_memory.
  rewrite !replace_Znth_Znth in H_retval.
  rewrite !replace_Znth_Znth.
  rewrite H_Znth in H_retval.
  rewrite H_Znth.
  rewrite H_retval.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_55_scan_move_pure :
  solver_propagate_partial_solve_wit_55_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_55_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  Unfold.
  right. intros.
  bind_fact ( retval = tag_lit (Znth ii (replace_Znth ii (Znth ii tagged_memory 0) (replace_Znth ii (Znth ii
    tagged_memory 0) tagged_memory)) 0) ) as H_retval.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( Mscan = msolver_propagation_scan_begin Mentry simp_count prop_count ) as H_Mscan.
  rewrite <- H_Mscan.
  rewrite !replace_Znth_Znth in H_retval.
  rewrite !replace_Znth_Znth.
  rewrite H_Znth in H_retval.
  rewrite H_Znth.
  rewrite H_retval.
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_56_scan_same_pure :
  solver_propagate_partial_solve_wit_56_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_56_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( retval = tag_lit (Znth ii (replace_Znth ii (Znth ii tagged_memory 0) (replace_Znth ii (Znth ii
    tagged_memory 0) tagged_memory)) 0) ) as H_retval.
  bind_fact ( enqueue_input (ms_size Mscan) (tag_lit scan_current) (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
    (mt_levels (ms_core Mscan)) (ms_reason_words Mscan) (mt_trail (ms_core Mscan)) ) as
    H_enqueue_input.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( jj = ii ) as H_jj.
  bind_fact ( Mscan = msolver_propagation_scan_begin Mentry simp_count prop_count ) as H_Mscan.
  bind_fact ( simp_count = ms_simpdb_props Mscan ) as H_simp_count.
  bind_fact ( prop_count = Znth 2 (ms_stats Mscan) 0 ) as H_prop_count.
  split_pures.
  all: (dump_pre_spatial);
    (try lia).
  all: (rewrite H_jj in H_tagged_memory);
    (assert (Hkey :
           Znth ii
             (replace_Znth ii (Znth ii tagged_memory 0)
                (replace_Znth ii (Znth ii tagged_memory 0) tagged_memory)) 0
           = scan_current)
      by (rewrite H_Znth;
          rewrite replace_Znth_replace_Znth_Same by lia;
          rewrite Znth_replace_Znth_Same
            by (rewrite H_tagged_memory, Zlength_replace_Znth; lia);
          reflexivity)).
  - rewrite H_retval, Hkey, <- H_simp_count, <- H_prop_count, <- H_Mscan.
    exact H_enqueue_input.
  - rewrite <- H_tagged_memory, Hkey, <- H_Mscan.
    exact H_enqueue_input.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_57_scan_same_pure :
  solver_propagate_partial_solve_wit_57_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_57_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_replace_same_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_58_scan_move_pure :
  solver_propagate_partial_solve_wit_58_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_58_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_replace_same_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_59_scan_same_pure :
  solver_propagate_partial_solve_wit_59_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_59_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_replace_same_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_60_scan_move_pure :
  solver_propagate_partial_solve_wit_60_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_60_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_replace_same_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_69_scan_move_pure :
  solver_propagate_partial_solve_wit_69_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_69_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_scan_wm_split_bound_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_84_scan_move_pure : solver_propagate_partial_solve_wit_84_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_84_scan_move_pure.
  unfold stats_inspects.
  LLM_pre_process ltac:(lia).
  bind_fact ( Znth ii tagged_enqueue_conflict_memory 0 = scan_current ) as H_Znth.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( 0 <= scan_current ) as H_scan_current.
  bind_fact ( propagation_binary_conflict_scan_ready n Mscan p scan_current source_words scan_wcap simp_count
    prop_count ) as H_propagation_binary_conflict_scan_r.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( tagged_enqueue_conflict_memory = replace_Znth jj scan_current watch_memory ) as
    H_tagged_enqueue_conflict_memory.
  assert (Hrest : rest = scan_current :: raw_suffix) by exact H_rest.
  pose proof (propagation_scan_current_tag_facts__propagate
    _ _ _ _ _ _ _ _ _ _ _ H_solver_propagation_scan_semantics Hrest
    (proj1 H_propagation_binary_conflict_scan_r)) as [Hnsize [Hdb Htag]].
    assert (H2n : 2 * ms_size Mscan <= INT_MAX).
    { pose proof H_solver_shape as Hshape2. unfold solver_shape in Hshape2. tauto. }
    assert (Hlenmem : Zlength tagged_enqueue_conflict_memory = ii + 1 + Zlength raw_suffix).
    { rewrite H_tagged_enqueue_conflict_memory, Zlength_replace_Znth, H_watch_memory, Zlength_app, Zlength_cons,
      H_Zlength. lia. }
    assert (Hcur : Znth ii (replace_Znth ii scan_current tagged_enqueue_conflict_memory) 0
        = scan_current).
    { apply Znth_replace_Znth_Same.
      pose proof (Zlength_nonneg raw_suffix). lia. }
    (* Seven residual conjuncts survive [split_pures]: three facts about the written word
       ([0 <= scan_current] once, the scan-ready projection twice) and four [tag_lit] range
       facts.  Each gets its own closer. *)
    split_pures;
      try entailer_with lia;
      rewrite ?H_Znth, Hcur.
    - exact H_scan_current.
    - exact (proj1 H_propagation_binary_conflict_scan_r).
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - exact (proj1 H_propagation_binary_conflict_scan_r).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_87_scan_same_pure : solver_propagate_partial_solve_wit_87_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_87_scan_same_pure.
  unfold stats_inspects.
  pre_process_default.
  bind_fact ( Znth ii tagged_enqueue_conflict_memory 0 = scan_current ) as H_Znth.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( 0 <= scan_current ) as H_scan_current.
  bind_fact ( propagation_binary_conflict_scan_ready n Mscan p scan_current source_words scan_wcap simp_count
    prop_count ) as H_propagation_binary_conflict_scan_r.
  bind_fact ( tagged_enqueue_conflict_memory = replace_Znth jj scan_current watch_memory ) as
    H_tagged_enqueue_conflict_memory.
  assert (Hrest : rest = scan_current :: raw_suffix) by exact H_rest.
  pose proof (propagation_scan_current_tag_facts__propagate
    _ _ _ _ _ _ _ _ _ _ _ H_solver_propagation_scan_semantics Hrest
    (proj1 H_propagation_binary_conflict_scan_r)) as [Hnsize [Hdb Htag]].
  assert (Henq : enqueue_input (ms_size Mscan) (tag_lit scan_current)
      (ms_qtail Mscan) (mt_assigns (ms_core Mscan))
      (mt_levels (ms_core Mscan)) (ms_reason_words Mscan)
      (mt_trail (ms_core Mscan))).
  { eapply propagation_scan_current_enqueue_input__propagate;
    [ exact H_solver_propagation_scan_semantics
    | exact Hrest
    | exact (proj1 H_propagation_binary_conflict_scan_r) ]. }
  assert (H2n : 2 * ms_size Mscan <= INT_MAX).
  { pose proof H_solver_shape as Hshape86. unfold solver_shape in Hshape86. tauto. }
    (* The RHS spells the written cell as [scan_current] rather than as [Znth ii tagged_enqueue_conflict_memory 0], so
       the read-back fact must be stated in that spelling: QCP cancellation is syntactic, and [rewrite Hcur] would not
       match the other one. *)
    assert (Hcur : Znth ii
        (replace_Znth ii scan_current tagged_enqueue_conflict_memory) 0
        = scan_current).
    { unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
      destruct H_propagation_watch_scan_physical as [_ [_ [_ [_ Hlenmem]]]].
      assert (Hii0 : 0 <= ii < Zlength tagged_enqueue_conflict_memory).
      { rewrite H_tagged_enqueue_conflict_memory, Zlength_replace_Znth, Hlenmem. lia. }
      apply Znth_replace_Znth_Same; exact Hii0. }
    (* Some residual conjuncts still spell the written cell as
       [Znth ii tagged_enqueue_conflict_memory 0]; H_Znth folds that back to [scan_current],
       and Hcur does the same for the freshly written cell.  Seven conjuncts survive, each
       with its own closer. *)
    split_pures.
    all: (entailer_with ltac:(lia));
      (try lia);
      (try (exact Henq)).
    all: (try (rewrite H_Znth));
      (rewrite Hcur).
    - exact H_scan_current.
    - exact (proj1 H_propagation_binary_conflict_scan_r).
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - exact (proj1 H_propagation_binary_conflict_scan_r).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_89_scan_move_pure :
  solver_propagate_partial_solve_wit_89_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_89_scan_move_pure.
  unfold stats_inspects.
  LLM_pre_process ltac:(lia).
  split_pures;
    try entailer_with lia;
    subst i endvar;
    change (sizeof (PTR)) with ptr_size_Z in *;
    unfold_arch;
    nia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_93_scan_move_pure :
  solver_propagate_partial_solve_wit_93_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_93_scan_move_pure.
  unfold stats_inspects.
  pre_process_default.
  bind_fact ( logical_words = retained ++ rest ) as H_logical_words.
  bind_fact ( ms_wm Mscan = scan_wm_pre ++ logical_words :: scan_wm_post ) as H_ms_wm.
  split_pures;
    entailer_with ltac:(lia);
    try lia.
  rewrite H_ms_wm. rewrite H_logical_words. reflexivity.
  unfold propagation_scan_open; tauto.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_94_binary_keep_pure :
  solver_propagate_partial_solve_wit_94_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_94_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  unshelve (LLM_pre_process ltac:(lia));
    msat_propagate_binary_keep_length_p8 tagged_memory.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_95_binary_keep_pure :
  solver_propagate_partial_solve_wit_95_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_95_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  unshelve (LLM_pre_process ltac:(lia));
    msat_propagate_binary_keep_length_p8 tagged_memory.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_96_binary_keep_pure :
  solver_propagate_partial_solve_wit_96_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_96_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  unshelve (LLM_pre_process ltac:(lia));
    msat_propagate_binary_keep_length_p8 tagged_memory.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_97_binary_keep_pure :
  solver_propagate_partial_solve_wit_97_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_97_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength.
  split_pures;
    entailer_with ltac:(lia);
    try lia;
    (symmetry; apply Znth_replace_Znth_Same;
          rewrite Zlength_replace_Znth, H_tagged_memory, Zlength_replace_Znth, H_Zlength;
          lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_98_binary_keep_pure :
  solver_propagate_partial_solve_wit_98_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_98_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( retval = tag_lit (Znth ii (replace_Znth ii (Znth ii tagged_memory 0) (replace_Znth ii (Znth ii
    tagged_memory 0) tagged_memory)) 0) ) as H_retval.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength.
  assert (Hw : 0 <= ii < Zlength watch_memory) by (rewrite H_Zlength; lia).
  assert (Hb : Znth ii (replace_Znth ii scan_current watch_memory) 0 = scan_current)
    by (apply Znth_replace_Znth_Same; exact Hw).
  assert (Ht : 0 <= ii < Zlength tagged_memory)
    by (rewrite H_tagged_memory, Zlength_replace_Znth; exact Hw).
  rewrite H_Znth in H_retval.
  rewrite (Znth_replace_Znth_Same 0 (replace_Znth ii scan_current tagged_memory) ii scan_current)
    in H_retval by (rewrite Zlength_replace_Znth; exact Ht).
  split_pures;
    entailer_with ltac:(lia);
    rewrite ?Hb, ?H_retval;
    lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_99_binary_keep_pure :
  solver_propagate_partial_solve_wit_99_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_99_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( retval = tag_lit (Znth ii (replace_Znth ii (Znth ii tagged_memory 0) (replace_Znth ii (Znth ii
    tagged_memory 0) tagged_memory)) 0) ) as H_retval.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength.
  assert (Ht : 0 <= ii < Zlength tagged_memory)
    by (rewrite H_tagged_memory, Zlength_replace_Znth, H_Zlength; lia).
  assert (Hb : Znth ii (replace_Znth jj scan_current watch_memory) 0 = scan_current)
    by (rewrite <- H_tagged_memory; exact H_Znth).
  rewrite H_Znth in H_retval.
  rewrite (Znth_replace_Znth_Same 0 (replace_Znth ii scan_current tagged_memory) ii scan_current)
    in H_retval by (rewrite Zlength_replace_Znth; exact Ht).
  split_pures;
    entailer_with ltac:(lia);
    rewrite ?Hb, ?H_retval;
    lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_100_binary_keep_pure :
  solver_propagate_partial_solve_wit_100_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_100_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength_2.
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength_3.
  assert (Hw : 0 <= ii < Zlength watch_memory) by (rewrite H_Zlength_3; lia).
  assert (Hb : Znth ii (replace_Znth ii scan_current watch_memory) 0 = scan_current)
    by (apply Znth_replace_Znth_Same; exact Hw).
  assert (Hb3 : Znth ii (replace_Znth ii scan_current
                  (replace_Znth ii scan_current
                     (replace_Znth ii scan_current watch_memory))) 0 = scan_current)
    by (apply Znth_replace_Znth_Same; rewrite !Zlength_replace_Znth; exact Hw).
  split_pures;
    entailer_with ltac:(lia);
    rewrite <- ?H_watch_memory;
    rewrite ?H_Zlength, ?H_Zlength_2;
    rewrite ?Hb;
    rewrite ?Hb3;
    lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_101_binary_keep_pure :
  solver_propagate_partial_solve_wit_101_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_101_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength_2.
  split_pures;
    entailer_with lia;
    try (rewrite H_Zlength_2; lia);
    rewrite <- ?H_watch_memory, ?H_Zlength;
         rewrite !Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia);
         rewrite <- ?H_tagged_memory, ?H_Znth; lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_102_binary_keep_pure :
  solver_propagate_partial_solve_wit_102_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_102_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_binary_keep_scan_key_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_103_binary_keep_pure :
  solver_propagate_partial_solve_wit_103_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_103_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( Znth ii tagged_memory 0 = scan_current ) as H_Znth.
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( is_tag scan_current = msat_true ) as H_is_tag.
  bind_fact ( ii < Zlength source_words ) as H_ii.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength_2.
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength_3.
  bind_fact ( 0 <= ii ) as H_ii_2.
  bind_fact ( ii <= Zlength source_words ) as H_ii_3.
  bind_fact ( Mscan = msolver_propagation_scan_begin Mentry simp_count prop_count ) as H_Mscan.
  bind_fact ( 0 <= Zlength source_words ) as H_Zlength_4.
  (* The watch row is physically [(retained ++ garbage) ++ rest]: [ii] counts the words
     already inspected and [jj] the words already kept.  Every residual conjunct is read
     off that one layout, so open a copy of it once instead of once per arm. *)
  pose proof H_propagation_watch_scan_physical as Hphys.
  unfold propagation_watch_scan_physical in Hphys.
  destruct Hphys as [Hperm [Hmem [Hkept [Hkg Hlen]]]].
  (* The tail still to be scanned starts at the word under the cursor. *)
  assert (Hrest_shape : rest = scan_current :: raw_suffix).
  { assert (Hconcat : raw_prefix ++ scan_current :: raw_suffix = (retained ++ garbage) ++ rest).
    { rewrite <- H_watch_memory, Hmem, app_assoc. reflexivity. }
    apply app_eq_app in Hconcat as [[m [Hm Htail]] | [m [Hm Htail]]].
    - assert (HZ : Zlength m = 0).
      { rewrite Hm in H_Zlength. rewrite Zlength_app, Hkg in H_Zlength. lia. }
      destruct m as [|a m]; [exact Htail |].
      exfalso. rewrite Zlength_cons in HZ. pose proof (Zlength_nonneg m). lia.
    - assert (HZ : Zlength m = 0).
      { rewrite Hm in Hkg. rewrite Zlength_app, H_Zlength in Hkg. lia. }
      destruct m as [|a m]; [symmetry; simpl in Htail; exact Htail |].
      exfalso. rewrite Zlength_cons in HZ. pose proof (Zlength_nonneg m). lia. }
  (* The keep-write stores [scan_current] at slot [jj], so the word read back at the
     cursor [ii] is [scan_current] whether or not the two slots coincide. *)
  assert (Hcursor : Znth ii (replace_Znth jj scan_current watch_memory) 0 = scan_current).
  { assert (Hjj0 : 0 <= jj) by (rewrite <- Hkept; apply Zlength_nonneg).
    assert (Hjjlen : jj < Zlength watch_memory).
    { rewrite H_Zlength_3. rewrite Zlength_app in Hkg.
      pose proof (Zlength_nonneg garbage). lia. }
    assert (Hiilen : ii < Zlength watch_memory) by (rewrite H_Zlength_3; exact H_ii).
    destruct (Z.eq_dec jj ii) as [Heq | Hneq].
    - rewrite <- Heq. apply Znth_replace_Znth_Same. exact (conj Hjj0 Hjjlen).
    - rewrite (Znth_replace_Znth_Diff 0 watch_memory jj ii scan_current
        (conj Hjj0 Hjjlen) (conj H_ii_2 Hiilen) Hneq).
      rewrite H_tagged_memory in H_Znth.
      rewrite (Znth_replace_Znth_Diff 0 watch_memory jj ii scan_current
        (conj Hjj0 Hjjlen) (conj H_ii_2 Hiilen) Hneq) in H_Znth.
      exact H_Znth. }
  (* The scan semantics transports to the literal conflict word 0: its conflict branch
     forces [rest = nil], which [Hrest_shape] refutes. *)
  assert (Hsem : solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest).
  { unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics |- *.
    destruct H_solver_propagation_scan_semantics as [Hlive | Hconf].
    - destruct Hlive as [Hc Hrestsem]. left. split; [reflexivity | exact Hrestsem].
    - destruct Hconf as [Hne [Hnil _]]. rewrite Hnil in Hrest_shape. discriminate. }
  assert (Hcf_zero : confl = 0).
  { destruct H_solver_propagation_scan_semantics as [[Hc _] | [_ [Hnil _]]];
      [ exact Hc | rewrite Hrest_shape in Hnil; discriminate ]. }
  assert (Hreuse0 : minisat_propagation_reuse_scan M0 Mscan p 0 rest).
  { rewrite <- Hcf_zero. assumption. }
  assert (Hreuse_begin : minisat_propagation_reuse_scan M0
    (msolver_propagation_scan_begin Mentry simp_count prop_count) p 0 rest).
  { rewrite <- H_Mscan. exact Hreuse0. }
  split_pures; entailer_with ltac:(lia);
    try solve [exact Hreuse0 | exact Hreuse_begin |
      unfold minisat_propagation_reuse_scan in *; tauto].
  - rewrite Hcursor. exact Hrest_shape.
  - unfold tagged_word. rewrite Hcursor. exact H_is_tag.
  - rewrite <- H_Mscan. exact Hsem.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_104_binary_keep_pure :
  solver_propagate_partial_solve_wit_104_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_104_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_binary_keep_scan_key_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_105_binary_keep_pure :
  solver_propagate_partial_solve_wit_105_binary_keep_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_105_binary_keep_pure.
  unfold stats_propagations, stats_inspects.
  msat_propagate_binary_keep_scan_key_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_106_scan_same_pure :
  solver_propagate_partial_solve_wit_106_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_106_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength.
  bind_fact ( ii <= Zlength source_words ) as H_ii.
  bind_fact ( Mscan = msolver_propagation_scan_begin Mentry simp_count prop_count ) as H_Mscan.
  bind_fact ( simp_count = ms_simpdb_props Mscan ) as H_simp_count.
  bind_fact ( prop_count = Znth 2 (ms_stats Mscan) 0 ) as H_prop_count.
  bind_fact ( Zlength source_words <= scan_wcap ) as H_Zlength_2.
  (* The scan semantics transports to the literal conflict word 0: in its conflict
     branch the row still to be scanned is empty, which contradicts the cursor bound
     carried by the physical layout. *)
  assert (Hcf_zero : confl = 0).
  { unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics.
    destruct H_solver_propagation_scan_semantics as [Hlive | Hconf].
    - exact (proj1 Hlive).
    - destruct Hconf as [Hne [Hnil _]].
      unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
      destruct H_propagation_watch_scan_physical as [_ [Hmem [_ [Hkg Hlen]]]].
      assert (Hsrc : Zlength source_words = ii + Zlength rest).
      { rewrite <- Hlen, Hmem, !Zlength_app in *. lia. }
      subst rest. rewrite Zlength_nil in Hsrc. rewrite Hsrc in *. lia. }
  assert (Hsem : solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest).
  { rewrite <- Hcf_zero. exact H_solver_propagation_scan_semantics. }
  assert (Hreuse0 : minisat_propagation_reuse_scan M0 Mscan p 0 rest).
  { rewrite <- Hcf_zero. assumption. }
  assert (Hreuse_slot : minisat_propagation_reuse_scan M0 Mscan (Zlength scan_wm_pre) 0 rest).
  { rewrite H_Zlength. exact Hreuse0. }
  assert (Hreuse_begin : minisat_propagation_reuse_scan M0
    (msolver_propagation_scan_begin Mentry simp_count prop_count) p 0 rest).
  { rewrite <- H_Mscan. exact Hreuse0. }
  split_pures; entailer_with ltac:(lia);
    try solve [exact Hreuse0 | exact Hreuse_slot | exact Hreuse_begin |
      unfold minisat_propagation_reuse_scan in *; tauto].
  - rewrite H_Zlength. exact Hsem.
  - unfold clause_is_lit_result. right. split; [lia | assumption].
  - rewrite <- H_Mscan. exact Hsem.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_107_scan_move_pure :
  solver_propagate_partial_solve_wit_107_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_107_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  pre_process_default.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  bind_fact ( logical_words = retained ++ rest ) as H_logical_words.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength.
  bind_fact ( Zlength scan_caps_pre = p ) as H_Zlength_2.
  bind_fact ( Mscan = msolver_propagation_scan_begin Mentry simp_count prop_count ) as H_Mscan.
  bind_fact ( simp_count = ms_simpdb_props Mscan ) as H_simp_count.
  bind_fact ( prop_count = Znth 2 (ms_stats Mscan) 0 ) as H_prop_count.
  bind_fact ( 0 <= Zlength source_words ) as H_Zlength_3.
  bind_fact ( 0 < scan_wcap ) as H_scan_wcap.
  (* Same scan-semantics-conflict note as in [proof_of_solver_propagate_partial_solve_wit_106_scan_same_pure] above. *)
  assert (Hcf_zero : confl = 0).
  { unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics.
    destruct H_solver_propagation_scan_semantics as [Hlive | Hconf].
    - exact (proj1 Hlive).
    - destruct Hconf as [Hne [Hnil _]].
      unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
      destruct H_propagation_watch_scan_physical as [_ [Hmem [_ [Hkg Hlen]]]].
      assert (Hsrc : Zlength source_words = ii + Zlength rest).
      { rewrite <- Hlen, Hmem, !Zlength_app in *. lia. }
      subst rest. rewrite Zlength_nil in Hsrc. rewrite Hsrc in *. lia. }
  assert (Hsem : solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest).
  { rewrite <- Hcf_zero. exact H_solver_propagation_scan_semantics. }
  assert (Hreuse0 : minisat_propagation_reuse_scan M0 Mscan p 0 rest).
  { rewrite <- Hcf_zero. assumption. }
  assert (Hreuse_slot : minisat_propagation_reuse_scan M0 Mscan (Zlength scan_wm_pre) 0 rest).
  { rewrite H_Zlength. exact Hreuse0. }
  assert (Hreuse_begin : minisat_propagation_reuse_scan M0
    (msolver_propagation_scan_begin Mentry simp_count prop_count) p 0 rest).
  { rewrite <- H_Mscan. exact Hreuse0. }
  split_pures; entailer_with ltac:(lia);
    try solve [exact Hreuse0 | exact Hreuse_slot | exact Hreuse_begin |
      unfold minisat_propagation_reuse_scan in *; tauto].
  - rewrite H_Zlength. exact Hsem.
  - unfold clause_is_lit_result. right. split; [lia | assumption].
  - rewrite <- H_Mscan. exact Hsem.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_320_scan_move_pure :
  solver_propagate_partial_solve_wit_320_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_320_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_321_scan_move_pure :
  solver_propagate_partial_solve_wit_321_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_321_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_322_scan_same_pure :
  solver_propagate_partial_solve_wit_322_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_322_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_323_scan_same_pure :
  solver_propagate_partial_solve_wit_323_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_323_scan_same_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_324_scan_move_pure :
  solver_propagate_partial_solve_wit_324_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_324_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_325_scan_move_pure :
  solver_propagate_partial_solve_wit_325_scan_move_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_325_scan_move_pure.
  unfold stats_propagations, stats_inspects.
  msat_clause_hdr_word_nonneg_scan_pure.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_422_scan_same_pure :
  solver_propagate_partial_solve_wit_422_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_422_scan_same_pure.
  unfold stats_propagations.
  (* Same shape as solver_propagate_partial_solve_wit_17_pure, one level down: the second disjunct needs only [offset <
     Zlength clause_contents], available from the clause-scan guard [k < stop] plus the two address equations.  Here
     the stride is [sizeof(INT)], which is arch-invariant, so sizeof_int alone makes it positive and nia cancels it. *)
  Unfold.
  right; intros.
  assert (HS : sizeof(INT) > 0) by (rewrite sizeof_int; lia).
  assert (Hoff : offset < Zlength clause_contents) by nia.
  msat_manual_entailer_with lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_423_scan_same_pure :
  solver_propagate_partial_solve_wit_423_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_423_scan_same_pure.
  unfold stats_propagations.
  msat_propagate_replacement_candidate_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_424_scan_same_pure :
  solver_propagate_partial_solve_wit_424_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_424_scan_same_pure.
  unfold stats_propagations.
  msat_propagate_replacement_candidate_p8.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_428_scan_same_pure :
  solver_propagate_partial_solve_wit_428_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_428_scan_same_pure.
  unfold stats_propagations.
  Unfold.
  right. intros.
  match goal with
  | Hinv : propagation_replacement_scan_inv _ _ _ _ _ |- _ =>
      destruct Hinv as [Hk [Hwf [Hfalse [Hlit Htail]]]]
  end.
  assert (Hwf_c : lit_wf_c n
      (Znth offset (propagation_normalized_clause watch0 false_lit clause_contents) 0)).
  { apply (Forall_Znth_elim Z (lit_wf_c n)
      (propagation_normalized_clause watch0 false_lit clause_contents) 0 offset Hwf).
    unfold propagation_normalized_clause.
    rewrite !Zlength_cons, Zlength_sublist by lia.
    lia. }
  unfold propagation_normalized_clause in Hwf_c.
  rewrite !Znth_cons, Znth_sublist in Hwf_c by lia.
  assert (Hcand : 0 <= candidate).
  { match goal with
    | Heq : candidate = _ |- _ => rewrite Heq
    end.
    rewrite Znth_sublist by lia.
    replace (offset - 2 + 2) with offset by lia.
    replace (offset - 1 - 1 + 2) with offset in Hwf_c by lia.
    exact (proj1 Hwf_c). }
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_433_scan_same_pure :
  solver_propagate_partial_solve_wit_433_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_433_scan_same_pure.
  unfold stats_propagations.
  Unfold.
  right. intros.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  assert (Hsem0 : solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest).
  { match goal with
    | Hsem : solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest |- _ => exact Hsem
    end. }
  assert (Hcur : Znth ii watch_memory 0 = scan_current).
  { rewrite H_watch_memory, <- H_Zlength.
    rewrite app_Znth2 by lia.
    replace (Zlength raw_prefix - Zlength raw_prefix) with 0 by lia.
    reflexivity. }
  entailer_with ltac:(lia);
    try rewrite Hcur; try rewrite <- H_rest;
    first [assumption |
      match goal with
      | Hreuse : minisat_propagation_reuse_scan M0 Mscan p 0 rest |- _ =>
          unfold minisat_propagation_reuse_scan in Hreuse; tauto
      end].
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_436_scan_same_pure :
  solver_propagate_partial_solve_wit_436_scan_same_pure.
Proof.
  unfold solver_propagate_partial_solve_wit_436_scan_same_pure.
  unfold stats_propagations.
  Unfold.
  right. intros.
  bind_fact ( retval_3 = lit_neg_c candidate ) as H_retval_3.
  bind_fact ( Zlength scan_wm_pre = p ) as H_Zlength.
  unfold vecp_rep, vecp_rep_at in *.
  Intros pp.
  entailer_with ltac:(lia);
    try rewrite H_retval_3;
    rewrite <- H_Zlength;
    lia.
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_442_capacity_copy_pure :
  solver_propagate_partial_solve_wit_442_capacity_copy_pure.
Proof.
  Unfold.
  right. intros.
  bind_fact ( i < endvar ) as H_i.
  bind_fact ( endvar = begin + Zlength source_words * sizeof ( PTR ) ) as H_endvar.
  bind_fact ( i = begin + copy_src * sizeof ( PTR ) ) as H_i_2.
  assert (Hsrc : copy_src < Zlength source_words).
  { rewrite H_endvar, H_i_2 in H_i.
    change (sizeof (PTR)) with ptr_size_Z in H_i. unfold_arch. cbn in H_i. nia. }
  msat_manual_entailer_with ltac:(assumption).
Qed.

Lemma proof_of_solver_propagate_partial_solve_wit_447_capacity_copy_pure :
  solver_propagate_partial_solve_wit_447_capacity_copy_pure.
Proof.
  Unfold.
  right. intros.
  bind_fact ( propagation_scan_open n F A_arr K M0 Mentry Mscan p confl source_words retained moved rest garbage
    watch_memory ii jj scan_current raw_suffix ) as H_propagation_scan_open.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src copy_dst
    copy_memory ) as H_binary_watch_copy_progress.
  bind_fact ( Zlength source_words <= scan_wcap ) as H_Zlength.
  unfold vecp_rep, vecp_rep_at in *.
  entailer_with ltac:(lia).
  assert (Hsrc : Zlength watch_memory = Zlength source_words).
  { unfold propagation_scan_open in H_propagation_scan_open.
    destruct H_propagation_scan_open as [_ [_ [_ [_ [_ [Hphys _]]]]]].
    unfold propagation_watch_scan_physical in Hphys.
    tauto. }
  assert (Hcopy : Zlength copy_memory = Zlength watch_memory).
  { unfold binary_watch_copy_progress in H_binary_watch_copy_progress.
    destruct H_binary_watch_copy_progress as [copied [rest' [H1 [H2 [H3 [H4 [H5 [H6 [H7 Hcopy]]]]]]]]].
    exact Hcopy. }
  rewrite Hcopy, Hsrc.
  exact H_Zlength.
Qed.

(* ===== solver_record entail wits (5 proofs) ===== *)
Lemma proof_of_solver_record_entail_wit_1 : solver_record_entail_wit_1.
Proof.
  Unfold.
  right. intros.
  sep_apply clause_new_post_physical__api_reentry.
  unfold clause_new_post_at_gen.
  Split.
  - Intros M' c. entailer_with ltac:(lia).
  - Intros Mcap. Exists Mcap. entailer_with ltac:(lia).
    subst retval. entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_record_entail_wit_2 : solver_record_entail_wit_2.
Proof.
  Unfold.
  right. intros.
  bind_fact ( 2 <= Zlength rec_words ) as H_Zlength.
  bind_fact ( mt_qhead (ms_core M0) = ms_qtail M0 ) as H_mt_qhead.
  sep_apply clause_new_post_physical__api_reentry.
  unfold clause_new_post_at_gen.
  Split.
  - Intros Mclause c_new.
    pose proof
      (clause_new_success_record_allocated__prep_pub_cap_exit
         rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c_new Mclause H_Zlength H_mt_qhead H0)
      as Hallocated.
    Exists Mclause c_new. entailer_with ltac:(lia).
    subst retval_2. entailer_with ltac:(lia).
  - Intros Mcap. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_record_entail_wit_3_1 : solver_record_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  bind_fact ( record_allocated rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c_new Mclause ) as H_record_allocated.
  unfold record_allocated in H_record_allocated.
  destruct H_record_allocated as [[[Hlen _] | [Hlen _]] _]; lia.
Qed.

Lemma proof_of_solver_record_entail_wit_3_2 : solver_record_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  bind_fact ( record_clause_cert rec_n rec_F M0 rec_words ) as H_record_clause_cert.
  bind_fact ( msolver_inv rec_n rec_F rec_A_arr rec_A_inst M0 ) as H_msolver_inv.
  bind_fact ( mt_qhead (ms_core M0) = ms_qtail M0 ) as H_mt_qhead.
  bind_fact ( ms_capacity_root_propagation_pending M0 = 0 ) as H_ms_capacity_root_propagation_pending.
  bind_fact ( msolver_seed_shadow M0 ) as H_msolver_seed_shadow.
  assert (Hlen : Zlength rec_words = 1) by lia.
  assert (Halloc :
    record_allocated rec_n rec_F rec_A_arr rec_A_inst M0 rec_words 0 M0).
  { unfold record_allocated.
    split.
    - left. split; [ | split ]; try assumption; reflexivity.
    - split; [exact H_record_clause_cert |].
      split; [exact H_msolver_inv |].
      split; [exact H_mt_qhead |].
      split; [exact H_ms_capacity_root_propagation_pending |].
      split; [exact H_msolver_seed_shadow |].
      split; reflexivity. }
  exact Halloc.
Qed.

Lemma proof_of_solver_record_entail_wit_4 : solver_record_entail_wit_4.
Proof.
  aggressive_pre_process.
  bind_fact ( record_allocated rec_n rec_F rec_A_arr rec_A_inst M0 rec_words c Mstage ) as H_record_allocated.
  sepcon_assoc_change.
  sepcon_lift (IntArray.missing_i learnt_ptr 0 0 (Zlength rec_words) rec_words).
  sepcon_lift (learnt_ptr # Int |-> Znth 0 rec_words 0).
  replace learnt_ptr with (learnt_ptr + 0 * sizeof(INT)) at 1 by lia.
  sep_apply_l_atomic
    (IntArray.missing_i_merge_to_full learnt_ptr 0 (Zlength rec_words)
       (Znth 0 rec_words 0) rec_words).
  - dump_pre_spatial. lia.
  - rewrite replace_Znth_Znth.
    unfold record_allocated in H_record_allocated.
    destruct H_record_allocated as [_ [Hcert _]].
    unfold record_clause_cert, record_ready_cert in Hcert.
    destruct Hcert as (_ & _ & _ & _ & Hfresh & _).
    unfold enqueue_post_at at 1.
    Intros qtail' assigns' levels' reasons' trail'.
    rename H into Htrans.
    assert (Hret : retval = 1).
    { unfold enqueue_transition in Htrans.
      destruct Htrans as
        [(Hassigned & Hret & _)|[(Hnonzero & _)|(Hzero & Hret & _)]];
        try exact Hret; congruence. }
    subst retval.
    unfold enqueue_post_at.
    Exists qtail' assigns' levels' reasons' trail'.
    msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_record return wits (1 proofs) ===== *)
Lemma proof_of_solver_record_return_wit_2 : solver_record_return_wit_2.
Proof.
  Unfold.
  right. intros.
  bind_fact ( clause_new_capacity_failure rec_n rec_F rec_A_arr rec_A_inst M0 Mcap rec_words ) as
    H_clause_new_capacity_failure.
  unfold solver_record_post_at.
  Right. Exists Mcap.
  destruct H_clause_new_capacity_failure as [Hprogress Hready].
  pose proof
    (clause_new_caps_progress_models__prep_pub_cap_exit
       M0 rec_words Mcap Hprogress) as [Hmodel Hmodel_cap].
  assert (Hreuse : minisat_record_reuse M0 rec_words Mcap).
  { intros [Hbase Hpositive].
    exact (proj1 (clause_new_caps_progress_base__record
      M0 rec_words Mcap Hprogress Hbase Hpositive)). }
  assert (Hcapacity : ms_cap Mcap = ms_cap M0).
  { unfold clause_new_caps_progress in Hprogress.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    end; subst Mcap; reflexivity. }
  entailer_with ltac:(lia).
  apply veci_rep_at_rep.
Qed.

(* ===== solver_reducedb entail wits (8 proofs) ===== *)
Lemma proof_of_solver_reducedb_entail_wit_1 : solver_reducedb_entail_wit_1.
Proof.
  Unfold.
  left. intros.
  subst Msorted.
  Exists words_sorted (msolver_reorder_learnts M0 db_sorted). entailer_with ltac:(lia);
    unfold msolver_reorder_learnts in *; simpl in *; entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_reducedb_entail_wit_2_1 : solver_reducedb_entail_wit_2_1.
Proof.
  msat_reducedb_entail_keep_words_p8 words Mnext_2.
Qed.

Lemma proof_of_solver_reducedb_entail_wit_2_2 : solver_reducedb_entail_wit_2_2.
Proof.
  msat_reducedb_compaction_step_exists_p8 j i words Mcur.
Qed.

Lemma proof_of_solver_reducedb_entail_wit_2_3 : solver_reducedb_entail_wit_2_3.
Proof.
  msat_reducedb_compaction_step_exists_p8 j i words Mcur.
Qed.

Lemma proof_of_solver_reducedb_entail_wit_3 : solver_reducedb_entail_wit_3.
Proof.
  Unfold.
  right. intros.
  bind_fact ( msolver_inv n F A_arr A_inst Mnext ) as H_msolver_inv.
  bind_fact ( db_compaction_inv Mnext words_next (i + 1) j ) as H_db_compaction_inv.
 entailer_with ltac:(lia);
    try (unfold db_compaction_inv in H_db_compaction_inv; lia).
  apply MSatFloatFacts.fp32_nonnegative_eq_refl.
  exact (msi_cla_inc_nonnegative H_msolver_inv).
Qed.

Lemma proof_of_solver_reducedb_entail_wit_4 : solver_reducedb_entail_wit_4.
Proof.
  Unfold.
  right. intros.
  bind_fact ( msolver_inv n F A_arr A_inst Mcur_2 ) as H_msolver_inv.
 entailer_with ltac:(lia).
  apply MSatFloatFacts.fp32_nonnegative_eq_refl.
  exact (msi_cla_inc_nonnegative H_msolver_inv).
Qed.

Lemma proof_of_solver_reducedb_entail_wit_5_1 : solver_reducedb_entail_wit_5_1.
Proof.
  msat_reducedb_entail_keep_words_p8 words Mnext_2.
Qed.

Lemma proof_of_solver_reducedb_entail_wit_6 : solver_reducedb_entail_wit_6.
Proof. exact proof_of_solver_reducedb_entail_wit_3. Qed.

(* ===== solver_reducedb partial_solve wits ===== *)


Lemma proof_of_solver_reducedb_partial_solve_wit_31_pure : solver_reducedb_partial_solve_wit_31_pure.
Proof.
  msat_reducedb_hdr_word_range_pure.
Qed.

Lemma proof_of_solver_reducedb_partial_solve_wit_35_pure : solver_reducedb_partial_solve_wit_35_pure.
Proof.
  msat_reducedb_first_lit_bounds_pure.
Qed.

(* ===== solver_reducedb safety wits (4 proofs) ===== *)
Lemma proof_of_solver_reducedb_safety_wit_1 : solver_reducedb_safety_wit_1.
Proof.
  Unfold.
  left. intros. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_reducedb_safety_wit_2 : solver_reducedb_safety_wit_2.
Proof.
  Unfold.
  left. intros. msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_reducedb_safety_wit_13 : solver_reducedb_safety_wit_13.
Proof.
  Unfold.
  left. intros.
  bind_fact ( db_compaction_inv Mnext words_next (i + 1) j ) as H_db_compaction_inv.
  unfold vecp_rep_at at 1. Intros_p Hvec.
  entailer_with ltac:(lia); unfold db_compaction_inv in H_db_compaction_inv; lia.
Qed.

Lemma proof_of_solver_reducedb_safety_wit_8 : solver_reducedb_safety_wit_8.
Proof. exact proof_of_solver_reducedb_safety_wit_13. Qed.

(* ===== solver_reducedb which_implies wits (6 proofs) ===== *)
Lemma proof_of_solver_reducedb_which_implies_wit_1 : solver_reducedb_which_implies_wit_1.
Proof.
  Unfold.
  left.
  intros.
  unfold solver_reducedb_pre_at, solver_rep_levels_wl_at, solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_db_mutation_frame_at,
    solver_ptrs_rep,
    solver_var_arrays_rep, solver_levels_slice_at,
    clause_new_scalars_frame, clause_new_vecs_frame,
    solver_scalars_rep, solver_fp_rep, solver_vecs_rep.
  Intros act asg opos rsn trl tgs.
  Exists rsn.
  destruct H as [Hinv [Hq [Hcap Hseed]]].
  assert (Hsort : learnt_sort_domain (ms_learnt M0) (db_words (ms_learnt M0))).
  { unfold learnt_sort_domain, db_words. split.
    - exact (msw_learnt_db (msi_weak Hinv)).
    - apply Permutation_refl. }
  assert (Hnodup : NoDup (db_words (ms_learnt M0))).
  { unfold db_words.
    pose proof (proj1 (msw_db_wf (msi_weak Hinv))) as Hdb.
    unfold msolver_db in Hdb.
    rewrite map_app in Hdb.
    revert Hdb.
    generalize (map fst (ms_prob M0)) as p.
    induction p as [|a p IHp]; intros Hdb.
    - exact Hdb.
    - inversion Hdb as [|x xs Hx Hrest]. subst.
      apply IHp. exact Hrest. }
  Exists act asg opos trl tgs.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_reducedb_which_implies_wit_2 : solver_reducedb_which_implies_wit_2.
Proof.
  Unfold.
  left.
  intros.
  bind_fact ( Permutation (db_words (ms_learnt M0)) words_sorted ) as H_Permutation.
  bind_fact ( msat_fp32_count_limit (Zlength (db_words (ms_learnt M0))) extra_lim ) as H_msat_fp32_count_limit.
  bind_fact ( Zlength (db_words (ms_learnt M0)) <= ms_learnt_cap M0 ) as H_Zlength.
  set (db := ms_learnt M0).
  assert (Hsym : Permutation words_sorted (map fst db)).
  { unfold db, db_words. apply Permutation_sym. exact H_Permutation. }
  destruct (@Permutation_map_inv (Z * clause_obj) Z fst words_sorted db Hsym)
    as [db_sorted [Hwords Hdb]].
  pose proof msat_clause_db_rep_perm as Hdbrep_gen.
  specialize (Hdbrep_gen _ _ Hdb).
  assert (Hlen : Zlength (db_words db) = Zlength words_sorted).
  { unfold db, db_words. rewrite !Zlength_correct.
    exact (f_equal Z.of_nat (Permutation_length H_Permutation)). }
  assert (Hwordsperm : Permutation (db_words db) (db_words db_sorted)).
  { unfold db_words. apply Permutation_map. exact Hdb. }
  assert (Hcomp : db_compaction_inv
      (msolver_reorder_learnts M0 db_sorted) words_sorted 0 0).
  { unfold db_compaction_inv, msolver_reorder_learnts,
      msolver_propagation_overlay, msolver_propagation_update. cbn.
    assert (Hnonneg : 0 <= Zlength words_sorted) by apply Zlength_nonneg.
    repeat split; try lia; try exact Hnonneg.
    unfold db_words.
    replace (sublist 0 0 words_sorted) with (@nil Z) by reflexivity.
    cbn. rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length words_sorted))) with
      (length words_sorted) by lia.
    rewrite firstn_all. symmetry. exact Hwords.
  }
  assert (Hlimit : msat_fp32_count_limit (Zlength words_sorted) extra_lim).
  { unfold msat_fp32_count_limit in *. intro Hpositive.
    apply H_msat_fp32_count_limit. change (0 < Zlength (db_words db)).
    rewrite Hlen. exact Hpositive. }
  assert (Hbase_sorted : minisat_base_watch_completed M0 ->
      minisat_base_watch_completed (msolver_reorder_learnts M0 db_sorted)).
  { apply minisat_base_watch_completed_reorder_learnts__api_reentry.
    exact Hdb. }
  Exists (msolver_reorder_learnts M0 db_sorted) db_sorted.
  entailer_with ltac:(int_auto);
    try (unfold db_words; symmetry; exact Hwords);
    try (apply msolver_inv_reorder_learnts__reducedb; assumption);
    try exact Hcomp;
    try exact Hlimit;
    try exact Hwordsperm.
  sep_apply Hdbrep_gen.
  cbn. rewrite Hlen.
  assert (Hb1 : 0 <= Zlength words_sorted <= ms_learnt_cap M0)
    by (split; [apply Zlength_nonneg | rewrite <- Hlen; exact H_Zlength]).
  assert (Hb2 : 0 < ms_learnt_cap M0 <= INT_MAX) by (split; assumption).
  sep_apply (solver_nested_vecp_rep_at_from_cells s "learnts" learnts
    words_sorted (ms_learnt_cap M0) Hb1 Hb2).
  msat_manual_entailer_with ltac:(lia).
Qed.

Lemma proof_of_solver_reducedb_which_implies_wit_3 : solver_reducedb_which_implies_wit_3.
Proof.
  msat_reducedb_focus_head_clause_p8.
Qed.

Lemma proof_of_solver_reducedb_which_implies_wit_4 : solver_reducedb_which_implies_wit_4.
Proof.
  Unfold. left. intros.
  msat_reducedb_focus_learnt_p8 n F A_arr A_inst Mcur i words lits_now lits_now activity_now Hdbi Hact Hpos Hev Hne.
Qed.

Lemma proof_of_solver_reducedb_which_implies_wit_7 : solver_reducedb_which_implies_wit_7.
Proof.
  msat_reducedb_focus_head_clause_p8.
Qed.

Lemma proof_of_solver_reducedb_which_implies_wit_8 : solver_reducedb_which_implies_wit_8.
Proof.
  Unfold. left. intros.
  msat_reducedb_focus_learnt_p8 n F A_arr A_inst Mcur i words lits_now lits_now activity_now Hdbi Hact Hpos Hev Hne.
Qed.

(* ===== solver_search partial_solve wits (19 proofs) ===== *)
Lemma proof_of_solver_search_partial_solve_wit_253_pure : solver_search_partial_solve_wit_253_pure.
Proof.
  msat_search_selection_state_range_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_254_pure : solver_search_partial_solve_wit_254_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_255_pure : solver_search_partial_solve_wit_255_pure.
Proof.
  msat_search_selection_state_range_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_256_pure : solver_search_partial_solve_wit_256_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_257_pure : solver_search_partial_solve_wit_257_pure.
Proof.
  msat_search_selection_state_range_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_258_pure : solver_search_partial_solve_wit_258_pure.
Proof.
  msat_search_decision_var_bounds_pure.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_259_pure : solver_search_partial_solve_wit_259_pure.
Proof.
  msat_search_selection_state_range_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_260_pure : solver_search_partial_solve_wit_260_pure.
Proof.
  msat_search_decision_lit_var_conjuncts_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_261_pure : solver_search_partial_solve_wit_261_pure.
Proof.
  msat_search_decision_lit_var_conjuncts_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_262_pure : solver_search_partial_solve_wit_262_pure.
Proof.
  msat_search_decision_lit_var_conjuncts_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_263_pure : solver_search_partial_solve_wit_263_pure.
Proof.
  msat_search_decision_lit_var_conjuncts_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_264_pure : solver_search_partial_solve_wit_264_pure.
Proof.
  Unfold.
  left; intros.
  bind_fact ( retval_2 = lit_neg_c retval_6 ) as H_retval_2.
  bind_fact ( retval_6 = retval + retval ) as H_retval_6.
  bind_fact ( Zlength (mt_lim (ms_core Mselected)) < n ) as H_Zlength.
  bind_fact ( enqueue_input n (lit_neg_c (retval + retval)) (ms_qtail Mselected) (mt_assigns (ms_core Mselected))
    (mt_levels (ms_core Mselected)) (ms_reason_words Mselected) (mt_trail (ms_core Mselected)) ) as H_enqueue_input.
  bind_fact ( solver_search_selection_state n F A_arr A_inst retval Mselected ) as H_solver_search_selection_state.
  msat_search_close_decision_lit_var_conjuncts H_Zlength H_enqueue_input H_solver_search_selection_state retval_2
    retval H_retval_2
    H_retval_6.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_265_pure : solver_search_partial_solve_wit_265_pure.
Proof.
  Unfold.
  left; intros.
  bind_fact ( retval_2 = lit_neg_c retval_6 ) as H_retval_2.
  bind_fact ( retval_6 = retval + retval ) as H_retval_6.
  bind_fact ( enqueue_input n (lit_neg_c (retval + retval)) (ms_qtail Mselected) (mt_assigns (ms_core Mselected))
    (mt_levels (ms_core Mselected)) (ms_reason_words Mselected) (mt_trail (ms_core Mselected)) ) as H_enqueue_input.
  bind_fact ( solver_search_selection_state n F A_arr A_inst retval Mselected ) as H_solver_search_selection_state.
  msat_search_close_decision_lit_var_entail H_retval_2 H_retval_6 H_enqueue_input H_solver_search_selection_state
    retval_2 retval
    Mselected.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_266_pure : solver_search_partial_solve_wit_266_pure.
Proof.
  msat_search_decision_lit_var_entail_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_267_pure : solver_search_partial_solve_wit_267_pure.
Proof.
  msat_search_decision_lit_var_entail_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_268_pure : solver_search_partial_solve_wit_268_pure.
Proof.
  msat_search_decision_lit_var_entail_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_269_pure : solver_search_partial_solve_wit_269_pure.
Proof.
  msat_search_decision_lit_var_entail_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_270_pure : solver_search_partial_solve_wit_270_pure.
Proof.
  msat_search_decision_lit_var_entail_p8.
Qed.

Lemma proof_of_solver_search_partial_solve_wit_271_pure : solver_search_partial_solve_wit_271_pure.
Proof.
  msat_search_decision_lit_var_entail_p8.
Qed.

(* ===== solver_search return wits (1 proofs) ===== *)
Lemma proof_of_solver_search_return_wit_11 : solver_search_return_wit_11.
Proof.
  Unfold.
  left. intros.
  unfold solver_search_result.
  Right.
  Exists Mcap.
  unfold solver_rep_wl. Exists levels.
  msat_manual_entailer_with ltac:(lia).
Qed.

(* ===== solver_simplify which_implies wits (4 proofs) ===== *)
Lemma proof_of_solver_simplify_which_implies_wit_14 : solver_simplify_which_implies_wit_14.
Proof.
  Unfold.
  left. intros.
  rename M_solver_simplify_spec into M.
  rename smp_wl_solver_simplify_spec into smp_wl.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i jcur ) as H_solver_simplify_db_compaction_inv.
  bind_fact ( i < Zlength words ) as H_i.
  bind_fact ( clause_simplify_result (co_lits co) (mt_assigns (ms_core Mcur)) 1 ) as H_clause_simplify_result.
  bind_fact ( Zlength (mt_lim (ms_core Mcur)) = 0 ) as H_Zlength.
  bind_fact ( mt_qhead (ms_core Mcur) = ms_qtail Mcur ) as H_mt_qhead.
  bind_fact ( ms_capacity_root_propagation_pending Mcur = 0 ) as H_ms_capacity_root_propagation_pending.
  bind_fact ( msolver_seed_shadow Mcur ) as H_msolver_seed_shadow.
  bind_fact ( db_lookup (solver_selected_db type Mcur) (Znth (i - 0) words 0) co ) as H_db_lookup.
  bind_fact (solver_simplify_reuse M Mcur) as Hreuse.
  pose proof H_solver_simplify_db_compaction_inv as Hcomp_seed.
  unfold solver_simplify_db_compaction_inv in Hcomp_seed.
  destruct Hcomp_seed as [Htype _].
  replace (i - 0) with i in * by lia.
  unfold clause_remove_post.
  Intros wm' stats'. coq_prop_lift.
  destruct H as [Hremove [Hstats [Hreasons Hunlocked]]].
  unfold clause_db_pair_remainder.
  Split.
  - Intros co1 pre post. coq_prop_lift.
    destruct H as [Hprob [Hlits Hlearnt]].
    destruct Htype as [-> | ->].
    + destruct (msat_simplify13_delete_arm_facts_p8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (or_introl (conj eq_refl eq_refl)) H_msolver_inv Hprob H_db_lookup
        H_clause_simplify_result H_Zlength H_mt_qhead
        H_ms_capacity_root_propagation_pending H_msolver_seed_shadow
        H_solver_simplify_db_compaction_inv H_i Hremove Hstats Hunlocked)
        as [Heq [Hdbnext Hstep]].
      subst co1.
      assert (Hdbclose : clause_db_rep pre ** clause_db_rep post
          |-- clause_db_rep (pre ++ post)).
      { sep_apply_r_atomic (clause_db_rep_app_intro pre post).
        entailer_with ltac:(lia). }
      assert (Hreuse_next : solver_simplify_reuse M
          (msolver_remove_clause Mcur false (Znth i words 0) wm' stats')).
      { unfold solver_simplify_reuse. intros Hentry.
        apply minisat_watch_completed_remove_clause__api_reentry.
        exact (Hreuse Hentry). }
      assert (Hcap_next : ms_cap
          (msolver_remove_clause Mcur false (Znth i words 0) wm' stats') = ms_cap M).
      { change (ms_cap Mcur = ms_cap M). assumption. }
      assert (Hroot_next : ms_root_level
          (msolver_remove_clause Mcur false (Znth i words 0) wm' stats') = ms_root_level M).
      { change (ms_root_level Mcur = ms_root_level M). assumption. }
      Exists (msolver_remove_clause Mcur false (Znth i words 0) wm' stats').
      entailer_with ltac:(lia).
      sep_apply Hdbclose.
      rewrite Hdbnext.
      rewrite (msat_simplify13_db_rest_after_remove_p8 s 0 false Mcur
        (Znth i words 0) wm' stats' reasons levels_ptr_solver_simplify_spec
        smp_wl asg (or_introl (conj eq_refl eq_refl))).
      cbn [solver_selected_cap msolver_remove_clause
        msolver_propagation_overlay msolver_propagation_update ].
      unfold solver_selected_learnt_db. cbn.
      entailer_with ltac:(lia).
    + unfold solver_selected_prob_db in Hprob. simpl in Hprob.
      destruct pre; discriminate Hprob.
  - Intros co1 pre post. coq_prop_lift.
    destruct H as [Hlearnt_db [Hlits Hlearnt]].
    destruct Htype as [-> | ->].
    + unfold solver_selected_learnt_db in Hlearnt_db.
      simpl in Hlearnt_db. destruct pre; discriminate Hlearnt_db.
    + destruct (msat_simplify13_delete_arm_facts_p8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (or_intror (conj eq_refl eq_refl)) H_msolver_inv Hlearnt_db H_db_lookup
        H_clause_simplify_result H_Zlength H_mt_qhead
        H_ms_capacity_root_propagation_pending H_msolver_seed_shadow
        H_solver_simplify_db_compaction_inv H_i Hremove Hstats Hunlocked)
        as [Heq [Hdbnext Hstep]].
      subst co1.
      assert (Hdbclose : clause_db_rep pre ** clause_db_rep post
          |-- clause_db_rep (pre ++ post)).
      { sep_apply_r_atomic (clause_db_rep_app_intro pre post).
        entailer_with ltac:(lia). }
      assert (Hreuse_next : solver_simplify_reuse M
          (msolver_remove_clause Mcur true (Znth i words 0) wm' stats')).
      { unfold solver_simplify_reuse. intros Hentry.
        apply minisat_watch_completed_remove_clause__api_reentry.
        exact (Hreuse Hentry). }
      assert (Hcap_next : ms_cap
          (msolver_remove_clause Mcur true (Znth i words 0) wm' stats') = ms_cap M).
      { change (ms_cap Mcur = ms_cap M). assumption. }
      assert (Hroot_next : ms_root_level
          (msolver_remove_clause Mcur true (Znth i words 0) wm' stats') = ms_root_level M).
      { change (ms_root_level Mcur = ms_root_level M). assumption. }
      Exists (msolver_remove_clause Mcur true (Znth i words 0) wm' stats').
      entailer_with ltac:(lia).
      sep_apply Hdbclose.
      rewrite Hdbnext.
      rewrite (msat_simplify13_db_rest_after_remove_p8 s 1 true Mcur
        (Znth i words 0) wm' stats' reasons levels_ptr_solver_simplify_spec
        smp_wl asg (or_intror (conj eq_refl eq_refl))).
      cbn [solver_selected_cap msolver_remove_clause
        msolver_propagation_overlay msolver_propagation_update ].
      unfold solver_selected_prob_db. cbn.
      msat_manual_entailer_with ltac:(lia).
Qed.

(* Both database-selection arms restore the same clause and vector cells
   after their distinct problem/learnt membership step. *)
Local Ltac msat_simplify_keep_db_close_p8 words i j cls co pre post :=
  let Hclose := fresh "Hclose" in
  assert (Hclose :
      clause_db_rep pre ** clause_db_rep post **
      clause_hdr_addr (Znth i words 0) # Int |->
        clause_hdr_word (co_learnt co) (Zlength (co_lits co)) **
      activity_state (Znth i words 0) (co_learnt co) **
      IntArray.seg (clause_lits_addr (Znth i words 0)) 0
        (Zlength (co_lits co)) (co_lits co)
    |-- clause_db_rep (pre ++ (Znth i words 0, co) :: post)) by
    (sep_apply_r_atomic (clause_db_rep_app_intro pre
      ((Znth i words 0, co) :: post));
     simpl; unfold MiniSatClause.rep;
     entailer_with ltac:(lia); try lia; apply Zlength_nonneg);
  sep_apply Hclose;
  unfold vecp_rep_at, solver_simplify_db_rest_at;
  entailer_with ltac:(int_auto);
    try rewrite Zlength_replace_Znth by lia;
    try lia;
    try apply Zlength_nonneg;
    unfold vecp_size_addr, vecp_cap_addr, vecp_ptr_addr;
    sep_apply_l_atomic (PtrArray.full_to_seg cls (Zlength words)
      (replace_Znth j (Znth i words 0) words));
    entailer_with ltac:(lia).

Lemma proof_of_solver_simplify_which_implies_wit_15 : solver_simplify_which_implies_wit_15.
Proof.
  Unfold.
  left. intros.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    smp_A_arr_solver_simplify_spec Mcur ) as H_msolver_inv.
  bind_fact ( solver_simplify_db_compaction_inv type Mcur words i j ) as H_solver_simplify_db_compaction_inv.
  bind_fact ( Zlength (mt_lim (ms_core Mcur)) = 0 ) as H_Zlength.
  bind_fact ( mt_qhead (ms_core Mcur) = ms_qtail Mcur ) as H_mt_qhead.
  bind_fact ( ms_capacity_root_propagation_pending Mcur = 0 ) as H_ms_capacity_root_propagation_pending.
  bind_fact ( msolver_seed_shadow Mcur ) as H_msolver_seed_shadow.
  unfold solver_simplify_db_compaction_inv in H_solver_simplify_db_compaction_inv.
  destruct H_solver_simplify_db_compaction_inv as [Htype [Hj0 [Hji [HiN Hdb]]]].
  assert (Hinv_keep : solver_simplify_db_compaction_inv type Mcur
      (solver_simplify_keep_words words i j) (i + 1) (j + 1)).
  { apply solver_simplify_keep_compaction_inv__simplify;
      try assumption.
    unfold solver_simplify_db_compaction_inv.
    repeat split; assumption. }
  assert (Hstep : solver_simplify_compaction_step
      smp_n_solver_simplify_spec smp_F_solver_simplify_spec
      smp_A_arr_solver_simplify_spec
      type Mcur words i j Mcur
      (solver_simplify_keep_words words i j) (j + 1)).
  { unfold solver_simplify_compaction_step,
      solver_simplify_keep_words.
    split.
    - left. split; [ | split ]; reflexivity.
    - split; [exact H_msolver_inv |].
      split; [exact H_Zlength |].
      split; [exact H_mt_qhead |].
      split; [exact H_ms_capacity_root_propagation_pending |].
      split; [exact H_msolver_seed_shadow |].
      split; [reflexivity |].
      split.
      + unfold msat_fp32_same. reflexivity.
      + exact Hinv_keep. }
  assert (Htail_current : sublist i (Zlength words) words =
      Znth i words 0 :: sublist (i + 1) (Zlength words) words).
  { rewrite (sublist_split i (Zlength words) (i + 1) words) by lia.
    rewrite (sublist_single 0 i words) by lia. reflexivity. }
  assert (Hinword : In (Znth i words 0)
      (map fst (solver_selected_db type Mcur))).
  { rewrite Hdb, Htail_current. apply in_or_app. right. left. reflexivity. }
  apply in_map_iff in Hinword.
  destruct Hinword as [[p co0] [Hp Hinselected]].
  cbn in Hp. subst p.
  assert (Hinfull : In (Znth i words 0, co0) (msolver_db Mcur)).
  { eapply solver_selected_db_in; eassumption. }
  assert (Hptrpos : 0 < Znth i words 0).
  { eapply db_wf_ptr_pos; [exact (msa_db_wf (msas_weak H_msolver_inv)) | exact Hinfull]. }
  assert (Hptreven : Znth i words 0 mod 2 = 0).
  { apply clause_ptr_mod2. eapply db_wf_even;
      [exact (msa_db_wf (msas_weak H_msolver_inv)) | exact Hinfull]. }
  unfold solver_simplify_compaction_step,
    solver_simplify_keep_words.
  entailer_with ltac:(lia).
  - prop_apply (PtrArray.undef_seg_valid cls (Zlength words)
      (solver_selected_cap type Mcur)).
    Intros_p Hcaplen.
    prop_apply (store_int_range (&( cs # "vecp_t" ->ₛ "cap"))
      (solver_selected_cap type Mcur)).
    Intros_p Hcaprange.
    replace (i - 0) with i by lia.
    unfold clause_db_pair_remainder.
    Split.
    + Intros co1 pre post. coq_prop_lift.
      destruct H as [Hprob [Hlits Hlearnt]].
      rewrite <- Hlits, <- Hlearnt.
      destruct Htype as [-> | ->].
      * unfold solver_selected_prob_db in Hprob. simpl in Hprob.
        unfold solver_selected_db. simpl. rewrite Hprob.
        msat_simplify_keep_db_close_p8 words i j cls co1 pre post.
      * unfold solver_selected_prob_db in Hprob. simpl in Hprob.
        destruct pre; discriminate Hprob.
    + Intros co1 pre post. coq_prop_lift.
      destruct H as [Hlearnt_db [Hlits Hlearnt]].
      rewrite <- Hlits, <- Hlearnt.
      destruct Htype as [-> | ->].
      * unfold solver_selected_learnt_db in Hlearnt_db. simpl in Hlearnt_db.
        destruct pre; discriminate Hlearnt_db.
      * unfold solver_selected_learnt_db in Hlearnt_db. simpl in Hlearnt_db.
        unfold solver_selected_db. simpl. rewrite Hlearnt_db.
        msat_simplify_keep_db_close_p8 words i j cls co1 pre post.
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_16 : solver_simplify_which_implies_wit_16.
Proof.
  Unfold.
  right. intros.
  unfold solver_simplify_outer_loop.
  Intros Mdone.
  Exists Mdone.
  unfold msat_fp32_same.
  msat_manual_entailer_with ltac:(int_auto).
Qed.

Lemma proof_of_solver_simplify_which_implies_wit_18 : solver_simplify_which_implies_wit_18.
Proof.
  unfold solver_simplify_which_implies_wit_18, stats_clauses_literals, stats_learnts_literals.
  Unfold.
  left. intros.
  rename M_solver_simplify_spec into M.
  bind_fact ( msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec smp_A_arr_solver_simplify_spec
    smp_A_arr_solver_simplify_spec Mdone ) as H_msolver_inv.
  bind_fact (solver_simplify_reuse M Mdone) as Hreuse.
  set (props := MiniSatTarget.uint64_sum_to_int
    (Znth 6 (ms_stats Mdone) 0) (Znth 8 (ms_stats Mdone) 0)).
  set (Mfinish := msolver_simpdb_update Mdone
    (mt_qhead (ms_core Mdone)) props).
  assert (Hreuse_finish : solver_simplify_reuse M Mfinish).
  { unfold solver_simplify_reuse. intros Hentry.
    apply minisat_watch_completed_same_fields__api_reentry with (M := Mdone);
      [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|].
    exact (Hreuse Hentry). }
  assert (Hcap_finish : ms_cap Mfinish = ms_cap M).
  { change (ms_cap Mdone = ms_cap M). assumption. }
  assert (Hroot_finish : ms_root_level Mfinish = ms_root_level M).
  { change (ms_root_level Mdone = ms_root_level M). assumption. }
  Exists Mfinish.
  assert (Hfinish_inv :
    msolver_inv_assuming_strong smp_n_solver_simplify_spec smp_F_solver_simplify_spec
      smp_A_arr_solver_simplify_spec smp_A_arr_solver_simplify_spec Mfinish).
  { unfold Mfinish.
    apply solver_assuming_simpdb_update__api_reentry.
    exact H_msolver_inv. }
  unfold solver_simplify_finish_transition.
  subst props.
  entailer_with ltac:(lia).
  unfold solver_rep_levels_wl_at, solver_cancel_owned.
  unfold solver_simplify_finish_frame_at, solver_search_bundle_at,
    solver_search_payload, solver_payload_cells.
  Intros act asg opos rsn trl tgs.
  Exists act asg opos rsn trl tgs.
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at.
  unfold solver_simplify_control_scalars_frame, solver_scalars_rep.
  unfold stats_without_simplify_totals_rep, stats_rep.
  replace (solver_fp_rep s Mfinish) with (solver_fp_rep s Mdone)
    by (unfold Mfinish; reflexivity).
  replace (solver_vecs_rep s Mfinish) with (solver_vecs_rep s Mdone)
    by (unfold Mfinish; reflexivity).
  replace (solver_trail_array_rep Mfinish trl)
    with (solver_trail_array_rep Mdone trl)
    by (unfold Mfinish; reflexivity).
  replace (solver_levels_slice_at s Mfinish levels_ptr_solver_simplify_spec)
    with (solver_levels_slice_at s Mdone levels_ptr_solver_simplify_spec)
    by (unfold Mfinish; reflexivity).
  subst Mfinish.
  set (P := MiniSatTarget.uint64_sum_to_int
    (Znth 6 (ms_stats Mdone) 0) (Znth 8 (ms_stats Mdone) 0)) in *.
  set (U := msolver_simpdb_update Mdone
    (mt_qhead (ms_core Mdone)) P) in *.
  pose proof (msa_shape (msas_weak Hfinish_inv)) as Hshape_finish.
  assert (HU_size : ms_size U = ms_size Mdone) by (unfold U; reflexivity).
  assert (HU_cap : ms_cap U = ms_cap Mdone) by (unfold U; reflexivity).
  assert (HU_qtail : ms_qtail U = ms_qtail Mdone) by (unfold U; reflexivity).
  assert (HU_pending_qhead : ms_capacity_pending_qhead U =
      ms_capacity_pending_qhead Mdone) by (unfold U; reflexivity).
  assert (HU_pending : ms_capacity_root_propagation_pending U =
      ms_capacity_root_propagation_pending Mdone)
    by (unfold U; reflexivity).
  assert (HU_core : ms_core U = ms_core Mdone) by (unfold U; reflexivity).
  assert (HU_root : ms_root_level U = ms_root_level Mdone)
    by (unfold U; reflexivity).
  assert (HU_simpdb_assigns : ms_simpdb_assigns U =
      mt_qhead (ms_core Mdone)) by (unfold U; reflexivity).
  assert (HU_simpdb_props : ms_simpdb_props U = P)
    by (unfold U; reflexivity).
  assert (HU_verbosity : ms_verbosity U = ms_verbosity Mdone)
    by (unfold U; reflexivity).
  assert (HU_binary : ms_binary U = ms_binary Mdone)
    by (unfold U; reflexivity).
  assert (HU_activity : ms_activity U = ms_activity Mdone)
    by (unfold U; reflexivity).
  assert (HU_orderpos : ms_orderpos U = ms_orderpos Mdone)
    by (unfold U; reflexivity).
  assert (HU_reasons : ms_reason_words U = ms_reason_words Mdone)
    by (unfold U; reflexivity).
  assert (HU_tags : ms_tags U = ms_tags Mdone)
    by (unfold U; reflexivity).
  assert (HU_wm : ms_wm U = ms_wm Mdone) by (unfold U; reflexivity).
  assert (HU_wcaps : ms_wcaps U = ms_wcaps Mdone)
    by (unfold U; reflexivity).
  assert (HU_prob : ms_prob U = ms_prob Mdone) by (unfold U; reflexivity).
  assert (HU_learnt : ms_learnt U = ms_learnt Mdone)
    by (unfold U; reflexivity).
  assert (HU_binary_lits : ms_binary_lits U = ms_binary_lits Mdone)
    by (unfold U; reflexivity).
  assert (HU_stats : ms_stats U = ms_stats Mdone)
    by (unfold U; reflexivity).
  rewrite HU_size, HU_cap, HU_qtail, HU_pending_qhead, HU_pending,
    HU_core, HU_root, HU_simpdb_assigns, HU_simpdb_props, HU_verbosity,
    HU_binary, HU_activity, HU_orderpos, HU_reasons, HU_tags, HU_wm,
    HU_wcaps, HU_prob, HU_learnt, HU_binary_lits, HU_stats.
  let finish := ltac:(csimpl; msat_manual_entailer_with ltac:(lia)) in
  first
    [ solve [msat_frame_entailer_with_p8 ltac:(lia); finish]
    | entailer_with ltac:(lia); finish ].
Qed.

(* ===== solver_solve entail wits (1 proofs) ===== *)
Lemma proof_of_solver_solve_entail_wit_1 : solver_solve_entail_wit_1.
Proof.
  Unfold. left; intros.
  rename n_solver_solve_spec into n.
  rename F_solver_solve_spec into F.
  rename M_solver_solve_spec into M0.
  rename solve_wl_solver_solve_spec into solve_wl.
  unfold solver_prepare_capacity_post.
  Intros Mcap.
  match goal with
  | H : solver_capacity_exhausted _ /\ _ |- _ =>
      destruct H as (Hexh & Hroot & Hseed & Hcap & Hwatch)
  end.
  assert (Hsize : ms_size Mcap = n)
    by exact (solver_operational_root_size n F Mcap Hroot).
  assert (Hcap_public : ms_cap Mcap = ms_cap M0) by (rewrite Hcap; exact PreH1).
  assert (Hguarded : solver_query_reuse_guard M0 -> solver_query_watch_ready Mcap)
    by (intros _; exact (Hwatch PreH2)).
  Exists Mcap.
  unfold solver_capacity_arm_at.
  repeat sep_apply store_ptr_undef_store_ptr.
  entailer_with ltac:(lia).
Qed.


(* ===== solver_solve safety wits (2 proofs) ===== *)
Lemma proof_of_solver_solve_safety_wit_11 : solver_solve_safety_wit_11.
Proof.
  Unfold. left; intros.
  msat_solve_assign_cell_not_int_min_p8 retval.
Qed.

Lemma proof_of_solver_solve_safety_wit_12 : solver_solve_safety_wit_12.
Proof.
  Unfold. left; intros.
  msat_solve_assign_cell_not_int_min_p8 retval.
Qed.
