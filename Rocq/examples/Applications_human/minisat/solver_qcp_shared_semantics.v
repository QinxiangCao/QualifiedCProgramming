From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_shared_memory.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** ** Derived facts: what the bundle does NOT need to carry. *)

(** The installed assumptions are well-formed literals -- derived, not
    carried: they are denotations of trail entries. *)
Lemma decisions_upto_wf : forall n t d,
  mtrail_wf n t -> Forall (literal_wf n) (decisions_upto t d).
Proof.
  intros n t d Hwf. unfold decisions_upto.
  apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [b [<- Hb]].
  assert (Hr : 0 <= b < Zlength (mt_trail t)).
  { pose proof (mtw_lim_range Hwf) as HR. rewrite Forall_forall in HR.
    apply HR. eapply In_ztake; eauto. }
  apply lit_denote_wf.
  apply (Forall_Znth_elim Z (lit_wf_c n) (mt_trail t) 0 b
           (mtw_trail_lits Hwf) Hr).
Qed.

Lemma msolver_inv_db_entailed : forall n F A_arr A_inst M,
  msolver_inv_weak n F A_arr A_inst M -> db_entailed F (msolver_view n M).
Proof.
  intros n F A_arr A_inst M Hinv c Hc.
  rewrite msolver_view_installed in Hc.
  unfold msolver_clauses, msolver_db in Hc.
  rewrite db_clauses_app in Hc.
  apply in_app_or in Hc. destruct Hc as [Hc|Hc].
  - pose proof (msw_db_matches Hinv) as Hm.
    unfold db_matches_cnf in Hm. rewrite Forall_forall in Hm.
    destruct (Hm c Hc) as [c0 [Hin0 Hperm]].
    apply (entails_clause_perm F c0 c).
    + apply Permutation_sym. exact Hperm.
    + apply entails_clause_in. exact Hin0.
  - pose proof (msw_db_implied Hinv) as Hi.
    unfold db_implied in Hi. rewrite Forall_forall in Hi. exact (Hi c Hc).
Qed.

Lemma db_clause_wf : forall n db p co,
  db_wf n db -> In (p, co) db -> Forall (literal_wf n) (denote_obj co).
Proof.
  intros n db p co Hwf Hin.
  destruct (db_wf_obj n db p co Hwf Hin) as [_ [Hall _]].
  apply lits_denote_wf. exact Hall.
Qed.

(** [trail_covers]: every true literal sits on the trail.  This is a pure
    consequence of [mtrail_wf] (a literal is determined by its variable and
    its sign, and both are pinned by the cell value). *)
Lemma mtrail_wf_trail_covers : forall n t,
  mtrail_wf n t -> trail_covers n (mt_assigns t) (mt_trail t).
Proof.
  intros n t Hwf l Hlwf Hlt.
  unfold lit_true in Hlt.
  assert (Hl0 : 0 <= l) by (destruct Hlwf; lia).
  assert (Hne : Znth (lit_var_c l) (mt_assigns t) 0 <> 0).
  { rewrite Hlt. apply lit_sig_nonzero. }
  pose proof (lit_var_c_in_range n l Hlwf) as Hvr.
  pose proof (proj1 (mtw_assigned_iff Hwf (lit_var_c l) Hvr) Hne) as Hin.
  destruct (In_Znth_index _ _ Hin) as [j [Hj Hjval]].
  rewrite Zlength_map_Z in Hj.
  assert (Hvar : lit_var_c (Znth j (mt_trail t) 0) = lit_var_c l).
  { rewrite <- Hjval. symmetry.
    apply (Znth_map Z Z lit_var_c (mt_trail t) j 0 0). exact Hj. }
  assert (Hjwf : lit_wf_c n (Znth j (mt_trail t) 0)).
  { apply (Forall_Znth_elim Z (lit_wf_c n) (mt_trail t) 0 j
             (mtw_trail_lits Hwf) Hj). }
  assert (Hj0 : 0 <= Znth j (mt_trail t) 0) by (destruct Hjwf; lia).
  assert (Hsig : Znth (lit_var_c (Znth j (mt_trail t) 0)) (mt_assigns t) 0
                 = lit_sig (Znth j (mt_trail t) 0)).
  { pose proof (mtw_trail_true Hwf) as HF. rewrite Forall_forall in HF.
    apply HF. apply Znth_In. exact Hj. }
  rewrite Hvar, Hlt in Hsig.
  assert (Hsign : lit_sign_c (Znth j (mt_trail t) 0) = lit_sign_c l).
  { unfold lit_sig in Hsig. unfold lit_sign_c.
    destruct (Z.odd l); destruct (Z.odd (Znth j (mt_trail t) 0));
      solve [reflexivity | lia]. }
  exists j. split; [exact Hj|].
  pose proof (lit_pack_unpack (Znth j (mt_trail t) 0) Hj0) as Hp1.
  pose proof (lit_pack_unpack l Hl0) as Hp2.
  rewrite Hvar, Hsign in Hp1. lia.
Qed.

(** ** From [lbool] cells to total valuations. *)

Lemma assigns_pv_rho_agree : forall assigns x b,
  assigns_pv assigns x = Some b -> rho_of_model assigns x = b.
Proof.
  intros assigns x b H. unfold assigns_pv, assigns_val in H.
  unfold rho_of_model.
  destruct b.
  - apply lbool_val_true in H. rewrite H. reflexivity.
  - apply lbool_val_false in H. rewrite H. reflexivity.
Qed.

Lemma mt_pv_rho_agree : forall t x b,
  mt_pv t x = Some b -> rho_of_model (mt_assigns t) x = b.
Proof.
  intros t x b H.
  destruct (Z_le_dec 0 x) as [Hx|Hx].
  - rewrite mt_pv_nonneg in H by lia.
    apply assigns_pv_rho_agree. unfold assigns_pv, assigns_val. exact H.
  - rewrite mt_pv_neg in H by lia. discriminate.
Qed.

Lemma eval_partial_mt_pv_true : forall t l,
  eval_partial_literal (mt_pv t) l = Some true ->
  eval_literal (rho_of_model (mt_assigns t)) l = true.
Proof.
  intros t l H.
  destruct (mt_pv t (literal_var l)) as [b|] eqn:Hb.
  - eapply eval_partial_literal_total_agree;
      [exact Hb | apply mt_pv_rho_agree; exact Hb | exact H].
  - unfold eval_partial_literal in H. rewrite Hb in H. discriminate.
Qed.

Lemma root_satisfied_clause : forall t c,
  root_satisfied t c -> clause_satisfied (rho_of_model (mt_assigns t)) c.
Proof.
  intros t c [l [Hin [Htrue _]]].
  exists l. split; [exact Hin | apply eval_partial_mt_pv_true; exact Htrue].
Qed.

(** [assigns_total] follows from an empty order heap.  The [heap_covers] fact
    is an explicit hypothesis (it lives in the STRONG bundle only). *)
Lemma msolver_inv_assigns_total : forall n F A_arr A_inst M,
  msolver_inv_weak n F A_arr A_inst M ->
  heap_covers n (msolver_heap M) (mt_assigns (ms_core M))
              (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
  ms_order M = [] ->
  assigns_total n (mt_assigns (ms_core M)).
Proof.
  intros n F A_arr A_inst M Hinv Hhc Hempty v Hv.
  pose proof (msw_trail_wf Hinv) as Hwf.
  assert (Hne : Znth v (mt_assigns (ms_core M)) 0 <> 0).
  { eapply heap_covers_total;
      [apply (msw_heap_wf Hinv) | exact Hempty | exact Hhc | exact Hv]. }
  assert (Hidx : 0 <= v < Zlength (mt_assigns (ms_core M)))
    by (rewrite (mtw_assigns_len Hwf); exact Hv).
  pose proof (Forall_Znth_elim Z lbool_cell (mt_assigns (ms_core M)) 0 v
                (mtw_cells Hwf) Hidx) as Hcell.
  unfold lbool_cell in Hcell. destruct Hcell as [H|[H|H]]; auto.
  contradiction.
Qed.

(** ** The saved model. *)

Definition model_copies (n : Z) (M : msolver) : Prop :=
  Zlength (ms_model M) = n /\
  (forall v, 0 <= v < n ->
     Znth v (ms_model M) 0 = Znth v (mt_assigns (ms_core M)) 0).

Definition model_saved (n : Z) (F : cnf) (A : list literal) (M : msolver) : Prop :=
  Zlength (ms_model M) = n /\
  Forall (fun z => z = -1 \/ z = 1) (ms_model M) /\
  models (rho_of_model (ms_model M)) (cnf_with_units F A).


(** Every model cell is a decided polarity: the saved model is TOTAL, not
    partial.  Named so the SAT arm of [solver_solve]'s C contract can state it
    without writing a lambda (annotations cannot). *)
Definition model_is_total (asgn : list Z) : Prop :=
  Forall (fun z => z = -1 \/ z = 1) asgn.

Definition assumptions_true_under (rho : valuation) (A : list literal) : Prop :=
  Forall (fun a => eval_literal rho a = true) A.

Lemma sat_arm_unfolded_iff : forall n F A M,
  (ms_size M = n /\ model_saved n F A M) <->
  (ms_size M = n /\
   Zlength (ms_model M) = n /\
   model_is_total (ms_model M) /\
   models (rho_of_model (ms_model M)) F /\
   assumptions_true_under (rho_of_model (ms_model M)) A).
Proof.
  intros n F A M.
  unfold model_saved, model_is_total, assumptions_true_under.
  rewrite models_cnf_with_units.
  tauto.
Qed.

Lemma model_copies_values : forall n M,
  model_copies n M ->
  assigns_total n (mt_assigns (ms_core M)) ->
  Forall (fun z => z = -1 \/ z = 1) (ms_model M).
Proof.
  intros n M [Hlength Hcopy] Htotal.
  apply Forall_forall. intros z Hin.
  destruct (In_Znth_index (ms_model M) z Hin) as [i [Hi Hz]].
  assert (Hrange : 0 <= i < n) by lia.
  rewrite <- Hz, Hcopy by exact Hrange.
  destruct (Htotal i Hrange); tauto.
Qed.

Lemma rho_of_model_agrees_total : forall n M x,
  model_copies n M -> 0 <= x < n ->
  rho_of_model (ms_model M) x = rho_of_model (mt_assigns (ms_core M)) x.
Proof.
  intros n M x [_ Hcopy] Hx.
  unfold rho_of_model. rewrite (Hcopy x Hx). reflexivity.
Qed.

(** ** The SAT endgame.

    The persistent weak bundle is combined with the propagation frontier and
    heap coverage available at the SAT fixpoint. *)

Lemma msolver_db_satisfied : forall n F A_arr A_inst M p co,
  msolver_inv_weak n F A_arr A_inst M ->
  minisat_watch_frontier n (msolver_db M)
              (mt_assigns (ms_core M))
              (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
  heap_covers n (msolver_heap M) (mt_assigns (ms_core M))
              (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
  mt_qhead (ms_core M) = Zlength (mt_trail (ms_core M)) ->
  ms_order M = [] ->
  In (p, co) (msolver_db M) ->
  clause_satisfied (rho_of_model (mt_assigns (ms_core M))) (denote_obj co).
Proof.
  intros n F A_arr A_inst M p co Hinv Hfrontier Hhc Hfix Hempty Hin.
  eapply minisat_watch_fixpoint_sat with (n := n) (p := p);
    [ apply (msw_db_wf Hinv)
    | exact Hfrontier
    | exact Hfix
    | apply mtrail_wf_trail_covers; apply (msw_trail_wf Hinv)
    | eapply msolver_inv_assigns_total; [exact Hinv | exact Hhc | exact Hempty]
    | exact Hin ].
Qed.

Theorem sat_endgame : forall n F A_arr A_inst M,
  msolver_inv_weak n F A_arr A_inst M ->
  minisat_watch_frontier n (msolver_db M)
              (mt_assigns (ms_core M))
              (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
  heap_covers n (msolver_heap M) (mt_assigns (ms_core M))
              (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
  mt_qhead (ms_core M) = Zlength (mt_trail (ms_core M)) ->
  ms_order M = [] ->
  models (rho_of_model (mt_assigns (ms_core M))) (cnf_with_units F A_arr).
Proof.
  intros n F A_arr A_inst M Hinv Hws Hhc Hfix Hempty.
  apply models_cnf_with_units. split.
  - (* the original clauses *)
    unfold models. apply Forall_forall. intros c Hc.
    destruct (msw_db_complete Hinv c Hc) as [[c' [Hin' Hperm]]|Hroot].
    + destruct (db_clauses_in_inv _ _ Hin') as [p [co [Hin'' Heq]]].
      apply (clause_satisfied_perm _ c' c Hperm).
      rewrite <- Heq.
      eapply msolver_db_satisfied; try eassumption.
      unfold msolver_db. apply in_or_app. left. exact Hin''.
    + apply root_satisfied_clause. exact Hroot.
  -
    apply Forall_forall. intros a Ha.
    pose proof (msw_assump_sat Hinv) as HS. rewrite Forall_forall in HS.
    destruct (HS a Ha) as [Htrue _].
    apply eval_partial_mt_pv_true. exact Htrue.
Qed.

Theorem sat_endgame_model : forall n F A_arr A_inst M,
  msolver_inv_weak n F A_arr A_inst M ->
  minisat_watch_frontier n (msolver_db M)
              (mt_assigns (ms_core M))
              (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
  heap_covers n (msolver_heap M) (mt_assigns (ms_core M))
              (mt_trail (ms_core M)) (mt_qhead (ms_core M)) ->
  mt_qhead (ms_core M) = Zlength (mt_trail (ms_core M)) ->
  ms_order M = [] ->
  model_copies n M ->
  model_saved n F A_arr M.
Proof.
  intros n F A_arr A_inst M Hinv Hws Hhc Hfix Hempty Hcopy.
  split; [apply Hcopy|]. split.
  - eapply model_copies_values; [exact Hcopy|].
    eapply msolver_inv_assigns_total; eassumption.
  - eapply models_congr_on_range with
      (n := n) (rho := rho_of_model (mt_assigns (ms_core M))).
    + apply cnf_with_units_wf;
        [apply (msw_F_wf Hinv) | apply (msw_A_wf Hinv)].
    + intros x Hx. symmetry.
      apply (rho_of_model_agrees_total n M x); assumption.
    + eapply sat_endgame; eassumption.
Qed.

(** ** The UNSAT endgame.
    The weak bundle is paired with an explicit installed decision list [A0]
    and [incl A0 A_arr]. The stored root can be stale during assumption
    installation. [unsat_endgame_at_root] specializes this to [A_inst]
    at the search-loop return. *)

Theorem unsat_endgame : forall n F A_arr A_inst M A0 Cd,
  msolver_inv_weak n F A_arr A_inst M ->
  decisions_upto (ms_core M) (Zlength (mt_lim (ms_core M))) = A0 ->
  incl A0 A_arr ->
  entails_clause F Cd ->
  clause_false (assigns_pv (mt_assigns (ms_core M))) Cd ->
  Forall (literal_wf n) Cd ->
  cnf_unsat n (cnf_with_units F A_arr).
Proof.
  intros n F A_arr A_inst M A0 Cd Hinv Hdec Hincl Hent Hfalse Hcdwf.
  apply cnf_unsat_units_mono with (A := A0);
    [exact Hincl | apply (msw_A_wf Hinv) |].
  eapply root_conflict_unsat with (t := ms_core M).
  - apply (msw_F_wf Hinv).
  - rewrite <- Hdec. apply decisions_upto_wf. apply (msw_trail_wf Hinv).
  - apply (msw_trail_wf Hinv).
  - apply (msw_trail_impl Hinv).
  - exact Hdec.
  - exact Hent.
  - exact Hfalse.
  - exact Hcdwf.
Qed.

(** The [solver_search] return-site shape: at [dlevel = root_level] the
    installed decisions ARE [A_inst], so the explicit hypotheses collapse
    into the bundle. *)
Theorem unsat_endgame_at_root : forall n F A_arr A_inst M Cd,
  msolver_inv_weak n F A_arr A_inst M ->
  solver_at_root M ->
  entails_clause F Cd ->
  clause_false (assigns_pv (mt_assigns (ms_core M))) Cd ->
  Forall (literal_wf n) Cd ->
  cnf_unsat n (cnf_with_units F A_arr).
Proof.
  intros n F A_arr A_inst M Cd Hinv Hroot Hent Hfalse Hcdwf.
  eapply unsat_endgame with (A0 := A_inst);
    [ exact Hinv
    | unfold solver_at_root in Hroot; rewrite Hroot;
      apply (msw_assumptions Hinv)
    | apply (msw_assump_incl Hinv)
    | exact Hent | exact Hfalse | exact Hcdwf ].
Qed.

(** ** UNSAT route 1: an assumption whose negation is already trail-implied.

    In [solver_solve]'s assumption loop, case [-1] can
    be reached with NO conflict clause: the assumption [a] reads back false,
    i.e. [~a]'s literal is on the trail.  No [F]-entailed clause refutes the
    state -- the refutation is [F /\ decisions |= ~a] against [a itself in
    A_arr].  This lemma is that route, in pure trail vocabulary. *)
Lemma assumption_false_unsat : forall n F A t A0 a i,
  cnf_wf n F ->
  Forall (literal_wf n) A ->
  trail_implied F t ->
  decisions_upto t (Zlength (mt_lim t)) = A0 ->
  incl A0 A ->
  In a A ->
  0 <= i < Zlength (mt_trail t) ->
  lit_denote (Znth i (mt_trail t) 0) = literal_neg a ->
  cnf_unsat n (cnf_with_units F A).
Proof.
  intros n F A t A0 a i HFwf HAwf Hti Hdec Hincl Ha Hi Hneg.
  split; [apply cnf_with_units_wf; assumption|].
  intros rho Hbound Hm.
  pose proof (proj1 (models_cnf_with_units rho F A) Hm) as [HmF HAtrue].
  assert (Hsub : incl (decisions_upto t (level_of_index t i)) A).
  { intros y Hy. apply Hincl. rewrite <- Hdec.
    exact (decisions_upto_incl t (level_of_index t i) (Zlength (mt_lim t))
             (conj (level_of_index_nonneg t i) (prop_level_processed_level_le t i))
             y Hy). }
  assert (Hmsub : models rho
            (cnf_with_units F (decisions_upto t (level_of_index t i)))).
  { apply models_cnf_with_units. split; [exact HmF|].
    apply Forall_forall. intros y Hy.
    rewrite Forall_forall in HAtrue. apply HAtrue. apply Hsub. exact Hy. }
  pose proof (Hti i (Znth i (mt_trail t) 0) Hi eq_refl) as Hent.
  destruct (Hent rho Hmsub) as [k [Hk Hktrue]].
  destruct Hk as [<-|[]].
  rewrite Hneg, eval_literal_neg in Hktrue.
  rewrite Forall_forall in HAtrue.
  rewrite (HAtrue a Ha) in Hktrue.
  discriminate.
Qed.

Record msolver_inv_assuming_strong
    (n : Z) (F : cnf) (A_arr A_proc : list literal) (M : msolver) : Prop := {
  msas_weak        : msolver_inv_assuming n F A_arr A_proc M;
  msas_prop_level  : prop_level (ms_core M);
  msas_watch_frontier : minisat_watch_frontier n (msolver_db M)
                                (mt_assigns (ms_core M))
                                (mt_trail (ms_core M))
                                (mt_qhead (ms_core M));
  msas_heap_covers : heap_covers n (msolver_heap M)
                                (mt_assigns (ms_core M))
                                (mt_trail (ms_core M)) (mt_qhead (ms_core M));
  msas_reasonless_current : current_reasonless_earliest n M
}.

Arguments msas_weak        {n F A_arr A_proc M} _.

Arguments msas_prop_level  {n F A_arr A_proc M} _.

Arguments msas_watch_frontier {n F A_arr A_proc M} _.

Arguments msas_heap_covers {n F A_arr A_proc M} _.

Arguments msas_reasonless_current {n F A_arr A_proc M} _.

(** At a state where [root_level] is CURRENT ([solver_at_root] -- the
    search-loop return sites), the weak bundle subsumes the assuming bundle
    with [A_proc := A_arr]: the assumption loop is over, so the whole array
    is processed. *)
Lemma msolver_inv_weak_assuming : forall n F A_arr A_inst M,
  msolver_inv_weak n F A_arr A_inst M ->
  solver_at_root M ->
  msolver_inv_assuming n F A_arr A_arr M.
Proof.
  intros n F A_arr A_inst M H Hroot. unfold solver_at_root in Hroot.
  constructor.
  - exact (msw_size H).
  - exact (msw_n_range H).
  - exact (msw_shape H).
  - exact (msw_F_wf H).
  - exact (msw_A_wf H).
  - exact (msw_trail_wf H).
  - exact (msw_level_bound H).
  - exists A_inst. split.
    + rewrite Hroot. exact (msw_assumptions H).
    + exact (msw_assump_incl H).
  - apply incl_refl.
  - rewrite Hroot. exact (msw_assump_sat H).
  - exact (msw_stable H).
  - exact (msw_reasons_ent H).
  - exact (msw_reasons_inj H).
  - exact (msw_trail_impl H).
  - exact (msw_db_wf H).
  - exact (msw_db_matches H).
  - exact (msw_db_implied H).
  - exact (msw_db_complete H).
  - exact (msw_learnt_db H).
  - exact (msw_prob_db H).
  - exact (msw_binary_out H).
  - exact (msw_reasons_mem H).
  - exact (msw_reason_head H).
  - exact (msw_reason_bin H).
  - exact (msw_wmap_exact H).
  - exact (msw_tags_clear H).
  - exact (msw_heap_wf H).
  - exact (msw_cla_inc_nonnegative H).
  - exact (msw_seed H).
Qed.

Theorem assuming_conflict_unsat : forall n F A_arr A_proc M Cd,
  msolver_inv_assuming n F A_arr A_proc M ->
  entails_clause F Cd ->
  clause_false (assigns_pv (mt_assigns (ms_core M))) Cd ->
  Forall (literal_wf n) Cd ->
  cnf_unsat n (cnf_with_units F A_arr).
Proof.
  intros n F A_arr A_proc M Cd Hinv Hent Hfalse Hcdwf.
  destruct (msa_decisions Hinv) as [A0 [Hdec Hincl0]].
  apply cnf_unsat_units_mono with (A := A0);
    [ intros y Hy; apply (msa_proc_incl Hinv); apply Hincl0; exact Hy
    | apply (msa_A_wf Hinv) |].
  eapply root_conflict_unsat with (t := ms_core M).
  - apply (msa_F_wf Hinv).
  - rewrite <- Hdec. apply decisions_upto_wf. apply (msa_trail_wf Hinv).
  - apply (msa_trail_wf Hinv).
  - apply (msa_trail_impl Hinv).
  - exact Hdec.
  - exact Hent.
  - exact Hfalse.
  - exact Hcdwf.
Qed.

(** Mid-loop assumption failure: the cursor assumption is false and is
    not required to belong to the processed prefix [A_proc]. *)
Theorem assuming_false_assumption_unsat : forall n F A_arr A_proc M a i,
  msolver_inv_assuming n F A_arr A_proc M ->
  In a A_arr ->
  0 <= i < Zlength (mt_trail (ms_core M)) ->
  lit_denote (Znth i (mt_trail (ms_core M)) 0) = literal_neg a ->
  cnf_unsat n (cnf_with_units F A_arr).
Proof.
  intros n F A_arr A_proc M a i Hinv Ha Hi Hneg.
  destruct (msa_decisions Hinv) as [A0 [Hdec Hincl0]].
  eapply assumption_false_unsat with (t := ms_core M) (A0 := A0);
    [ apply (msa_F_wf Hinv) | apply (msa_A_wf Hinv)
    | apply (msa_trail_impl Hinv) | exact Hdec
    | intros y Hy; apply (msa_proc_incl Hinv); apply Hincl0; exact Hy
    | exact Ha | exact Hi | exact Hneg ].
Qed.

Lemma msolver_inv_propagation_of_strong : forall n F A_arr A_inst M,
  msolver_inv n F A_arr A_inst M ->
  msolver_inv_propagation n F A_arr A_inst M.
Proof.
  intros n F A_arr A_inst M H. constructor.
  - exact (msi_weak H).
  - exact (msi_prop_level H).
  - exact (msi_watch_frontier H).
  - left. exact (msi_heap_covers H).
  - exact (msi_reasonless_current H).
Qed.

Lemma solver_propagation_drained_strong :
  forall n F A_arr A_inst M,
    solver_propagation_inv
      n F A_arr (PropagationStable A_inst) M ->
    mt_qhead (ms_core M) = ms_qtail M ->
    msolver_inv n F A_arr A_inst M.
Proof.
  msat_propagation_drained.
Qed.

Lemma solver_propagation_drained_assuming_strong :
  forall n F A_arr A_proc M,
    solver_propagation_inv
      n F A_arr (PropagationAssuming A_proc) M ->
    mt_qhead (ms_core M) = ms_qtail M ->
    msolver_inv_assuming_strong n F A_arr A_proc M.
Proof.
  msat_propagation_drained.
Qed.

(** Shared context view: [msolver_inv_ctx] is the invariant component of
    [solver_propagation_weak], without its pending-capacity conjunct. *)
Definition msolver_inv_ctx
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) : Prop :=
  match K with
  | PropagationStable A_inst => msolver_inv_weak n F A_arr A_inst M
  | PropagationAssuming A_proc => msolver_inv_assuming n F A_arr A_proc M
  end.

Lemma msolver_inv_ctx_of_propagation :
  forall n F A_arr K M,
    solver_propagation_inv n F A_arr K M -> msolver_inv_ctx n F A_arr K M.
Proof.
  intros n F A_arr K M Hinv. unfold solver_propagation_inv in Hinv.
  destruct K as [A_inst|A_proc]; destruct Hinv as [_ Hprop];
    cbn in Hprop |- *; destruct Hprop as [Hweak _ _ _ _]; exact Hweak.
Qed.

Lemma msolver_inv_ctx_core_facts :
  forall n F A_arr K M,
    msolver_inv_ctx n F A_arr K M ->
    n = ms_size M /\ mtrail_wf n (ms_core M) /\ heap_wf n (msolver_heap M).
Proof.
  intros n F A_arr K M H. destruct K as [A_inst|A_proc]; cbn in H.
  - split; [exact (msw_size H)|]. split;
      [exact (msw_trail_wf H)|exact (msw_heap_wf H)].
  - split; [exact (msa_size H)|]. split;
      [exact (msa_trail_wf H)|exact (msa_heap_wf H)].
Qed.

Lemma msolver_inv_ctx_shape :
  forall n F A_arr K M, msolver_inv_ctx n F A_arr K M -> solver_shape M.
Proof.
  intros n F A_arr K M H. destruct K as [A_inst|A_proc]; cbn in H;
    [exact (msw_shape H)|exact (msa_shape H)].
Qed.

Lemma propagation_inv_context_facts__analyze :
  forall n F A_arr K M,
    solver_propagation_inv n F A_arr K M ->
    ms_capacity_root_propagation_pending M = 0 /\
    prop_level (ms_core M) /\
    minisat_watch_frontier n (msolver_db M) (mt_assigns (ms_core M))
      (mt_trail (ms_core M)) (mt_qhead (ms_core M)) /\
    propagation_heap_ready n M /\
    current_reasonless_earliest n M /\
    mtrail_wf n (ms_core M) /\
    wmap_exact n (msolver_db M) (ms_wm M).
Proof.
  intros n F A_arr K M Hinv.
  destruct Hinv as [Hroot Hprop].
  destruct K as [A_inst | A_proc]; cbn in Hprop;
    destruct Hprop as [Hweak Hlevel Hfrontier Hheap_ready Hreasonless].
  - split; [exact Hroot|]. split; [exact Hlevel|]. split; [exact Hfrontier|].
    split; [exact Hheap_ready|]. split; [exact Hreasonless|].
    split; [exact (msw_trail_wf Hweak)|exact (msw_wmap_exact Hweak)].
  - split; [exact Hroot|]. split; [exact Hlevel|]. split; [exact Hfrontier|].
    split; [exact Hheap_ready|]. split; [exact Hreasonless|].
    split; [exact (msa_trail_wf Hweak)|exact (msa_wmap_exact Hweak)].
Qed.

Lemma solver_propagation_weak_reason_core :
  forall n F A_arr K M,
  solver_propagation_weak n F A_arr K M ->
  n = ms_size M /\
  reasons_match n (ms_core M) (msolver_db M)
    (ms_reason_words M) (ms_reason_of M) /\
  binary_reason_same_level M.
Proof.
  intros n F A_arr K M [_ Hweak]. destruct K as [A_inst | A_proc];
    cbn in Hweak.
  - split; [exact (msw_size Hweak) |]. split;
      [exact (msw_reasons_mem Hweak) | exact (msw_reason_bin Hweak)].
  - split; [exact (msa_size Hweak) |]. split;
      [exact (msa_reasons_mem Hweak) | exact (msa_reason_bin Hweak)].
Qed.

(** Fields that are semantically fixed throughout analysis.  Activity,
    heap order, scratch vectors, clause/variable increments, and statistics
    are intentionally omitted because the C updates them. *)
Definition analysis_core_equiv (M0 M : msolver) : Prop :=
  ms_size M = ms_size M0 /\ ms_cap M = ms_cap M0 /\
  ms_qtail M = ms_qtail M0 /\ ms_core M = ms_core M0 /\
  ms_root_level M = ms_root_level M0 /\
  ms_reason_words M = ms_reason_words M0 /\
  ms_reason_of M = ms_reason_of M0 /\
  ms_prob M = ms_prob M0 /\ ms_learnt M = ms_learnt M0 /\
  ms_binary M = ms_binary M0 /\ ms_binary_lits M = ms_binary_lits M0 /\
  ms_wm M = ms_wm M0 /\
  ms_model M = ms_model M0 /\
  ms_cla_decay M = ms_cla_decay M0 /\
  ms_random_seed M = ms_random_seed M0 /\
  ms_capacity_pending_qhead M = ms_capacity_pending_qhead M0 /\
  ms_capacity_root_propagation_pending M =
    ms_capacity_root_propagation_pending M0 /\
  ms_simpdb_assigns M = ms_simpdb_assigns M0 /\
  ms_simpdb_props M = ms_simpdb_props M0.

(** Facts frozen while analysis changes heuristic and scratch fields.
    Assumption bookkeeping and mutable heap/shape facts are deliberately
    excluded, so both propagation contexts share this semantic view. *)
Record analysis_semantic_context (n : Z) (F : cnf) (M : msolver) : Prop := {
  asc_size : n = ms_size M;
  asc_trail_wf : mtrail_wf n (ms_core M);
  asc_stable : stable_view (msolver_view n M);
  asc_reasons_ent : reasons_entailed F (msolver_view n M);
  asc_reasons_inj : reasons_var_injective (msolver_view n M);
  asc_trail_impl : trail_implied F (ms_core M);
  asc_db_wf : db_wf n (msolver_db M);
  asc_reason_head : reason_head_ok M;
  asc_binary_out : ~ In (ms_binary M) (map fst (msolver_db M));
  asc_prob_db : prob_db (ms_prob M);
  asc_learnt_db : learnt_db (ms_learnt M);
  asc_qtail : Zlength (mt_trail (ms_core M)) = ms_qtail M;
  asc_reasons_mem : reasons_match n (ms_core M) (msolver_db M)
    (ms_reason_words M) (ms_reason_of M);
  asc_reason_bin : binary_reason_same_level M
}.

Lemma msolver_inv_ctx_analysis_semantics :
  forall n F A_arr K M,
    msolver_inv_ctx n F A_arr K M -> analysis_semantic_context n F M.
Proof.
  intros n F A_arr K M Hctx.
  pose proof (msolver_inv_ctx_shape n F A_arr K M Hctx) as Hshape.
  assert (Hqtail : Zlength (mt_trail (ms_core M)) = ms_qtail M).
  { unfold solver_shape in Hshape. tauto. }
  destruct K as [A_inst | A_proc]; cbn in Hctx;
    destruct Hctx; constructor; assumption.
Qed.

Lemma analysis_core_equiv_semantics : forall n F M0 M,
  analysis_core_equiv M0 M ->
  analysis_semantic_context n F M0 -> analysis_semantic_context n F M.
Proof.
  intros n F M0 M Hequiv Hctx.
  destruct Hequiv as
    (Esize & Ecap & Eqtail & Ecore & Eroot & Ewords & Ereason &
     Eprob & Elearnt & Ebinary & Erest).
  destruct Hctx; constructor;
    unfold reason_head_ok, binary_reason_same_level,
      msolver_view, msolver_clauses, msolver_db in *;
    rewrite ?Esize, ?Eqtail, ?Ecore, ?Ewords, ?Ereason,
      ?Eprob, ?Elearnt, ?Ebinary; assumption.
Qed.

Lemma analysis_core_equiv_shape : forall M0 M,
  analysis_core_equiv M0 M -> solver_shape M0 ->
  Zlength (ms_orderpos M) = ms_size M ->
  Zlength (ms_activity M) = ms_size M ->
  Zlength (ms_tags M) = ms_size M ->
  Zlength (ms_stats M) = 11 -> solver_shape M.
Proof.
  intros M0 M Hequiv Hshape Horder Hactivity Htags Hstats.
  destruct Hequiv as
    (Hsize & Hcap & Hqtail & Hcore & Hroot & Hwords & Hreason & Hprob &
     Hlearnt & Hbinary & Hbinarylits & Hwm &
     Hmodel & Hcladecay & Hseed & Hpendingq &
     Hpending & Hsimpassigns & Hsimpprops).
  unfold solver_shape in Hshape |- *.
  rewrite Horder, Hactivity, Htags, Hstats, Hsize, Hcap, Hqtail, Hcore,
    Hroot, Hwords, Hbinary, Hbinarylits, Hwm, Hpendingq, Hpending.
  tauto.
Qed.

Lemma analysis_core_equiv_analyze_tag_step_self :
  forall M tags tagged activity orderpos order var_inc,
    analysis_core_equiv M
      (analyze_tag_step_msolver M tags tagged
         activity orderpos order var_inc).
Proof.
  intros. unfold analysis_core_equiv. repeat split; reflexivity.
Qed.

Lemma analysis_core_equiv_analyze_tag_step :
  forall M0 M tags tagged activity orderpos order var_inc,
    analysis_core_equiv M0 M ->
    analysis_core_equiv M0
      (analyze_tag_step_msolver M tags tagged
         activity orderpos order var_inc).
Proof.
  intros M0 M tags tagged activity orderpos order var_inc H.
  exact H.
Qed.

(** Analysis may reorder the heap and mutate activity/scratch data, including
    the exact clause increment, so the focus-aware propagation token is
    retained on an equivalent entry state; full heap coverage and the
    operation-closed nonnegative clause-increment carrier are restated for the
    current heap.  The current-level focus equation is also restated at the
    current record, so an isolated cancellation cut need not recover it from
    the existential entry state. *)
Definition analysis_cancel_ready
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) (focus : Z) : Prop :=
  exists M0,
    propagation_cancel_ready n F A_arr K M0 focus /\
    analysis_core_equiv M0 M /\
    heap_wf n (msolver_heap M) /\
    heap_covers n (msolver_heap M)
      (mt_assigns (ms_core M)) (mt_trail (ms_core M))
      (mt_qhead (ms_core M)) /\
    current_reasonless_earliest n M /\
    level_of (msolver_view n M) (lit_var_c focus) =
      Some (Zlength (mt_lim (ms_core M))) /\
    msat_fp32_nonnegative (ms_cla_inc M).

Lemma analysis_cancel_ready_semantics : forall n F A_arr K M focus,
  analysis_cancel_ready n F A_arr K M focus -> analysis_semantic_context n F M.
Proof.
  intros n F A_arr K M focus [M0 [[[Hpending Hctx] Hcancel] [Hequiv Hrest]]].
  eapply analysis_core_equiv_semantics; [exact Hequiv |].
  exact (msolver_inv_ctx_analysis_semantics n F A_arr K M0 Hctx).
Qed.

Lemma analysis_cancel_ready_reason_core :
  forall n F A_arr K M focus,
  analysis_cancel_ready n F A_arr K M focus ->
  n = ms_size M /\
  reasons_match n (ms_core M) (msolver_db M)
    (ms_reason_words M) (ms_reason_of M) /\
  binary_reason_same_level M.
Proof.
  intros n F A_arr K M focus Hready.
  pose proof (analysis_cancel_ready_semantics n F A_arr K M focus Hready) as Hctx.
  exact (conj (asc_size _ _ _ Hctx)
    (conj (asc_reasons_mem _ _ _ Hctx) (asc_reason_bin _ _ _ Hctx))).
Qed.

Lemma analysis_cancel_ready_tagged_reason_nodup :
  forall n F A_arr K M focus v C,
  analysis_cancel_ready n F A_arr K M focus ->
  0 <= v < n ->
  is_tag (Znth v (ms_reason_words M) 0) = true ->
  ms_reason_of M v = Some C ->
  NoDup (map literal_var C).
Proof.
  intros n F A_arr K M focus v C Hready Hv Htag HC.
  destruct (analysis_cancel_ready_reason_core
    n F A_arr K M focus Hready) as [Hsize [Hmatch Hbinary]].
  assert (HvM : 0 <= v < ms_size M) by lia.
  destruct (Hbinary v HvM Htag) as [Hwf [_ Hdifferent]].
  assert (Hpositive : 0 < Znth v (ms_reason_words M) 0).
  { eapply tag_pos_of_lit_wf; [exact Htag | exact Hwf]. }
  assert (Hshape := reason_word_ok_tag
    (ms_core M) v (msolver_db M) (Znth v (ms_reason_words M) 0)
    (ms_reason_of M v) Hpositive Htag (Hmatch v Hv)).
  rewrite HC in Hshape. inversion Hshape. subst C.
  apply tagged_reason_nodup_vars.
  rewrite (trail_lit_of_var (ms_core M) v) by lia.
  intro Heq. apply Hdifferent. symmetry. exact Heq.
Qed.

Definition reason_target_wf
    (n : Z) (M : msolver) (v p : Z) (C : clause) : Prop :=
  0 <= v < ms_size M /\ p = Znth v (ms_reason_words M) 0 /\
  p <> 0 /\ ms_reason_of M v = Some C /\
  ((is_tag p = true /\ 0 < p /\ lit_wf_c n (tag_lit p)) \/
   (exists co, is_tag p = false /\ p <> ms_binary M /\
      In (p, co) (msolver_db M) /\ C = denote_obj co)).

Definition analysis_clause_focus
    (n : Z) (M : msolver) (p : Z) (C : clause) : Prop :=
  (p = ms_binary M /\ C = lits_denote (ms_binary_lits M) /\
   ms_binary_lits M <> []) \/
  (exists v, reason_target_wf n M v p C /\ is_tag p = true) \/
  (exists co, p <> ms_binary M /\ is_tag p = false /\
     In (p, co) (msolver_db M) /\ C = denote_obj co).

Definition analysis_clause_remainder
    (M : msolver) (p : Z) (is_learnt : bool) (lits : list Z) : Assertion :=
  (“ p = ms_binary M /\ is_learnt = false /\
      lits = ms_binary_lits M /\ ms_binary_lits M <> [] ” &&
    (clause_db_rep (ms_prob M) ** clause_db_rep (ms_learnt M))) ||
  (“ p <> ms_binary M ” &&
    (clause_db_pair_remainder
       (ms_prob M) (ms_learnt M) p is_learnt lits **
     binary_scratch_rep (ms_binary M) (ms_binary_lits M))).

Definition removable_reason_focus
    (n : Z) (M : msolver) (v p : Z) (C : clause) : Prop :=
  reason_target_wf n M v p C.

(** Opaque symbolic-execution carrier for the untouched part of the reason
    array while a native non-null assertion reads the focused cell.  Keeping
    the hole abstract prevents a read from being refolded as a same-value
    [replace_Znth]; the adjacent annotation obligations open and close exactly
    this standard array resource. *)
Definition removable_reason_array_hole
    (p i n : Z) (words : list Z) : Assertion :=
  PtrArray.missing_i p i 0 n words.

Definition minimize_tag_scope
    (n : Z) (M : msolver) (base T : list Z) : Prop :=
  forall x, In x (ms_tagged M) ->
    level_of (msolver_view n M) x =
      Some (current_level (msolver_view n M)) \/
    In x (map lit_var_c base) \/ In x T.

Definition removable_dfs_loop_inv
    (n : Z) (M : msolver) (l minl : Z)
    (base tags tagged stack done : list Z) : Prop :=
  exists fresh,
    tagged = base ++ fresh /\
    analysis_tags_exact n tags tagged /\
    NoDup (lit_var_c l :: fresh) /\
    NoDup (done ++ stack) /\
    Permutation (done ++ stack) (lit_var_c l :: fresh) /\
    (forall x, In x (lit_var_c l :: fresh) ->
       assigned_below_current (msolver_view n M) x) /\
    (forall v, In v stack -> exists p C,
       reason_target_wf n M v p C) /\
    dfs_witness (msolver_view n M) base done stack /\
    0 <= minl <= UINT_MAX.

Definition removable_reason_scan_inv
    (n : Z) (M : msolver) (l minl : Z)
    (base done stack tags tagged : list Z) (C : clause)
    (v p i : Z) : Prop :=
  removable_dfs_loop_inv n M l minl base tags tagged (v :: stack) done /\
  removable_reason_focus n M v p C /\
  1 <= i <= Zlength C /\ Forall (literal_wf n) C /\
  forall k, 1 <= k < i ->
    let x := literal_var (Znth k C (Pos 0)) in
    level_of (msolver_view n M) x = Some 0 \/
    In x base \/ In x done \/ In x stack.

Definition removable_rollback_inv
    (n top j : Z) (base entry_tags tags0 tagged tags : list Z) : Prop :=
  0 <= top /\ top <= j /\ j <= Zlength tagged /\
  top = Zlength base /\
  sublist 0 top tagged = base /\
  analysis_tags_exact n entry_tags base /\
  analysis_tags_exact n tags0 tagged /\
  tags = clear_indices (sublist top j tagged) tags0.

Definition solver_lit_removable_post
    (s l rsn lvl trl tgs n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) (focus ret : Z)
    (wl : Z) : Assertion :=
  EX M' : msolver,
    “ analysis_cancel_ready n F A_arr K M' focus /\
      msolver_seed_shadow M' /\
      analysis_core_equiv M M' /\
      ((ret = 0 /\ ms_tags M' = ms_tags M /\
          ms_tagged M' = ms_tagged M) \/
       (ret = 1 /\ ms_stack M' = [] /\
          exists fresh,
            ms_tagged M' = ms_tagged M ++ fresh /\
            analysis_tags_exact n (ms_tags M') (ms_tagged M') /\
            removable_witness (msolver_view n M)
              (ms_tagged M) (lit_var_c l :: fresh) /\
            (forall x, In x (lit_var_c l :: fresh) ->
               assigned_below_current (msolver_view n M) x))) ” &&
    solver_rep_analyze_at s M' rsn lvl trl tgs wl.

(** The C do-loop has two genuinely different header states: the untouched
    conflict on its first entry, and a selected trail literal whose reason is
    scanned on later entries. *)
Inductive analyze_resolution_phase : Type :=
| AnalyzeInitial
| AnalyzeSelected.

Definition analyze_resolution_loop_inv
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) (focus : Z)
    (phase : analyze_resolution_phase)
    (c : Z) (C : clause) (words : list Z) (cnt ind p : Z) : Prop :=
  analysis_cancel_ready n F A_arr K M focus /\
  0 <= ind < ms_qtail M /\
  1 <= Zlength words <= n /\
  ms_root_level M < Zlength (mt_lim (ms_core M)) /\
  analysis_tags_exact n (ms_tags M) (ms_tagged M) /\
  match phase with
  | AnalyzeInitial =>
      p = -2 /\ cnt = 0 /\ ind + 1 = ms_qtail M /\
      propagation_conflict_cert n F M C /\
      conflict_ptr_denotes M c C /\ ms_tagged M = [] /\
      lits_denote (tl words) = []
  | AnalyzeSelected =>
      exists S R learnt x,
        p <> -2 /\ x = lit_var_c p /\ In x S /\
        Znth (ind + 1) (mt_trail (ms_core M)) 0 = p /\
        assignment_rank (msolver_view n M) x =
          Some (Z.to_nat (ind + 1)) /\
        (forall s, In s S -> s <> x ->
           rank_lt (msolver_view n M) s x) /\
        lit_denote p = view_lit (msolver_view n M) x /\
        cnt + 1 = Zlength S /\ 0 < cnt /\
        c = Znth x (ms_reason_words M) 0 /\
        ms_reason_of M x = Some C /\
        reason_target_wf n M x c C /\
        analysis_clause_focus n M c C /\
        reason_valid (msolver_view n M) x C /\
        entails_clause F C /\
        Forall (literal_wf n) C /\ NoDup (map literal_var C) /\
        analyze_inv F (msolver_view n M) S R learnt /\
        lits_denote (tl words) = learnt /\
        Permutation (ms_tagged M) (analyze_tags S R learnt)
  end.

(** Incremental scan of a concrete, non-tagged conflict/reason clause.  The
    initial arm scans the whole conflict; a selected reason skips its true
    head.  The equations are the prefix versions of [analyze_init] and
    [analyze_resolve_step], so the full-prefix exit can invoke those lemmas
    without reconstructing an informal set of tags. *)
Definition analyze_clause_scan_inv
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M0 M : msolver) (focus : Z)
    (phase : analyze_resolution_phase) (C : clause) (j ind : Z)
    (S0 R0 : list Z) (learnt0 : clause) (x : Z)
    (S R : list Z) (learnt : clause) (words : list Z) (cnt : Z) : Prop :=
  analysis_cancel_ready n F A_arr K M focus /\
  analysis_core_equiv M0 M /\
  0 <= ind < ms_qtail M /\
  ms_root_level M < Zlength (mt_lim (ms_core M)) /\
  Forall (literal_wf n) C /\ NoDup (map literal_var C) /\
  0 <= j <= Zlength C /\
  cnt = Zlength S /\
  1 <= Zlength words <= n /\
  lits_denote (tl words) = learnt /\
  analysis_tags_exact n (ms_tags M) (ms_tagged M) /\
  Permutation (ms_tagged M) (analyze_tags S R learnt) /\
  match phase with
  | AnalyzeInitial =>
      S0 = [] /\ R0 = [] /\ learnt0 = [] /\ x = -1 /\
      ind + 1 = ms_qtail M0 /\
      propagation_conflict_cert n F M0 C /\
      S = analyze_start_S (msolver_view n M0) (sublist 0 j C) /\
      R = [] /\
      learnt =
        analyze_start_learnt (msolver_view n M0) (sublist 0 j C)
  | AnalyzeSelected =>
      0 < cnt /\
      1 <= j /\ In x S0 /\
      assignment_rank (msolver_view n M0) x =
        Some (Z.to_nat (ind + 1)) /\
      (forall s, In s S0 -> s <> x ->
         rank_lt (msolver_view n M0) s x) /\
      analyze_inv F (msolver_view n M0) S0 R0 learnt0 /\
      ms_reason_of M0 x = Some C /\
      reason_valid (msolver_view n M0) x C /\
      entails_clause F C /\
      S = resolve_S (msolver_view n M0) x (sublist 1 j C)
            S0 R0 learnt0 /\
      R = x :: R0 /\
      learnt = resolve_learnt (msolver_view n M0) (sublist 1 j C)
                  S0 R0 learnt0
  end.

(** The tagged reason has one physical side word.  Its
    variable is at the selected variable's current level, so the native
    lower-level push arm is unreachable; the logical step still resolves
    against the full two-literal reason clause. *)
Definition analyze_tagged_step
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M0 M : msolver) (focus pword q : Z)
    (C : clause) (S0 R0 : list Z) (learnt0 : clause) (x : Z)
    (S R : list Z) (learnt : clause) (words : list Z) (cnt : Z) : Prop :=
  analysis_cancel_ready n F A_arr K M focus /\
  analysis_core_equiv M0 M /\
  ms_root_level M < Zlength (mt_lim (ms_core M)) /\
  reason_target_wf n M0 x pword C /\ is_tag pword = true /\
  q = tag_lit pword /\ In x S0 /\
  (forall s, In s S0 -> s <> x ->
     rank_lt (msolver_view n M0) s x) /\
  analyze_inv F (msolver_view n M0) S0 R0 learnt0 /\
  reason_valid (msolver_view n M0) x C /\ entails_clause F C /\
  NoDup (map literal_var C) /\
  level_of (msolver_view n M0) (lit_var_c q) =
    Some (current_level (msolver_view n M0)) /\
  S = resolve_S (msolver_view n M0) x C S0 R0 learnt0 /\
  R = x :: R0 /\
  learnt = resolve_learnt (msolver_view n M0) C S0 R0 learnt0 /\
  cnt = Zlength S /\ 1 <= Zlength words <= n /\
  lits_denote (tl words) = learnt /\
  analysis_tags_exact n (ms_tags M) (ms_tagged M) /\
  Permutation (ms_tagged M) (analyze_tags S R learnt).

(** State after the current clause has been resolved and before the reverse
    trail scan.  Pending tags are at/below [ind], while all resolved tags are
    strictly above it; this makes each unchecked decrement safe and prevents
    stopping on an old resolved tag. *)
Definition analyze_backward_scan_inv
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) (focus : Z)
    (words : list Z) (cnt ind : Z) (S R : list Z)
    (learnt : clause) : Prop :=
  analysis_cancel_ready n F A_arr K M focus /\
  analyze_inv F (msolver_view n M) S R learnt /\
  cnt = Zlength S /\ 0 < cnt /\
  0 <= ind < ms_qtail M /\
  1 <= Zlength words <= n /\
  ms_root_level M < Zlength (mt_lim (ms_core M)) /\
  lits_denote (tl words) = learnt /\
  analysis_tags_exact n (ms_tags M) (ms_tagged M) /\
  Permutation (ms_tagged M) (analyze_tags S R learnt) /\
  (forall x, In x S -> exists r,
     assignment_rank (msolver_view n M) x = Some r /\
     Z.of_nat r <= ind) /\
  (forall x, In x R -> exists r,
     assignment_rank (msolver_view n M) x = Some r /\ ind < Z.of_nat r) /\
  exists x r, In x S /\
    assignment_rank (msolver_view n M) x = Some r /\ Z.of_nat r <= ind.

(** Zero-counter state immediately after selecting the UIP trail word.  This
    is deliberately retained across the do-loop exit: without it the head
    overwrite would have no derivation path to [analyze_exit]. *)
Definition analyze_resolution_exit
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) (focus p : Z)
    (words : list Z) : Prop :=
  analysis_cancel_ready n F A_arr K M focus /\
  1 <= Zlength words <= n /\
  ms_root_level M < Zlength (mt_lim (ms_core M)) /\
  exists x R learnt r,
    x = lit_var_c p /\
    assignment_rank (msolver_view n M) x = Some r /\
    Znth (Z.of_nat r) (mt_trail (ms_core M)) 0 = p /\
    lit_denote p = view_lit (msolver_view n M) x /\
    analyze_inv F (msolver_view n M) [x] R learnt /\
    lits_denote (tl words) = learnt /\
    analysis_tags_exact n (ms_tags M) (ms_tagged M) /\
    Permutation (ms_tagged M) (analyze_tags [x] R learnt).

Definition analyze_minimize_loop_inv
    (n : Z) (M : msolver) (original kept removed words T : list Z)
    (i j : Z) : Prop :=
  1 <= j /\ j <= i /\ i <= Zlength original /\
  Zlength words = Zlength original /\
  Znth 0 words 0 = Znth 0 original 0 /\
  Forall (lit_wf_c n) original /\
  Forall (lit_wf_c n) words /\
  Zlength kept = j /\
  Zlength removed = i - j /\
  sublist i (Zlength original) words =
    sublist i (Zlength original) original /\
  analysis_tags_exact n (ms_tags M) (ms_tagged M) /\
  let pending := sublist i (Zlength original) original in
  Permutation (lits_denote (tl original))
    (lits_denote (tl kept) ++ lits_denote removed ++
     lits_denote pending) /\
  removable_witness (msolver_view n M)
    (map lit_var_c (kept ++ pending)) T /\
  minimize_tag_scope n M (kept ++ pending) T /\
  Forall (fun l => In (lit_var_c l) T) removed /\
  (forall x, In x T -> exists d r,
     level_of (msolver_view n M) x = Some d /\
     assignment_rank (msolver_view n M) x = Some r /\
     d < current_level (msolver_view n M)) /\
  sublist 0 j words = sublist 0 j kept.

Definition analyze_clear_loop_inv
    (n i : Z) (tagged tags0 tags : list Z) : Prop :=
  0 <= i <= Zlength tagged /\
  analysis_tags_exact n tags0 tagged /\
  tags = clear_indices (sublist 0 i tagged) tags0.

Definition analyze_max_loop_inv
    (n : Z) (M : msolver) (words : list Z)
    (i max_i max_level : Z) : Prop :=
  2 <= i <= Zlength words /\ 1 <= max_i < i /\
  Forall (lit_wf_c n) words /\
  max_level = Znth (lit_var_c (Znth max_i words 0))
                   (mt_levels (ms_core M)) 0 /\
  (forall k, 1 <= k < i ->
     Znth (lit_var_c (Znth k words 0)) (mt_levels (ms_core M)) 0
       <= max_level).

Definition learned_tail_positive
    (n : Z) (M : msolver) (words : list Z) : Prop :=
  Forall (fun l => exists d,
    level_of (msolver_view n M) (literal_var l) = Some d /\ 0 < d)
    (lits_denote (tl words)).


Definition record_watch1_positive (M : msolver) (words : list Z) : Prop :=
  2 <= Zlength words ->
  0 < Znth (lit_var_c (Znth 1 words 0)) (mt_levels (ms_core M)) 0.


Definition analyze_clause_cert
    (n : Z) (F : cnf) (M : msolver) (words : list Z) : Prop :=
  uip_exit_cert F (msolver_view n M) (lits_denote words) /\
  ms_root_level M < Zlength (mt_lim (ms_core M)) /\
  learned_tail_positive n M words.


Definition analyze_backjump_cert
    (n : Z) (M : msolver) (words : list Z) (blevel : Z) : Prop :=
  1 <= Zlength words /\
  blevel =
    (if Z.ltb 1 (Zlength words)
     then Z.max (ms_root_level M)
       (Znth (lit_var_c (Znth 1 words 0))
             (mt_levels (ms_core M)) 0)
     else ms_root_level M) /\
  ms_root_level M <= blevel /\
  blevel < Zlength (mt_lim (ms_core M)) /\
  level_of (msolver_view n M)
    (literal_var (lit_denote (Znth 0 words 0))) =
      Some (Zlength (mt_lim (ms_core M))) /\
  Forall (fun l => exists d,
    level_of (msolver_view n M) (literal_var l) = Some d /\ d <= blevel)
    (tl (lits_denote words)).

Definition minisat_base_watch_completed (M : msolver) : Prop :=
  forall owner co, In (owner,co) (msolver_db M) ->
    (processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
       (mt_qhead (ms_core M)) (lit_neg_c (co_watch0 co)) ->
     Znth (lit_var_c (co_watch0 co)) (mt_levels (ms_core M)) 0 = 0 ->
     lit_true (mt_assigns (ms_core M)) (co_watch1 co) /\
     Znth (lit_var_c (co_watch1 co)) (mt_levels (ms_core M)) 0 = 0) /\
    (processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
       (mt_qhead (ms_core M)) (lit_neg_c (co_watch1 co)) ->
     Znth (lit_var_c (co_watch1 co)) (mt_levels (ms_core M)) 0 = 0 ->
     lit_true (mt_assigns (ms_core M)) (co_watch0 co) /\
     Znth (lit_var_c (co_watch0 co)) (mt_levels (ms_core M)) 0 = 0).

Lemma analysis_core_equiv_base_completion__api_reentry : forall M0 M,
  analysis_core_equiv M0 M ->
  minisat_base_watch_completed M0 -> minisat_base_watch_completed M.
Proof.
  intros M0 M Hcore Hcomplete.
  destruct Hcore as [_ [_ [_ [Htrail [_ [_ [_ [Hprob [Hlearnt _]]]]]]]]].
  unfold minisat_base_watch_completed, msolver_db in *.
  rewrite Htrail, Hprob, Hlearnt. exact Hcomplete.
Qed.

Definition solver_analyze_pre
    (s c learnt lvl n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) (focus : Z)
    (C : clause) (wl : Z) : Assertion :=
  “ analysis_cancel_ready n F A_arr K M focus /\
    propagation_conflict_cert n F M C /\
    conflict_ptr_denotes M c C /\
    msolver_seed_shadow M /\
    ms_root_level M < Zlength (mt_lim (ms_core M)) /\
    ms_tags M = repeat 0 (Z.to_nat n) /\ ms_tagged M = [] /\
    2 * n <= INT_MAX ” &&
  (solver_rep_levels_wl_at s M wl lvl ** Veci.rep learnt []).

Definition solver_analyze_post
    (s learnt lvl n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (entry : msolver)
    (focus : Z) (wl : Z) : Assertion :=
  EX M' : msolver, EX words : list Z, EX blevel : Z,
    “ analysis_cancel_ready n F A_arr K M' focus /\
      msolver_seed_shadow M' /\
      ms_model M' = ms_model entry /\
      ms_cap M' = ms_cap entry /\
      (minisat_base_watch_completed entry -> minisat_base_watch_completed M') /\
      ms_cla_decay M' = ms_cla_decay entry /\
      1 <= Zlength words <= n /\
      Forall (lit_wf_c n) words /\ NoDup (map lit_var_c words) /\
      analyze_clause_cert n F M' words /\
      analyze_backjump_cert n M' words blevel /\
      ms_tags M' = repeat 0 (Z.to_nat n) /\ ms_tagged M' = [] ” &&
    (solver_rep_levels_wl_at s M' wl lvl ** Veci.rep learnt words).

Definition minisat_watch_completed (M : msolver) : Prop :=
  forall p co, In (p, co) (msolver_db M) ->
    (processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
       (mt_qhead (ms_core M)) (lit_neg_c (co_watch0 co)) ->
     lit_true (mt_assigns (ms_core M)) (co_watch1 co) /\
     Znth (lit_var_c (co_watch1 co)) (mt_levels (ms_core M)) 0 <=
     Znth (lit_var_c (co_watch0 co)) (mt_levels (ms_core M)) 0) /\
    (processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
       (mt_qhead (ms_core M)) (lit_neg_c (co_watch1 co)) ->
     lit_true (mt_assigns (ms_core M)) (co_watch0 co) /\
     Znth (lit_var_c (co_watch0 co)) (mt_levels (ms_core M)) 0 <=
     Znth (lit_var_c (co_watch1 co)) (mt_levels (ms_core M)) 0).


Definition minisat_base_watch_completed_except (M : msolver) (focus : Z) : Prop :=
  forall owner co, In (owner,co) (msolver_db M) ->
    (lit_neg_c (co_watch0 co) <> focus ->
     processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
       (mt_qhead (ms_core M)) (lit_neg_c (co_watch0 co)) ->
     Znth (lit_var_c (co_watch0 co)) (mt_levels (ms_core M)) 0 = 0 ->
     lit_true (mt_assigns (ms_core M)) (co_watch1 co) /\
     Znth (lit_var_c (co_watch1 co)) (mt_levels (ms_core M)) 0 = 0) /\
    (lit_neg_c (co_watch1 co) <> focus ->
     processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
       (mt_qhead (ms_core M)) (lit_neg_c (co_watch1 co)) ->
     Znth (lit_var_c (co_watch1 co)) (mt_levels (ms_core M)) 0 = 0 ->
     lit_true (mt_assigns (ms_core M)) (co_watch0 co) /\
     Znth (lit_var_c (co_watch0 co)) (mt_levels (ms_core M)) 0 = 0).


Definition minisat_watch_completed_except (M : msolver) (focus : Z) : Prop :=
  forall p co, In (p, co) (msolver_db M) ->
    (lit_neg_c (co_watch0 co) <> focus ->
     processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
       (mt_qhead (ms_core M)) (lit_neg_c (co_watch0 co)) ->
     lit_true (mt_assigns (ms_core M)) (co_watch1 co) /\
     Znth (lit_var_c (co_watch1 co)) (mt_levels (ms_core M)) 0 <=
     Znth (lit_var_c (co_watch0 co)) (mt_levels (ms_core M)) 0) /\
    (lit_neg_c (co_watch1 co) <> focus ->
     processed (mt_assigns (ms_core M)) (mt_trail (ms_core M))
       (mt_qhead (ms_core M)) (lit_neg_c (co_watch1 co)) ->
     lit_true (mt_assigns (ms_core M)) (co_watch0 co) /\
     Znth (lit_var_c (co_watch0 co)) (mt_levels (ms_core M)) 0 <=
     Znth (lit_var_c (co_watch1 co)) (mt_levels (ms_core M)) 0).

Definition minisat_base_focus_word_completed (M : msolver) (focus word : Z) : Prop :=
  Znth (lit_var_c focus) (mt_levels (ms_core M)) 0 = 0 ->
  forall owner co, In (owner,co) (msolver_db M) ->
    (lit_neg_c (co_watch0 co) = focus ->
     word = (if 3 <=? Zlength (co_lits co) then owner else tag_of_lit (co_watch1 co)) ->
     lit_true (mt_assigns (ms_core M)) (co_watch1 co) /\
     Znth (lit_var_c (co_watch1 co)) (mt_levels (ms_core M)) 0 = 0) /\
    (lit_neg_c (co_watch1 co) = focus ->
     word = (if 3 <=? Zlength (co_lits co) then owner else tag_of_lit (co_watch0 co)) ->
     lit_true (mt_assigns (ms_core M)) (co_watch0 co) /\
     Znth (lit_var_c (co_watch0 co)) (mt_levels (ms_core M)) 0 = 0).
Definition minisat_base_scan_completed (M : msolver) (focus : Z) (pending : list Z) : Prop :=
  forall word, ~ In word pending -> minisat_base_focus_word_completed M focus word.
Definition minisat_base_clause_completed_except (t : mtrail) (focus : Z)
    (co : clause_obj) : Prop :=
  (lit_neg_c (co_watch0 co) <> focus ->
   processed (mt_assigns t) (mt_trail t) (mt_qhead t) (lit_neg_c (co_watch0 co)) ->
   Znth (lit_var_c (co_watch0 co)) (mt_levels t) 0 = 0 ->
   lit_true (mt_assigns t) (co_watch1 co) /\
   Znth (lit_var_c (co_watch1 co)) (mt_levels t) 0 = 0) /\
  (lit_neg_c (co_watch1 co) <> focus ->
   processed (mt_assigns t) (mt_trail t) (mt_qhead t) (lit_neg_c (co_watch1 co)) ->
   Znth (lit_var_c (co_watch1 co)) (mt_levels t) 0 = 0 ->
   lit_true (mt_assigns t) (co_watch0 co) /\
   Znth (lit_var_c (co_watch0 co)) (mt_levels t) 0 = 0).
Definition minisat_resident_false_clause (M : msolver) : Prop :=
  exists owner co, In (owner, co) (msolver_db M) /\
    clause_false (assigns_pv (mt_assigns (ms_core M))) (denote_obj co).

Definition minisat_watch_conflict_ready (n : Z) (M : msolver) : Prop :=
  exists focus,
    level_of (msolver_view n M) (lit_var_c focus) =
      Some (Zlength (mt_lim (ms_core M))) /\
    minisat_base_watch_completed_except M focus.
Definition minisat_propagation_reuse_loop
    (n : Z) (entry M : msolver) (confl : Z) : Prop :=
  (minisat_base_watch_completed entry ->
    ((confl = 0 -> minisat_base_watch_completed M) /\
     (confl <> 0 -> minisat_watch_conflict_ready n M))) /\
  (minisat_resident_false_clause entry -> minisat_resident_false_clause M) /\
  (confl <> 0 -> minisat_resident_false_clause M).
Definition minisat_propagation_reuse_scan
    (entry M : msolver) (focus confl : Z) (pending : list Z) : Prop :=
  (minisat_base_watch_completed entry ->
    minisat_base_watch_completed_except M focus /\
    (confl = 0 -> minisat_base_scan_completed M focus pending)) /\
  (minisat_resident_false_clause entry -> minisat_resident_false_clause M) /\
  (confl <> 0 -> minisat_resident_false_clause M).
Definition minisat_propagation_reuse_live (entry M : msolver) : Prop :=
  (minisat_base_watch_completed entry -> minisat_base_watch_completed M) /\
  (minisat_resident_false_clause entry -> minisat_resident_false_clause M).
Definition solver_propagation_loop_inv
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (entry M : msolver)
    (confl : Z) : Prop :=
  propagation_caller_frame entry M /\
  ((confl = 0 /\ solver_propagation_inv n F A_arr K M) \/
   (confl <> 0 /\ exists focus C,
      propagation_cancel_ready n F A_arr K M focus /\
      propagation_conflict_cert n F M C /\ conflict_ptr_denotes M confl C)).

(** The pre-increment propagation invariant produces the rollback carrier.
    If it already has full heap coverage, a missing focus would force an
    earlier occurrence of the same variable, contradicting trail
    uniqueness.  The propagation-only exception arm directly supplies a
    non-empty decision-level stack. *)
Lemma propagation_heap_rollback_ready_scan_begin :
  forall n M p simpdb_props propagation_count,
    mtrail_wf n (ms_core M) ->
    propagation_heap_ready n M ->
    mt_qhead (ms_core M) < ms_qtail M ->
    ms_qtail M = Zlength (mt_trail (ms_core M)) ->
    p = Znth (mt_qhead (ms_core M)) (mt_trail (ms_core M)) 0 ->
    propagation_heap_rollback_ready
      (msolver_propagation_scan_begin M simpdb_props propagation_count) p.
Proof.
  intros n M p simpdb_props propagation_count Hwf Hready Hpending
         Hqtail Hp.
  unfold propagation_heap_rollback_ready.
  pose proof (mtw_qhead_range Hwf) as Hqrange.
  split.
  { rewrite msolver_propagation_scan_begin_qhead. lia. }
  split.
  { rewrite msolver_propagation_scan_begin_qhead.
    replace (mt_qhead (ms_core M) + 1 - 1)
      with (mt_qhead (ms_core M)) by lia.
    change (p = Znth (mt_qhead (ms_core M)) (mt_trail (ms_core M)) 0).
    exact Hp. }
  change (0 < Zlength (mt_lim (ms_core M)) \/
    Znth (lit_var_c p) (ms_orderpos M) (-1) <> -1).
  destruct Hready as [Hcovers|[Hlevels _]].
    + right. intro Hmissing.
      assert (Hidx :
        0 <= mt_qhead (ms_core M) < Zlength (mt_trail (ms_core M))) by lia.
      pose proof
        (Forall_Znth_elim _ _ _ 0 (mt_qhead (ms_core M))
          (mtw_trail_lits Hwf) Hidx) as Hlit.
      rewrite <- Hp in Hlit.
      pose proof (lit_var_c_in_range n p Hlit) as Hvar_range.
      destruct (Hcovers (lit_var_c p) Hvar_range Hmissing)
        as [_ [i [Hi Hvar]]].
      assert (i = mt_qhead (ms_core M)).
      { eapply (mtrail_wf_trail_var_injective n (ms_core M));
          [exact Hwf|lia|exact Hidx|].
        unfold trail_var. rewrite <- Hp. exact Hvar. }
      lia.
  + left. exact Hlevels.
Qed.

(** Successful propagation enqueues append behind the fixed scan cursor and
    leave its decision levels and order heap untouched, so the exact rollback
    focus and its root/non-root gate remain valid. *)
Lemma propagation_heap_rollback_ready_enqueue_success :
  forall n M p l reason_word reason_clause,
    mtrail_wf n (ms_core M) ->
    propagation_heap_rollback_ready M p ->
    propagation_heap_rollback_ready
      (msolver_propagation_enqueue_success M l reason_word reason_clause) p.
Proof.
  intros n M p l reason_word reason_clause Hwf Hready.
  unfold msolver_propagation_enqueue_success.
  destruct (Znth (lit_var_c l) (mt_assigns (ms_core M)) 0 =? 0)
    eqn:Hfresh; [|exact Hready].
  unfold propagation_heap_rollback_ready in Hready |- *.
  cbn [msolver_propagation_overlay msolver_propagation_update mt_enqueue mt_push].
  destruct Hready as [Hq [Hp Hgate]].
  change (0 < mt_qhead (ms_core M) /\
    p = Znth (mt_qhead (ms_core M) - 1)
      (mt_trail (ms_core M) ++ [l]) 0 /\
    (0 < Zlength (mt_lim (ms_core M)) \/
     Znth (lit_var_c p) (ms_orderpos M) (-1) <> -1)).
  split; [exact Hq|]. split; [|exact Hgate].
  rewrite app_Znth1; [exact Hp|].
  pose proof (mtw_qhead_range Hwf). lia.
Qed.

Definition propagation_binary_conflict_scan_ready
    (n : Z) (M : msolver) (p current : Z) (source : list Z)
    (simp_count prop_count : Z) : Prop :=
  tagged_word current /\
  heap_covers n (msolver_heap M) (mt_assigns (ms_core M))
    (mt_trail (ms_core M)) (mt_qhead (ms_core M)) /\
  current_reasonless_earliest n M /\
  level_of (msolver_view n M) (lit_var_c p) =
    Some (Zlength (mt_lim (ms_core M))) /\
  simp_count = ms_simpdb_props M /\
  prop_count = stats_propagations (ms_stats M) /\
  0 <= Zlength source.

Definition propagation_scan_keep_step
    (source retained moved rest memory : list Z) (ii jj current : Z)
    (retained' rest' garbage' memory' : list Z) : Prop :=
  rest = current :: rest' /\
  retained' = retained ++ [current] /\
  memory' = replace_Znth jj current memory /\
  propagation_watch_scan_physical
    source retained' moved rest' garbage' memory' (ii + 1) (jj + 1).

Definition propagation_scan_move_step
    (source retained moved rest memory : list Z) (ii jj current : Z)
    (moved' rest' garbage' : list Z) : Prop :=
  rest = current :: rest' /\
  moved' = moved ++ [current] /\
  propagation_watch_scan_physical
    source retained moved' rest' garbage' memory (ii + 1) jj.

Definition propagation_scan_conflict_step
    (source retained moved rest memory' garbage' : list Z)
    (retained' : list Z) : Prop :=
  retained' = retained ++ rest /\
  propagation_watch_scan_physical
    source retained' moved nil garbage' memory'
    (Zlength source) (Zlength retained').

Definition propagation_binary_keep_transition
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver)
    (p current : Z) (retained' rest' : list Z) (M' : msolver) : Prop :=
  M' = msolver_propagation_enqueue_success M
         (tag_lit current) (tag_of_lit p)
         [lit_denote (tag_lit current); literal_neg (lit_denote p)] /\
  solver_propagation_scan_semantics
    n F A_arr K M' p 0 retained' rest'.

Definition propagation_binary_conflict_transition
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver)
    (p current : Z) (retained' : list Z) (M' : msolver) : Prop :=
  M' = msolver_propagation_binary_conflict M (tag_lit current) p /\
  solver_propagation_scan_semantics
    n F A_arr K M' p (ms_binary M') retained' nil.

Definition propagation_real_satisfied_transition
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) (p : Z)
    (prob learnt : dbmap) (retained' rest' : list Z) (M' : msolver) : Prop :=
  M' = msolver_propagation_db_wmap_update
         M prob learnt (ms_wm M) /\
  solver_propagation_scan_semantics
    n F A_arr K M' p 0 retained' rest'.

Definition propagation_real_migrated_transition
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver) (p : Z)
    (prob learnt : dbmap) (wm : wmap)
    (retained moved' rest' : list Z) (M' : msolver) : Prop :=
  M' = msolver_propagation_db_wmap_update M prob learnt wm /\
  solver_propagation_scan_semantics
    n F A_arr K M' p 0 retained rest'.

Definition propagation_real_migrated_exit_carrier
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context)
    (M0 Mentry M M' : msolver) (p : Z)
    (prob learnt : dbmap)
    (wm : wmap)
    (candidate current : Z)
    (source retained moved rest memory : list Z) (ii jj : Z)
    (moved' rest' garbage' memory' : list Z)
    (simp_count prop_count : Z) : Prop :=
  M' = msolver_propagation_db_wmap_update
         M prob learnt
         (propagation_move_wmap
            p (lit_neg_c candidate) wm (retained ++ rest') current) /\
  propagation_real_migrated_transition
    n F A_arr K M p prob learnt
    (propagation_move_wmap
       p (lit_neg_c candidate) wm (retained ++ rest') current)
    retained moved' rest' M' /\
  propagation_scan_move_step
    source retained moved rest memory ii jj current moved' rest' garbage' /\
  solver_shape M' /\
  msolver_seed_shadow M' /\
  propagation_caller_frame M0 M' /\
  propagation_scan_frontier Mentry M' p /\
  solver_propagation_scan_semantics
    n F A_arr K M' p 0 retained rest' /\
  simp_count = ms_simpdb_props M' /\
  prop_count = stats_propagations (ms_stats M') /\
  memory' = memory /\
  propagation_watch_scan_physical
    source retained moved' rest' garbage' memory' (ii + 1) jj /\
  ms_wm M' =
    replace_Znth p (retained ++ rest')
      (replace_Znth (lit_neg_c candidate)
         (Znth (lit_neg_c candidate) wm nil ++ [current]) wm).

Definition propagation_unit_success_transition
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver)
    (p watch0 current : Z) (new_lits : list Z)
    (prob learnt : dbmap) (retained' rest' : list Z) (M' : msolver) : Prop :=
  let Mdb := msolver_propagation_db_wmap_update
               M prob learnt (ms_wm M) in
  M' = msolver_propagation_enqueue_success
         Mdb watch0 current (lits_denote new_lits) /\
  solver_propagation_scan_semantics
    n F A_arr K M' p 0 retained' rest'.

Definition propagation_unit_conflict_transition
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver)
    (p current : Z) (prob learnt : dbmap)
    (retained' : list Z) (M' : msolver) : Prop :=
  M' = msolver_propagation_db_wmap_update
         M prob learnt (ms_wm M) /\
  solver_propagation_scan_semantics
    n F A_arr K M' p current retained' nil.

(** The semantic work for a real-clause unit conflict is completed before
    the subsequent in-place watcher-suffix copy.  The copy then carries only
    this pure certificate and the physical source-vector progress; it does
    not have to rediscover that every literal of the normalized clause is
    false after the replacement scan has ended. *)
Definition propagation_unit_conflict_ready
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (M : msolver)
    (p current watch0 false_lit : Z)
    (old_lits retained rest : list Z)
    (prob learnt : dbmap) (M' : msolver) : Prop :=
  db_pair_lits_update
    (ms_prob M) (ms_learnt M) current old_lits
    (propagation_normalized_clause watch0 false_lit old_lits)
    prob learnt /\
  propagation_unit_conflict_transition
    n F A_arr K M p current prob learnt (retained ++ rest) M'.

Definition propagation_scan_live_finalize
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (entry M : msolver)
    (p inspect_delta : Z) (retained : list Z) (M' : msolver) : Prop :=
  M' = msolver_propagation_scan_finish M inspect_delta /\
  solver_propagation_scan_semantics n F A_arr K M p 0 retained nil /\
  solver_propagation_loop_inv n F A_arr K entry M' 0.

Definition propagation_scan_conflict_finalize
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context) (entry M : msolver)
    (p confl inspect_delta : Z) (retained : list Z) (M' : msolver) : Prop :=
  confl <> 0 /\
  M' = msolver_propagation_scan_finish M inspect_delta /\
  solver_propagation_scan_semantics n F A_arr K M p confl retained nil /\
  solver_propagation_loop_inv n F A_arr K entry M' confl.

Lemma propagation_binary_conflict_transition_intro :
  forall n F A_arr K M p current retained' M',
    M' = msolver_propagation_binary_conflict M (tag_lit current) p ->
    solver_propagation_scan_semantics
      n F A_arr K M' p (ms_binary M') retained' nil ->
    propagation_binary_conflict_transition
      n F A_arr K M p current retained' M'.
Proof. intros; split; assumption. Qed.

Definition propagation_scan_open
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context)
    (M0 Mentry M : msolver) (p confl : Z)
    (source kept moved rest garbage memory : list Z)
    (ii jj current : Z) (suffix : list Z) : Prop :=
  solver_shape M /\
  msolver_seed_shadow M /\
  propagation_caller_frame M0 M /\
  propagation_scan_frontier Mentry M p /\
  solver_propagation_scan_semantics n F A_arr K M p 0 kept rest /\
  propagation_watch_scan_physical source kept moved rest garbage memory ii jj /\
  rest = current :: suffix /\
  confl = 0.

(** Literal-array geometry once a concrete replacement candidate has been selected:
    [k] points at a real literal and [sig] is its sign token. *)
Definition propagation_scan_candidate_layout
    (current lits stop k offset false_lit p candidate sig : Z)
    (contents : list Z) : Prop :=
  clause_lits_pointer current lits /\
  3 <= Zlength contents /\
  false_lit = lit_neg_c p /\
  stop = lits + Zlength contents * sizeof(INT) /\
  k = lits + offset * sizeof(INT) /\
  2 <= offset < Zlength contents /\
  candidate = Znth (offset - 2) (sublist 2 (Zlength contents) contents) 0 /\
  sig = 2 * lit_sign_c candidate - 1.

Definition propagation_binary_conflict_exit
    (n : Z) (F : cnf) (A_arr : list literal)
    (K : solver_propagation_context)
    (M0 Mentry M M' : msolver) (p current confl : Z)
    (source kept moved rest memory garbage' kept' : list Z) : Prop :=
  solver_shape M' /\
  msolver_seed_shadow M' /\
  propagation_caller_frame M0 M' /\
  propagation_scan_frontier Mentry M' p /\
  propagation_binary_conflict_transition n F A_arr K M p current kept' M' /\
  propagation_scan_conflict_step source kept moved rest memory garbage' kept' /\
  solver_propagation_scan_semantics n F A_arr K M' p confl kept' nil /\
  propagation_watch_scan_physical
    source kept' moved nil garbage' memory
    (Zlength source) (Zlength kept') /\
  confl = ms_binary M'.

Definition propagation_scan_slot
    (M : msolver) (p : Z) (wm : wmap) (words : list Z) : Prop :=
  ms_wm M = replace_Znth p words wm /\
  0 <= p < Zlength wm.

(** Reattach assignment storage while leaving [qhead] explicit. *)
Definition solver_propagation_scan_arrays_noqh_at
    (s : Z) (M : msolver) (asg rsn lvl trl simp prop : Z) : Assertion :=
  CharArray.seg asg 0 (ms_size M) (mt_assigns (ms_core M)) **
  solver_char_tail asg (ms_size M) (ms_cap M) **
  solver_propagation_scan_core_at s M asg rsn lvl trl simp prop.

Definition valid_int_position (p : Z) : Prop :=
  0 <= p <= addr_max_unsigned /\
  p mod sizeof(INT) = 0.

Definition assumptions_array
    (n begin finish : Z) (A_arr : list literal) : Assertion :=
  EX raw : list Z,
    “ finish = begin + Zlength raw * sizeof(INT) /\
      A_arr = lits_denote raw /\
      Forall (lit_wf_c n) raw /\
      (raw = [] -> valid_int_position begin) ” &&
    IntArray.seg begin 0 (Zlength raw) raw.

Definition solver_normal_root (n : Z) (F : cnf) (M : msolver) : Prop :=
  msolver_inv n F [] [] M /\
  solver_at_root M /\
  ms_root_level M = 0 /\
  mt_qhead (ms_core M) = ms_qtail M /\
  ms_capacity_root_propagation_pending M = 0.

(** Root-state carrier with a saved cursor and a drained physical queue. *)
Definition solver_suspended_root (n : Z) (F : cnf) (M : msolver) : Prop :=
  ms_capacity_root_propagation_pending M = 1 /\
  0 <= ms_capacity_pending_qhead M < ms_qtail M /\
  mt_qhead (ms_core M) = ms_qtail M /\
  ms_root_level M = 0 /\
  Zlength (mt_lim (ms_core M)) = 0 /\
  msolver_inv n F [] [] (msolver_resume M) /\
  solver_at_root (msolver_resume M).

Definition solver_operational_root (n : Z) (F : cnf) (M : msolver) : Prop :=
  solver_normal_root n F M \/ solver_suspended_root n F M.

(* Growth does not read the stored assumption root. Its semantic view may
   therefore use the current logical root while memory still describes M.
   Choosing the physical root recovers the entire previous contract. *)
Definition solver_support_inv
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (logical_root : Z) (M : msolver) : Prop :=
  msolver_inv n F A_arr A_inst (msolver_set_root M logical_root).

Definition solver_base_state (n : Z) (F : cnf) (M : msolver) : Prop :=
  msolver_inv_assuming_strong n F nil nil M /\
  Zlength (mt_lim (ms_core M)) = 0 /\
  ms_capacity_root_propagation_pending M = 0.


(** An ordinary query may retain the preceding call's stored assumption root.
    Its live trail is at level zero; the assuming carrier ignores that stale
    field until solver_solve installs the next assumption root. *)
Definition solver_query_ready (n : Z) (F : cnf) (M : msolver) : Prop :=
  msolver_inv_assuming_strong n F [] [] M /\
  Zlength (mt_lim (ms_core M)) = 0 /\
  mt_qhead (ms_core M) = ms_qtail M /\
  ms_capacity_root_propagation_pending M = 0.


(** Ordinary nonempty queries require propagation closure before assume.
     Empty queries reach search directly. *)
Definition solver_assumptions_entry_ready (A : list literal) (M : msolver) : Prop :=
  ms_capacity_root_propagation_pending M = 1 \/ A = nil \/
  mt_qhead (ms_core M) = ms_qtail M.


Definition solver_query_watch_ready (M : msolver) : Prop :=
  (ms_capacity_root_propagation_pending M = 0 -> minisat_watch_completed M) /\
  (ms_capacity_root_propagation_pending M = 1 ->
    minisat_watch_completed (msolver_resume M)).


Definition solver_base_recovery (n : Z) (F : cnf) (M : msolver) : Prop :=
  solver_base_state n F M /\
  (minisat_watch_completed M \/ minisat_resident_false_clause M).


Definition solver_query_entry (n : Z) (F : cnf) (M : msolver) : Prop :=
  solver_query_ready n F M \/ solver_suspended_root n F M.

Definition solver_public_query_entry (n : Z) (F : cnf) (M : msolver) : Prop :=
  solver_query_entry n F M \/
  (solver_base_state n F M /\ minisat_resident_false_clause M).

Definition solver_query_reentry (n : Z) (F : cnf) (M : msolver) : Prop :=
  (solver_query_ready n F M /\ minisat_watch_completed M) \/
  (solver_base_state n F M /\ minisat_resident_false_clause M).

Definition solver_query_reuse_guard (M : msolver) : Prop :=
  solver_query_watch_ready M \/
  (ms_capacity_root_propagation_pending M = 0 /\
   minisat_resident_false_clause M).

Definition msolver_resume_pending (M : msolver) : msolver :=
  if Z.eqb (ms_capacity_root_propagation_pending M) 1
  then msolver_resume M else M.

Lemma solver_normal_root_query_ready__solve : forall n F M,
  solver_normal_root n F M -> solver_query_ready n F M.
Proof.
  intros n F M [Hinv [Hatroot [Hroot [Hdrain Hpending]]]].
  unfold solver_query_ready. split.
  - constructor.
    + apply msolver_inv_weak_assuming with (A_inst := (@nil literal));
        [exact (msi_weak Hinv) | exact Hatroot].
    + exact (msi_prop_level Hinv).
    + exact (msi_watch_frontier Hinv).
    + exact (msi_heap_covers Hinv).
    + exact (msi_reasonless_current Hinv).
  - split; [unfold solver_at_root in Hatroot; lia |].
    split; assumption.
Qed.

Lemma solver_operational_root_query_entry__solve : forall n F M,
  solver_operational_root n F M -> solver_query_entry n F M.
Proof.
  intros n F M [Hnormal|Hsuspended].
  - left. apply solver_normal_root_query_ready__solve. exact Hnormal.
  - right. exact Hsuspended.
Qed.

Lemma solver_query_assumptions__solve : forall n F M A,
  msolver_inv_assuming_strong n F [] [] M ->
  Forall (literal_wf n) A ->
  msolver_inv_assuming_strong n F A [] M.
Proof.
  intros n F M A [Hweak Hprop Hwatch Hheap Hreason] HAwf.
  constructor; try assumption.
  destruct Hweak. constructor; try assumption.
  intros x Hx. inversion Hx.
Qed.


Definition solver_simplify_reuse (entry current : msolver) : Prop :=
  (minisat_watch_completed entry \/ minisat_resident_false_clause entry) ->
  minisat_watch_completed current.

Definition solver_simplify_pre_at
    (s n : Z) (F : cnf) (A_arr : list literal)
    (M : msolver) (lvl : Z) (wl : Z) : Assertion :=
  “ msolver_inv_assuming_strong n F A_arr A_arr M /\
    Zlength (mt_lim (ms_core M)) = 0 /\
    ms_capacity_root_propagation_pending M = 0 /\
    msolver_seed_shadow M ” && solver_rep_levels_wl_at s M wl lvl.

Definition solver_selected_prob_db (type : Z) (M : msolver) : dbmap :=
  if Z.eqb type 0 then ms_prob M else [].

Definition solver_selected_learnt_db (type : Z) (M : msolver) : dbmap :=
  if Z.eqb type 0 then [] else ms_learnt M.

Lemma solver_selected_db_in : forall type M p co,
  (type = 0 \/ type = 1) ->
  In (p, co) (solver_selected_db type M) ->
  In (p, co) (msolver_db M).
Proof.
  intros type M p co Htype Hin.
  destruct Htype as [Htype | Htype]; subst type;
    unfold solver_selected_db in Hin; simpl in Hin;
    unfold msolver_db.
  - apply in_or_app. left. exact Hin.
  - apply in_or_app. right. exact Hin.
Qed.

(** The one concrete lock test is enough for the whole reason array.  If the
    same real clause pointer occurred at any reason index, [reason_head_ok]
    fixes that index to the selected clause's head variable; database
    well-formedness supplies its positive even pointer encoding. *)
Lemma solver_simplify_head_unlocked :
  forall n F A_arr A_inst M c co,
    msolver_inv_weak n F A_arr A_inst M ->
    In (c, co) (msolver_db M) ->
    Znth (lit_var_c (co_watch0 co)) (ms_reason_words M) 0 <> c ->
    clause_unlocked_words c (ms_reason_words M).
Proof.
  intros n F A_arr A_inst M c co Hinv Hin Hhead.
  unfold clause_unlocked_words. rewrite Forall_forall.
  intros r Hr Heq. subst r.
  destruct (In_Znth_index (ms_reason_words M) c Hr)
    as [v [Hv Hword]].
  assert (Hvrange : 0 <= v < ms_size M).
  { pose proof (msw_shape Hinv) as Hshape.
    rewrite (solver_shape_reasons_len M Hshape) in Hv.
    exact Hv. }
  assert (Heven : Z.even c = true).
  { eapply db_wf_even; [exact (msw_db_wf Hinv)|exact Hin]. }
  assert (Hpos : c <> 0).
  { pose proof (db_wf_ptr_pos n (msolver_db M) c co
      (msw_db_wf Hinv) Hin). lia. }
  pose proof (msw_reason_head Hinv v co Hvrange) as Hreason.
  rewrite Hword in Hreason.
  specialize (Hreason (even_not_tag c Heven) Hpos Hin).
  apply Hhead. rewrite Hreason. exact Hword.
Qed.

Definition stats_without_simplify_totals_rep
    (p : Z) (st : list Z) : Assertion :=
  “ Zlength st = 11 ” &&
  (&( p # "stats_t" ->ₛ "starts") # UInt64 |-> stats_starts st **
   &( p # "stats_t" ->ₛ "decisions") # UInt64 |-> stats_decisions st **
   &( p # "stats_t" ->ₛ "propagations") # UInt64 |-> stats_propagations st **
   &( p # "stats_t" ->ₛ "inspects") # UInt64 |-> stats_inspects st **
   &( p # "stats_t" ->ₛ "conflicts") # UInt64 |-> stats_conflicts st **
   &( p # "stats_t" ->ₛ "clauses") # UInt64 |-> stats_clauses st **
   &( p # "stats_t" ->ₛ "learnts") # UInt64 |-> stats_learnts st **
   &( p # "stats_t" ->ₛ "max_literals") # UInt64 |-> stats_max_literals st **
   &( p # "stats_t" ->ₛ "tot_literals") # UInt64 |-> stats_tot_literals st).

Definition solver_simplify_finish_frame_at
    (s : Z) (M : msolver) (lvl wl : Z) : Assertion :=
  solver_search_bundle_at s M lvl wl
    (solver_simplify_control_scalars_frame s M)
    (solver_fp_rep s M)
    (solver_vecs_rep s M)
    (stats_without_simplify_totals_rep
       &( s # "solver_t" ->ₛ "stats") (ms_stats M)).

Definition solver_simplify_db_compaction_inv
    (type : Z) (M : msolver) (words : list Z) (i j : Z) : Prop :=
  (type = 0 \/ type = 1) /\
  0 <= j /\ j <= i /\ i <= Zlength words /\
  map fst (solver_selected_db type M) =
    sublist 0 j words ++ sublist i (Zlength words) words.

Definition solver_simplify_outer_loop
    (s n : Z) (F : cnf) (A_arr : list literal)
    (reasons lvl type : Z) (entry : msolver)
    (wl : Z) : Assertion :=
  EX M : msolver,
    “ ms_cap M = ms_cap entry /\
      ms_root_level M = ms_root_level entry /\
      solver_simplify_reuse entry M /\ 0 <= type <= 2 /\ msolver_inv_assuming_strong n F A_arr A_arr M /\
      Zlength (mt_lim (ms_core M)) = 0 /\
      mt_qhead (ms_core M) = ms_qtail M /\
      ms_capacity_root_propagation_pending M = 0 /\
      msolver_seed_shadow M /\
      (ms_model entry = [] -> ms_model M = []) /\
      (msat_fp32_positive_finite (ms_cla_decay entry) ->
       msat_fp32_positive_finite (ms_cla_decay M)) ” &&
    solver_rep_reasons_levels_wl_at s M reasons lvl wl.


Definition solver_simplify_keep_words
    (words : list Z) (i j : Z) : list Z :=
  replace_Znth j (Znth i words 0) words.

Definition solver_simplify_delete_transition
    (n : Z) (F : cnf) (A_arr : list literal)
    (type : Z) (M : msolver) (c : Z)
    (wm : wmap) (stats : list Z) (M' : msolver) : Prop :=
  M' = msolver_remove_clause
         M (solver_selected_is_learnt type) c wm stats /\
  msolver_inv_assuming_strong n F A_arr A_arr M' /\
  Zlength (mt_lim (ms_core M')) = 0 /\
  mt_qhead (ms_core M') = ms_qtail M' /\
  ms_capacity_root_propagation_pending M' = 0 /\
  msolver_seed_shadow M'.

Definition solver_simplify_compaction_step
    (n : Z) (F : cnf) (A_arr : list literal)
    (type : Z) (M : msolver) (words : list Z) (i j : Z)
    (M' : msolver) (words' : list Z) (j' : Z) : Prop :=
  ((j' = j + 1 /\ M' = M /\
    words' = solver_simplify_keep_words words i j) \/
   (j' = j /\ words' = words /\ exists wm stats,
      solver_simplify_delete_transition
        n F A_arr type M (Znth i words 0) wm stats M')) /\
  msolver_inv_assuming_strong n F A_arr A_arr M' /\
  Zlength (mt_lim (ms_core M')) = 0 /\
  mt_qhead (ms_core M') = ms_qtail M' /\
  ms_capacity_root_propagation_pending M' = 0 /\
  msolver_seed_shadow M' /\ ms_model M' = ms_model M /\
  ms_cla_decay M' = ms_cla_decay M /\
  solver_simplify_db_compaction_inv type M' words' (i + 1) j'.

Definition solver_simplify_finish_transition
    (n : Z) (F : cnf) (A_arr : list literal)
    (M : msolver) (simpdb_props : Z) (M' : msolver) : Prop :=
  M' = msolver_simpdb_update M (mt_qhead (ms_core M)) simpdb_props /\
  msolver_inv_assuming_strong n F A_arr A_arr M' /\
  Zlength (mt_lim (ms_core M')) = 0 /\
  mt_qhead (ms_core M') = ms_qtail M' /\
  ms_capacity_root_propagation_pending M' = 0 /\
  msolver_seed_shadow M' /\ ms_model M' = ms_model M /\
  ms_cla_decay M' = ms_cla_decay M.

(* ==== Per-arm predicates for solver_simplify's Ensure ==== *)

Definition solver_simplify_post_sat_at
    (s n : Z) (F : cnf) (A_arr : list literal)
    (entry : msolver) (lvl wl : Z) : Assertion :=
  EX M : msolver,
    “ ms_cap M = ms_cap entry /\
      ms_root_level M = ms_root_level entry /\
      msolver_inv_assuming_strong n F A_arr A_arr M /\
      solver_simplify_reuse entry M /\
      Zlength (mt_lim (ms_core M)) = 0 /\
      mt_qhead (ms_core M) = ms_qtail M /\
      ms_capacity_root_propagation_pending M = 0 /\
      msolver_seed_shadow M /\
      (ms_model entry = [] -> ms_model M = []) /\
      (msat_fp32_positive_finite (ms_cla_decay entry) ->
       msat_fp32_positive_finite (ms_cla_decay M)) ” &&
    solver_rep_levels_wl_at s M wl lvl.

Definition solver_simplify_post_unsat_at
    (s n : Z) (F : cnf) (A_arr : list literal)
    (entry : msolver) (lvl wl : Z) : Assertion :=
  EX M : msolver,
    “ ms_cap M = ms_cap entry /\
      ms_root_level M = ms_root_level entry /\
      msolver_inv_assuming n F A_arr A_arr M /\
      Zlength (mt_lim (ms_core M)) = 0 /\
      (minisat_watch_completed entry ->
       solver_base_recovery n F M /\ msolver_seed_shadow M) /\
      cancel_bound_ready M 0 /\
      ms_capacity_root_propagation_pending M = 0 /\
      minisat_resident_false_clause M /\
      cnf_unsat n (cnf_with_units F A_arr) ” &&
    solver_rep_levels_wl_at s M wl lvl.

Definition solver_simplify_post_at
    (s n : Z) (F : cnf) (A_arr : list literal)
    (entry : msolver) (lvl ret : Z) (wl : Z) : Assertion :=
  ((“ ret = 1 ” && solver_simplify_post_sat_at s n F A_arr entry lvl wl) ||
   (“ ret = 0 /\ mt_qhead (ms_core entry) < ms_qtail entry ” &&
      solver_simplify_post_unsat_at s n F A_arr entry lvl wl)).

Definition solver_search_reuse (entry current : msolver) : Prop :=
  minisat_base_watch_completed entry -> minisat_base_watch_completed current.

Definition solver_search_conflict_reuse
    (n : Z) (F : cnf) (A_arr A_inst : list literal) (M : msolver) : Prop :=
  msolver_seed_shadow M /\
  ((exists focus,
      propagation_cancel_ready n F A_arr (PropagationStable A_inst) M focus /\
      minisat_watch_conflict_ready n M /\ minisat_resident_false_clause M) \/
   (solver_base_recovery n F M /\ minisat_resident_false_clause M)).

Definition solver_search_pre
    (s n : Z)
    (F : cnf) (A_arr A_inst : list literal) (M : msolver) (wl : Z) : Assertion :=
  “ msolver_inv n F A_arr A_inst M /\
    solver_at_root M /\
    ms_capacity_root_propagation_pending M = 0 /\
    msolver_seed_shadow M ” && solver_rep_wl s M wl.

Definition solver_search_loop
    (s learnt levels_ptr n : Z) (F : cnf) (A_arr A_inst : list literal)
    (wl : Z) (entry : msolver) : Assertion :=
  EX M : msolver, EX words : list Z,
    “ ms_cap M = ms_cap entry /\ solver_search_reuse entry M /\
      solver_propagation_inv
        n F A_arr (PropagationStable A_inst) M /\
      msolver_seed_shadow M /\ ms_model M = [] /\
      msat_fp32_positive_finite (ms_cla_decay M) ” &&
    (solver_rep_levels_wl_at s M wl levels_ptr ** Veci.rep learnt words).

Definition search_decision_stats_update (stats : list Z) : list Z :=
  stats_set_decisions (MiniSatTarget.lo64 (stats_decisions stats + 1)) stats.

(** The heap exception is the only semantic weakening between selecting a
    fresh decision variable and enqueueing it. *)
Definition solver_search_selection_state
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (next : Z) (M : msolver) : Prop :=
  msolver_inv_weak n F A_arr A_inst M /\
  prop_level (ms_core M) /\
  minisat_watch_frontier n (msolver_db M)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M))
    (mt_qhead (ms_core M)) /\
  current_reasonless_earliest n M /\
  ms_capacity_root_propagation_pending M = 0 /\
  mt_qhead (ms_core M) = ms_qtail M /\
  msolver_seed_shadow M /\ ms_model M = [] /\
  msat_fp32_positive_finite (ms_cla_decay M) /\
  2 * n <= INT_MAX /\ 0 <= next < n /\
  Znth next (mt_assigns (ms_core M)) 0 = 0 /\
  heap_covers_except n (msolver_heap M)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M))
    (mt_qhead (ms_core M)) next.

Definition solver_search_model_ready
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (M : msolver) : Prop :=
  msolver_inv n F A_arr A_inst M /\
  mt_qhead (ms_core M) = ms_qtail M /\ ms_order M = [] /\
  ms_capacity_root_propagation_pending M = 0 /\
  msolver_seed_shadow M /\ ms_model M = [].

Definition solver_search_select_transition
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (ret : Z) (orderpos order : list Z)
    (seed : fp64) (stats : list Z) (current : msolver) : Prop :=
  current = msolver_search_select entry orderpos order seed stats /\
  ms_cla_decay current = ms_cla_decay entry /\
  msat_fp32_positive_finite (ms_cla_decay current) /\
  stats = search_decision_stats_update (ms_stats entry) /\
  order_select_post n ret (ms_order entry) order orderpos
    (mt_assigns (ms_core entry)) (mt_trail (ms_core entry))
    (mt_qhead (ms_core entry)) /\
  ((ret = -1 /\
    solver_search_model_ready n F A_arr A_inst current) \/
   solver_search_selection_state n F A_arr A_inst ret current).

Definition solver_search_decision_transition
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (selected : msolver) (next : Z) (current : msolver) : Prop :=
  current = msolver_assume selected (lit_neg_c (next + next)) /\
  solver_propagation_inv
    n F A_arr (PropagationStable A_inst) current /\
  msolver_seed_shadow current /\ ms_model current = [] /\
  msat_fp32_positive_finite (ms_cla_decay current) /\
  ms_cla_decay current = ms_cla_decay selected.

Definition solver_search_backjump_ready
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry current : msolver) (words : list Z) : Prop :=
  msolver_inv n F A_arr A_inst current /\
  record_clause_cert n F current words /\
  record_watch1_positive current words /\
  mt_qhead (ms_core current) = ms_qtail current /\
  ms_capacity_root_propagation_pending current = 0 /\
  msolver_seed_shadow current /\
  ms_model current = ms_model entry /\
  msat_fp32_positive_finite (ms_cla_decay current) /\
  ms_cla_decay current = ms_cla_decay entry.

Definition model_copy_progress
    (n : Z) (M : msolver) (model : list Z) (i : Z) : Prop :=
  0 <= i <= n /\ Zlength model = i /\
  model = sublist 0 i (mt_assigns (ms_core M)).

Definition model_copy_finish
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (base : msolver) (model : list Z)
    (M : msolver) : Prop :=
  M = msolver_with_model base model /\
  msolver_inv n F A_arr A_inst M /\
  mt_qhead (ms_core M) = ms_qtail M /\ ms_order M = [] /\
  ms_capacity_root_propagation_pending M = 0 /\
  msolver_seed_shadow M /\ model_saved n F A_arr M.

Definition solver_search_result
    (s n : Z)
    (F : cnf) (A_arr A_inst : list literal) (ret : Z) (wl : Z) (entry : msolver) : Assertion :=
  ((“ ret = 1 ” &&
      (EX M : msolver,
        “ ms_cap M = ms_cap entry /\ solver_search_reuse entry M /\ msolver_inv n F A_arr A_inst M /\ solver_at_root M /\
          mt_qhead (ms_core M) = ms_qtail M /\
          ms_capacity_root_propagation_pending M = 0 /\
          msolver_seed_shadow M /\ model_saved n F A_arr M ” && solver_rep_wl s M wl)) ||
   (“ ret = -1 ” &&
      (EX M : msolver,
        “ ms_cap M = ms_cap entry /\
          (minisat_base_watch_completed entry ->
           solver_search_conflict_reuse n F A_arr A_inst M) /\ msolver_inv_weak n F A_arr A_inst M /\ solver_at_root M /\
          cancel_bound_ready M 0 /\
          ms_capacity_root_propagation_pending M = 0 /\
          cnf_unsat n (cnf_with_units F A_arr) ” && solver_rep_wl s M wl)) ||
   (“ ret = 0 ” &&
      (EX M : msolver,
        “ ms_cap M = ms_cap entry /\ solver_search_reuse entry M /\ msolver_inv n F A_arr A_inst M /\ solver_at_root M /\
          mt_qhead (ms_core M) = ms_qtail M /\
          ms_capacity_root_propagation_pending M = 0 /\
          msolver_seed_shadow M ” &&
        solver_rep_wl s M wl))).

Definition msolver_install_problem_clause
    (M : msolver) (c : Z) (words : list Z) : msolver :=
  msolver_install_clause M c words false.

(** ** Projections.  Every scalar and array the overlay copies. *)

Lemma ms_prob_install : forall M c words b,
  ms_prob (msolver_install_clause M c words b) =
  (if b then ms_prob M else ms_prob M ++ [(c, clause_obj_of words false)]).
Proof. reflexivity. Qed.

Lemma ms_learnt_install : forall M c words b,
  ms_learnt (msolver_install_clause M c words b) =
  (if b then ms_learnt M ++ [(c, clause_obj_of words true)] else ms_learnt M).
Proof. reflexivity. Qed.

Lemma ms_size_install : forall M c words b,
  ms_size (msolver_install_clause M c words b) = ms_size M.
Proof. reflexivity. Qed.

Lemma ms_core_install : forall M c words b,
  ms_core (msolver_install_clause M c words b) = ms_core M.
Proof. reflexivity. Qed.

Lemma ms_root_level_install : forall M c words b,
  ms_root_level (msolver_install_clause M c words b) = ms_root_level M.
Proof. reflexivity. Qed.

Lemma ms_reason_words_install : forall M c words b,
  ms_reason_words (msolver_install_clause M c words b) = ms_reason_words M.
Proof. reflexivity. Qed.

Lemma ms_reason_of_install : forall M c words b,
  ms_reason_of (msolver_install_clause M c words b) = ms_reason_of M.
Proof. reflexivity. Qed.

Lemma ms_binary_install : forall M c words b,
  ms_binary (msolver_install_clause M c words b) = ms_binary M.
Proof. reflexivity. Qed.

Lemma msolver_heap_install : forall M c words b,
  msolver_heap (msolver_install_clause M c words b) = msolver_heap M.
Proof. reflexivity. Qed.

Lemma ms_random_seed_install : forall M c words b,
  ms_random_seed (msolver_install_clause M c words b) = ms_random_seed M.
Proof. reflexivity. Qed.

Lemma ms_tags_install : forall M c words b,
  ms_tags (msolver_install_clause M c words b) = ms_tags M.
Proof. reflexivity. Qed.

Lemma ms_tagged_install : forall M c words b,
  ms_tagged (msolver_install_clause M c words b) = ms_tagged M.
Proof. reflexivity. Qed.

(** ** The database bridge.
    A learnt entry appends to the combined database; a problem entry is
    inserted between its two components. The latter requires permutation
    transport for database-indexed invariant fields. *)

Lemma msolver_db_install_learnt_eq : forall M c words,
  msolver_db (msolver_install_clause M c words true) =
  msolver_db M ++ [(c, clause_obj_of words true)].
Proof.
  intros M c words. unfold msolver_db.
  rewrite ms_prob_install, ms_learnt_install. simpl.
  rewrite app_assoc. reflexivity.
Qed.

Lemma msolver_db_install_problem_eq : forall M c words,
  msolver_db (msolver_install_problem_clause M c words) =
  ms_prob M ++ [(c, clause_obj_of words false)] ++ ms_learnt M.
Proof.
  intros M c words. unfold msolver_install_problem_clause, msolver_db.
  rewrite ms_prob_install, ms_learnt_install. simpl.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma msolver_db_install_perm : forall M c words b,
  Permutation (msolver_db (msolver_install_clause M c words b))
              (msolver_db M ++ [(c, clause_obj_of words b)]).
Proof.
  intros M c words b. destruct b.
  - rewrite msolver_db_install_learnt_eq. apply Permutation_refl.
  - change (msolver_install_clause M c words false)
      with (msolver_install_problem_clause M c words).
    rewrite msolver_db_install_problem_eq.
    unfold msolver_db. rewrite <- app_assoc.
    apply Permutation_app_head. apply Permutation_app_comm.
Qed.

(** ** [F]-monotonicity toolkit. *)

Lemma models_incl : forall rho (F F' : cnf),
  incl F F' -> models rho F' -> models rho F.
Proof.
  intros rho F F' Hincl HF'. unfold models in *.
  rewrite Forall_forall in *. intros c Hc. apply HF'. apply Hincl. exact Hc.
Qed.

Lemma entails_clause_incl : forall (F F' : cnf) c,
  incl F F' -> entails_clause F c -> entails_clause F' c.
Proof.
  intros F F' c Hincl H rho Hmod. apply H. eapply models_incl; eauto.
Qed.

Lemma entails_clause_app_r : forall (F G : cnf) c,
  entails_clause F c -> entails_clause (F ++ G) c.
Proof.
  intros F G c H. eapply entails_clause_incl; [| exact H].
  intros x Hx. apply in_or_app. left. exact Hx.
Qed.

Lemma cnf_with_units_app_incl : forall (F G : cnf) A,
  incl (cnf_with_units F A) (cnf_with_units (F ++ G) A).
Proof.
  intros F G A x Hx. unfold cnf_with_units in *.
  apply in_app_or in Hx. apply in_or_app.
  destruct Hx as [Hx | Hx].
  - left. apply in_or_app. left. exact Hx.
  - right. exact Hx.
Qed.

Lemma trail_implied_app_r : forall (F G : cnf) t,
  trail_implied F t -> trail_implied (F ++ G) t.
Proof.
  intros F G t H i l Hi Hl.
  eapply entails_clause_incl;
    [apply cnf_with_units_app_incl | apply H; assumption].
Qed.

Lemma reasons_entailed_app_r : forall (F G : cnf) a,
  reasons_entailed F a -> reasons_entailed (F ++ G) a.
Proof.
  intros F G a H x c Hc. apply entails_clause_app_r. eapply H. exact Hc.
Qed.

Lemma cnf_wf_app_one : forall n (F : cnf) (c : clause),
  cnf_wf n F -> Forall (literal_wf n) c -> cnf_wf n (F ++ [c]).
Proof.
  intros n F c [Hn HF] Hc. split; [exact Hn|].
  apply Forall_app. split; [exact HF | constructor; [exact Hc | constructor]].
Qed.

Lemma db_complete_prob_grow : forall (F : cnf) M M' (extra : dbmap),
  db_complete F M ->
  ms_prob M' = ms_prob M ++ extra ->
  ms_core M' = ms_core M ->
  db_complete F M'.
Proof.
  intros F M M' extra H Hprob Hcore c0 Hc0.
  destruct (H c0 Hc0) as [[c' [Hin Hperm]] | Hroot].
  - left. exists c'. split; [| exact Hperm].
    rewrite Hprob. unfold db_clauses. rewrite map_app.
    apply in_or_app. left. exact Hin.
  - right. rewrite Hcore. exact Hroot.
Qed.

(** ** Database-level preservation for a problem-clause installation. *)


Lemma db_clauses_install_problem : forall M c words,
  db_clauses (ms_prob (msolver_install_problem_clause M c words)) =
  db_clauses (ms_prob M) ++ [lits_denote words].
Proof.
  intros M c words. unfold msolver_install_problem_clause.
  rewrite ms_prob_install. unfold db_clauses. rewrite map_app. reflexivity.
Qed.

Lemma db_matches_cnf_install_problem : forall F M c words,
  db_matches_cnf F M ->
  db_matches_cnf (F ++ [lits_denote words])
                 (msolver_install_problem_clause M c words).
Proof.
  intros F M c words H. unfold db_matches_cnf in *.
  rewrite db_clauses_install_problem. apply Forall_app. split.
  - revert H. apply Forall_impl. intros a [c0 [Hin Hperm]].
    exists c0. split; [apply in_or_app; left; exact Hin | exact Hperm].
  - constructor; [| constructor].
    exists (lits_denote words). split.
    + apply in_or_app. right. left. reflexivity.
    + apply Permutation_refl.
Qed.

Lemma db_implied_install_problem : forall F M c words,
  db_implied F M ->
  db_implied (F ++ [lits_denote words])
             (msolver_install_problem_clause M c words).
Proof.
  intros F M c words H. unfold db_implied in *.
  unfold msolver_install_problem_clause. rewrite ms_learnt_install. simpl.
  revert H. apply Forall_impl. intros a Ha. apply entails_clause_app_r. exact Ha.
Qed.

Lemma db_complete_install_problem : forall F M c words,
  db_complete F M ->
  db_complete (F ++ [lits_denote words])
              (msolver_install_problem_clause M c words).
Proof.
  intros F M c words H c0 Hc0.
  rewrite db_clauses_install_problem.
  unfold msolver_install_problem_clause. rewrite ms_core_install.
  apply in_app_or in Hc0. destruct Hc0 as [Hc0 | Hc0].
  - destruct (H c0 Hc0) as [[c' [Hin Hperm]] | Hroot].
    + left. exists c'. split; [apply in_or_app; left; exact Hin | exact Hperm].
    + right. exact Hroot.
  - simpl in Hc0. destruct Hc0 as [<- | []].
    left. exists (lits_denote words). split.
    + apply in_or_app. right. left. reflexivity.
    + apply Permutation_refl.
Qed.

Lemma prob_db_install_problem : forall M c words,
  prob_db (ms_prob M) ->
  prob_db (ms_prob (msolver_install_problem_clause M c words)).
Proof.
  intros M c words H. unfold msolver_install_problem_clause.
  rewrite ms_prob_install. apply prob_db_app; [exact H|].
  constructor; [reflexivity | constructor].
Qed.

Lemma learnt_db_install_problem : forall M c words,
  learnt_db (ms_learnt M) ->
  learnt_db (ms_learnt (msolver_install_problem_clause M c words)).
Proof.
  intros M c words H. unfold msolver_install_problem_clause.
  rewrite ms_learnt_install. exact H.
Qed.

(** ** [db_wf] under a permutation and under a fresh append. *)

Lemma db_wf_perm : forall n d1 d2,
  Permutation d1 d2 -> db_wf n d1 -> db_wf n d2.
Proof.
  intros n d1 d2 Hperm [Hnodup [Hptr Hobj]]. split; [| split].
  - eapply Permutation_NoDup; [| exact Hnodup].
    apply Permutation_map. exact Hperm.
  - rewrite Forall_forall in *. intros x Hx. apply Hptr.
    eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hx].
  - rewrite Forall_forall in *. intros x Hx. apply Hobj.
    eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hx].
Qed.

Lemma db_wf_snoc : forall n db p co,
  db_wf n db -> obj_wf n co -> 0 < p -> Z.even p = true ->
  ~ In p (map fst db) ->
  db_wf n (db ++ [(p, co)]).
Proof.
  intros n db p co [Hnodup [Hptr Hobj]] Hco Hpos Heven Hfresh.
  split; [| split].
  - rewrite map_app. simpl. apply NoDup_snoc; assumption.
  - apply Forall_app. split; [exact Hptr |].
    constructor; [simpl; split; assumption | constructor].
  - apply Forall_app. split; [exact Hobj |].
    constructor; [simpl; exact Hco | constructor].
Qed.

(** ** [reasons_match] / [reason_head_ok] under database growth. *)

Lemma reason_word_ok_db_incl : forall t v d1 d2 w r,
  incl d1 d2 -> reason_word_ok t v d1 w r -> reason_word_ok t v d2 w r.
Proof.
  intros t v d1 d2 w r Hincl H. unfold reason_word_ok, db_lookup in *.
  destruct (w =? 0); [exact H |].
  destruct H as [Ha H]. split; [exact Ha |].
  destruct (is_tag w); [exact H |].
  destruct H as [co [Hin Hr]].
  exists co. split; [apply Hincl; exact Hin | exact Hr].
Qed.

Lemma reasons_match_db_incl : forall n t d1 d2 words r,
  incl d1 d2 -> reasons_match n t d1 words r -> reasons_match n t d2 words r.
Proof.
  intros n t d1 d2 words r Hincl H v Hv.
  eapply reason_word_ok_db_incl; [exact Hincl | apply H; exact Hv].
Qed.

Lemma reasons_match_install : forall n M c words b,
  reasons_match n (ms_core M) (msolver_db M)
                (ms_reason_words M) (ms_reason_of M) ->
  reasons_match n (ms_core (msolver_install_clause M c words b))
                (msolver_db (msolver_install_clause M c words b))
                (ms_reason_words (msolver_install_clause M c words b))
                (ms_reason_of (msolver_install_clause M c words b)).
Proof.
  intros n M c words b H.
  rewrite ms_core_install, ms_reason_words_install, ms_reason_of_install.
  eapply reasons_match_db_incl; [| exact H].
  intros x Hx.
  eapply Permutation_in;
    [apply Permutation_sym; apply msolver_db_install_perm |].
  apply in_or_app. left. exact Hx.
Qed.

(** A real (non-tag, non-null) reason word is resident, so a FRESH clause
    pointer is never any variable's reason word.  That is what lets
    [reason_head_ok] survive database growth. *)
Lemma reason_word_resident : forall t v db w r,
  reason_word_ok t v db w r -> w <> 0 -> is_tag w = false ->
  In w (map fst db).
Proof.
  intros t v db w r H Hnz Ht. unfold reason_word_ok, db_lookup in H.
  destruct (w =? 0) eqn:E; [apply Z.eqb_eq in E; congruence |].
  destruct H as [_ H]. rewrite Ht in H. destruct H as [co [Hin _]].
  change w with (fst (w, co)). apply in_map. exact Hin.
Qed.

Lemma reason_head_ok_install : forall M c words b,
  reason_head_ok M ->
  reasons_match (ms_size M) (ms_core M) (msolver_db M)
                (ms_reason_words M) (ms_reason_of M) ->
  ~ In c (map fst (msolver_db M)) ->
  reason_head_ok (msolver_install_clause M c words b).
Proof.
  intros M c words b Hhead Hmatch Hfresh.
  unfold reason_head_ok in *.
  rewrite ms_size_install, ms_reason_words_install.
  intros v co Hv Htag Hnz Hin.
  assert (Hres : In (Znth v (ms_reason_words M) 0) (map fst (msolver_db M))).
  { eapply reason_word_resident;
      [apply Hmatch; exact Hv | exact Hnz | exact Htag]. }
  assert (Hne : Znth v (ms_reason_words M) 0 <> c)
    by (intros Heq; rewrite Heq in Hres; contradiction).
  apply Hhead with (co := co); try assumption.
  eapply Permutation_in in Hin; [| apply msolver_db_install_perm].
  apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [exact Hin |].
  simpl in Hin. destruct Hin as [Heq | []]. inversion Heq. congruence.
Qed.

(** ** Watcher-map exactness at the installed clause.

    This is the one substantive spatial-side lemma, and it is shared by both
    installations: [clause_new_watch_map] pushes one word onto each of the
    two watch lists indexed by the negated watched literals, and
    [entry_watchers] of the new entry contributes exactly those two words. *)

Lemma leb3_ltb2 : forall n : Z, (3 <=? n) = (2 <? n).
Proof.
  intros n. destruct (3 <=? n) eqn:E1; destruct (2 <? n) eqn:E2;
    try reflexivity.
  - rewrite Z.leb_le in E1. rewrite Z.ltb_ge in E2. lia.
  - rewrite Z.leb_gt in E1. rewrite Z.ltb_lt in E2. lia.
Qed.

Lemma expected_watchers_perm : forall d1 d2 l,
  Permutation d1 d2 ->
  Permutation (expected_watchers d1 l) (expected_watchers d2 l).
Proof.
  intros d1 d2 l H. induction H.
  - apply Permutation_refl.
  - simpl. apply Permutation_app_head. exact IHPermutation.
  - simpl. rewrite !app_assoc. apply Permutation_app_tail.
    apply Permutation_app_comm.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma entry_watchers_new : forall c words b l,
  lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
  entry_watchers (c, clause_obj_of words b) l =
  (if lit_neg_c (Znth 0 words 0) =? l
   then [clause_watch_word c words (Znth 1 words 0)]
   else if lit_neg_c (Znth 1 words 0) =? l
        then [clause_watch_word c words (Znth 0 words 0)]
        else []).
Proof.
  intros c words b l Hne.
  unfold entry_watchers, clause_obj_of, co_watch0, co_watch1,
         clause_watch_word. simpl.
  rewrite leb3_ltb2.
  destruct (lit_neg_c (Znth 0 words 0) =? l) eqn:E0.
  - apply Z.eqb_eq in E0. subst l.
    assert (E1 : (lit_neg_c (Znth 1 words 0) =? lit_neg_c (Znth 0 words 0))
                 = false)
      by (apply Z.eqb_neq; congruence).
    rewrite E1. apply app_nil_r.
  - destruct (lit_neg_c (Znth 1 words 0) =? l); reflexivity.
Qed.

Lemma wmap_exact_install_app : forall n M c words b,
  wmap_exact n (msolver_db M) (ms_wm M) ->
  0 <= lit_neg_c (Znth 0 words 0) < 2 * n ->
  0 <= lit_neg_c (Znth 1 words 0) < 2 * n ->
  lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
  wmap_exact n (msolver_db M ++ [(c, clause_obj_of words b)])
               (clause_new_watch_map M c words).
Proof.
  intros n M c words b [Hlen Hperm] H0 H1 Hne.
  assert (Hlen' : Zlength (ms_wm M) = 2 * n) by exact Hlen.
  split.
  - rewrite clause_new_watch_map_Zlength. exact Hlen.
  - intros l Hl.
    rewrite expected_watchers_app.
    assert (Hone : expected_watchers [(c, clause_obj_of words b)] l
                   = entry_watchers (c, clause_obj_of words b) l)
      by (rewrite expected_watchers_cons; apply app_nil_r).
    rewrite Hone.
    rewrite entry_watchers_new by exact Hne.
    rewrite clause_new_watch_map_Znth by lia.
    destruct (lit_neg_c (Znth 0 words 0) =? l).
    + apply Permutation_app_tail. apply Hperm. exact Hl.
    + destruct (lit_neg_c (Znth 1 words 0) =? l).
      * apply Permutation_app_tail. apply Hperm. exact Hl.
      * rewrite app_nil_r. apply Hperm. exact Hl.
Qed.

Lemma wmap_exact_perm_db : forall n d1 d2 wm,
  Permutation d1 d2 -> wmap_exact n d1 wm -> wmap_exact n d2 wm.
Proof.
  intros n d1 d2 wm Hperm [Hlen H]. split; [exact Hlen |].
  intros l Hl. eapply Permutation_trans; [apply H; exact Hl |].
  apply expected_watchers_perm. exact Hperm.
Qed.

Lemma wmap_exact_install : forall n M c words b,
  wmap_exact n (msolver_db M) (ms_wm M) ->
  0 <= lit_neg_c (Znth 0 words 0) < 2 * n ->
  0 <= lit_neg_c (Znth 1 words 0) < 2 * n ->
  lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
  wmap_exact n (msolver_db (msolver_install_clause M c words b))
               (ms_wm (msolver_install_clause M c words b)).
Proof.
  intros n M c words b H H0 H1 Hne.
  rewrite ms_wm_install.
  eapply wmap_exact_perm_db;
    [apply Permutation_sym; apply msolver_db_install_perm |].
  apply wmap_exact_install_app; assumption.
Qed.

Lemma stable_view_installed_irrel : forall n M M',
  ms_core M' = ms_core M ->
  ms_reason_of M' = ms_reason_of M ->
  stable_view (msolver_view n M) ->
  stable_view (msolver_view n M').
Proof.
  intros n M M' Hcore Hro H.
  unfold stable_view, grounded_at, closed_levels, msolver_view, view_of in *.
  simpl in *. rewrite Hcore, Hro. exact H.
Qed.

Lemma reasons_var_injective_install : forall n M c words b,
  reasons_var_injective (msolver_view n M) ->
  reasons_var_injective (msolver_view n (msolver_install_clause M c words b)).
Proof.
  intros n M c words b H.
  unfold reasons_var_injective, msolver_view, view_of in *. simpl in *.
  exact H.
Qed.

Lemma binary_out_install : forall M c words b,
  ~ In (ms_binary M) (map fst (msolver_db M)) ->
  c <> ms_binary M ->
  ~ In (ms_binary (msolver_install_clause M c words b))
       (map fst (msolver_db (msolver_install_clause M c words b))).
Proof.
  intros M c words b Hout Hne. rewrite ms_binary_install. intros Hin.
  eapply Permutation_in in Hin;
    [| apply Permutation_map; apply msolver_db_install_perm].
  rewrite map_app in Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | Hin]; [contradiction |].
  simpl in Hin. destruct Hin as [Heq | []]. congruence.
Qed.

Lemma reasons_entailed_install : forall n F M c words b,
  reasons_entailed F (msolver_view n M) ->
  reasons_entailed F (msolver_view n (msolver_install_clause M c words b)).
Proof.
  intros n F M c words b H.
  unfold reasons_entailed, msolver_view, view_of in *. simpl in *. exact H.
Qed.

Lemma current_reasonless_earliest_install : forall n M c words b,
  current_reasonless_earliest n M ->
  current_reasonless_earliest n (msolver_install_clause M c words b).
Proof.
  intros n M c words b H.
  unfold current_reasonless_earliest, msolver_view, view_of in *.
  simpl in *. exact H.
Qed.

Lemma minisat_watch_occurrences_perm : forall d1 d2,
  Permutation d1 d2 ->
  Permutation (minisat_watch_occurrences d1) (minisat_watch_occurrences d2).
Proof.
  intros d1 d2 H. unfold minisat_watch_occurrences. apply Permutation_map. exact H.
Qed.

Lemma minisat_watch_frontier_install : forall n M c words b assigns trail qhead,
  minisat_watch_frontier n (msolver_db M) assigns trail qhead ->
  ~ (minisat_processed n assigns trail qhead
       (literal_neg (lit_denote (Znth 0 words 0))) /\
     minisat_processed n assigns trail qhead
       (literal_neg (lit_denote (Znth 1 words 0)))) ->
  minisat_watch_frontier n (msolver_db (msolver_install_clause M c words b))
                         assigns trail qhead.
Proof.
  intros n M c words b assigns trail qhead Hold Hnew.
  unfold minisat_watch_frontier, watch_frontier in *.
  eapply Forall_of_perm;
    [apply minisat_watch_occurrences_perm;
     apply Permutation_sym; apply msolver_db_install_perm |].
  unfold minisat_watch_occurrences. rewrite map_app.
  apply Forall_app. split; [exact Hold |].
  constructor; [| constructor]. simpl. exact Hnew.
Qed.

Lemma obj_wf_clause_obj_of : forall n words b,
  2 <= Zlength words -> Forall (lit_wf_c n) words ->
  NoDup (map lit_var_c words) ->
  obj_wf n (clause_obj_of words b).
Proof.
  intros n words b H1 H2 H3. unfold obj_wf, clause_obj_of. simpl.
  split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

(** An UNASSIGNED variable is never on the processed prefix, in either
    polarity.  This is what discharges [msolver_inv_install_problem]'s
    frontier hypothesis from [problem_clause_cert] alone: every literal the
    dedup pass of [solver_addclause] keeps has a zero [values] cell. *)
Lemma minisat_processed_unassigned : forall n assigns trail qhead w,
  Znth (lit_var_c w) assigns 0 = 0 ->
  ~ minisat_processed n assigns trail qhead (literal_neg (lit_denote w)).
Proof.
  intros n assigns trail qhead w Hunassigned [packed [_ [Hden [Htrue _]]]].
  unfold lit_true in Htrue.
  assert (Hvar : lit_var_c packed = lit_var_c w).
  { rewrite <- (lit_var_c_denote packed), <- (lit_var_c_denote w).
    rewrite Hden. apply literal_var_neg. }
  rewrite Hvar, Hunassigned in Htrue.
  unfold lit_sig in Htrue. destruct (Z.odd packed); discriminate.
Qed.


Theorem msolver_inv_weak_install_problem :
  forall n F A_arr A_inst M c words,
    msolver_inv_weak n F A_arr A_inst M ->
    clause_allocator_fresh M c ->
    2 <= Zlength words ->
    Forall (lit_wf_c n) words ->
    NoDup (map lit_var_c words) ->
    lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
    0 <= lit_neg_c (Znth 0 words 0) < 2 * n ->
    0 <= lit_neg_c (Znth 1 words 0) < 2 * n ->
    msolver_inv_weak n (F ++ [lits_denote words]) A_arr A_inst
      (msolver_install_problem_clause M c words).
Proof.
  intros n F A_arr A_inst M c words H Hfresh Hlen Hwf Hnodup Hne H0 H1.
  destruct Hfresh as [Hpos [Heven [Hbin Hnotin]]].
  unfold msolver_install_problem_clause in *.
  constructor.
  - rewrite ms_size_install. exact (msw_size H).
  - exact (msw_n_range H).
  - apply solver_shape_install. exact (msw_shape H).
  - apply cnf_wf_app_one; [exact (msw_F_wf H) | apply lits_denote_wf; exact Hwf].
  - exact (msw_A_wf H).
  - rewrite ms_core_install. exact (msw_trail_wf H).
  - rewrite ms_core_install. exact (msw_level_bound H).
  - rewrite ms_core_install, ms_root_level_install. exact (msw_root_range H).
  - rewrite ms_core_install, ms_root_level_install. exact (msw_assumptions H).
  - exact (msw_assump_incl H).
  - rewrite ms_core_install, ms_root_level_install. exact (msw_assump_sat H).
  - eapply stable_view_installed_irrel;
      [apply ms_core_install | apply ms_reason_of_install | exact (msw_stable H)].
  - apply reasons_entailed_install. apply reasons_entailed_app_r.
    exact (msw_reasons_ent H).
  - apply reasons_var_injective_install. exact (msw_reasons_inj H).
  - rewrite ms_core_install. apply trail_implied_app_r. exact (msw_trail_impl H).
  - eapply db_wf_perm; [apply Permutation_sym; apply msolver_db_install_perm |].
    apply db_wf_snoc; try assumption.
    + exact (msw_db_wf H).
    + apply obj_wf_clause_obj_of; assumption.
  - apply db_matches_cnf_install_problem. exact (msw_db_matches H).
  - apply db_implied_install_problem. exact (msw_db_implied H).
  - apply db_complete_install_problem. exact (msw_db_complete H).
  - apply learnt_db_install_problem. exact (msw_learnt_db H).
  - apply prob_db_install_problem. exact (msw_prob_db H).
  - apply binary_out_install; [exact (msw_binary_out H) | exact Hbin].
  - apply reasons_match_install. exact (msw_reasons_mem H).
  - apply reason_head_ok_install;
      [exact (msw_reason_head H) | rewrite <- (msw_size H); exact (msw_reasons_mem H)
       | exact Hnotin].
  - unfold binary_reason_same_level.
    rewrite ms_size_install, ms_reason_words_install, ms_core_install.
    exact (msw_reason_bin H).
  - apply wmap_exact_install;
      [exact (msw_wmap_exact H) | exact H0 | exact H1 | exact Hne].
  - unfold solver_tags_clear. rewrite ms_tags_install, ms_tagged_install.
    exact (msw_tags_clear H).
  - rewrite msolver_heap_install. exact (msw_heap_wf H).
  - exact (msw_cla_inc_nonnegative H).
  - unfold msolver_seed_ok. rewrite ms_random_seed_install. exact (msw_seed H).
Qed.

(** *** ...and of the strong bundle.

    The only extra content is the watcher frontier for the new object; the
    other three strong fields project the trail and the heap, both untouched. *)
Theorem msolver_inv_install_problem :
  forall n F A_arr A_inst M c words,
    msolver_inv n F A_arr A_inst M ->
    clause_allocator_fresh M c ->
    2 <= Zlength words ->
    Forall (lit_wf_c n) words ->
    NoDup (map lit_var_c words) ->
    lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
    0 <= lit_neg_c (Znth 0 words 0) < 2 * n ->
    0 <= lit_neg_c (Znth 1 words 0) < 2 * n ->
    ~ (minisat_processed n (mt_assigns (ms_core M)) (mt_trail (ms_core M))
         (mt_qhead (ms_core M))
         (literal_neg (lit_denote (Znth 0 words 0))) /\
       minisat_processed n (mt_assigns (ms_core M)) (mt_trail (ms_core M))
         (mt_qhead (ms_core M))
         (literal_neg (lit_denote (Znth 1 words 0)))) ->
    msolver_inv n (F ++ [lits_denote words]) A_arr A_inst
      (msolver_install_problem_clause M c words).
Proof.
  intros n F A_arr A_inst M c words H Hfresh Hlen Hwf Hnodup Hne H0 H1 Hfront.
  unfold msolver_install_problem_clause in *.
  constructor.
  - apply msolver_inv_weak_install_problem; try assumption. exact (msi_weak H).
  - rewrite ms_core_install. exact (msi_prop_level H).
  - rewrite ms_core_install.
    apply minisat_watch_frontier_install; [exact (msi_watch_frontier H) | exact Hfront].
  - rewrite ms_core_install, msolver_heap_install. exact (msi_heap_covers H).
  - apply current_reasonless_earliest_install. exact (msi_reasonless_current H).
Qed.

Lemma db_clauses_install_learnt : forall M c words,
  db_clauses (ms_learnt (msolver_install_clause M c words true)) =
  db_clauses (ms_learnt M) ++ [lits_denote words].
Proof.
  intros M c words. rewrite ms_learnt_install.
  unfold db_clauses. rewrite map_app. reflexivity.
Qed.

Lemma db_matches_cnf_install_learnt : forall F M c words,
  db_matches_cnf F M ->
  db_matches_cnf F (msolver_install_clause M c words true).
Proof.
  intros F M c words H. unfold db_matches_cnf in *.
  rewrite ms_prob_install. exact H.
Qed.

Lemma db_implied_install_learnt : forall F M c words,
  db_implied F M ->
  entails_clause F (lits_denote words) ->
  db_implied F (msolver_install_clause M c words true).
Proof.
  intros F M c words H Hent. unfold db_implied in *.
  rewrite db_clauses_install_learnt. apply Forall_app. split.
  - exact H.
  - constructor; [exact Hent | constructor].
Qed.

Lemma db_complete_install_learnt : forall F M c words,
  db_complete F M ->
  db_complete F (msolver_install_clause M c words true).
Proof.
  intros F M c words H. eapply db_complete_prob_grow with (extra := nil).
  - exact H.
  - rewrite ms_prob_install. rewrite app_nil_r. reflexivity.
  - apply ms_core_install.
Qed.

Lemma learnt_db_install_learnt : forall M c words,
  learnt_db (ms_learnt M) ->
  learnt_db (ms_learnt (msolver_install_clause M c words true)).
Proof.
  intros M c words H. rewrite ms_learnt_install.
  unfold learnt_db in *. apply Forall_app. split;
    [exact H | constructor; [reflexivity | constructor]].
Qed.

Lemma prob_db_install_learnt : forall M c words,
  prob_db (ms_prob M) ->
  prob_db (ms_prob (msolver_install_clause M c words true)).
Proof. intros M c words H. rewrite ms_prob_install. exact H. Qed.

Theorem msolver_inv_weak_install_learnt :
  forall n F A_arr A_inst M c words,
    msolver_inv_weak n F A_arr A_inst M ->
    clause_allocator_fresh M c ->
    2 <= Zlength words ->
    Forall (lit_wf_c n) words ->
    NoDup (map lit_var_c words) ->
    entails_clause F (lits_denote words) ->
    lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
    0 <= lit_neg_c (Znth 0 words 0) < 2 * n ->
    0 <= lit_neg_c (Znth 1 words 0) < 2 * n ->
    msolver_inv_weak n F A_arr A_inst (msolver_install_clause M c words true).
Proof.
  intros n F A_arr A_inst M c words H Hfresh Hlen Hwf Hnodup Hent Hne H0 H1.
  destruct Hfresh as [Hpos [Heven [Hbin Hnotin]]].
  constructor.
  - rewrite ms_size_install. exact (msw_size H).
  - exact (msw_n_range H).
  - apply solver_shape_install. exact (msw_shape H).
  - exact (msw_F_wf H).
  - exact (msw_A_wf H).
  - rewrite ms_core_install. exact (msw_trail_wf H).
  - rewrite ms_core_install. exact (msw_level_bound H).
  - rewrite ms_core_install, ms_root_level_install. exact (msw_root_range H).
  - rewrite ms_core_install, ms_root_level_install. exact (msw_assumptions H).
  - exact (msw_assump_incl H).
  - rewrite ms_core_install, ms_root_level_install. exact (msw_assump_sat H).
  - eapply stable_view_installed_irrel;
      [apply ms_core_install | apply ms_reason_of_install | exact (msw_stable H)].
  - apply reasons_entailed_install. exact (msw_reasons_ent H).
  - apply reasons_var_injective_install. exact (msw_reasons_inj H).
  - rewrite ms_core_install. exact (msw_trail_impl H).
  - eapply db_wf_perm; [apply Permutation_sym; apply msolver_db_install_perm |].
    apply db_wf_snoc; try assumption.
    + exact (msw_db_wf H).
    + apply obj_wf_clause_obj_of; assumption.
  - apply db_matches_cnf_install_learnt. exact (msw_db_matches H).
  - apply db_implied_install_learnt; [exact (msw_db_implied H) | exact Hent].
  - apply db_complete_install_learnt. exact (msw_db_complete H).
  - apply learnt_db_install_learnt. exact (msw_learnt_db H).
  - apply prob_db_install_learnt. exact (msw_prob_db H).
  - apply binary_out_install; [exact (msw_binary_out H) | exact Hbin].
  - apply reasons_match_install. exact (msw_reasons_mem H).
  - apply reason_head_ok_install;
      [exact (msw_reason_head H) | rewrite <- (msw_size H); exact (msw_reasons_mem H)
       | exact Hnotin].
  - unfold binary_reason_same_level.
    rewrite ms_size_install, ms_reason_words_install, ms_core_install.
    exact (msw_reason_bin H).
  - apply wmap_exact_install;
      [exact (msw_wmap_exact H) | exact H0 | exact H1 | exact Hne].
  - unfold solver_tags_clear. rewrite ms_tags_install, ms_tagged_install.
    exact (msw_tags_clear H).
  - rewrite msolver_heap_install. exact (msw_heap_wf H).
  - exact (msw_cla_inc_nonnegative H).
  - unfold msolver_seed_ok. rewrite ms_random_seed_install. exact (msw_seed H).
Qed.

(** The learned clause's own frontier obligation is discharged by exactly the
    same route as the problem clause's: [record_clause_cert] says the HEAD
    literal is unassigned, and one unassigned watch is enough. *)
Theorem msolver_inv_install_learnt :
  forall n F A_arr A_inst M c words,
    msolver_inv n F A_arr A_inst M ->
    clause_allocator_fresh M c ->
    2 <= Zlength words ->
    Forall (lit_wf_c n) words ->
    NoDup (map lit_var_c words) ->
    entails_clause F (lits_denote words) ->
    Znth (lit_var_c (Znth 0 words 0)) (mt_assigns (ms_core M)) 0 = 0 ->
    lit_neg_c (Znth 0 words 0) <> lit_neg_c (Znth 1 words 0) ->
    0 <= lit_neg_c (Znth 0 words 0) < 2 * n ->
    0 <= lit_neg_c (Znth 1 words 0) < 2 * n ->
    msolver_inv n F A_arr A_inst (msolver_install_clause M c words true).
Proof.
  intros n F A_arr A_inst M c words H Hfresh Hlen Hwf Hnodup Hent Hhead Hne H0 H1.
  constructor.
  - apply msolver_inv_weak_install_learnt; try assumption. exact (msi_weak H).
  - rewrite ms_core_install. exact (msi_prop_level H).
  - rewrite ms_core_install.
    apply minisat_watch_frontier_install; [exact (msi_watch_frontier H) |].
    intros [Hp0 _]. revert Hp0. apply minisat_processed_unassigned. exact Hhead.
  - rewrite ms_core_install, msolver_heap_install. exact (msi_heap_covers H).
  - apply current_reasonless_earliest_install. exact (msi_reasonless_current H).
Qed.

Definition record_allocated
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (words : list Z) (c : Z) (current : msolver) : Prop :=
  ((Zlength words = 1 /\ c = 0 /\ current = entry) \/
   (2 <= Zlength words /\ c <> 0 /\
    clause_new_success_transition
      n F A_arr A_inst entry words c current)) /\
  record_clause_cert n F current words /\
  msolver_inv n F A_arr A_inst current /\
  mt_qhead (ms_core current) = ms_qtail current /\
  ms_capacity_root_propagation_pending current = 0 /\
  msolver_seed_shadow current /\
  ms_model current = ms_model entry.

Definition record_reason_opt (words : list Z) (c : Z) : option clause :=
  if Z.eq_dec c 0 then None else Some (lits_denote words).

Definition msolver_record_enqueue
    (M : msolver) (words : list Z) (c : Z) : msolver :=
  msolver_enqueue_fresh M (Znth 0 words 0) c
    (record_reason_opt words c).

Definition minisat_record_reuse (entry : msolver) (words : list Z) (current : msolver) : Prop :=
  (minisat_base_watch_completed entry /\ record_watch1_positive entry words) ->
  minisat_base_watch_completed current.

Definition record_enqueue_success
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry current : msolver) (words : list Z) (c : Z)
    (M' : msolver) : Prop :=
  M' = msolver_record_enqueue current words c /\
  msolver_inv n F A_arr A_inst M' /\
  ms_capacity_root_propagation_pending M' = 0 /\
  msolver_seed_shadow M' /\
  ms_model M' = ms_model entry /\
  ms_cla_decay M' = ms_cla_decay entry /\
  ms_cap M' = ms_cap entry /\
  minisat_record_reuse entry words M'.

Definition record_stats_update (words stats : list Z) : list Z :=
  stats_set_learnts_literals (MiniSatTarget.lo64 (stats_learnts_literals stats + Zlength words)) (stats_set_learnts
  (MiniSatTarget.lo64 (stats_learnts stats + 1)) stats).

Definition msolver_record_finish
    (M : msolver) (words : list Z) (c : Z) (cla_inc : fp32) : msolver :=
  if Z.eq_dec c 0 then M
  else msolver_with_cla_inc_stats M cla_inc
         (record_stats_update words (ms_stats M)).

Definition record_finish_success
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry enqueued : msolver) (words : list Z) (c : Z)
    (cla_inc : fp32) (M' : msolver) : Prop :=
  M' = msolver_record_finish enqueued words c cla_inc /\
  msolver_inv n F A_arr A_inst M' /\
  ms_capacity_root_propagation_pending M' = 0 /\
  msolver_seed_shadow M' /\
  ms_model M' = ms_model entry /\
  ms_cla_decay M' = ms_cla_decay entry /\
  ms_cap M' = ms_cap entry /\
        minisat_record_reuse entry words M'.

Definition solver_record_pre_at
    (s learnt lvl n : Z) (F : cnf) (A_arr A_inst : list literal)
    (M : msolver) (words : list Z) (wl : Z) : Assertion :=
  “ record_clause_cert n F M words /\
    msolver_inv n F A_arr A_inst M /\
    mt_qhead (ms_core M) = ms_qtail M /\
    ms_capacity_root_propagation_pending M = 0 /\
    msolver_seed_shadow M ” &&
  (solver_rep_levels_wl_at s M wl lvl ** Veci.rep learnt words).

Definition solver_record_post_at
    (s learnt lvl n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (words : list Z) (ret : Z) (wl : Z) : Assertion :=
  (“ ret = 1 ” &&
    (EX M' : msolver,
      “ msolver_inv n F A_arr A_inst M' /\
        ms_capacity_root_propagation_pending M' = 0 /\
        msolver_seed_shadow M' /\
        ms_model M' = ms_model entry /\
        ms_cla_decay M' = ms_cla_decay entry /\
        ms_cap M' = ms_cap entry /\
        minisat_record_reuse entry words M' ” &&
      (solver_rep_levels_wl_at s M' wl lvl **
       Veci.rep learnt words))).

Definition solver_reducedb_loop_state
    (n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry cur : msolver) (words : list Z) (i j : Z) (extra_lim : fp64) : Prop :=
  msolver_inv n F A_arr A_inst cur /\
  mt_qhead (ms_core cur) = ms_qtail cur /\
  ms_capacity_root_propagation_pending cur = 0 /\ msolver_seed_shadow cur /\
  ms_model cur = ms_model entry /\ ms_cap cur = ms_cap entry /\
  (minisat_base_watch_completed entry -> minisat_base_watch_completed cur) /\
  msat_fp32_same (ms_cla_decay cur) (ms_cla_decay entry) /\
  db_compaction_inv cur words i j /\ msat_fp64_count_limit (Zlength words) extra_lim.

Definition solver_reducedb_pre_at
    (s lvl n : Z) (F : cnf) (A_arr A_inst : list literal)
    (M : msolver) (wl : Z) : Assertion :=
  “ msolver_inv n F A_arr A_inst M /\
    mt_qhead (ms_core M) = ms_qtail M /\
    ms_capacity_root_propagation_pending M = 0 /\
    msolver_seed_shadow M ” && solver_rep_levels_wl_at s M wl lvl.

Definition solver_reducedb_post_at
    (s lvl n : Z) (F : cnf) (A_arr A_inst : list literal)
    (entry : msolver) (wl : Z) : Assertion :=
  EX M' : msolver,
    “ msolver_inv n F A_arr A_inst M' /\
      mt_qhead (ms_core M') = ms_qtail M' /\
      ms_capacity_root_propagation_pending M' = 0 /\
      msolver_seed_shadow M' /\ ms_model M' = ms_model entry /\
      ms_cla_decay M' = ms_cla_decay entry /\
        ms_cap M' = ms_cap entry /\
      (minisat_base_watch_completed entry ->
       minisat_base_watch_completed M') ” &&
    solver_rep_levels_wl_at s M' wl lvl.

(** Cancellation exposes a physical boundary. Callers transport their
     semantic certificates across its state projection. *)
Definition solver_cancel_pre (s level : Z) (M : msolver) (wl : Z) : Assertion :=
  “ solver_shape M /\ mtrail_wf (ms_size M) (ms_core M) /\
    cancel_bound_ready M level /\
    heap_wf (ms_size M) (msolver_heap M) /\
    0 <= level <= Zlength (mt_lim (ms_core M)) ” &&
  solver_cancel_owned s M wl.

Definition solver_cancel_post (s level : Z) (M : msolver) (wl : Z) : Assertion :=
  ((“ Zlength (mt_lim (ms_core M)) <= level ” && solver_cancel_owned s M wl) ||
   (EX orderpos order : list Z,
      “ 0 <= level < Zlength (mt_lim (ms_core M)) /\
        heap_wf (ms_size M) (heap_of_lists order orderpos) /\
        incl (ms_order M) order /\
        cancel_reinserted (heap_of_lists order orderpos)
          (mt_trail (ms_core M))
          (Znth level (mt_lim (ms_core M)) 0)
          (mt_qhead (ms_core M)) ” &&
      solver_cancel_owned s
        (msolver_cancel_project M level orderpos order
                                 (ms_root_level M)) wl)).

(** Minimal semantic input for rebuilding a strong level-zero state.  Queue
    range follows from the weak invariant's trail/shape fields; the only
    strong facts not already there are the surviving watch frontier and heap
    coverage. *)
Definition solver_root_rebuild_ready
    (n : Z) (F : cnf) (M : msolver) : Prop :=
  msolver_inv_weak n F [] [] (msolver_set_root M 0) /\
  Zlength (mt_lim (ms_core M)) = 0 /\
  minisat_watch_frontier n (msolver_db (msolver_set_root M 0))
    (mt_assigns (ms_core M)) (mt_trail (ms_core M))
    (mt_qhead (ms_core M)) /\
  heap_covers n (msolver_heap M)
    (mt_assigns (ms_core M)) (mt_trail (ms_core M))
    (mt_qhead (ms_core M)).

Definition assumption_prefix (raw : list Z) (k : Z) : list literal :=
  lits_denote (sublist 0 k raw).

Definition assumption_true_advance
    (n : Z) (F : cnf) (A_arr : list literal)
    (raw : list Z) (k : Z) (M : msolver) : Prop :=
  msolver_inv_assuming_strong n F A_arr (assumption_prefix raw (k + 1)) M.

Definition assumption_fresh_ready
    (n : Z) (raw : list Z) (k : Z) (M : msolver) : Prop :=
  let current := Znth k raw 0 in
  ms_size M = n /\ mt_qhead (ms_core M) = ms_qtail M /\
  Znth (lit_var_c current) (mt_assigns (ms_core M)) 0 = 0 /\
  Zlength (mt_lim (ms_core M)) < n /\
  enqueue_input n current (ms_qtail M)
    (mt_assigns (ms_core M)) (mt_levels (ms_core M))
    (ms_reason_words M) (mt_trail (ms_core M)).

Definition assumption_fresh_transition
    (n : Z) (F : cnf) (A_arr : list literal)
    (raw : list Z) (k : Z) (entry next : msolver) : Prop :=
  let current := Znth k raw 0 in
  next = msolver_assume entry current /\
  solver_propagation_inv
    n F A_arr (PropagationAssuming (assumption_prefix raw (k + 1))) next /\
  msolver_seed_shadow next.

Definition assumption_propagation_success
    (n : Z) (F : cnf) (A_arr : list literal)
    (raw : list Z) (k : Z) (M : msolver) : Prop :=
  msolver_inv_assuming_strong n F A_arr (assumption_prefix raw k) M /\
  mt_qhead (ms_core M) = ms_qtail M /\
  ms_capacity_root_propagation_pending M = 0 /\
  msolver_seed_shadow M.

Definition assumption_root_install
    (n : Z) (F : cnf) (A_arr : list literal)
    (entry root_state : msolver) (A_inst : list literal) : Prop :=
  A_inst = decisions_upto
    (ms_core entry) (Zlength (mt_lim (ms_core entry))) /\
  root_state = msolver_set_root
    entry (Zlength (mt_lim (ms_core entry))) /\
  msolver_inv n F A_arr A_inst root_state /\
  solver_at_root root_state /\
  ms_capacity_root_propagation_pending root_state = 0 /\
  msolver_seed_shadow root_state.

Definition solver_sat_cancel_ready
    (n : Z) (F : cnf) (A_arr : list literal) (M : msolver) : Prop :=
  exists A_inst : list literal,
    msolver_inv n F A_arr A_inst M /\
    mt_qhead (ms_core M) = ms_qtail M /\
    ms_capacity_root_propagation_pending M = 0 /\ msolver_seed_shadow M.

Definition solver_query_reuse (entry current : msolver) : Prop :=
  solver_query_reuse_guard entry -> minisat_base_watch_completed current.

Definition solver_terminal_reuse
    (n : Z) (F : cnf) (A : list literal)
    (entry current : msolver) (status : Z) : Prop :=
  solver_query_reuse_guard entry ->
  ((status = 1 -> minisat_base_watch_completed current) /\
   (status = -1 -> exists A_inst,
      solver_search_conflict_reuse n F A A_inst current)).

(** Before the first search, an empty-assumption query may have an undrained
    root queue.  This initial status-zero arm requires precisely search's
    input invariant; completed calls retain the full search-result contract. *)
Definition solver_restart_loop
    (s begin finish n : Z) (F : cnf) (A_arr : list literal) (status : Z)
    (wl : Z) (public_entry : msolver) : Assertion :=
  assumptions_array n begin finish A_arr **
  (EX search_entry : msolver, EX A_inst : list literal,
     “ ms_cap search_entry = ms_cap public_entry /\
       (solver_query_reuse_guard public_entry ->
        minisat_base_watch_completed search_entry) ” &&
     (solver_search_result s n F A_arr A_inst status wl search_entry ||
      (“ status = 0 ” &&
       solver_search_pre s n F A_arr A_inst search_entry wl))).

Definition solver_sat_arm_at (s n : Z) (F : cnf) (A : list literal)
    (entry M : msolver) (wl : Z) : Assertion :=
  “ ms_size M = n /\ model_saved n F A M /\
    solver_query_ready n F M /\ msolver_seed_shadow M /\
    ms_cap M = ms_cap entry /\
    (solver_query_reuse_guard entry -> minisat_watch_completed M) ” &&
  solver_rep_wl s M wl.


Definition solver_unsat_arm_at (s n : Z) (F : cnf) (A : list literal)
    (entry M : msolver) (wl : Z) : Assertion :=
  “ ms_size M = n /\ cnf_unsat n (cnf_with_units F A) /\
    ms_cap M = ms_cap entry /\
    (solver_query_reuse_guard entry ->
      solver_base_recovery n F M /\ solver_query_reentry n F M /\ msolver_seed_shadow M) ” &&
  solver_rep_wl s M wl.


Lemma msolver_inv_literal_bound : forall n F A_arr A_inst M,
  msolver_inv_weak n F A_arr A_inst M -> 2 * ms_size M <= INT_MAX.
Proof.
  intros n F A_arr A_inst M H.
  pose proof (msw_shape H) as Hshape.
  unfold solver_shape in Hshape. tauto.
Qed.

(** Finite constructor-level [binary64] and [binary32] constants. *)
Definition msat_fp32_zero : fp32 := Binary.B754_zero 24 128 false.

Lemma msat_fp32_zero_nonnegative : msat_fp32_nonnegative msat_fp32_zero.
Proof. unfold msat_fp32_nonnegative, msat_fp32_zero. exact I. Qed.

Lemma msat_fp64_zero_finite : fp64_isFinite msat_fp64_zero.
Proof. reflexivity. Qed.

(** MiniSat's own default: [solver_new] stores [random_seed = 91648253]. *)
Definition msat_seed_default : Z := 91648253.

Definition msat_fp64_seed : fp64 := Z_to_fp64 msat_seed_default.

Lemma msat_seed_default_ok : seed_ok msat_seed_default.
Proof. unfold seed_ok, msat_seed_default. lia. Qed.

Lemma msat_fp64_seed_finite : fp64_isFinite msat_fp64_seed.
Proof.
  unfold msat_fp64_seed. apply MSatFloatFacts.Z_to_fp64_i32_finite.
  unfold msat_seed_default. lia.
Qed.

Lemma msat_fp64_seed_shadow : forall M,
  ms_random_seed M = msat_fp64_seed -> msolver_seed_shadow M.
Proof.
  intros M H. exists msat_seed_default.
  split; [exact H | exact msat_seed_default_ok].
Qed.

Lemma msat_fp64_zero_not_a_seed : forall z,
  seed_ok z -> Z_to_fp64 z <> msat_fp64_zero.
Proof. exact MSatFloatFacts.Z_to_fp64_seed_not_zero. Qed.

Lemma msat_fp64_zero_no_shadow : forall M,
  ms_random_seed M = msat_fp64_zero -> ~ msolver_seed_shadow M.
Proof.
  intros M H [z [Hz Hok]].
  apply (msat_fp64_zero_not_a_seed z Hok).
  rewrite <- Hz. exact H.
Qed.

(** *** Reseeding transfer.

    The seed field is read by exactly one invariant conjunct,
    [msolver_seed_ok], so replacing it preserves both bundles.  Reusing
    [msolver_search_select] avoids restating the record. *)
Definition msolver_reseed (M : msolver) (sd : fp64) : msolver :=
  msolver_search_select M (ms_orderpos M) (ms_order M) sd (ms_stats M).

Lemma msolver_inv_weak_reseed : forall n F A_arr A_inst M sd,
  msolver_inv_weak n F A_arr A_inst M ->
  fp64_isFinite sd ->
  msolver_inv_weak n F A_arr A_inst (msolver_reseed M sd).
Proof.
  intros n F A_arr A_inst M sd H Hsd.
  (* every field but [msw_seed] is convertible to the one for [M]; the seed
     field is convertible to [Hsd] *)
  destruct H. constructor; assumption.
Qed.

Lemma msolver_inv_reseed : forall n F A_arr A_inst M sd,
  msolver_inv n F A_arr A_inst M ->
  fp64_isFinite sd ->
  msolver_inv n F A_arr A_inst (msolver_reseed M sd).
Proof.
  intros n F A_arr A_inst M sd H Hsd.
  constructor.
  - apply msolver_inv_weak_reseed; [exact (msi_weak H) | exact Hsd].
  - exact (msi_prop_level H).
  - exact (msi_watch_frontier H).
  - exact (msi_heap_covers H).
  - exact (msi_reasonless_current H).
Qed.

