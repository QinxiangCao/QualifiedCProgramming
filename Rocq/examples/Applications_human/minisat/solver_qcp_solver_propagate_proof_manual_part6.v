From SimpleC.Verification Require Import VCPrelude.
Require Import Coq.Reals.Reals.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_lib.
Local Open Scope sac.


Require Export SimpleC.EE.Applications_human.minisat.solver_qcp_proof_common.

Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_solver_propagate_goal.
Require Import SimpleC.EE.Applications_human.minisat.solver_qcp_proof_automation.

Lemma proof_of_solver_propagate_partial_solve_wit_298_scan_move_pure : solver_propagate_partial_solve_wit_298_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_307_scan_move_pure : solver_propagate_partial_solve_wit_307_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_safety_wit_212_scan_same : solver_propagate_safety_wit_212_scan_same.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst retval. pose proof (lit_sign_c_range candidate). rewrite signed_last_nbits_8_lit_sign. msat_manual_entailer_with ltac:(int_auto || lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_10 : solver_propagate_which_implies_wit_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH1 as Hin.
  unfold enqueue_input in Hin.
  destruct Hin as [_ [_ [Hassigns [Hlevels [Hreasons [Htrail [Hqtail _]]]]]]].
  unfold enqueue_state_at.
  Exists rsn trl.
  msat_manual_entailer_with ltac:(first [assumption | lia]).
Qed.



Lemma proof_of_solver_propagate_which_implies_wit_52 : solver_propagate_which_implies_wit_52.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( Znth ii candidate_post_memory 0 = scan_current ) as H_Znth.
  bind_fact ( Zlength candidate_post_memory = Zlength source_words ) as H_Zlength.
  unfold propagation_ptr_segment.
  prop_apply_p (PtrArray.seg_valid begin 0 jj
    (sublist 0 jj candidate_post_memory)).
  prop_apply_p (PtrArray.seg_valid begin (jj + 1) ii
    (sublist (jj + 1) ii candidate_post_memory)).
  Intros_p Hlo. Intros_p Hmid.
  rewrite <- H_Znth.
  unfold StorePtrAsElement.storeA.
  sep_apply_l_atomic (PtrArray.seg_single begin jj
    (Znth ii candidate_post_memory 0)).
  sep_apply_l_atomic (PtrArray.seg_merge_to_seg begin 0 jj (jj + 1)
    (sublist 0 jj candidate_post_memory)
    ((Znth ii candidate_post_memory 0) :: nil)%list).
  - dump_pre_spatial. lia.
  - sep_apply_l_atomic (PtrArray.seg_merge_to_seg begin 0 (jj + 1) ii
      (sublist 0 jj candidate_post_memory ++
        ((Znth ii candidate_post_memory 0) :: nil))
      (sublist (jj + 1) ii candidate_post_memory)).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic (PtrArray.seg_single begin ii
        (Znth ii candidate_post_memory 0)).
      sep_apply_l_atomic (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
        ((sublist 0 jj candidate_post_memory ++
            ((Znth ii candidate_post_memory 0) :: nil)) ++
          sublist (jj + 1) ii candidate_post_memory)
        ((Znth ii candidate_post_memory 0) :: nil)%list).
      * dump_pre_spatial. lia.
      * prop_apply_p (PtrArray.seg_valid begin (ii + 1)
          (Zlength source_words)
          (sublist (ii + 1) (Zlength source_words)
            candidate_post_memory)).
        Intros_p Hhi.
        sep_apply_l_atomic (PtrArray.seg_merge_to_full begin 0 (ii + 1)
          (Zlength source_words)
          (((sublist 0 jj candidate_post_memory ++
               ((Znth ii candidate_post_memory 0) :: nil)) ++
             sublist (jj + 1) ii candidate_post_memory) ++
            ((Znth ii candidate_post_memory 0) :: nil))
          (sublist (ii + 1) (Zlength source_words)
            candidate_post_memory)).
        -- dump_pre_spatial. lia.
        -- rewrite <- H_Zlength.
           replace (Zlength candidate_post_memory - 0)
             with (Zlength candidate_post_memory) by lia.
           rewrite (replace_Znth_split jj (Znth ii candidate_post_memory 0) candidate_post_memory) by lia.
           rewrite (sublist_split (jj + 1)
             (Zlength candidate_post_memory) ii
             candidate_post_memory) by lia.
           rewrite (sublist_split ii
             (Zlength candidate_post_memory) (ii + 1)
             candidate_post_memory) by lia.
           rewrite (sublist_single 0 ii candidate_post_memory) by lia.
           simpl.
           replace (begin + 0) with begin by lia.
           assert (HL :
             (((sublist 0 jj candidate_post_memory ++
                  ((Znth ii candidate_post_memory 0) :: nil)) ++
                sublist (jj + 1) ii candidate_post_memory) ++
               ((Znth ii candidate_post_memory 0) :: nil)) ++
              sublist (ii + 1) (Zlength candidate_post_memory)
                candidate_post_memory =
             sublist 0 jj candidate_post_memory ++
               Znth ii candidate_post_memory 0 ::
               sublist (jj + 1) ii candidate_post_memory ++
               Znth ii candidate_post_memory 0 ::
               sublist (ii + 1) (Zlength candidate_post_memory)
                 candidate_post_memory).
           { rewrite <- !app_assoc. reflexivity. }
           rewrite HL.
           cancel.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_9 : solver_propagate_which_implies_wit_9.
Proof.
LLM_pre_process ltac:(lia || int_auto).
subst i.
  sep_apply (PtrArray.full_split_to_missing_i begin ii
    (Zlength source_words) tagged_memory 0 ltac:(lia)).
  msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_propagate_entail_wit_2_1 : solver_propagate_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_propagate_scan_begin trl rsn retval_4.
Qed.



Lemma proof_of_solver_propagate_entail_wit_5_1_scan_move : solver_propagate_entail_wit_5_1_scan_move.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlen_tecm : Zlength tagged_enqueue_conflict_memory = Zlength watch_memory).
  { match goal with
    | H1 : tagged_enqueue_conflict_memory = replace_Znth _ _ ?tm,
      H2 : ?tm = replace_Znth _ _ watch_memory |- _ =>
        rewrite H1, Zlength_replace_Znth, H2, Zlength_replace_Znth; reflexivity
    end. }
  assert (Hlen_ws : Zlength watch_memory = Zlength source_words) by lia.
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words)
    tagged_enqueue_conflict_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin tagged_enqueue_conflict_memory cap);
    [ | first [lia | vec_buf_solve] .. ].
  cancel.
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
  cancel.
  Exists (clause_lits_addr (ms_binary Mscan)).
  rewrite Hretval60.
  subst retval_5.
  rewrite ?Z.mul_0_l, ?Z.mul_1_l, ?Z.add_0_r.
  assert (Henq : tagged_enqueue_conflict_memory = tagged_memory).
  { rewrite Hupdate0.
    rewrite replace_Znth_Znth.
    reflexivity. }
  assert (Hready : propagation_binary_conflict_scan_ready n Mscan p
    (Znth ii tagged_memory 0) source_words simp_count prop_count).
  { unfold propagation_binary_conflict_scan_ready.
    split; [assumption|].
    split; [exact Hheap_covers|].
    split; [exact Hreasonless|].
    split; [exact Hcurrent_level|].
    split; [assumption|].
    split; [assumption|].
    apply Zlength_nonneg. }
  rewrite Henq, Htag0.
  rewrite !Znth_replace_Znth_Diff by lia.
  assert (Hcurrent :
    Znth ii tagged_memory 0 = Znth ii watch_memory 0) by
    (rewrite Htag0, Znth_replace_Znth_Diff by lia; reflexivity).
  rewrite <- Hcurrent.
  rewrite Zlength_replace_Znth.
  unfold clause_lits_pointer.
  split_pure_spatial.
  - cancel (solver_propagate_frame s_pre Mscan).
    cancel.
  - split_pures; dump_pre_spatial;
      solve [auto | lia | rewrite Htag0, Zlength_replace_Znth; lia].
Qed.



Lemma proof_of_solver_propagate_entail_wit_11_2_scan_same : solver_propagate_entail_wit_11_2_scan_same.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | subst candidate_post_memory; first [reflexivity | lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_12_4_scan_move : solver_propagate_entail_wit_12_4_scan_move.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | try rewrite Hcandidate; first [lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_6_real_satisfied : solver_propagate_entail_wit_20_6_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_9_real_satisfied : solver_propagate_entail_wit_20_9_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_251_scan_same_pure : solver_propagate_partial_solve_wit_251_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (retval_3 - 0) with retval_3 in * by lia.
  split_pures; dump_pre_spatial; try lia.
  all: try assumption.
  all: first [ (rewrite <- PreH2, <- PreH4; lia) | (rewrite <- PreH73; lia) ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_258_scan_same_pure : solver_propagate_partial_solve_wit_258_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite ?Z.sub_0_r in *.
  split_pures; dump_pre_spatial.
  all: try lia.
  all: try assumption.
  rewrite <- PreH2, <- PreH4, PreH3; lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_294_scan_same_pure : solver_propagate_partial_solve_wit_294_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_1 : solver_propagate_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_propagate_open_at, stats_propagations, stats_inspects in *.
  unfold solver_rep_assigns_levels_at.
  Intros act opos rsn trl tgs.
  unfold solver_rep_at.
  Intros.
  bind_fact (solver_propagation_inv n F A_arr K M0) as Hinv.
  bind_fact (solver_shape M0) as Hshape.
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
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  unfold solver_nonlevel_rep_at, solver_nonlevel_rep_nostats_at, solver_levels_slice_at,
    solver_scalars_rep, solver_vecs_rep, solver_trail_array_rep,
    solver_binary_rep, solver_propagate_frame, stats_rep,
    stats_propagate_frame.
  unfold stats_propagations, stats_inspects.
  Exists act opos tgs.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  cancel.
  csimpl.
  cancel.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_7 : solver_propagate_which_implies_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (msat_propagate_watch_prefix_write_refold watch_memory ii jj source_words raw_prefix scan_current raw_suffix begin PreH1 PreH2 PreH3 PreH4).
  cancel.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_26 : solver_propagate_which_implies_wit_26.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (msat_propagate_watch_prefix_write_refold watch_memory ii jj source_words raw_prefix scan_current raw_suffix begin PreH1 PreH2 PreH3 PreH4).
  cancel.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_15 : solver_propagate_which_implies_wit_15.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( i = begin + copy_src * sizeof ( PTR ) ) as H_i.
  bind_fact ( j = begin + copy_dst * sizeof ( PTR ) ) as H_j.
  destruct (Z.eq_dec copy_dst copy_src) as [Heq | Hneq].
  - subst copy_dst.
    Left; intros.
    unfold StorePtrAsElement.storeA.
    sep_apply_l_atomic (PtrArray.full_split_to_missing_i begin copy_src
      (Zlength source_words) copy_memory 0).
    + dump_pre_spatial. lia.
    + (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
      rewrite H_i.
      cancel.
  - assert (Hlt : copy_dst < copy_src) by lia.
    Right; intros.
    prop_apply_p (PtrArray.full_Zlength begin (Zlength source_words)
      copy_memory).
    Intros_p Hlen.
    sep_apply_l_atomic (PtrArray.full_split_to_seg begin copy_dst
      (Zlength source_words) copy_memory).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic (PtrArray.seg_split_to_seg begin copy_dst
        (copy_dst + 1) (Zlength source_words)
        (sublist copy_dst (Zlength source_words) copy_memory)).
      * dump_pre_spatial. lia.
      * rewrite !Zsublist_Zsublist by lia.
        replace (0 + copy_dst) with copy_dst by lia.
        replace (copy_dst + 1 - copy_dst + copy_dst)
          with (copy_dst + 1) by lia.
        replace (Zlength source_words - copy_dst + copy_dst)
          with (Zlength source_words) by lia.
        sep_apply_l_atomic (PtrArray.seg_split_to_seg begin
          (copy_dst + 1) copy_src (Zlength source_words)
          (sublist (copy_dst + 1) (Zlength source_words) copy_memory)).
        -- dump_pre_spatial. lia.
        -- rewrite !Zsublist_Zsublist by lia.
           replace (0 + (copy_dst + 1)) with (copy_dst + 1) by lia.
           replace (copy_src - (copy_dst + 1) + (copy_dst + 1))
             with copy_src by lia.
           replace (Zlength source_words - (copy_dst + 1) +
             (copy_dst + 1)) with (Zlength source_words) by lia.
           sep_apply_l_atomic (PtrArray.seg_split_to_seg begin copy_src
             (copy_src + 1) (Zlength source_words)
             (sublist copy_src (Zlength source_words) copy_memory)).
           ++ dump_pre_spatial. lia.
           ++ rewrite !Zsublist_Zsublist by lia.
              replace (0 + copy_src) with copy_src by lia.
              replace (copy_src + 1 - copy_src + copy_src)
                with (copy_src + 1) by lia.
              replace (Zlength source_words - copy_src + copy_src)
                with (Zlength source_words) by lia.
              rewrite (sublist_single 0 copy_src copy_memory) by lia.
              rewrite (sublist_single 0 copy_dst copy_memory) by lia.
              unfold PtrArray.seg at 1 4.
              simpl.
              (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
              rewrite H_i, H_j.
              cancel.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_51 : solver_propagate_which_implies_wit_51.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Heq : jj = ii) by lia.
  subst jj.
  rewrite <- PreH4.
  unfold propagation_ptr_segment.
  unfold StorePtrAsElement.storeA.
  prop_apply_p (PtrArray.seg_valid begin 0 ii
    (sublist 0 ii candidate_post_memory)).
  Intros_p Hlo.
  sep_apply_l_atomic (PtrArray.seg_single begin ii
    (Znth ii candidate_post_memory 0)).
  sep_apply_l_atomic (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    (sublist 0 ii candidate_post_memory)
    ((Znth ii candidate_post_memory 0) :: nil)%list).
  - dump_pre_spatial. lia.
  - prop_apply_p (PtrArray.seg_valid begin (ii + 1)
      (Zlength source_words)
      (sublist (ii + 1) (Zlength source_words)
        candidate_post_memory)).
    Intros_p Hhi.
    sep_apply_l_atomic (PtrArray.seg_merge_to_full begin 0 (ii + 1)
      (Zlength source_words)
      (sublist 0 ii candidate_post_memory ++
        ((Znth ii candidate_post_memory 0) :: nil))
      (sublist (ii + 1) (Zlength source_words)
        candidate_post_memory)).
    + dump_pre_spatial. lia.
    + rewrite <- PreH3.
      replace (begin + 0 * sizeof (PTR)) with begin by ring.
      replace (Zlength candidate_post_memory - 0)
        with (Zlength candidate_post_memory) by lia.
      rewrite (replace_Znth_split ii
        (Znth ii candidate_post_memory 0) candidate_post_memory) by lia.
      simpl.
      rewrite <- app_assoc.
      reflexivity.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_44 : solver_propagate_which_implies_wit_44.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (replace_Znth ii scan_current candidate_post_memory).
  split_pure_spatial;
    [ cancel
    | split_pures; dump_pre_spatial;
      first [ reflexivity | rewrite <- PreH1, replace_Znth_Znth; reflexivity ] .. ].
Qed.



Lemma proof_of_solver_propagate_entail_wit_10_binary_conflict : solver_propagate_entail_wit_10_binary_conflict.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold stats_propagations in *.
    bind_fact ( propagation_binary_conflict_exit n F A_arr K M0 Mentry Mscan Mroute p scan_current confl source_words
      retained moved rest copy_memory garbage_route retained_route ) as H_propagation_binary_conflict_exit.
    bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
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
    scan_wm
    retained_route source_words moved garbage_route copy_memory
    (Zlength source_words) (Zlength retained_route)
    retained_route (@nil Z) Mentry.
  Exists Mroute levels_entry.
  split_pure_spatial.
  - unfold solver_propagation_scan_arrays_noqh_at.
    cancel (Vecp.rep_ptr (Vecp.slot wlists_entry p) begin copy_memory).
    cancel (clause_db_rep (ms_prob Mroute)).
    cancel (clause_db_rep (ms_learnt Mroute)).
    cancel (&( s_pre # "solver_t" ->ₛ "qhead") # Int |-> mt_qhead (ms_core Mroute)).
    cancel.
  - split_pures; dump_pre_spatial;
      solve [assumption | reflexivity | tauto | (rewrite app_nil_r; reflexivity) | lia].
Qed.



Lemma proof_of_solver_propagate_entail_wit_11_11_scan_same : solver_propagate_entail_wit_11_11_scan_same.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | try rewrite Hcandidate; first [lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_16_2_unit_conflict_copy : solver_propagate_entail_wit_16_2_unit_conflict_copy.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( i < endvar ) as H_i.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( endvar = begin + Zlength source_words * sizeof ( PTR ) ) as H_endvar.
  bind_fact ( i = begin + copy_src_2 * sizeof ( PTR ) ) as H_i_2.
  bind_fact ( binary_watch_copy_progress watch_memory raw_prefix scan_current raw_suffix ii jj copy_src_2 copy_dst_2
      copy_memory_2 ) as H_binary_watch_copy_progress.
  Exists (replace_Znth copy_dst_2 (Znth copy_src_2 copy_memory_2 0)
    copy_memory_2) (copy_dst_2 + 1) (copy_src_2 + 1).
  assert (Hbound : 0 <= copy_src_2 < Zlength source_words).
  { change (sizeof (PTR)) with ptr_size_Z in H_endvar, H_i_2. unfold_arch. cbn in H_endvar, H_i_2. nia. }
  split_pure_spatial.
  - sep_apply PtrArray.full_to_seg.
    sep_apply (PtrArray.seg_merge_to_seg begin 0 (copy_dst_2 + 1)
      (copy_src_2 + 1)) ; try lia.
    sep_apply (PtrArray.seg_merge_to_full begin 0 (copy_src_2 + 1)
      (Zlength source_words)) ; try lia.
    unfold binary_watch_copy_progress in H_binary_watch_copy_progress.
    destruct H_binary_watch_copy_progress as [copied [rest0
      [Hwords [Hkept [Hjj [Hsuffix [Hsrc [Hdst [Hmem Hlen]]]]]]]]].
    unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
    destruct H_propagation_watch_scan_physical as [_ [_ [_ [_ Hphysical_len]]]].
    assert (Hcopy_length :
      Zlength copy_memory_2 = Zlength source_words) by lia.
    assert (Hdst_length :
      copy_dst_2 + 1 <= Zlength copy_memory_2) by
      (rewrite Hcopy_length; lia).
    assert (Hsrc_length :
      copy_src_2 + 1 <= Zlength copy_memory_2) by
      (rewrite Hcopy_length; lia).
    pose proof (eq_sym (sublist_snoc 0 copy_memory_2 0 copy_dst_2
      ltac:(lia) ltac:(lia))) as Hprefix.
    pose proof (eq_sym (sublist_snoc 0 copy_memory_2 (copy_dst_2 + 1) copy_src_2
      ltac:(lia) ltac:(lia))) as Hmid.
    assert (Hvalue :
      Znth (copy_src_2 - (copy_dst_2 + 1))
        (sublist (copy_dst_2 + 1) copy_src_2 copy_memory_2 +::
          Znth copy_src_2 copy_memory_2 0) 0 =
      Znth copy_src_2 copy_memory_2 0).
    { rewrite Hmid.
      rewrite Znth_sublist by lia.
      replace (copy_src_2 - (copy_dst_2 + 1) +
        (copy_dst_2 + 1)) with copy_src_2 by lia.
      reflexivity. }
    pose proof (replace_Znth_prefix_split copy_memory_2 copy_dst_2
      copy_src_2 (Zlength source_words) ltac:(lia) ltac:(lia) ltac:(lia)
      (eq_sym Hcopy_length)) as Hreplace.
    rewrite Hvalue, Hprefix, Hmid.
    rewrite <- Hreplace.
    replace (begin + 0 * sizeof (PTR)) with begin by ring.
    replace (Zlength source_words - 0) with (Zlength source_words) by lia.
    sep_apply (PtrArray.full_to_seg begin (Zlength source_words)
      (replace_Znth copy_dst_2 (Znth copy_src_2 copy_memory_2 0) copy_memory_2)).
    sep_apply (Vecp.rep_ptr_intro ws begin
      (replace_Znth copy_dst_2 (Znth copy_src_2 copy_memory_2 0) copy_memory_2) cap);
      [ | rewrite ?Zlength_replace_Znth; first [lia | vec_buf_solve] .. ].
    cancel.
    all: lia.
  - split_pures; dump_pre_spatial; try solve [auto | lia].
    + rewrite Zlength_replace_Znth. lia.
    + assert (Hcursor_words : copy_src_2 < Zlength watch_memory).
      { assert (Hwatch_len : Zlength watch_memory = Zlength source_words).
        { unfold propagation_watch_scan_physical in H_propagation_watch_scan_physical.
          tauto. }
        lia. }
      pose proof (ms_binary_watch_copy_step__common
        watch_memory raw_prefix scan_current raw_suffix
        ii jj copy_src_2 copy_dst_2 copy_memory_2
        H_binary_watch_copy_progress Hcursor_words) as Hprogress_next.
      exact Hprogress_next.
Qed.


Lemma proof_of_solver_propagate_entail_wit_17_unit_conflict : solver_propagate_entail_wit_17_unit_conflict.
Proof.
  LLM_pre_process ltac:(idtac).
  unfold propagation_unit_conflict_transition in PreH3.
  destruct PreH3 as [HMroute Hsem].
  unfold propagation_scan_conflict_step in PreH5.
  destruct PreH5 as [Hretained Hphysical].
  unfold solver_qcp_model.propagation_watch_scan_physical in Hphysical, PreH15.
  destruct Hphysical as
    [Hinv_final [Hmemory_final [Hkept_final [Hprefix_final Hmemory_length]]]].
  destruct PreH15 as
    [Hinv_old [Hmemory_old [Hkept_old [Hprefix_old Hmemory_old_length]]]].
  unfold binary_watch_copy_progress in PreH26.
  destruct PreH26 as
    (copied & copy_rest & Hwords & Hkept & Hbounds & Hsuffix &
     Hsrc & Hdst & Hcopy_memory & Hcopy_length).
  unfold solver_qcp_model.wlist_scan_inv in Hinv_final, Hinv_old.
  assert (Hsource_final :
    Zlength source_words = Zlength retained_route + Zlength moved).
  { pose proof
      (solver_qcp_model.Zlength_perm_eq _ _ _ Hinv_final) as Hlen.
    rewrite !Zlength_app in Hlen. cbn in Hlen. lia. }
  assert (Hsource_positive : 0 < Zlength source_words).
  { pose proof
      (solver_qcp_model.Zlength_perm_eq _ _ _ Hinv_old) as Hlen.
    rewrite PreH18 in Hlen.
    rewrite !Zlength_app in Hlen.
    rewrite Zlength_cons in Hlen. cbn in Hlen.
    pose proof (Zlength_nonneg retained).
    pose proof (Zlength_nonneg moved).
    pose proof (Zlength_nonneg raw_suffix). lia. }
  change (sizeof(PTR)) with ptr_size_Z in *.
  unfold_arch.
  assert (Hcopy_src : copy_src = Zlength source_words) by lia.
  assert (Hsource_raw :
    Zlength source_words = ii + 1 + Zlength raw_suffix).
  { rewrite <- Hmemory_old_length, Hwords.
    rewrite !Zlength_app, Zlength_cons, Hkept. lia. }
  assert (Hcopied_raw : Zlength copied = Zlength raw_suffix) by lia.
  assert (Hretained_length :
    Zlength retained_route = jj + 1 + Zlength raw_suffix).
  { rewrite Hretained, Zlength_app, PreH18, Zlength_cons, Hkept_old. lia. }
  assert (Hcopy_dst : copy_dst = Zlength retained_route) by lia.
  assert (Hretained_bound :
    Zlength retained_route <= Zlength source_words).
  { pose proof (Zlength_nonneg moved). lia. }
  Left.
  Exists trl_route rsn_route
    (Znth 2 (solver_qcp_model.ms_stats Mroute) 0)
    (solver_qcp_model.ms_simpdb_props Mroute)
    scan_wm (retained ++ rest)%list source_words moved garbage_route
    copy_memory (Zlength source_words) (Zlength retained_route)
    retained_route (@nil Z) Mentry Mroute levels_entry.
  split_pure_spatial.
  - unfold solver_qcp_model.solver_propagation_scan_core_at.
    rewrite HMroute.
    unfold solver_qcp_model.msolver_propagation_db_wmap_update,
      solver_qcp_model.msolver_propagation_overlay,
      solver_qcp_model.msolver_propagation_update.
    cbn.
    unfold PtrArray.seg, solver_qcp_model.stats_propagate_scan.
    set_String_name. sepcon_assoc_change. sepcon_cancel.
    subst_all_strings.
    exact
      (stats_propagate_scan_refold__propagate
        s_pre (Znth 2 (solver_qcp_model.ms_stats Mscan) 0)
        (solver_qcp_model.ms_stats Mscan)).
  - split_pures; dump_pre_spatial;
      try exact Hsem; try assumption; try reflexivity; try tauto;
      try (rewrite List.app_nil_r; congruence); try lia;
      try rewrite HMroute;
      try unfold solver_qcp_model.msolver_propagation_db_wmap_update,
        solver_qcp_model.msolver_propagation_overlay,
        solver_qcp_model.msolver_propagation_update;
      cbn; try assumption; try reflexivity; try tauto; try lia.
Qed.



Lemma proof_of_solver_propagate_entail_wit_19_2_binary_keep : solver_propagate_entail_wit_19_2_binary_keep.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_binary_keep.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_3_real_satisfied : solver_propagate_entail_wit_20_3_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_4_real_satisfied : solver_propagate_entail_wit_20_4_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_25_2_unit_success : solver_propagate_entail_wit_25_2_unit_success.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  Exists trl_next rsn_next simp_count_next prop_count_next next_wm logical_next source_words_next moved_next garbage_next memory_next ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  subst lvl_next.
  split_pure_spatial.
  - unfold solver_propagation_scan_core_at, stats_propagate_scan.
    cbn -[ptr_size_Z Znth].
    msat_cancel_sound.
    csimpl.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.



Lemma proof_of_solver_propagate_entail_wit_27_3_binary_conflict : solver_propagate_entail_wit_27_3_binary_conflict.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( lvl_next = levels_entry ) as H_lvl_next.
  Left.
  Exists trl_next rsn_next prop_count_next simp_count_next next_wm logical_next source_words_next moved_next garbage_next memory_next ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  msat_propagate_binary_keep_close H_lvl_next.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_87_binary_keep_pure : solver_propagate_partial_solve_wit_87_binary_keep_pure.
Abort.


Lemma proof_of_solver_propagate_partial_solve_wit_266_scan_same_pure : solver_propagate_partial_solve_wit_266_scan_same_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  rewrite Z.sub_0_r in PreH1.
  bind_fact ( Mscan = msolver_propagation_scan_begin Mentry simp_count prop_count ) as H_scan.
  repeat lazymatch goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end.
  all: dump_pre_spatial.
  all: subst retval_3 retval_2.
  all: rewrite <- ?H_scan.
  all: first [assumption | reflexivity | lia].
Qed.



Lemma proof_of_solver_propagate_which_implies_wit_2 : solver_propagate_which_implies_wit_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact (mt_qhead (ms_core M1) < ms_qtail M1) as Hcurrent_pending.
  bind_fact
    (mt_qhead (ms_core M0) >= ms_qtail M0 -> M1 = M0 /\ cf = 0)
    as Hentry_idle.
  assert (Hentry_pending : mt_qhead (ms_core M0) < ms_qtail M0).
  {
    destruct (Z_lt_ge_dec
      (mt_qhead (ms_core M0)) (ms_qtail M0)) as [Hlt | Hge].
    - exact Hlt.
    - destruct (Hentry_idle Hge) as [Heq _]. subst M1. lia.
  }
  bind_fact ( solver_propagation_loop_inv n F A_arr K M0 M1 cf ) as H_solver_propagation_loop_inv.
  unfold solver_propagation_loop_inv in H_solver_propagation_loop_inv.
  destruct H_solver_propagation_loop_inv as [Hframe [[_ Hinv] | [Hconflict _]]].
  - (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - lia.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_34 : solver_propagate_which_implies_wit_34.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (Znth (offset - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0).
  subst k. unfold propagation_int_missing.
  sep_apply (IntArray.seg_split_to_missing_i lits 2 offset (Zlength clause_contents)
    (sublist 2 (Zlength clause_contents) clause_contents) 0 ltac:(lia)).
  split_pure_spatial; [cancel | split_pures; dump_pre_spatial; lia ..].
Qed.



Lemma proof_of_solver_propagate_which_implies_wit_39 : solver_propagate_which_implies_wit_39.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( propagation_destination_ok (2 * ms_size Mscan) p (lit_neg_c candidate) ) as
      H_propagation_destination_ok.
  unfold propagation_destination_ok in H_propagation_destination_ok.
  destruct H_propagation_destination_ok as [Hhole [Htarget Hdistinct]].
  prop_apply_p (VecpArray.missing_i_index_range wlists_entry p 0 (2 * n) scan_wm). Intros.
  prop_apply_p (VecpArray.missing_i_Zlength wlists_entry p 0 (2 * n) scan_wm). Intros.
  sep_apply (VecpArray.missing_i_split_to_missing2 wlists_entry p (lit_neg_c candidate)
    (2 * n) scan_wm nil); [ | lia | lia | lia ].
  unfold VecpArray.vec_store.
  cancel.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_42 : solver_propagate_which_implies_wit_42.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite Znth_replace_Znth_Same in PreH4 by lia.
  Exists destination_words_now_2.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_56 : solver_propagate_which_implies_wit_56.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Heq : jj = ii) by lia.
  subst jj.
  unfold propagation_ptr_segment.
  prop_apply_p (PtrArray.seg_valid begin 0 ii
    (sublist 0 ii candidate_post_memory)).
  Intros_p Hlo.
  sep_apply_l_atomic (PtrArray.seg_single begin ii scan_current).
  sep_apply_l_atomic (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    (sublist 0 ii candidate_post_memory) (scan_current :: nil)%list).
  - dump_pre_spatial. lia.
  - prop_apply_p (PtrArray.seg_valid begin (ii + 1)
      (Zlength source_words)
      (sublist (ii + 1) (Zlength source_words)
        candidate_post_memory)).
    Intros_p Hhi.
    sep_apply_l_atomic (PtrArray.seg_merge_to_full begin 0 (ii + 1)
      (Zlength source_words)
      (sublist 0 ii candidate_post_memory ++ (scan_current :: nil))
      (sublist (ii + 1) (Zlength source_words)
        candidate_post_memory)).
    + dump_pre_spatial. lia.
    + rewrite <- PreH3.
      replace (begin + 0 * sizeof (PTR)) with begin by ring.
      replace (Zlength candidate_post_memory - 0)
        with (Zlength candidate_post_memory) by lia.
      rewrite (replace_Znth_split ii scan_current candidate_post_memory)
        by lia.
      simpl.
      rewrite <- app_assoc.
      reflexivity.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_33 : solver_propagate_which_implies_wit_33.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact ( Forall (lit_wf_c n) clause_contents ) as H_Forall.
  bind_fact ( false_lit = lit_neg_c p ) as H_false_lit.
  unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics.
  destruct H_solver_propagation_scan_semantics as [[_ Hlive] | [Hcontra _]]; [|lia].
  destruct Hlive as
    (_ & _ & _ & _ & _ & _ & Hp_wf & Hprocessed & _ & _).
  destruct Hprocessed as [Hp_true _].
  assert (Hwatch_wf : lit_wf_c n watch0_base).
  { unfold lit_wf_c. lia. }
  assert (Hfalse_wf : lit_wf_c n false_lit).
  { rewrite H_false_lit. apply lit_neg_c_wf. exact Hp_wf. }
  assert (Htail_wf :
    Forall (lit_wf_c n)
      (sublist 2 (Zlength clause_contents) clause_contents)).
  {
    rewrite <- (sublist_self clause_contents (Zlength clause_contents) eq_refl)
      in H_Forall.
    rewrite (sublist_split 0 (Zlength clause_contents) 2 clause_contents)
      in H_Forall by lia.
    apply Forall_app in H_Forall.
    exact (proj2 H_Forall).
  }
  assert (Hwords_wf :
    Forall (lit_wf_c n)
      (propagation_normalized_clause watch0_base false_lit clause_contents)).
  {
    unfold propagation_normalized_clause.
    constructor; [exact Hwatch_wf|].
    constructor; [exact Hfalse_wf|exact Htail_wf].
  }
  assert (Hfalse : lit_false (mt_assigns (ms_core Mscan)) false_lit).
  {
    rewrite H_false_lit.
    unfold lit_false, lit_true in *.
    rewrite lit_var_c_neg, lit_sig_neg.
    lia.
  }
  assert (Hinv :
    propagation_replacement_scan_inv n Mscan false_lit
      (propagation_normalized_clause watch0_base false_lit clause_contents) 2).
  {
    unfold propagation_replacement_scan_inv.
    split.
    - rewrite propagation_normalized_clause_length by lia. lia.
    - split; [exact Hwords_wf|].
      split.
      + unfold propagation_normalized_clause. simpl. reflexivity.
      + split; [exact Hfalse|].
        intros j Hj. lia.
  }
  msat_manual_entailer_with ltac:(lia).
Qed.
