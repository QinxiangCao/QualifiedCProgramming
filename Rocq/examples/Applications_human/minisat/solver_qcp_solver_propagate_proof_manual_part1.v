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
Lemma proof_of_solver_propagate_entail_wit_11_7_scan_same : solver_propagate_entail_wit_11_7_scan_same.
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



Lemma proof_of_solver_propagate_entail_wit_12_2_scan_move : solver_propagate_entail_wit_12_2_scan_move.
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



Lemma proof_of_solver_propagate_entail_wit_12_10_scan_move : solver_propagate_entail_wit_12_10_scan_move.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap);
    [ | subst candidate_post_memory; first [lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close_nested_addr 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_15_real_satisfied : solver_propagate_entail_wit_20_15_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_18_real_satisfied : solver_propagate_entail_wit_20_18_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_25_1_unit_success : solver_propagate_entail_wit_25_1_unit_success.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists trl_next rsn_next prop_count_next simp_count_next next_wm logical_next source_words_next moved_next garbage_next memory_next ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  subst lvl_next.
  split_pure_spatial.
  - unfold solver_propagation_scan_core_at, stats_propagate_scan.
    msat_cancel_sound.
    csimpl.
    cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_94_binary_keep_pure : solver_propagate_partial_solve_wit_94_binary_keep_pure.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
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
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength_3.
  bind_fact ( 0 <= ii ) as H_ii_2.
  bind_fact ( ii <= Zlength source_words ) as H_ii_3.
  bind_fact ( 0 <= Zlength source_words ) as H_Zlength_4.
  (* The watch row is physically [(retained ++ garbage) ++ rest]: [ii] counts the words
     already inspected and [jj] the words already kept.  Every residual conjunct is read
     off that one layout, so open a copy of it once instead of once per arm. *)
  pose proof H_propagation_watch_scan_physical as Hphys.
  unfold propagation_watch_scan_physical in Hphys.
  destruct Hphys as [Hperm [Hmem [Hkept [Hkg Hlen]]]].
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
  assert (Hcursor : Znth ii (replace_Znth ii scan_current watch_memory) 0 = scan_current).
  { apply Znth_replace_Znth_Same. rewrite H_Zlength_3. lia. }
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
  split_pures; dump_pre_spatial; try rewrite Hcursor;
    solve [ auto | lia | unfold tagged_word; exact H_is_tag ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_297_scan_move_pure : solver_propagate_partial_solve_wit_297_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_13 : solver_propagate_which_implies_wit_13.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  subst i.
  sep_apply_l_atomic
    (PtrArray.full_split_to_missing_i begin ii (Zlength source_words)
      tagged_enqueue_conflict_memory 0);
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_17 : solver_propagate_which_implies_wit_17.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (replace_Znth ii (Znth ii tagged_memory 0) tagged_memory).
  msat_propagate_ptr_missing_merge begin ii source_words tagged_memory i;
    msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_propagate_which_implies_wit_21 : solver_propagate_which_implies_wit_21.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold clause_db_pair_focus, clause_db_pair_frame,
    MiniSatClause.rep, IntArray.full.
  Intros is_learnt.
  Exists is_learnt.
  msat_manual_entailer_with ltac:(int_auto).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_28 : solver_propagate_which_implies_wit_28.
Proof.
LLM_pre_process ltac:(lia || int_auto).
unfold clause_db_pair_frame.
  Intros is_learnt_scan.
  Exists is_learnt_scan.
  pose proof
    (clause_hdr_word_div2 is_learnt_scan (Zlength clause_contents)
      (Zlength_nonneg clause_contents)) as Hhdr.
  split_pure_spatial.
  - cancel (activity_state scan_current is_learnt_scan (Zlength clause_contents)).
    cancel.
  - dump_pre_spatial.
    rewrite zdiv_equiv.
    + exact Hhdr.
    + unfold clause_hdr_word.
      destruct is_learnt_scan;
        pose proof (Zlength_nonneg clause_contents); lia.
    + lia.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_53 : solver_propagate_which_implies_wit_53.
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


Lemma proof_of_solver_propagate_entail_wit_7_scan_move : solver_propagate_entail_wit_7_scan_move.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  cancel.
  bind_fact (retval_2 = tag_lit (Znth ii tagged_enqueue_conflict_memory 0))
      as H_retval_2.
  bind_fact ( scratch_base0 = clause_lits_addr (ms_binary Mscan) ) as H_scratch_base0.
  bind_fact ( retval = clause_lits_addr (ms_binary Mscan) ) as H_retval_ptr.
  bind_fact ( Znth ii tagged_enqueue_conflict_memory 0 = scan_current ) as H_Znth.
  bind_fact ( confl = ms_binary Mscan ) as H_confl.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength_2.
  bind_fact ( tagged_enqueue_conflict_memory = replace_Znth jj scan_current watch_memory )
      as H_tagged_enqueue_conflict_memory.
  rewrite <- H_scratch_base0.
  rewrite H_confl.
  rewrite H_Znth in H_retval_2.
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words) tagged_enqueue_conflict_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin tagged_enqueue_conflict_memory cap
    (Zlength tagged_enqueue_conflict_memory) (Zlength source_words)
    (Zlength tagged_enqueue_conflict_memory)); [ | first [lia | vec_buf_solve] .. ].
  cancel.
  Exists tagged_enqueue_conflict_memory (jj + 1) (ii + 1)
         (retval_2 :: lit_neg_c p :: nil) scratch_base0.
  cancel.
  unfold IntArray.full, IntArray.seg, store_array.
  split_pure_spatial.
  - rewrite H_retval_ptr, <- H_scratch_base0.
    simpl.
    split_pure_spatial.
    + cancel (solver_propagate_frame s_pre Mscan).
      simpl_nonptr_sizeof.
      cancel.
    + split_pures; dump_pre_spatial; reflexivity.
  - split_pures; dump_pre_spatial;
      solve [auto | lia | msat_binary_copy_start_close raw_suffix H_watch_memory
        H_Zlength_2 H_tagged_enqueue_conflict_memory H_retval_2 H_Znth].
Qed.



Lemma proof_of_solver_propagate_entail_wit_11_5_scan_same : solver_propagate_entail_wit_11_5_scan_same.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap);
    [ | subst candidate_post_memory; first [lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_11_12_scan_same : solver_propagate_entail_wit_11_12_scan_same.
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



Lemma proof_of_solver_propagate_entail_wit_12_8_scan_move : solver_propagate_entail_wit_12_8_scan_move.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | subst candidate_post_memory; first [reflexivity | lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close_nested_addr 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_19_1_binary_keep : solver_propagate_entail_wit_19_1_binary_keep.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_binary_keep.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_13_real_satisfied : solver_propagate_entail_wit_20_13_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_20_real_satisfied : solver_propagate_entail_wit_20_20_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_26_1_real_migrated : solver_propagate_entail_wit_26_1_real_migrated.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists trl_next rsn_next prop_count_next simp_count_next next_wm logical_next source_words_next moved_next garbage_next memory_next ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  subst lvl_next.
  split_pure_spatial.
  - unfold solver_propagation_scan_core_at, stats_propagate_scan.
    cbn -[ptr_size_Z Znth Vecp.rep_ptr].
    cancel (solver_propagate_frame s_pre Mnext).
    cancel.
    csimpl. cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.



Lemma proof_of_solver_propagate_entail_wit_27_6_unit_conflict : solver_propagate_entail_wit_27_6_unit_conflict.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( lvl_next = levels_entry ) as H_lvl_next.
  Right.
  Exists trl_next rsn_next simp_count_next prop_count_next next_wm logical_next source_words_next moved_next garbage_next memory_next ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  msat_propagate_binary_keep_close H_lvl_next.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_6_pure : solver_propagate_partial_solve_wit_6_pure.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 rewrite !Z.sub_0_r. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_90_binary_keep_pure : solver_propagate_partial_solve_wit_90_binary_keep_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH19, <- PreH18.
  try subst retval.
  try match goal with H : tagged_memory = replace_Znth _ _ _ |- _ =>
    assert (Htlen : Zlength tagged_memory = Zlength watch_memory)
      by (rewrite H; apply Zlength_replace_Znth) end.
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  split_pures; dump_pre_spatial.
  all: try lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_259_scan_same_pure : solver_propagate_partial_solve_wit_259_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_close_scan_first_lit_assigned.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_306_scan_move_pure : solver_propagate_partial_solve_wit_306_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_37 : solver_propagate_which_implies_wit_37.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( ms_wm Mscan = replace_Znth p logical_words scan_wm ) as H_ms_wm.
  unfold solver_shape in H_solver_shape.
  rewrite H_ms_wm in H_solver_shape.
  rewrite Zlength_replace_Znth in H_solver_shape.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]); intuition (try lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_47 : solver_propagate_which_implies_wit_47.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  simpl_nonptr_sizeof.
  assert (Hoffset : offset = Zlength clause_contents) by lia.
  subst offset.
  entailer!.
Qed.


Lemma proof_of_solver_propagate_entail_wit_11_9_scan_same : solver_propagate_entail_wit_11_9_scan_same.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap);
    [ | subst candidate_post_memory; first [lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_12_6_scan_move : solver_propagate_entail_wit_12_6_scan_move.
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



Lemma proof_of_solver_propagate_entail_wit_12_11_scan_move : solver_propagate_entail_wit_12_11_scan_move.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | subst candidate_post_memory; first [reflexivity | lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close_nested_addr 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_8_real_satisfied : solver_propagate_entail_wit_20_8_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_22_real_satisfied : solver_propagate_entail_wit_20_22_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_23_1_binary_keep : solver_propagate_entail_wit_23_1_binary_keep.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists trl_next rsn_next prop_count_next simp_count_next next_wm logical_next source_words_next moved_next garbage_next memory_next ii_next jj_next retained_next rest_next Mentry_next.
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



Lemma proof_of_solver_propagate_entail_wit_27_5_unit_conflict : solver_propagate_entail_wit_27_5_unit_conflict.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( lvl_next = levels_entry ) as H_lvl_next.
  Left.
  Exists trl_next rsn_next prop_count_next simp_count_next next_wm logical_next source_words_next moved_next garbage_next memory_next ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  msat_propagate_binary_keep_close H_lvl_next.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_265_scan_same_pure : solver_propagate_partial_solve_wit_265_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try replace (retval_3 - 0) with retval_3 in * by lia.
  subst retval_3. rewrite <- PreH73.
  split_pures; dump_pre_spatial; first [ assumption | lia ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_293_scan_same_pure : solver_propagate_partial_solve_wit_293_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_299_scan_move_pure : solver_propagate_partial_solve_wit_299_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_311_scan_move_pure : solver_propagate_partial_solve_wit_311_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_414_scan_same_pure : solver_propagate_partial_solve_wit_414_scan_same_pure.
Proof.  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH9 as (Hs1 & Hs2 & Hs3 & _).
  unfold lit_var_c in PreH2, PreH3.
  pose proof (Z_div_mod_eq_full candidate 2) as Hdm.
  pose proof (Z.mod_pos_bound candidate 2 ltac:(lia)) as Hmb.
  split_pures; dump_pre_spatial; lia.
Qed.



Lemma proof_of_solver_propagate_return_wit_1 : solver_propagate_return_wit_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
rename M1 into Mcur.
bind_fact (solver_shape Mcur) as Hshape.
bind_fact (solver_propagation_loop_inv n F A_arr K M0 Mcur cf) as Hloop.
bind_fact (minisat_propagation_reuse_loop n M0 Mcur cf) as Hreuse.
bind_fact (mt_qhead (ms_core M0) >= ms_qtail M0 -> Mcur = M0 /\ cf = 0) as Hidle.
destruct Hloop as [Hframe [[Hzero Hinv] | [Hnonzero [focus [C [Hready [Hcert Hdenotes]]]]]]].
- contradiction.
- destruct Hreuse as [Hcompleted [Hresident Hconflict_resident]].
  assert (Hpending : mt_qhead (ms_core M0) < ms_qtail M0).
  { destruct (Z_lt_ge_dec (mt_qhead (ms_core M0)) (ms_qtail M0)) as [Hlt|Hge].
    - exact Hlt.
    - destruct (Hidle Hge) as [_ Hzero]. contradiction. }
  assert (Hwatch : minisat_base_watch_completed M0 -> minisat_watch_conflict_ready n Mcur).
  { intro Hentry. exact (proj2 (Hcompleted Hentry) Hnonzero). }
  pose proof (Hconflict_resident Hnonzero) as Hfalse.
  unfold solver_propagate_open_at.
  lazymatch goal with
  | |- _ |-- ?T =>
      assert (Hcut : solver_rep_assigns_levels_at s_pre Mcur assigns_entry levels_entry wlists_entry **
        ((( &( "l_Undef" ) ) # Char |-> 0) ** (( &( "true" ) ) # Int |-> 1)) |-- T)
  end.
  { Exists C Mcur focus. msat_manual_entailer_with ltac:(lia || tauto). }
  sep_apply_r_atomic Hcut.
  sep_apply_r_atomic (solver_propagation_open_refold__propagate s_pre Mcur assigns_entry rsn levels_entry trl wlists_entry Hshape).
  cancel (&( "true") # Int |-> 1).
  cancel.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_30 : solver_propagate_which_implies_wit_30.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( raw_prefix ++ scan_current :: raw_suffix = watch_memory ) as H_raw_prefix.
  rewrite <- H_raw_prefix.
  unfold propagation_ptr_segment.
  prop_apply_p (PtrArray.seg_valid begin 0 ii raw_prefix).
  Intros.
  prop_apply_p (PtrArray.seg_valid begin (ii + 1)
    (Zlength source_words) raw_suffix).
  Intros.
  sep_apply (PtrArray.seg_single begin ii scan_current).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    raw_prefix (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words) (raw_prefix ++ scan_current :: nil)
    raw_suffix ltac:(lia)).
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  replace ((raw_prefix ++ scan_current :: nil) ++ raw_suffix) with
    (raw_prefix ++ scan_current :: raw_suffix) by
    (rewrite <- app_assoc; reflexivity).
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_31 : solver_propagate_which_implies_wit_31.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( raw_prefix ++ scan_current :: raw_suffix = watch_memory ) as H_raw_prefix.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  pose proof (Znth_split 0 raw_prefix jj ltac:(lia)) as Hsplit.
  rewrite <- H_raw_prefix.
  unfold propagation_ptr_segment.
  prop_apply_p (PtrArray.seg_valid begin (ii + 1)
    (Zlength source_words) raw_suffix).
  Intros.
  sep_apply (PtrArray.seg_single begin jj (Znth jj raw_prefix 0)).
  sep_apply (PtrArray.seg_single begin ii scan_current).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 jj (jj + 1)
    (sublist 0 jj raw_prefix) (Znth jj raw_prefix 0 :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 (jj + 1) ii
    (sublist 0 jj raw_prefix ++ Znth jj raw_prefix 0 :: nil)
    (sublist (jj + 1) ii raw_prefix) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_seg begin 0 ii (ii + 1)
    ((sublist 0 jj raw_prefix ++ Znth jj raw_prefix 0 :: nil) ++
      sublist (jj + 1) ii raw_prefix)
    (scan_current :: nil) ltac:(lia)).
  sep_apply (PtrArray.seg_merge_to_full begin 0 (ii + 1)
    (Zlength source_words)
    (((sublist 0 jj raw_prefix ++ Znth jj raw_prefix 0 :: nil) ++
      sublist (jj + 1) ii raw_prefix) ++ scan_current :: nil)
    raw_suffix ltac:(lia)).
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  rewrite <- !app_assoc.
  simpl.
  cancel.
  rewrite H_Zlength in Hsplit.
  assert (Hwords :
    sublist 0 jj raw_prefix ++
      Znth jj raw_prefix 0 ::
      sublist (jj + 1) ii raw_prefix ++ scan_current :: raw_suffix =
    raw_prefix ++ scan_current :: raw_suffix).
  {
    pose proof
      (f_equal (fun words => words ++ scan_current :: raw_suffix) Hsplit)
      as Happ.
    cbn in Happ.
    rewrite <- app_assoc in Happ.
    symmetry. exact Happ.
  }
  rewrite Hwords.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_43 : solver_propagate_which_implies_wit_43.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 Exists (lit_neg_c candidate).
 split_pure_spatial.
 - cancel (Vecp.rep (Vecp.slot wlists_entry (lit_neg_c candidate)) destination_words_now).
 - dump_pre_spatial. constructor; auto.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_46 : solver_propagate_which_implies_wit_46.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold propagation_replacement_scan_inv in PreH1 |- *.
  destruct PreH1 as [Hrange [Hwf [Hslot [Hfalse Hprefix]]]].
  entailer!.
  - sep_apply store_char_undef_store_char.
    cancel.
  - rewrite (propagation_normalized_clause_length
      watch0 false_lit clause_contents) by lia.
    lia.
  - intros j Hj.
    destruct (Z.lt_trichotomy j offset) as [Hlt | [Heq | Hgt]].
    + apply Hprefix. lia.
    + subst j. rewrite <- PreH4.
      unfold lit_false. rewrite PreH6, PreH5.
      unfold lit_sig, lit_sign_c.
      destruct (Z.odd candidate); reflexivity.
    + lia.
Qed.
Lemma proof_of_solver_propagate_which_implies_wit_48 : solver_propagate_which_implies_wit_48.
Proof.
LLM_pre_process ltac:(lia || int_auto).
prop_apply_p (PtrArray.full_Zlength begin
    (Zlength source_words) candidate_post_memory).
  Intros_p Hcandidate_len.
  sep_apply (PtrArray.full_to_seg begin
    (Zlength source_words) candidate_post_memory).
  destruct (Z.eq_dec jj ii) as [Heq | Hneq].
  - subst jj. Left. split_pure_spatial.
    2: { split_pures; dump_pre_spatial; lia. }
    unfold propagation_ptr_segment.
    sep_apply (PtrArray.seg_split_to_seg begin 0 ii
      (Zlength source_words) candidate_post_memory ltac:(lia)).
    sep_apply (PtrArray.seg_split_to_seg begin ii (ii + 1)
      (Zlength source_words)
      (sublist (ii - 0) (Zlength source_words - 0)
        candidate_post_memory) ltac:(lia)).
    rewrite !Zsublist_Zsublist by lia.
    replace (ii - 0) with ii by lia.
    replace (ii + 1 - ii) with 1 by lia.
    replace (0 + ii) with ii by lia.
    replace (1 + ii) with (ii + 1) by lia.
    replace (Zlength source_words - ii + ii)
      with (Zlength source_words) by lia.
    rewrite sublist_single with (d := 0)
      by (rewrite Hcandidate_len; lia).
    sep_apply_l_atomic (PtrArray.seg_unfold begin ii (ii + 1) nil
      (Znth ii candidate_post_memory 0)).
    sep_apply_l_atomic (PtrArray.seg_empty begin (ii + 1) (ii + 1)).
    Intros_p Htriv.
    msat_manual_entailer_with ltac:(lia).
  - Right. split_pure_spatial.
    2: { split_pures; dump_pre_spatial; lia. }
    unfold propagation_ptr_segment.
    sep_apply (PtrArray.seg_split_to_seg begin 0 jj
      (Zlength source_words) candidate_post_memory ltac:(lia)).
    sep_apply (PtrArray.seg_split_to_seg begin jj (jj + 1)
      (Zlength source_words)
      (sublist (jj - 0) (Zlength source_words - 0)
        candidate_post_memory) ltac:(lia)).
    rewrite !Zsublist_Zsublist by lia.
    replace (jj - 0) with jj by lia.
    replace (jj + 1 - jj) with 1 by lia.
    replace (0 + jj) with jj by lia.
    replace (1 + jj) with (jj + 1) by lia.
    replace (Zlength source_words - jj + jj)
      with (Zlength source_words) by lia.
    sep_apply (PtrArray.seg_split_to_seg begin (jj + 1) ii
      (Zlength source_words)
      (sublist (jj + 1) (Zlength source_words)
        candidate_post_memory) ltac:(lia)).
    rewrite !Zsublist_Zsublist by lia.
    replace (0 + (jj + 1)) with (jj + 1) by lia.
    replace (ii - (jj + 1) + (jj + 1)) with ii by lia.
    replace (Zlength source_words - (jj + 1) + (jj + 1))
      with (Zlength source_words) by lia.
    sep_apply (PtrArray.seg_split_to_seg begin ii (ii + 1)
      (Zlength source_words)
      (sublist ii (Zlength source_words) candidate_post_memory) ltac:(lia)).
    rewrite !Zsublist_Zsublist by lia.
    replace (ii + 1 - ii) with 1 by lia.
    replace (0 + ii) with ii by lia.
    replace (1 + ii) with (ii + 1) by lia.
    replace (Zlength source_words - ii + ii)
      with (Zlength source_words) by lia.
    rewrite !sublist_single with (d := 0)
      by (rewrite Hcandidate_len; lia).
    sep_apply_l_atomic (PtrArray.seg_unfold begin jj (jj + 1) nil
      (Znth jj candidate_post_memory 0)).
    sep_apply_l_atomic (PtrArray.seg_empty begin (jj + 1) (jj + 1)).
    Intros_p Htriv1.
    sep_apply_l_atomic (PtrArray.seg_unfold begin ii (ii + 1) nil
      (Znth ii candidate_post_memory 0)).
    sep_apply_l_atomic (PtrArray.seg_empty begin (ii + 1) (ii + 1)).
    Intros_p Htriv2.
    change (sizeof (PTR)) with ptr_size_Z.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_49 : solver_propagate_which_implies_wit_49.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH1 as Henq.
  unfold enqueue_input in Henq.
  destruct Henq as (_ & _ & Ha & Hl & Hr & Ht & Hq & _).
  unfold enqueue_state_at, solver_propagation_scan_core_at, stats_propagate_scan.
  Exists rsn trl.
  repeat (split_pure_spatial || split_pures).
  - msat_cancel_sound.
    csimpl.
    cancel.
  - dump_pre_spatial. exact PreH1.
  - dump_pre_spatial. lia.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_55 : solver_propagate_which_implies_wit_55.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold solver_propagation_nonwatch_rest_at.
  Intros rsn_route trl_route.
  Exists trl_route rsn_route.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_entail_wit_1 : solver_propagate_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_propagate_open_at, stats_propagations, stats_inspects in *.
  pose proof (minisat_propagation_reuse_loop_initial__api_reentry n M0)
    as Hreuse_initial.
  Exists rsn_2 trl_2 M0.
  split_pure_spatial.
  - cancel (solver_propagate_frame s_pre M0).
    cancel.
  - split_pures; dump_pre_spatial; try assumption.
    unfold solver_propagation_loop_inv, propagation_caller_frame.
    intuition.
  all: intuition.
Qed.


Lemma proof_of_solver_propagate_entail_wit_11_10_scan_same : solver_propagate_entail_wit_11_10_scan_same.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | subst candidate_post_memory; first [reflexivity | lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_12_1_scan_move : solver_propagate_entail_wit_12_1_scan_move.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap);
    [ | subst candidate_post_memory; first [lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close 1 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_12_12_scan_move : solver_propagate_entail_wit_12_12_scan_move.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hmemory.
  bind_fact (Zlength raw_prefix = ii) as Hprefix.
  bind_fact (candidate_post_memory = watch_memory) as Hcandidate.
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words) candidate_post_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin candidate_post_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | try rewrite Hcandidate; first [lia | vec_buf_solve] .. ].
  msat_propagate_scan_step_close_nested_addr 0 clause_contents ii watch_memory scan_current
    Hmemory Hprefix Hcandidate.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_10_real_satisfied : solver_propagate_entail_wit_20_10_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_16_real_satisfied : solver_propagate_entail_wit_20_16_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_28_1 : solver_propagate_entail_wit_28_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  intros.
  subst retval_2; subst retval.
  pose proof (propagation_scan_finish_step__shared_solver_propagate_normal
    s_pre levels_entry assigns_entry M0 K A_arr F n
    i endvar p confl ws begin j Mscan watch_memory logical_words
    scan_wm
    retained moved rest garbage ii jj prop_count simp_count rsn_scan trl_scan
    wlists_entry Mentry source_words begin begin) as Hfinish.
  msat_propagate_finish_normal_close Hfinish.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_245_scan_move_pure : solver_propagate_partial_solve_wit_245_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_close_scan_first_lit_assigned.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_254_scan_move_pure : solver_propagate_partial_solve_wit_254_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite ?Z.sub_0_r in *.
  split_pures; dump_pre_spatial.
  all: try lia.
  all: try assumption.
  rewrite <- PreH2, <- PreH4, PreH3; lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_255_scan_move_pure : solver_propagate_partial_solve_wit_255_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  bind_fact ( Znth (retval_3 - 0) (mt_assigns (ms_core Mscan)) 0 = 0 + (0 - 1) ) as H_Znth.
  bind_fact ( retval_3 = lit_var_c (Znth 1 clause_contents 0) ) as H_retval_3.
  bind_fact ( retval_2 = lit_sign_c (Znth 1 clause_contents 0) ) as H_retval_2.
  rewrite Z.sub_0_r in H_Znth.
  subst retval_3 retval_2.
  split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_267_scan_same_pure : solver_propagate_partial_solve_wit_267_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_close_scan_first_lit_assigned.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_313_scan_same_pure : solver_propagate_partial_solve_wit_313_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_12 : solver_propagate_which_implies_wit_12.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (solver_shape Mscan) as Hshape.
  subst confl0.
  Exists (ms_binary Mscan).
  sep_apply_l_atomic (solver_binary_open_for_write Mscan Hshape).
  unfold clause_hdr_addr.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (first [assumption | lia])] ..]).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_35 : solver_propagate_which_implies_wit_35.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( 0 <= lit_var_c candidate ) as H_lit_var_c.
  assert (Hcandidate : 0 <= candidate).
  {
    unfold lit_var_c in H_lit_var_c.
    pose proof (Z.mod_pos_bound candidate 2 ltac:(lia)) as Hmod.
    pose proof (Z.div_mod candidate 2 ltac:(lia)) as Hdivmod.
    lia.
  }
  assert (Hcandidate_wf : lit_wf_c (ms_size Mscan) candidate).
  {
    unfold lit_wf_c.
    pose proof (lit_pack_unpack candidate Hcandidate) as Hpack.
    pose proof (lit_sign_c_range candidate) as Hsign.
    lia.
  }
  pose proof (lit_neg_c_wf (ms_size Mscan) candidate Hcandidate_wf) as Hneg_wf.
  unfold lit_wf_c in Hneg_wf.
  msat_manual_entailer_with ltac:(lia).
Qed.
