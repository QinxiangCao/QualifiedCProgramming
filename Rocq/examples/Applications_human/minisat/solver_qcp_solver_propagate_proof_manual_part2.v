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

Lemma proof_of_solver_propagate_which_implies_wit_36 : solver_propagate_which_implies_wit_36.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.



Lemma proof_of_solver_propagate_which_implies_wit_50 : solver_propagate_which_implies_wit_50.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact (minisat_propagation_reuse_scan M0 Mscan p 0 rest) as Hreuse_entry.
  bind_fact ( propagation_replacement_scan_inv n Mscan false_lit (propagation_normalized_clause watch0 false_lit
      clause_contents) (Zlength (propagation_normalized_clause watch0 false_lit clause_contents)) ) as
      H_propagation_replacement_scan_inv.
  bind_fact ( false_lit = lit_neg_c p ) as H_false_lit.
  bind_fact ( clause_lits_pointer scan_current lits ) as H_clause_lits_pointer.
  bind_fact ( real_watch_pair p clause_contents ) as H_real_watch_pair.
  bind_fact ( watch0 + false_lit = Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ) as H_watch0.
  bind_fact ( simp_count = ms_simpdb_props Mscan ) as H_simp_count.
  bind_fact ( prop_count = Znth 2 (ms_stats Mscan) 0 ) as H_prop_count.
  unfold clause_db_pair_frame, enqueue_post_at, enqueue_state_at.
  Intros is_learnt qtail' assigns' levels' reasons' trail' rsn trl.
  unfold enqueue_transition in H; cbn in H.
  destruct H as [Hsame | Hrest].
  - destruct Hsame as [_ [Hret _]]. lia.
  - destruct Hrest as [Hconflict | Hfresh].
    2: { destruct Hfresh as [_ [Hret _]]; lia. }
    destruct Hconflict as
      [Hassigned [Hnotsig [Hret
        [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]]]].
    subst conflict_ret assigns' levels' reasons' trail' qtail'.
    pose proof H_solver_propagation_scan_semantics as H_scan_arms.
    destruct H_scan_arms as [Hlive | Hdead].
    2: { destruct Hdead as [Hzero _]; lia. }
    destruct Hlive as
      [_ [Hweak [Hprop [Hheapready [Hheapcovers [Hreasonless
        [Hlevel [Hp [Hprocessed [Hfrontier Hscan]]]]]]]]]].
    unfold clause_db_pair_remainder at 1. Split.
    + Intros co pre post.
      destruct H as [Hprob [Hlits Hlearnt]].
      assert (Hdbwf : db_wf n (msolver_db Mscan)).
      { msat_propagate_project_weak_field Hweak K (@msw_db_wf)
          (@msa_db_wf). }
      assert (Hin : In (scan_current, co) (msolver_db Mscan)).
      { unfold msolver_db. apply in_or_app. left.
        rewrite Hprob. apply in_or_app. right. simpl. auto. }
      destruct (msat_propagate_unit_conflict_scan_shape n F A_arr K Mscan co
          scan_current p watch0 false_lit
          clause_contents Hweak Hdbwf Hin Hlits Hassigned Hnotsig
          H_propagation_replacement_scan_inv H_false_lit H_real_watch_pair
          H_watch0)
        as [a0 [a1 [tail [Hcontents [Hlen [Hall [Hnodup [Hnew_eq [Htail
           [Hperm [Hwatchcases [Hnew_false [Hno_reason_ptr
           Hentry_perm]]]]]]]]]]]]].
      rewrite Hcontents in Hlits. subst clause_contents.
      set (new_lits := watch0 :: false_lit :: tail).
      set (co_new := clause_obj_with_lits co new_lits).
      set (prob_route := pre ++ (scan_current, co_new) :: post).
      set (Mroute := msolver_propagation_db_wmap_update Mscan prob_route
        (ms_learnt Mscan) (ms_wm Mscan)).
      pose proof (msat_propagate_unit_conflict_prob_ready n F A_arr K Mscan co pre
        post scan_current p watch0 false_lit a0 a1 tail retained rest
        H_solver_propagation_scan_semantics
        Hdbwf Hin Hlits Hprob Hlen Hall Hnodup Hperm Hnew_false H_false_lit
        Hno_reason_ptr Hentry_perm Hwatchcases Hnew_eq) as Hready.
      pose proof (proj1 Hready) as Hupdate_normalized.
      assert (Hreuse_normalized : minisat_propagation_reuse_scan M0 Mroute p 0 rest).
      { unfold Mroute.
        eapply (minisat_propagation_reuse_normalize__api_reentry
          M0 Mscan p 0 rest scan_current a0 a1 tail watch0).
        - rewrite <- H_false_lit. exact Hupdate_normalized.
        - rewrite <- H_false_lit. exact Hwatchcases.
        - exact Hreuse_entry. }
      destruct (db_pair_lits_update_selected_owner__propagate_dbu
        _ _ _ _ _ _ _ Hupdate_normalized) as [selected [Hselected Hselected_words]].
      assert (Hselected_false : clause_false
        (assigns_pv (mt_assigns (ms_core Mroute))) (denote_obj selected)).
      { unfold denote_obj. rewrite Hselected_words, Hnew_eq.
        apply lits_denote_false_iff; [|exact Hnew_false].
        apply Forall_forall. intros word Hword.
        assert (Holdword : In word (a0 :: a1 :: tail)).
        { eapply Permutation_in; [exact Hperm|exact Hword]. }
        pose proof Hall as Hwords_wf. rewrite Forall_forall in Hwords_wf.
        specialize (Hwords_wf word Holdword). destruct Hwords_wf. lia. }
      assert (Hreuse_conflict : minisat_propagation_reuse_scan
        M0 Mroute p scan_current nil).
      { eapply minisat_propagation_reuse_resident_conflict__api_reentry;
          [exact Hreuse_normalized| |exact Hselected|exact Hselected_false].
        pose proof (db_wf_ptr_pos n (msolver_db Mscan) scan_current co Hdbwf Hin). lia. }
      Exists prob_route (ms_learnt Mscan) Mroute.
      split_pure_spatial.
      * unfold prob_route.
        lazymatch goal with
        | |- _ |-- ?T =>
            lazymatch T with
            | context C [clause_db_rep (pre ++ (scan_current, co_new) :: post)] =>
                let T' := context C [clause_db_rep pre ** clause_db_rep ((scan_current, co_new) :: post)] in
                assert (Hcut : T' |-- T)
            end
        end.
        { sep_apply (clause_db_rep_app_intro pre ((scan_current, co_new) :: post)). cancel. }
        sep_apply_r_atomic Hcut. clear Hcut.
        rewrite clause_db_rep_cons.
        rewrite Htail.
        unfold MiniSatClause.rep, co_new, clause_obj_with_lits,
          new_lits; cbn [fst snd co_learnt co_lits].
        rewrite Hlearnt.
        repeat lazymatch goal with
          | |- ?L |-- _ =>
              lazymatch L with
              | context [IntArray.seg ?x ?lo ?hi (?a :: ?l)] =>
                  sep_apply_l_atomic (IntArray.seg_unfold x lo hi l a)
              end
          end.
        do 2 (Intros; lazymatch goal with
          | |- _ |-- ?T =>
              lazymatch T with
              | context C [IntArray.seg ?x ?lo ?hi (?a :: ?l)] =>
                  lazymatch type of (IntArray.seg_unfold x lo hi l a) with
                  | _ --||-- ?U =>
                      let T' := context C [U] in
                      let Hc := fresh "Hcut" in
                      assert (Hc : T' |-- T)
                        by (Intros; split_pure_spatial;
                            [ sep_apply (proj2 (IntArray.seg_unfold x lo hi l a)); cancel
                            | dump_pre_spatial; first [assumption | tauto] ]);
                      sep_apply_r_atomic Hc; clear Hc
                  end
              end
          end).
        repeat (Intros; lazymatch goal with
          | |- _ |-- ?T =>
              lazymatch T with
              | context C [IntArray.seg ?x ?lo ?hi (?a :: ?l)] =>
                  lazymatch type of (IntArray.seg_unfold x lo hi l a) with
                  | _ --||-- ?U =>
                      let T' := context C [U] in
                      let Hc := fresh "Hcut" in
                      assert (Hc : T' |-- T)
                        by (Intros; split_pure_spatial;
                            [ sep_apply (proj2 (IntArray.seg_unfold x lo hi l a)); cancel
                            | dump_pre_spatial; first [assumption | tauto] ]);
                      sep_apply_r_atomic Hc; clear Hc
                  end
              end
          end).
        unfold clause_lits_pointer in H_clause_lits_pointer. subst lits.
        subst Mroute.
        unfold solver_propagation_nonwatch_rest_at.
        Exists rsn trl.
        rewrite (msat_propagate_unit_conflict_binary_rep Mscan prob_route
          (ms_learnt Mscan) (ms_wm Mscan)).
        rewrite (msat_propagate_unit_conflict_frame_eq s Mscan prob_route
          (ms_learnt Mscan) (ms_wm Mscan)
          (msat_propagate_unit_conflict_keys_replace pre post scan_current co
            co_new _ Hprob) eq_refl).
        unfold msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
        rewrite H_simp_count, H_prop_count.
        msat_propagate_unit_conflict_route_close Mscan Hdbwf Hin.
      * split_pures; apply derivable1s_coq_prop_r; try exact Hready; try exact Hreuse_conflict;
          cbn [Mroute msolver_propagation_db_wmap_update msolver_propagation_overlay msolver_propagation_update ]; try assumption; try reflexivity.
    + Intros co pre post.
      destruct H as [Hlearnt_split [Hlits Hlearnt]].
      assert (Hdbwf : db_wf n (msolver_db Mscan)).
      { msat_propagate_project_weak_field Hweak K (@msw_db_wf)
          (@msa_db_wf). }
      assert (Hin : In (scan_current, co) (msolver_db Mscan)).
      { unfold msolver_db. apply in_or_app. right.
        rewrite Hlearnt_split. apply in_or_app. right. simpl. auto. }
      destruct (msat_propagate_unit_conflict_scan_shape n F A_arr K Mscan co
          scan_current p watch0 false_lit
          clause_contents Hweak Hdbwf Hin Hlits Hassigned Hnotsig
          H_propagation_replacement_scan_inv H_false_lit H_real_watch_pair
          H_watch0)
        as [a0 [a1 [tail [Hcontents [Hlen [Hall [Hnodup [Hnew_eq [Htail
           [Hperm [Hwatchcases [Hnew_false [Hno_reason_ptr
           Hentry_perm]]]]]]]]]]]]].
      rewrite Hcontents in Hlits. subst clause_contents.
      set (new_lits := watch0 :: false_lit :: tail).
      set (co_new := clause_obj_with_lits co new_lits).
      set (learnt_route := pre ++ (scan_current, co_new) :: post).
      set (Mroute := msolver_propagation_db_wmap_update Mscan (ms_prob Mscan)
        learnt_route (ms_wm Mscan)).
      pose proof (msat_propagate_unit_conflict_learnt_ready n F A_arr K Mscan co
        pre post scan_current p watch0 false_lit a0 a1 tail retained rest
        H_solver_propagation_scan_semantics
        Hdbwf Hin Hlits Hlearnt_split Hlen Hall Hnodup Hperm Hnew_false
        H_false_lit Hno_reason_ptr Hentry_perm Hwatchcases Hnew_eq) as Hready.
      pose proof (proj1 Hready) as Hupdate_normalized.
      assert (Hreuse_normalized : minisat_propagation_reuse_scan M0 Mroute p 0 rest).
      { unfold Mroute.
        eapply (minisat_propagation_reuse_normalize__api_reentry
          M0 Mscan p 0 rest scan_current a0 a1 tail watch0).
        - rewrite <- H_false_lit. exact Hupdate_normalized.
        - rewrite <- H_false_lit. exact Hwatchcases.
        - exact Hreuse_entry. }
      destruct (db_pair_lits_update_selected_owner__propagate_dbu
        _ _ _ _ _ _ _ Hupdate_normalized) as [selected [Hselected Hselected_words]].
      assert (Hselected_false : clause_false
        (assigns_pv (mt_assigns (ms_core Mroute))) (denote_obj selected)).
      { unfold denote_obj. rewrite Hselected_words, Hnew_eq.
        apply lits_denote_false_iff; [|exact Hnew_false].
        apply Forall_forall. intros word Hword.
        assert (Holdword : In word (a0 :: a1 :: tail)).
        { eapply Permutation_in; [exact Hperm|exact Hword]. }
        pose proof Hall as Hwords_wf. rewrite Forall_forall in Hwords_wf.
        specialize (Hwords_wf word Holdword). destruct Hwords_wf. lia. }
      assert (Hreuse_conflict : minisat_propagation_reuse_scan
        M0 Mroute p scan_current nil).
      { eapply minisat_propagation_reuse_resident_conflict__api_reentry;
          [exact Hreuse_normalized| |exact Hselected|exact Hselected_false].
        pose proof (db_wf_ptr_pos n (msolver_db Mscan) scan_current co Hdbwf Hin). lia. }
      Exists (ms_prob Mscan) learnt_route Mroute.
      split_pure_spatial.
      * unfold learnt_route.
        lazymatch goal with
        | |- _ |-- ?T =>
            lazymatch T with
            | context C [clause_db_rep (pre ++ (scan_current, co_new) :: post)] =>
                let T' := context C [clause_db_rep pre ** clause_db_rep ((scan_current, co_new) :: post)] in
                assert (Hcut : T' |-- T)
            end
        end.
        { sep_apply (clause_db_rep_app_intro pre ((scan_current, co_new) :: post)). cancel. }
        sep_apply_r_atomic Hcut. clear Hcut.
        rewrite clause_db_rep_cons.
        rewrite Htail.
        unfold MiniSatClause.rep, co_new, clause_obj_with_lits,
          new_lits; cbn [fst snd co_learnt co_lits].
        rewrite Hlearnt.
        repeat lazymatch goal with
          | |- ?L |-- _ =>
              lazymatch L with
              | context [IntArray.seg ?x ?lo ?hi (?a :: ?l)] =>
                  sep_apply_l_atomic (IntArray.seg_unfold x lo hi l a)
              end
          end.
        do 2 (Intros; lazymatch goal with
          | |- _ |-- ?T =>
              lazymatch T with
              | context C [IntArray.seg ?x ?lo ?hi (?a :: ?l)] =>
                  lazymatch type of (IntArray.seg_unfold x lo hi l a) with
                  | _ --||-- ?U =>
                      let T' := context C [U] in
                      let Hc := fresh "Hcut" in
                      assert (Hc : T' |-- T)
                        by (Intros; split_pure_spatial;
                            [ sep_apply (proj2 (IntArray.seg_unfold x lo hi l a)); cancel
                            | dump_pre_spatial; first [assumption | tauto] ]);
                      sep_apply_r_atomic Hc; clear Hc
                  end
              end
          end).
        repeat (Intros; lazymatch goal with
          | |- _ |-- ?T =>
              lazymatch T with
              | context C [IntArray.seg ?x ?lo ?hi (?a :: ?l)] =>
                  lazymatch type of (IntArray.seg_unfold x lo hi l a) with
                  | _ --||-- ?U =>
                      let T' := context C [U] in
                      let Hc := fresh "Hcut" in
                      assert (Hc : T' |-- T)
                        by (Intros; split_pure_spatial;
                            [ sep_apply (proj2 (IntArray.seg_unfold x lo hi l a)); cancel
                            | dump_pre_spatial; first [assumption | tauto] ]);
                      sep_apply_r_atomic Hc; clear Hc
                  end
              end
          end).
        unfold clause_lits_pointer in H_clause_lits_pointer. subst lits.
        subst Mroute.
        unfold solver_propagation_nonwatch_rest_at.
        Exists rsn trl.
        rewrite (msat_propagate_unit_conflict_binary_rep Mscan (ms_prob Mscan)
          learnt_route (ms_wm Mscan)).
        rewrite (msat_propagate_unit_conflict_frame_eq s Mscan (ms_prob Mscan)
          learnt_route (ms_wm Mscan) eq_refl
          (msat_propagate_unit_conflict_keys_replace pre post scan_current co
            co_new _ Hlearnt_split)).
        unfold msolver_propagation_db_wmap_update,
          msolver_propagation_overlay, msolver_propagation_update; cbn -[ptr_size_Z].
        rewrite H_simp_count, H_prop_count.
        msat_propagate_unit_conflict_route_close Mscan Hdbwf Hin.
      * split_pures; apply derivable1s_coq_prop_r; try exact Hready; try exact Hreuse_conflict;
          cbn [Mroute msolver_propagation_db_wmap_update msolver_propagation_overlay msolver_propagation_update ]; try assumption; try reflexivity.
Qed.


Lemma proof_of_solver_propagate_entail_wit_2_2 : solver_propagate_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_propagate_scan_begin trl rsn retval_4.
Qed.



Lemma proof_of_solver_propagate_entail_wit_6_2_scan_same : solver_propagate_entail_wit_6_2_scan_same.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hmsc : msolver_propagation_scan_begin Mentry (ms_simpdb_props Mscan)
      (stats_propagations (ms_stats Mscan)) = Mscan)
    by (rewrite <- PreH54, <- PreH55; symmetry; exact PreH53).
  rewrite Hmsc.
  assert (Hlen_tecm : Zlength tagged_enqueue_conflict_memory = Zlength source_words)
    by (rewrite PreH6, PreH14, !Zlength_replace_Znth; exact PreH46).
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words)
    tagged_enqueue_conflict_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin tagged_enqueue_conflict_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | first [lia | assumption] .. ].
  unfold stats_propagations, stats_inspects in *.
  lazymatch goal with
  | Hrv : retval_2 = tag_lit _ |- _ => repeat rewrite replace_Znth_Znth in Hrv
  end;
  subst retval_2;
  subst retval_3;
  subst retval_4;
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
    Hretval6 : retval_6 = lit_neg_c ?lp |- _ =>
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
        cancel;
        Exists (clause_lits_addr (ms_binary Mscan));
        rewrite Hretval6;
        lazymatch goal with
        | Hptr : ?returned = clause_lits_addr (ms_binary Mscan) |- _ => subst returned
        end;
        rewrite ?Z.mul_0_l, ?Z.mul_1_l, ?Z.add_0_r;
        split_pure_spatial;
        [ msat_cancel_sound;
          lazymatch goal with
          | |- ?A |-- ?B => unify A B; change (A |-- A)
          end;
          cancel
        | split_pures; dump_pre_spatial; try solve [auto | int_auto];
          [ unfold propagation_binary_conflict_scan_ready;
            split; [assumption|];
            split; [exact Hheap_covers|];
            split; [exact Hreasonless|];
            split; [exact Hcurrent_level|];
            split; [assumption|];
            split; [assumption|];
            lia
          | rewrite Hupdate; rewrite replace_Znth_Znth; exact Htag
          | rewrite Hupdate; rewrite replace_Znth_Znth; reflexivity ] ]
      | destruct Hconflict as [Hnonzero _];
        exfalso; apply Hnonzero; reflexivity ]
  end.
Qed.



Lemma proof_of_solver_propagate_entail_wit_13_scan_same : solver_propagate_entail_wit_13_scan_same.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( candidate = Znth (offset - 2) (sublist 2 (Zlength clause_contents) clause_contents) 0 ) as H_candidate.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact ( propagation_replacement_scan_inv n Mscan false_lit (propagation_normalized_clause watch0 false_lit
      clause_contents) offset ) as H_propagation_replacement_scan_inv.
  assert (Hcandidate' : candidate =
      Znth offset (propagation_normalized_clause watch0 false_lit clause_contents) 0) by
      (rewrite H_candidate; unfold propagation_normalized_clause;
      rewrite Znth_cons by lia;
      rewrite Znth_cons by lia;
      replace (offset - 1 - 1) with (offset - 2) by lia; reflexivity).
  assert (Hrange : 0 <= lit_var_c candidate < ms_size Mscan).
  { destruct H_propagation_replacement_scan_inv as [_ [Hwf _]].
    assert (Hcand : lit_wf_c n candidate) by
      (rewrite Hcandidate'; apply (Forall_Znth_elim Z (lit_wf_c n)
        (propagation_normalized_clause watch0 false_lit clause_contents) 0 offset Hwf);
      unfold propagation_normalized_clause;
      rewrite !Zlength_cons;
      rewrite Zlength_sublist by lia;
      lia).
    unfold solver_propagation_scan_semantics in H_solver_propagation_scan_semantics.
    destruct H_solver_propagation_scan_semantics as [[_ [Hweak _]] | [Hconf _]]; [|lia].
    pose proof (solver_propagation_weak_reason_core n F A_arr K Mscan Hweak) as [Hsize _].
    pose proof (lit_var_c_in_range n candidate Hcand) as Hvar.
    lia. }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [assumption | reflexivity | lia].
Qed.


Lemma proof_of_solver_propagate_entail_wit_14_scan_same : solver_propagate_entail_wit_14_scan_same.
Proof.
  LLM_pre_process ltac:(idtac).
  Intros.
  pose proof (IntArray.missing_i_merge_to_seg lits 2 offset_2
    (Zlength clause_contents) candidate
    (sublist 2 (Zlength clause_contents) clause_contents) ltac:(lia)) as Hmerge.
  unfold propagation_int_missing.
  sep_apply Hmerge.
  rewrite PreH9, replace_Znth_Znth.
  Exists (offset_2 + 1) watch0_2.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_entail_wit_15_1_unit_conflict_copy : solver_propagate_entail_wit_15_1_unit_conflict_copy.
Proof.
  LLM_pre_process ltac:(lia).
  msat_propagate_unit_conflict_copy_close jj.
Qed.


Lemma proof_of_solver_propagate_entail_wit_15_2_unit_conflict_copy : solver_propagate_entail_wit_15_2_unit_conflict_copy.
Proof.
  LLM_pre_process ltac:(lia).
  msat_propagate_unit_conflict_copy_close jj.
Qed.



Lemma proof_of_solver_propagate_entail_wit_18_2_unit_move : solver_propagate_entail_wit_18_2_unit_move.
Proof.
Abort.


Lemma proof_of_solver_propagate_entail_wit_20_11_real_satisfied : solver_propagate_entail_wit_20_11_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_27_2 : solver_propagate_entail_wit_27_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Right.
  Exists trl_scan_2 rsn_scan_2 simp_count_2 prop_count_2 scan_wm_2 logical_words_2 source_words_2 moved_2 garbage_2 watch_memory_2 ii_2 jj_2 retained_2 rest_2 Mentry_2.
  Exists Mscan_2.
  msat_manual_entailer_with lia.
Qed.



Lemma proof_of_solver_propagate_entail_wit_27_4_binary_conflict : solver_propagate_entail_wit_27_4_binary_conflict.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( lvl_next = levels_entry ) as H_lvl_next.
  Right.
  Exists trl_next rsn_next simp_count_next prop_count_next next_wm logical_next source_words_next moved_next garbage_next memory_next ii_next jj_next retained_next rest_next Mentry_next.
  Exists Mnext.
  msat_propagate_binary_keep_close H_lvl_next.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_14_pure : solver_propagate_partial_solve_wit_14_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  assert (HS : sizeof(PTR) > 0) by (change (sizeof (PTR)) with ptr_size_Z; solve_arch).
  assert (Hii : ii < Zlength source_words) by nia.
  msat_manual_entailer_with lia.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_91_binary_keep_pure : solver_propagate_partial_solve_wit_91_binary_keep_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hw : 0 <= ii < Zlength watch_memory) by lia.
  assert (Hsc : Znth ii watch_memory 0 = scan_current).
  { rewrite PreH18, app_Znth2 by lia.
    replace (ii - Zlength raw_prefix) with 0 by lia. reflexivity. }
  assert (HX : Znth ii (replace_Znth jj scan_current watch_memory) 0 = scan_current).
  { rewrite Znth_replace_Znth_Diff by lia. exact Hsc. }
  assert (Hw2 : 0 <= ii < Zlength (replace_Znth jj scan_current watch_memory))
    by (rewrite Zlength_replace_Znth; lia).
  rewrite <- PreH18.
  rewrite PreH19, HX.
  split_pures; dump_pre_spatial; lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_247_scan_same_pure : solver_propagate_partial_solve_wit_247_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_close_scan_first_lit_assigned.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_253_scan_move_pure : solver_propagate_partial_solve_wit_253_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_close_scan_first_lit_assigned.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_302_scan_same_pure : solver_propagate_partial_solve_wit_302_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_27 : solver_propagate_which_implies_wit_27.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
      H_solver_propagation_scan_semantics.
  bind_fact (minisat_propagation_reuse_scan M0 Mscan p 0 rest) as Hreuse_entry.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
      H_propagation_watch_scan_physical.
  bind_fact ( clause_lits_pointer scan_current lits ) as H_clause_lits_pointer.
  bind_fact ( 3 <= Zlength clause_contents ) as H_Zlength.
  bind_fact ( real_watch_pair p clause_contents ) as H_real_watch_pair.
  bind_fact ( false_lit = lit_neg_c p ) as H_false_lit.
  bind_fact ( watch0_2 + false_lit = Znth 0 clause_contents 0 + Znth 1 clause_contents 0 ) as H_watch0_2.
  bind_fact ( sig = 1 - 2 * lit_sign_c watch0_2 ) as H_sig.
  bind_fact ( Znth (lit_var_c watch0_2) (mt_assigns (ms_core Mscan)) 0 = sig ) as H_Znth.
  destruct H_solver_propagation_scan_semantics as [Hlive | Hdead].
  2: { destruct Hdead as [Hnz _]; lia. }
  destruct Hlive as [_ [Hweak [Hprop [Hheapready [Hheapcovers
    [Hreasonless [Hlevel [Hp [Hprocessed [Hfrontier Hscan]]]]]]]]]].
  rewrite H_rest in Hscan, Hreuse_entry.
  assert (Htrail_wf : mtrail_wf n (ms_core Mscan)).
  { destruct (solver_propagation_weak_core_facts__propagate n F A_arr K Mscan Hweak)
      as (_ & _ & _ & _ & Htrail). exact Htrail. }
  pose proof (level_of_msolver_view_levels__analyze n Mscan (lit_var_c p)
    (Zlength (mt_lim (ms_core Mscan))) Htrail_wf Hlevel) as Hfocus_cell.
  assert (Hother_true : lit_true (mt_assigns (ms_core Mscan)) watch0_2).
  { unfold lit_true. rewrite H_Znth, H_sig.
    unfold lit_sig, lit_sign_c. destruct (Z.odd watch0_2); reflexivity. }
  assert (Hdbwf : db_wf n (msolver_db Mscan))
    by (destruct (solver_propagation_weak_core_facts__propagate
          n F A_arr K Mscan Hweak) as [_ [_ [Hdb _]]]; exact Hdb).
  destruct (msat_propagate_scan_keep_step source_words retained moved rest
    garbage watch_memory ii jj scan_current raw_suffix
    H_propagation_watch_scan_physical H_rest) as [garbage_route Hkeep].
  unfold clause_db_pair_frame. Intros is_learnt.
  unfold clause_db_pair_remainder. Split.
  - Intros co pre post.
    destruct H as [Hprob [Hlits Hlearnt]].
    assert (Hin : In (scan_current, co) (msolver_db Mscan)).
    { unfold msolver_db. apply in_or_app. left. rewrite Hprob.
      apply in_or_app. right. simpl. auto. }
    pose proof (db_wf_obj n (msolver_db Mscan) scan_current co Hdbwf Hin)
      as Hobj.
    unfold obj_wf in Hobj. rewrite Hlits in Hobj.
    destruct Hobj as [Hlen _].
    destruct clause_contents as [|a0 tail0]; cbn in Hlen; [lia|].
    destruct tail0 as [|a1 tail]; cbn in Hlen; [lia|].
    assert (Htail : sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail)
      = tail) by (apply msat_sublist_two_tail).
    set (new_lits := propagation_normalized_clause watch0_2 false_lit
      (a0 :: a1 :: tail)).
    set (co_new := clause_obj_with_lits co new_lits).
    set (prob_route := pre ++ (scan_current, co_new) :: post).
    set (learnt_route := ms_learnt Mscan).
    set (Mroute := msolver_propagation_db_wmap_update Mscan prob_route
      learnt_route (ms_wm Mscan)).
    assert (Hupdate : db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan)
        scan_current (a0 :: a1 :: tail) new_lits prob_route learnt_route).
    { left. exists co, pre, post. repeat split; try assumption;
        try reflexivity. }
    assert (Hdb : msolver_db Mscan =
        pre ++ (scan_current, co) :: (post ++ ms_learnt Mscan)).
    { unfold msolver_db. rewrite Hprob, <- app_assoc. reflexivity. }
    assert (Hdb2 : prob_route ++ learnt_route =
        pre ++ (scan_current, co_new) :: (post ++ ms_learnt Mscan)).
    { unfold prob_route, learnt_route. rewrite <- app_assoc. reflexivity. }
    destruct (msat_propagate_clause_watch_facts n Mscan p scan_current co
      a0 a1 tail new_lits co_new false_lit watch0_2 sig Hdbwf Hin Hlits
      H_Zlength H_real_watch_pair H_watch0_2 H_false_lit H_sig H_Znth Hp
      Hprocessed ltac:(reflexivity) ltac:(reflexivity)) as
      [Hperm [Hentryold [Hentrynew [Honewsafe
        [Hentryperm [Hswap Hhead]]]]]].
    pose proof (msat_propagate_route_facts n F A_arr K Mscan Mroute p
      scan_current co co_new a0 a1 tail new_lits prob_route learnt_route
      pre (post ++ ms_learnt Mscan) retained raw_suffix Hdb Hdb2 Hupdate
      ltac:(reflexivity) Hdbwf Hin Hperm Hentryold Hentrynew Honewsafe
      Hentryperm Hswap Hhead Hweak Hprop Hheapready Hheapcovers Hreasonless
      Hlevel Hp Hprocessed Hfrontier Hscan) as Htransition.
    assert (Hcases : (a0 = lit_neg_c p /\ watch0_2 = a1) \/
      (a1 = lit_neg_c p /\ watch0_2 = a0)).
    { pose proof H_real_watch_pair as Hpair. pose proof H_watch0_2 as Hsum.
      change (a0 = lit_neg_c p \/ a1 = lit_neg_c p) in Hpair.
      change (watch0_2 + false_lit = a0 + a1) in Hsum.
      rewrite H_false_lit in Hsum. destruct Hpair; [left|right]; split; lia. }
    assert (Hreal : is_tag scan_current = false).
    { apply even_not_tag. exact (db_wf_even n (msolver_db Mscan) scan_current co Hdbwf Hin). }
    assert (Hdbnew : db_wf n (prob_route ++ learnt_route)).
    { pose proof (proj2 Htransition) as Hsem_new.
      destruct Hsem_new as [Hlive_new|[Hnonzero _]]; [|contradiction].
      destruct Hlive_new as (_ & Hweak_new & _).
      destruct (solver_propagation_weak_core_facts__propagate n F A_arr K Mroute Hweak_new)
        as (_ & _ & Hdb_new & _). exact Hdb_new. }
    assert (Hreuse_next : minisat_propagation_reuse_scan M0 Mroute p 0 raw_suffix).
    { unfold Mroute.
      eapply minisat_propagation_reuse_real_satisfied__api_reentry;
        [exact Hdbnew|exact Htrail_wf| |exact Hcases|exact Hreal|
         exact Hfocus_cell|exact Hother_true|exact Hreuse_entry].
      unfold new_lits in Hupdate. rewrite H_false_lit in Hupdate. exact Hupdate. }
    Exists garbage_route (replace_Znth jj scan_current watch_memory)
      Mroute raw_suffix (retained ++ scan_current :: nil) watch0_2
      prob_route learnt_route.
    split_pure_spatial.
    + unfold prob_route.
      msat_propagate_db_entry_spatial pre post scan_current co_new
        new_lits Htail Hlearnt H_clause_lits_pointer lits tail.
    + split_pures; apply derivable1s_coq_prop_r;
        try exact Hupdate; try exact Htransition; try exact Hkeep; try exact Hreuse_next;
        try reflexivity.
  - Intros co pre post.
    destruct H as [Hlearntsplit [Hlits Hcolearnt]].
    assert (Hin : In (scan_current, co) (msolver_db Mscan)).
    { unfold msolver_db. apply in_or_app. right. rewrite Hlearntsplit.
      apply in_or_app. right. simpl. auto. }
    pose proof (db_wf_obj n (msolver_db Mscan) scan_current co Hdbwf Hin)
      as Hobj.
    unfold obj_wf in Hobj. rewrite Hlits in Hobj.
    destruct Hobj as [Hlen _].
    destruct clause_contents as [|a0 tail0]; cbn in Hlen; [lia|].
    destruct tail0 as [|a1 tail]; cbn in Hlen; [lia|].
    assert (Htail : sublist 2 (Zlength (a0 :: a1 :: tail)) (a0 :: a1 :: tail)
      = tail) by (apply msat_sublist_two_tail).
    set (new_lits := propagation_normalized_clause watch0_2 false_lit
      (a0 :: a1 :: tail)).
    set (co_new := clause_obj_with_lits co new_lits).
    set (prob_route := ms_prob Mscan).
    set (learnt_route := pre ++ (scan_current, co_new) :: post).
    set (Mroute := msolver_propagation_db_wmap_update Mscan prob_route
      learnt_route (ms_wm Mscan)).
    assert (Hupdate : db_pair_lits_update (ms_prob Mscan) (ms_learnt Mscan)
        scan_current (a0 :: a1 :: tail) new_lits prob_route learnt_route).
    { right. exists co, pre, post. repeat split; try assumption;
        try reflexivity. }
    assert (Hdb : msolver_db Mscan =
        (ms_prob Mscan ++ pre) ++ (scan_current, co) :: post).
    { unfold msolver_db. rewrite Hlearntsplit, app_assoc. reflexivity. }
    assert (Hdb2 : prob_route ++ learnt_route =
        (ms_prob Mscan ++ pre) ++ (scan_current, co_new) :: post).
    { unfold prob_route, learnt_route. rewrite app_assoc. reflexivity. }
    destruct (msat_propagate_clause_watch_facts n Mscan p scan_current co
      a0 a1 tail new_lits co_new false_lit watch0_2 sig Hdbwf Hin Hlits
      H_Zlength H_real_watch_pair H_watch0_2 H_false_lit H_sig H_Znth Hp
      Hprocessed ltac:(reflexivity) ltac:(reflexivity)) as
      [Hperm [Hentryold [Hentrynew [Honewsafe
        [Hentryperm [Hswap Hhead]]]]]].
    pose proof (msat_propagate_route_facts n F A_arr K Mscan Mroute p
      scan_current co co_new a0 a1 tail new_lits prob_route learnt_route
      (ms_prob Mscan ++ pre) post retained raw_suffix Hdb Hdb2 Hupdate
      ltac:(reflexivity) Hdbwf Hin Hperm Hentryold Hentrynew Honewsafe
      Hentryperm Hswap Hhead Hweak Hprop Hheapready Hheapcovers Hreasonless
      Hlevel Hp Hprocessed Hfrontier Hscan) as Htransition.
    assert (Hcases : (a0 = lit_neg_c p /\ watch0_2 = a1) \/
      (a1 = lit_neg_c p /\ watch0_2 = a0)).
    { pose proof H_real_watch_pair as Hpair. pose proof H_watch0_2 as Hsum.
      change (a0 = lit_neg_c p \/ a1 = lit_neg_c p) in Hpair.
      change (watch0_2 + false_lit = a0 + a1) in Hsum.
      rewrite H_false_lit in Hsum. destruct Hpair; [left|right]; split; lia. }
    assert (Hreal : is_tag scan_current = false).
    { apply even_not_tag. exact (db_wf_even n (msolver_db Mscan) scan_current co Hdbwf Hin). }
    assert (Hdbnew : db_wf n (prob_route ++ learnt_route)).
    { pose proof (proj2 Htransition) as Hsem_new.
      destruct Hsem_new as [Hlive_new|[Hnonzero _]]; [|contradiction].
      destruct Hlive_new as (_ & Hweak_new & _).
      destruct (solver_propagation_weak_core_facts__propagate n F A_arr K Mroute Hweak_new)
        as (_ & _ & Hdb_new & _). exact Hdb_new. }
    assert (Hreuse_next : minisat_propagation_reuse_scan M0 Mroute p 0 raw_suffix).
    { unfold Mroute.
      eapply minisat_propagation_reuse_real_satisfied__api_reentry;
        [exact Hdbnew|exact Htrail_wf| |exact Hcases|exact Hreal|
         exact Hfocus_cell|exact Hother_true|exact Hreuse_entry].
      unfold new_lits in Hupdate. rewrite H_false_lit in Hupdate. exact Hupdate. }
    Exists garbage_route (replace_Znth jj scan_current watch_memory)
      Mroute raw_suffix (retained ++ scan_current :: nil) watch0_2
      prob_route learnt_route.
    split_pure_spatial.
    + unfold learnt_route.
      msat_propagate_db_entry_spatial pre post scan_current co_new
        new_lits Htail Hcolearnt H_clause_lits_pointer lits tail.
    + split_pures; apply derivable1s_coq_prop_r;
        try exact Hupdate; try exact Htransition; try exact Hkeep; try exact Hreuse_next;
        try reflexivity.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_59 : solver_propagate_which_implies_wit_59.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH8 as Hph.
  unfold propagation_watch_scan_physical in Hph.
  destruct Hph as [Hinv [Hmem [Hkept [Hprefix Hmemlen]]]].
  assert (HS : sizeof(PTR) > 0) by (change (sizeof (PTR)) with ptr_size_Z; solve_arch).
  assert (Hii_ge : ii >= Zlength source_words).
  { subst i endvar.
    destruct (Z_lt_ge_dec ii (Zlength source_words)) as [Hlt | Hge]; [|exact Hge].
    exfalso. assert (ii * sizeof(PTR) < Zlength source_words * sizeof(PTR)) by nia. lia. }
  assert (Hrest_len : Zlength rest = 0).
  { rewrite Hmem in Hmemlen. rewrite app_assoc, Zlength_app in Hmemlen.
    pose proof (Zlength_nonneg rest). lia. }
  assert (Hrest : rest = nil).
  { destruct rest as [|x rest']; [reflexivity|].
    rewrite Zlength_cons in Hrest_len. pose proof (Zlength_nonneg rest'). lia. }
  subst rest.
  assert (Hii : ii = Zlength source_words).
  { rewrite app_nil_r in Hmem. rewrite Hmem in Hmemlen. lia. }
  rewrite app_nil_r in PreH9.
  subst logical_words.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [auto | lia | subst; lia].
Qed.



Lemma proof_of_solver_propagate_entail_wit_9_2_scan_move : solver_propagate_entail_wit_9_2_scan_move.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
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
  pose proof (ms_binary_watch_copy_step__common
    watch_memory raw_prefix scan_current raw_suffix
    ii jj copy_src_2 copy_dst_2 copy_memory_2
    H_binary_watch_copy_progress Hcursor_words) as Hprogress_next.
  bind_fact (Zlength copy_memory_2 = Zlength source_words) as Hcopy_len.
  sep_apply PtrArray.full_to_seg.
  sep_apply (PtrArray.seg_merge_to_full begin 0
    (copy_dst_2 + 1) (copy_src_2 + 1)); try lia.
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (copy_src_2 + 1 - 0) with (copy_src_2 + 1) by lia.
  sep_apply PtrArray.full_to_seg.
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  sep_apply (PtrArray.seg_merge_to_full begin 0
    (copy_src_2 + 1) (Zlength source_words)); try lia.
  rewrite ?Z.mul_0_l, ?Z.add_0_r.
  replace (Zlength source_words - 0) with (Zlength source_words) by lia.
  set (newmem := replace_Znth copy_dst_2 (Znth copy_src_2 copy_memory_2 0) copy_memory_2).
  assert (Hnewlen : Zlength newmem = Zlength source_words)
    by (subst newmem; rewrite Zlength_replace_Znth; lia).
  lazymatch goal with
  | |- context [PtrArray.full begin (Zlength source_words) ?LL] =>
      assert (Heq : LL = newmem)
  end.
  { subst newmem.
    rewrite (replace_Znth_split copy_dst_2 (Znth copy_src_2 copy_memory_2 0) copy_memory_2) by lia.
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
    simpl.
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
    reflexivity. }
  rewrite Heq.
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words) newmem).
  sep_apply (Vecp.rep_ptr_intro ws begin newmem cap); [ | first [lia | vec_buf_solve] .. ].
  Exists newmem (copy_dst_2 + 1) (copy_src_2 + 1)
         scratch_lits_2 scratch_base_2.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.



Lemma proof_of_solver_propagate_entail_wit_11_8_scan_same : solver_propagate_entail_wit_11_8_scan_same.
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



Lemma proof_of_solver_propagate_entail_wit_12_5_scan_move : solver_propagate_entail_wit_12_5_scan_move.
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



Lemma proof_of_solver_propagate_entail_wit_12_9_scan_move : solver_propagate_entail_wit_12_9_scan_move.
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



Lemma proof_of_solver_propagate_entail_wit_20_12_real_satisfied : solver_propagate_entail_wit_20_12_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_17_real_satisfied : solver_propagate_entail_wit_20_17_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_23_real_satisfied : solver_propagate_entail_wit_20_23_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_28_2 : solver_propagate_entail_wit_28_2.
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



Lemma proof_of_solver_propagate_entail_wit_29_2 : solver_propagate_entail_wit_29_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold solver_propagate_open_at, stats_propagations, stats_inspects in *.
  msat_propagate_finish_frame lvl_finish levels_entry trl_finish rsn_finish Mfinish.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_85_binary_keep_pure : solver_propagate_partial_solve_wit_85_binary_keep_pure.
Proof.
Abort.


Lemma proof_of_solver_propagate_partial_solve_wit_89_binary_keep_pure : solver_propagate_partial_solve_wit_89_binary_keep_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  try subst retval.
  try match goal with H : tagged_memory = replace_Znth _ _ _ |- _ =>
    assert (Htlen : Zlength tagged_memory = Zlength watch_memory)
      by (rewrite H; apply Zlength_replace_Znth); rewrite <- H end.
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  split_pures; dump_pre_spatial.
  all: try lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_95_binary_keep_pure : solver_propagate_partial_solve_wit_95_binary_keep_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold stats_propagations, stats_inspects.
  msat_propagation_keep_scan_key ltac:((dump_pre_spatial; try assumption)).
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_301_scan_same_pure : solver_propagate_partial_solve_wit_301_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_315_scan_move_pure : solver_propagate_partial_solve_wit_315_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_3 : solver_propagate_which_implies_wit_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
bind_fact ( solver_propagation_inv n F A_arr K M0 ) as H_solver_propagation_inv.
  bind_fact ( p = Znth (mt_qhead (ms_core M0)) (mt_trail (ms_core M0)) 0 ) as H_p.
  pose proof H_solver_propagation_inv as [_ Hprop].
  destruct K as [A_inst | A_proc].
  - destruct Hprop as [Hweak _ _ _ _].
    pose proof (msw_trail_wf Hweak) as Hwf.
    pose proof (msw_size Hweak) as Hn.
    pose proof (msw_shape Hweak) as Hshape.
    assert (Hidx :
      0 <= mt_qhead (ms_core M0) < Zlength (mt_trail (ms_core M0))).
    { unfold solver_shape in Hshape. lia. }
    pose proof (Forall_Znth_elim _ _ _ 0 _ (mtw_trail_lits Hwf) Hidx)
      as Hlit.
    rewrite <- H_p in Hlit.
    unfold lit_wf_c in Hlit.
    unfold solver_wlists_handle.
    (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
  - destruct Hprop as [Hweak _ _ _ _].
    pose proof (msa_trail_wf Hweak) as Hwf.
    pose proof (msa_size Hweak) as Hn.
    pose proof (msa_shape Hweak) as Hshape.
    assert (Hidx :
      0 <= mt_qhead (ms_core M0) < Zlength (mt_trail (ms_core M0))).
    { unfold solver_shape in Hshape. lia. }
    pose proof (Forall_Znth_elim _ _ _ 0 _ (mtw_trail_lits Hwf) Hidx)
      as Hlit.
    rewrite <- H_p in Hlit.
    unfold lit_wf_c in Hlit.
    unfold solver_wlists_handle.
    msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_11 : solver_propagate_which_implies_wit_11.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (replace_Znth ii (Znth ii tagged_memory 0) tagged_memory).
  msat_propagate_ptr_missing_merge begin ii source_words tagged_memory i;
    msat_manual_entailer_with ltac:(lia).
Qed.



Lemma proof_of_solver_propagate_which_implies_wit_14 : solver_propagate_which_implies_wit_14.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold clause_lits_pointer in *.
  subst confl scratch_base0.
  (Intros; split_pure_spatial; [cancel | split_pures; dump_pre_spatial; solve [auto | (lia)] ..]).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_18 : solver_propagate_which_implies_wit_18.
Proof.
LLM_pre_process ltac:(lia || int_auto).
assert (Hl : enq_l = tag_lit scan_current) by lia.
  assert (Hr : enq_reason = tag_of_lit p_v) by lia.
  subst enq_l enq_reason.
  unfold enqueue_post_at.
  Intros qtail' assigns' levels' reasons' trail'.
  assert (Hret : enq_ret = 1).
  {
    unfold enqueue_transition in H.
    destruct H as [H | [H | H]];
      decompose [and] H; lia.
  }
  subst enq_ret.
  Exists qtail' assigns' levels' reasons' trail'.
  msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_which_implies_wit_41 : solver_propagate_which_implies_wit_41.
Proof.
 LLM_pre_process ltac:(lia || int_auto).
 subst i. sep_apply_l_atomic (PtrArray.full_split_to_missing_i begin ii (Zlength source_words) candidate_post_memory 0 ltac:(lia)). unfold StorePtrAsElement.storeA. rewrite PreH4. msat_manual_entailer_with ltac:(lia).
Qed.


Lemma proof_of_solver_propagate_partial_solve_wit_13_pure : solver_propagate_partial_solve_wit_13_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsz : sizeof(PTR) = 4) by reflexivity.
  split_pures; dump_pre_spatial;
  subst i endvar; rewrite Hsz in *; lia.
Qed.
