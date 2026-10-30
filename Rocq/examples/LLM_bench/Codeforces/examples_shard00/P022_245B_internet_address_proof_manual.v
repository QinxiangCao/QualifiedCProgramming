From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P022_245B_internet_address_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P022_245B_internet_address_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P022_245B_internet_address_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  unfold string_length.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold valid_string, all_ascii, no_inner_nul.
  split; intros i Hi; specialize (PreH3 i Hi); lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval.
  pose proof PreH5 as Hstructure.
  unfold Pre in Hstructure.
  destruct Hstructure as [_ [_ [address Hrestored]]].
  unfold RestoredInternetAddress in Hrestored.
  destruct Hrestored as
      [protocol [domain [context
        [Hprotocol [Hdomain [_ [Hplain _]]]]]]].
  destruct Hdomain as [Hdomain _].
  destruct Hprotocol as [Hprotocol | Hprotocol]; subst protocol; subst plain.
  - assert (Hprefix :
        sublist 0 4
          ((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++
           domain ++ (cons 114 (cons 117 (@nil Z))) ++ context) =
        (cons 104 (cons 116 (cons 116 (cons 112 (@nil Z)))))).
    {
      simpl. reflexivity.
    }
    assert (Hmarker :
        Znth (4 + Zlength domain)
          ((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++
           domain ++ (cons 114 (cons 117 (@nil Z))) ++ context) 0 =
        114).
    {
      replace (4 + Zlength domain)
        with (Zlength
          ((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++ domain))
        by (rewrite Zlength_app; repeat rewrite Zlength_cons; rewrite Zlength_nil; lia).
      replace
        ((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++
         domain ++ (cons 114 (cons 117 (@nil Z))) ++ context)
        with
        (((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++ domain) ++
         cons 114 (cons 117 context))
        by (rewrite app_assoc; reflexivity).
      unfold Znth.
      rewrite app_nth2.
      + rewrite Zlength_correct, Nat2Z.id.
        rewrite Nat.sub_diag.
        reflexivity.
      + rewrite Zlength_correct, Nat2Z.id. lia.
    }
    assert (Hmarker_next :
        Znth (4 + Zlength domain + 1)
          ((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++
           domain ++ (cons 114 (cons 117 (@nil Z))) ++ context) 0 =
        117).
    {
      replace (4 + Zlength domain + 1)
        with (Zlength
          (((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++ domain) ++
           (cons 114 (@nil Z))))
        by (repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
            repeat rewrite Zlength_nil; lia).
      replace
        ((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++
         domain ++ (cons 114 (cons 117 (@nil Z))) ++ context)
        with
        ((((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++ domain) ++
          (cons 114 (@nil Z))) ++ cons 117 context)
        by (
          transitivity
            (((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++
              domain) ++ cons 114 (cons 117 context));
          [ exact (eq_sym
              (app_assoc
                ((cons 104 (cons 116 (cons 116 (cons 112 (@nil Z))))) ++
                 domain)
                (cons 114 (@nil Z)) (cons 117 context)))
          | exact (eq_sym
              (app_assoc
                (cons 104 (cons 116 (cons 116 (cons 112 (@nil Z)))))
                domain (cons 114 (cons 117 context)))) ]).
      unfold Znth.
      rewrite app_nth2.
      + rewrite Zlength_correct, Nat2Z.id.
        rewrite Nat.sub_diag.
        reflexivity.
      + rewrite Zlength_correct, Nat2Z.id. lia.
    }
    pose proof (Zlength_nonneg context) as Hcontext_nonneg.
    Exists (4 + Zlength domain).
    split_pure_spatial.
    + unfold store_string, string_length, c_string.
      cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: try reflexivity.
      all: try unfold string_length.
      all: try (repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
        repeat rewrite Zlength_nil; lia).
  - unfold c_string, Znth in PreH1.
    simpl in PreH1.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval.
  pose proof PreH5 as Hstructure.
  unfold Pre in Hstructure.
  destruct Hstructure as [_ [_ [address Hrestored]]].
  unfold RestoredInternetAddress in Hrestored.
  destruct Hrestored as
      [protocol [domain [context
        [Hprotocol [Hdomain [_ [Hplain _]]]]]]].
  destruct Hdomain as [Hdomain _].
  destruct Hprotocol as [Hprotocol | Hprotocol]; subst protocol; subst plain.
  - unfold c_string, Znth in PreH1.
    simpl in PreH1.
    contradiction.
  - assert (Hprefix :
        sublist 0 3
          ((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain ++
           (cons 114 (cons 117 (@nil Z))) ++ context) =
        (cons 102 (cons 116 (cons 112 (@nil Z))))).
    {
      change
        (sublist 0 (Zlength (cons 102 (cons 116 (cons 112 (@nil Z)))))
           ((cons 102 (cons 116 (cons 112 (@nil Z)))) ++
            (domain ++ (cons 114 (cons 117 (@nil Z))) ++ context)) =
         (cons 102 (cons 116 (cons 112 (@nil Z))))).
      apply sublist_app_exact1.
    }
    assert (Hmarker :
        Znth (3 + Zlength domain)
          ((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain ++
           (cons 114 (cons 117 (@nil Z))) ++ context) 0 = 114).
    {
      replace (3 + Zlength domain)
        with (Zlength ((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain))
        by (rewrite Zlength_app; repeat rewrite Zlength_cons; rewrite Zlength_nil; lia).
      replace
        ((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain ++
         (cons 114 (cons 117 (@nil Z))) ++ context)
        with (((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain) ++
              cons 114 (cons 117 context))
        by (rewrite app_assoc; reflexivity).
      unfold Znth.
      rewrite app_nth2.
      + rewrite Zlength_correct, Nat2Z.id.
        rewrite Nat.sub_diag.
        reflexivity.
      + rewrite Zlength_correct, Nat2Z.id. lia.
    }
    assert (Hmarker_next :
        Znth (3 + Zlength domain + 1)
          ((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain ++
           (cons 114 (cons 117 (@nil Z))) ++ context) 0 = 117).
    {
      replace (3 + Zlength domain + 1)
        with (Zlength
          (((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain) ++
           (cons 114 (@nil Z))))
        by (repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
            repeat rewrite Zlength_nil; lia).
      replace
        ((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain ++
         (cons 114 (cons 117 (@nil Z))) ++ context)
        with ((((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain) ++
               (cons 114 (@nil Z))) ++ cons 117 context)
        by (
          transitivity
            (((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain) ++
             cons 114 (cons 117 context));
          [ exact (eq_sym
              (app_assoc
                ((cons 102 (cons 116 (cons 112 (@nil Z)))) ++ domain)
                (cons 114 (@nil Z)) (cons 117 context)))
          | exact (eq_sym
              (app_assoc
                (cons 102 (cons 116 (cons 112 (@nil Z))))
                domain (cons 114 (cons 117 context)))) ]).
      unfold Znth.
      rewrite app_nth2.
      + rewrite Zlength_correct, Nat2Z.id.
        rewrite Nat.sub_diag.
        reflexivity.
      + rewrite Zlength_correct, Nat2Z.id. lia.
    }
    pose proof (Zlength_nonneg context) as Hcontext_nonneg.
    Exists (3 + Zlength domain).
    split_pure_spatial.
    + unfold store_string, string_length, c_string.
      cancel.
    + split_pures.
      all: dump_pre_spatial.
      all: try assumption.
      all: try reflexivity.
      all: try unfold string_length.
      all: try (repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
        repeat rewrite Zlength_nil; lia).
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_1 : solver_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 in PreH1 by lia.
  exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_3_1_split_goal_2 : solver_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 in PreH2 by lia.
  exact PreH2.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_1 : solver_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 in PreH1 by lia.
  exact PreH1.
Qed.

Lemma proof_of_solver_entail_wit_3_2_split_goal_2 : solver_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 in PreH2 by lia.
  exact PreH2.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n; subst p; subst ru; subst k.
  rewrite app_Znth1 in PreH1 by lia.
  assert (i <> marker_2) by (intros Heq; subst marker_2; contradiction).
  Exists marker_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; (lia || assumption).
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n; subst p; subst ru; subst k.
  rewrite app_Znth1 in PreH1 by lia.
  assert (i <> marker_2) by (intros Heq; subst marker_2; contradiction).
  Exists marker_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; (lia || assumption).
Qed.

Lemma proof_of_solver_entail_wit_4_3 : solver_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n; subst p; subst ru; subst k.
  rewrite app_Znth1 in PreH1 by lia.
  assert (i <> marker_2) by (intros Heq; subst marker_2; contradiction).
  Exists marker_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; (lia || assumption).
Qed.

Lemma proof_of_solver_entail_wit_4_4 : solver_entail_wit_4_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst n; subst p; subst ru; subst k.
  rewrite app_Znth1 in PreH1 by lia.
  assert (i <> marker_2) by (intros Heq; subst marker_2; contradiction).
  Exists marker_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; (lia || assumption).
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_spatial : solver_entail_wit_5_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k.
  rewrite Zsublist_nil by lia.
  rewrite CharArray.seg_empty.
  split_pure_spatial.
  - sep_apply CharArray.undef_full_to_undef_seg.
    cancel.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_1_split_goal_spatial.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_spatial : solver_entail_wit_5_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k.
  rewrite Zsublist_nil by lia.
  rewrite CharArray.seg_empty.
  split_pure_spatial.
  - sep_apply CharArray.undef_full_to_undef_seg.
    cancel.
  - dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_2_split_goal_spatial.
Qed.

Lemma proof_of_solver_entail_wit_6_1_split_goal_1 : solver_entail_wit_6_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k.
  rewrite app_Znth1 by lia.
  rewrite (sublist_split 0 (i + 1) i plain) by lia.
  rewrite (sublist_single 0) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_2_split_goal_1 : solver_entail_wit_6_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst k.
  rewrite app_Znth1 by lia.
  rewrite (sublist_split 0 (i + 1) i plain) by lia.
  rewrite (sublist_single 0) by lia.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = p) by lia.
  subst i.
  subst k.
  subst p.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = p) by lia.
  subst i.
  subst k.
  subst p.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_1_split_goal_1 : solver_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnil : sublist 3 3 plain = (@nil Z)) by
    (unfold sublist; apply skipn_all2; rewrite length_firstn; lia).
  rewrite Hnil, app_nil_r.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_2_split_goal_1 : solver_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hnil : sublist 4 4 plain = (@nil Z)) by
    (unfold sublist; apply skipn_all2; rewrite length_firstn; lia).
  rewrite Hnil, app_nil_r.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_1_split_goal_1 : solver_entail_wit_9_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 by lia.
  rewrite (sublist_split 3 (i + 1) i plain) by lia.
  rewrite (sublist_single 0 i plain) by lia.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_9_2_split_goal_1 : solver_entail_wit_9_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite app_Znth1 by lia.
  rewrite (sublist_split 4 (i + 1) i plain) by lia.
  rewrite (sublist_single 0 i plain) by lia.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = ru) by lia.
  subst i.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (i = ru) by lia.
  subst i.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_1_split_goal_1 : solver_entail_wit_11_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (Zsublist_nil plain (ru + 2) (ru + 2)) by lia.
  rewrite app_nil_r.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_2_split_goal_1 : solver_entail_wit_11_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (Zsublist_nil plain (ru + 2) (ru + 2)) by lia.
  rewrite app_nil_r.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_1_split_goal_1 : solver_entail_wit_12_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (sublist_split (ru + 2) (i + 1) i plain) by lia.
  rewrite (sublist_single 0 i plain) by lia.
  unfold Znth at 1.
  rewrite app_nth1.
  - repeat rewrite app_assoc.
    reflexivity.
  - rewrite Zlength_correct in *.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12_2_split_goal_1 : solver_entail_wit_12_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite (sublist_split (ru + 2) (i + 1) i plain) by lia.
  rewrite (sublist_single 0 i plain) by lia.
  unfold Znth at 1.
  rewrite app_nth1.
  - repeat rewrite app_assoc.
    reflexivity.
  - rewrite Zlength_correct in *.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_2 : solver_entail_wit_12_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_12_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_13_1_split_goal_1 : solver_entail_wit_13_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  try rewrite Zlength_nil.
  repeat rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_13_1_split_goal_2 : solver_entail_wit_13_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  subst p.
  destruct PreH5 as [_ [Hlower _]].
  eapply (restored_address_with_context__final_semantic
            plain (sublist 0 3 plain) (sublist 3 ru plain)
            (sublist (ru + 2) i plain)).
  - right. exact PreH7.
  - unfold LowercaseNonempty. split.
    + rewrite Zlength_sublist by lia. lia.
    + unfold sublist.
      apply Forall_skipn__final_semantic.
      apply Forall_firstn__final_semantic.
      exact Hlower.
  - unfold LowercaseNonempty. split.
    + rewrite Zlength_sublist by lia. lia.
    + unfold sublist.
      apply Forall_skipn__final_semantic.
      apply Forall_firstn__final_semantic.
      exact Hlower.
  - assert (Hi : i = Zlength plain) by lia.
    rewrite <- (sublist_self plain i Hi) at 1.
    rewrite (sublist_split 0 i 3 plain) by lia.
    rewrite (sublist_split 3 i ru plain) by lia.
    rewrite (sublist_split ru i (ru + 1) plain) by lia.
    rewrite (sublist_split (ru + 1) i (ru + 2) plain) by lia.
    rewrite (sublist_single 0 ru plain) by lia.
    replace (ru + 2) with ((ru + 1) + 1) by lia.
    rewrite (sublist_single 0 (ru + 1) plain) by lia.
    rewrite PreH10, PreH11.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_13_2_split_goal_1 : solver_entail_wit_13_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  try rewrite Zlength_nil.
  repeat rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_13_2_split_goal_2 : solver_entail_wit_13_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  subst p.
  destruct PreH5 as [_ [Hlower _]].
  eapply (restored_address_with_context__final_semantic
            plain (sublist 0 4 plain) (sublist 4 ru plain)
            (sublist (ru + 2) i plain)).
  - left. exact PreH7.
  - unfold LowercaseNonempty. split.
    + rewrite Zlength_sublist by lia. lia.
    + unfold sublist.
      apply Forall_skipn__final_semantic.
      apply Forall_firstn__final_semantic.
      exact Hlower.
  - unfold LowercaseNonempty. split.
    + rewrite Zlength_sublist by lia. lia.
    + unfold sublist.
      apply Forall_skipn__final_semantic.
      apply Forall_firstn__final_semantic.
      exact Hlower.
  - assert (Hi : i = Zlength plain) by lia.
    rewrite <- (sublist_self plain i Hi) at 1.
    rewrite (sublist_split 0 i 4 plain) by lia.
    rewrite (sublist_split 4 i ru plain) by lia.
    rewrite (sublist_split ru i (ru + 1) plain) by lia.
    rewrite (sublist_split (ru + 1) i (ru + 2) plain) by lia.
    rewrite (sublist_single 0 ru plain) by lia.
    replace (ru + 2) with ((ru + 1) + 1) by lia.
    rewrite (sublist_single 0 (ru + 1) plain) by lia.
    rewrite PreH10, PreH11.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_13_3_split_goal_1 : solver_entail_wit_13_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  try rewrite Zlength_nil.
  repeat rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_13_3_split_goal_2 : solver_entail_wit_13_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  subst p.
  destruct PreH5 as [_ [Hlower _]].
  eapply (restored_address_without_context__final_semantic
            plain (sublist 0 3 plain) (sublist 3 ru plain)).
  - right. exact PreH7.
  - unfold LowercaseNonempty. split.
    + rewrite Zlength_sublist by lia. lia.
    + unfold sublist.
      apply Forall_skipn__final_semantic.
      apply Forall_firstn__final_semantic.
      exact Hlower.
  - assert (Hn : n = ru + 2) by lia.
    rewrite <- (sublist_self plain n PreH2) at 1.
    rewrite (sublist_split 0 n 3 plain) by lia.
    rewrite (sublist_split 3 n ru plain) by lia.
    rewrite (sublist_split ru n (ru + 1) plain) by lia.
    rewrite (sublist_single 0 ru plain) by lia.
    replace (ru + 2) with ((ru + 1) + 1) in Hn by lia.
    rewrite Hn.
    rewrite (sublist_single 0 (ru + 1) plain) by lia.
    rewrite PreH10, PreH11.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_13_3 : solver_entail_wit_13_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_3_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_13_4_split_goal_1 : solver_entail_wit_13_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_app.
  repeat rewrite Zlength_cons.
  try rewrite Zlength_nil.
  repeat rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_13_4_split_goal_2 : solver_entail_wit_13_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold Spec.
  subst p.
  destruct PreH5 as [_ [Hlower _]].
  eapply (restored_address_without_context__final_semantic
            plain (sublist 0 4 plain) (sublist 4 ru plain)).
  - left. exact PreH7.
  - unfold LowercaseNonempty. split.
    + rewrite Zlength_sublist by lia. lia.
    + unfold sublist.
      apply Forall_skipn__final_semantic.
      apply Forall_firstn__final_semantic.
      exact Hlower.
  - assert (Hn : n = ru + 2) by lia.
    rewrite <- (sublist_self plain n PreH2) at 1.
    rewrite (sublist_split 0 n 4 plain) by lia.
    rewrite (sublist_split 4 n ru plain) by lia.
    rewrite (sublist_split ru n (ru + 1) plain) by lia.
    rewrite (sublist_single 0 ru plain) by lia.
    replace (ru + 2) with ((ru + 1) + 1) in Hn by lia.
    rewrite Hn.
    rewrite (sublist_single 0 (ru + 1) plain) by lia.
    rewrite PreH10, PreH11.
    reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_13_4 : solver_entail_wit_13_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_13_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_13_4_split_goal_2.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists address_2.
  rewrite PreH1, PreH9.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray.seg_to_full out_pre 0 (Zlength address_2 + 1)
         (address_2 +:: 0)).
    replace (out_pre + 0 * sizeof(CHAR)) with out_pre by lia.
    replace (Zlength address_2 + 1 - 0) with (Zlength address_2 + 1) by lia.
    cancel (CharArray.full s_pre (Zlength plain + 1) (plain +:: 0)).
    cancel (CharArray.full out_pre (Zlength address_2 + 1)
              (address_2 +:: 0)).
    cancel (CharArray.undef_seg out_pre (Zlength address_2 + 1) 72).
  - dump_pre_spatial.
    exact PreH8.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists address_2.
  rewrite PreH1, PreH9.
  split_pure_spatial.
  - sep_apply_l_atomic
      (CharArray.seg_to_full out_pre 0 (Zlength address_2 + 1)
         (address_2 +:: 0)).
    replace (out_pre + 0 * sizeof(CHAR)) with out_pre by lia.
    replace (Zlength address_2 + 1 - 0) with (Zlength address_2 + 1) by lia.
    cancel (CharArray.full s_pre (Zlength plain + 1) (plain +:: 0)).
    cancel (CharArray.full out_pre (Zlength address_2 + 1)
              (address_2 +:: 0)).
    cancel (CharArray.undef_seg out_pre (Zlength address_2 + 1) 72).
  - dump_pre_spatial.
    exact PreH8.
Qed.
