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

Lemma proof_of_solver_propagate_partial_solve_wit_29_scan_same_pure : solver_propagate_partial_solve_wit_29_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hk : Znth ii tagged_memory 0 = scan_current)
    by (rewrite PreH1, PreH12; apply Znth_replace_Znth_Same; lia).
  split_pures; dump_pre_spatial; first [exact Hk | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_30_scan_move_pure : solver_propagate_partial_solve_wit_30_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hk : Znth ii tagged_memory 0 = scan_current).
  { subst tagged_memory.
    rewrite (Znth_replace_Znth_Diff 0 watch_memory jj ii scan_current) by lia.
    subst watch_memory.
    rewrite app_Znth2 by lia.
    replace (ii - Zlength raw_prefix) with 0 by lia.
    reflexivity. }
  split_pures; dump_pre_spatial; first [exact Hk | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_31_scan_same_pure : solver_propagate_partial_solve_wit_31_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hk : Znth ii tagged_memory 0 = scan_current)
    by (rewrite PreH1, PreH12; apply Znth_replace_Znth_Same; lia).
  split_pures; dump_pre_spatial; first [exact Hk | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_32_scan_move_pure : solver_propagate_partial_solve_wit_32_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hk : Znth ii tagged_memory 0 = scan_current).
  { rewrite PreH1, Znth_replace_Znth_Diff by lia.
    rewrite PreH10, <- PreH11. apply Znth_app_hd. }
  split_pures; dump_pre_spatial; first [exact Hk | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_33_scan_same_pure : solver_propagate_partial_solve_wit_33_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hphys : propagation_watch_scan_physical _ _ _ _ _ ?wm _ _,
    Hwm : ?wm = ?rp ++ ?sc :: ?rs, Hrp : Zlength ?rp = _ |- _ =>
      pose proof (propagation_watch_scan_rest_head__propagate
        _ _ _ _ _ _ _ _ _ _ _ Hphys Hwm Hrp) as Hrest
  end.
  match goal with
  | Hsem : solver_propagation_scan_semantics _ _ _ _ _ _ _ _ _,
    Htag : is_tag _ = msat_true |- _ =>
      pose proof (propagation_scan_current_enqueue_input__propagate
        _ _ _ _ _ _ _ _ _ _ _ Hsem Hrest Htag) as Henq
  end.
  try match goal with H : Mscan = msolver_propagation_scan_begin _ _ _ |- _ => rewrite <- H end.
  try subst retval.
  try match goal with H : tagged_memory = replace_Znth _ _ _ |- _ =>
    assert (Htlen : Zlength tagged_memory = Zlength watch_memory)
      by (rewrite H; apply Zlength_replace_Znth) end.
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  split_pures; dump_pre_spatial.
  all: try solve [ reflexivity | exact Henq | unfold solver_shape in *; lia ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_34_scan_move_pure : solver_propagate_partial_solve_wit_34_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( tagged_memory = replace_Znth jj scan_current watch_memory ) as H_tagged_memory.
  bind_fact ( is_tag scan_current = msat_true ) as H_is_tag.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  msat_propagate_scan_enqueue_input H_propagation_watch_scan_physical
    H_watch_memory H_Zlength H_solver_propagation_scan_semantics H_is_tag
    as Henq.
  bind_fact (Zlength watch_memory = Zlength source_words) as Hwl.
  bind_fact (Mscan = msolver_propagation_scan_begin Mentry simp_count prop_count) as H_Mscan.
  rewrite <- H_tagged_memory, <- H_Mscan.
  assert (Hlen : 0 <= ii < Zlength tagged_memory)
    by (rewrite H_tagged_memory, Zlength_replace_Znth; lia).
  assert (Hk : Znth ii tagged_memory 0 = scan_current) by assumption.
  rewrite Hk.
  pose proof H_solver_shape as Hsh. unfold solver_shape in Hsh.
  split_pures; dump_pre_spatial; first [reflexivity | exact Henq | tauto | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_35_scan_same_pure : solver_propagate_partial_solve_wit_35_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact ( is_tag scan_current = msat_true ) as H_is_tag.
  bind_fact ( watch_memory = raw_prefix ++ scan_current :: raw_suffix ) as H_watch_memory.
  bind_fact ( Zlength raw_prefix = ii ) as H_Zlength.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p confl retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj ) as
    H_propagation_watch_scan_physical.
  bind_fact ( Zlength watch_memory = Zlength source_words ) as H_Zlength_2.
  assert (Hcur : Znth ii (replace_Znth ii scan_current watch_memory) 0 = scan_current).
  { apply Znth_replace_Znth_Same. rewrite H_Zlength_2. lia. }
  msat_propagate_scan_enqueue_input H_propagation_watch_scan_physical
    H_watch_memory H_Zlength H_solver_propagation_scan_semantics H_is_tag
    as Henq.
  rewrite Hcur.
  unfold solver_shape in H_solver_shape.
  split_pures; dump_pre_spatial; try solve [auto | lia | tauto].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_36_scan_move_pure : solver_propagate_partial_solve_wit_36_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hphys : propagation_watch_scan_physical _ _ _ _ _ ?wm _ _,
    Hwm : ?wm = ?rp ++ ?sc :: ?rs, Hrp : Zlength ?rp = _ |- _ =>
      pose proof (propagation_watch_scan_rest_head__propagate
        _ _ _ _ _ _ _ _ _ _ _ Hphys Hwm Hrp) as Hrest
  end.
  match goal with
  | Hsem : solver_propagation_scan_semantics _ _ _ _ _ _ _ _ _,
    Htag : is_tag _ = msat_true |- _ =>
      pose proof (propagation_scan_current_enqueue_input__propagate
        _ _ _ _ _ _ _ _ _ _ _ Hsem Hrest Htag) as Henq
  end.
  try match goal with H : Mscan = msolver_propagation_scan_begin _ _ _ |- _ => rewrite <- H end.
  try subst retval.
  try match goal with H : tagged_memory = replace_Znth _ _ _ |- _ =>
    assert (Htlen : Zlength tagged_memory = Zlength watch_memory)
      by (rewrite H; apply Zlength_replace_Znth) end.
  try match goal with H : tagged_memory = replace_Znth _ _ _ |- _ => rewrite <- H end.
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  split_pures; dump_pre_spatial.
  all: try solve [ reflexivity | exact Henq | unfold solver_shape in *; lia ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_38_scan_move_pure : solver_propagate_partial_solve_wit_38_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH2.
  assert (Htw : tagged_word scan_current) by (unfold tagged_word; exact PreH6).
  destruct PreH1 as [Hwf [Hn2 _]].
  unfold lit_wf_c in Hwf.
  split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_41_scan_same_pure : solver_propagate_partial_solve_wit_41_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH2.
  assert (Htw : tagged_word scan_current) by (unfold tagged_word; exact PreH6).
  destruct PreH1 as [Hwf [Hn2 _]].
  unfold lit_wf_c in Hwf.
  split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_44_scan_move_pure : solver_propagate_partial_solve_wit_44_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH2.
  assert (Htw : tagged_word scan_current) by (unfold tagged_word; exact PreH6).
  destruct PreH1 as [Hwf [Hn2 _]].
  unfold lit_wf_c in Hwf.
  split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_47_scan_same_pure : solver_propagate_partial_solve_wit_47_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite PreH2.
  assert (Htw : tagged_word scan_current) by (unfold tagged_word; exact PreH6).
  destruct PreH1 as [Hwf [Hn2 _]].
  unfold lit_wf_c in Hwf.
  split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_49_scan_move_pure : solver_propagate_partial_solve_wit_49_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hphys : propagation_watch_scan_physical _ _ _ _ _ ?wm _ _,
    Hwm : ?wm = ?rp ++ ?sc :: ?rs, Hrp : Zlength ?rp = _ |- _ =>
      pose proof (propagation_watch_scan_rest_head__propagate
        _ _ _ _ _ _ _ _ _ _ _ Hphys Hwm Hrp) as Hrest
  end.
  match goal with
  | Hsem : solver_propagation_scan_semantics _ _ _ _ _ _ _ _ _,
    Htag : is_tag _ = msat_true |- _ =>
      pose proof (propagation_scan_current_enqueue_input__propagate
        _ _ _ _ _ _ _ _ _ _ _ Hsem Hrest Htag) as Henq
  end.
  try match goal with H : Mscan = msolver_propagation_scan_begin _ _ _ |- _ => rewrite <- H end.
  try subst retval.
  try match goal with H : jj = ii |- _ => subst jj end.
  try match goal with H : tagged_memory = replace_Znth _ _ _ |- _ =>
    assert (Htlen : Zlength tagged_memory = Zlength watch_memory)
      by (rewrite H; apply Zlength_replace_Znth); rewrite <- H end.
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  split_pures; dump_pre_spatial.
  all: try solve [ reflexivity | exact Henq | unfold solver_shape in *; lia ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_50_scan_same_pure : solver_propagate_partial_solve_wit_50_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (tagged_memory = replace_Znth jj scan_current watch_memory) as Ht.
  bind_fact (jj = ii) as Hjj.
  bind_fact (Znth ii tagged_memory 0 = scan_current) as Hk.
  replace (replace_Znth ii scan_current watch_memory) with tagged_memory
    by (rewrite Ht, Hjj; reflexivity).
  rewrite Hk in *.
  subst retval.
  split_pures; dump_pre_spatial; first [reflexivity | assumption].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_51_scan_move_pure : solver_propagate_partial_solve_wit_51_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite <- PreH44, <- PreH45, <- PreH43.
  subst retval.
  rewrite <- PreH5.
  rewrite PreH4.
  split_pures; dump_pre_spatial; solve [auto].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_52_scan_same_pure : solver_propagate_partial_solve_wit_52_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hphys : propagation_watch_scan_physical _ _ _ _ _ ?wm _ _,
    Hwm : ?wm = ?rp ++ ?sc :: ?rs, Hrp : Zlength ?rp = _ |- _ =>
      pose proof (propagation_watch_scan_rest_head__propagate
        _ _ _ _ _ _ _ _ _ _ _ Hphys Hwm Hrp) as Hrest
  end.
  match goal with
  | Hsem : solver_propagation_scan_semantics _ _ _ _ _ _ _ _ _,
    Htag : is_tag _ = msat_true |- _ =>
      pose proof (propagation_scan_current_enqueue_input__propagate
        _ _ _ _ _ _ _ _ _ _ _ Hsem Hrest Htag) as Henq
  end.
  try match goal with H : Mscan = msolver_propagation_scan_begin _ ?sc ?pc,
    Hs : ?sc = ms_simpdb_props Mscan, Hp : ?pc = stats_propagations (ms_stats Mscan) |- _ =>
      rewrite <- Hs, <- Hp, <- H end.
  try subst retval.
  try match goal with H : jj = ii |- _ => subst jj end.
  try match goal with H : tagged_memory = replace_Znth _ _ _ |- _ =>
    assert (Htlen : Zlength tagged_memory = Zlength watch_memory)
      by (rewrite H; apply Zlength_replace_Znth); rewrite <- H end.
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
  repeat match goal with H : Znth ?i ?l 0 = scan_current |- context [Znth ?i ?l 0] => rewrite H end.
  split_pures; dump_pre_spatial.
  all: try solve [ reflexivity | exact Henq | unfold solver_shape in *; lia ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_54_scan_move_pure : solver_propagate_partial_solve_wit_54_scan_move_pure.
Abort.



Lemma proof_of_solver_propagate_partial_solve_wit_55_scan_same_pure : solver_propagate_partial_solve_wit_55_scan_same_pure.
Abort.



Lemma proof_of_solver_propagate_partial_solve_wit_56_scan_move_pure : solver_propagate_partial_solve_wit_56_scan_move_pure.
Abort.



Lemma proof_of_solver_propagate_partial_solve_wit_76_scan_move_pure : solver_propagate_partial_solve_wit_76_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( Znth ii tagged_enqueue_conflict_memory 0 = scan_current ) as H_Znth.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( 0 <= scan_current ) as H_scan_current.
  bind_fact ( propagation_binary_conflict_scan_ready n Mscan p scan_current source_words simp_count
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
    split_pures;
      dump_pre_spatial;
      rewrite ?H_Znth, ?Hcur.
    - exact H_scan_current.
    - exact (proj1 H_propagation_binary_conflict_scan_r).
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - exact (proj1 H_propagation_binary_conflict_scan_r).
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_78_scan_same_pure : solver_propagate_partial_solve_wit_78_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia).
  bind_fact ( Znth ii tagged_enqueue_conflict_memory 0 = scan_current ) as H_Znth.
  bind_fact ( solver_shape Mscan ) as H_solver_shape.
  bind_fact ( solver_propagation_scan_semantics n F A_arr K Mscan p 0 retained rest ) as
    H_solver_propagation_scan_semantics.
  bind_fact ( rest = scan_current :: raw_suffix ) as H_rest.
  bind_fact ( 0 <= scan_current ) as H_scan_current.
  bind_fact ( propagation_binary_conflict_scan_ready n Mscan p scan_current source_words simp_count
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
    split_pures;
      dump_pre_spatial;
      rewrite ?H_Znth, ?Hcur.
    - exact H_scan_current.
    - exact (proj1 H_propagation_binary_conflict_scan_r).
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - unfold lit_wf_c in Htag; lia.
    - exact (proj1 H_propagation_binary_conflict_scan_r).
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_79_scan_move_pure : solver_propagate_partial_solve_wit_79_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (sizeof (PTR)) with ptr_size_Z in *. unfold_arch.
  split_pures; dump_pre_spatial; lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_83_scan_move_pure : solver_propagate_partial_solve_wit_83_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hk : propagation_scan_open n F A_arr K M0 Mentry Mscan p 0 source_words
                 retained moved rest garbage watch_memory ii jj scan_current raw_suffix).
  { unfold propagation_scan_open. do 7 (split; [assumption |]). reflexivity. }
  split_pures; dump_pre_spatial;
    first [ exact Hk | assumption | reflexivity | lia | (subst logical_words; assumption) ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_84_binary_keep_pure : solver_propagate_partial_solve_wit_84_binary_keep_pure.
Abort.



Lemma proof_of_solver_propagate_partial_solve_wit_96_scan_same_pure : solver_propagate_partial_solve_wit_96_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj) as Hph.
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hw.
  bind_fact (Zlength raw_prefix = ii) as Hz.
  pose proof (propagation_watch_scan_rest_head__propagate _ _ _ _ _ _ _ _ _ _ _ Hph Hw Hz) as Hrest.
  assert (Hc : confl = 0).
  { match goal with Hs : solver_propagation_scan_semantics _ _ _ _ _ _ confl _ _ |- _ =>
      destruct Hs as [[Hc _] | [_ [Hnil _]]] end;
    [exact Hc | rewrite Hrest in Hnil; discriminate]. }
  subst confl.
  split_pures; dump_pre_spatial;
    first [ assumption | (subst retval; assumption)
          | (match goal with HM : _ = msolver_propagation_scan_begin _ _ _ |- _ =>
               rewrite <- HM; assumption end) ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_97_scan_move_pure : solver_propagate_partial_solve_wit_97_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bind_fact (propagation_watch_scan_physical source_words retained moved rest garbage watch_memory ii jj) as Hph.
  bind_fact (watch_memory = raw_prefix ++ scan_current :: raw_suffix) as Hw.
  bind_fact (Zlength raw_prefix = ii) as Hz.
  pose proof (propagation_watch_scan_rest_head__propagate _ _ _ _ _ _ _ _ _ _ _ Hph Hw Hz) as Hrest.
  assert (Hc : confl = 0).
  { match goal with Hs : solver_propagation_scan_semantics _ _ _ _ _ _ confl _ _ |- _ =>
      destruct Hs as [[Hc _] | [_ [Hnil _]]] end;
    [exact Hc | rewrite Hrest in Hnil; discriminate]. }
  subst confl.
  split_pures; dump_pre_spatial;
    first [ assumption | (subst retval; assumption)
          | (match goal with HM : _ = msolver_propagation_scan_begin _ _ _ |- _ =>
               rewrite <- HM; assumption end) ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_98_scan_same_pure : solver_propagate_partial_solve_wit_98_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  bind_fact (solver_propagation_scan_semantics n F A_arr K Mscan p
    confl retained rest) as Hscan.
  bind_fact (propagation_watch_scan_physical source_words retained moved
    rest garbage watch_memory ii jj) as Hphysical.
  assert (Hconfl : confl = 0).
  { pose proof Hscan as Hcases.
    destruct Hcases as [[Hzero _] | [_ [Hrest _]]]; [exact Hzero |].
    pose proof Hphysical as Hlayout.
    destruct Hlayout as [_ [Hmemory [_ [Hprefix Hlength]]]].
    subst rest. rewrite app_nil_r in Hmemory.
    rewrite Hmemory, Hprefix in Hlength. lia. }
  subst confl.
  (Intros; split_pures; dump_pre_spatial; solve [auto | (congruence)]).
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_99_scan_move_pure : solver_propagate_partial_solve_wit_99_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  match goal with
  | Hphys : propagation_watch_scan_physical _ _ _ _ _ ?wm _ _,
    Hwm : ?wm = ?rp ++ ?sc :: ?rs, Hrp : Zlength ?rp = _ |- _ =>
      pose proof (propagation_watch_scan_rest_head__propagate
        _ _ _ _ _ _ _ _ _ _ _ Hphys Hwm Hrp) as Hrest
  end.
  assert (Hcf : confl = 0).
  { match goal with
    | Hsem : solver_propagation_scan_semantics _ _ _ _ _ _ confl _ _ |- _ =>
        destruct Hsem as [[Hc _] | [_ [Hnil _]]];
        [ exact Hc | rewrite Hrest in Hnil; discriminate ]
    end. }
  subst confl.
  split_pures; dump_pre_spatial; first [ assumption | (subst retval; assumption) ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_108_scan_same_pure : solver_propagate_partial_solve_wit_108_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_109_scan_move_pure : solver_propagate_partial_solve_wit_109_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_110_scan_same_pure : solver_propagate_partial_solve_wit_110_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_111_scan_move_pure : solver_propagate_partial_solve_wit_111_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_244_scan_move_pure : solver_propagate_partial_solve_wit_244_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (retval_3 - 0) with retval_3 in * by lia.
  split_pures; dump_pre_spatial;
    first [ assumption | lia | (subst retval_3 retval_2; lia)
          | (match goal with HM : _ = msolver_propagation_scan_begin _ _ _ |- _ =>
               rewrite <- HM; lia end) ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_246_scan_same_pure : solver_propagate_partial_solve_wit_246_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (retval_3 - 0) with retval_3 in PreH1 by lia.
  subst retval_3.
  split_pures; dump_pre_spatial; solve [auto | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_248_scan_move_pure : solver_propagate_partial_solve_wit_248_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite ?Z.sub_0_r in *.
  split_pures; dump_pre_spatial.
  all: first [ assumption | lia | (subst retval_3 retval_2; lia)
             | (match goal with HM : _ = msolver_propagation_scan_begin _ _ _ |- _ =>
                  rewrite <- HM; lia end) ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_250_scan_same_pure : solver_propagate_partial_solve_wit_250_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (retval_3 - 0) with retval_3 in * by lia.
  split_pures; dump_pre_spatial;
    first [ assumption | lia | (subst retval_3 retval_2; lia)
          | (match goal with HM : _ = msolver_propagation_scan_begin _ _ _ |- _ =>
               rewrite <- HM; lia end) ].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_252_scan_move_pure : solver_propagate_partial_solve_wit_252_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (retval_3 - 0) with retval_3 in PreH1 by lia.
  subst retval_3.
  repeat lazymatch goal with
  | |- _ |-- _ && _ => apply _derivable1_andp_intros
  end;
  apply dump_spatial_left.
  all: first [assumption | reflexivity | (rewrite <- PreH70; lia) | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_256_scan_same_pure : solver_propagate_partial_solve_wit_256_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rewrite ?Z.sub_0_r in *.
  subst retval_3.
  split_pures; dump_pre_spatial.
  all: first [assumption | reflexivity | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_260_scan_move_pure : solver_propagate_partial_solve_wit_260_scan_move_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (retval_3 - 0) with retval_3 in * by lia.
  subst retval_3. rewrite <- PreH72.
  split_pures; dump_pre_spatial; first [assumption | reflexivity | lia].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_264_scan_same_pure : solver_propagate_partial_solve_wit_264_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto). unfold stats_propagations, stats_inspects in *.
  msat_propagate_close_scan_first_lit_assigned.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_292_scan_same_pure : solver_propagate_partial_solve_wit_292_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_296_scan_move_pure : solver_propagate_partial_solve_wit_296_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_300_scan_same_pure : solver_propagate_partial_solve_wit_300_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_304_scan_move_pure : solver_propagate_partial_solve_wit_304_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_308_scan_same_pure : solver_propagate_partial_solve_wit_308_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_310_scan_move_pure : solver_propagate_partial_solve_wit_310_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_312_scan_same_pure : solver_propagate_partial_solve_wit_312_scan_same_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_314_scan_move_pure : solver_propagate_partial_solve_wit_314_scan_move_pure.
Proof.
  msat_close_clause_hdr_word_nonneg.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_412_scan_same_pure : solver_propagate_partial_solve_wit_412_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (sizeof (INT)) with 4 in *.
  split_pures; dump_pre_spatial; lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_419_scan_same_pure : solver_propagate_partial_solve_wit_419_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  split_pures; dump_pre_spatial; solve [auto | lia | congruence].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_425_scan_same_pure : solver_propagate_partial_solve_wit_425_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold lit_var_c in *.
  pose proof (Z.div_mod candidate 2 ltac:(lia)).
  pose proof (Z.mod_pos_bound candidate 2 ltac:(lia)).
  prop_apply_p (store_int_range (lits + 1 * sizeof(INT)) candidate).
  Intros_p Hrange.
  change Int.max_signed with 2147483647 in Hrange.
  split_pures; dump_pre_spatial; lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_432_real_migrated_pure : solver_propagate_partial_solve_wit_432_real_migrated_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst candidate_post_memory false_lit k.
  assert (Hcur : Znth ii watch_memory 0 = scan_current) by assumption.
  assert (Hmig : Znth ii migration_post_memory 0 = scan_current) by assumption.
  assert (Hlen : 0 <= ii < Zlength watch_memory) by lia.
  assert (Hrep : Znth ii (replace_Znth ii scan_current watch_memory) 0 = scan_current)
    by (apply Znth_replace_Znth_Same; exact Hlen).
  assert (Hsign : 0 <= lit_sign_c candidate <= 1) by apply lit_sign_c_range.
  rewrite Z.sub_0_r in PreH19. subst retval retval_2.
  assert (Hassign : Znth (lit_var_c candidate) (mt_assigns (ms_core Mscan)) 0 <> 2 * lit_sign_c candidate - 1).
  { rewrite signed_last_nbits_8_lit_sign in PreH19.
    assert (Hcase : lit_sign_c candidate = 0 \/ lit_sign_c candidate = 1) by lia.
    destruct Hcase as [Hc | Hc]; rewrite Hc in PreH19 |- *; exact PreH19. }
  assert (Hlay : propagation_scan_candidate_layout scan_current lits stop (lits + offset * sizeof(INT))
                   offset (lit_neg_c p) p candidate (2 * lit_sign_c candidate - 1) clause_contents).
  { unfold propagation_scan_candidate_layout.
    repeat split; first [assumption | lia | reflexivity]. }
  assert (Hn : n = ms_size Mscan).
  { destruct PreH12 as [[_ [Hweak _]] | [Hnz _]];
      [exact (proj1 (solver_propagation_weak_reason_core _ _ _ _ _ Hweak)) | lia]. }
  assert (Hslot : propagation_scan_slot Mscan p scan_wm logical_words)
    by (unfold propagation_scan_slot; split; [assumption | lia]).
  rewrite ?PreH49, ?Hmig, ?Hcur, <- ?PreH26.
  split_pures; dump_pre_spatial.
  all: first [assumption | reflexivity | lia | (constructor; reflexivity)].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_446_unit_conflict_copy_pure : solver_propagate_partial_solve_wit_446_unit_conflict_copy_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hsz : sizeof(PTR) = 4) by reflexivity.
  split_pures; dump_pre_spatial; subst i endvar; rewrite Hsz in *; lia.
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_434_scan_same_pure : solver_propagate_partial_solve_wit_434_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hs : sizeof(INT) = 4) by reflexivity.
  assert (Hk : k = stop) by (rewrite PreH36, PreH37 in *; rewrite Hs in *; lia).
  split_pures; dump_pre_spatial; first [exact Hk | assumption | reflexivity | (rewrite Hs in *; lia)].
Qed.



Lemma proof_of_solver_propagate_partial_solve_wit_433_scan_same_pure : solver_propagate_partial_solve_wit_433_scan_same_pure.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval retval_2. pose proof (lit_sign_c_range candidate).
  rewrite !signed_last_nbits_8_lit_sign in *.
  rewrite (signed_last_nbits_eq (lit_sign_c candidate + (lit_sign_c candidate - 1)) 8) in * by (try lia; cbn; lia).
  rewrite ?Z.sub_0_r in *.
  split_pures; dump_pre_spatial.
  all: try assumption.
  all: try lia.
  all: try (unfold propagation_normalized_clause;
            rewrite (Znth_cons 0 offset) by lia; rewrite (Znth_cons 0 (offset - 1)) by lia;
            replace (offset - 1 - 1) with (offset - 2) by lia; assumption).
Qed.




Lemma proof_of_solver_propagate_entail_wit_5_2_scan_move : solver_propagate_entail_wit_5_2_scan_move.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (HMs : msolver_propagation_scan_begin Mentry (ms_simpdb_props Mscan)
      (stats_propagations (ms_stats Mscan)) = Mscan) by congruence.
  rewrite HMs.
  assert (Hlen_tecm : Zlength tagged_enqueue_conflict_memory = Zlength watch_memory).
  { match goal with
    | H1 : tagged_enqueue_conflict_memory = replace_Znth _ _ ?tm,
      H2 : ?tm = replace_Znth _ _ watch_memory |- _ =>
        rewrite H1, Zlength_replace_Znth, H2, Zlength_replace_Znth; reflexivity
    end. }
  assert (Hlen_ws : Zlength watch_memory = Zlength source_words) by lia.
  sep_apply_l_atomic (PtrArray.full_to_seg begin (Zlength source_words)
    tagged_enqueue_conflict_memory).
  sep_apply (Vecp.rep_ptr_intro ws begin tagged_enqueue_conflict_memory cap
    (Zlength watch_memory) (Zlength source_words) (Zlength watch_memory));
    [ | first [lia | vec_buf_solve] .. ].
  unfold stats_propagations, stats_inspects in *.
  lazymatch goal with
  | Hrv : retval_2 = tag_lit _ |- _ => repeat rewrite replace_Znth_Znth in Hrv
  end.
  subst retval_2. subst retval_3. subst retval_4. subst scan_current.
  lazymatch goal with
  | Hsem : solver_propagation_scan_semantics ?n ?F ?A ?K ?M ?p ?cfl ?kept ?rst,
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
  end.
  subst confl.
  lazymatch goal with
  | Hsem : solver_propagation_scan_semantics ?n ?F ?A ?K ?M ?p 0 ?kept ?rst,
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



Lemma proof_of_solver_propagate_entail_wit_12_3_scan_move : solver_propagate_entail_wit_12_3_scan_move.
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



Lemma proof_of_solver_propagate_entail_wit_20_1_real_satisfied : solver_propagate_entail_wit_20_1_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_20_24_real_satisfied : solver_propagate_entail_wit_20_24_real_satisfied.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  msat_real_satisfied_dispatch.
Qed.



Lemma proof_of_solver_propagate_entail_wit_21_unit_success : solver_propagate_entail_wit_21_unit_success.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  rename PreH1 into H_db_pair_lits_update.
  rename PreH4 into H_propagation_unit_success_transitio.
  rename PreH6 into H_propagation_scan_keep_step.
  rename PreH18 into H_msolver_seed_shadow.
  rename PreH19 into H_propagation_caller_frame.
  rename PreH20 into H_propagation_scan_frontier.
  rename PreH21 into H_solver_propagation_scan_semantics.
  rename PreH27 into H_confl.
  rename PreH38 into H_candidate_post_memory.
  rename PreH40 into H_logical_words.
  unfold enqueue_post_at.
  Intros qtail_after assigns_after levels_after reasons_after trail_after.
  unfold enqueue_state_at.
  Intros rsn_route trl_route.
  rename H into Henq.
  unfold propagation_unit_success_transition in H_propagation_unit_success_transitio.
  cbn in H_propagation_unit_success_transitio.
  destruct H_propagation_unit_success_transitio as [HMroute Hsem].
  pose proof HMroute as HMroute_original.
  unfold propagation_scan_keep_step in H_propagation_scan_keep_step.
  destruct H_propagation_scan_keep_step as [Hrest [Hretained [Hmemory Hphysical]]].
  assert (Hphysical_route : propagation_watch_scan_physical source_words
      retained_route moved rest_route garbage_route memory_route
      (ii + 1) (jj + 1)) by exact Hphysical.
  assert (Hmemory_length : Zlength memory_route = Zlength source_words).
  { unfold propagation_watch_scan_physical in Hphysical_route. intuition. }
  assert (Hlogical : logical_words = retained_route ++ rest_route).
  { rewrite H_logical_words, Hretained, Hrest. rewrite <- app_assoc. reflexivity. }
  assert (Hsem_confl : solver_propagation_scan_semantics n F A_arr K
      Mroute p confl retained_route rest_route).
  { rewrite H_confl. exact Hsem. }
  assert (Hreuse_confl : minisat_propagation_reuse_scan M0 Mroute p confl rest_route).
  { rewrite H_confl. assumption. }
  destruct (msat_propagate_scan_live_core n F A_arr K Mroute p
    retained_route rest_route Hsem) as [Hshape_route _].
  destruct (msat_propagate_scan_live_core n F A_arr K Mscan p retained rest
    H_solver_propagation_scan_semantics) as [Hshape_scan Hwf_scan].
  assert (Htrail_len : Zlength (mt_trail (ms_core Mscan)) = ms_qtail Mscan)
    by (unfold solver_shape in Hshape_scan; intuition).
  sep_apply (PtrArray.full_to_seg begin (Zlength source_words)
    (replace_Znth jj scan_current candidate_post_memory)).
  sep_apply (Vecp.rep_ptr_intro ws begin
    (replace_Znth jj scan_current candidate_post_memory) cap
    (Zlength candidate_post_memory) (Zlength source_words)
    (Zlength candidate_post_memory));
    [ | rewrite ?Zlength_replace_Znth; pose proof (Zlength_nonneg candidate_post_memory);
        first [lia | vec_buf_solve] .. ].
  unfold enqueue_transition in Henq.
  destruct Henq as [Hsame | [Hconflict | Hfresh]].
  - destruct Hsame as
      [Hassigned [_ [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]]].
    assert (Hnonzero :
      Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 <> 0)
      by (pose proof (lit_sig_nonzero watch0); congruence).
    assert (Htest :
      (Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 =? 0)%Z
      = false) by (apply Z.eqb_neq; exact Hnonzero).
    msat_propagate_enqueue_route_shape Htest HMroute assigns_after
      levels_after reasons_after trail_after qtail_after.
    assert (Hfrontier_route : propagation_scan_frontier Mentry Mroute p)
      by (rewrite HMroute;
        unfold propagation_scan_frontier in H_propagation_scan_frontier |- *;
        cbn; exact H_propagation_scan_frontier).
    msat_propagate_unit_route_facts HMroute HMroute_original
      H_msolver_seed_shadow H_propagation_caller_frame H_db_pair_lits_update
      Mroute Mscan M0 s_pre.
    Left.
    Exists trl_route rsn_route prop_count simp_count
      scan_wm
      logical_words source_words moved garbage_route memory_route
      (ii + 1) (jj + 1) retained_route rest_route Mentry.
    Exists Mroute levels_entry.
    split_pure_spatial.
    + rewrite H_candidate_post_memory, Hmemory; msat_cancel_sound.
      rewrite HMroute; cbn; msat_cancel_sound.
      unfold solver_propagation_scan_core_at; cbn.
      unfold PtrArray.seg, stats_propagate_scan; msat_cancel_sound.
      fold (stats_inspects (ms_stats Mscan)).
      rewrite <- HMroute, Hbinary, Hframe; msat_cancel_sound.
      rewrite <- !msat_dot_field_addr_arrow; unfold stats_inspects.
      lazymatch goal with
      | |- ?A |-- ?B => unify A B; change (A |-- A)
      end; cancel.
    + msat_propagate_unit_pure_close Hshape_route Hseed_route Hcaller_route
        Hfrontier_route Hsem_confl Hphysical_route Hlogical Hmemory_length
        HMroute.
  - destruct Hconflict as [_ [_ [Hret _]]]. lia.
  - destruct Hfresh as
      [Hzero [_ [Hassigns [Hlevels [Hreasons [Htrail Hqtail]]]]]].
    assert (Htest :
      (Znth (lit_var_c watch0) (mt_assigns (ms_core Mscan)) 0 =? 0)%Z
      = true) by (apply Z.eqb_eq; exact Hzero).
    assert (Hfrontier_route : propagation_scan_frontier Mentry Mroute p)
      by (eapply msat_propagate_scan_frontier_push;
        [ exact Hwf_scan | exact Htrail_len | exact Hzero
        | exact HMroute_original | exact H_propagation_scan_frontier ]).
    msat_propagate_enqueue_route_shape Htest HMroute assigns_after
      levels_after reasons_after trail_after qtail_after.
    msat_propagate_unit_route_facts HMroute HMroute_original
      H_msolver_seed_shadow H_propagation_caller_frame H_db_pair_lits_update
      Mroute Mscan M0 s_pre.
    Left.
    Exists trl_route rsn_route prop_count simp_count
      scan_wm
      logical_words source_words moved garbage_route memory_route
      (ii + 1) (jj + 1) retained_route rest_route Mentry.
    Exists Mroute levels_entry.
    split_pure_spatial.
    + rewrite H_candidate_post_memory, Hmemory; msat_cancel_sound.
      rewrite HMroute; cbn; msat_cancel_sound.
      unfold solver_propagation_scan_core_at; cbn.
      unfold CharArray.seg, IntArray.seg, PtrArray.seg, stats_propagate_scan.
      unfold replace_Znth; msat_cancel_sound.
      fold (stats_inspects (ms_stats Mscan)).
      rewrite <- HMroute, Hbinary, Hframe; msat_cancel_sound.
      rewrite <- !msat_dot_field_addr_arrow; unfold stats_inspects.
      lazymatch goal with
      | |- ?A |-- ?B => unify A B; change (A |-- A)
      end; cancel.
    + msat_propagate_unit_pure_close Hshape_route Hseed_route Hcaller_route
        Hfrontier_route Hsem_confl Hphysical_route Hlogical Hmemory_length
        HMroute.
Qed.
