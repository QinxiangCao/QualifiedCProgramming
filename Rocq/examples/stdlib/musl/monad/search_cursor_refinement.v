From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE.stdlib.musl.monad Require Import
  two_way_rel_lib factorization_refinement shift_table_refinement strstr_result_bridge.
Local Open Scope Z_scope.
Local Transparent refines.

Definition cursor_program (periodic : bool) text patn cut q pos memory :=
  if periodic then generic_match_periodic_from text patn cut q pos memory
  else generic_match_from text patn cut q pos.
Definition right_program (periodic : bool) text patn cut q pos memory k :=
  if periodic then generic_match_periodic_from_right text patn cut q pos memory k
  else generic_match_from_right text patn cut q pos k.
Definition left_program (periodic : bool) text patn cut q pos memory k :=
  if periodic then generic_match_periodic_from_left text patn cut q pos memory (k-1)
  else generic_match_from_left text patn cut q pos 0 (k-1).
Definition cursor_config (periodic : bool) (patn : list Z) p q memory remembered :=
  if periodic then q=p /\ remembered=Zlength patn-p
  else memory=0 /\ remembered=0.
Definition search_cursor text patn cut p remembered pos memory :=
  exists periodic q, cursor_config periodic patn p q memory remembered /\
    refines (two_way_generic_prog text patn) (cursor_program periodic text patn cut q pos memory).
Definition search_right_cursor text patn cut p remembered pos memory k :=
  exists periodic q, cursor_config periodic patn p q memory remembered /\
    refines (two_way_generic_prog text patn) (cursor_program periodic text patn cut q pos memory) /\
    refines (two_way_generic_prog text patn) (right_program periodic text patn cut q pos memory k).
Definition search_left_cursor text patn cut p remembered pos memory k :=
  exists periodic q, cursor_config periodic patn p q memory remembered /\
    refines (two_way_generic_prog text patn) (cursor_program periodic text patn cut q pos memory) /\
    refines (two_way_generic_prog text patn) (left_program periodic text patn cut q pos memory k).

Lemma search_cursor_init_periodic : forall text patn cut p,
  factorization_done patn cut p -> repetitive_split patn cut p ->
  search_cursor text patn cut p (Zlength patn-p) 0 0.
Proof.
  intros text patn cut p Hf Hr. exists true, p; split; [split; reflexivity|].
  intros X Hexec. pose proof (factorization_done_search_continuation text patn cut p Hf X Hexec) as H.
  unfold generic_match_phase in H. prog_nf in H. safe_choice_l H. exact H.
Qed.

Lemma search_cursor_init_nonperiodic : forall text patn cut original_p actual_p,
  factorization_done patn cut original_p -> ~repetitive_split patn cut original_p ->
  search_cursor text patn cut actual_p 0 0 0.
Proof.
  intros text patn cut original_p actual_p Hf Hr.
  exists false, (Z.max cut (Zlength patn-cut)+1); split; [split; reflexivity|].
  intros X Hexec. pose proof (factorization_done_search_continuation text patn cut original_p Hf X Hexec) as H.
  unfold generic_match_phase in H. prog_nf in H. safe_choice_r H. exact H.
Qed.

Lemma search_cursor_skip : forall text patn cut p remembered pos memory d,
  pos+Zlength patn <= Zlength text -> valid_skip text patn pos d ->
  search_cursor text patn cut p remembered pos memory ->
  search_cursor text patn cut p remembered (pos+d) 0.
Proof.
  intros text patn cut p remembered pos memory d Hw Hd [mode [q [Hc Href]]].
  exists mode,q; split.
  - destruct mode; simpl in *; tauto.
  - intros X Hexec. specialize (Href X Hexec).
    destruct mode; simpl in *.
    + eapply generic_periodic_valid_skip_continuation; eauto.
    + eapply generic_valid_skip_continuation; eauto.
Qed.

Lemma search_cursor_end : forall text patn cut p remembered pos memory,
  pos+Zlength patn > Zlength text ->
  search_cursor text patn cut p remembered pos memory ->
  refines (two_way_generic_prog text patn) (ret None).
Proof.
  intros text patn cut p remembered pos memory Hw [mode [q [Hc Href]]] X Hexec.
  specialize (Href X Hexec). destruct mode; simpl in Href.
  - unfold generic_match_periodic_from in Href. prog_nf in Href.
    unfold_loop in Href. prog_nf in Href.
    unfold generic_match_periodic_loop_body in Href at 1. prog_nf in Href.
    safe_choice_r Href. unfold match_periodic_loop_body in Href at 1. prog_nf in Href.
    safe_choice_r Href. unfold break in Href. prog_nf in Href. exact Href.
  - unfold generic_match_from in Href. prog_nf in Href.
    unfold_loop in Href. prog_nf in Href.
    unfold generic_match_loop_body in Href at 1. prog_nf in Href.
    safe_choice_r Href. unfold match_loop_body in Href at 1. prog_nf in Href.
    safe_choice_r Href. unfold break in Href. prog_nf in Href. exact Href.
Qed.

Lemma search_cursor_right : forall text patn cut p remembered pos memory,
  0 <= cut -> pos+Zlength patn <= Zlength text ->
  search_cursor text patn cut p remembered pos memory ->
  search_right_cursor text patn cut p remembered pos memory (Z.max cut memory).
Proof.
  intros text patn cut p remembered pos memory Hcut Hw [mode [q [Hc Href]]].
  exists mode,q; split; [exact Hc|]. split; [exact Href|].
  intros X Hexec. specialize (Href X Hexec). destruct mode; simpl in *.
  - unfold generic_match_periodic_from in Href. prog_nf in Href.
    unfold_loop in Href. prog_nf in Href.
    unfold generic_match_periodic_loop_body in Href at 1. prog_nf in Href.
    safe_choice_r Href. unfold match_periodic_loop_body in Href at 1. prog_nf in Href.
    safe_choice_l Href. unfold generic_match_periodic_from_right, generic_match_periodic_from.
    prog_nf. eapply safeExec_proequiv; [|exact Href].
    apply common_step_equiv; intros [[pos2 mem2]|res]; simpl; reflexivity.
  - destruct Hc as [-> _]. rewrite Z.max_l by lia.
    unfold generic_match_from in Href. prog_nf in Href.
    unfold_loop in Href. prog_nf in Href.
    unfold generic_match_loop_body in Href at 1. prog_nf in Href.
    safe_choice_r Href. unfold match_loop_body in Href at 1. prog_nf in Href.
    safe_choice_l Href.
    eapply safeExec_proequiv; [|exact Href].
    unfold generic_match_from_right. apply common_step_equiv. intro a.
    unfold generic_match_after_right. rewrite bind_choice_equiv.
    apply choice_case_equiv;
      [unfold generic_match_from_left, generic_match_after_left, generic_match_from
      |unfold generic_match_from].
    + prog_nf. apply common_step_equiv. intros _.
      rewrite bind_assoc. apply common_step_equiv. intro b.
      rewrite bind_choice_equiv.
      apply choice_case_equiv; unfold break, continue; prog_nf; reflexivity.
    + unfold continue. prog_nf; reflexivity.
Qed.

Lemma search_right_step : forall text patn cut p remembered pos memory k,
  k < Zlength patn -> match_cond text patn pos k ->
  search_right_cursor text patn cut p remembered pos memory k ->
  search_right_cursor text patn cut p remembered pos memory (k+1).
Proof.
  intros text patn cut p remembered pos memory k Hk He [mode [q [Hc [Hb Hr]]]].
  exists mode,q; split; [exact Hc|]. split; [exact Hb|].
  intros X Hexec. specialize (Hr X Hexec). destruct mode; simpl in *.
  - unfold generic_match_periodic_from_right, match_periodic_from_right in *.
    unfold match_right in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
    unfold match_right_f in Hr at 1. prog_nf in Hr. safe_choice_l Hr; try lia; try solve [split; [lia|assumption]].
    unfold continue in Hr. prog_nf in Hr. unfold match_right. prog_nf. exact Hr.
  - unfold generic_match_from_right in *.
    unfold match_right in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
    unfold match_right_f in Hr at 1. prog_nf in Hr. safe_choice_l Hr; try lia; try solve [split; [lia|assumption]].
    unfold continue in Hr. prog_nf in Hr. unfold match_right. prog_nf. exact Hr.
Qed.

Lemma search_right_mismatch : forall text patn cut p remembered pos memory k,
  k < Zlength patn -> ~match_cond text patn pos k ->
  search_right_cursor text patn cut p remembered pos memory k ->
  search_cursor text patn cut p remembered (pos+k-cut+1) 0.
Proof.
  intros text patn cut p remembered pos memory k Hk He [mode [q [Hc [Hb Hr]]]].
  exists mode,q; split; [destruct mode; simpl in *; tauto|].
  intros X Hexec. specialize (Hr X Hexec). destruct mode; simpl in *.
  - unfold generic_match_periodic_from_right, match_periodic_from_right in Hr.
    unfold match_right in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
    unfold match_right_f in Hr at 1. prog_nf in Hr. safe_choice_r Hr; try lia; try (left; lia).
    unfold break in Hr. prog_nf in Hr.
    unfold match_periodic_after_right in Hr. prog_nf in Hr. safe_choice_r Hr; try lia; try (left; lia).
    unfold continue in Hr. prog_nf in Hr. exact Hr.
  - unfold generic_match_from_right in Hr.
    unfold match_right in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
    unfold match_right_f in Hr at 1. prog_nf in Hr. safe_choice_r Hr; try lia; try (left; lia).
    unfold break in Hr. prog_nf in Hr.
    unfold generic_match_after_right in Hr. prog_nf in Hr. safe_choice_r Hr; try lia; try (left; lia). exact Hr.
Qed.

Lemma search_right_end : forall text patn cut p remembered pos memory,
  search_right_cursor text patn cut p remembered pos memory (Zlength patn) ->
  search_left_cursor text patn cut p remembered pos memory cut.
Proof.
  intros text patn cut p remembered pos memory [mode [q [Hc [Hb Hr]]]].
  exists mode,q; split; [exact Hc|]. split; [exact Hb|].
  intros X Hexec. specialize (Hr X Hexec). destruct mode; simpl in *.
  - unfold generic_match_periodic_from_right, match_periodic_from_right in Hr.
    unfold match_right in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
    unfold match_right_f in Hr at 1. prog_nf in Hr. safe_choice_r Hr; try lia; try (left; lia).
    unfold break in Hr. prog_nf in Hr.
    unfold match_periodic_after_right in Hr. prog_nf in Hr. safe_choice_l Hr; try lia; try solve [split; [lia|assumption]].
    unfold generic_match_periodic_from_left. exact Hr.
  - unfold generic_match_from_right in Hr.
    unfold match_right in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
    unfold match_right_f in Hr at 1. prog_nf in Hr. safe_choice_r Hr; try lia; try (left; lia).
    unfold break in Hr. prog_nf in Hr.
    unfold generic_match_after_right in Hr. prog_nf in Hr. safe_choice_l Hr; try lia; try solve [split; [lia|assumption]]. exact Hr.
Qed.

Lemma search_left_step : forall text patn cut p remembered pos memory k,
  memory < k -> match_cond text patn pos (k-1) ->
  search_left_cursor text patn cut p remembered pos memory k ->
  search_left_cursor text patn cut p remembered pos memory (k-1).
Proof.
  intros text patn cut p remembered pos memory k Hk He [mode [q [Hc [Hb Hr]]]].
  exists mode,q; split; [exact Hc|]. split; [exact Hb|].
  intros X Hexec. specialize (Hr X Hexec). destruct mode; simpl in *.
  - unfold generic_match_periodic_from_left, match_periodic_from_left in *.
    unfold match_left in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
    unfold match_left_f in Hr at 1. prog_nf in Hr. safe_choice_l Hr; try lia; try solve [split; [lia|assumption]].
    unfold continue in Hr. prog_nf in Hr. unfold match_left. prog_nf. exact Hr.
  - destruct Hc as [Hmem _].
    unfold generic_match_from_left in *.
    unfold match_left in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
    unfold match_left_f in Hr at 1. prog_nf in Hr. safe_choice_l Hr; try lia; try solve [split; [lia|assumption]].
    unfold continue in Hr. prog_nf in Hr. unfold match_left. prog_nf. exact Hr.
Qed.

Lemma search_left_found : forall text patn cut p remembered pos memory k,
  k <= memory -> search_left_cursor text patn cut p remembered pos memory k ->
  refines (two_way_generic_prog text patn) (ret (Some pos)).
Proof.
  intros text patn cut p remembered pos memory k Hk [mode [q [Hc [Hb Hr]]]] X Hexec.
  specialize (Hr X Hexec). destruct mode; simpl in *.
  - unfold generic_match_periodic_from_left, match_periodic_from_left in Hr.
    unfold match_left in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
    unfold match_left_f in Hr at 1. prog_nf in Hr. safe_choice_r Hr; try lia; try (left; lia).
    unfold break in Hr. prog_nf in Hr.
    unfold match_periodic_after_left in Hr. prog_nf in Hr. safe_choice_l Hr; try lia; try solve [split; [lia|assumption]].
    unfold break in Hr. prog_nf in Hr. exact Hr.
  - destruct Hc as [Hmem _].
    unfold generic_match_from_left in Hr.
    unfold match_left in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
    unfold match_left_f in Hr at 1. prog_nf in Hr. safe_choice_r Hr; try lia; try (left; lia).
    unfold break in Hr. prog_nf in Hr.
    unfold generic_match_after_left in Hr. prog_nf in Hr. safe_choice_l Hr; try lia; try solve [split; [lia|assumption]]. exact Hr.
Qed.

Lemma search_left_mismatch : forall text patn cut p remembered pos memory k,
  memory < k -> ~match_cond text patn pos (k-1) ->
  pos+Zlength patn <= Zlength text -> valid_skip text patn pos p ->
  search_left_cursor text patn cut p remembered pos memory k ->
  search_cursor text patn cut p remembered (pos+p) remembered.
Proof.
  intros text patn cut p remembered pos memory k Hk He Hw Hskip [mode [q [Hc [Hb Hr]]]].
  exists mode,q; split.
  - destruct mode; simpl in *; tauto.
  - intros X Hexec. destruct mode; simpl in *.
    + destruct Hc as [-> ->]. specialize (Hr X Hexec).
      unfold generic_match_periodic_from_left, match_periodic_from_left in Hr.
      unfold match_left in Hr. prog_nf in Hr. unfold_loop in Hr. prog_nf in Hr.
      unfold match_left_f in Hr at 1. prog_nf in Hr. safe_choice_r Hr; try lia; try (left; lia).
      unfold break in Hr. prog_nf in Hr.
      unfold match_periodic_after_left in Hr. prog_nf in Hr. safe_choice_r Hr; try lia; try (left; lia).
      unfold continue in Hr. prog_nf in Hr. exact Hr.
    + specialize (Hb X Hexec). eapply generic_valid_skip_continuation; eauto.
Qed.

Lemma search_left_result : forall text patn base cut p remembered pos memory k,
  patn <> nil -> k <= memory ->
  search_left_cursor text patn cut p remembered pos memory k ->
  strstr_rel_lib.strstr_result text patn base (base+pos).
Proof.
  intros. change (strstr_rel_lib.strstr_result text patn base (result_pointer base (Some pos))).
  apply two_way_generic_refinement_strstr_result; [assumption|].
  eapply search_left_found; eauto.
Qed.

Lemma search_cursor_result_none : forall text patn base cut p remembered pos memory,
  patn <> nil -> pos+Zlength patn > Zlength text ->
  search_cursor text patn cut p remembered pos memory ->
  strstr_rel_lib.strstr_result text patn base 0.
Proof.
  intros. change (strstr_rel_lib.strstr_result text patn base (result_pointer base None)).
  apply two_way_generic_refinement_strstr_result; [assumption|].
  eapply search_cursor_end; eauto.
Qed.

Global Opaque search_cursor search_right_cursor search_left_cursor.
