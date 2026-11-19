From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE.stdlib.musl.monad Require Import two_way_rel_lib two_way_list_lemmas two_way_critical_factorization_theorem factorization_refinement.
From SetsClass Require Import SetsClass.
Import SetsNotation.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope sets.
Local Transparent refines scan_done factorization_done.

(* Use the framework's existing result_state as a concrete postcondition.
   No replacement predicate for safeExec is introduced. *)
Lemma safeExec_result_state_refines {A} (initial residual : program unit A) :
  safeExec ATrue residual (result_state ATrue initial) ->
  refines initial residual.
Proof.
  intros Hr X [s [HP HX]]. destruct s.
  eapply safeExec_X_subset; [|exact Hr].
  intros a s [s0 [_ Hrun]]. destruct s0.
  destruct HX as [_ Hpost]. exact (Hpost a s Hrun).
Qed.

Lemma scan_safeExec_init patn direction :
  safeExec ATrue (scan_initial patn direction)
    (result_state ATrue (scan_initial patn direction)).
Proof.
  apply safeExec_result_state. exists tt; split; [exact I|].
  unfold scan_initial, scan_cmp.
  destruct (Z.eq_dec direction 1).
  - exact ((proj2 (maxsuf_fwd_sound patn)) tt I).
  - exact ((proj2 (maxsuf_rev_sound patn)) tt I).
Qed.

Lemma scan_safeExec_step patn direction cut j k p X :
  safeExec ATrue (maxsuf_cal (scan_cmp direction) patn (cut-1,j,k,p)) X ->
  1 <= k -> j+k < Zlength patn -> 0 <= cut-1+k < Zlength patn ->
  match scan_cmp direction (Znth (j+k) patn 0) (Znth (cut-1+k) patn 0) with
  | Eq => if Z.eq_dec k p
          then safeExec ATrue (maxsuf_cal (scan_cmp direction) patn (cut-1,j+p,1,p)) X
          else safeExec ATrue (maxsuf_cal (scan_cmp direction) patn (cut-1,j,k+1,p)) X
  | Lt => safeExec ATrue (maxsuf_cal (scan_cmp direction) patn (cut-1,j+k,1,j+k-(cut-1))) X
  | Gt => safeExec ATrue (maxsuf_cal (scan_cmp direction) patn (j,j+1,1,1)) X
  end.
Proof.
  intros Hsafe Hk Hguard Hindex.
  unfold maxsuf_cal in Hsafe; unfold_loop in Hsafe.
  unfold maxsuf_cal_body in Hsafe at 1.
  safe_choice_r Hsafe; try lia.
  destruct (scan_cmp direction (Znth (j+k) patn 0) (Znth (cut-1+k) patn 0));
    try (destruct (Z.eq_dec k p); [safe_choice_l Hsafe |safe_choice_r Hsafe]);
    try lia; unfold continue in Hsafe; prog_nf in Hsafe; exact Hsafe.
  all: try lia.
Qed.

Lemma scan_safeExec_exit patn direction cut j k p X :
  safeExec ATrue (maxsuf_cal (scan_cmp direction) patn (cut-1,j,k,p)) X ->
  Zlength patn = j+k ->
  safeExec ATrue (ret (cut-1,p)) X.
Proof.
  intros Hsafe Hexit.
  unfold maxsuf_cal in Hsafe; unfold_loop in Hsafe.
  unfold maxsuf_cal_body in Hsafe at 1.
  safe_choice_l Hsafe; try lia.
  unfold break in Hsafe. prog_nf in Hsafe. exact Hsafe.
Qed.

Lemma scans_safeExec_done patn cf pf cr pr :
  patn <> nil ->
  safeExec ATrue (ret (cf-1,pf)) (result_state ATrue (maxsuf_fwd patn)) ->
  safeExec ATrue (ret (cr-1,pr)) (result_state ATrue (maxsuf_rev patn)) ->
  safeExec ATrue
    (ret (Z.max cf cr, if Z_lt_dec cf cr then pr else pf))
    (result_state ATrue (critical_factorization_prog patn)).
Proof.
  intros Hne Hf Hr.
  pose proof (safeExec_result_state_refines _ _ Hf) as Hfd.
  pose proof (safeExec_result_state_refines _ _ Hr) as Hrd.
  assert (Hfs : scan_done patn 1 cf pf).
  { unfold scan_done, scan_initial, scan_cmp.
    destruct (Z.eq_dec 1 1); [exact Hfd|lia]. }
  assert (Hrs : scan_done patn 0 cr pr).
  { unfold scan_done, scan_initial, scan_cmp.
    destruct (Z.eq_dec 0 1); [lia|exact Hrd]. }
  pose proof (scans_factorization_done patn cf pf cr pr Hne Hfs Hrs) as Hcf.
  apply Hcf. apply safeExec_result_state.
  exists tt; split; [exact I|].
  exact ((proj2 (critical_factorization_prog_match_sound patn Hne)) tt I).
Qed.

Lemma factorization_safeExec_done patn cut p :
  safeExec ATrue (ret (cut,p))
    (result_state ATrue (critical_factorization_prog patn)) ->
  factorization_done patn cut p.
Proof. apply safeExec_result_state_refines. Qed.

Lemma maxsuf_result_bounds patn cmp cut p :
  patn <> nil -> Cmp Z cmp -> maxsuf_prop patn cmp cut p ->
  0 <= cut < Zlength patn /\ 0 < p /\ cut+p <= Zlength patn.
Proof.
  intros Hne Hcmp Hmax.
  destruct (minimal_period_existence patn Hne) as [mp [Hmpbound Hmp]].
  pose proof (maxsuf_prop_l_less_min_period patn Hne cmp cut p mp Hcmp Hmp Hmax) as [Hcut Hbound].
  destruct Hmax as [_ [[Hp _] _]]. repeat split; lia.
Qed.

Lemma maxsuf_choose_bounds patn ms msr p pr :
  patn <> nil -> forward_maxsuf_prop patn ms p -> reverse_maxsuf_prop patn msr pr ->
  Hoare ATrue (maxsuf_choose_with_ms ms msr p pr)
    (fun r _ => 0 <= fst r < Zlength patn /\ 0 < snd r /\ fst r+snd r <= Zlength patn).
Proof.
  intros Hne Hf Hr.
  pose proof (maxsuf_result_bounds patn Z.compare (ms+1) p Hne Cmp_Zcompare Hf) as Hfb.
  pose proof (maxsuf_result_bounds patn Z_compare_rev (msr+1) pr Hne Cmp_Zcompare_rev Hr) as Hrb.
  unfold maxsuf_choose_with_ms. hoare_auto.
Qed.

Lemma factorization_program_bounds patn : patn <> nil ->
  Hoare ATrue (critical_factorization_prog patn)
    (fun r _ => 0 <= fst r < Zlength patn /\ 0 < snd r /\ fst r+snd r <= Zlength patn).
Proof.
  intros Hne. unfold critical_factorization_prog.
  eapply Hoare_bind.
  - apply maxsuf_fwd_sound.
  - intros [ms p].
    eapply Hoare_bind with (Q := fun r _ =>
      forward_maxsuf_prop patn ms p /\ reverse_maxsuf_prop patn (fst r) (snd r)).
    + unfold Hoare; split.
      * intros r s1 s2 Hf Hrun. split; [exact Hf|].
        exact ((proj1 (maxsuf_rev_sound patn)) r s1 s2 I Hrun).
      * intros s Hf Herr. exact ((proj2 (maxsuf_rev_sound patn)) s I Herr).
    + intros [msr pr]. unfold Hoare; split.
      * intros r s1 s2 [Hf Hr] Hrun.
        exact ((proj1 (maxsuf_choose_bounds patn ms msr p pr Hne Hf Hr)) r s1 s2 I Hrun).
      * intros s [Hf Hr] Herr.
        exact ((proj2 (maxsuf_choose_bounds patn ms msr p pr Hne Hf Hr)) s I Herr).
Qed.

Lemma factorization_safeExec_bounds patn cut p :
  patn <> nil ->
  safeExec ATrue (ret (cut,p)) (result_state ATrue (critical_factorization_prog patn)) ->
  0 <= cut < Zlength patn /\ 0 < p /\ cut+p <= Zlength patn.
Proof.
  intros Hne Hsafe.
  exact (refines_return_sound (critical_factorization_prog patn) (cut,p)
    (fun r => 0 <= fst r < Zlength patn /\ 0 < snd r /\ fst r+snd r <= Zlength patn)
    (factorization_program_bounds patn Hne) (safeExec_result_state_refines _ _ Hsafe)).
Qed.
