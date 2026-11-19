From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE.stdlib.musl.monad Require Import
  two_way_rel_lib two_way_list_lemmas two_way_critical_factorization_theorem.
From SetsClass Require Import SetsClass.
Import SetsNotation.
Local Open Scope Z_scope.
Local Open Scope monad.
Local Open Scope sets.

(* A residual-program relation quantified over every continuation. *)
Definition refines {A : Type} (before after : program unit A) : Prop :=
  forall X, safeExec ATrue before X -> safeExec ATrue after X.

Lemma refines_refl {A} (c : program unit A) : refines c c.
Proof. firstorder. Qed.

Lemma refines_return_sound {A} (c : program unit A) r (Q : A -> Prop) :
  Hoare ATrue c (fun a _ => Q a) -> refines c (ret r) -> Q r.
Proof.
  intros Hsound Hr.
  pose proof (Hoare_safeexec_imply_compose ATrue ATrue c
    (fun a _ => Q a) r Hsound (Hr _) ltac:(exists tt; exact I))
    as [s [Hq _]]. exact Hq.
Qed.

Definition scan_cmp (direction : Z) :=
  if Z.eq_dec direction 1 then Z.compare else Z_compare_rev.
Definition scan_initial (patn : list Z) (direction : Z) :=
  maxsuf_cal (scan_cmp direction) patn (-1, 0, 1, 1).
Definition scan_refines (patn : list Z) (direction cut j k p : Z) :=
  j + k <= Zlength patn /\
  refines (scan_initial patn direction)
    (maxsuf_cal (scan_cmp direction) patn (cut - 1, j, k, p)).
Definition scan_done (patn : list Z) (direction cut p : Z) :=
  refines (scan_initial patn direction) (ret (cut - 1, p)).
Definition factorization_done (patn : list Z) (cut p : Z) :=
  refines (critical_factorization_prog patn) (ret (cut, p)).

Lemma scan_refines_init patn direction :
  1 <= Zlength patn -> scan_refines patn direction 0 0 1 1.
Proof. intros. split; [lia|apply refines_refl]. Qed.

Lemma scan_refines_step patn direction cut j k p :
  scan_refines patn direction cut j k p ->
  1 <= k -> j + k < Zlength patn -> 0 <= cut - 1 + k < Zlength patn ->
  match scan_cmp direction (Znth (j+k) patn 0) (Znth (cut-1+k) patn 0) with
  | Eq => if Z.eq_dec k p
          then scan_refines patn direction cut (j+p) 1 p
          else scan_refines patn direction cut j (k+1) p
  | Lt => scan_refines patn direction cut (j+k) 1 (j+k-(cut-1))
  | Gt => scan_refines patn direction (j+1) (j+1) 1 1
  end.
Proof.
  intros [Hbound Hr] Hk Hguard Hindex.
  destruct (scan_cmp direction (Znth (j+k) patn 0)
    (Znth (cut-1+k) patn 0)) eqn:Hcmp.
  - destruct (Z.eq_dec k p) as [Heq|Hne]; split; try lia;
      intros X Hsafe; specialize (Hr X Hsafe);
      unfold maxsuf_cal in *; unfold_loop in Hr;
      unfold maxsuf_cal_body in Hr at 1;
      safe_choice_r Hr; try lia; rewrite Hcmp in Hr.
    + safe_choice_l Hr; try lia. unfold continue in Hr. prog_nf in Hr. exact Hr.
    + safe_choice_r Hr; try lia. unfold continue in Hr. prog_nf in Hr. exact Hr.
  - split; [lia|]. intros X Hsafe. specialize (Hr X Hsafe).
    unfold maxsuf_cal in *; unfold_loop in Hr.
    unfold maxsuf_cal_body in Hr at 1.
    safe_choice_r Hr; try lia. rewrite Hcmp in Hr.
    unfold continue in Hr. prog_nf in Hr. exact Hr.
  - split; [lia|]. intros X Hsafe. specialize (Hr X Hsafe).
    unfold maxsuf_cal in *; unfold_loop in Hr.
    unfold maxsuf_cal_body in Hr at 1.
    safe_choice_r Hr; try lia. rewrite Hcmp in Hr.
    unfold continue in Hr. prog_nf in Hr.
    replace (j+1-1) with j by lia. exact Hr.
Qed.

Lemma scan_refines_exit patn direction cut j k p :
  scan_refines patn direction cut j k p ->
  Zlength patn <= j+k -> scan_done patn direction cut p.
Proof.
  intros [Hbound Hr] Hexit X Hsafe. specialize (Hr X Hsafe).
  unfold maxsuf_cal in Hr. unfold_loop in Hr.
  unfold maxsuf_cal_body in Hr at 1.
  safe_choice_l Hr; try lia. unfold break in Hr. prog_nf in Hr. exact Hr.
Qed.

Lemma refines_bind_return {A B} (c : program unit A) r
    (f : A -> program unit B) :
  refines c (ret r) -> refines (bind c f) (f r).
Proof.
  intros Hr X Hsafe.
  apply safeExec_bind in Hsafe as [Y [Hc Hnext]].
  apply (Hnext ATrue r). apply Hr. exact Hc.
Qed.

Lemma scan_done_fwd patn cut p :
  scan_done patn 1 cut p -> refines (maxsuf_fwd patn) (ret (cut-1,p)).
Proof. unfold scan_done, scan_initial, scan_cmp, maxsuf_fwd.
  destruct (Z.eq_dec 1 1); [auto|lia]. Qed.
Lemma scan_done_rev patn cut p :
  scan_done patn 0 cut p -> refines (maxsuf_rev patn) (ret (cut-1,p)).
Proof. unfold scan_done, scan_initial, scan_cmp, maxsuf_rev, Z_compare_rev.
  destruct (Z.eq_dec 0 1); [lia|auto]. Qed.

Lemma scan_done_equal_cut_period patn cut p pr :
  patn <> nil -> scan_done patn 1 cut p -> scan_done patn 0 cut pr -> p = pr.
Proof.
  intros Hne Hf Hr.
  pose proof (refines_return_sound _ _ _ (maxsuf_fwd_sound patn)
    (scan_done_fwd _ _ _ Hf)) as Hfp.
  pose proof (refines_return_sound _ _ _ (maxsuf_rev_sound patn)
    (scan_done_rev _ _ _ Hr)) as Hrp.
  unfold forward_maxsuf_prop, reverse_maxsuf_prop, maxsuf_ret_prop in *.
  cbn in Hfp, Hrp.
  destruct Hfp as [_ [Hp Hminp]], Hrp as [_ [Hpr Hminpr]].
  specialize (Hminp pr Hpr). specialize (Hminpr p Hp). lia.
Qed.

Lemma scans_factorization_done patn cutf pf cutr pr :
  patn <> nil ->
  scan_done patn 1 cutf pf -> scan_done patn 0 cutr pr ->
  factorization_done patn (Z.max cutf cutr)
    (if Z_lt_dec cutf cutr then pr else pf).
Proof.
  intros Hne Hf Hr X Hsafe.
  unfold critical_factorization_prog in Hsafe.
  pose proof (refines_bind_return _ _ _ (scan_done_fwd _ _ _ Hf) X Hsafe) as Hnext.
  cbn beta iota zeta in Hnext.
  pose proof (refines_bind_return _ _ _ (scan_done_rev _ _ _ Hr) X Hnext) as Hchoose.
  cbn beta iota zeta in Hchoose.
  unfold maxsuf_choose_with_ms in Hchoose.
  destruct (Z_lt_dec cutf cutr) as [Hlt|Hge].
  - rewrite Z.max_r by lia.
    safe_choice_r Hchoose; try lia.
    replace (cutr-1+1) with cutr in Hchoose by lia. exact Hchoose.
  - rewrite Z.max_l by lia.
    destruct (Z.eq_dec cutf cutr) as [Heq|Hnecut].
    + subst cutr.
      pose proof (scan_done_equal_cut_period _ _ _ _ Hne Hf Hr) as Heqper.
      subst pr. safe_choice_r Hchoose; try lia.
      replace (cutf-1+1) with cutf in Hchoose by lia. exact Hchoose.
    + safe_choice_l Hchoose; try lia.
      replace (cutf-1+1) with cutf in Hchoose by lia. exact Hchoose.
Qed.

Lemma factorization_done_match_sound patn cut p :
  patn <> nil -> factorization_done patn cut p ->
  critical_factorization_match_prop patn cut p.
Proof.
  intros Hne Href.
  pose proof (refines_return_sound _ _ _
    (critical_factorization_prog_match_sound patn Hne) Href) as H.
  exact H.
Qed.

(* Preserve the arbitrary continuation into the original search phase. *)
Lemma factorization_done_search_continuation text patn cut p :
  factorization_done patn cut p ->
  refines (two_way_generic_prog text patn)
    (generic_match_phase text patn cut p).
Proof.
  intros Href.
  exact (refines_bind_return (critical_factorization_prog patn) (cut,p)
    (fun '(l,q) => generic_match_phase text patn l q) Href).
Qed.

(* Keep VC automation at the refinement interface; the step lemmas above
   are the only place that unfolds the residual-program certificates. *)
Global Opaque refines scan_refines scan_done factorization_done.
