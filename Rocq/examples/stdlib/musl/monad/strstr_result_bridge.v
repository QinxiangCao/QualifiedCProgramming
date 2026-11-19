From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE.stdlib.musl Require Import strstr_rel_lib.
From SimpleC.EE.stdlib.musl.monad Require Import
  two_way_rel_lib two_way_match_generic.
Local Open Scope Z_scope.

(* Keep the original option-valued postcondition unchanged.  Only the C
   boundary converts a logical position to a pointer, or None to NULL. *)
Definition result_pointer (base : Z) (res : option Z) : Z :=
  match res with Some pos => base + pos | None => 0 end.

Lemma nonempty_sublist_match_bounds :
  forall (hay needle : list Z) pos,
    needle <> nil ->
    sublist pos (pos + Zlength needle) hay = needle ->
    0 <= pos /\ pos + Zlength needle <= Zlength hay.
Proof.
  intros hay needle pos Hne Heq.
  assert (Hlen : 0 < Zlength needle).
  { rewrite Zlength_correct. destruct needle; simpl in *; [contradiction | lia]. }
  pose proof (f_equal (@length Z) Heq) as Hlength.
  unfold sublist in Hlength.
  rewrite length_skipn, length_firstn in Hlength.
  rewrite Zlength_correct in *.
  destruct (Nat.min_spec (Z.to_nat (pos + Z.of_nat (length needle)))
    (length hay)) as [[Hmin He] | [Hmin He]]; rewrite He in Hlength;
    rewrite Zlength_correct; lia.
Qed.

Lemma match_post_strstr_result :
  forall (hay needle : list Z) base res,
    needle <> nil ->
    match_post hay needle res ->
    strstr_result hay needle base (result_pointer base res).
Proof.
  intros hay needle base [pos |] Hne Hpost.
  - destruct Hpost as [Hbefore Heq].
    pose proof (nonempty_sublist_match_bounds hay needle pos Hne Heq) as Hb.
    right. exists pos. split; [|reflexivity].
    split.
    + unfold substring_at. tauto.
    + intros j Hj [_ [_ Hmatch]]. exact (Hbefore j Hj Hmatch).
  - left. split; [reflexivity|].
    intros pos [Hpos [Hend Heq]].
    assert (Hlen : 0 < Zlength needle).
    { rewrite Zlength_correct. destruct needle; simpl in *; [contradiction | lia]. }
    exact (Hpost pos ltac:(lia) Heq).
Qed.

Theorem two_way_generic_prog_strstr_result :
  forall (hay needle : list Z) base,
    Hoare (fun _ => needle <> nil) (two_way_generic_prog hay needle)
      (fun res _ => strstr_result hay needle base (result_pointer base res)).
Proof.
  intros hay needle base.
  apply Hoare_stateless. intro Hne.
  eapply Hoare_cons_post with (Q := fun res _ => match_post hay needle res).
  - intros res s Hpost. apply match_post_strstr_result; assumption.
  - eapply Hoare_cons_pre; [|apply two_way_generic_prog_sound].
    intros; exact Hne.
Qed.

(* This is the continuation interface that the concrete C refinement must
   establish.  The algorithmic conclusion comes from the original soundness
   theorem, including its factorization and search proofs. *)
Theorem two_way_generic_refinement_strstr_result :
  forall (hay needle : list Z) base res,
    needle <> nil ->
    (forall X : option Z -> unit -> Prop,
      safeExec ATrue (two_way_generic_prog hay needle) X ->
      safeExec ATrue (ret res) X) ->
    strstr_result hay needle base (result_pointer base res).
Proof.
  intros hay needle base res Hne Href.
  assert (Hsound : Hoare ATrue (two_way_generic_prog hay needle)
    (fun r _ => strstr_result hay needle base (result_pointer base r))).
  { eapply Hoare_cons_pre; [|apply two_way_generic_prog_strstr_result].
    intros; exact Hne. }
  pose proof (Hoare_safeexec_imply_compose ATrue ATrue
    (two_way_generic_prog hay needle)
    (fun r _ => strstr_result hay needle base (result_pointer base r))
    res Hsound (Href _) ltac:(exists tt; exact I)) as [s [Hresult _]].
  exact Hresult.
Qed.
