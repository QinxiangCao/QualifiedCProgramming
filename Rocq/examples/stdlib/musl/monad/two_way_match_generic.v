Require Import Coq.ZArith.ZArith Coq.micromega.Psatz Coq.Lists.List.
Require Import SetsClass.SetsClass ListLib.Base.Positional ListLib.General.Length.
From MonadLib Require Export MonadLib.
Export StateRelMonadErr MonadNotation.
From SimpleC.EE.stdlib.musl.monad Require Import two_way_rel_lib two_way_list_lemmas.
From SimpleC.EE.stdlib.musl.monad Require Import two_way_critical_factorization_theorem two_way_match.
Import ListNotations SetsNotation.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sets.
Local Open Scope monad.

Lemma generic_match_from_correct :
  forall (text patn : list Z) (l p pos : Z),
    patn <> nil -> critical_factorization_prop patn l p ->
    match_inv text patn pos ->
    Hoare (fun _ => True) (generic_match_from text patn l p pos)
      (fun res _ => match_post text patn res).
Proof.
  intros text patn l p pos Hn Hc Hi.
  unfold generic_match_from.
  eapply Hoare_cons_pre with (P := fun _ => match_inv text patn pos).
  { intros; exact Hi. }
  apply (Hoare_repeat_break _ (fun pos _ => match_inv text patn pos)).
  intro x. unfold generic_match_loop_body. apply Hoare_choice.
  - apply Hoare_assume_bind. intro Hbound.
    apply Hoare_any_bind. intro n.
    apply Hoare_assume_bind. intros [Hnpositive [Hend Hskip]].
    unfold continue. apply Hoare_ret. intros st [Hx Hbefore].
    constructor; [lia |].
    intros j Hj. destruct (Z_lt_ge_dec j x).
    + apply Hbefore; lia.
    + apply Hskip; lia.
  - eapply Hoare_cons_post with
      (Q := fun r _ =>
        (match r with by_continue x' => match_inv text patn x' | by_break _ => True end) /\
        match_post_break text patn r).
    + intros [x'|r] st [Hcontinue Hbreak]; assumption.
    + apply Hoare_conj.
      * apply match_proof_continue_pre; assumption.
      * apply match_proof_break_pre; assumption.
Qed.

Lemma generic_match_periodic_from_correct :
  forall (text patn : list Z) (l p pos memory : Z),
    patn <> nil -> critical_factorization_prop patn l p ->
    repetitive_split patn l p -> periodic_match_inv text patn l p pos memory ->
    Hoare (fun _ => True) (generic_match_periodic_from text patn l p pos memory)
      (fun res _ => match_post text patn res).
Proof.
  intros text patn l p pos memory Hn Hc Hr Hi.
  unfold generic_match_periodic_from.
  eapply Hoare_cons_pre with
    (P := fun _ => periodic_match_inv text patn l p pos memory).
  { intros; exact Hi. }
  refine (Hoare_repeat_break (generic_match_periodic_loop_body text patn l p)
    (fun s _ => periodic_match_inv text patn l p (fst s) (snd s))
    (fun res _ => match_post text patn res) _ (pos, memory)).
  intros [x m]. unfold generic_match_periodic_loop_body. apply Hoare_choice.
  - apply Hoare_assume_bind. intro Hbound.
    apply Hoare_any_bind. intro n.
    apply Hoare_assume_bind. intros [Hpositive [Hend Hskip]].
    unfold continue. apply Hoare_ret. intros st Hinv. simpl in *.
    destruct Hinv as [[Hx Hbefore] Hrange Hprefix].
    constructor.
    + constructor; [lia |].
      intros j Hj. destruct (Z_lt_ge_dec j x).
      * apply Hbefore; lia.
      * apply Hskip; lia.
    + pose proof (Zlength_nonneg patn); lia.
    + rewrite !Zsublist_nil by lia. reflexivity.
  - eapply Hoare_cons_post with
      (Q := fun r _ => periodic_match_post_continue text patn l p r /\
                       periodic_match_post_break text patn r).
    + intros [[x' m']|r] st [Hcontinue Hbreak]; assumption.
    + apply Hoare_conj.
      * apply periodic_match_proof_continue_pre; assumption.
      * apply periodic_match_proof_break_pre; assumption.
Qed.

Lemma generic_match_phase_correct :
  forall (text patn : list Z) (l p : Z),
    patn <> nil -> critical_factorization_match_prop patn l p ->
    Hoare (fun _ => True) (generic_match_phase text patn l p)
      (fun res _ => match_post text patn res).
Proof.
  intros text patn l p Hn [Hc Hnonrep].
  unfold generic_match_phase. apply Hoare_choice.
  - apply Hoare_assume_bind. intro Hr.
    apply generic_match_periodic_from_correct; auto using periodic_match_inv_init.
  - apply Hoare_assume_bind. intro Hr.
    apply generic_match_from_correct; auto using match_inv_init.
Qed.

Theorem two_way_generic_prog_sound :
  forall (text patn : list Z),
    Hoare (fun _ => patn <> nil) (two_way_generic_prog text patn)
      (fun res _ => match_post text patn res).
Proof.
  intros text patn. apply Hoare_stateless. intro Hn.
  unfold two_way_generic_prog.
  eapply Hoare_bind.
  - apply critical_factorization_prog_match_sound; exact Hn.
  - intros [l p]. simpl. apply Hoare_stateless. intro Hc.
    apply generic_match_phase_correct; assumption.
Qed.
