Require Export SimpleC.EE.stdlib.glibc.horspool_memmem_lib.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From MonadLib Require Export MonadLib.
Export StateRelMonadErr MonadNotation.
Local Open Scope Z_scope.
Local Open Scope monad.

Definition hp_valid_skip (bytes : list Z)
    (hayoff haylen needleoff needlelen position next : Z) : Prop :=
  position < next /\
  forall candidate, position <= candidate < next ->
    ~ hp_match_at bytes hayoff haylen needleoff needlelen candidate.

Definition hp_search_body (bytes : list Z)
    (hayoff haylen needleoff needlelen position : Z)
    : program unit (CntOrBrk Z (option Z)) :=
  choice
    (assume!! (haylen < position + needlelen);; break None)
    (choice
      (assume!! (hp_match_at bytes hayoff haylen needleoff needlelen position);;
       break (Some position))
      (assume!! (position + needlelen <= haylen);;
       next <- any Z;;
       assume!! (hp_valid_skip bytes hayoff haylen needleoff needlelen position next);;
       continue next)).

Definition hp_search_from (bytes : list Z)
    (hayoff haylen needleoff needlelen position : Z) : program unit (option Z) :=
  repeat_break (hp_search_body bytes hayoff haylen needleoff needlelen) position.

Definition hp_search_post (bytes : list Z)
    (hayoff haylen needleoff needlelen : Z) (result : option Z) : Prop :=
  match result with
  | None => forall position, ~ hp_match_at bytes hayoff haylen needleoff needlelen position
  | Some position =>
      hp_match_at bytes hayoff haylen needleoff needlelen position /\
      hp_no_match_before bytes hayoff haylen needleoff needlelen position
  end.

Definition hp_ptr_result (base result : Z) : option Z :=
  if Z.eq_dec result 0 then None else Some (result - base).

Require Import Coq.micromega.Psatz.

(* Helper lemmas migrated from merged_proof_manual.v. *)

Lemma hp_rel_g0_search_correct : forall bytes hayoff haylen needleoff needlelen position,
    Hoare (fun _ : unit => 0 <= position /\ hp_no_match_before bytes hayoff haylen needleoff needlelen position)
      (hp_search_from bytes hayoff haylen needleoff needlelen position)
      (fun result _ => hp_search_post bytes hayoff haylen needleoff needlelen result).
Proof.
    intros bytes ho hl no nl pos; unfold hp_search_from.
    apply (Hoare_repeat_break _ (fun p (_ : unit) => 0 <= p /\ hp_no_match_before bytes ho hl no nl p)).
    intro p; unfold hp_search_body; apply Hoare_choice.
    - apply Hoare_assume_bind; intro Hend; unfold break; apply Hoare_ret.
      intros st [Hp Hbefore]; cbn; intros q Hmatch.
      destruct (Z_lt_ge_dec q p).
      + apply (Hbefore q); [unfold hp_match_at in Hmatch; lia | exact Hmatch].
      + unfold hp_match_at in Hmatch; lia.
    - apply Hoare_choice.
      + apply Hoare_assume_bind; intro Hmatch; unfold break; apply Hoare_ret.
        intros st [Hp Hbefore]; split; assumption.
      + apply Hoare_assume_bind; intro Hguard.
        eapply Hoare_bind; [apply Hoare_any | intro next].
        apply Hoare_assume_bind; intros [Hnext Hskip]; unfold continue; apply Hoare_ret.
        intros st [Hp Hbefore]; split; [lia | intros q Hq].
        destruct (Z_lt_ge_dec q p); [apply Hbefore; lia | apply Hskip; lia].
Qed.

Lemma hp_rel_g0_search_entry_correct : forall bytes ho hl no nl,
    Hoare (fun _ : unit => True) (hp_search_from bytes ho hl no nl 0)
      (fun result _ => hp_search_post bytes ho hl no nl result).
Proof.
    intros bytes ho hl no nl.
    eapply Hoare_conseq with
      (P2 := fun _ : unit => 0 <= 0 /\ hp_no_match_before bytes ho hl no nl 0)
      (Q2 := fun result (_ : unit) => hp_search_post bytes ho hl no nl result).
    - intros; split; [lia | unfold hp_no_match_before; intros; lia].
    - auto.
    - apply hp_rel_g0_search_correct.
Qed.
