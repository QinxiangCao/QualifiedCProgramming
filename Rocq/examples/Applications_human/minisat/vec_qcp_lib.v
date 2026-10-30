(** * The vectors of [vec_qcp.h]

    [veci_t] holds [int] elements and [vecp_t] holds pointers stored as their
    [Z] addresses; both are [DynVec] instances ([dynvec_lib]).  This file
    depends on nothing of the solver: a program that includes [vec_qcp.h]
    gets its predicates, its strategies ([vec_qcp.strategies]) and their
    proofs ([vec_qcp_strategy_proof.v]) from here. *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.Applications_human Require Export dynvec_lib.
Import naive_C_Rules.
Local Open Scope string.

Module VeciLayout <: VEC_LAYOUT.
  Definition struct_name := "veci_t".
  Definition size_field := "size".
  Definition cap_field := "cap".
  Definition ptr_field := "ptr".
End VeciLayout.

Module VecpLayout <: VEC_LAYOUT.
  Definition struct_name := "vecp_t".
  Definition size_field := "size".
  Definition cap_field := "cap".
  Definition ptr_field := "ptr".
End VecpLayout.

Module Veci := DynVec IntElems VeciLayout.
Module Vecp := DynVec PtrElems VecpLayout.
Module VecpArray := VecArray Vecp.

(** QCP's names for an uninitialized [veci_t] and [vecp_t]. *)
Definition UndefStructPredveci_t (v : Z) : Assertion := Veci.shell v.
Definition UndefStructPredvecp_t (v : Z) : Assertion := Vecp.shell v.

(** * [vecp_remove]

    [vecp_remove] removes the first occurrence of an element.  Vectors are
    positional and may contain duplicates, so this is not a set-level removal.
    The scan invariant keeps the element in the unread suffix, so the next
    read is in bounds; the shift invariant records the duplicate at the
    moving hole while the tail shifts down. *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list.

Definition vecp_remove_scan_inv (e : Z) (l : list Z) (j : Z) : Prop :=
  0 <= j < Zlength l /\
  In e (sublist j (Zlength l) l) /\
  Forall (fun x => x <> e) (sublist 0 j l).

Definition vecp_remove_shift_inv
    (e : Z) (l : list Z) (found j : Z) (current : list Z) : Prop :=
  first_occurrence e l found /\
  found <= j < Zlength l /\
  current =
    sublist 0 found l ++
    sublist (found + 1) (j + 1) l ++
    sublist j (Zlength l) l.

Lemma vecp_remove_scan_step : forall e l j,
  vecp_remove_scan_inv e l j -> Znth j l 0 <> e ->
  vecp_remove_scan_inv e l (j + 1).
Proof.
  intros e l j (Hj & Hin & Hbefore) Hneq.
  rewrite (sublist_suffix_cons 0) in Hin by lia.
  simpl in Hin. destruct Hin as [Heq | Hafter]; [congruence|].
  assert (Hnext : j + 1 < Zlength l).
  { destruct (sublist (j + 1) (Zlength l) l) as [|a t] eqn:E.
    - contradiction.
    - pose proof (Zlength_sublist (j + 1) (Zlength l) l ltac:(lia))
        as Hlen.
      rewrite E, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg t). lia. }
  unfold vecp_remove_scan_inv. split; [lia|]. split; [exact Hafter|].
  rewrite (sublist_snoc 0) by lia.
  apply Forall_app. split; [exact Hbefore|].
  constructor; [exact Hneq|constructor].
Qed.

Lemma vecp_remove_shift_init : forall e l j,
  vecp_remove_scan_inv e l j -> Znth j l 0 = e ->
  vecp_remove_shift_inv e l j j l.
Proof.
  intros e l j (Hj & Hin & Hbefore) Heq.
  unfold vecp_remove_shift_inv, first_occurrence.
  split.
  - split; [exact Hj|]. split; [|exact Hbefore].
    rewrite (Znth_indep l j e 0) by lia. exact Heq.
  - split; [lia|].
    rewrite (Zsublist_nil l (j + 1) (j + 1)) by lia.
    rewrite app_nil_l.
    rewrite <- (sublist_split 0 (Zlength l) j l) by lia.
    rewrite (sublist_self l (Zlength l)) by reflexivity. reflexivity.
Qed.

Lemma vecp_remove_shift_replace : forall l found j,
  0 <= found <= j -> j + 1 < Zlength l ->
  replace_Znth j
    (Znth (j + 1)
      (sublist 0 found l ++
       sublist (found + 1) (j + 1) l ++
       sublist j (Zlength l) l) 0)
    (sublist 0 found l ++
     sublist (found + 1) (j + 1) l ++
     sublist j (Zlength l) l) =
  sublist 0 found l ++
  sublist (found + 1) (j + 2) l ++
  sublist (j + 1) (Zlength l) l.
Proof.
  intros l found j Hfound Hj.
  rewrite (sublist_suffix_cons 0) by lia.
  replace (j + 2) with (j + 1 + 1) by lia.
  rewrite (sublist_split (found + 1) (j + 1 + 1) (j + 1) l) by lia.
  rewrite (sublist_single 0 (j + 1) l) by lia.
  rewrite !app_assoc.
  assert (Hprefix :
      Zlength (sublist 0 found l ++
               sublist (found + 1) (j + 1) l) = j).
  { rewrite Zlength_app.
    rewrite (Zlength_sublist 0 found l) by lia.
    rewrite (Zlength_sublist (found + 1) (j + 1) l) by lia. lia. }
  rewrite app_Znth2 by lia.
  replace
    (j + 1 - Zlength
      (sublist 0 found l ++ sublist (found + 1) (j + 1) l))
    with 1 by lia.
  replace
    (Znth 1 (Znth j l 0 :: sublist (j + 1) (Zlength l) l) 0)
    with (Znth 0 (sublist (j + 1) (Zlength l) l) 0)
    by reflexivity.
  rewrite Znth_sublist by lia.
  replace (0 + (j + 1)) with (j + 1) by lia.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace
    (j - Zlength
      (sublist 0 found l ++ sublist (found + 1) (j + 1) l))
    with 0 by lia.
  unfold replace_Znth. simpl.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma vecp_remove_shift_step :
  forall e original found j current,
  vecp_remove_shift_inv e original found j current ->
  j + 1 < Zlength current ->
  vecp_remove_shift_inv e original found (j + 1)
    (replace_Znth j (Znth (j + 1) current 0) current).
Proof.
  intros e original found j current Hinv Hnext.
  destruct Hinv as (Hfound & Hj & Hcurrent).
  destruct Hfound as (Hfound_range & Heq & Hbefore).
  assert (Hlen : Zlength current = Zlength original).
  { rewrite Hcurrent, !Zlength_app.
    rewrite (Zlength_sublist 0 found original) by lia.
    rewrite (Zlength_sublist (found + 1) (j + 1) original) by lia.
    rewrite (Zlength_sublist j (Zlength original) original) by lia. lia. }
  unfold vecp_remove_shift_inv. split.
  - unfold first_occurrence. split; [exact Hfound_range|].
    split; assumption.
  - split; [lia|].
    rewrite Hcurrent at 1 2.
    replace (j + 1 + 1) with (j + 2) by lia.
    apply vecp_remove_shift_replace; lia.
Qed.

Lemma vecp_remove_shift_done :
  forall e original found j current,
  vecp_remove_shift_inv e original found j current ->
  j >= Zlength current - 1 -> j < Zlength current ->
  first_occurrence e original found /\
  1 <= Zlength current /\
  sublist 0 (Zlength current - 1) current =
    remove_nth found original.
Proof.
  intros e original found j current Hinv Hjlast Hjlt.
  destruct Hinv as (Hfound & Hj & Hcurrent).
  destruct Hfound as (Hfound_range & Heq & Hbefore).
  assert (Hlen : Zlength current = Zlength original).
  { rewrite Hcurrent, !Zlength_app.
    rewrite (Zlength_sublist 0 found original) by lia.
    rewrite (Zlength_sublist (found + 1) (j + 1) original) by lia.
    rewrite (Zlength_sublist j (Zlength original) original) by lia. lia. }
  split.
  - unfold first_occurrence. split; [exact Hfound_range|].
    split; assumption.
  - split; [lia|]. unfold remove_nth. rewrite Hcurrent, app_assoc.
    assert (Hprefix :
      Zlength (sublist 0 found original ++
               sublist (found + 1) (j + 1) original) = j).
    { rewrite Zlength_app.
      rewrite (Zlength_sublist 0 found original) by lia.
      rewrite (Zlength_sublist (found + 1) (j + 1) original) by lia. lia. }
    replace
      (Zlength
        ((sublist 0 found original ++
          sublist (found + 1) (j + 1) original) ++
         sublist j (Zlength original) original) - 1)
      with
      (Zlength (sublist 0 found original ++
                sublist (found + 1) (j + 1) original)).
    2: { rewrite !Zlength_app.
         rewrite (Zlength_sublist 0 found original) by lia.
         rewrite (Zlength_sublist (found + 1) (j + 1) original) by lia.
         rewrite (Zlength_sublist j (Zlength original) original) by lia.
         lia. }
    rewrite sublist_app_exact1.
    replace (j + 1) with (Zlength original) by lia. reflexivity.
Qed.
