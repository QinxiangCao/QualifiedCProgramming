Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
Require Import SimpleC.StdLib.string_lib.

Local Open Scope Z_scope.
Import ListNotations.
Local Open Scope list.

Definition strncat_result (dst src : list Z) (n : Z) (out : list Z) : Prop :=
  0 <= n /\
  ((string_length src <= n /\ out = dst ++ src) \/
   (n < string_length src /\ out = dst ++ sublist 0 n src)).

Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import naive_C_Rules.
Local Open Scope sets.
Local Open Scope sac.

(* Helper lemmas migrated from strcat__vc_proving_subagent_tmp_proof_manual__merged_proof_manual.v. *)

Lemma helper_sublist_snoc_Z : forall (l : list Z) j d,
  0 <= j < Zlength l ->
  sublist 0 (j + 1) l = sublist 0 j l ++ Znth j l d :: nil.
Proof.
  intros.
  rewrite (sublist_split 0 (j + 1) j l) by lia.
  rewrite (sublist_single d) by lia.
  reflexivity.
Qed.

Lemma helper_replace_Znth_last_Z : forall (l : list Z) a,
  replace_Znth (Zlength l) a (l ++ 0 :: nil) = l ++ a :: nil.
Proof.
  intros.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (Zlength l - Zlength l) with 0 by lia.
  simpl.
  reflexivity.
Qed.

Lemma helper_strncat_step_list : forall (dst src : list Z) j,
  0 <= j < Zlength src ->
  replace_Znth (Zlength dst + j) (Znth j (src ++ 0 :: nil) 0)
    ((dst ++ sublist 0 j src) ++ 0 :: nil) =
  dst ++ sublist 0 (j + 1) src.
Proof.
  intros.
  replace (Zlength dst + j) with (Zlength (dst ++ sublist 0 j src)) by
    (rewrite Zlength_app, Zlength_sublist0; lia).
  rewrite helper_replace_Znth_last_Z.
  rewrite app_Znth1 by lia.
  rewrite helper_sublist_snoc_Z with (d := 0) by lia.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma helper_sublist_app_last_Z : forall (l : list Z) a,
  sublist (Zlength l) (Zlength l + 1) (l ++ a :: nil) = a :: nil.
Proof.
  intros.
  rewrite sublist_split_app_r with (len := Zlength l) by lia.
  replace (Zlength l - Zlength l) with 0 by lia.
  replace (Zlength l + 1 - Zlength l) with 1 by lia.
  rewrite sublist_cons1 by lia.
  replace (1 - 1) with 0 by lia.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.

Lemma helper_chararray_full_single_point : forall p a,
  CharArray.full p 1 (a :: nil) |-- p # Char |-> a.
Proof.
  intros.
  rewrite CharArray.full_unfold.
  replace (p + 0 * sizeof ( CHAR )) with p by lia.
  cancel (p # Char |-> a).
  rewrite CharArray.seg_empty; Intros; cancel.
Qed.

Lemma helper_chararray_point_to_full_single : forall p a,
  p # Char |-> a |-- CharArray.full p 1 (a :: nil).
Proof.
  intros.
  rewrite CharArray.full_unfold.
  replace (p + 0 * sizeof ( CHAR )) with p by lia.
  rewrite CharArray.seg_empty.
  cancel (p # Char |-> a).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma helper_chararray_full_snoc : forall p n l a,
  0 <= n ->
  CharArray.full p n l ** (p + n * sizeof ( CHAR )) # Char |-> a
  |-- CharArray.full p (n + 1) (l ++ a :: nil).
Proof.
  intros.
  sep_apply CharArray.seg_single.
  sep_apply CharArray.seg_to_full.
  sep_apply (CharArray.full_merge_to_full p n) ; try lia.
  cancel.
Qed.

Lemma helper_c_string_nonzero_lt : forall s j,
  0 <= j -> j <= Zlength s -> Znth j (s ++ 0 :: nil) 0 <> 0 -> j < Zlength s.
Proof.
  intros.
  destruct (Z_lt_ge_dec j (Zlength s)); [lia|].
  assert (j = Zlength s) by lia; subst j.
  rewrite app_Znth2 in H1 by lia.
  replace (Zlength s - Zlength s) with 0 in H1 by lia.
  simpl in H1.
  contradiction.
Qed.

Lemma helper_c_string_zero_index : forall s j,
  string_lib.valid_string s ->
  0 <= j <= string_lib.string_length s ->
  Znth j (string_lib.c_string s) 0 = 0 ->
  j = string_lib.string_length s.
Proof.
  unfold string_lib.valid_string, string_lib.no_inner_nul,
    string_lib.string_length, string_lib.c_string.
  intros s j [_ Hno] Hj Hz.
  destruct (Z_lt_ge_dec j (Zlength s)); [|lia].
  specialize (Hno j ltac:(lia)).
  rewrite app_Znth1 in Hz by lia.
  contradiction.
Qed.
