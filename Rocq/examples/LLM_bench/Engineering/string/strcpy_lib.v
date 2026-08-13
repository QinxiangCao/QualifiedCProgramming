Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
Require Import SimpleC.StdLib.string_lib.

Local Open Scope Z_scope.
Import ListNotations.
Local Open Scope list.

Definition strncpy_content (src : list Z) (n : Z) (out : list Z) : Prop :=
  0 <= n /\
  ((n <= string_length src /\ out = sublist 0 n src) \/
   (string_length src < n /\
    out = src ++ repeat 0 (Z.to_nat (n - string_length src)))).

Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

(* Helper lemmas migrated from strcpy_proof_manual__merged.v. *)

Lemma strncpy_undef_seg_empty_to_full_nil : forall x,
  CharArray.undef_seg x 0 0 |-- CharArray.full x 0 nil.
Proof.
  intros.
  rewrite CharArray.undef_seg_empty.
  rewrite CharArray.full_empty.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial. reflexivity.
Qed.

Lemma strncpy_c_string_nonzero_lt : forall (src : list Z) i,
  Znth i (string_lib.c_string src) 0 <> 0 ->
  0 <= i ->
  i <= string_lib.string_length src ->
  i < string_lib.string_length src.
Proof.
  intros src i Hnz Hi0 Hile.
  unfold string_lib.c_string, string_lib.string_length in *.
  destruct (Z_lt_ge_dec i (Zlength src)) as [Hlt | Hge]; [lia |].
  assert (i = Zlength src) by lia.
  subst i.
  rewrite app_Znth2 in Hnz by lia.
  replace (Zlength src - Zlength src) with 0 in Hnz by lia.
  simpl in Hnz.
  contradiction.
Qed.

Lemma strncpy_sublist_succ : forall (src : list Z) i,
  Znth i (string_lib.c_string src) 0 <> 0 ->
  0 <= i ->
  i <= string_lib.string_length src ->
  sublist 0 i src ++ Znth i (string_lib.c_string src) 0 :: nil =
  sublist 0 (i + 1) src.
Proof.
  intros src i Hnz Hi0 Hile.
  pose proof (strncpy_c_string_nonzero_lt src i Hnz Hi0 Hile) as Hlt.
  unfold string_lib.c_string, string_lib.string_length in *.
  rewrite app_Znth1 by lia.
  rewrite (sublist_split 0 (i + 1) i src) by lia.
  rewrite (sublist_single 0 i src) by lia.
  reflexivity.
Qed.

Lemma strncpy_c_string_zero_ge_length : forall (src : list Z) i,
  string_lib.valid_string src ->
  Znth i (string_lib.c_string src) 0 = 0 ->
  0 <= i ->
  i <= string_lib.string_length src ->
  string_lib.string_length src <= i.
Proof.
  intros src i Hvalid Hz Hi0 Hile.
  unfold string_lib.valid_string in Hvalid.
  destruct Hvalid as [_ Hno].
  unfold string_lib.c_string, string_lib.string_length in *.
  destruct (Z_lt_ge_dec i (Zlength src)) as [Hlt | Hge]; [| lia].
  rewrite app_Znth1 in Hz by lia.
  specialize (Hno i ltac:(lia)).
  congruence.
Qed.

Lemma strncpy_content_pad_zero_step : forall src i out,
  0 <= i ->
  string_lib.string_length src <= i ->
  strncpy_content src i out ->
  strncpy_content src (i + 1) (out ++ 0 :: nil).
Proof.
  intros src i out Hi Hlen Hcontent.
  unfold strncpy_content in Hcontent |- *.
  destruct Hcontent as [_ [[Hi_len Hout] | [Hlt_len Hout]]].
  - split; [lia|].
    right.
    split; [lia|].
    subst out.
    rewrite sublist_self by (unfold string_lib.string_length in *; lia).
    replace (i + 1 - string_lib.string_length src) with 1 by lia.
    reflexivity.
  - split; [lia|].
    right.
    split; [lia|].
    subst out.
    replace (i + 1 - string_lib.string_length src)
      with ((i - string_lib.string_length src) + 1) by lia.
    rewrite Z2Nat.inj_add by lia.
    change (Z.to_nat 1) with 1%nat.
    rewrite repeat_app.
    simpl.
    rewrite app_assoc.
    reflexivity.
Qed.
