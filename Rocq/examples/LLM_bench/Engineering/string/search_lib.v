Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
Require Import SimpleC.StdLib.string_lib.

Local Open Scope Z_scope.

Definition memchr_result (bytes : list Z) (c n ret s : Z) : Prop :=
  (exists i,
      0 <= i < n /\
      Znth i bytes 0 = c /\
      (forall k, 0 <= k < i -> Znth k bytes 0 <> c) /\
      ret = s + i) \/
  ((forall k, 0 <= k < n -> Znth k bytes 0 <> c) /\
   ret = 0).

Definition strchr_result (str : list Z) (c ret s : Z) : Prop :=
  (exists i,
      0 <= i < string_length str /\
      Znth i str 0 = c /\
      (forall k, 0 <= k < i -> Znth k str 0 <> c) /\
      ret = s + i) \/
  ((forall k, 0 <= k < string_length str -> Znth k str 0 <> c) /\
   ((c = 0 /\ ret = s + string_length str) \/
    (c <> 0 /\ ret = 0))).

Lemma string_length_nonneg :
  forall str, 0 <= string_length str.
Proof.
  intros str.
  unfold string_length.
  rewrite Zlength_correct.
  apply Zle_0_nat.
Qed.

Lemma c_string_Znth_inside :
  forall str i d,
    0 <= i < string_length str ->
    Znth i (c_string str) d = Znth i str d.
Proof.
  intros str i d Hi.
  unfold c_string, string_length in *.
  rewrite app_Znth1; auto.
Qed.

Lemma c_string_Znth_terminator :
  forall str d,
    Znth (string_length str) (c_string str) d = 0.
Proof.
  intros str d.
  unfold c_string, string_length.
  rewrite app_Znth2.
  rewrite Z.sub_diag.
  reflexivity.
  unfold Z.ge.
  rewrite Z.compare_refl.
  discriminate.
Qed.

Lemma c_string_nonzero_index_lt :
  forall str i,
    0 <= i ->
    i <= string_length str ->
    Znth i (c_string str) 0 <> 0 ->
    i < string_length str.
Proof.
  intros str i Hi0 Hile Hnz.
  destruct (Z_lt_ge_dec i (string_length str)) as [Hlt | Hge].
  - exact Hlt.
  - assert (i = string_length str).
    { apply Z.le_antisymm; auto.
      apply Z.ge_le; auto. }
    subst i.
    rewrite c_string_Znth_terminator in Hnz.
    contradiction.
Qed.

Lemma c_string_zero_index_eq_length :
  forall str i,
    valid_string str ->
    0 <= i ->
    i <= string_length str ->
    Znth i (c_string str) 0 = 0 ->
    i = string_length str.
Proof.
  intros str i [_ Hno_nul] Hi0 Hile Hzero.
  destruct (Z_lt_ge_dec i (string_length str)) as [Hlt | Hge].
  - rewrite c_string_Znth_inside in Hzero by (split; auto).
    exfalso.
    apply (Hno_nul i).
    + split; auto.
    + exact Hzero.
  - apply Z.le_antisymm; auto.
    apply Z.ge_le; auto.
Qed.
