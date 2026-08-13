Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From AUXLib Require Import ListLib.
Require Import SimpleC.StdLib.string_lib.

Local Open Scope Z_scope.
Import ListNotations.
Local Open Scope list.

Definition strcmp_result (str1 str2 : list Z) (ret : Z) : Prop :=
  exists i,
    0 <= i <= string_length str1 /\
    i <= string_length str2 /\
    (forall k, 0 <= k < i -> Znth k (c_string str1) 0 = Znth k (c_string str2) 0) /\
    ret = Znth i (c_string str1) 0 - Znth i (c_string str2) 0 /\
    (Znth i (c_string str1) 0 = 0 \/
     Znth i (c_string str1) 0 <> Znth i (c_string str2) 0).

Definition strncmp_result (str1 str2 : list Z) (n ret : Z) : Prop :=
  exists i,
    0 <= i <= n /\
    i <= string_length str1 /\
    i <= string_length str2 /\
    (forall k, 0 <= k < i -> Znth k (c_string str1) 0 = Znth k (c_string str2) 0) /\
    ((i = n /\ ret = 0) \/
     (i < n /\
      ret = Znth i (c_string str1) 0 - Znth i (c_string str2) 0 /\
      (Znth i (c_string str1) 0 = 0 \/
       Znth i (c_string str1) 0 <> Znth i (c_string str2) 0))).

Lemma c_string_char_bound:
  forall s i,
    valid_string s ->
    0 <= i <= string_length s ->
    0 <= Znth i (c_string s) 0 <= 127.
Proof.
  intros s i Hvalid Hi.
  unfold valid_string, all_ascii, c_string, string_length in *.
  destruct Hvalid as [Hascii _].
  destruct (Z.eq_dec i (Zlength s)).
  - subst i.
    rewrite app_Znth2 by auto with zarith.
    replace (Zlength s - Zlength s) with 0 by auto with zarith.
    simpl. auto with zarith.
  - rewrite app_Znth1 by auto with zarith.
    apply Hascii. auto with zarith.
Qed.

Lemma c_string_nonzero_lt_length:
  forall s i,
    valid_string s ->
    0 <= i <= string_length s ->
    Znth i (c_string s) 0 <> 0 ->
    i < string_length s.
Proof.
  intros s i Hvalid Hi Hnz.
  unfold c_string, string_length in *.
  destruct (Z.eq_dec i (Zlength s)); [|auto with zarith].
  subst i.
  rewrite app_Znth2 in Hnz by auto with zarith.
  replace (Zlength s - Zlength s) with 0 in Hnz by auto with zarith.
  simpl in Hnz. contradiction.
Qed.

Lemma prefix_eq_extend:
  forall str1 str2 i,
    (forall k, 0 <= k < i ->
     Znth k (c_string str1) 0 = Znth k (c_string str2) 0) ->
    Znth i (c_string str1) 0 = Znth i (c_string str2) 0 ->
    forall k, 0 <= k < i + 1 ->
      Znth k (c_string str1) 0 = Znth k (c_string str2) 0.
Proof.
  intros str1 str2 i Hprefix Hi k Hk.
  destruct (Z.eq_dec k i).
  - subst. exact Hi.
  - apply Hprefix. auto with zarith.
Qed.
