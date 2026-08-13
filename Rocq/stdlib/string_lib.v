Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Definition all_ascii (s: list Z): Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition no_inner_nul (s: list Z): Prop :=
  forall i, 0 <= i < Zlength s -> Znth i s 0 <> 0.

Definition valid_string (s: list Z): Prop :=
  all_ascii s /\ no_inner_nul s.

Definition c_string (s: list Z): list Z :=
  s ++ [0].

Definition string_length (s: list Z): Z :=
  Zlength s.

Definition store_string (p: Z) (s: list Z): Assertion :=
  CharArray.full p (string_length s + 1) (c_string s).

Definition memchr_result (bytes: list Z) (c n ret s: Z): Prop :=
  (exists i,
      0 <= i < n /\
      Znth i bytes 0 = c /\
      (forall k, 0 <= k < i -> Znth k bytes 0 <> c) /\
      ret = s + i) \/
  ((forall k, 0 <= k < n -> Znth k bytes 0 <> c) /\ ret = 0).

Definition strchr_result (str : list Z) (c ret s : Z) : Prop :=
  (exists i,
      0 <= i < string_length str /\
      Znth i str 0 = c /\
      (forall k, 0 <= k < i -> Znth k str 0 <> c) /\
      ret = s + i) \/
  ((forall k, 0 <= k < string_length str -> Znth k str 0 <> c) /\
   ((c = 0 /\ ret = s + string_length str) \/
    (c <> 0 /\ ret = 0))).

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

Definition strncpy_content (src : list Z) (n : Z) (out : list Z) : Prop :=
  0 <= n /\
  ((n <= string_length src /\ out = sublist 0 n src) \/
   (string_length src < n /\
    out = src ++ repeat 0 (Z.to_nat (n - string_length src)))).

Definition strncat_result (dst src : list Z) (n : Z) (out : list Z) : Prop :=
  0 <= n /\
  ((string_length src <= n /\ out = dst ++ src) \/
   (n < string_length src /\ out = dst ++ sublist 0 n src)).

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

Lemma strncpy_undef_seg_empty_to_full_nil : forall x,
  CharArray.undef_seg x 0 0 |-- CharArray.full x 0 nil.
Proof.
  intros.
  rewrite CharArray.undef_seg_empty.
  rewrite CharArray.full_empty.
  entailer!.
Qed.

Lemma strncpy_c_string_nonzero_lt : forall (src : list Z) i,
  Znth i (c_string src) 0 <> 0 ->
  0 <= i ->
  i <= string_length src ->
  i < string_length src.
Proof.
  intros src i Hnz Hi0 Hile.
  unfold c_string, string_length in *.
  destruct (Z_lt_ge_dec i (Zlength src)) as [Hlt | Hge]; [lia |].
  assert (i = Zlength src) by lia.
  subst i.
  rewrite app_Znth2 in Hnz by lia.
  replace (Zlength src - Zlength src) with 0 in Hnz by lia.
  simpl in Hnz.
  contradiction.
Qed.

Lemma strncpy_sublist_succ : forall (src : list Z) i,
  Znth i (c_string src) 0 <> 0 ->
  0 <= i ->
  i <= string_length src ->
  sublist 0 i src ++ Znth i (c_string src) 0 :: nil =
  sublist 0 (i + 1) src.
Proof.
  intros src i Hnz Hi0 Hile.
  pose proof (strncpy_c_string_nonzero_lt src i Hnz Hi0 Hile) as Hlt.
  unfold c_string, string_length in *.
  rewrite app_Znth1 by lia.
  rewrite (sublist_split 0 (i + 1) i src) by lia.
  rewrite (sublist_single 0 i src) by lia.
  reflexivity.
Qed.

Lemma strncpy_c_string_zero_ge_length : forall (src : list Z) i,
  valid_string src ->
  Znth i (c_string src) 0 = 0 ->
  0 <= i ->
  i <= string_length src ->
  string_length src <= i.
Proof.
  intros src i Hvalid Hz Hi0 Hile.
  unfold valid_string in Hvalid.
  destruct Hvalid as [_ Hno].
  unfold c_string, string_length in *.
  destruct (Z_lt_ge_dec i (Zlength src)) as [Hlt | Hge]; [| lia].
  rewrite app_Znth1 in Hz by lia.
  specialize (Hno i ltac:(lia)).
  congruence.
Qed.

Lemma strncpy_content_pad_zero_step : forall src i out,
  0 <= i ->
  string_length src <= i ->
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
    rewrite sublist_self by (unfold string_length in *; lia).
    replace (i + 1 - string_length src) with 1 by lia.
    reflexivity.
  - split; [lia|].
    right.
    split; [lia|].
    subst out.
    replace (i + 1 - string_length src)
      with ((i - string_length src) + 1) by lia.
    rewrite Z2Nat.inj_add by lia.
    change (Z.to_nat 1) with 1%nat.
    rewrite repeat_app.
    simpl.
    rewrite app_assoc.
    reflexivity.
Qed.

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
  rewrite CharArray.seg_empty; Intros; normalize ; cancel.
Qed.

Lemma helper_chararray_point_to_full_single : forall p a,
  p # Char |-> a |-- CharArray.full p 1 (a :: nil).
Proof.
  intros.
  rewrite CharArray.full_unfold.
  replace (p + 0 * sizeof ( CHAR )) with p by lia.
  rewrite CharArray.seg_empty.
  cancel (p # Char |-> a).
  entailer!.
Qed.

Lemma helper_chararray_full_snoc : forall p n l a,
  0 <= n ->
  CharArray.full p n l ** (p + n * sizeof ( CHAR )) # Char |-> a
  |-- CharArray.full p (n + 1) (l ++ a :: nil).
Proof.
  intros.
  sep_apply helper_chararray_point_to_full_single.
  transitivity (CharArray.full p n l **
                CharArray.full (p + n * sizeof ( CHAR )) (n + 1 - n) (a :: nil)).
  - replace (n + 1 - n) with 1 by lia; cancel.
  - exact (CharArray.full_merge_to_full p n (n + 1) l (a :: nil) ltac:(lia)).
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
  valid_string s ->
  0 <= j <= string_length s ->
  Znth j (c_string s) 0 = 0 ->
  j = string_length s.
Proof.
  unfold valid_string, no_inner_nul, string_length, c_string.
  intros s j [_ Hno] Hj Hz.
  destruct (Z_lt_ge_dec j (Zlength s)); [|lia].
  specialize (Hno j ltac:(lia)).
  rewrite app_Znth1 in Hz by lia.
  contradiction.
Qed.
