Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Input characters are restricted to alphanumeric ASCII codes, so they
   cannot collide with Manacher's marker characters '$', '#', and '\0'. *)
Definition AlnumCode (z : Z) : Prop :=
  (48 <= z <= 57) \/ (65 <= z <= 90) \/ (97 <= z <= 122).

(* Pointwise alphanumeric condition for the logical model of the C string. *)
Definition AlnumString (s : list Z) : Prop :=
  forall k, 0 <= k < Zlength s -> AlnumCode (Znth k s 0).

(* A substring [s[lo, lo+len)) is a palindrome in the original string. *)
Definition PalindromeSegment (s : list Z) (lo len : Z) : Prop :=
  0 <= lo /\
  0 <= len /\
  lo + len <= Zlength s /\
  forall k, 0 <= k < len ->
    Znth (lo + k) s 0 = Znth (lo + len - 1 - k) s 0.

(* Final functional postcondition: [out] is a longest palindromic substring
   of [s], and [ret] is exactly its length. *)
Definition LongestPalindromeResult
    (s out : list Z) (ret : Z) : Prop :=
  ret = Zlength out /\
  exists lo,
    out = sublist lo (lo + ret) s /\
    PalindromeSegment s lo ret /\
    forall lo' len',
      PalindromeSegment s lo' len' -> len' <= ret.

(* Prefix shape while building the transformed string:
   "$#s0#s1#..." up to the first [i] input characters. *)
Definition ManacherTransformedPrefix
    (s s2 : list Z) (i : Z) : Prop :=
  0 <= i <= Zlength s /\
  Zlength s2 = 2 * i + 1 /\
  Znth 0 s2 0 = 36 /\
  forall k,
    0 <= k < i ->
      Znth (2 * k + 1) s2 0 = 35 /\
      Znth (2 * k + 2) s2 0 = Znth k s 0.

(* Complete transformed string used by the C implementation:
   '$' at index 0, alternating '#' and input characters, final '#',
   and a trailing '\0' outside the logical Manacher length [len]. *)
Definition ManacherTransformedString
    (s s2 : list Z) (len : Z) : Prop :=
  len = 2 * Zlength s + 2 /\
  Zlength s2 = len + 1 /\
  Znth 0 s2 0 = 36 /\
  Znth (len - 1) s2 0 = 35 /\
  Znth len s2 0 = 0 /\
  (forall k,
      0 < k < len ->
        Znth k s2 0 <> 36) /\
  (forall k,
      0 <= k < Zlength s ->
        Znth (2 * k + 1) s2 0 = 35 /\
        Znth (2 * k + 2) s2 0 = Znth k s 0) /\
  (forall k,
      0 <= k < len ->
        Znth k s2 0 <> 0).

(* In the transformed string, [radius] means all offsets [0, radius) around
   [center] are symmetric and stay inside [0, len). *)
Definition CenterRadiusPalindrome
    (s2 : list Z) (len center radius : Z) : Prop :=
  1 <= center < len /\
  1 <= radius /\
  0 <= center - (radius - 1) /\
  center + (radius - 1) < len /\
  forall d,
    0 <= d < radius ->
      Znth (center - d) s2 0 = Znth (center + d) s2 0.

(* A center radius is maximal if it is palindromic and cannot be extended
   because it hits a boundary or a mismatching pair. *)
Definition CenterRadiusMaximal
    (s2 : list Z) (len center radius : Z) : Prop :=
  CenterRadiusPalindrome s2 len center radius /\
  (center - radius < 0 \/
   len <= center + radius \/
   Znth (center - radius) s2 0 <> Znth (center + radius) s2 0).

(* The first [upto] entries of the radius table [p] have been computed and
   each stored radius is maximal for its center. *)
Definition RadiusTablePrefix
    (s2 : list Z) (len : Z) (p : list Z) (upto : Z) : Prop :=
  Zlength p = upto /\
  1 <= upto <= len /\
  forall k,
    1 <= k < upto ->
      CenterRadiusMaximal s2 len k (Znth k p 0).

(* The usual Manacher rightmost known palindrome window, represented by
   center [id] and right boundary [limit]. *)
Definition CurrentRightmostWindow
    (s2 : list Z) (len id limit : Z) : Prop :=
  0 <= id < len /\
  0 <= limit <= len /\
  (id < limit ->
    CenterRadiusPalindrome s2 len id (limit - id)).

(* The best palindrome found before [upto]: [maxId] is its center and
   [maxLen] is the original-string length, i.e. transformed radius minus one. *)
Definition BestRadiusPrefix
    (s2 : list Z) (len : Z) (p : list Z)
    (upto maxId maxLen : Z) : Prop :=
  1 <= upto <= len /\
  0 <= maxLen /\
  0 <= maxId < len /\
  ((maxLen = 0 /\ upto <= 2) \/
   CenterRadiusPalindrome s2 len maxId (maxLen + 1)) /\
  (forall k,
      1 <= k < upto -> Znth k p 0 - 1 <= maxLen) /\
  ((maxLen = 0 /\ upto <= 2) \/
   exists k,
     1 <= k < upto /\
     k = maxId /\
     Znth k p 0 - 1 = maxLen).

(* Main loop invariant after processing centers below [i].  It packages the
   transformed string, computed radius prefix, rightmost window, and best-so-far
   result used by later witnesses. *)
Definition ManacherLoopState
    (s s2 : list Z) (len : Z) (p : list Z)
    (i id limit maxId maxLen : Z) : Prop :=
  ManacherTransformedString s s2 len /\
  RadiusTablePrefix s2 len p i /\
  0 <= id < i /\
  CurrentRightmostWindow s2 len id limit /\
  BestRadiusPrefix s2 len p i maxId maxLen.

(* State at the start of an expansion attempt: current radius is already
   palindromic and the next compared pair is within or on the boundary. *)
Definition ExpansionCandidate
    (s2 : list Z) (len center radius : Z) : Prop :=
  1 <= center < len /\
  1 <= radius /\
  0 <= center - radius /\
  center + radius <= len /\
  CenterRadiusPalindrome s2 len center radius /\
  (Znth (center - radius) s2 0 = Znth (center + radius) s2 0 ->
   center + radius < len /\ 0 < center - radius).

(* The next compared pair matched, so expansion may safely increase radius. *)
Definition ExpansionAfterMatch
    (s2 : list Z) (len center radius : Z) : Prop :=
  ExpansionCandidate s2 len center radius /\
  center + radius < len /\
  0 < center - radius /\
  Znth (center - radius) s2 0 = Znth (center + radius) s2 0.

(* Invariant for the inner expansion loop for center [i], with [p_written]
   already containing the candidate radius at index [i]. *)
Definition ExpansionLoopState
    (s s2 : list Z) (len : Z) (p_written : list Z)
    (i r id limit maxId maxLen : Z) : Prop :=
  Zlength p_written = i + 1 /\
  ManacherLoopState s s2 len (sublist 0 i p_written)
                    i id limit maxId maxLen /\
  Znth i p_written 0 = r /\
  ExpansionCandidate s2 len i r.

(* Extract original-string characters from a transformed-string slice. *)
Definition NonHashChars (xs : list Z) : list Z :=
  filter (fun z => negb (Z.eqb z 35)) xs.

(* Progress invariant for copying the selected transformed window into output:
   [out] is exactly the non-# characters already visited. *)
Definition OutputCopyPrefix
    (s2 out : list Z) (start cur : Z) (j : Z) : Prop :=
  0 <= start /\
  start <= cur /\
  cur <= Zlength s2 /\
  out = NonHashChars (sublist start cur s2) /\
  j = Zlength out.

(* A lightweight bound used during output copying: any partial copied prefix
   has length at most [maxLen]. *)
Definition OutputCopyBound
    (s2 : list Z) (start cur maxLen : Z) : Prop :=
  0 <= start /\
  start <= cur /\
  cur <= Zlength s2 /\
  Zlength (NonHashChars (sublist start cur s2)) <= maxLen.

(* Final state after copying: the copied output corresponds to the selected
   best palindrome and satisfies the overall longest-palindrome spec. *)
Definition OutputCopyDone
    (s s2 out : list Z) (len maxId maxLen ret : Z) : Prop :=
  ManacherTransformedString s s2 len /\
  ret = maxLen /\
  OutputCopyPrefix s2 out (maxId - maxLen) (maxId + maxLen + 1) ret /\
  LongestPalindromeResult s out ret.

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import SimpleC.EE.LLM_bench.Engineering.string.string_lib.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

(* Extends the transformed-prefix invariant after writing one input character
   and its following '#'.  Used by the transformed-string construction loop. *)
Lemma manacher_transformed_prefix_append_char :
  forall str s2 i,
    ManacherTransformedPrefix str s2 i ->
    0 <= i < Zlength str ->
    ManacherTransformedPrefix str
      ((s2 ++ 35 :: nil) ++ Znth i str 0 :: nil) (i + 1).
Proof.
  intros str s2 i Hpre Hi.
  unfold ManacherTransformedPrefix in *.
  destruct Hpre as (Hb & Hlen & Hzero & Hstep).
  repeat split.
  - lia.
  - lia.
  - rewrite !Zlength_app_cons, Hlen. lia.
  - rewrite app_Znth1.
    + rewrite app_Znth1; auto. lia.
    + rewrite Zlength_app_cons, Hlen. lia.
  - destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + specialize (Hstep k ltac:(lia)) as [Hhash _].
      rewrite app_Znth1.
      * rewrite app_Znth1; auto. rewrite Hlen. lia.
      * rewrite Zlength_app_cons, Hlen. lia.
    + assert (k = i) by lia; subst k.
      rewrite app_Znth1.
      * rewrite app_Znth2.
        -- rewrite Hlen. replace (2 * i + 1 - (2 * i + 1)) with 0 by lia.
           reflexivity.
        -- rewrite Hlen. lia.
      * rewrite Zlength_app_cons, Hlen. lia.
  - destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + specialize (Hstep k ltac:(lia)) as [_ Hchar].
      rewrite app_Znth1.
      * rewrite app_Znth1; auto. rewrite Hlen. lia.
      * rewrite Zlength_app_cons, Hlen. lia.
    + assert (k = i) by lia; subst k.
      rewrite app_Znth2.
      * rewrite Zlength_app_cons, Hlen.
        replace (2 * i + 2 - (2 * i + 1 + 1)) with 0 by lia.
        simpl. reflexivity.
      * rewrite Zlength_app_cons, Hlen. lia.
Qed.
(* Turns a completed transformed prefix into the full transformed-string
   predicate after writing the final '#' and trailing '\0'. *)
Lemma manacher_transformed_prefix_close_string :
  forall str s2 i,
    AlnumString str ->
    string_length str = i ->
    ManacherTransformedPrefix str s2 i ->
    ManacherTransformedString str ((s2 ++ 35 :: nil) ++ 0 :: nil) (2 * i + 2).
Proof.
  intros str s2 i Halnum Hstrlen Hpre.
  unfold ManacherTransformedPrefix in Hpre.
  unfold ManacherTransformedString.
  destruct Hpre as (Hb & Hlen & Hzero & Hstep).
  assert (HZlen_str : Zlength str = i).
  { rewrite <- Hstrlen. unfold string_length. reflexivity. }
  assert (Hchar_not_special :
    forall q, 0 <= q < i -> Znth q str 0 <> 36 /\ Znth q str 0 <> 0).
  {
    intros q Hq.
    specialize (Halnum q ltac:(rewrite HZlen_str; lia)).
    unfold AlnumCode in Halnum.
    lia.
  }
  repeat split.
  - lia.
  - rewrite !Zlength_app_cons, Hlen. lia.
  - rewrite app_Znth1.
    + rewrite app_Znth1; auto. lia.
    + rewrite Zlength_app_cons, Hlen. lia.
  - rewrite app_Znth1.
    + rewrite app_Znth2.
      * rewrite Hlen. replace (2 * i + 2 - 1 - (2 * i + 1)) with 0 by lia.
        simpl. reflexivity.
      * rewrite Hlen. lia.
    + rewrite Zlength_app_cons, Hlen. lia.
  - rewrite app_Znth2.
    + rewrite Zlength_app_cons, Hlen.
      replace (2 * i + 2 - (2 * i + 1 + 1)) with 0 by lia.
      simpl. reflexivity.
    + rewrite Zlength_app_cons, Hlen. lia.
  - intros k Hk.
    assert (Hdecomp : k = 2 * (k / 2) + k mod 2).
    { pose proof (Z.div_mod k 2 ltac:(lia)) as Hdiv; lia. }
    assert (Hmod : 0 <= k mod 2 < 2) by (apply Z.mod_pos_bound; lia).
    destruct (Z.eq_dec (k mod 2) 0) as [Heven | Hodd].
    + set (q := k / 2).
      assert (Hk_eq : k = 2 * q) by (unfold q; lia).
      assert (1 <= q <= i).
      { split; nia. }
      rewrite Hk_eq.
      rewrite app_Znth1.
      * rewrite app_Znth1.
        -- specialize (Hstep (q - 1) ltac:(lia)) as [_ Hchar].
           replace (2 * (q - 1) + 2) with (2 * q) in Hchar by lia.
           rewrite Hchar.
           specialize (Hchar_not_special (q - 1) ltac:(lia)) as [Hnot36 _].
           exact Hnot36.
        -- rewrite Hlen. lia.
      * rewrite Zlength_app_cons, Hlen. lia.
    + assert (k mod 2 = 1) by lia.
      set (q := k / 2).
      assert (Hk_eq : k = 2 * q + 1) by (unfold q; lia).
      assert (0 <= q <= i) by nia.
      rewrite Hk_eq.
      destruct (Z_lt_ge_dec q i) as [Hlt | Hge].
      * rewrite app_Znth1.
        -- rewrite app_Znth1.
           ++ specialize (Hstep q ltac:(lia)) as [Hhash _].
              rewrite Hhash. lia.
           ++ rewrite Hlen. lia.
        -- rewrite Zlength_app_cons, Hlen. lia.
      * assert (Hq : q = i) by lia; subst q; rewrite Hq.
        rewrite app_Znth1.
        -- rewrite app_Znth2.
           ++ rewrite Hlen.
              change (Znth (2 * i + 1 - (2 * i + 1)) (35 :: nil) 0 <> 36).
              replace (2 * i + 1 - (2 * i + 1)) with 0 by lia.
              change (35 <> 36). lia.
           ++ rewrite Hlen. lia.
        -- rewrite Zlength_app_cons, Hlen. lia.
  - rewrite HZlen_str in H.
    specialize (Hstep k H) as [Hhash _].
    rewrite app_Znth1.
    + rewrite app_Znth1; auto. rewrite Hlen. lia.
    + rewrite Zlength_app_cons, Hlen. lia.
  - rewrite HZlen_str in H.
    specialize (Hstep k H) as [_ Hchar].
    rewrite app_Znth1.
    + rewrite app_Znth1; auto. rewrite Hlen. lia.
    + rewrite Zlength_app_cons, Hlen. lia.
  - intros k0 Hk0.
    destruct (Z.eq_dec k0 0) as [-> | Hk0_nonzero].
    + rewrite app_Znth1.
      * rewrite app_Znth1.
        -- rewrite Hzero. lia.
        -- lia.
      * rewrite Zlength_app_cons, Hlen. lia.
    + assert (Hdecomp : k0 = 2 * (k0 / 2) + k0 mod 2).
      { pose proof (Z.div_mod k0 2 ltac:(lia)) as Hdiv; lia. }
      assert (Hmod : 0 <= k0 mod 2 < 2) by (apply Z.mod_pos_bound; lia).
      destruct (Z.eq_dec (k0 mod 2) 0) as [Heven | Hodd].
      * set (q := k0 / 2).
      assert (Hk_eq : k0 = 2 * q) by (unfold q; lia).
      assert (1 <= q <= i).
      { split; nia. }
      rewrite Hk_eq.
      rewrite app_Znth1.
      -- rewrite app_Znth1.
         ++ specialize (Hstep (q - 1) ltac:(lia)) as [_ Hchar].
            replace (2 * (q - 1) + 2) with (2 * q) in Hchar by lia.
            rewrite Hchar.
            specialize (Hchar_not_special (q - 1) ltac:(lia)) as [_ Hnot0].
            exact Hnot0.
         ++ rewrite Hlen. lia.
      -- rewrite Zlength_app_cons, Hlen. lia.
      * assert (k0 mod 2 = 1) by lia.
        set (q := k0 / 2).
        assert (Hk_eq : k0 = 2 * q + 1) by (unfold q; lia).
        assert (0 <= q <= i) by nia.
        rewrite Hk_eq.
        destruct (Z_lt_ge_dec q i) as [Hlt | Hge].
        { rewrite app_Znth1.
          - rewrite app_Znth1.
            + specialize (Hstep q ltac:(lia)) as [Hhash _].
              rewrite Hhash. lia.
            + rewrite Hlen. lia.
          - rewrite Zlength_app_cons, Hlen. lia. }
        { assert (Hq : q = i) by lia; subst q; rewrite Hq.
          rewrite app_Znth1.
          - rewrite app_Znth2.
            + rewrite Hlen.
              change (Znth (2 * i + 1 - (2 * i + 1)) (35 :: nil) 0 <> 0).
              replace (2 * i + 1 - (2 * i + 1)) with 0 by lia.
              change (35 <> 0). lia.
            + rewrite Hlen. lia.
          - rewrite Zlength_app_cons, Hlen. lia. }
Qed.
(* Any smaller radius around the same center remains a palindrome. *)
Lemma center_radius_palindrome_shrink:
  forall s2 len center r r',
    CenterRadiusPalindrome s2 len center r ->
    1 <= r' <= r ->
    CenterRadiusPalindrome s2 len center r'.
Proof.
  intros s2 len center r r' Hpal Hr.
  unfold CenterRadiusPalindrome in *.
  destruct Hpal as (Hc & Hr0 & Hl & Hrgt & Hsym).
  repeat split; try lia.
  intros d Hd.
  apply Hsym; lia.
Qed.
(* Transfers palindrome information from a mirror center across the current
   rightmost window; this is the core mirror argument in Manacher's algorithm. *)
Lemma manacher_mirror_palindrome_transfer:
  forall s2 len id limit i mirror r,
    mirror = 2 * id - i ->
    id < i ->
    CenterRadiusPalindrome s2 len id (limit - id) ->
    CenterRadiusPalindrome s2 len mirror r ->
    1 <= r <= limit - i ->
    CenterRadiusPalindrome s2 len i r.
Proof.
  intros s2 len id limit i mirror r Hmirror Hid Hwin Hmir Hrng.
  unfold CenterRadiusPalindrome in *.
  destruct Hwin as (Hid_bounds & Hwin_r & Hwin_l & Hwin_rgt & Hwin_sym).
  destruct Hmir as (Hmir_bounds & Hmir_r & Hmir_l & Hmir_rgt & Hmir_sym).
  repeat split; try lia.
  intros d Hd.
  assert (Hleft: Znth (i - d) s2 0 = Znth (mirror + d) s2 0).
  {
    destruct (Z_le_dec d (i - id)).
    - assert (Hoff : 0 <= i - id - d < limit - id) by lia.
      specialize (Hwin_sym (i - id - d) Hoff).
      replace (id - (i - id - d)) with (mirror + d) in Hwin_sym by lia.
      replace (id + (i - id - d)) with (i - d) in Hwin_sym by lia.
      symmetry; exact Hwin_sym.
    - assert (Hoff : 0 <= id - i + d < limit - id) by lia.
      specialize (Hwin_sym (id - i + d) Hoff).
      replace (id - (id - i + d)) with (i - d) in Hwin_sym by lia.
      replace (id + (id - i + d)) with (mirror + d) in Hwin_sym by lia.
      exact Hwin_sym.
  }
  assert (Hright: Znth (mirror - d) s2 0 = Znth (i + d) s2 0).
  {
    assert (Hoff : 0 <= i - id + d < limit - id) by lia.
    specialize (Hwin_sym (i - id + d) Hoff).
    replace (id - (i - id + d)) with (mirror - d) in Hwin_sym by lia.
    replace (id + (i - id + d)) with (i + d) in Hwin_sym by lia.
    exact Hwin_sym.
  }
  assert (Hmd: Znth (mirror - d) s2 0 = Znth (mirror + d) s2 0).
  {
    apply Hmir_sym; lia.
  }
  rewrite Hleft.
  rewrite <- Hright.
  symmetry; exact Hmd.
Qed.
(* When the mirror radius stays strictly inside the rightmost window, it is a
   valid expansion candidate for the current center. *)
Lemma manacher_mirror_candidate_inside:
  forall s s2 len id limit i mirror radius,
    ManacherTransformedString s s2 len ->
    mirror = 2 * id - i ->
    1 <= i < len ->
    0 <= mirror < i ->
    i < limit <= len ->
    CenterRadiusPalindrome s2 len id (limit - id) ->
    CenterRadiusPalindrome s2 len mirror radius ->
    1 <= radius < limit - i ->
    ExpansionCandidate s2 len i radius.
Proof.
  intros s s2 len id limit i mirror radius Htrans Hmirror Hi Hmirpos Hlimit Hwin Hmir Hrad.
  assert (Hpal: CenterRadiusPalindrome s2 len i radius).
  {
    apply (manacher_mirror_palindrome_transfer s2 len id limit i mirror radius);
      try lia; auto.
  }
  unfold CenterRadiusPalindrome in Hwin.
  destruct Hwin as (_ & _ & Hwin_l & _ & _).
  unfold ExpansionCandidate.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [exact Hpal|].
  intros _; split; lia.
Qed.
(* Shows the mirror index is positive in the branch where the current center is
   inside the rightmost window. *)
Lemma manacher_mirror_positive:
  forall s s2 len id limit i mirror,
    ManacherTransformedString s s2 len ->
    mirror = 2 * id - i ->
    1 <= i < len ->
    0 <= mirror ->
    i < limit <= len ->
    CenterRadiusPalindrome s2 len id (limit - id) ->
    0 < mirror.
Proof.
  intros s s2 len id limit i mirror Htrans Hmirror Hi Hmirror_nonneg Hlimit Hpal.
  unfold ManacherTransformedString in Htrans.
  destruct Htrans as (_ & _ & Hstart & _ & _ & Hnot36 & _ & _).
  unfold CenterRadiusPalindrome in Hpal.
  destruct Hpal as (_ & _ & _ & _ & Hsym).
  destruct (Z.eq_dec mirror 0) as [Hz|Hnz]; [|lia].
  subst mirror.
  assert (Hi_eq : i = 2 * id) by lia.
  assert (Hid_off : 0 <= id < limit - id) by lia.
  specialize (Hsym id Hid_off).
  replace (id - id) with 0 in Hsym by lia.
  replace (id + id) with i in Hsym by lia.
  assert (Hi_internal : 0 < i < len) by lia.
  specialize (Hnot36 i Hi_internal).
  rewrite Hstart in Hsym.
  congruence.
Qed.
(* A palindrome radius in the transformed string cannot correspond to an
   original-string length greater than the input length. *)
Lemma center_radius_palindrome_radius_minus_one_bound:
  forall s2 len center radius n,
    CenterRadiusPalindrome s2 len center (radius + 1) ->
    len = 2 * n + 2 ->
    radius <= n.
Proof.
  intros s2 len center radius n Hpal Hlen.
  unfold CenterRadiusPalindrome in Hpal.
  destruct Hpal as (_ & _ & Hleft & Hright & _).
  lia.
Qed.
(* The best-so-far original length [maxLen] is bounded by the input length. *)
Lemma best_radius_prefix_maxLen_bound:
  forall s2 len p upto maxId maxLen n,
    BestRadiusPrefix s2 len p upto maxId maxLen ->
    len = 2 * n + 2 ->
    maxLen <= n.
Proof.
  intros s2 len p upto maxId maxLen n Hbest Hlen.
  unfold BestRadiusPrefix in Hbest.
  destruct Hbest as (Hrange & _ & _ & Hpal & _ & _).
  destruct Hpal as [(Hz & _)|Hpal].
  - lia.
  - eapply center_radius_palindrome_radius_minus_one_bound; eauto.
Qed.
(* If the mirror palindrome reaches the current right boundary, the current
   center can start expansion from [limit - i]. *)
Lemma manacher_mirror_candidate_at_limit:
  forall s s2 len id limit i mirror mirror_radius,
    ManacherTransformedString s s2 len ->
    mirror = 2 * id - i ->
    1 <= i < len ->
    0 <= mirror < i ->
    i < limit <= len ->
    CenterRadiusPalindrome s2 len id (limit - id) ->
    CenterRadiusPalindrome s2 len mirror mirror_radius ->
    mirror_radius >= limit - i ->
    ExpansionCandidate s2 len i (limit - i).
Proof.
  intros s s2 len id limit i mirror mirror_radius Htrans Hmirror Hi Hmirpos
    Hlimit Hwin Hmir Hrad.
  assert (Hwin_l_for_lia: 0 <= id - (limit - id - 1)).
  {
    unfold CenterRadiusPalindrome in Hwin.
    tauto.
  }
  assert (Hpal_mirror: CenterRadiusPalindrome s2 len mirror (limit - i)).
  {
    apply (center_radius_palindrome_shrink s2 len mirror mirror_radius (limit - i));
      try lia; auto.
  }
  assert (Hpal: CenterRadiusPalindrome s2 len i (limit - i)).
  {
    apply (manacher_mirror_palindrome_transfer s2 len id limit i mirror (limit - i));
      try lia; auto.
  }
  unfold ManacherTransformedString in Htrans.
  destruct Htrans as (_ & _ & Hstart & _ & Hend & Hnot36 & _ & Hnonzero).
  unfold ExpansionCandidate.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [exact Hpal|].
  intros Heq.
  split.
  - destruct (Z_lt_ge_dec limit len); [lia|].
    assert (limit = len) by lia; subst limit.
    assert (0 <= 2 * i - len < len) by lia.
    specialize (Hnonzero (2 * i - len) H).
    replace (i - (len - i)) with (2 * i - len) in Heq by lia.
    replace (i + (len - i)) with len in Heq by lia.
    rewrite Hend in Heq.
    congruence.
  - destruct (Z_lt_ge_dec 0 (i - (limit - i))); [lia|].
    assert (i - (limit - i) = 0) by lia.
    assert (0 < limit < len).
    {
      split; [lia|].
      destruct (Z_lt_ge_dec limit len); [lia|].
      assert (limit = len) by lia; subst limit.
      replace (i - (len - i)) with 0 in Heq by lia.
      replace (i + (len - i)) with len in Heq by lia.
      rewrite Hstart in Heq.
      rewrite Hend in Heq.
      discriminate.
    }
    assert (Hlimit_range : 0 <= limit < len) by lia.
    specialize (Hnot36 limit H0).
    replace (i - (limit - i)) with 0 in Heq by lia.
    replace (i + (limit - i)) with limit in Heq by lia.
    rewrite Hstart in Heq.
    congruence.
Qed.
(* Rules out the degenerate "best length is zero" case once the loop has seen
   a real alphanumeric character. *)
Lemma manacher_best_zero_keep_edge_contradiction:
  forall str s2 len i r maxLen,
    ManacherTransformedString str s2 len ->
    ExpansionCandidate s2 len i r ->
    maxLen = 0 ->
    maxLen >= r - 1 ->
    1 <= i ->
    i <= 2 ->
    Znth (i + r - 0) s2 0 <> Znth (i - r - 0) s2 0 ->
    i + 1 <= 2.
Proof.
  intros str s2 len i r maxLen HT HC Hmax Hge Hi Hile Hneq.
  destruct HC as [_ [Hr [Hcr [Hpr _]]]].
  assert (r = 1) by lia.
  subst r maxLen.
  assert (i = 1 \/ i = 2) as [-> | ->] by lia; [lia|].
  exfalso.
  destruct HT as [Hlen [HZlen [Hfirst [Hlast [Hnul [Hnot36 [Hodd Hnot0]]]]]]].
  assert (0 <= 0 < Zlength str) as Hk0 by lia.
  pose proof (Hodd 0 Hk0) as [Hone _].
  replace (2 * 0 + 1) with 1 in Hone by lia.
  assert (Zlength str = 1 \/ 2 <= Zlength str) as [Hz1 | Hz2] by lia.
  - assert (len = 4) by lia.
    replace (2 + 1 - 0) with (len - 1) in Hneq by lia.
    replace (2 - 1 - 0) with 1 in Hneq by lia.
    congruence.
  - assert (0 <= 1 < Zlength str) as Hk1 by lia.
    pose proof (Hodd 1 Hk1) as [Hthree _].
    replace (2 * 1 + 1) with 3 in Hthree by lia.
    replace (2 + 1 - 0) with 3 in Hneq by lia.
    replace (2 - 1 - 0) with 1 in Hneq by lia.
    congruence.
Qed.
(* After an expansion stops by mismatch, keeping the old best remains sound
   when the new radius is not better. *)
Lemma manacher_best_radius_keep_after_mismatch:
  forall str s2 len p_written i r id limit maxId maxLen,
    ManacherLoopState str s2 len (sublist 0 i p_written) i id limit maxId maxLen ->
    ExpansionCandidate s2 len i r ->
    maxLen >= r - 1 ->
    Znth (i + r - 0) s2 0 <> Znth (i - r - 0) s2 0 ->
    Zlength p_written = i + 1 ->
    Znth i p_written 0 = r ->
    1 <= i ->
    i < len ->
    ManacherLoopState str s2 len p_written (i + 1) id limit maxId maxLen.
Proof.
  intros str s2 len p_written i r id limit maxId maxLen
    HLoop HC Hge Hneq Hlenp Hpi Hi Hilt.
  destruct HLoop as [HT [HR [Hid [Hcur HB]]]].
  unfold ManacherLoopState.
  split; [exact HT|].
  split.
  - unfold RadiusTablePrefix in *.
    destruct HR as [HRlen [HRbounds HRmax]].
    split; [exact Hlenp|].
    split; [lia|].
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + specialize (HRmax k ltac:(lia)).
      rewrite (Znth_sublist0 0 k i p_written) in HRmax by lia.
      exact HRmax.
    + assert (k = i) by lia.
      subst k.
      rewrite Hpi.
      unfold CenterRadiusMaximal.
      split.
      * destruct HC as [_ [_ [_ [_ [Hpal _]]]]].
        exact Hpal.
      * right; right.
        replace (i - r) with (i - r - 0) by lia.
        replace (i + r) with (i + r - 0) by lia.
        intros Heq; apply Hneq; symmetry; exact Heq.
  - split; [lia|].
    split; [exact Hcur|].
    unfold BestRadiusPrefix in *.
    destruct HB as [HBbounds [HBmaxLen [HBmaxId [HBpal [HBall HBex]]]]].
    repeat split; try lia.
    + destruct HBpal as [[Hz Hupto] | Hpal].
      * destruct (Z_lt_ge_dec i 2) as [Hi2 | Hige2].
        -- left; lia.
        -- left.
           split; [lia|].
           eapply manacher_best_zero_keep_edge_contradiction; eauto; lia.
      * right; exact Hpal.
    + intros k Hk.
      destruct (Z_lt_ge_dec k i) as [Hki | Hki].
      * specialize (HBall k ltac:(lia)).
        rewrite (Znth_sublist0 0 k i p_written) in HBall by lia.
        exact HBall.
      * assert (k = i) by lia.
        subst k.
        rewrite Hpi.
        lia.
    + destruct HBex as [[Hz Hupto] | [k [Hk1 [Hkmax Hval]]]].
      * destruct (Z_lt_ge_dec i 2) as [Hi2 | Hige2].
        -- left; lia.
        -- left.
           split; [lia|].
           eapply manacher_best_zero_keep_edge_contradiction; eauto; lia.
      * right.
        exists k.
        repeat split; try lia.
        rewrite (Znth_sublist0 0 k i p_written) in Hval by lia.
        exact Hval.
Qed.
(* Same best-preservation fact as above, for the branch that also updates the
   current rightmost window. *)
Lemma manacher_best_radius_keep_after_mismatch_new_window:
  forall str s2 len p_written i r id limit maxId maxLen,
    ManacherLoopState str s2 len (sublist 0 i p_written) i id limit maxId maxLen ->
    ExpansionCandidate s2 len i r ->
    maxLen >= r - 1 ->
    Znth (i + r - 0) s2 0 <> Znth (i - r - 0) s2 0 ->
    Zlength p_written = i + 1 ->
    Znth i p_written 0 = r ->
    1 <= i ->
    i < len ->
    ManacherLoopState str s2 len p_written (i + 1) i (i + r) maxId maxLen.
Proof.
  intros str s2 len p_written i r id limit maxId maxLen
    HLoop HC Hge Hneq Hlenp Hpi Hi Hilt.
  pose proof (manacher_best_radius_keep_after_mismatch
    str s2 len p_written i r id limit maxId maxLen
    HLoop HC Hge Hneq Hlenp Hpi Hi Hilt) as HKeep.
  destruct HKeep as [HT [HR [_ [_ HB]]]].
  unfold ManacherLoopState.
  split; [exact HT|].
  split; [exact HR|].
  split; [lia|].
  split.
  - unfold CurrentRightmostWindow.
    destruct HC as [[HCi HClen] [Hrad [Hlower [Hupper [Hpal _]]]]].
    split; [lia|].
    split; [lia|].
    intros _.
    replace (i + r - i) with r by lia.
    exact Hpal.
  - exact HB.
Qed.
(* Packages the main loop invariant after finishing an expansion whose window
   does not extend beyond the previous right boundary. *)
Lemma expansion_loop_best_update_inside :
  forall str s2 len p_written i r id limit maxId maxLen,
    maxLen < r - 1 ->
    i + r <= limit ->
    Znth (i + r - 0) s2 0 <> Znth (i - r - 0) s2 0 ->
    1 <= i ->
    i < len ->
    1 <= r ->
    0 <= i - r ->
    i + r <= len ->
    ExpansionLoopState str s2 len p_written i r id limit maxId maxLen ->
    ManacherLoopState str s2 len p_written (i + 1) id limit i (r - 1).
Proof.
  intros str s2 len p_written i r id limit maxId maxLen
         Hbest_lt Hlimit Hneq Hi Hilen Hr Hleft Hright Hexp.
  unfold ExpansionLoopState in Hexp.
  destruct Hexp as [Hp_len [Hloop [Hp_i Hcand]]].
  unfold ManacherLoopState in Hloop |- *.
  destruct Hloop as [Htrans [Hradius [Hwindow Hbest]]].
  unfold RadiusTablePrefix in Hradius.
  destruct Hradius as [Hsub_len [Hupto Hmax_old]].
  unfold BestRadiusPrefix in Hbest.
  destruct Hbest as [Hbest_upto [Hmax_nonneg [Hmaxid_bounds
           [Hbest_pal [Hbest_bound Hbest_exists]]]]].
  destruct Hbest_exists as [Hbest_bound_old Hbest_exists_old].
  unfold ExpansionCandidate in Hcand.
  destruct Hcand as [Hcenter [Hrad_pos [Hcand_left [Hcand_right [Hpal Hextend]]]]].
  split; [exact Htrans |].
  split.
  - unfold RadiusTablePrefix.
    split; [exact Hp_len |].
    split; [lia |].
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hik].
    + assert (Hz : Znth k (sublist 0 i p_written) 0 = Znth k p_written 0).
      { apply Znth_sublist0; lia. }
      rewrite <- Hz.
      apply Hmax_old; lia.
    + assert (k = i) by lia; subst k.
      rewrite Hp_i.
      unfold CenterRadiusMaximal.
      split; [exact Hpal |].
      right; right.
      replace (i - r) with (i - r - 0) by lia.
      replace (i + r) with (i + r - 0) by lia.
      intro Heq; apply Hneq; symmetry; exact Heq.
  - split; [lia |].
    split; [exact Hbest_upto |].
    unfold BestRadiusPrefix.
    repeat split; try lia.
    + right.
      replace (r - 1 + 1) with r by lia.
      exact Hpal.
    + intros k Hk.
      destruct (Z_lt_ge_dec k i) as [Hki | Hik].
      * specialize (Hbest_bound_old k ltac:(lia)).
        assert (Hz : Znth k (sublist 0 i p_written) 0 = Znth k p_written 0).
        { apply Znth_sublist0; lia. }
        rewrite <- Hz.
        lia.
      * assert (k = i) by lia; subst k.
        rewrite Hp_i; lia.
    + right.
      exists i.
      repeat split; try lia.
Qed.
(* Packages the main loop invariant after finishing an expansion that becomes
   the new rightmost window. *)
Lemma expansion_loop_best_update_extend :
  forall str s2 len p_written i r id limit maxId maxLen,
    maxLen < r - 1 ->
    i + r > limit ->
    Znth (i + r - 0) s2 0 <> Znth (i - r - 0) s2 0 ->
    1 <= i ->
    i < len ->
    1 <= r ->
    0 <= i - r ->
    i + r <= len ->
    ExpansionLoopState str s2 len p_written i r id limit maxId maxLen ->
    ManacherLoopState str s2 len p_written (i + 1) i (i + r) i (r - 1).
Proof.
  intros str s2 len p_written i r id limit maxId maxLen
         Hbest_lt Hlimit Hneq Hi Hilen Hr Hleft Hright Hexp.
  unfold ExpansionLoopState in Hexp.
  destruct Hexp as [Hp_len [Hloop [Hp_i Hcand]]].
  unfold ManacherLoopState in Hloop |- *.
  destruct Hloop as [Htrans [Hradius [Hwindow Hbest]]].
  unfold RadiusTablePrefix in Hradius.
  destruct Hradius as [Hsub_len [Hupto Hmax_old]].
  unfold BestRadiusPrefix in Hbest.
  destruct Hbest as [Hbest_upto [Hmax_nonneg [Hmaxid_bounds
           [Hbest_pal [Hbest_bound Hbest_exists]]]]].
  destruct Hbest_exists as [Hbest_bound_old Hbest_exists_old].
  unfold ExpansionCandidate in Hcand.
  destruct Hcand as [Hcenter [Hrad_pos [Hcand_left [Hcand_right [Hpal Hextend]]]]].
  split; [exact Htrans |].
  split.
  - unfold RadiusTablePrefix.
    split; [exact Hp_len |].
    split; [lia |].
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hik].
    + assert (Hz : Znth k (sublist 0 i p_written) 0 = Znth k p_written 0).
      { apply Znth_sublist0; lia. }
      rewrite <- Hz.
      apply Hmax_old; lia.
    + assert (k = i) by lia; subst k.
      rewrite Hp_i.
      unfold CenterRadiusMaximal.
      split; [exact Hpal |].
      right; right.
      replace (i - r) with (i - r - 0) by lia.
      replace (i + r) with (i + r - 0) by lia.
      intro Heq; apply Hneq; symmetry; exact Heq.
  - split; [lia |].
    split.
    + unfold CurrentRightmostWindow.
      split; [lia |].
      split; [lia |].
      intros Hlt.
      replace (i + r - i) with r by lia.
      exact Hpal.
    + unfold BestRadiusPrefix.
      repeat split; try lia.
      * right.
        replace (r - 1 + 1) with r by lia.
        exact Hpal.
      * intros k Hk.
        destruct (Z_lt_ge_dec k i) as [Hki | Hik].
        -- specialize (Hbest_bound_old k ltac:(lia)).
           assert (Hz : Znth k (sublist 0 i p_written) 0 = Znth k p_written 0).
           { apply Znth_sublist0; lia. }
           rewrite <- Hz.
           lia.
        -- assert (k = i) by lia; subst k.
           rewrite Hp_i; lia.
      * right.
        exists i.
        repeat split; try lia.
Qed.
(* Splits an uninitialized output buffer into an empty written prefix and an
   uninitialized suffix; useful when output copying starts at length zero. *)
Lemma char_undef_full_to_full0_undef:
  forall x n,
    0 <= n ->
    CharArray.undef_full x n |--
      CharArray.full x 0 nil ** CharArray.undef_seg x 0 n.
Proof.
  intros.
  sep_apply (CharArray.undef_full_to_undef_seg x n).
  rewrite (CharArray.full_empty x 0).
  cancel (CharArray.undef_seg x 0 n).
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; lia.
Qed.

(* Merges two adjacent CharArray uninitialized segments starting at zero back
   into a full uninitialized block with the original base address. *)
Lemma char_undef_seg0_merge_to_undef_full:
  forall x mid hi,
    0 <= mid <= hi ->
    CharArray.undef_seg x 0 mid ** CharArray.undef_seg x mid hi |--
    CharArray.undef_full x hi.
Proof.
  intros.
  sep_apply (CharArray.undef_seg_merge_to_undef_full x 0 mid hi); try lia.
  replace (x + 0 * sizeof (CHAR)) with x by lia.
  replace (hi - 0) with hi by lia.
  cancel.
Qed.

(* IntArray analogue of [char_undef_seg0_merge_to_undef_full], used when
   releasing the local radius table. *)
Lemma int_undef_seg0_merge_to_undef_full:
  forall x mid hi,
    0 <= mid <= hi ->
    IntArray.undef_seg x 0 mid ** IntArray.undef_seg x mid hi |--
    IntArray.undef_full x hi.
Proof.
  intros.
  sep_apply (IntArray.undef_seg_merge_to_undef_full x 0 mid hi); try lia.
  replace (x + 0 * sizeof (INT)) with x by lia.
  replace (hi - 0) with hi by lia.
  cancel.
Qed.

(* Initializes output-copy progress before any transformed-window position has
   been visited. *)
Lemma output_copy_prefix_nil:
  forall s2 start,
    0 <= start ->
    start <= Zlength s2 ->
    OutputCopyPrefix s2 nil start start 0.
Proof.
  intros.
  unfold OutputCopyPrefix.
  repeat split; try lia.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.
(* Advances output-copy progress over a non-# transformed character, appending
   it to the copied output and increasing [j]. *)
Lemma output_copy_prefix_step_nonhash:
  forall s2 out start i j maxLen,
    OutputCopyPrefix s2 out start i j ->
    OutputCopyBound s2 start (i + 1) maxLen ->
    Znth (i - 0) s2 0 <> 35 ->
    OutputCopyPrefix s2 (out ++ Znth (i - 0) s2 0 :: nil) start (i + 1) (j + 1) /\
    j + 1 <= maxLen.
Proof.
  intros s2 out start i j maxLen Hpref Hbound Hneq.
  unfold OutputCopyPrefix in Hpref.
  unfold OutputCopyBound in Hbound.
  destruct Hpref as [Hs0 [Hsi [HiLen [Hout Hj]]]].
  destruct Hbound as [_ [_ [Hi1Len Hbound_len]]].
  assert (HiLen' : i < Zlength s2) by lia.
  assert (Hstep :
    NonHashChars (sublist start (i + 1) s2) =
    NonHashChars (sublist start i s2) ++ Znth i s2 0 :: nil).
  {
    rewrite (sublist_split start (i + 1) i s2) by lia.
    rewrite (sublist_single 0 i s2) by lia.
    unfold NonHashChars.
    rewrite filter_app.
    simpl.
    replace (i - 0) with i in Hneq by lia.
    destruct (Z.eqb (Znth i s2 0) 35) eqn:Heq.
    - apply Z.eqb_eq in Heq; congruence.
    - reflexivity.
  }
  split.
  - unfold OutputCopyPrefix.
    repeat split; try lia.
    + subst out. replace (i - 0) with i by lia. rewrite Hstep. reflexivity.
    + subst out j. rewrite Zlength_app_cons. lia.
  - subst out j. rewrite Hstep in Hbound_len.
    rewrite Zlength_app_cons in Hbound_len.
    lia.
Qed.
(* Advances output-copy progress over a '#' marker without changing the copied
   output length. *)
Lemma output_copy_prefix_step_hash:
  forall s2 out start i j maxLen,
    OutputCopyPrefix s2 out start i j ->
    OutputCopyBound s2 start (i + 1) maxLen ->
    Znth (i - 0) s2 0 = 35 ->
    OutputCopyPrefix s2 out start (i + 1) j.
Proof.
  intros s2 out start i j maxLen Hpref Hbound Heq.
  unfold OutputCopyPrefix in Hpref.
  unfold OutputCopyBound in Hbound.
  destruct Hpref as [Hs0 [Hsi [HiLen [Hout Hj]]]].
  destruct Hbound as [_ [_ [Hi1Len _]]].
  assert (HiLen' : i < Zlength s2) by lia.
  assert (Hstep :
    NonHashChars (sublist start (i + 1) s2) =
    NonHashChars (sublist start i s2)).
  {
    rewrite (sublist_split start (i + 1) i s2) by lia.
    rewrite (sublist_single 0 i s2) by lia.
    unfold NonHashChars.
    rewrite filter_app.
    simpl.
    replace (i - 0) with i in Heq by lia.
    rewrite Heq.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  }
  unfold OutputCopyPrefix.
  repeat split; try lia.
  subst out. rewrite Hstep. reflexivity.
Qed.
(* Derives basic bounds for the final selected best window from the completed
   Manacher loop state. *)
Lemma manacher_final_selected_window_bounds:
  forall str s2 p len id limit maxId maxLen n_pre,
    string_length str = n_pre ->
    1 <= n_pre ->
    len = 2 * n_pre + 2 ->
    ManacherLoopState str s2 len p len id limit maxId maxLen ->
    1 <= maxLen /\ 0 <= maxId - maxLen /\ maxId + maxLen < len.
Proof.
  intros str s2 p len id limit maxId maxLen n_pre Hstrlen Hn Hlen Hstate.
  unfold string_length in Hstrlen.
  unfold ManacherLoopState in Hstate.
  destruct Hstate as [Htrans [Hrt [_ [_ Hbest]]]].
  unfold ManacherTransformedString in Htrans.
  destruct Htrans as
    [_ [_ [_ [Hlast_hash [_ [_ [Hchars _]]]]]]].
  unfold RadiusTablePrefix in Hrt.
  destruct Hrt as [_ [_ Hmaximal]].
  unfold BestRadiusPrefix in Hbest.
  destruct Hbest as [_ [_ [_ [Hpal_or [Hall _]]]]].
  assert (Hlen_gt2 : 2 < len) by lia.
  assert (Hp2_ge2 : 2 <= Znth 2 p 0).
  {
    pose proof (Hmaximal 2 ltac:(lia)) as Hcm.
    unfold CenterRadiusMaximal in Hcm.
    destruct Hcm as [Hpal Hstop].
    unfold CenterRadiusPalindrome in Hpal.
    destruct Hpal as [_ [Hrad [_ [_ _]]]].
    assert (Hz1 : Znth 1 s2 0 = 35).
    {
      destruct (Hchars 0 ltac:(rewrite Hstrlen; lia)) as [Hz _].
      exact Hz.
    }
    assert (Hz3 : Znth 3 s2 0 = 35).
    {
      destruct (Z_lt_ge_dec 1 (Zlength str)) as [Hlt | Hge].
      - destruct (Hchars 1 ltac:(lia)) as [Hz _].
        exact Hz.
      - replace 3 with (len - 1) by (rewrite Hstrlen in Hge; lia).
        exact Hlast_hash.
    }
    assert (Znth 2 p 0 <> 1).
    {
      intro Hp.
      rewrite Hp in Hstop.
      destruct Hstop as [Hstop | [Hstop | Hstop]]; try lia.
      replace (2 - 1) with 1 in Hstop by lia.
      replace (2 + 1) with 3 in Hstop by lia.
      rewrite Hz1 in Hstop.
      rewrite Hz3 in Hstop.
      congruence.
    }
    lia.
  }
  assert (HmaxLen_pos : 1 <= maxLen).
  {
    pose proof (Hall 2 ltac:(lia)) as Hle.
    lia.
  }
  assert (Hbounds : 0 <= maxId - maxLen /\ maxId + maxLen < len).
  {
    destruct Hpal_or as [[Hzero Hsmall] | Hpal].
    - lia.
    - unfold CenterRadiusPalindrome in Hpal.
      destruct Hpal as [_ [_ [Hleft [Hright _]]]].
      lia.
  }
  tauto.
Qed.

(* Small local helper for list-length arithmetic in the counting lemmas below. *)
Ltac zlength_simpl := rewrite ?Zlength_cons, ?Zlength_nil in *.

(* Nat-indexed counting lemma: if all even positions in a length [2m+1] list
   are '#', then at most [m] non-# characters remain. *)
Lemma nonhash_even_slots_hash_bound_nat:
  forall (m : nat) xs,
    (forall k, 0 <= k < Zlength xs -> k mod 2 = 0 -> Znth k xs 0 = 35) ->
    Zlength xs <= 2 * Z.of_nat m + 1 ->
    Zlength (NonHashChars xs) <= Z.of_nat m.
Proof.
  induction m as [|m IH]; intros xs Heven Hlen.
  - destruct xs as [|a xs].
    + unfold NonHashChars. simpl. zlength_simpl. lia.
    + destruct xs as [|b xs].
      * assert (Ha : a = 35).
        {
          assert (Hb0 : 0 <= 0 < Zlength [a]) by (zlength_simpl; lia).
          assert (Hm0 : 0 mod 2 = 0) by reflexivity.
          pose proof (Heven 0 Hb0 Hm0) as Hz.
          rewrite Znth0_cons in Hz. exact Hz.
        }
        subst. unfold NonHashChars. simpl. zlength_simpl. lia.
      * rewrite Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct xs as [|a xs].
    + unfold NonHashChars. simpl. zlength_simpl. lia.
    + assert (Ha : a = 35).
      {
        assert (Hb0 : 0 <= 0 < Zlength (a :: xs)).
        { zlength_simpl. rewrite Zlength_correct. lia. }
        assert (Hm0 : 0 mod 2 = 0) by reflexivity.
        pose proof (Heven 0 Hb0 Hm0) as Hz.
        rewrite Znth0_cons in Hz. exact Hz.
      }
      subst a. destruct xs as [|b xs].
      * unfold NonHashChars. simpl. zlength_simpl. lia.
      * assert (Htail_even:
          forall k : Z, 0 <= k < Zlength xs -> k mod 2 = 0 ->
            Znth k xs 0 = 35).
        {
          intros k Hk Hmod.
          assert (Hb : 0 <= k + 2 < Zlength (35 :: b :: xs)).
          {
            zlength_simpl.
            replace (Z.succ (Z.succ (Zlength xs))) with (Zlength xs + 2) by lia.
            lia.
          }
          assert (Hm : (k + 2) mod 2 = 0).
          { rewrite Z.add_mod by lia. rewrite Hmod. reflexivity. }
          pose proof (Heven (k + 2) Hb Hm) as Hz.
          rewrite Znth_cons in Hz by lia.
          replace (k + 2 - 1) with (k + 1) in Hz by lia.
          rewrite Znth_cons in Hz by lia.
          replace (k + 1 - 1) with k in Hz by lia.
          exact Hz.
        }
        assert (Htail_len : Zlength xs <= 2 * Z.of_nat m + 1).
        { zlength_simpl. lia. }
        specialize (IH xs Htail_even Htail_len).
        unfold NonHashChars in *.
        simpl.
        destruct (Z.eqb b 35); simpl; zlength_simpl; lia.
Qed.

(* Z-indexed wrapper around [nonhash_even_slots_hash_bound_nat]. *)
Lemma nonhash_even_slots_hash_bound:
  forall xs m,
    0 <= m ->
    (forall k, 0 <= k < Zlength xs -> k mod 2 = 0 -> Znth k xs 0 = 35) ->
    Zlength xs <= 2 * m + 1 ->
    Zlength (NonHashChars xs) <= m.
Proof.
  intros xs m Hm Heven Hlen.
  pose proof (nonhash_even_slots_hash_bound_nat (Z.to_nat m) xs Heven) as Hbound.
  rewrite Z2Nat.id in Hbound by lia.
  apply Hbound. lia.
Qed.

(* Nat-indexed exact counting: even slots are '#', odd slots are not '#', so
   the transformed slice contains exactly [m] original characters. *)
Lemma nonhash_even_hash_odd_nonhash_exact_nat:
  forall (m : nat) xs,
    Zlength xs = 2 * Z.of_nat m + 1 ->
    (forall k, 0 <= k < Zlength xs -> k mod 2 = 0 -> Znth k xs 0 = 35) ->
    (forall k, 0 <= k < Zlength xs -> k mod 2 = 1 -> Znth k xs 0 <> 35) ->
    Zlength (NonHashChars xs) = Z.of_nat m.
Proof.
  induction m as [|m IH]; intros xs Hlen Heven Hodd.
  - destruct xs as [|a xs].
    + unfold NonHashChars. simpl. zlength_simpl. lia.
    + destruct xs as [|b xs].
      * assert (Ha : a = 35).
        {
          assert (Hb0 : 0 <= 0 < Zlength [a]) by (zlength_simpl; lia).
          pose proof (Heven 0 Hb0 ltac:(reflexivity)) as Hz.
          rewrite Znth0_cons in Hz. exact Hz.
        }
        subst. unfold NonHashChars. simpl. zlength_simpl. lia.
      * rewrite Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct xs as [|a xs].
    + rewrite Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct xs as [|b xs].
      * rewrite Zlength_correct in Hlen. simpl in Hlen. lia.
      * assert (Ha : a = 35).
        {
          assert (Hb0 : 0 <= 0 < Zlength (a :: b :: xs))
            by (zlength_simpl; rewrite Zlength_correct; lia).
          pose proof (Heven 0 Hb0 ltac:(reflexivity)) as Hz.
          rewrite Znth0_cons in Hz. exact Hz.
        }
        assert (Hbne : b <> 35).
        {
          assert (Hb1 : 0 <= 1 < Zlength (a :: b :: xs))
            by (zlength_simpl; rewrite Zlength_correct; lia).
          pose proof (Hodd 1 Hb1 ltac:(reflexivity)) as Hz.
          rewrite Znth_cons in Hz by lia.
          replace (1 - 1) with 0 in Hz by lia.
          rewrite Znth0_cons in Hz. exact Hz.
        }
        subst a.
        assert (Htail_len : Zlength xs = 2 * Z.of_nat m + 1).
        {
          zlength_simpl.
          replace (Z.succ (Z.succ (Zlength xs))) with (Zlength xs + 2) in Hlen by lia.
          lia.
        }
        assert (Htail_even:
          forall k, 0 <= k < Zlength xs -> k mod 2 = 0 -> Znth k xs 0 = 35).
        {
          intros k Hk Hm.
          assert (Hbnd : 0 <= k + 2 < Zlength (35 :: b :: xs)).
          {
            zlength_simpl.
            replace (Z.succ (Z.succ (Zlength xs))) with (Zlength xs + 2) by lia.
            lia.
          }
          assert (Hmod : (k + 2) mod 2 = 0).
          { rewrite Z.add_mod by lia. rewrite Hm. reflexivity. }
          pose proof (Heven (k + 2) Hbnd Hmod) as Hz.
          rewrite Znth_cons in Hz by lia.
          replace (k + 2 - 1) with (k + 1) in Hz by lia.
          rewrite Znth_cons in Hz by lia.
          replace (k + 1 - 1) with k in Hz by lia.
          exact Hz.
        }
        assert (Htail_odd:
          forall k, 0 <= k < Zlength xs -> k mod 2 = 1 -> Znth k xs 0 <> 35).
        {
          intros k Hk Hm.
          assert (Hbnd : 0 <= k + 2 < Zlength (35 :: b :: xs)).
          {
            zlength_simpl.
            replace (Z.succ (Z.succ (Zlength xs))) with (Zlength xs + 2) by lia.
            lia.
          }
          assert (Hmod : (k + 2) mod 2 = 1).
          { rewrite Z.add_mod by lia. rewrite Hm. reflexivity. }
          pose proof (Hodd (k + 2) Hbnd Hmod) as Hz.
          rewrite Znth_cons in Hz by lia.
          replace (k + 2 - 1) with (k + 1) in Hz by lia.
          rewrite Znth_cons in Hz by lia.
          replace (k + 1 - 1) with k in Hz by lia.
          exact Hz.
        }
        specialize (IH xs Htail_len Htail_even Htail_odd).
        unfold NonHashChars in *.
        simpl.
        destruct (Z.eqb b 35) eqn:Hbeq.
        { apply Z.eqb_eq in Hbeq; contradiction. }
        simpl. rewrite Zlength_cons. lia.
Qed.

(* Z-indexed wrapper around [nonhash_even_hash_odd_nonhash_exact_nat]. *)
Lemma nonhash_even_hash_odd_nonhash_exact:
  forall xs m,
    0 <= m ->
    Zlength xs = 2 * m + 1 ->
    (forall k, 0 <= k < Zlength xs -> k mod 2 = 0 -> Znth k xs 0 = 35) ->
    (forall k, 0 <= k < Zlength xs -> k mod 2 = 1 -> Znth k xs 0 <> 35) ->
    Zlength (NonHashChars xs) = m.
Proof.
  intros xs m Hm Hlen Heven Hodd.
  pose proof (nonhash_even_hash_odd_nonhash_exact_nat
    (Z.to_nat m) xs) as Hexact.
  rewrite Z2Nat.id in Hexact by lia.
  apply Hexact; auto.
Qed.

(* In the complete transformed string, every odd transformed slot is '#',
   including the final marker before [len]. *)
Lemma manacher_transformed_hash_at_odd_slot:
  forall s s2 len q,
    ManacherTransformedString s s2 len ->
    0 <= 2 * q + 1 < len ->
    Znth (2 * q + 1) s2 0 = 35.
Proof.
  intros s s2 len q Htrans Hq.
  pose proof Htrans as Htrans_full.
  unfold ManacherTransformedString in Htrans.
  destruct Htrans as [Hlen [_ [_ [Hlast [_ [_ [Hchars _]]]]]]].
  destruct (Z_lt_ge_dec q (Zlength s)) as [Hlt | Hge].
  - destruct (Hchars q ltac:(lia)) as [Hhash _].
    exact Hhash.
  - assert (q = Zlength s) by lia.
    subst q.
    replace (2 * Zlength s + 1) with (len - 1) by lia.
    exact Hlast.
Qed.

(* Even transformed slots that correspond to original characters are not '#',
   by the alphanumeric input assumption. *)
Lemma manacher_transformed_even_slot_not_hash:
  forall s s2 len n_pre q,
    AlnumString s ->
    string_length s = n_pre ->
    len = 2 * n_pre + 2 ->
    ManacherTransformedString s s2 len ->
    1 <= q <= n_pre ->
    Znth (2 * q) s2 0 <> 35.
Proof.
  intros s s2 len n_pre q Halnum Hstrlen Hlen Htrans Hq.
  unfold ManacherTransformedString in Htrans.
  destruct Htrans as [_ [_ [_ [_ [_ [_ [Hchars _]]]]]]].
  destruct (Hchars (q - 1)) as [_ Hchar]; [unfold string_length in Hstrlen; lia|].
  replace (2 * (q - 1) + 2) with (2 * q) in Hchar by lia.
  rewrite Hchar.
  specialize (Halnum (q - 1) ltac:(unfold string_length in Hstrlen; lia)).
  unfold AlnumCode in Halnum.
  lia.
Qed.

(* The final selected palindrome window starts at an odd transformed index,
   i.e. at a '#' marker.  This makes the non-# counting exact. *)
Lemma manacher_final_selected_window_start_odd:
  forall str s2 p len id limit maxId maxLen n_pre,
    string_length str = n_pre ->
    1 <= n_pre ->
    len = 2 * n_pre + 2 ->
    ManacherLoopState str s2 len p len id limit maxId maxLen ->
    exists q, maxId - maxLen = 2 * q + 1.
Proof.
  intros str s2 p len id limit maxId maxLen n_pre Hstrlen Hn Hlen Hstate.
  pose proof (manacher_final_selected_window_bounds
    str s2 p len id limit maxId maxLen n_pre Hstrlen Hn Hlen Hstate)
    as [HmaxLen_pos [Hstart_nonneg Hend_lt]].
  unfold ManacherLoopState in Hstate.
  destruct Hstate as [Htrans [Hrt [_ [_ Hbest]]]].
  unfold RadiusTablePrefix in Hrt.
  destruct Hrt as [_ [_ Hmaximal]].
  unfold BestRadiusPrefix in Hbest.
  destruct Hbest as [_ [_ [_ [Hpal_or [_ Hexists]]]]].
  destruct Hpal_or as [[Hzero _] | Hpal_best]; [lia |].
  destruct Hexists as [[Hzero _] | [k [Hk_bounds [Hk_eq Hk_radius]]]]; [lia |].
  subst k.
  pose proof (Hmaximal maxId ltac:(unfold CenterRadiusPalindrome in Hpal_best; tauto))
    as Hmaximal_at.
  replace (Znth maxId p 0) with (maxLen + 1) in Hmaximal_at by lia.
  unfold CenterRadiusMaximal in Hmaximal_at.
  destruct Hmaximal_at as [Hpal_max Hstop].
  unfold CenterRadiusPalindrome in Hpal_max.
  destruct Hpal_max as [_ [_ [_ [_ Hsym]]]].
  pose proof Htrans as Htrans_full.
  unfold ManacherTransformedString in Htrans.
  destruct Htrans as [Hlen_shape [_ [Hfirst [_ [_ [Hnot36 _]]]]]].
  set (start := maxId - maxLen).
  set (finish := maxId + maxLen).
  assert (Hendpoint_eq : Znth start s2 0 = Znth finish s2 0).
  {
    specialize (Hsym maxLen ltac:(lia)).
    replace (maxId - maxLen) with start in Hsym by (unfold start; lia).
    replace (maxId + maxLen) with finish in Hsym by (unfold finish; lia).
    exact Hsym.
  }
  destruct (Z.eq_dec (start mod 2) 1) as [Hodd | Hnot_odd].
  - exists (start / 2).
    pose proof (Z.div_mod start 2 ltac:(lia)) as Hdiv.
    lia.
  - assert (Hstart_even : start mod 2 = 0).
    { pose proof (Z.mod_pos_bound start 2 ltac:(lia)); lia. }
    assert (Heven_repr : exists q, start = 2 * q).
    {
      exists (start / 2).
      pose proof (Z.div_mod start 2 ltac:(lia)) as Hdiv.
      lia.
    }
    destruct Heven_repr as [q Hq].
    destruct (Z.eq_dec start 0) as [Hstart_zero | Hstart_nonzero].
    + assert (Hfinish_pos : 0 < finish < len) by (unfold finish, start in *; lia).
      specialize (Hnot36 finish Hfinish_pos).
      rewrite Hstart_zero in Hendpoint_eq.
      unfold start in Hendpoint_eq.
      rewrite Hfirst in Hendpoint_eq.
      congruence.
    + assert (Hq_pos : 1 <= q) by (unfold start in *; lia).
      assert (Hfinish_repr : finish = 2 * (q + maxLen)).
      { unfold finish, start in *; lia. }
      assert (Hright_inside : finish + 1 < len).
      {
        assert (Hle : finish + 1 <= len) by lia.
        destruct (Z.eq_dec (finish + 1) len) as [Heq | Hneq]; [|lia].
        assert ((finish + 1) mod 2 = 1).
        {
          rewrite Hfinish_repr.
          replace (2 * (q + maxLen) + 1) with ((q + maxLen) * 2 + 1) by lia.
          rewrite Z.add_mod by lia.
          rewrite Z_mod_mult by lia.
          reflexivity.
        }
        assert (len mod 2 = 0).
        {
          rewrite Hlen.
          replace (2 * n_pre + 2) with ((n_pre + 1) * 2) by lia.
          rewrite Z_mod_mult by lia.
          reflexivity.
        }
        congruence.
      }
      assert (Hleft_hash : Znth (start - 1) s2 0 = 35).
      {
        replace (start - 1) with (2 * (q - 1) + 1) by lia.
        eapply manacher_transformed_hash_at_odd_slot; [exact Htrans_full |].
        unfold start in *; lia.
      }
      assert (Hright_hash : Znth (finish + 1) s2 0 = 35).
      {
        rewrite Hfinish_repr.
        replace (2 * (q + maxLen) + 1) with (2 * (q + maxLen) + 1) by lia.
        eapply manacher_transformed_hash_at_odd_slot; [exact Htrans_full |].
        lia.
      }
      destruct Hstop as [Hleft_stop | [Hright_stop | Hneq_stop]].
      * unfold start in *; lia.
      * unfold finish in *; lia.
      * replace (maxId - (maxLen + 1)) with (start - 1) in Hneq_stop by (unfold start; lia).
        replace (maxId + (maxLen + 1)) with (finish + 1) in Hneq_stop by (unfold finish; lia).
        congruence.
Qed.

(* Every prefix of the final selected transformed window copies at most
   [maxLen] original characters.  Used as the output-copy loop bound. *)
Lemma manacher_output_copy_bound_from_selected_window:
  forall str s2 len p id limit maxId maxLen n_pre cur,
    string_length str = n_pre ->
    1 <= n_pre ->
    len = 2 * n_pre + 2 ->
    ManacherLoopState str s2 len p len id limit maxId maxLen ->
    maxId - maxLen <= cur <= maxId + maxLen + 1 ->
    OutputCopyBound s2 (maxId - maxLen) cur maxLen.
Proof.
  intros str s2 len p id limit maxId maxLen n_pre cur
    Hstrlen Hn Hlen Hstate Hcur.
  pose proof (manacher_final_selected_window_bounds
    str s2 p len id limit maxId maxLen n_pre Hstrlen Hn Hlen Hstate)
    as [HmaxLen_pos [Hstart_nonneg Hend_lt]].
  pose proof (manacher_final_selected_window_start_odd
    str s2 p len id limit maxId maxLen n_pre Hstrlen Hn Hlen Hstate)
    as [q Hstart_odd].
  unfold OutputCopyBound.
  repeat split; try lia.
  - unfold ManacherLoopState in Hstate.
    destruct Hstate as [Htrans _].
    unfold ManacherTransformedString in Htrans.
    destruct Htrans as [_ [Hs2_len _]].
    rewrite Hs2_len. lia.
  - set (start := maxId - maxLen).
    assert (Hcur_len : cur <= len) by lia.
    unfold ManacherLoopState in Hstate.
    destruct Hstate as [Htrans _].
    pose proof Htrans as Htrans_full.
    unfold ManacherTransformedString in Htrans.
    destruct Htrans as [_ [Hs2_len _]].
    assert (Hcur_s2 : cur <= Zlength s2) by (rewrite Hs2_len; lia).
    eapply nonhash_even_slots_hash_bound with (m := maxLen).
    + lia.
    + intros k Hk Hk_even.
      assert (Hsub_len : Zlength (sublist start cur s2) = cur - start).
      { rewrite Zlength_sublist by lia. reflexivity. }
      rewrite Znth_sublist by lia.
      pose proof (Z.div_mod k 2 ltac:(lia)) as Hdiv.
      assert (Hk_start : k + start = 2 * (q + k / 2) + 1).
      {
        unfold start in Hstart_odd.
        lia.
      }
      replace (k + start) with (2 * (q + k / 2) + 1) by (symmetry; exact Hk_start).
      * eapply manacher_transformed_hash_at_odd_slot; [exact Htrans_full |].
        rewrite <- Hk_start.
        rewrite Hsub_len in Hk. unfold start in *; lia.
    + rewrite Zlength_sublist by lia.
      unfold start. lia.
Qed.

(* The whole selected transformed window contains exactly [maxLen] non-#
   characters. *)
Lemma manacher_selected_window_nonhash_length:
  forall str s2 len p id limit maxId maxLen n_pre,
    AlnumString str ->
    string_length str = n_pre ->
    1 <= n_pre ->
    len = 2 * n_pre + 2 ->
    ManacherLoopState str s2 len p len id limit maxId maxLen ->
    Zlength (NonHashChars (sublist (maxId - maxLen) (maxId + maxLen + 1) s2)) = maxLen.
Proof.
  intros str s2 len p id limit maxId maxLen n_pre Halnum Hstrlen Hn Hlen Hstate.
  pose proof (manacher_final_selected_window_bounds
    str s2 p len id limit maxId maxLen n_pre Hstrlen Hn Hlen Hstate)
    as [HmaxLen_pos [Hstart_nonneg Hend_lt]].
  pose proof (manacher_final_selected_window_start_odd
    str s2 p len id limit maxId maxLen n_pre Hstrlen Hn Hlen Hstate)
    as [q Hstart_odd].
  unfold ManacherLoopState in Hstate.
  destruct Hstate as [Htrans _].
  set (start := maxId - maxLen).
  set (finish := maxId + maxLen + 1).
  assert (Hsub_len : Zlength (sublist start finish s2) = 2 * maxLen + 1).
  {
    rewrite Zlength_sublist by (unfold start, finish; unfold ManacherTransformedString in Htrans; tauto || lia).
    unfold start, finish. lia.
  }
  apply (nonhash_even_hash_odd_nonhash_exact
    (sublist start finish s2) maxLen); try lia.
  - intros k Hk Hmod.
    rewrite Znth_sublist by (unfold start, finish in *; lia).
    pose proof (Z.div_mod k 2 ltac:(lia)) as Hdiv.
    replace (k + start) with (2 * (q + k / 2) + 1).
    + eapply manacher_transformed_hash_at_odd_slot; [exact Htrans|].
      rewrite Hsub_len in Hk. unfold start, finish in *; lia.
    + unfold start in Hstart_odd. lia.
  - intros k Hk Hmod.
    rewrite Znth_sublist by (unfold start, finish in *; lia).
    pose proof (Z.div_mod k 2 ltac:(lia)) as Hdiv.
    assert (Hk_decomp : k = 2 * (k / 2) + 1) by lia.
    assert (Hhalf : (k + 1) / 2 = k / 2 + 1).
    {
      replace (k + 1) with (2 * (k / 2 + 1)) by lia.
      replace (2 * (k / 2 + 1)) with ((k / 2 + 1) * 2) by lia.
      rewrite Z.div_mul by lia.
      reflexivity.
    }
    replace (k + start) with (2 * (q + (k + 1) / 2)).
    + eapply manacher_transformed_even_slot_not_hash; [exact Halnum|exact Hstrlen|exact Hlen|exact Htrans|].
      rewrite Hhalf.
      rewrite Hsub_len in Hk. unfold start, finish in *; lia.
    + unfold start in Hstart_odd.
      rewrite Hhalf.
      lia.
Qed.

(* At the end of output copying, the copy index [j] is exactly [maxLen]. *)
Lemma manacher_output_copy_prefix_full_j:
  forall str s2 len p id limit maxId maxLen n_pre out j,
    AlnumString str ->
    string_length str = n_pre ->
    1 <= n_pre ->
    len = 2 * n_pre + 2 ->
    ManacherLoopState str s2 len p len id limit maxId maxLen ->
    OutputCopyPrefix s2 out (maxId - maxLen) (maxId + maxLen + 1) j ->
    j = maxLen.
Proof.
  intros str s2 len p id limit maxId maxLen n_pre out j
    Halnum Hstrlen Hn Hlen Hstate Hpref.
  unfold OutputCopyPrefix in Hpref.
  destruct Hpref as [_ [_ [_ [Hout Hj]]]].
  subst j out.
  eapply manacher_selected_window_nonhash_length; eauto.
Qed.

(* Reads back an original string character from its even slot in the complete
   transformed string. *)
Lemma manacher_transformed_even_value:
  forall s s2 len q,
    ManacherTransformedString s s2 len ->
    1 <= q <= Zlength s ->
    Znth (2 * q) s2 0 = Znth (q - 1) s 0.
Proof.
  intros s s2 len q Htrans Hq.
  unfold ManacherTransformedString in Htrans.
  destruct Htrans as [_ [_ [_ [_ [_ [_ [Hchars _]]]]]]].
  destruct (Hchars (q - 1) ltac:(lia)) as [_ Hchar].
  replace (2 * (q - 1) + 2) with (2 * q) in Hchar by lia.
  exact Hchar.
Qed.

(* A maximal stored radius dominates any other palindromic radius at the same
   center. *)
Lemma center_radius_maximal_dominates:
  forall s2 len center r r',
    CenterRadiusMaximal s2 len center r ->
    CenterRadiusPalindrome s2 len center r' ->
    r' <= r.
Proof.
  intros s2 len center r r' Hmax Hpal'.
  unfold CenterRadiusMaximal in Hmax.
  destruct Hmax as [Hpal Hstop].
  unfold CenterRadiusPalindrome in Hpal.
  destruct Hpal as [_ [Hr [_ [_ _]]]].
  unfold CenterRadiusPalindrome in Hpal'.
  destruct Hpal' as [_ [Hr' [Hleft' [Hright' Hsym']]]].
  destruct (Z_le_gt_dec r' r) as [Hle | Hgt]; [lia |].
  specialize (Hsym' r ltac:(lia)).
  destruct Hstop as [Hleft | [Hright | Hneq]]; lia || congruence.
Qed.

(* Embeds an original-string palindrome segment into the transformed-string
   center/radius representation. *)
Lemma palindrome_segment_to_center_radius:
  forall s s2 len lo plen,
    ManacherTransformedString s s2 len ->
    PalindromeSegment s lo plen ->
    CenterRadiusPalindrome s2 len (2 * lo + plen + 1) (plen + 1).
Proof.
  intros s s2 len lo plen Htrans Hpal.
  unfold PalindromeSegment in Hpal.
  destruct Hpal as [Hlo [Hplen [Hrange Hsym_s]]].
  pose proof Htrans as Htrans_full.
  unfold ManacherTransformedString in Htrans.
  destruct Htrans as [Hlen [Hs2len [_ [_ [_ [_ [_ Hnonzero]]]]]]].
  unfold CenterRadiusPalindrome.
  repeat split; try lia.
  intros d Hd.
  set (center := 2 * lo + plen + 1).
  set (lpos := center - d).
  set (rpos := center + d).
  assert (Hlpos_bounds : 1 <= lpos < len) by (unfold lpos, center; lia).
  assert (Hrpos_bounds : 1 <= rpos < len) by (unfold rpos, center; lia).
  destruct (Z.eq_dec (lpos mod 2) 1) as [Hodd | Hnotodd].
  - assert (Hrodd : rpos mod 2 = 1).
    {
      replace rpos with (lpos + d * 2) by (unfold lpos, rpos; lia).
      rewrite Z.add_mod by lia.
      rewrite Z_mod_mult by lia.
      rewrite Z.add_0_r.
      rewrite Z.mod_mod by lia.
      exact Hodd.
    }
    assert (Hlrepr : lpos = 2 * (lpos / 2) + 1).
    { pose proof (Z.div_mod lpos 2 ltac:(lia)); lia. }
    assert (Hrrepr : rpos = 2 * (rpos / 2) + 1).
    { pose proof (Z.div_mod rpos 2 ltac:(lia)); lia. }
    rewrite Hlrepr.
    rewrite Hrrepr.
    rewrite (manacher_transformed_hash_at_odd_slot s s2 len (lpos / 2) Htrans_full ltac:(lia)).
    rewrite (manacher_transformed_hash_at_odd_slot s s2 len (rpos / 2) Htrans_full ltac:(lia)).
    reflexivity.
  - assert (Heven_l : lpos mod 2 = 0).
    { pose proof (Z.mod_pos_bound lpos 2 ltac:(lia)); lia. }
    assert (Heven_r : rpos mod 2 = 0).
    {
      replace rpos with (lpos + d * 2) by (unfold lpos, rpos; lia).
      rewrite Z.add_mod by lia.
      rewrite Z_mod_mult by lia.
      rewrite Z.add_0_r.
      rewrite Z.mod_mod by lia.
      exact Heven_l.
    }
    assert (Hlrepr : lpos = 2 * (lpos / 2)).
    { pose proof (Z.div_mod lpos 2 ltac:(lia)); lia. }
    assert (Hrrepr : rpos = 2 * (rpos / 2)).
    { pose proof (Z.div_mod rpos 2 ltac:(lia)); lia. }
    rewrite Hlrepr.
    rewrite Hrrepr.
    rewrite (manacher_transformed_even_value s s2 len (lpos / 2) Htrans_full ltac:(lia)).
    rewrite (manacher_transformed_even_value s s2 len (rpos / 2) Htrans_full ltac:(lia)).
    assert (Hk_bounds : 0 <= lpos / 2 - 1 - lo < plen).
    {
      unfold lpos, center in *.
      pose proof (Z.div_mod d 2 ltac:(lia)).
      lia.
    }
    specialize (Hsym_s (lpos / 2 - 1 - lo) Hk_bounds).
    replace (lo + (lpos / 2 - 1 - lo)) with (lpos / 2 - 1) in Hsym_s by lia.
    replace (lo + plen - 1 - (lpos / 2 - 1 - lo)) with (rpos / 2 - 1) in Hsym_s
      by (unfold lpos, rpos, center in *; lia).
    exact Hsym_s.
Qed.

(* Nat-indexed structural lemma: removing '#' markers from a selected
   transformed window recovers the corresponding original substring. *)
Lemma manacher_window_nonhash_substring_nat:
  forall n str s2 len q,
    AlnumString str ->
    ManacherTransformedString str s2 len ->
    0 <= q ->
    q + Z.of_nat n <= Zlength str ->
    NonHashChars (sublist (2 * q + 1) (2 * q + 1 + 2 * Z.of_nat n + 1) s2) =
    sublist q (q + Z.of_nat n) str.
Proof.
  induction n as [|n IH]; intros str s2 len q Halnum Htrans Hq Hrange.
  - change (Z.of_nat 0) with 0.
    replace (2 * q + 1 + 2 * 0 + 1) with (2 * q + 2) by lia.
    replace (2 * q + 2) with (2 * q + 1 + 1) by lia.
    rewrite (sublist_single 0 (2 * q + 1) s2) by (unfold ManacherTransformedString in Htrans; lia).
    rewrite (manacher_transformed_hash_at_odd_slot str s2 len q Htrans ltac:(unfold ManacherTransformedString in Htrans; lia)).
    unfold NonHashChars. simpl.
    destruct (Z.eqb_spec 35 35) as [_ | Hneq]; [|contradiction].
    rewrite Zsublist_nil by lia.
    reflexivity.
  - rewrite Nat2Z.inj_succ.
    set (m := Z.of_nat n).
    replace (2 * q + 1 + 2 * Z.succ m + 1) with (2 * q + 3 + 2 * m + 1) by lia.
    rewrite (sublist_split (2 * q + 1) (2 * q + 3 + 2 * m + 1) (2 * q + 3))
      by (unfold ManacherTransformedString in Htrans; lia).
    rewrite (sublist_split (2 * q + 1) (2 * q + 3) (2 * q + 2))
      by (unfold ManacherTransformedString in Htrans; lia).
    replace (2 * q + 2) with (2 * q + 1 + 1) by lia.
    replace (2 * q + 3) with (2 * q + 2 + 1) by lia.
    rewrite (sublist_single 0 (2 * q + 1) s2) by (unfold ManacherTransformedString in Htrans; lia).
    replace (2 * q + 1 + 1) with (2 * q + 2) by lia.
    rewrite (sublist_single 0 (2 * q + 2) s2) by (unfold ManacherTransformedString in Htrans; lia).
    rewrite (manacher_transformed_hash_at_odd_slot str s2 len q Htrans ltac:(unfold ManacherTransformedString in Htrans; lia)).
    replace (2 * q + 2) with (2 * (q + 1)) by lia.
    rewrite (manacher_transformed_even_value str s2 len (q + 1) Htrans ltac:(lia)).
    rewrite <- app_assoc.
    simpl.
    unfold NonHashChars at 1.
    assert (Hchar_ne : Znth q str 0 <> 35).
    {
      specialize (Halnum q ltac:(lia)).
      unfold AlnumCode in Halnum.
      lia.
    }
    replace (q + 1 - 1) with q by lia.
    destruct (Z.eqb_spec (Znth q str 0) 35) as [Heq | Hneq]; [contradiction|].
    simpl.
    change (filter (fun z : Z => negb (Z.eqb z 35))
      (sublist
        (match q + 1 with
         | 0 => 0
         | Z.pos y' => Z.pos y'~0
         | Z.neg y' => Z.neg y'~0
         end + 1)
        (match q + 1 with
         | 0 => 0
         | Z.pos y' => Z.pos y'~0
         | Z.neg y' => Z.neg y'~0
         end + 1 +
         match m with
         | 0 => 0
         | Z.pos y' => Z.pos y'~0
         | Z.neg y' => Z.neg y'~0
         end + 1) s2))
      with (NonHashChars
      (sublist
        (match q + 1 with
         | 0 => 0
         | Z.pos y' => Z.pos y'~0
         | Z.neg y' => Z.neg y'~0
         end + 1)
        (match q + 1 with
         | 0 => 0
         | Z.pos y' => Z.pos y'~0
         | Z.neg y' => Z.neg y'~0
         end + 1 +
         match m with
         | 0 => 0
         | Z.pos y' => Z.pos y'~0
         | Z.neg y' => Z.neg y'~0
         end + 1) s2)).
    change (match q + 1 with
      | 0 => 0
      | Z.pos y' => Z.pos y'~0
      | Z.neg y' => Z.neg y'~0
      end) with (2 * (q + 1)).
    replace (2 * (q + 1) + 1) with (2 * (q + 1) + 1) by lia.
    change (match m with
      | 0 => 0
      | Z.pos y' => Z.pos y'~0
      | Z.neg y' => Z.neg y'~0
      end) with (2 * m).
    unfold m.
    rewrite (IH str s2 len (q + 1) Halnum Htrans ltac:(lia) ltac:(lia)).
    rewrite (sublist_split q (q + Z.succ m) (q + 1)) by lia.
    rewrite (sublist_single 0 q str) by lia.
    replace (q + Z.succ m) with (q + 1 + m) by lia.
    reflexivity.
Qed.

(* Z-indexed wrapper around [manacher_window_nonhash_substring_nat]. *)
Lemma manacher_window_nonhash_substring:
  forall str s2 len q m,
    AlnumString str ->
    ManacherTransformedString str s2 len ->
    0 <= m ->
    0 <= q ->
    q + m <= Zlength str ->
    NonHashChars (sublist (2 * q + 1) (2 * q + 1 + 2 * m + 1) s2) =
    sublist q (q + m) str.
Proof.
  intros str s2 len q m Halnum Htrans Hm Hq Hrange.
  pose proof (manacher_window_nonhash_substring_nat (Z.to_nat m) str s2 len q Halnum Htrans Hq) as Hnat.
  rewrite Z2Nat.id in Hnat by lia.
  apply Hnat; lia.
Qed.

(* Converts a transformed-string center/radius palindrome back into an
   original-string palindrome segment. *)
Lemma center_radius_to_palindrome_segment:
  forall s s2 len lo plen,
    ManacherTransformedString s s2 len ->
    0 <= lo ->
    0 <= plen ->
    lo + plen <= Zlength s ->
    CenterRadiusPalindrome s2 len (2 * lo + plen + 1) (plen + 1) ->
    PalindromeSegment s lo plen.
Proof.
  intros s s2 len lo plen Htrans Hlo Hplen Hrange Hpal.
  unfold PalindromeSegment.
  repeat split; try lia.
  intros k Hk.
  unfold CenterRadiusPalindrome in Hpal.
  destruct Hpal as [_ [_ [_ [_ Hsym]]]].
  set (delta := plen - 1 - 2 * k).
  assert (Hleft_q : 1 <= lo + k + 1 <= Zlength s) by lia.
  assert (Hright_q : 1 <= lo + plen - k <= Zlength s) by lia.
  replace (lo + k) with (lo + k + 1 - 1) by lia.
  replace (lo + plen - 1 - k) with (lo + plen - k - 1) by lia.
  rewrite <- (manacher_transformed_even_value s s2 len (lo + k + 1) Htrans Hleft_q).
  rewrite <- (manacher_transformed_even_value s s2 len (lo + plen - k) Htrans Hright_q).
  destruct (Z_le_gt_dec 0 delta) as [Hdelta_nonneg | Hdelta_neg].
  - specialize (Hsym delta ltac:(unfold delta; lia)).
    replace (2 * lo + plen + 1 - delta) with (2 * (lo + k + 1)) in Hsym
      by (unfold delta; lia).
    replace (2 * lo + plen + 1 + delta) with (2 * (lo + plen - k)) in Hsym
      by (unfold delta; lia).
    exact Hsym.
  - specialize (Hsym (- delta) ltac:(unfold delta; lia)).
    replace (2 * lo + plen + 1 - - delta) with (2 * (lo + plen - k)) in Hsym
      by (unfold delta; lia).
    replace (2 * lo + plen + 1 + - delta) with (2 * (lo + k + 1)) in Hsym
      by (unfold delta; lia).
    symmetry; exact Hsym.
Qed.

(* Main semantic bridge for the final witness: the final loop state plus the
   completed output-copy prefix implies the user-facing longest-palindrome
   result. *)
Lemma manacher_longest_result_from_final_prefix:
  forall str s2 len p id limit maxId maxLen n_pre out,
    AlnumString str ->
    string_length str = n_pre ->
    1 <= n_pre ->
    len = 2 * n_pre + 2 ->
    ManacherLoopState str s2 len p len id limit maxId maxLen ->
    OutputCopyPrefix s2 out (maxId - maxLen) (maxId + maxLen + 1) maxLen ->
    LongestPalindromeResult str out maxLen.
Proof.
  intros str s2 len p id limit maxId maxLen n_pre out
    Halnum Hstrlen Hn Hlen Hstate Hpref.
  pose proof (manacher_final_selected_window_start_odd
    str s2 p len id limit maxId maxLen n_pre Hstrlen Hn Hlen Hstate)
    as [q Hstart].
  pose proof (manacher_final_selected_window_bounds
    str s2 p len id limit maxId maxLen n_pre Hstrlen Hn Hlen Hstate)
    as [HmaxLen_pos [Hstart_nonneg Hend_lt]].
  unfold ManacherLoopState in Hstate.
  destruct Hstate as [Htrans [Hrt [_ [_ Hbest]]]].
  unfold OutputCopyPrefix in Hpref.
  destruct Hpref as [_ [_ [_ [Hout Hj]]]].
  assert (Hq_nonneg : 0 <= q) by lia.
  assert (Hq_range : q + maxLen <= Zlength str).
  {
    unfold string_length in Hstrlen.
    rewrite Hstrlen.
    unfold string_length.
    lia.
  }
  assert (Hout_sub : out = sublist q (q + maxLen) str).
  {
    rewrite Hout.
    replace (maxId - maxLen) with (2 * q + 1) by lia.
    replace (maxId + maxLen + 1) with (2 * q + 1 + 2 * maxLen + 1) by lia.
    eapply (manacher_window_nonhash_substring str s2 len q maxLen); eauto; try lia.
  }
  unfold LongestPalindromeResult.
  split.
  {
    rewrite Hout_sub.
    rewrite Zlength_sublist by lia.
    lia.
  }
  exists q.
  split; [exact Hout_sub|].
  split.
  - unfold BestRadiusPrefix in Hbest.
    destruct Hbest as [_ [_ [_ [Hpal_or _]]]].
    destruct Hpal_or as [[Hzero _] | Hpal]; [lia |].
    replace maxId with (2 * q + maxLen + 1) in Hpal by lia.
    eapply center_radius_to_palindrome_segment; eauto; lia.
  - intros lo' len' Hseg.
    destruct (Z_le_gt_dec len' 0) as [Hlen'_nonpos | Hlen'_pos].
    { unfold PalindromeSegment in Hseg; lia. }
    unfold RadiusTablePrefix in Hrt.
    destruct Hrt as [_ [_ Hmaximal]].
    unfold BestRadiusPrefix in Hbest.
    destruct Hbest as [_ [_ [_ [_ [Hall _]]]]].
    set (center := 2 * lo' + len' + 1).
    assert (Hcenter_bounds : 1 <= center < len).
    {
      unfold PalindromeSegment in Hseg.
      unfold string_length in Hstrlen.
      lia.
    }
    pose proof (palindrome_segment_to_center_radius str s2 len lo' len' Htrans Hseg)
      as Hcenter_pal.
    pose proof (Hmaximal center Hcenter_bounds) as Hcenter_max.
    pose proof (center_radius_maximal_dominates
      s2 len center (Znth center p 0) (len' + 1) Hcenter_max Hcenter_pal)
      as Hdom.
    specialize (Hall center Hcenter_bounds).
    lia.
Qed.

(* Packages the final copy prefix and longest-result bridge into the
   [OutputCopyDone] predicate required by the generated return VC. *)
Lemma manacher_output_copy_done_from_final_prefix:
  forall str s2 len p id limit maxId maxLen n_pre out,
    AlnumString str ->
    string_length str = n_pre ->
    1 <= n_pre ->
    len = 2 * n_pre + 2 ->
    ManacherLoopState str s2 len p len id limit maxId maxLen ->
    OutputCopyPrefix s2 out (maxId - maxLen) (maxId + maxLen + 1) maxLen ->
    OutputCopyDone str s2 out len maxId maxLen maxLen.
Proof.
  intros str s2 len p id limit maxId maxLen n_pre out
    Halnum Hstrlen Hn Hlen Hstate Hpref.
  unfold OutputCopyDone.
  split.
  - unfold ManacherLoopState in Hstate.
    destruct Hstate as [Htrans _].
    exact Htrans.
  - split; [reflexivity|].
    split; [exact Hpref|].
    eapply manacher_longest_result_from_final_prefix; eauto.
Qed.
