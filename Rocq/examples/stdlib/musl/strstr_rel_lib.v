From Coq Require Import ZArith List Lia Classical_Prop Wf_nat.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

(* A string is represented by the bytes before its first NUL.  The
   enclosing memory contract owns the terminating byte separately. *)
Definition substring_at (hay needle : list Z) (i : Z) : Prop :=
  0 <= i /\ i + Zlength needle <= Zlength hay /\
  sublist i (i + Zlength needle) hay = needle.

Definition first_substring (hay needle : list Z) (i : Z) : Prop :=
  substring_at hay needle i /\
  (forall j, 0 <= j < i -> ~ substring_at hay needle j).

Definition no_match_before (hay needle : list Z) (i : Z) : Prop :=
  forall j, 0 <= j < i -> ~ substring_at hay needle j.

Definition strstr_result (hay needle : list Z) (base result : Z) : Prop :=
  (result = 0 /\ forall i, ~ substring_at hay needle i) \/
  (exists i, first_substring hay needle i /\ result = base + i).

(* A search for NUL scans only the available prefix, even when [count]
   exceeds the bytes left in the string object. *)
Definition memchr_zero_result (hay : list Z) (base start count result : Z)
    : Prop :=
  (Zlength hay - start < count /\ result = base + Zlength hay /\
   result <> 0) \/
  (count <= Zlength hay - start /\ result = 0).

(* Every byte before the terminator is nonzero.  This condition also fixes
   the first NUL position used by the external strchr/memchr contracts. *)
Definition nonzero_bytes (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s.

Definition first_byte_at (hay : list Z) (c i : Z) : Prop :=
  0 <= i < Zlength hay /\ Znth i hay 0 = c /\
  (forall j, 0 <= j < i -> Znth j hay 0 <> c).

Definition strchr_result (hay : list Z) (c base result : Z) : Prop :=
  (result = 0 /\ forall i, ~ first_byte_at hay (Z.land c 255) i) \/
  (exists i, first_byte_at hay (Z.land c 255) i /\
             result = base + i /\ result <> 0).

(* The short helpers compare packed windows.  The words below are only
   loop observations; strstr_result remains the implementation-independent
   first-occurrence specification. *)
Definition rolling2 (hay : list Z) (i word : Z) : Prop :=
  1 <= i <= Zlength hay /\
  word = Z.land (256 * Znth (i - 1) (hay ++ [0]) 0 +
                 Znth i (hay ++ [0]) 0) 65535.

Definition needle2 (needle : list Z) (word : Z) : Prop :=
  Zlength needle = 2 /\
  word = 256 * Znth 0 needle 0 + Znth 1 needle 0.

Definition rolling3 (hay : list Z) (i word : Z) : Prop :=
  2 <= i <= Zlength hay /\
  word = Z.land (16777216 * Znth (i - 2) (hay ++ [0]) 0 +
                 65536 * Znth (i - 1) (hay ++ [0]) 0 +
                   256 * Znth i (hay ++ [0]) 0) 4294967295.

Definition needle3 (needle : list Z) (word : Z) : Prop :=
  Zlength needle = 3 /\
  word = 16777216 * Znth 0 needle 0 +
          65536 * Znth 1 needle 0 +
            256 * Znth 2 needle 0.

Definition rolling4 (hay : list Z) (i word : Z) : Prop :=
  3 <= i <= Zlength hay /\
  word = Z.land (16777216 * Znth (i - 3) (hay ++ [0]) 0 +
                 65536 * Znth (i - 2) (hay ++ [0]) 0 +
                   256 * Znth (i - 1) (hay ++ [0]) 0 +
                         Znth i (hay ++ [0]) 0) 4294967295.

Definition needle4 (needle : list Z) (word : Z) : Prop :=
  Zlength needle = 4 /\
  word = 16777216 * Znth 0 needle 0 +
          65536 * Znth 1 needle 0 +
            256 * Znth 2 needle 0 +
                  Znth 3 needle 0.

Definition memcmp_zero (bytes : list Z) (i j count ret : Z) : Prop :=
  0 <= count /\
  (ret = 0 <-> sublist i (i + count) bytes =
                sublist j (j + count) bytes).

Lemma memcmp_nonzero_count_positive :
  forall bytes i j count ret,
    memcmp_zero bytes i j count ret ->
    ret <> 0 ->
    0 < count.
Proof.
  intros bytes i j count ret [Hcount Heq] Hret.
  destruct (Z.eq_dec count 0) as [Hzero | Hnonzero]; [|lia].
  subst count.
  assert (ret = 0).
  { apply Heq. repeat rewrite Zsublist_nil by lia. reflexivity. }
  contradiction.
Qed.

(* The bitset contains exactly the byte values inspected in the prefix.
   This is a mathematical property of the table, independent of how the
   C loop performs its read/modify/write. *)
Definition byteset_prefix (needle : list Z) (upto : Z)
    (bits : list Z) : Prop :=
  forall c, 0 <= c < 256 ->
    (Z.testbit (Znth (c / 64) bits 0) (c mod 64) = true <->
     exists j, 0 <= j < upto /\ Znth j needle 0 = c).

(* An initialized shift entry is one past the last occurrence among the
   inspected needle bytes.  No value is claimed for untouched entries. *)
Definition shift_prefix (needle : list Z) (upto : Z)
    (entries : list Z) : Prop :=
  forall c j, 0 <= c < 256 ->
    0 <= j < upto ->
    Znth j needle 0 = c ->
    (forall k, j < k < upto -> Znth k needle 0 <> c) ->
    Znth c entries 0 = j + 1.

(* Equality of the currently inspected comparison interval.  The guard
   identifies actual needle indices; the predicate says nothing about
   out-of-range reads or memory ownership. *)
Definition matched_range (hay needle : list Z) (pos lo hi : Z) : Prop :=
  forall j, lo <= j < hi -> Znth (pos + j) hay 0 = Znth j needle 0.

(* The right-half loop starts after both the factorization boundary and
   any remembered periodic prefix. *)
Definition right_half_matched (hay needle : list Z)
    (pos split memory next : Z) : Prop :=
  Z.max split memory <= next /\
  matched_range hay needle pos (Z.max split memory) next.

(* Maximal-suffix scan facts shared by the two comparison directions.
   [start] is the mathematical value of unsigned [ip + 1]. *)
Definition maxsuf_partial_match (needle : list Z)
    (start jp k : Z) : Prop :=
  sublist start (start + k - 1) needle =
  sublist (jp + 1) (jp + k) needle.

Definition maxsuf_periodicity (needle : list Z)
    (start jp k p : Z) : Prop :=
  forall t, start <= t -> t + p < jp + k ->
    Znth t needle 0 = Znth (t + p) needle 0.

Definition maxsuf_suffix_period (needle : list Z)
    (start period : Z) : Prop :=
  forall t, start <= t -> t + period < Zlength needle ->
    Znth t needle 0 = Znth (t + period) needle 0.

Lemma maxsuf_exit_suffix_period :
  forall needle start jp k period,
    Zlength needle <= jp + k ->
    maxsuf_periodicity needle start jp k period ->
    maxsuf_suffix_period needle start period.
Proof.
  intros needle start jp k period Hend Hscan t Hstart Hbound.
  apply Hscan; lia.
Qed.

(* Every earlier suffix has already lost a lexicographic comparison to
   the current candidate.  Direction 1 is the ordinary byte ordering;
   direction 0 reverses it.  The witness is the first differing byte. *)
Definition maxsuf_optimal (needle : list Z)
    (start direction : Z) : Prop :=
  forall earlier, 0 <= earlier < start ->
    exists d, 0 <= d /\
      start + d < Zlength needle /\
      earlier + d < Zlength needle /\
      (forall t, 0 <= t < d ->
        Znth (start + t) needle 0 = Znth (earlier + t) needle 0) /\
      (direction = 1 ->
        Znth (start + d) needle 0 > Znth (earlier + d) needle 0) /\
      (direction = 0 ->
        Znth (start + d) needle 0 < Znth (earlier + d) needle 0).

(* Migrated from the old maxsuf_optimality2 invariant.  Candidate [start]
   wins a strict lexicographic comparison against every intermediate
   suffix inside its current period window.  The explicit first-difference
   witness is the Z-indexed form of old list_lex_gt_ex on the two sublists. *)
Definition maxsuf_intermediate_optimal (needle : list Z)
    (start period direction : Z) : Prop :=
  forall intermediate, start < intermediate < start + period ->
    exists d, 0 <= d /\
      intermediate + d < start + period /\
      intermediate + d < Zlength needle /\
      (forall t, 0 <= t < d ->
        Znth (start + t) needle 0 =
        Znth (intermediate + t) needle 0) /\
      (direction = 1 ->
        Znth (start + d) needle 0 >
        Znth (intermediate + d) needle 0) /\
      (direction = 0 ->
        Znth (start + d) needle 0 <
        Znth (intermediate + d) needle 0).

Definition selected_maxsuf (needle : list Z) (split shift : Z) : Prop :=
  (maxsuf_optimal needle split 0 /\
   maxsuf_intermediate_optimal needle split shift 0) \/
  (maxsuf_optimal needle split 1 /\
   maxsuf_intermediate_optimal needle split shift 1).

Definition selected_maxsuf_cuts (selected first second : Z) : Prop :=
  selected = Z.max first second.

(* The C cut index is a size_t. Its all-ones value denotes the cut before
   byte zero; otherwise the index lies inside the needle. *)
Definition maxsuf_cut_index64 (index length : Z) : Prop :=
  0 <= index /\
  (index = 18446744073709551615 \/ index < length).

(* Critical factorization is stated through the mathematical least period
   of the needle.  The search loop uses the selected shift to skip only
   positions that cannot contain an occurrence. *)
Definition string_period (needle : list Z) (period : Z) : Prop :=
  0 < period /\
  forall j, 0 <= j -> j + period < Zlength needle ->
    Znth j needle 0 = Znth (j + period) needle 0.

Definition least_string_period (needle : list Z) (period : Z) : Prop :=
  string_period needle period /\
  forall q, string_period needle q -> period <= q.

Definition local_period (needle : list Z) (split period : Z) : Prop :=
  0 <= split <= Zlength needle /\ 0 < period /\
  forall j, 0 <= j < period ->
    0 <= split + j - period < split ->
    split + j < Zlength needle ->
    Znth (split + j - period) needle 0 =
    Znth (split + j) needle 0.

Definition critical_split (needle : list Z) (split shift : Z) : Prop :=
  exists period,
    least_string_period needle period /\
    0 <= split < period /\
    0 < shift <= period /\
    local_period needle split period.

(* The selected cut has no shorter local period.  The search loop needs this
   fact when the left comparison fails and advances by the selected shift. *)
Definition critical_min_local (needle : list Z) (split : Z) : Prop :=
  exists period,
    least_string_period needle period /\
    local_period needle split period /\
    forall q, local_period needle split q -> period <= q.

Definition critical_search_split (needle : list Z) (split shift : Z) : Prop :=
  critical_split needle split shift /\ critical_min_local needle split.

Lemma left_mismatch_period_skip :
  forall hay needle pos split shift memory k,
    no_match_before hay needle pos ->
    0 <= memory < k ->
    k <= split ->
    k <= Zlength needle ->
    matched_range hay needle pos k (Zlength needle) ->
    Znth (k - 1) needle 0 <> Znth (pos + k - 1) hay 0 ->
    critical_search_split needle split shift ->
    no_match_before hay needle (pos + shift).
Proof.
  intros hay needle pos split shift memory k Hbefore Hmem Hksplit Hklen
    Hmatched Hmismatch [Hcritical Hminimal].
  unfold no_match_before in *.
  intros j Hj.
  destruct (Z_lt_ge_dec j pos) as [Hold | Hnew].
  - apply Hbefore. lia.
  - intro Hocc.
    destruct Hocc as [Hj0 [Hwindow Hsub]].
    set (q := j - pos).
    assert (Hq : 0 <= q < shift) by (unfold q; lia).
    destruct (Z.eq_dec q 0) as [Hq0 | Hq0].
    + assert (Hjpos : j = pos) by (unfold q in Hq0; lia).
      subst j.
      pose proof (f_equal (fun xs => Znth (k - 1) xs 0) Hsub) as Hnth.
      cbn beta in Hnth.
      rewrite Znth_sublist in Hnth by lia.
      replace (k - 1 + pos) with (pos + k - 1) in Hnth by lia.
      apply Hmismatch. symmetry. exact Hnth.
    + destruct Hcritical as [period [Hleast [Hsplit [Hshift Hlocal]]]].
      destruct Hminimal as [period' [Hleast' [Hlocal' Hmin]]].
      destruct Hleast as [Hperiod Hleast].
      destruct Hleast' as [Hperiod' Hleast'].
      assert (Heq : period = period') by
        (specialize (Hleast period' Hperiod');
         specialize (Hleast' period Hperiod); lia).
      subst period'.
      assert (Hq_local : local_period needle split q).
      { unfold local_period.
        unfold local_period in Hlocal.
        destruct Hlocal as [Hsplit_len [Hperiod_pos Hperiod_local]].
        split; [exact Hsplit_len |].
        split; [lia |].
        intros i Hi Hleft Hright.
        assert (Hcur :
          Znth (pos + (split + i)) hay 0 = Znth (split + i) needle 0).
        { apply Hmatched. lia. }
        pose proof
          (f_equal (fun xs => Znth (split + i - q) xs 0) Hsub) as Hnth.
        cbn beta in Hnth.
        rewrite Znth_sublist in Hnth by lia.
        replace (split + i - q + j) with (pos + (split + i)) in Hnth
          by (unfold q; lia).
        rewrite Hcur in Hnth.
        symmetry. exact Hnth. }
      specialize (Hmin q Hq_local).
      lia.
Qed.

Lemma absent_last_byte_skip :
  forall hay needle pos length c,
    length = Zlength needle ->
    0 < length ->
    c = Znth (pos + length - 1) hay 0 ->
    (forall j, 0 <= j < length -> Znth j needle 0 <> c) ->
    no_match_before hay needle pos ->
    no_match_before hay needle (pos + length).
Proof.
  intros hay needle pos length c Hlength Hpositive Hc Habs Hbefore.
  unfold no_match_before in *.
  intros j Hj.
  destruct (Z_lt_ge_dec j pos) as [Hold | Hnew].
  - apply Hbefore. lia.
  - intro Hocc.
    destruct Hocc as [Hj0 [Hwindow Hsub]].
    set (q := j - pos).
    assert (Hq : 0 <= q < length) by (unfold q; lia).
    set (idx := length - 1 - q).
    assert (Hidx : 0 <= idx < length) by (unfold idx; lia).
    pose proof (f_equal (fun xs => Znth idx xs 0) Hsub) as Hnth.
    cbn beta in Hnth.
    rewrite Znth_sublist in Hnth by lia.
    apply (Habs idx Hidx).
    rewrite Hc.
    replace (idx + j) with (pos + length - 1) in Hnth
      by (unfold idx, q; lia).
    symmetry. exact Hnth.
Qed.

(* A global period would make the candidate at [start - period]
   indistinguishable from [start] through the whole latter suffix. *)
Lemma maxsuf_optimal_cut_lt_period :
  forall needle start direction period,
    (direction = 0 \/ direction = 1) ->
    maxsuf_optimal needle start direction ->
    string_period needle period ->
    start < period.
Proof.
  intros needle start direction period Hdir Hopt [Hperiod Hrepeat].
  destruct (Z_lt_ge_dec start period) as [Hlt | Hge]; [exact Hlt|].
  unfold maxsuf_optimal in Hopt.
  specialize (Hopt (start - period) ltac:(lia)).
  destruct Hopt as [d [Hd [Hend [_ [Heq [Hgt Hrev]]]]]].
  specialize (Hrepeat (start - period + d) ltac:(lia) ltac:(lia)).
  replace (start - period + d + period) with (start + d) in Hrepeat by lia.
  destruct Hdir as [Hdir | Hdir]; subst direction;
    [specialize (Hrev eq_refl) | specialize (Hgt eq_refl)]; lia.
Qed.

(* If the scan period exceeded a global period, the intermediate suffix
   one global period later could not have a first differing byte. *)
Lemma maxsuf_intermediate_period_le_global :
  forall needle start scan_period direction period,
    0 <= start ->
    (direction = 0 \/ direction = 1) ->
    maxsuf_intermediate_optimal needle start scan_period direction ->
    string_period needle period ->
    scan_period <= period.
Proof.
  intros needle start scan_period direction period Hstart Hdir Hopt
    [Hperiod Hrepeat].
  destruct (Z_le_gt_dec scan_period period) as [Hle | Hgt]; [exact Hle|].
  unfold maxsuf_intermediate_optimal in Hopt.
  specialize (Hopt (start + period) ltac:(lia)).
  destruct Hopt as [d [Hd [_ [Hend [_ [Hfwd Hrev]]]]]].
  specialize (Hrepeat (start + d) ltac:(lia) ltac:(lia)).
  replace (start + d + period) with (start + period + d) in Hrepeat by lia.
  destruct Hdir as [Hdir | Hdir]; subst direction;
    [specialize (Hrev eq_refl) | specialize (Hfwd eq_refl)]; lia.
Qed.

Lemma nat_property_has_least (P : nat -> Prop) :
  (exists n, P n) ->
  exists m, P m /\ forall n, P n -> (m <= n)%nat.
Proof.
  intros [n0 Hn0].
  revert Hn0.
  pattern n0.
  apply lt_wf_ind.
  intros n IH Hn.
  destruct (classic (exists m, (m < n)%nat /\ P m)) as [Hex | Hnone].
  - destruct Hex as [m [Hm HmP]].
    destruct (IH m Hm HmP) as [least [Hleast Hbound]].
    exists least. split; [exact Hleast | exact Hbound].
  - exists n. split; [exact Hn |].
    intros m Hm.
    assert (~ (m < n)%nat).
    { intro Hlt. apply Hnone. exists m. split; assumption. }
    lia.
Qed.

Lemma least_string_period_exists :
  forall needle, 0 < Zlength needle ->
    exists period, least_string_period needle period.
Proof.
  intros needle Hlength.
  set (P := fun n : nat =>
    (0 < n)%nat /\ string_period needle (Z.of_nat n)).
  assert (Hex : exists n, P n).
  { exists (Z.to_nat (Zlength needle)).
    unfold P. split.
    - apply (Z2Nat.inj_lt 0 (Zlength needle)); lia.
    - rewrite Z2Nat.id by lia.
      split; [lia |]. intros j Hj Hbound. lia. }
  destruct (nat_property_has_least P Hex) as [n [Hn Hleast]].
  exists (Z.of_nat n).
  unfold least_string_period.
  split; [exact (proj2 Hn) |].
  intros q Hq.
  destruct Hq as [Hqpos Hqbody].
  specialize (Hleast (Z.to_nat q)).
  assert (P (Z.to_nat q)) as HP.
  { unfold P. split.
    - apply (Z2Nat.inj_lt 0 q); lia.
    - rewrite Z2Nat.id by lia. split; assumption. }
  specialize (Hleast HP).
  apply Nat2Z.inj_le in Hleast.
  rewrite Z2Nat.id in Hleast by lia.
  exact Hleast.
Qed.

Lemma maxsuf_direction_critical_split :
  forall needle split shift direction,
    0 < Zlength needle ->
    0 <= split <= Zlength needle ->
    0 < shift ->
    (direction = 0 \/ direction = 1) ->
    maxsuf_optimal needle split direction ->
    maxsuf_intermediate_optimal needle split shift direction ->
    critical_split needle split shift.
Proof.
  intros needle split shift direction Hlength Hsplit Hshift Hdir Hopt Hmid.
  destruct (least_string_period_exists needle Hlength) as [period Hleast].
  destruct Hleast as [Hperiod Hminimal].
  exists period.
  split; [split; assumption |].
  split.
  - split; [lia |].
    eapply maxsuf_optimal_cut_lt_period; eauto.
  - split.
    + split; [exact Hshift |].
      eapply maxsuf_intermediate_period_le_global; eauto; lia.
    + unfold local_period.
      split; [exact Hsplit |].
      split; [exact (proj1 Hperiod) |].
      intros j Hj Hleft Hright.
      destruct Hperiod as [_ Hrepeat].
      specialize (Hrepeat (split + j - period) ltac:(lia) ltac:(lia)).
      replace (split + j - period + period) with (split + j) in Hrepeat by lia.
      exact Hrepeat.
Qed.

Lemma selected_maxsuf_critical_split :
  forall needle split shift,
    0 < Zlength needle ->
    0 <= split <= Zlength needle ->
    0 < shift ->
    selected_maxsuf needle split shift ->
    critical_split needle split shift.
Proof.
  intros needle split shift Hlength Hsplit Hshift Hselected.
  unfold selected_maxsuf in Hselected.
  destruct Hselected as [[Hopt Hmid] | [Hopt Hmid]].
  - eapply (maxsuf_direction_critical_split needle split shift 0);
      eauto; left; reflexivity.
  - eapply (maxsuf_direction_critical_split needle split shift 1);
      eauto; right; reflexivity.
Qed.

Lemma selected_maxsuf_cut_shift :
  forall needle split scan_shift,
    0 < Zlength needle ->
    0 < split <= Zlength needle ->
    0 < scan_shift ->
    selected_maxsuf needle split scan_shift ->
    critical_split needle split split.
Proof.
  intros needle split scan_shift Hlength Hsplit Hscan Hselected.
  pose proof (selected_maxsuf_critical_split needle split scan_shift
    Hlength ltac:(lia) Hscan Hselected) as Hcritical.
  destruct Hcritical as [period [Hleast [Hcut [Hshift Hlocal]]]].
  exists period.
  split; [exact Hleast |].
  split; [exact Hcut |].
  split; [lia | exact Hlocal].
Qed.

(* The loop either carries no remembered prefix or carries precisely the
   periodic prefix available after advancing by [shift].  Packaging these
   three equivalent conjuncts avoids repeated case splitting during QCP
   state propagation; it does not weaken any conjunct. *)
Definition periodic_memory_state (needle : list Z)
    (shift memory remembered : Z) : Prop :=
  (memory = 0 \/ memory = remembered) /\
  (remembered = 0 \/ remembered = Zlength needle - shift) /\
  (remembered <> 0 -> string_period needle shift).

Lemma periodic_memory_after_shift :
  forall hay needle pos split shift memory remembered k,
    periodic_memory_state needle shift memory remembered ->
    critical_search_split needle split shift ->
    k <= split ->
    matched_range hay needle pos k (Zlength needle) ->
    matched_range hay needle (pos + shift) 0 remembered.
Proof.
  intros hay needle pos split shift memory remembered k Hstate
    [Hcritical Hminimal] Hksplit Hmatched.
  destruct Hstate as [Hmemory [Hremembered Hremembered_period]].
  destruct Hremembered as [-> | Hremembered].
  - unfold matched_range. intros. lia.
  - subst remembered.
    destruct (Z.eq_dec (Zlength needle - shift) 0) as [Hzero | Hnonzero].
    { unfold matched_range. intros. lia. }
    assert (Hshift_period : string_period needle shift).
    { apply Hremembered_period. exact Hnonzero. }
    destruct Hcritical as [period [Hleast [Hsplit [Hshift Hlocal]]]].
    destruct Hleast as [Hperiod Hleast].
    specialize (Hleast shift Hshift_period).
    assert (Heq : shift = period) by lia.
    subst period.
    unfold matched_range in *.
    intros q Hq.
    assert (Hcur := Hmatched (shift + q) ltac:(lia)).
    destruct Hshift_period as [Hshift_pos Hrepeat].
    specialize (Hrepeat q ltac:(lia) ltac:(lia)).
    replace (q + shift) with (shift + q) in Hrepeat by lia.
    replace (pos + shift + q) with (pos + (shift + q)) by lia.
    rewrite Hcur.
    symmetry. exact Hrepeat.
Qed.


Lemma pack2_bytes__proof_of_twobyte_1 : forall a b,
  0 <= a < 256 -> 0 <= b < 256 ->
  Z.lor (256 * a) b = 256 * a + b.
Proof.
  intros a b Ha Hb.
  destruct (Z.eq_dec b 0) as [-> | Hb0].
  { rewrite Z.lor_0_r. lia. }
  pose proof (Z.add_lor_land (256 * a) b) as Hsum.
  assert (Z.log2 b < 8) as Hlog by (apply Z.log2_lt_pow2; lia).
  assert (Z.land (256 * a) b = 0) as Hzero.
  { apply Z.bits_inj'. intros k Hk.
    rewrite Z.land_spec, Z.testbit_0_l.
    destruct (Z_lt_ge_dec k 8) as [Hlow | Hhigh].
    - replace (256 * a) with (Z.shiftl a 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite (Z.bits_above_log2 b k); [now rewrite Bool.andb_false_r | lia | lia]. }
  lia.
Qed.


Lemma first_two_bytes__proof_of_twobyte_1 : forall l,
  nonzero_bytes l -> 2 <= Zlength l ->
  0 <= Znth 0 (l ++ [0]) 0 < 256 /\
  0 <= Znth 1 (l ++ [0]) 0 < 256 /\
  Znth 0 (l ++ [0]) 0 = Znth 0 l 0 /\
  Znth 1 (l ++ [0]) 0 = Znth 1 l 0.
Proof.
  intros l Hbytes Hlen.
  unfold nonzero_bytes in Hbytes.
  rewrite Zlength_correct in Hlen.
  destruct l as [|a [|b tl]]; simpl in *; try lia.
  inversion Hbytes as [|x xs Ha Htail].
  inversion Htail as [|y ys Hb Hrest].
  unfold Znth; simpl; lia.
Qed.

From Coq Require Import Lia.

Lemma nonzero_byte_range__proof_of_threebyte_2 :
  forall s j, nonzero_bytes s -> 0 <= j < Zlength s ->
    0 < Znth j s 0 < 256.
Proof.
  intros s j Hs Hj.
  unfold nonzero_bytes in Hs.
  apply Forall_forall with (x := Znth j s 0) in Hs.
  - exact Hs.
  - unfold Znth. apply nth_In.
    rewrite Zlength_correct in Hj. lia.
Qed.

Lemma Znth_app_nul_prefix__proof_of_threebyte_2 :
  forall s j, 0 <= j < Zlength s ->
    Znth j (s ++ [0]) 0 = Znth j s 0.
Proof.
  intros s j Hj. unfold Znth.
  apply app_nth1. rewrite Zlength_correct in Hj. lia.
Qed.

Lemma maxsuf_prefix_and_suffix_period :
  forall needle split period,
    0 <= split <= Zlength needle ->
    0 < period ->
    period + split <= Zlength needle + 1 ->
    sublist 0 split (needle ++ [0]) =
      sublist period (period + split) (needle ++ [0]) ->
    maxsuf_suffix_period needle split period ->
    string_period needle period.
Proof.
  intros needle split period Hsplit Hperiod Hrange Hprefix Hsuffix.
  split; [exact Hperiod |].
  intros j Hj Hbound.
  destruct (Z_lt_ge_dec j split) as [Hprefix_j | Hsuffix_j].
  - pose proof (f_equal (fun xs => Znth j xs 0) Hprefix) as Hnth.
    cbv beta in Hnth.
    repeat rewrite Znth_sublist in Hnth by lia.
    replace (j + 0) with j in Hnth by lia.
    rewrite !Znth_app_nul_prefix__proof_of_threebyte_2 in Hnth by lia.
    exact Hnth.
  - apply Hsuffix; lia.
Qed.

Lemma packed3_inj__proof_of_threebyte_2 :
  forall a b c a' b' c',
    0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 ->
    0 <= a' < 256 -> 0 <= b' < 256 -> 0 <= c' < 256 ->
    16777216 * a + 65536 * b + 256 * c =
    16777216 * a' + 65536 * b' + 256 * c' ->
    a = a' /\ b = b' /\ c = c'.
Proof.
  intros. lia.
Qed.

Lemma byte_or_nul_range__proof_of_threebyte_2 :
  forall s j, nonzero_bytes s -> 0 <= j <= Zlength s ->
    0 <= Znth j (s ++ [0]) 0 < 256.
Proof.
  intros s j Hs Hj.
  destruct (Z.eq_dec j (Zlength s)) as [Heq | Hne].
  - subst j. unfold Znth.
    rewrite app_nth2 by (rewrite Zlength_correct; lia).
    rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length s)) - length s)%nat with 0%nat by lia.
    simpl. lia.
  - rewrite Znth_app_nul_prefix__proof_of_threebyte_2 by lia.
    pose proof (nonzero_byte_range__proof_of_threebyte_2 s j Hs ltac:(lia)).
    lia.
Qed.

Lemma rolling3_unmask__proof_of_threebyte_2 :
  forall s i w, nonzero_bytes s -> rolling3 s i w ->
    w = 16777216 * Znth (i - 2) (s ++ [0]) 0 +
        65536 * Znth (i - 1) (s ++ [0]) 0 +
          256 * Znth i (s ++ [0]) 0.
Proof.
  intros s i w Hs [Hi Hw]. subst w.
  pose proof (byte_or_nul_range__proof_of_threebyte_2 s (i - 2) Hs ltac:(lia)) as Ha.
  pose proof (byte_or_nul_range__proof_of_threebyte_2 s (i - 1) Hs ltac:(lia)) as Hb.
  pose proof (byte_or_nul_range__proof_of_threebyte_2 s i Hs ltac:(lia)) as Hc.
  replace 4294967295 with (Z.ones 32) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small; lia.
Qed.

Lemma packed3_step__proof_of_threebyte_2 :
  forall a b c d,
    0 <= a < 256 -> 0 <= b < 256 ->
    0 <= c < 256 -> 0 <= d < 256 ->
    (
      (Z.shiftl
        (Z.lor (16777216 * a + 65536 * b + 256 * c)
          (d mod 4294967296)) 8) mod 4294967296) =
    16777216 * b + 65536 * c + 256 * d.
Proof.
  intros a b c d Ha Hb Hc Hd.
  rewrite (Z.mod_small d 4294967296) by lia.
  set (w := 16777216 * a + 65536 * b + 256 * c).
  assert (Hlow : Z.land w d = 0).
  {
    replace d with (Z.land d (Z.ones 8)).
    2: { rewrite Z.land_ones by lia.
         change (2 ^ 8) with 256. apply Z.mod_small. lia. }
    rewrite (Z.land_comm d (Z.ones 8)).
    rewrite Z.land_assoc.
    replace (Z.land w (Z.ones 8)) with 0.
    - apply Z.land_0_l.
    - rewrite Z.land_ones by lia.
      change (2 ^ 8) with 256.
      subst w.
      replace (16777216 * a + 65536 * b + 256 * c)
        with (256 * (65536 * a + 256 * b + c)) by ring.
      rewrite Z.mul_comm.
      symmetry. apply Z.mod_mul; lia.
  }
  pose proof (Z.add_lor_land w d) as Hlor.
  rewrite Hlow, Z.add_0_r in Hlor.
  replace (Z.lor w d) with (w + d) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 8) with 256.
  subst w.
  replace ((16777216 * a + 65536 * b + 256 * c + d) * 256)
    with (16777216 * b + 65536 * c + 256 * d + a * 4294967296)
    by ring.
  rewrite Z.mod_add by lia.
  rewrite Z.mod_small; lia.
Qed.

Lemma packed3_implies_match__proof_of_threebyte_2 :
  forall hs ns i hw nw,
    nonzero_bytes hs -> nonzero_bytes ns ->
    2 <= i < Zlength hs ->
    rolling3 hs i hw -> needle3 ns nw -> hw = nw ->
    substring_at hs ns (i - 2).
Proof.
  intros hs ns i hw nw Hhs Hns Hi Hr Hn Heq.
  pose proof (rolling3_unmask__proof_of_threebyte_2 hs i hw Hhs Hr) as Hw.
  unfold needle3 in Hn.
  destruct Hn as [Hlen Hnw].
  assert (Ha := nonzero_byte_range__proof_of_threebyte_2 hs (i - 2) Hhs ltac:(lia)).
  assert (Hb := nonzero_byte_range__proof_of_threebyte_2 hs (i - 1) Hhs ltac:(lia)).
  assert (Hc := nonzero_byte_range__proof_of_threebyte_2 hs i Hhs ltac:(lia)).
  assert (Ha' := nonzero_byte_range__proof_of_threebyte_2 ns 0 Hns ltac:(lia)).
  assert (Hb' := nonzero_byte_range__proof_of_threebyte_2 ns 1 Hns ltac:(lia)).
  assert (Hc' := nonzero_byte_range__proof_of_threebyte_2 ns 2 Hns ltac:(lia)).
  rewrite Znth_app_nul_prefix__proof_of_threebyte_2 in Hw by lia.
  rewrite Znth_app_nul_prefix__proof_of_threebyte_2 in Hw by lia.
  rewrite Znth_app_nul_prefix__proof_of_threebyte_2 in Hw by lia.
  pose proof (packed3_inj__proof_of_threebyte_2
    (Znth (i - 2) hs 0) (Znth (i - 1) hs 0) (Znth i hs 0)
    (Znth 0 ns 0) (Znth 1 ns 0) (Znth 2 ns 0)
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [E0 [E1 E2]].
  unfold substring_at.
  split; [lia |].
  split; [lia |].
  rewrite Hlen.
  replace (i - 2 + 3) with (i + 1) by lia.
  apply (proj2 (list_eq_ext (sublist (i - 2) (i + 1) hs) ns 0)).
  split.
  - rewrite Zlength_sublist by lia. lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist by lia.
    destruct (Z.eq_dec k 0) as [-> | Hk0].
    + replace (0 + (i - 2)) with (i - 2) by lia. exact E0.
    + destruct (Z.eq_dec k 1) as [-> | Hk1].
      * replace (1 + (i - 2)) with (i - 1) by lia. exact E1.
      * assert (k = 2) by lia. subst k.
        replace (2 + (i - 2)) with i by lia. exact E2.
Qed.

Lemma terminator_index__proof_of_threebyte_2 :
  forall s, Znth (Zlength s) (s ++ [0]) 0 = 0.
Proof.
  intro s. unfold Znth.
  rewrite app_nth2 by (rewrite Zlength_correct; lia).
  rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length s)) - length s)%nat with 0%nat by lia.
  reflexivity.
Qed.

Lemma match_implies_packed3__proof_of_threebyte_2 :
  forall hs ns i hw nw,
    nonzero_bytes hs ->
    rolling3 hs i hw -> needle3 ns nw ->
    substring_at hs ns (i - 2) -> hw = nw.
Proof.
  intros hs ns i hw nw Hhs Hr Hn Hmatch.
  pose proof (rolling3_unmask__proof_of_threebyte_2 hs i hw Hhs Hr) as Hw.
  unfold needle3 in Hn. destruct Hn as [Hlen Hnw].
  unfold substring_at in Hmatch.
  destruct Hmatch as [Hlo [Hhi Hsub]].
  rewrite Hlen in Hsub.
  replace (i - 2 + 3) with (i + 1) in Hsub by lia.
  assert (Hi : i < Zlength hs) by lia.
  assert (E0 : Znth (i - 2) hs 0 = Znth 0 ns 0).
  { rewrite <- Hsub. rewrite Znth_sublist by lia.
    replace (0 + (i - 2)) with (i - 2) by lia. reflexivity. }
  assert (E1 : Znth (i - 1) hs 0 = Znth 1 ns 0).
  { rewrite <- Hsub. rewrite Znth_sublist by lia.
    replace (1 + (i - 2)) with (i - 1) by lia. reflexivity. }
  assert (E2 : Znth i hs 0 = Znth 2 ns 0).
  { rewrite <- Hsub. rewrite Znth_sublist by lia.
    replace (2 + (i - 2)) with i by lia. reflexivity. }
  rewrite Znth_app_nul_prefix__proof_of_threebyte_2 in Hw by lia.
  rewrite Znth_app_nul_prefix__proof_of_threebyte_2 in Hw by lia.
  rewrite Znth_app_nul_prefix__proof_of_threebyte_2 in Hw by lia.
  lia.
Qed.

(* Disjoint byte fields: a high word shifted by k cannot share a low bit. *)
Lemma lor_high_low__proof_of_threebyte_2 : forall hi lo k,
  0 <= k -> 0 <= lo < 2 ^ k ->
  Z.lor (Z.shiftl hi k) lo = Z.shiftl hi k + lo.
Proof.
  intros hi lo k Hk Hlo.
  assert (Hlo_bits : Z.land lo (Z.ones k) = lo).
  { rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  assert (Hhigh_bits : Z.land (Z.shiftl hi k) (Z.ones k) = 0).
  { rewrite Z.land_ones by lia.
    rewrite Z.shiftl_mul_pow2 by lia.
    apply Z.mod_mul.
    pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). lia. }
  assert (Hdisjoint : Z.land (Z.shiftl hi k) lo = 0).
  { rewrite <- Hlo_bits.
    rewrite (Z.land_comm lo (Z.ones k)).
    rewrite Z.land_assoc.
    rewrite Hhigh_bits.
    apply Z.land_0_l. }
  pose proof (Z.add_lor_land (Z.shiftl hi k) lo) as Hsum.
  lia.
Qed.

Lemma packed3__proof_of_threebyte_2 : forall a b c,
  0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 ->
  Z.lor
    (Z.lor ((Z.shiftl a 24) mod 2 ^ 32)
           ((Z.shiftl b 16) mod 2 ^ 32))
    ((Z.shiftl c 8) mod 2 ^ 32) =
    16777216 * a + 65536 * b + 256 * c.
Proof.
  intros a b c Ha Hb Hc.
  repeat rewrite Z.mod_small by
    (rewrite Z.shiftl_mul_pow2 by lia; cbv [Z.pow]; lia).
  rewrite (lor_high_low__proof_of_threebyte_2 a (Z.shiftl b 16) 24)
    by (try lia; rewrite Z.shiftl_mul_pow2 by lia; cbv [Z.pow]; lia).
  replace (Z.shiftl a 24 + Z.shiftl b 16)
    with (Z.shiftl (256 * a + b) 16)
    by (repeat rewrite Z.shiftl_mul_pow2 by lia;
        change (2 ^ 24) with 16777216;
        change (2 ^ 16) with 65536; ring).
  rewrite (lor_high_low__proof_of_threebyte_2 (256 * a + b) (Z.shiftl c 8) 16)
    by (try lia; rewrite Z.shiftl_mul_pow2 by lia; cbv [Z.pow]; lia).
  repeat rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 16) with 65536.
  change (2 ^ 8) with 256.
  ring.
Qed.


Lemma nonzero_nth_bound__proof_of_threebyte_2 : forall s i,
  nonzero_bytes s -> 0 <= i < Zlength s -> 0 <= Znth i s 0 < 256.
Proof.
  intros s i Hbytes Hi.
  unfold nonzero_bytes in Hbytes.
  apply Forall_forall with (x := Znth i s 0) in Hbytes.
  - lia.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma nth_app_zero__proof_of_threebyte_2 : forall s i,
  0 <= i < Zlength s -> Znth i (s ++ [0]) 0 = Znth i s 0.
Proof.
  intros s i Hi.
  unfold Znth.
  apply app_nth1.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

From Coq Require Import Lia.

Lemma fourbyte_byte_bound__proof_of_fourbyte_2 : forall ns k,
  nonzero_bytes ns -> 0 <= k < Zlength ns ->
  0 < Znth k ns 0 < 256.
Proof.
  intros ns k Hnz Hk.
  unfold nonzero_bytes in Hnz.
  rewrite Forall_nth in Hnz.
  unfold Znth.
  apply Hnz.
  rewrite Zlength_correct in Hk.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma fourbyte_substring_bytes__proof_of_fourbyte_2 : forall hs ns i k,
  Zlength ns = 4 -> i < Zlength hs ->
  substring_at hs ns (i - 3) -> 0 <= k < 4 ->
  Znth (i - 3 + k) (hs ++ [0]) 0 = Znth k ns 0.
Proof.
  intros hs ns i k Hlen Hi Hsub Hk.
  destruct Hsub as [Hlo [Hhi Heq]].
  assert (Hidx : 0 <= i - 3 + k < Zlength hs) by lia.
  assert (Hnat : (Z.to_nat (i - 3 + k) < length hs)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  unfold Znth at 1.
  rewrite app_nth1 by exact Hnat.
  assert (Hnth := f_equal (fun l => Znth k l 0) Heq).
  cbn beta in Hnth.
  rewrite Znth_sublist in Hnth by lia.
  replace (k + (i - 3)) with (i - 3 + k) in Hnth by lia.
  unfold Znth in Hnth.
  exact Hnth.
Qed.

Lemma fourbyte_match_word__proof_of_fourbyte_2 : forall hs ns i hw nw,
  nonzero_bytes ns -> rolling4 hs i hw -> needle4 ns nw ->
  i < Zlength hs -> substring_at hs ns (i - 3) -> hw = nw.
Proof.
  intros hs ns i hw nw Hnz Hroll Hneedle Hi Hsub.
  destruct Hroll as [_ Hhw].
  destruct Hneedle as [Hlen Hnw].
  pose proof (fourbyte_substring_bytes__proof_of_fourbyte_2 hs ns i 0 Hlen Hi Hsub ltac:(lia)) as H0.
  pose proof (fourbyte_substring_bytes__proof_of_fourbyte_2 hs ns i 1 Hlen Hi Hsub ltac:(lia)) as H1.
  pose proof (fourbyte_substring_bytes__proof_of_fourbyte_2 hs ns i 2 Hlen Hi Hsub ltac:(lia)) as H2.
  pose proof (fourbyte_substring_bytes__proof_of_fourbyte_2 hs ns i 3 Hlen Hi Hsub ltac:(lia)) as H3.
  replace (i - 3 + 0) with (i - 3) in H0 by lia.
  replace (i - 3 + 1) with (i - 2) in H1 by lia.
  replace (i - 3 + 2) with (i - 1) in H2 by lia.
  replace (i - 3 + 3) with i in H3 by lia.
  rewrite H0, H1, H2, H3 in Hhw.
  pose proof (fourbyte_byte_bound__proof_of_fourbyte_2 ns 0 Hnz ltac:(lia)) as B0.
  pose proof (fourbyte_byte_bound__proof_of_fourbyte_2 ns 1 Hnz ltac:(lia)) as B1.
  pose proof (fourbyte_byte_bound__proof_of_fourbyte_2 ns 2 Hnz ltac:(lia)) as B2.
  pose proof (fourbyte_byte_bound__proof_of_fourbyte_2 ns 3 Hnz ltac:(lia)) as B3.
  rewrite Hhw, Hnw.
  replace 4294967295 with (Z.ones 32) by reflexivity.
  rewrite Z.land_ones by lia.
  change (2 ^ 32) with 4294967296.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma fourbyte_lor_mul256_byte__proof_of_fourbyte_2 : forall x b,
  0 <= b < 256 -> Z.lor (x * 256) b = x * 256 + b.
Proof.
  intros x b Hb.
  assert (Hmask : Z.land (x * 256) (Z.ones 8) = 0).
  { rewrite Z.land_ones by lia.
    change (2 ^ 8) with 256.
    apply Z.mod_mul; lia. }
  assert (Hland : Z.land (x * 256) b = 0).
  { assert (Hbmask : b = Z.land b (Z.ones 8)).
    { rewrite Z.land_ones by lia.
      change (2 ^ 8) with 256.
      symmetry; apply Z.mod_small; lia. }
    rewrite Hbmask.
    rewrite (Z.land_comm b (Z.ones 8)).
    rewrite Z.land_assoc.
    rewrite Hmask.
    apply Z.land_0_l. }
  pose proof (Z.add_lor_land (x * 256) b) as Hsum.
  lia.
Qed.

Lemma fourbyte_shift_word__proof_of_fourbyte_2 : forall a b c d e,
  0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 ->
  0 <= d < 256 -> 0 <= e < 256 ->
  Z.lor
    ((Z.shiftl (Z.land (16777216 * a + 65536 * b + 256 * c + d)
                          4294967295) 8) mod (2 ^ 32))
    (e mod (2 ^ 32)) =
  Z.land (16777216 * b + 65536 * c + 256 * d + e) 4294967295.
Proof.
  intros a b c d e Ha Hb Hc Hd He.
  assert (Hold : Z.land (16777216 * a + 65536 * b + 256 * c + d)
                           4294967295 =
                  16777216 * a + 65536 * b + 256 * c + d).
  { replace 4294967295 with (Z.ones 32) by reflexivity.
    rewrite Z.land_ones by lia.
    change (2 ^ 32) with 4294967296.
    apply Z.mod_small; lia. }
  rewrite Hold.
  assert (Hnew : Z.land (16777216 * b + 65536 * c + 256 * d + e)
                           4294967295 =
                  16777216 * b + 65536 * c + 256 * d + e).
  { replace 4294967295 with (Z.ones 32) by reflexivity.
    rewrite Z.land_ones by lia.
    change (2 ^ 32) with 4294967296.
    apply Z.mod_small; lia. }
  rewrite Hnew.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 8) with 256.
  change (2 ^ 32) with 4294967296.
  rewrite Z.mod_small with (a := e) (b := 4294967296) by lia.
  replace ((16777216 * a + 65536 * b + 256 * c + d) * 256)
    with (a * 4294967296 +
          (16777216 * b + 65536 * c + 256 * d)) by ring.
  rewrite Z.add_mod by lia.
  rewrite Z.mod_mul by lia.
  rewrite Z.add_0_l.
  rewrite Z.mod_mod by lia.
  rewrite Z.mod_small by lia.
  replace (16777216 * b + 65536 * c + 256 * d)
    with ((65536 * b + 256 * c + d) * 256) by ring.
  rewrite fourbyte_lor_mul256_byte__proof_of_fourbyte_2 by lia.
  ring.
Qed.

Lemma fourbyte_app_byte_bound__proof_of_fourbyte_2 : forall hs k,
  nonzero_bytes hs -> 0 <= k <= Zlength hs ->
  0 <= Znth k (hs ++ [0]) 0 < 256.
Proof.
  intros hs k Hnz Hk.
  destruct (Z.eq_dec k (Zlength hs)) as [Heq|Hne].
  - subst k. unfold Znth.
    rewrite app_nth2 by (rewrite Zlength_correct; lia).
    rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length hs)) - length hs)%nat with 0%nat by
      (rewrite Nat2Z.id; lia).
    simpl. lia.
  - assert (Hlt : 0 <= k < Zlength hs) by lia.
    assert (Hnat : (Z.to_nat k < length hs)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct. lia. }
    unfold Znth.
    rewrite app_nth1 by exact Hnat.
    pose proof (fourbyte_byte_bound__proof_of_fourbyte_2 hs k Hnz Hlt) as Hb.
    unfold Znth in Hb; lia.
Qed.

Lemma fourbyte_pack_injective__proof_of_fourbyte_2 :
  forall a b c d a' b' c' d',
    0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
    0 <= a' < 256 -> 0 <= b' < 256 -> 0 <= c' < 256 -> 0 <= d' < 256 ->
    16777216 * a + 65536 * b + 256 * c + d =
    16777216 * a' + 65536 * b' + 256 * c' + d' ->
    a = a' /\ b = b' /\ c = c' /\ d = d'.
Proof.
  intros; lia.
Qed.

Lemma fourbyte_digits_substring__proof_of_fourbyte_2 : forall hs ns i,
  Zlength ns = 4 -> 3 <= i < Zlength hs ->
  (forall k, 0 <= k < 4 ->
     Znth (i - 3 + k) (hs ++ [0]) 0 = Znth k ns 0) ->
  substring_at hs ns (i - 3).
Proof.
  intros hs ns i Hlen Hi Hdigits.
  unfold substring_at.
  split; [lia|]. split; [lia|].
  assert (Hsub_len : Zlength (sublist (i - 3) (i - 3 + Zlength ns) hs) = 4).
  { rewrite Zlength_sublist by lia. lia. }
  apply nth_ext with (d := 0) (d' := 0).
  - apply Nat2Z.inj. rewrite <- !Zlength_correct. lia.
  - intros n Hn.
    assert (Hk : 0 <= Z.of_nat n < 4).
    { rewrite Zlength_correct in Hsub_len. lia. }
    specialize (Hdigits (Z.of_nat n) Hk).
    replace (nth n (sublist (i - 3) (i - 3 + Zlength ns) hs) 0)
      with (Znth (Z.of_nat n) (sublist (i - 3) (i - 3 + Zlength ns) hs) 0)
      by (unfold Znth; rewrite Nat2Z.id; reflexivity).
    replace (nth n ns 0) with (Znth (Z.of_nat n) ns 0)
      by (unfold Znth; rewrite Nat2Z.id; reflexivity).
    rewrite Znth_sublist by lia.
    assert (Hidx : 0 <= i - 3 + Z.of_nat n < Zlength hs) by lia.
    assert (Hnat : (Z.to_nat (i - 3 + Z.of_nat n) < length hs)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct. lia. }
    unfold Znth in Hdigits.
    rewrite app_nth1 in Hdigits by exact Hnat.
    unfold Znth.
    replace (Z.of_nat n + (i - 3)) with (i - 3 + Z.of_nat n) by lia.
    exact Hdigits.
Qed.

Lemma fourbyte_nonzero_read_lt__proof_of_fourbyte_2 : forall hs i,
  0 <= i <= Zlength hs ->
  Znth 0 (sublist i (Zlength hs + 1) (hs ++ [0])) 0 <> 0 ->
  i < Zlength hs.
Proof.
  intros hs i Hi Hread.
  destruct (Z.eq_dec i (Zlength hs)) as [Heq|Hne]; [subst i|lia].
  rewrite Znth_sublist in Hread by (try rewrite Zlength_app_cons; lia).
  unfold Znth in Hread.
  rewrite app_nth2 in Hread by (rewrite Zlength_correct; lia).
  rewrite Zlength_correct in Hread.
  replace (0 + Z.of_nat (Datatypes.length hs)) with
    (Z.of_nat (Datatypes.length hs)) in Hread by lia.
  rewrite Nat2Z.id in Hread.
  rewrite Nat.sub_diag in Hread.
  simpl in Hread; contradiction.
Qed.

Lemma fourbyte_zero_read_eq_len__proof_of_fourbyte_2 : forall hs i,
  nonzero_bytes hs -> 0 <= i <= Zlength hs ->
  Znth 0 (sublist i (Zlength hs + 1) (hs ++ [0])) 0 = 0 ->
  i = Zlength hs.
Proof.
  intros hs i Hnz Hi Hread.
  destruct (Z.eq_dec i (Zlength hs)) as [Heq|Hne]; [exact Heq|].
  assert (Hlt : 0 <= i < Zlength hs) by lia.
  pose proof (fourbyte_byte_bound__proof_of_fourbyte_2 hs i Hnz Hlt) as Hb.
  rewrite Znth_sublist in Hread by (try rewrite Zlength_app_cons; lia).
  assert (Hnat : (Z.to_nat i < length hs)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  replace (0 + i) with i in Hread by lia.
  unfold Znth in Hread, Hb.
  rewrite app_nth1 in Hread by exact Hnat.
  lia.
Qed.

Lemma fourbyte_word_substring__proof_of_fourbyte_2 : forall hs ns i hw nw,
  nonzero_bytes hs -> nonzero_bytes ns ->
  rolling4 hs i hw -> needle4 ns nw -> hw = nw ->
  i < Zlength hs -> substring_at hs ns (i - 3).
Proof.
  intros hs ns i hw nw Hhs Hns Hroll Hneedle Heq Hi.
  destruct Hroll as [Hidx Hhw].
  destruct Hneedle as [Hlen Hnw].
  assert (Ha := fourbyte_app_byte_bound__proof_of_fourbyte_2 hs (i - 3) Hhs ltac:(lia)).
  assert (Hb := fourbyte_app_byte_bound__proof_of_fourbyte_2 hs (i - 2) Hhs ltac:(lia)).
  assert (Hc := fourbyte_app_byte_bound__proof_of_fourbyte_2 hs (i - 1) Hhs ltac:(lia)).
  assert (Hd := fourbyte_app_byte_bound__proof_of_fourbyte_2 hs i Hhs ltac:(lia)).
  assert (Ha' := fourbyte_byte_bound__proof_of_fourbyte_2 ns 0 Hns ltac:(lia)).
  assert (Hb' := fourbyte_byte_bound__proof_of_fourbyte_2 ns 1 Hns ltac:(lia)).
  assert (Hc' := fourbyte_byte_bound__proof_of_fourbyte_2 ns 2 Hns ltac:(lia)).
  assert (Hd' := fourbyte_byte_bound__proof_of_fourbyte_2 ns 3 Hns ltac:(lia)).
  rewrite Hhw, Hnw in Heq.
  replace 4294967295 with (Z.ones 32) in Heq by reflexivity.
  rewrite Z.land_ones in Heq by lia.
  change (2 ^ 32) with 4294967296 in Heq.
  rewrite Z.mod_small in Heq by lia.
  pose proof (fourbyte_pack_injective__proof_of_fourbyte_2
    (Znth (i - 3) (hs ++ [0]) 0)
    (Znth (i - 2) (hs ++ [0]) 0)
    (Znth (i - 1) (hs ++ [0]) 0)
    (Znth i (hs ++ [0]) 0)
    (Znth 0 ns 0) (Znth 1 ns 0) (Znth 2 ns 0) (Znth 3 ns 0)
    Ha Hb Hc Hd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq)
    as [E0 [E1 [E2 E3]]].
  apply fourbyte_digits_substring__proof_of_fourbyte_2; try lia.
  intros k Hk.
  assert (Hcase : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct Hcase as [H0|[H1|[H2|H3]]]; subst k;
    try replace (i - 3 + 0) with (i - 3) by lia;
    try replace (i - 3 + 1) with (i - 2) by lia;
    try replace (i - 3 + 2) with (i - 1) by lia;
    try replace (i - 3 + 3) with i by lia;
    assumption.
Qed.

Lemma fourbyte_lor_disjoint__proof_of_fourbyte_2 : forall x y k,
  0 <= k -> 0 <= y < 2 ^ k ->
  Z.lor (x * 2 ^ k) y = x * 2 ^ k + y.
Proof.
  intros x y k Hk Hy.
  assert (Hmask : Z.land (x * 2 ^ k) (Z.ones k) = 0).
  { rewrite Z.land_ones by lia. apply Z.mod_mul; lia. }
  assert (Hland : Z.land (x * 2 ^ k) y = 0).
  { assert (Hy_mask : y = Z.land y (Z.ones k)).
    { rewrite Z.land_ones by lia. symmetry; apply Z.mod_small; lia. }
    rewrite Hy_mask.
    rewrite (Z.land_comm y (Z.ones k)).
    rewrite Z.land_assoc.
    rewrite Hmask.
    apply Z.land_0_l. }
  pose proof (Z.add_lor_land (x * 2 ^ k) y).
  lia.
Qed.

Lemma fourbyte_pack_or__proof_of_fourbyte_2 : forall a b c d,
  0 <= a < 256 -> 0 <= b < 256 ->
  0 <= c < 256 -> 0 <= d < 256 ->
  Z.lor (Z.lor (Z.lor
    ((Z.shiftl a 24) mod (2 ^ 32))
    ((Z.shiftl b 16) mod (2 ^ 32)))
    ((Z.shiftl c 8) mod (2 ^ 32)))
    (d mod (2 ^ 32)) =
  16777216 * a + 65536 * b + 256 * c + d.
Proof.
  intros a b c d Ha Hb Hc Hd.
  rewrite !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 24) with 16777216.
  change (2 ^ 16) with 65536.
  change (2 ^ 8) with 256.
  change (2 ^ 32) with 4294967296.
  rewrite !Z.mod_small by lia.
  replace (Z.lor (a * 16777216) (b * 65536))
    with (a * 16777216 + b * 65536).
  2: { symmetry. change (Z.lor (a * 2 ^ 24) (b * 65536) =
               a * 2 ^ 24 + b * 65536).
       apply fourbyte_lor_disjoint__proof_of_fourbyte_2;
         change (2 ^ 24) with 16777216; lia. }
  replace (Z.lor (a * 16777216 + b * 65536) (c * 256))
    with (a * 16777216 + b * 65536 + c * 256).
  2: { symmetry.
       replace (a * 16777216 + b * 65536) with ((256 * a + b) * 2 ^ 16)
         by (change (2 ^ 16) with 65536; ring).
       change (Z.lor ((256 * a + b) * 2 ^ 16) (c * 256) =
               (256 * a + b) * 2 ^ 16 + c * 256).
       apply fourbyte_lor_disjoint__proof_of_fourbyte_2;
         change (2 ^ 16) with 65536; lia. }
  replace (Z.lor (a * 16777216 + b * 65536 + c * 256) d)
    with (a * 16777216 + b * 65536 + c * 256 + d).
  2: { symmetry.
       replace (a * 16777216 + b * 65536 + c * 256)
         with ((65536 * a + 256 * b + c) * 2 ^ 8)
         by (change (2 ^ 8) with 256; ring).
       change (Z.lor ((65536 * a + 256 * b + c) * 2 ^ 8) d =
               (65536 * a + 256 * b + c) * 2 ^ 8 + d).
       apply fourbyte_lor_disjoint__proof_of_fourbyte_2;
         change (2 ^ 8) with 256; lia. }
  ring.
Qed.

From Coq Require Import Lia.

Lemma fourbyte_byte_bound__proof_of_fourbyte_3 : forall ns k,
  nonzero_bytes ns -> 0 <= k < Zlength ns ->
  0 < Znth k ns 0 < 256.
Proof.
  intros ns k Hnz Hk.
  unfold nonzero_bytes in Hnz.
  rewrite Forall_nth in Hnz.
  unfold Znth.
  apply Hnz.
  rewrite Zlength_correct in Hk.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma fourbyte_zero_read_eq_len__proof_of_fourbyte_3 : forall hs i,
  nonzero_bytes hs -> 0 <= i <= Zlength hs ->
  Znth 0 (sublist i (Zlength hs + 1) (hs ++ [0])) 0 = 0 ->
  i = Zlength hs.
Proof.
  intros hs i Hnz Hi Hread.
  destruct (Z.eq_dec i (Zlength hs)) as [Heq|Hne]; [exact Heq|].
  assert (Hlt : 0 <= i < Zlength hs) by lia.
  pose proof (fourbyte_byte_bound__proof_of_fourbyte_3 hs i Hnz Hlt) as Hb.
  rewrite Znth_sublist in Hread by (try rewrite Zlength_app_cons; lia).
  assert (Hnat : (Z.to_nat i < length hs)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  replace (0 + i) with i in Hread by lia.
  unfold Znth in Hread, Hb.
  rewrite app_nth1 in Hread by exact Hnat.
  lia.
Qed.

From Coq Require Import Lia.

Lemma nonzero_terminator_index__twoway_table_1 (ns : list Z) (l : Z) :
  nonzero_bytes ns -> 0 <= l <= Zlength ns ->
  Znth l (ns ++ [0]) 0 = 0 -> l = Zlength ns.
Proof.
  intros Hnz [Hlo Hhi] Hz.
  destruct (Z.eq_dec l (Zlength ns)) as [Heq | Hneq]; auto.
  assert (Hlt : 0 <= l < Zlength ns) by lia.
  rewrite app_Znth1 in Hz by exact Hlt.
  unfold nonzero_bytes in Hnz.
  rewrite Forall_forall in Hnz.
  specialize (Hnz (Znth l ns 0)).
  assert (Hin : In (Znth l ns 0) ns).
  { unfold Znth. apply nth_In. rewrite Zlength_correct in Hlt. lia. }
  specialize (Hnz Hin).
  lia.
Qed.

Lemma nonzero_index_lt__twoway_table_1 (s : list Z) (i : Z) :
  0 <= i <= Zlength s -> Znth i (s ++ [0]) 0 <> 0 -> i < Zlength s.
Proof.
  intros [Hlo Hhi] Hnz.
  destruct (Z.eq_dec i (Zlength s)) as [Heq | Hneq]; [|lia].
  subst i.
  rewrite app_Znth2 in Hnz by lia.
  replace (Zlength s - Zlength s) with 0 in Hnz by lia.
  simpl in Hnz. contradiction.
Qed.

Lemma byte_at_or_terminator__twoway_table_1 (s : list Z) (i : Z) :
  nonzero_bytes s -> 0 <= i <= Zlength s ->
  0 <= Znth i (s ++ [0]) 0 < 256.
Proof.
  intros Hnz [Hlo Hhi].
  destruct (Z.eq_dec i (Zlength s)) as [Heq | Hneq].
  - subst i. rewrite app_Znth2 by lia.
    replace (Zlength s - Zlength s) with 0 by lia.
    unfold Znth. simpl. lia.
  - assert (Hlt : 0 <= i < Zlength s) by lia.
    rewrite app_Znth1 by exact Hlt.
    unfold nonzero_bytes in Hnz.
    rewrite Forall_forall in Hnz.
    specialize (Hnz (Znth i s 0)).
    assert (Hin : In (Znth i s 0) s).
    { unfold Znth. apply nth_In. rewrite Zlength_correct in Hlt. lia. }
    specialize (Hnz Hin). lia.
Qed.

Lemma shift_prefix_step__twoway_table_1
    (needle : list Z) (upto a : Z) (entries : list Z) :
  0 <= upto < Zlength needle ->
  0 <= a < 256 ->
  Znth upto needle 0 = a ->
  Zlength entries = 256 ->
  shift_prefix needle upto entries ->
  shift_prefix needle (upto + 1)
    (replace_Znth a (upto + 1) entries).
Proof.
  intros Hupto Ha Hat Hlen Hold.
  unfold shift_prefix in *.
  intros c j Hc Hj Hsame Hlast.
  destruct (Z.eq_dec j upto) as [Hju | Hju].
  - subst j. assert (c = a) by congruence. subst c. rewrite Hat in *.
    apply Znth_replace_Znth_Same. lia.
  - assert (Hjold : 0 <= j < upto) by lia.
    assert (Hca : c <> a).
    { intro Heq. subst c. specialize (Hlast upto ltac:(lia)). congruence. }
    rewrite Znth_replace_Znth_Diff by lia.
    apply Hold; try assumption.
    intros k Hk. apply Hlast. lia.
Qed.

Lemma mask_testbit__twoway_table_1 (k b : Z) :
  0 <= k < 64 -> 0 <= b < 64 ->
  Z.testbit ((Z.shiftl 1 k) mod (2 ^ 64)) b = Z.eqb b k.
Proof.
  intros Hk Hb.
  rewrite Z.mod_pow2_bits_low by lia.
  destruct (Z.lt_trichotomy b k) as [Hlt | [-> | Hgt]].
  - rewrite Z.shiftl_spec_low by lia.
    symmetry. apply Z.eqb_neq. lia.
  - rewrite Z.shiftl_spec by lia.
    replace (k - k) with 0 by lia.
    simpl. symmetry. apply Z.eqb_refl.
  - rewrite Z.shiftl_spec by lia.
    replace (b =? k) with false by (symmetry; apply Z.eqb_neq; lia).
    apply Z.bits_above_log2; [lia |]. cbn. lia.
Qed.

Lemma byteset_prefix_step__twoway_table_1
    (needle : list Z) (upto a : Z) (bits : list Z) :
  0 <= upto < Zlength needle ->
  0 <= a < 256 ->
  Znth upto needle 0 = a ->
  Zlength bits = 4 ->
  byteset_prefix needle upto bits ->
  byteset_prefix needle (upto + 1)
    (replace_Znth (a / 64)
      (Z.lor (Znth (a / 64) bits 0)
        ((Z.shiftl 1 (a mod 64)) mod (2 ^ 64))) bits).
Proof.
  intros Hupto Ha Hat Hlen Hold.
  unfold byteset_prefix in *.
  intros c Hc.
  assert (Hai : 0 <= a / 64 < 4).
  { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  assert (Hci : 0 <= c / 64 < 4).
  { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  assert (Ham : 0 <= a mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (Hcm : 0 <= c mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  destruct (Z.eq_dec (c / 64) (a / 64)) as [Hword | Hword].
  - rewrite Hword.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Z.lor_spec.
    rewrite mask_testbit__twoway_table_1 by lia.
    specialize (Hold c Hc).
    rewrite Hword in Hold.
    destruct (Z.eq_dec c a) as [Hca | Hca].
    + subst c. rewrite Z.eqb_refl. rewrite Bool.orb_true_r.
      split.
      * intro Htrue. exists upto. split; [lia | exact Hat].
      * intro Hexists. reflexivity.
    + assert (Hmodneq : c mod 64 <> a mod 64).
      { intro Hmod.
        pose proof (Z.div_mod c 64 ltac:(lia)) as Hcd.
        pose proof (Z.div_mod a 64 ltac:(lia)) as Had.
        lia. }
      replace (c mod 64 =? a mod 64) with false
        by (symmetry; apply Z.eqb_neq; exact Hmodneq).
      rewrite Bool.orb_false_r.
      split.
      * intros Hbit. apply Hold in Hbit.
        destruct Hbit as [j [Hj Hsame]].
        exists j. split; auto. lia.
      * intros [j [Hj Hsame]].
        assert (j < upto) by (destruct (Z.eq_dec j upto); [subst; congruence | lia]).
        apply Hold. exists j. split; auto. lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    specialize (Hold c Hc).
    assert (Hca : c <> a) by (intro Heq; subst; contradiction).
    split.
    + intros Hbit. apply Hold in Hbit.
      destruct Hbit as [j [Hj Hsame]].
      exists j. split; auto. lia.
    + intros [j [Hj Hsame]].
      assert (j < upto) by (destruct (Z.eq_dec j upto); [subst; congruence | lia]).
      apply Hold. exists j. split; auto. lia.
Qed.

From Coq Require Import Lia.

(* Direct migration of the old two_way_list_lemmas.Zsublist_hi_plus_1. *)
Lemma Zsublist_hi_plus_1__factor_equal_1 {A : Type} (default : A)
    (l1 l2 : list A) (lo hi lo' hi' : Z) :
  0 <= lo <= hi -> hi + 1 <= Zlength l1 ->
  0 <= lo' <= hi' -> hi' + 1 <= Zlength l2 ->
  sublist lo hi l1 = sublist lo' hi' l2 ->
  Znth hi l1 default = Znth hi' l2 default ->
  sublist lo (hi + 1) l1 = sublist lo' (hi' + 1) l2.
Proof.
  intros Hlo Hhi Hlo' Hhi' Hsub Hnth.
  rewrite (sublist_split lo (hi + 1) hi) by lia.
  rewrite (sublist_split lo' (hi' + 1) hi') by lia.
  rewrite Hsub.
  rewrite (sublist_single default hi l1) by lia.
  rewrite (sublist_single default hi' l2) by lia.
  rewrite Hnth.
  reflexivity.
Qed.

(* Direct migration of the old maxsuf_periodicity_ext proof. *)
Lemma maxsuf_periodicity_ext__factor_equal_1
    (needle : list Z) (start jp k p t z : Z) :
  0 <= p -> maxsuf_periodicity needle start jp k p ->
  start <= t -> 0 <= z -> t + z * p < jp + k ->
  Znth t needle 0 = Znth (t + z * p) needle 0.
Proof.
  intros Hp Hper Ht Hz Hbound.
  set (n := Z.to_nat z).
  replace z with (Z.of_nat n) in * by lia.
  induction n.
  - simpl. replace (t + 0) with t by lia. reflexivity.
  - rewrite Nat2Z.inj_succ.
    replace (t + Z.succ (Z.of_nat n) * p)
      with (t + Z.of_nat n * p + p) by lia.
    pose proof Hper (t + Z.of_nat n * p) as Hstep.
    assert (start <= t + Z.of_nat n * p) by lia.
    assert (t + Z.of_nat n * p + p < jp + k) by lia.
    specialize (Hstep H H0).
    rewrite <- Hstep.
    apply IHn; lia.
Qed.

Lemma Zmod_shift_small__factor_equal_1 (x d m : Z) :
  0 < m -> 0 <= d -> 0 <= x mod m + d < m ->
  (x + d) mod m = x mod m + d.
Proof.
  intros Hm Hd Hrange.
  pose proof (Z.mod_pos_bound x m Hm) as Hx.
  rewrite Z.add_mod by lia.
  rewrite (Z.mod_small d m) by lia.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma maxsuf_intermediate_period_bound__factor_equal_1
    (needle : list Z) (start p direction : Z) :
  1 < p -> maxsuf_intermediate_optimal needle start p direction ->
  start + p <= Zlength needle.
Proof.
  intros Hp Hopt.
  specialize (Hopt (start + p - 1) ltac:(lia)).
  destruct Hopt as [d [Hd [_ [Hlen _]]]].
  lia.
Qed.

From Coq Require Import Lia.

Lemma maxsuf_match_point__factor_reset_1 (needle : list Z) (jp k t : Z) :
  0 <= jp ->
  maxsuf_partial_match needle 0 jp k ->
  0 <= t < k - 1 ->
  Znth t needle 0 = Znth (jp + 1 + t) needle 0.
Proof.
  intros Hjp Hpm Ht.
  unfold maxsuf_partial_match in Hpm.
  replace (0 + k - 1) with (k - 1) in Hpm by lia.
  assert (H : Znth t (sublist 0 (k - 1) needle) 0 =
              Znth t (sublist (jp + 1) (jp + k) needle) 0).
  { now rewrite Hpm. }
  rewrite (Znth_sublist 0 0 t (k - 1) needle) in H by lia.
  rewrite (Znth_sublist 0 (jp + 1) t (jp + k) needle) in H by lia.
  replace (t + 0) with t in H by lia.
  replace (t + (jp + 1)) with (jp + 1 + t) in H by lia.
  exact H.
Qed.

Lemma maxsuf_periodic_ext__factor_reset_1
    (needle : list Z) (jp k p t q : Z) :
  0 < p -> 0 <= q -> 0 <= t -> t + q * p < jp + k ->
  maxsuf_periodicity needle 0 jp k p ->
  Znth t needle 0 = Znth (t + q * p) needle 0.
Proof.
  intros Hp Hq Ht Hbound Hper.
  set (n := Z.to_nat q).
  replace q with (Z.of_nat n) in * by (unfold n; lia).
  induction n.
  - simpl. replace (t + 0) with t by lia. reflexivity.
  - rewrite Nat2Z.inj_succ.
    replace (t + Z.succ (Z.of_nat n) * p)
      with (t + Z.of_nat n * p + p) by lia.
    transitivity (Znth (t + Z.of_nat n * p) needle 0).
    + apply IHn; lia.
    + apply Hper; lia.
Qed.

Lemma Znth_app_left__factor_reset_1
    {A : Type} (d : A) (l1 l2 : list A) i :
  0 <= i < Zlength l1 ->
  Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros Hi. unfold Znth. rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi. lia.
Qed.

Lemma maxsuf_reset_optimal__factor_reset_1
    (needle : list Z) (jp k p z : Z) :
  0 <= jp -> 1 <= k <= p -> jp + k < Zlength needle ->
  jp + 1 = z * p ->
  maxsuf_partial_match needle 0 jp k ->
  maxsuf_periodicity needle 0 jp k p ->
  maxsuf_intermediate_optimal needle 0 p 1 ->
  Znth (k - 1) needle 0 < Znth (jp + k) needle 0 ->
  maxsuf_optimal needle (jp + 1) 1.
Proof.
  intros Hjp Hkp Hlen Hz Hpm Hper Hmid Hcmp.
  assert (Hp : 0 < p) by lia.
  assert (Hzpos : 0 < z) by nia.
  unfold maxsuf_optimal.
  intros earlier Hearlier.
  set (r := earlier mod p).
  set (q := earlier / p).
  assert (Hr : 0 <= r < p).
  { unfold r. apply Z.mod_pos_bound. lia. }
  assert (Hdecomp : earlier = r + q * p).
  { unfold r, q. pose proof (Z.div_mod earlier p ltac:(lia)). lia. }
  assert (Hq : 0 <= q < z) by nia.
  destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
  - exists (k - 1). repeat split; try lia.
    + intros t Ht.
      pose proof (maxsuf_match_point__factor_reset_1 needle jp k t Hjp Hpm Ht) as Hmatch.
      pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p t q Hp
        ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
      replace (earlier + t) with (t + q * p) by lia.
      symmetry in Hmatch. etransitivity; eauto.
    + intros _. pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p
        (k - 1) q Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
      replace (earlier + (k - 1)) with (k - 1 + q * p) by lia.
      replace (jp + 1 + (k - 1)) with (jp + k) by lia.
      lia.
  - assert (Hrpos : 0 < r < p) by lia.
    specialize (Hmid r ltac:(lia)).
    destruct Hmid as [d0 [Hd0 [Hwindow [Hdbound [Heq [Hgt _]]]]]].
    specialize (Hgt eq_refl).
    replace (0 + d0) with d0 in Hgt by lia.
    replace (0 + d0) with d0 in Hwindow by lia.
    destruct (Z_lt_ge_dec d0 (k - 1)) as [Hearly | Hlate].
    + exists d0. repeat split; try lia.
      * intros t Ht.
        pose proof (maxsuf_match_point__factor_reset_1 needle jp k t Hjp Hpm ltac:(lia)) as Hmatch.
        pose proof (Heq t Ht) as Hprefix.
        pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p (r + t) q
          Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
        replace (earlier + t) with (r + t + q * p) by lia.
        symmetry in Hmatch. etransitivity; [exact Hmatch|].
        etransitivity; [exact Hprefix|exact Hperiod].
      * intros _. pose proof (maxsuf_match_point__factor_reset_1 needle jp k d0 Hjp Hpm ltac:(lia)) as Hmatch.
        pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p (r + d0) q
          Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
        replace (earlier + d0) with (r + d0 + q * p) by lia.
        lia.
    + exists (k - 1). repeat split; try lia.
      * intros t Ht.
        pose proof (maxsuf_match_point__factor_reset_1 needle jp k t Hjp Hpm Ht) as Hmatch.
        pose proof (Heq t ltac:(lia)) as Hprefix.
        pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p (r + t) q
          Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
        replace (earlier + t) with (r + t + q * p) by lia.
        symmetry in Hmatch. etransitivity; [exact Hmatch|].
        etransitivity; [exact Hprefix|exact Hperiod].
      * intros _.
        pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p (r + k - 1) q
          Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
        replace (earlier + (k - 1)) with (r + k - 1 + q * p) by lia.
        replace (jp + 1 + (k - 1)) with (jp + k) by lia.
        destruct (Z.eq_dec d0 (k - 1)) as [Hequal | Hlater].
        -- subst d0.
           replace (r + (k - 1)) with (r + k - 1) in Hgt by lia.
           lia.
        -- pose proof (Heq (k - 1) ltac:(lia)) as Hprefix.
           replace (0 + (k - 1)) with (k - 1) in Hprefix by lia.
           replace (r + (k - 1)) with (r + k - 1) in Hprefix by lia.
           lia.
Qed.

(* The strict-comparison period update, migrated from the three residue
   cases of maxsuf_optimality2_holds_Lt in the earlier Two-Way proof.
   The first differing byte is explicit in this version of the invariant. *)
Lemma maxsuf_strict_extend_zero__factor_strict_1
    (needle : list Z) (jp k p z : Z) :
  0 <= jp -> 1 <= k <= p -> jp + k < Zlength needle ->
  jp + 1 = z * p ->
  maxsuf_periodicity needle 0 jp k p ->
  maxsuf_intermediate_optimal needle 0 p 1 ->
  Znth (k - 1) needle 0 > Znth (jp + k) needle 0 ->
  maxsuf_intermediate_optimal needle 0 (jp + k + 1) 1.
Proof.
  intros Hjp Hkp Hlen Hz Hper Hmid Hcmp.
  assert (Hp : 0 < p) by lia.
  assert (Hzpos : 0 < z) by nia.
  unfold maxsuf_intermediate_optimal.
  intros intermediate Hinter.
  set (r := intermediate mod p).
  set (q := intermediate / p).
  assert (Hr : 0 <= r < p).
  { unfold r. apply Z.mod_pos_bound. lia. }
  assert (Hdecomp : intermediate = r + q * p).
  { unfold r, q. pose proof (Z.div_mod intermediate p ltac:(lia)). lia. }
  assert (Hq : 0 <= q <= z) by nia.
  destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
  - assert (Hqpos : 0 < q) by nia.
    exists (jp + k - intermediate).
    repeat split; try lia.
    + intros t Ht.
      replace (0 + t) with t by lia.
      replace (intermediate + t) with (t + q * p) by lia.
      eapply maxsuf_periodic_ext__factor_reset_1; eauto; lia.
    + intros _.
      replace (intermediate + (jp + k - intermediate)) with (jp + k) by lia.
      replace (0 + (jp + k - intermediate)) with
        (k - 1 + (z - q) * p) by nia.
      pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p
        (k - 1) (z - q) Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Heq.
      lia.
  - assert (Hrpos : 0 < r < p) by lia.
    specialize (Hmid r ltac:(lia)).
    destruct Hmid as [d0 [Hd0 [Hwindow [Hdbound [Heq [Hgt _]]]]]].
    specialize (Hgt eq_refl).
    replace (0 + d0) with d0 in Hgt by lia.
    destruct (Z_lt_ge_dec q z) as [Hqsmall | Hqeq].
    + exists d0. repeat split; try nia.
      * intros t Ht.
        replace (0 + t) with t by lia.
        replace (intermediate + t) with (r + t + q * p) by lia.
        pose proof (Heq t Ht) as Hprefix.
        replace (0 + t) with t in Hprefix by lia.
        rewrite Hprefix.
        eapply maxsuf_periodic_ext__factor_reset_1; eauto; nia.
      * intros _.
        replace (0 + d0) with d0 by lia.
        replace (intermediate + d0) with (r + d0 + q * p) by lia.
        pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p
          (r + d0) q Hp ltac:(lia) ltac:(lia) ltac:(nia) Hper) as Hperiod.
        lia.
    + assert (Hqexact : q = z) by lia.
      assert (HrK : r < k) by nia.
      destruct (Z_lt_ge_dec d0 (k - r - 1)) as [Hearly | Hlate].
      * exists d0. repeat split; try nia.
        -- intros t Ht.
           replace (0 + t) with t by lia.
           replace (intermediate + t) with (r + t + q * p) by lia.
           pose proof (Heq t Ht) as Hprefix.
        replace (0 + t) with t in Hprefix by lia.
        rewrite Hprefix.
           eapply maxsuf_periodic_ext__factor_reset_1; eauto; nia.
        -- intros _.
           replace (0 + d0) with d0 by lia.
           replace (intermediate + d0) with (r + d0 + q * p) by lia.
           pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p
             (r + d0) q Hp ltac:(lia) ltac:(lia) ltac:(nia) Hper) as Hperiod.
           lia.
      * exists (k - r - 1). repeat split; try nia.
        -- intros t Ht.
           replace (0 + t) with t by lia.
           replace (intermediate + t) with (r + t + q * p) by lia.
           pose proof (Heq t ltac:(lia)) as Hprefix.
           replace (0 + t) with t in Hprefix by lia.
           rewrite Hprefix.
           eapply maxsuf_periodic_ext__factor_reset_1; eauto; nia.
        -- intros _.
           replace (0 + (k - r - 1)) with (k - r - 1) by lia.
           replace (intermediate + (k - r - 1)) with (jp + k) by nia.
           destruct (Z.eq_dec d0 (k - r - 1)) as [Hsame | Hgreater].
           ++ subst d0.
              replace (r + (k - r - 1)) with (k - 1) in Hgt by lia.
              lia.
           ++ pose proof (Heq (k - r - 1) ltac:(lia)) as Hedge.
              replace (0 + (k - r - 1)) with (k - r - 1) in Hedge by lia.
              replace (r + (k - r - 1)) with (k - 1) in Hedge by lia.
              lia.
Qed.

(* The general-start case is the same old Lt transition on the needle tail.
   Translating through sublist changes only indices, not the comparison. *)
Lemma maxsuf_strict_extend__factor_strict_2
    (needle : list Z) (start jp k p z : Z) :
  0 <= start <= jp -> 1 <= k <= p -> jp + k < Zlength needle ->
  jp + 1 = start + z * p ->
  maxsuf_periodicity needle start jp k p ->
  maxsuf_intermediate_optimal needle start p 1 ->
  Znth (start + k - 1) needle 0 > Znth (jp + k) needle 0 ->
  maxsuf_intermediate_optimal needle start (jp + k + 1 - start) 1.
Proof.
  intros Hstart Hkp Hlen Hz Hper Hmid Hcmp.
  set (tail := sublist start (Zlength needle) needle).
  assert (Htail_len : Zlength tail = Zlength needle - start).
  { unfold tail. rewrite Zlength_sublist; lia. }
  assert (Htail : forall t, 0 <= t < Zlength tail ->
      Znth t tail 0 = Znth (start + t) needle 0).
  { intros t Ht. unfold tail.
    rewrite (Znth_sublist 0 start t (Zlength needle) needle) by lia.
    f_equal. lia. }
  assert (Htail_per : maxsuf_periodicity tail 0 (jp - start) k p).
  { unfold maxsuf_periodicity in *.
    intros t Ht Hbound.
    rewrite !Htail by lia.
    replace (start + (t + p)) with (start + t + p) by lia.
    apply Hper; lia. }
  assert (Htail_mid : maxsuf_intermediate_optimal tail 0 p 1).
  { unfold maxsuf_intermediate_optimal in *.
    intros u Hu.
    specialize (Hmid (start + u) ltac:(lia)).
    destruct Hmid as [d [Hd [Hwindow [Hbound [Heq [Hgt Hlt]]]]]].
    exists d. repeat split; try lia.
    - intros t Ht.
      rewrite !Htail by lia.
      replace (start + (u + t)) with (start + u + t) by lia.
      apply Heq; lia.
    - intros _.
      rewrite !Htail by lia.
      replace (start + (u + d)) with (start + u + d) by lia.
      apply Hgt. reflexivity.
    }
  assert (Htail_cmp : Znth (k - 1) tail 0 >
      Znth (jp - start + k) tail 0).
  { rewrite !Htail by lia.
    replace (start + (k - 1)) with (start + k - 1) by lia.
    replace (start + (jp - start + k)) with (jp + k) by lia.
    exact Hcmp. }
  pose proof (maxsuf_strict_extend_zero__factor_strict_1 tail
    (jp - start) k p z ltac:(lia) Hkp ltac:(lia) ltac:(lia)
    Htail_per Htail_mid Htail_cmp) as Hnew.
  unfold maxsuf_intermediate_optimal in *.
  intros intermediate Hinter.
  specialize (Hnew (intermediate - start) ltac:(lia)).
  destruct Hnew as [d [Hd [Hwindow [Hbound [Heq [Hgt Hlt]]]]]].
  exists d. repeat split; try lia.
  - intros t Ht.
    specialize (Heq t Ht).
    rewrite !Htail in Heq by lia.
    replace (start + (intermediate - start + t)) with
      (intermediate + t) in Heq by lia.
    replace (start + (0 + t)) with (start + t) in Heq by lia.
    exact Heq.
  - intros _.
    specialize (Hgt eq_refl).
    rewrite !Htail in Hgt by lia.
    replace (start + (intermediate - start + d)) with
      (intermediate + d) in Hgt by lia.
    replace (start + (0 + d)) with (start + d) in Hgt by lia.
    exact Hgt.
Qed.

(* General-start form of the old maxsuf_optimality_holds_Gt transition.
   The old candidate's optimality covers positions before [start]; the
   period/residue decomposition covers positions from [start] to [jp]. *)
Lemma maxsuf_match_point__factor_reset_2
    (needle : list Z) (start jp k t : Z) :
  0 <= start <= jp ->
  maxsuf_partial_match needle start jp k ->
  0 <= t < k - 1 ->
  Znth (start + t) needle 0 = Znth (jp + 1 + t) needle 0.
Proof.
  intros Hstart Hpm Ht.
  unfold maxsuf_partial_match in Hpm.
  assert (H : Znth t (sublist start (start + k - 1) needle) 0 =
              Znth t (sublist (jp + 1) (jp + k) needle) 0).
  { now rewrite Hpm. }
  rewrite (Znth_sublist 0 start t (start + k - 1) needle) in H by lia.
  rewrite (Znth_sublist 0 (jp + 1) t (jp + k) needle) in H by lia.
  replace (t + start) with (start + t) in H by lia.
  replace (t + (jp + 1)) with (jp + 1 + t) in H by lia.
  exact H.
Qed.

Lemma maxsuf_reset_optimal__factor_reset_2
    (needle : list Z) (start jp k p z : Z) :
  0 <= start <= jp -> 1 <= k <= p -> jp + k < Zlength needle ->
  jp + 1 = start + z * p ->
  maxsuf_partial_match needle start jp k ->
  maxsuf_periodicity needle start jp k p ->
  maxsuf_optimal needle start 1 ->
  maxsuf_intermediate_optimal needle start p 1 ->
  Znth (start + k - 1) needle 0 < Znth (jp + k) needle 0 ->
  maxsuf_optimal needle (jp + 1) 1.
Proof.
  intros Hstart Hkp Hlen Hz Hpm Hper Hopt Hmid Hcmp.
  assert (Hp : 0 < p) by lia.
  assert (Hzpos : 0 < z) by nia.
  unfold maxsuf_optimal.
  intros earlier Hearlier.
  destruct (Z_lt_ge_dec earlier start) as [Hbefore | Hafter].
  - specialize (Hopt earlier ltac:(lia)).
    destruct Hopt as [d0 [Hd0 [Hstartlen [Hearlierlen [Heq [Hgt _]]]]]].
    specialize (Hgt eq_refl).
    destruct (Z_lt_ge_dec d0 (k - 1)) as [Hearly | Hlate].
    + exists d0. repeat split; try lia.
      * intros t Ht.
        pose proof (maxsuf_match_point__factor_reset_2 needle start jp k t
          Hstart Hpm ltac:(lia)) as Hmatch.
        pose proof (Heq t Ht) as Hprefix.
        lia.
      * intros _.
        pose proof (maxsuf_match_point__factor_reset_2 needle start jp k d0
          Hstart Hpm ltac:(lia)) as Hmatch.
        lia.
    + exists (k - 1). repeat split; try lia.
      * intros t Ht.
        pose proof (maxsuf_match_point__factor_reset_2 needle start jp k t
          Hstart Hpm Ht) as Hmatch.
        pose proof (Heq t ltac:(lia)) as Hprefix.
        lia.
      * intros _.
        destruct (Z.eq_dec d0 (k - 1)) as [Hsame | Hgreater].
        -- subst d0.
           replace (jp + 1 + (k - 1)) with (jp + k) by lia.
           replace (start + (k - 1)) with (start + k - 1) in Hgt by lia.
           lia.
        -- pose proof (Heq (k - 1) ltac:(lia)) as Hprefix.
           replace (jp + 1 + (k - 1)) with (jp + k) by lia.
           replace (start + (k - 1)) with (start + k - 1) in Hprefix by lia.
           lia.
  - set (offset := earlier - start).
    set (r := offset mod p).
    set (q := offset / p).
    assert (Hr : 0 <= r < p).
    { unfold r. apply Z.mod_pos_bound. lia. }
    assert (Hdecomp : earlier = start + r + q * p).
    { unfold r, q, offset.
      pose proof (Z.div_mod (earlier - start) p ltac:(lia)). lia. }
    assert (Hq : 0 <= q < z) by nia.
    destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
    + exists (k - 1). repeat split; try lia.
      * intros t Ht.
        pose proof (maxsuf_match_point__factor_reset_2 needle start jp k t
          Hstart Hpm Ht) as Hmatch.
        pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
          (start + t) q ltac:(lia) Hper ltac:(lia) ltac:(lia) ltac:(lia))
          as Hperiod.
        replace (earlier + t) with (start + t + q * p) by lia.
        lia.
      * intros _.
        pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
          (start + k - 1) q ltac:(lia) Hper ltac:(lia) ltac:(lia)
          ltac:(lia)) as Hperiod.
        replace (earlier + (k - 1)) with
          (start + k - 1 + q * p) by lia.
        replace (jp + 1 + (k - 1)) with (jp + k) by lia.
        lia.
    + assert (Hrpos : 0 < r < p) by lia.
      specialize (Hmid (start + r) ltac:(lia)).
      destruct Hmid as [d0 [Hd0 [Hwindow [Hdbound [Heq [Hgt _]]]]]].
      specialize (Hgt eq_refl).
      destruct (Z_lt_ge_dec d0 (k - 1)) as [Hearly | Hlate].
      * exists d0. repeat split; try lia.
        -- intros t Ht.
           pose proof (maxsuf_match_point__factor_reset_2 needle start jp k t
             Hstart Hpm ltac:(lia)) as Hmatch.
           pose proof (Heq t Ht) as Hprefix.
           pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
             (start + r + t) q ltac:(lia) Hper ltac:(lia) ltac:(lia)
             ltac:(lia)) as Hperiod.
           replace (earlier + t) with (start + r + t + q * p) by lia.
           lia.
        -- intros _.
           pose proof (maxsuf_match_point__factor_reset_2 needle start jp k d0
             Hstart Hpm ltac:(lia)) as Hmatch.
           pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
             (start + r + d0) q ltac:(lia) Hper ltac:(lia) ltac:(lia)
             ltac:(lia)) as Hperiod.
           replace (earlier + d0) with (start + r + d0 + q * p) by lia.
           lia.
      * exists (k - 1). repeat split; try lia.
        -- intros t Ht.
           pose proof (maxsuf_match_point__factor_reset_2 needle start jp k t
             Hstart Hpm Ht) as Hmatch.
           pose proof (Heq t ltac:(lia)) as Hprefix.
           pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
             (start + r + t) q ltac:(lia) Hper ltac:(lia) ltac:(lia)
             ltac:(lia)) as Hperiod.
           replace (earlier + t) with (start + r + t + q * p) by lia.
           lia.
        -- intros _.
           pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
             (start + r + k - 1) q ltac:(lia) Hper ltac:(lia) ltac:(lia)
             ltac:(lia)) as Hperiod.
           replace (earlier + (k - 1)) with
             (start + r + k - 1 + q * p) by lia.
           replace (jp + 1 + (k - 1)) with (jp + k) by lia.
           destruct (Z.eq_dec d0 (k - 1)) as [Hsame | Hgreater].
           ++ subst d0.
              replace (start + (k - 1)) with (start + k - 1) in Hgt by lia.
              replace (start + r + (k - 1)) with
                (start + r + k - 1) in Hgt by lia.
              lia.
           ++ pose proof (Heq (k - 1) ltac:(lia)) as Hprefix.
              replace (start + (k - 1)) with (start + k - 1) in Hprefix by lia.
              replace (start + r + (k - 1)) with
                (start + r + k - 1) in Hprefix by lia.
              lia.
Qed.

(* Reverse byte order: the same period and residue argument as the first scan. *)
Lemma maxsuf_reset_optimal_reverse__factor_reset_1
    (needle : list Z) (jp k p z : Z) :
  0 <= jp -> 1 <= k <= p -> jp + k < Zlength needle ->
  jp + 1 = z * p ->
  maxsuf_partial_match needle 0 jp k ->
  maxsuf_periodicity needle 0 jp k p ->
  maxsuf_intermediate_optimal needle 0 p 0 ->
  Znth (k - 1) needle 0 > Znth (jp + k) needle 0 ->
  maxsuf_optimal needle (jp + 1) 0.
Proof.
  intros Hjp Hkp Hlen Hz Hpm Hper Hmid Hcmp.
  assert (Hp : 0 < p) by lia.
  assert (Hzpos : 0 < z) by nia.
  unfold maxsuf_optimal.
  intros earlier Hearlier.
  set (r := earlier mod p).
  set (q := earlier / p).
  assert (Hr : 0 <= r < p).
  { unfold r. apply Z.mod_pos_bound. lia. }
  assert (Hdecomp : earlier = r + q * p).
  { unfold r, q. pose proof (Z.div_mod earlier p ltac:(lia)). lia. }
  assert (Hq : 0 <= q < z) by nia.
  destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
  - exists (k - 1). repeat split; try lia.
    + intros t Ht.
      pose proof (maxsuf_match_point__factor_reset_1 needle jp k t Hjp Hpm Ht) as Hmatch.
      pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p t q Hp
        ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
      replace (earlier + t) with (t + q * p) by lia.
      symmetry in Hmatch. etransitivity; eauto.
    + intros _. pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p
        (k - 1) q Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
      replace (earlier + (k - 1)) with (k - 1 + q * p) by lia.
      replace (jp + 1 + (k - 1)) with (jp + k) by lia.
      lia.
  - assert (Hrpos : 0 < r < p) by lia.
    specialize (Hmid r ltac:(lia)).
    destruct Hmid as [d0 [Hd0 [Hwindow [Hdbound [Heq [_ Hlt]]]]]].
    specialize (Hlt eq_refl).
    replace (0 + d0) with d0 in Hlt by lia.
    replace (0 + d0) with d0 in Hwindow by lia.
    destruct (Z_lt_ge_dec d0 (k - 1)) as [Hearly | Hlate].
    + exists d0. repeat split; try lia.
      * intros t Ht.
        pose proof (maxsuf_match_point__factor_reset_1 needle jp k t Hjp Hpm ltac:(lia)) as Hmatch.
        pose proof (Heq t Ht) as Hprefix.
        pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p (r + t) q
          Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
        replace (earlier + t) with (r + t + q * p) by lia.
        symmetry in Hmatch. etransitivity; [exact Hmatch|].
        etransitivity; [exact Hprefix|exact Hperiod].
      * intros _. pose proof (maxsuf_match_point__factor_reset_1 needle jp k d0 Hjp Hpm ltac:(lia)) as Hmatch.
        pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p (r + d0) q
          Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
        replace (earlier + d0) with (r + d0 + q * p) by lia.
        lia.
    + exists (k - 1). repeat split; try lia.
      * intros t Ht.
        pose proof (maxsuf_match_point__factor_reset_1 needle jp k t Hjp Hpm Ht) as Hmatch.
        pose proof (Heq t ltac:(lia)) as Hprefix.
        pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p (r + t) q
          Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
        replace (earlier + t) with (r + t + q * p) by lia.
        symmetry in Hmatch. etransitivity; [exact Hmatch|].
        etransitivity; [exact Hprefix|exact Hperiod].
      * intros _.
        pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p (r + k - 1) q
          Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Hperiod.
        replace (earlier + (k - 1)) with (r + k - 1 + q * p) by lia.
        replace (jp + 1 + (k - 1)) with (jp + k) by lia.
        destruct (Z.eq_dec d0 (k - 1)) as [Hequal | Hlater].
        -- subst d0.
           replace (r + (k - 1)) with (r + k - 1) in Hlt by lia.
           lia.
        -- pose proof (Heq (k - 1) ltac:(lia)) as Hprefix.
           replace (0 + (k - 1)) with (k - 1) in Hprefix by lia.
           replace (r + (k - 1)) with (r + k - 1) in Hprefix by lia.
           lia.
Qed.


(* General-start reset in reverse byte order; migrated from the same
   factorization argument as maxsuf_reset_optimal__factor_reset_2. *)
Lemma maxsuf_reset_optimal_reverse__factor_reset_2
    (needle : list Z) (start jp k p z : Z) :
  0 <= start <= jp -> 1 <= k <= p -> jp + k < Zlength needle ->
  jp + 1 = start + z * p ->
  maxsuf_partial_match needle start jp k ->
  maxsuf_periodicity needle start jp k p ->
  maxsuf_optimal needle start 0 ->
  maxsuf_intermediate_optimal needle start p 0 ->
  Znth (start + k - 1) needle 0 > Znth (jp + k) needle 0 ->
  maxsuf_optimal needle (jp + 1) 0.
Proof.
  intros Hstart Hkp Hlen Hz Hpm Hper Hopt Hmid Hcmp.
  assert (Hp : 0 < p) by lia.
  assert (Hzpos : 0 < z) by nia.
  unfold maxsuf_optimal.
  intros earlier Hearlier.
  destruct (Z_lt_ge_dec earlier start) as [Hbefore | Hafter].
  - specialize (Hopt earlier ltac:(lia)).
    destruct Hopt as [d0 [Hd0 [Hstartlen [Hearlierlen [Heq [_ Hlt]]]]]].
    specialize (Hlt eq_refl).
    destruct (Z_lt_ge_dec d0 (k - 1)) as [Hearly | Hlate].
    + exists d0. repeat split; try lia.
      * intros t Ht.
        pose proof (maxsuf_match_point__factor_reset_2 needle start jp k t
          Hstart Hpm ltac:(lia)) as Hmatch.
        pose proof (Heq t Ht) as Hprefix.
        lia.
      * intros _.
        pose proof (maxsuf_match_point__factor_reset_2 needle start jp k d0
          Hstart Hpm ltac:(lia)) as Hmatch.
        lia.
    + exists (k - 1). repeat split; try lia.
      * intros t Ht.
        pose proof (maxsuf_match_point__factor_reset_2 needle start jp k t
          Hstart Hpm Ht) as Hmatch.
        pose proof (Heq t ltac:(lia)) as Hprefix.
        lia.
      * intros _.
        destruct (Z.eq_dec d0 (k - 1)) as [Hsame | Hgreater].
        -- subst d0.
           replace (jp + 1 + (k - 1)) with (jp + k) by lia.
           replace (start + (k - 1)) with (start + k - 1) in Hlt by lia.
           lia.
        -- pose proof (Heq (k - 1) ltac:(lia)) as Hprefix.
           replace (jp + 1 + (k - 1)) with (jp + k) by lia.
           replace (start + (k - 1)) with (start + k - 1) in Hprefix by lia.
           lia.
  - set (offset := earlier - start).
    set (r := offset mod p).
    set (q := offset / p).
    assert (Hr : 0 <= r < p).
    { unfold r. apply Z.mod_pos_bound. lia. }
    assert (Hdecomp : earlier = start + r + q * p).
    { unfold r, q, offset.
      pose proof (Z.div_mod (earlier - start) p ltac:(lia)). lia. }
    assert (Hq : 0 <= q < z) by nia.
    destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
    + exists (k - 1). repeat split; try lia.
      * intros t Ht.
        pose proof (maxsuf_match_point__factor_reset_2 needle start jp k t
          Hstart Hpm Ht) as Hmatch.
        pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
          (start + t) q ltac:(lia) Hper ltac:(lia) ltac:(lia) ltac:(lia))
          as Hperiod.
        replace (earlier + t) with (start + t + q * p) by lia.
        lia.
      * intros _.
        pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
          (start + k - 1) q ltac:(lia) Hper ltac:(lia) ltac:(lia)
          ltac:(lia)) as Hperiod.
        replace (earlier + (k - 1)) with
          (start + k - 1 + q * p) by lia.
        replace (jp + 1 + (k - 1)) with (jp + k) by lia.
        lia.
    + assert (Hrpos : 0 < r < p) by lia.
      specialize (Hmid (start + r) ltac:(lia)).
      destruct Hmid as [d0 [Hd0 [Hwindow [Hdbound [Heq [_ Hlt]]]]]].
      specialize (Hlt eq_refl).
      destruct (Z_lt_ge_dec d0 (k - 1)) as [Hearly | Hlate].
      * exists d0. repeat split; try lia.
        -- intros t Ht.
           pose proof (maxsuf_match_point__factor_reset_2 needle start jp k t
             Hstart Hpm ltac:(lia)) as Hmatch.
           pose proof (Heq t Ht) as Hprefix.
           pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
             (start + r + t) q ltac:(lia) Hper ltac:(lia) ltac:(lia)
             ltac:(lia)) as Hperiod.
           replace (earlier + t) with (start + r + t + q * p) by lia.
           lia.
        -- intros _.
           pose proof (maxsuf_match_point__factor_reset_2 needle start jp k d0
             Hstart Hpm ltac:(lia)) as Hmatch.
           pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
             (start + r + d0) q ltac:(lia) Hper ltac:(lia) ltac:(lia)
             ltac:(lia)) as Hperiod.
           replace (earlier + d0) with (start + r + d0 + q * p) by lia.
           lia.
      * exists (k - 1). repeat split; try lia.
        -- intros t Ht.
           pose proof (maxsuf_match_point__factor_reset_2 needle start jp k t
             Hstart Hpm Ht) as Hmatch.
           pose proof (Heq t ltac:(lia)) as Hprefix.
           pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
             (start + r + t) q ltac:(lia) Hper ltac:(lia) ltac:(lia)
             ltac:(lia)) as Hperiod.
           replace (earlier + t) with (start + r + t + q * p) by lia.
           lia.
        -- intros _.
           pose proof (maxsuf_periodicity_ext__factor_equal_1 needle start jp k p
             (start + r + k - 1) q ltac:(lia) Hper ltac:(lia) ltac:(lia)
             ltac:(lia)) as Hperiod.
           replace (earlier + (k - 1)) with
             (start + r + k - 1 + q * p) by lia.
           replace (jp + 1 + (k - 1)) with (jp + k) by lia.
           destruct (Z.eq_dec d0 (k - 1)) as [Hsame | Hgreater].
           ++ subst d0.
              replace (start + (k - 1)) with (start + k - 1) in Hlt by lia.
              replace (start + r + (k - 1)) with
                (start + r + k - 1) in Hlt by lia.
              lia.
           ++ pose proof (Heq (k - 1) ltac:(lia)) as Hprefix.
              replace (start + (k - 1)) with (start + k - 1) in Hprefix by lia.
              replace (start + r + (k - 1)) with
                (start + r + k - 1) in Hprefix by lia.
              lia.
Qed.


(* Reverse strict comparison, with the same three residue cases. *)
Lemma maxsuf_strict_extend_zero_reverse__factor_strict_1
    (needle : list Z) (jp k p z : Z) :
  0 <= jp -> 1 <= k <= p -> jp + k < Zlength needle ->
  jp + 1 = z * p ->
  maxsuf_periodicity needle 0 jp k p ->
  maxsuf_intermediate_optimal needle 0 p 0 ->
  Znth (k - 1) needle 0 < Znth (jp + k) needle 0 ->
  maxsuf_intermediate_optimal needle 0 (jp + k + 1) 0.
Proof.
  intros Hjp Hkp Hlen Hz Hper Hmid Hcmp.
  assert (Hp : 0 < p) by lia.
  assert (Hzpos : 0 < z) by nia.
  unfold maxsuf_intermediate_optimal.
  intros intermediate Hinter.
  set (r := intermediate mod p).
  set (q := intermediate / p).
  assert (Hr : 0 <= r < p).
  { unfold r. apply Z.mod_pos_bound. lia. }
  assert (Hdecomp : intermediate = r + q * p).
  { unfold r, q. pose proof (Z.div_mod intermediate p ltac:(lia)). lia. }
  assert (Hq : 0 <= q <= z) by nia.
  destruct (Z.eq_dec r 0) as [Hr0 | Hr0].
  - assert (Hqpos : 0 < q) by nia.
    exists (jp + k - intermediate).
    repeat split; try lia.
    + intros t Ht.
      replace (0 + t) with t by lia.
      replace (intermediate + t) with (t + q * p) by lia.
      eapply maxsuf_periodic_ext__factor_reset_1; eauto; lia.
    + intros _.
      replace (intermediate + (jp + k - intermediate)) with (jp + k) by lia.
      replace (0 + (jp + k - intermediate)) with
        (k - 1 + (z - q) * p) by nia.
      pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p
        (k - 1) (z - q) Hp ltac:(lia) ltac:(lia) ltac:(lia) Hper) as Heq.
      lia.
  - assert (Hrpos : 0 < r < p) by lia.
    specialize (Hmid r ltac:(lia)).
    destruct Hmid as [d0 [Hd0 [Hwindow [Hdbound [Heq [_ Hlt]]]]]].
    specialize (Hlt eq_refl).
    replace (0 + d0) with d0 in Hlt by lia.
    destruct (Z_lt_ge_dec q z) as [Hqsmall | Hqeq].
    + exists d0. repeat split; try nia.
      * intros t Ht.
        replace (0 + t) with t by lia.
        replace (intermediate + t) with (r + t + q * p) by lia.
        pose proof (Heq t Ht) as Hprefix.
        replace (0 + t) with t in Hprefix by lia.
        rewrite Hprefix.
        eapply maxsuf_periodic_ext__factor_reset_1; eauto; nia.
      * intros _.
        replace (0 + d0) with d0 by lia.
        replace (intermediate + d0) with (r + d0 + q * p) by lia.
        pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p
          (r + d0) q Hp ltac:(lia) ltac:(lia) ltac:(nia) Hper) as Hperiod.
        lia.
    + assert (Hqexact : q = z) by lia.
      assert (HrK : r < k) by nia.
      destruct (Z_lt_ge_dec d0 (k - r - 1)) as [Hearly | Hlate].
      * exists d0. repeat split; try nia.
        -- intros t Ht.
           replace (0 + t) with t by lia.
           replace (intermediate + t) with (r + t + q * p) by lia.
           pose proof (Heq t Ht) as Hprefix.
        replace (0 + t) with t in Hprefix by lia.
        rewrite Hprefix.
           eapply maxsuf_periodic_ext__factor_reset_1; eauto; nia.
        -- intros _.
           replace (0 + d0) with d0 by lia.
           replace (intermediate + d0) with (r + d0 + q * p) by lia.
           pose proof (maxsuf_periodic_ext__factor_reset_1 needle jp k p
             (r + d0) q Hp ltac:(lia) ltac:(lia) ltac:(nia) Hper) as Hperiod.
           lia.
      * exists (k - r - 1). repeat split; try nia.
        -- intros t Ht.
           replace (0 + t) with t by lia.
           replace (intermediate + t) with (r + t + q * p) by lia.
           pose proof (Heq t ltac:(lia)) as Hprefix.
           replace (0 + t) with t in Hprefix by lia.
           rewrite Hprefix.
           eapply maxsuf_periodic_ext__factor_reset_1; eauto; nia.
        -- intros _.
           replace (0 + (k - r - 1)) with (k - r - 1) by lia.
           replace (intermediate + (k - r - 1)) with (jp + k) by nia.
           destruct (Z.eq_dec d0 (k - r - 1)) as [Hsame | Hgreater].
           ++ subst d0.
              replace (r + (k - r - 1)) with (k - 1) in Hlt by lia.
              lia.
           ++ pose proof (Heq (k - r - 1) ltac:(lia)) as Hedge.
              replace (0 + (k - r - 1)) with (k - r - 1) in Hedge by lia.
              replace (r + (k - r - 1)) with (k - 1) in Hedge by lia.
              lia.
Qed.


(* General-start reverse strict transition via the needle tail. *)
Lemma maxsuf_strict_extend_reverse__factor_strict_2
    (needle : list Z) (start jp k p z : Z) :
  0 <= start <= jp -> 1 <= k <= p -> jp + k < Zlength needle ->
  jp + 1 = start + z * p ->
  maxsuf_periodicity needle start jp k p ->
  maxsuf_intermediate_optimal needle start p 0 ->
  Znth (start + k - 1) needle 0 < Znth (jp + k) needle 0 ->
  maxsuf_intermediate_optimal needle start (jp + k + 1 - start) 0.
Proof.
  intros Hstart Hkp Hlen Hz Hper Hmid Hcmp.
  set (tail := sublist start (Zlength needle) needle).
  assert (Htail_len : Zlength tail = Zlength needle - start).
  { unfold tail. rewrite Zlength_sublist; lia. }
  assert (Htail : forall t, 0 <= t < Zlength tail ->
      Znth t tail 0 = Znth (start + t) needle 0).
  { intros t Ht. unfold tail.
    rewrite (Znth_sublist 0 start t (Zlength needle) needle) by lia.
    f_equal. lia. }
  assert (Htail_per : maxsuf_periodicity tail 0 (jp - start) k p).
  { unfold maxsuf_periodicity in *.
    intros t Ht Hbound.
    rewrite !Htail by lia.
    replace (start + (t + p)) with (start + t + p) by lia.
    apply Hper; lia. }
  assert (Htail_mid : maxsuf_intermediate_optimal tail 0 p 0).
  { unfold maxsuf_intermediate_optimal in *.
    intros u Hu.
    specialize (Hmid (start + u) ltac:(lia)).
    destruct Hmid as [d [Hd [Hwindow [Hbound [Heq [Hgt Hlt]]]]]].
    exists d. repeat split; try lia.
    - intros t Ht.
      rewrite !Htail by lia.
      replace (start + (u + t)) with (start + u + t) by lia.
      apply Heq; lia.
    - intros _.
      rewrite !Htail by lia.
      replace (start + (u + d)) with (start + u + d) by lia.
      apply Hlt. reflexivity.
    }
  assert (Htail_cmp : Znth (k - 1) tail 0 <
      Znth (jp - start + k) tail 0).
  { rewrite !Htail by lia.
    replace (start + (k - 1)) with (start + k - 1) by lia.
    replace (start + (jp - start + k)) with (jp + k) by lia.
    exact Hcmp. }
  pose proof (maxsuf_strict_extend_zero_reverse__factor_strict_1 tail
    (jp - start) k p z ltac:(lia) Hkp ltac:(lia) ltac:(lia)
    Htail_per Htail_mid Htail_cmp) as Hnew.
  unfold maxsuf_intermediate_optimal in *.
  intros intermediate Hinter.
  specialize (Hnew (intermediate - start) ltac:(lia)).
  destruct Hnew as [d [Hd [Hwindow [Hbound [Heq [Hgt Hlt]]]]]].
  exists d. repeat split; try lia.
  - intros t Ht.
    specialize (Heq t Ht).
    rewrite !Htail in Heq by lia.
    replace (start + (intermediate - start + t)) with
      (intermediate + t) in Heq by lia.
    replace (start + (0 + t)) with (start + t) in Heq by lia.
    exact Heq.
  - intros _.
    specialize (Hlt eq_refl).
    rewrite !Htail in Hlt by lia.
    replace (start + (intermediate - start + d)) with
      (intermediate + d) in Hlt by lia.
    replace (start + (0 + d)) with (start + d) in Hlt by lia.
    exact Hlt.
Qed.

Lemma last_occurrence_nat_stage12 : forall (needle : list Z) (c : Z) (n : nat),
  (exists j, 0 <= j < Z.of_nat n /\ Znth j needle 0 = c) ->
  exists last, 0 <= last < Z.of_nat n /\ Znth last needle 0 = c /\
    (forall t, last < t < Z.of_nat n -> Znth t needle 0 <> c).
Proof.
  intros needle c n. induction n as [|n IH]; intros [j [Hj Heq]].
  - cbn in Hj. lia.
  - rewrite Nat2Z.inj_succ in *.
    destruct (Z.eq_dec (Znth (Z.of_nat n) needle 0) c) as [Hlast | Hlast].
    + exists (Z.of_nat n). repeat split; try lia; try assumption.
    + assert (Hjold : 0 <= j < Z.of_nat n) by
        (destruct (Z.eq_dec j (Z.of_nat n)); [subst; congruence | lia]).
      destruct (IH ltac:(eauto)) as [last [Hrange [Heq' Hlatest]]].
      exists last. repeat split; try lia; try assumption.
      intros t Ht Htc. destruct (Z.eq_dec t (Z.of_nat n)); [subst; contradiction |].
      eapply Hlatest; eauto; lia.
Qed.

Lemma shift_hit_last_stage12 : forall needle upto bits entries c,
  0 <= upto -> 0 <= c < 256 -> byteset_prefix needle upto bits ->
  shift_prefix needle upto entries ->
  Z.testbit (Znth (c / 64) bits 0) (c mod 64) = true ->
  exists last, 0 <= last < upto /\ Znth last needle 0 = c /\
    (forall t, last < t < upto -> Znth t needle 0 <> c) /\
    Znth c entries 0 = last + 1.
Proof.
  intros needle upto bits entries c Hupto Hc Hbits Hshift Hhit.
  apply (Hbits c Hc) in Hhit. destruct Hhit as [j [Hj Heq]].
  replace upto with (Z.of_nat (Z.to_nat upto)) in * by (rewrite Z2Nat.id; lia).
  destruct (last_occurrence_nat_stage12 needle c (Z.to_nat upto) ltac:(eauto))
    as [last [Hlast [Heqlast Hlatest]]].
  exists last. split; [exact Hlast|]. split; [exact Heqlast|].
  split; [exact Hlatest|]. eapply Hshift; eauto.
Qed.

Lemma terminated_nonzero_lt_stage12 : forall s j,
  0 <= j <= Zlength s -> Znth j (s ++ 0 :: nil) 0 <> 0 -> j < Zlength s.
Proof.
  intros s j Hj Hnz. destruct (Z_lt_ge_dec j (Zlength s)); [lia|].
  assert (j = Zlength s) by lia. subst j.
  rewrite app_Znth2 in Hnz by lia.
  replace (Zlength s - Zlength s) with 0 in Hnz by lia.
  simpl in Hnz. contradiction.
Qed.
