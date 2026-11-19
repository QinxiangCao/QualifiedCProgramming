Require Export SimpleC.EE.stdlib.glibc.strlen_memory.
Import StrlenLittleEndian.
Local Open Scope Z_scope.
Local Open Scope sac.

Definition sl_addr (p : Z) := p.

(** Object storage: m excludes the terminating zero. All capacity bytes
    are readable/initialized; the suffix values are existentially hidden.
    This predicate does not grant ownership outside [s,s+capacity). *)
Module ObjectString.

Definition store_string (s capacity : Z) (m : list Z) : Assertion :=
  EX tail : list Z,
    “ StrlenLittleEndian.valid_string m ” &&
    UCharArray.full s capacity (m ++ 0 :: tail).

Definition store_string_exact (s : Z) (m : list Z) : Assertion :=
  store_string s (Zlength m + 1) m.

End ObjectString.

(** Observation of all eight bytes of a loaded little-endian word. *)
Definition sl_word_matches (w : Z) (bytes : list Z) (offset : Z) : Prop :=
  forall j, 0 <= j < 8 ->
    (w / 256^j) mod 256 = Znth (offset+j) bytes 0.

Definition sl_suffix (w i : Z) : Z := w / 256^i.
Definition sl_byte (w i : Z) : Z := sl_suffix w i mod 256.
Definition sl_found (w start r : Z) : Prop :=
  start <= r <= 8 /\
  (forall i, start <= i < r -> sl_byte w i <> 0) /\
  (r < 8 -> sl_byte w r = 0).

Lemma sl_suffix_zero : forall w, sl_suffix w 0 = w.
Proof. intros; unfold sl_suffix; cbn; apply Z.div_1_r. Qed.

Lemma sl_suffix_step : forall w i, 0 <= i ->
  sl_suffix w i / 256 = sl_suffix w (i+1).
Proof.
 intros; unfold sl_suffix. rewrite Z.div_div by lia.
 rewrite Z.pow_add_r by lia. cbn. reflexivity.
Qed.

Lemma sl_suffix_range : forall w i, 0 <= w <= 18446744073709551615 ->
  0 <= i -> 0 <= sl_suffix w i <= 18446744073709551615.
Proof.
 intros; unfold sl_suffix. assert (0 < 256^i) by (apply Z.pow_pos_nonneg; lia).
 split; [apply Z.div_pos; lia|].
 apply Z.le_trans with w; [apply Z.div_le_upper_bound; nia|lia].
Qed.


(** The user's boundary examples: capacity is the allocation size. *)
Example strlen_capacity_19_length_18_rejected :
  ~ (8 * (18 / 8 + 1) <= 19).
Proof. change (~ (24 <= 19)); lia. Qed.

Example strlen_capacity_30_length_18_accepted :
  8 * (18 / 8 + 1) <= 30.
Proof. change (24 <= 30); lia. Qed.

Example strlen_unsigned_byte_255_allowed :
  StrlenLittleEndian.valid_string [255].
Proof. unfold StrlenLittleEndian.valid_string, StrlenLittleEndian.valid_char.
  constructor; [lia | constructor]. Qed.


Lemma radix_digit__object_load : forall w b lo digit hi,
  0 <= lo < b -> 0 <= digit < 256 ->
  w = b * (digit + 256 * hi) + lo ->
  (w / b) mod 256 = digit.
Proof.
  intros w b lo digit hi Hlo Hd Hw.
  assert (Hq : digit + 256 * hi = w / b).
  { apply Z.div_unique with lo; [left; exact Hlo | exact Hw]. }
  rewrite <- Hq. symmetry.
  apply Z.mod_unique with hi; [left; exact Hd | ring].
Qed.
Lemma pack_eight__object_load : forall a b c d e f g h,
  0 <= a <= 255 -> 0 <= b <= 255 -> 0 <= c <= 255 ->
  0 <= d <= 255 -> 0 <= e <= 255 -> 0 <= f <= 255 ->
  0 <= g <= 255 -> 0 <= h <= 255 ->
  let w := a+256*b+65536*c+16777216*d+4294967296*e+
           1099511627776*f+281474976710656*g+72057594037927936*h in
  0 <= w <= 18446744073709551615 /\
  forall j, 0 <= j < 8 ->
    (w / 256^j) mod 256 = Znth j [a;b;c;d;e;f;g;h] 0.
Proof.
  intros a b c d e f g h Ha Hb Hc Hd He Hf Hg Hh w.
  split; [unfold w; lia |].
  intros j Hj.
  assert (j=0 \/ j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6 \/ j=7) as Hcases by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    unfold w.
  - change ((a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h) / 1 mod 256 = a).
eapply radix_digit__object_load with (lo := 0) (hi := 1*b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h); [lia | lia | ring].
  - change ((a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h) / 256 mod 256 = b).
eapply radix_digit__object_load with (lo := 1*a) (hi := 1*c + 256*d + 65536*e + 16777216*f + 4294967296*g + 1099511627776*h); [lia | lia | ring].
  - change ((a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h) / 65536 mod 256 = c).
eapply radix_digit__object_load with (lo := 1*a + 256*b) (hi := 1*d + 256*e + 65536*f + 16777216*g + 4294967296*h); [lia | lia | ring].
  - change ((a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h) / 16777216 mod 256 = d).
eapply radix_digit__object_load with (lo := 1*a + 256*b + 65536*c) (hi := 1*e + 256*f + 65536*g + 16777216*h); [lia | lia | ring].
  - change ((a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h) / 4294967296 mod 256 = e).
eapply radix_digit__object_load with (lo := 1*a + 256*b + 65536*c + 16777216*d) (hi := 1*f + 256*g + 65536*h); [lia | lia | ring].
  - change ((a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h) / 1099511627776 mod 256 = f).
eapply radix_digit__object_load with (lo := 1*a + 256*b + 65536*c + 16777216*d + 4294967296*e) (hi := 1*g + 256*h); [lia | lia | ring].
  - change ((a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h) / 281474976710656 mod 256 = g).
eapply radix_digit__object_load with (lo := 1*a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f) (hi := 1*h); [lia | lia | ring].
  - change ((a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h) / 72057594037927936 mod 256 = h).
eapply radix_digit__object_load with (lo := 1*a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g) (hi := 0); [lia | lia | ring].
Qed.
Lemma extract_eight__object_load : forall s o l, (s+o) mod 8 = 0 -> UCharArray.seg s o (o+8) l |-- EX w : Z, “ 0 <= w <= 18446744073709551615 ” && “ forall j, 0 <= j < 8 -> (w / 256^j) mod 256 = Znth j l 0 ” && ((s+o) # UInt64 |-> w).
Proof.
intros s o l Halign.
prop_apply (UCharArray.seg_Zlength s o (o+8) l).
Intros_p Hlen.
destruct l as [|a l]; [rewrite Zlength_nil in Hlen; lia|].
destruct l as [|b l]; [rewrite Zlength_cons, Zlength_nil in Hlen; lia|].
destruct l as [|c l]; [rewrite !Zlength_cons, Zlength_nil in Hlen; lia|].
destruct l as [|d l]; [rewrite !Zlength_cons, Zlength_nil in Hlen; lia|].
destruct l as [|e l]; [rewrite !Zlength_cons, Zlength_nil in Hlen; lia|].
destruct l as [|f l]; [rewrite !Zlength_cons, Zlength_nil in Hlen; lia|].
destruct l as [|g l]; [rewrite !Zlength_cons, Zlength_nil in Hlen; lia|].
destruct l as [|h l]; [rewrite !Zlength_cons, Zlength_nil in Hlen; lia|].
assert (l = []) by (apply Zlength_nil_inv; rewrite !Zlength_cons in Hlen; lia).
subst l.
unfold UCharArray.seg.
cbn [store_array_rec StoreUCharAsElement.storeA].
rewrite !sizeof_uchar, !Z.mul_1_r.
replace (s + (o + 1)) with (s+o+1) by lia.
replace (s + (o + 1 + 1)) with (s+o+2) by lia.
replace (s + (o + 1 + 1 + 1)) with (s+o+3) by lia.
replace (s + (o + 1 + 1 + 1 + 1)) with (s+o+4) by lia.
replace (s + (o + 1 + 1 + 1 + 1 + 1)) with (s+o+5) by lia.
replace (s + (o + 1 + 1 + 1 + 1 + 1 + 1)) with (s+o+6) by lia.
replace (s + (o + 1 + 1 + 1 + 1 + 1 + 1 + 1)) with (s+o+7) by lia.
Intros.
prop_apply_p (store_uchar_range (s+o) a).
Intros_p Ha.
prop_apply_p (store_uchar_range (s+o+1) b).
Intros_p Hb.
prop_apply_p (store_uchar_range (s+o+2) c).
Intros_p Hc.
prop_apply_p (store_uchar_range (s+o+3) d).
Intros_p Hd.
prop_apply_p (store_uchar_range (s+o+4) e).
Intros_p He.
prop_apply_p (store_uchar_range (s+o+5) f).
Intros_p Hf.
prop_apply_p (store_uchar_range (s+o+6) g).
Intros_p Hg.
prop_apply_p (store_uchar_range (s+o+7) h).
Intros_p Hh.
pose proof (pack_eight__object_load a b c d e f g h Ha Hb Hc Hd He Hf Hg Hh) as [Hw Hbytes].
Exists (a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h).
split_pure_spatial.
- rewrite store_uint64_store_uchar.
Exists a b c d e f g h.
split_pure_spatial; [cancel |].
split_pures.
+ dump_pre_spatial.
unfold merge_n_bytes.
change ((a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h) mod 18446744073709551616 = a mod 256 + 256*(b mod 256 + 256*(c mod 256 + 256*(d mod 256 + 256*(e mod 256 + 256*(f mod 256 + 256*(g mod 256 + 256*(h mod 256 + 256*0)))))))).
change Byte.max_unsigned with 255 in *.
rewrite !Z.mod_small by lia.
ring.
+ dump_pre_spatial.
exact Hw.
+ dump_pre_spatial.
unfold aligned_4, aligned, Arch.aligned.
apply Z.mod_divide in Halign; [|lia].
destruct Halign as [q Hq].
apply Z.mod_divide; [lia | exists (2*q); lia].
- split_pures; dump_pre_spatial; assumption.
Qed.
Lemma restore_eight__object_load : forall s o w l, Zlength l = 8 -> (forall j, 0 <= j < 8 -> (w/256^j) mod 256 = Znth j l 0) -> ((s+o) # UInt64 |-> w) |-- UCharArray.seg s o (o+8) l.
Proof.
intros s o w l Hlen Hmatch.
rewrite store_uint64_store_uchar.
Intros a b c d e f g h.
rename H into Hmerge.
rename H0 into Hw.
rename H1 into Halign.
prop_apply_p (store_uchar_range (s+o) a).
Intros_p Ha.
prop_apply_p (store_uchar_range (s+o+1) b).
Intros_p Hb.
prop_apply_p (store_uchar_range (s+o+2) c).
Intros_p Hc.
prop_apply_p (store_uchar_range (s+o+3) d).
Intros_p Hd.
prop_apply_p (store_uchar_range (s+o+4) e).
Intros_p He.
prop_apply_p (store_uchar_range (s+o+5) f).
Intros_p Hf.
prop_apply_p (store_uchar_range (s+o+6) g).
Intros_p Hg.
prop_apply_p (store_uchar_range (s+o+7) h).
Intros_p Hh.
change Byte.max_unsigned with 255 in *.
change Int64.max_unsigned with 18446744073709551615 in Hw.
change (w mod 18446744073709551616 = a mod 256 + 256*(b mod 256 + 256*(c mod 256 + 256*(d mod 256 + 256*(e mod 256 + 256*(f mod 256 + 256*(g mod 256 + 256*(h mod 256 + 256*0)))))))) in Hmerge.
rewrite !Z.mod_small in Hmerge by lia.
assert (Ew : w = a+256*b+65536*c+16777216*d+4294967296*e+1099511627776*f+281474976710656*g+72057594037927936*h) by lia.
pose proof (pack_eight__object_load a b c d e f g h Ha Hb Hc Hd He Hf Hg Hh) as [Hrange Hdigits].
assert (El : l = [a;b;c;d;e;f;g;h]).
{ apply (proj2 (list_eq_ext l [a;b;c;d;e;f;g;h] 0)).
split; [rewrite Hlen; reflexivity|].
intros j Hj.
rewrite Hlen in Hj.
rewrite <- (Hmatch j Hj), Ew.
apply Hdigits; exact Hj.
} rewrite El.
unfold UCharArray.seg.
cbn [store_array_rec StoreUCharAsElement.storeA].
rewrite !sizeof_uchar, !Z.mul_1_r.
replace (s + (o + 1)) with (s+o+1) by lia.
replace (s + (o + 1 + 1)) with (s+o+2) by lia.
replace (s + (o + 1 + 1 + 1)) with (s+o+3) by lia.
replace (s + (o + 1 + 1 + 1 + 1)) with (s+o+4) by lia.
replace (s + (o + 1 + 1 + 1 + 1 + 1)) with (s+o+5) by lia.
replace (s + (o + 1 + 1 + 1 + 1 + 1 + 1)) with (s+o+6) by lia.
replace (s + (o + 1 + 1 + 1 + 1 + 1 + 1 + 1)) with (s+o+7) by lia.
split_pure_spatial.
- cancel.
- split_pures; dump_pre_spatial; auto; lia.
Qed.
Lemma rounded_capacity__outer_loop : forall n c, 0 <= n ->
  8 * (Z.quot n 8 + 1) <= c -> 8 <= c /\ n < c.
Proof.
 intros n c Hn Hc. rewrite Z.quot_div_nonneg in Hc by lia.
 pose proof (Z.div_pos n 8 Hn ltac:(lia)).
 pose proof (Z.div_mod n 8 ltac:(lia)).
 pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia.
Qed.
Lemma aligned_last_word_bound__outer_loop : forall s p n c,
  0 <= n -> s mod 8 = 0 -> p mod 8 = 0 -> s <= p <= s+n ->
  8 * (Z.quot n 8 + 1) <= c -> p+8 <= s+c.
Proof.
 intros s p n c Hn Hs Hp Hb Hc.
 rewrite Z.quot_div_nonneg in Hc by lia.
 pose proof (Z.div_mod s 8 ltac:(lia)).
 pose proof (Z.div_mod p 8 ltac:(lia)).
 pose proof (Z.div_mod n 8 ltac:(lia)).
 pose proof (Z.mod_pos_bound n 8 ltac:(lia)). nia.
Qed.
Lemma no_zero_word_step__outer_loop : forall m tail w o r,
  0 <= o <= Zlength m -> sl_word_matches w (m ++ 0::tail) o ->
  sl_found w 0 r -> r >= 8 -> o+8 <= Zlength m.
Proof.
 intros m tail w o r Ho Hmatch [Hr [Hnz Hz]] Hge.
 destruct (Z_le_gt_dec (o+8) (Zlength m)); [assumption|].
 specialize (Hmatch (Zlength m-o) ltac:(lia)).
 specialize (Hnz (Zlength m-o) ltac:(lia)).
 unfold sl_byte, sl_suffix in Hnz.
 replace (o+(Zlength m-o)) with (Zlength m) in Hmatch by lia.
 rewrite app_Znth2 in Hmatch by lia.
 rewrite Z.sub_diag, Znth0_cons in Hmatch.
 contradiction.
Qed.
Lemma first_zero_is_string_end__result_specs : forall m tail o w r,
  valid_string m -> 0 <= o <= Zlength m ->
  sl_word_matches w (m ++ 0 :: tail) o -> sl_found w 0 r ->
  r < 8 -> o+r = Zlength m.
Proof.
  intros m tail o w r Hv Ho Hmatch [Hr [Hbefore Hzero]] Hlt.
  unfold sl_byte, sl_suffix in Hbefore, Hzero.
  destruct (Z_lt_ge_dec (o+r) (Zlength m)) as [Hless|Hge].
  - specialize (Hzero Hlt).
    rewrite (Hmatch r ltac:(lia)) in Hzero.
    unfold Znth in Hzero.
    rewrite app_nth1 in Hzero by (rewrite Zlength_correct in Hless; lia).
    unfold valid_string in Hv. rewrite Forall_forall in Hv.
    pose proof (Hv (nth (Z.to_nat (o+r)) m 0)) as Hchar.
    assert (Hin : List.In (nth (Z.to_nat (o+r)) m 0) m).
    { apply nth_In. rewrite Zlength_correct in Hless. lia. }
    specialize (Hchar Hin). unfold valid_char in Hchar. lia.
  - destruct (Z.eq_dec (o+r) (Zlength m)); auto.
    specialize (Hbefore (Zlength m-o) ltac:(lia)).
    rewrite (Hmatch (Zlength m-o) ltac:(lia)) in Hbefore.
    replace (o+(Zlength m-o)) with (Zlength m) in Hbefore by lia.
    unfold Znth in Hbefore. rewrite Zlength_correct, Nat2Z.id in Hbefore.
    rewrite app_nth2 in Hbefore by lia.
    rewrite Nat.sub_diag in Hbefore. simpl in Hbefore. contradiction.
Qed.
