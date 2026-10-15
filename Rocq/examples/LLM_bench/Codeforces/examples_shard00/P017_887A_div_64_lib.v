Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ChosenBinaryDigits (s : list Z) (indices digits : list Z) : Prop :=
  0 < Zlength indices /\
  Forall2
    (fun index digit =>
      0 <= index < Zlength s /\ digit = Znth index s 0)
    indices digits /\
  mono_inc indices.

Definition BinaryValue (digits : list Z) : Z :=
  fold_left (fun value character => 2 * value + (character - 48)) digits 0.

Definition Pre (s : list Z) : Prop :=
  1 <= Zlength s <= 100 /\
  (* Character codes: '0' = 48, '1' = 49. *)
  Forall (fun character => character = 48 \/ character = 49) s.

Definition Spec (s : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> exists indices digits,
    ChosenBinaryDigits s indices digits /\
    BinaryValue digits > 0 /\
    (64 | BinaryValue digits)).

Definition PrefixScan (prefix : list Z) (seen_one zeros : Z) : Prop :=
  (seen_one = 0 /\ zeros = 0 /\ ~ In 49 prefix) \/
  (seen_one = 1 /\ exists before after,
    prefix = before ++ 49 :: after /\
    ~ In 49 before /\
    zeros = Z.of_nat (count_occ Z.eq_dec after 48)).

Require Import Coq.micromega.Lia.
Lemma terminator_nonzero_index__prefix_scan_transitions :
  forall (text : list Z) i,
    0 <= i <= Zlength text ->
    Znth i (text ++ (0 :: nil)) 0 <> 0 ->
    i < Zlength text /\
    Znth i (text ++ (0 :: nil)) 0 = Znth i text 0.
Proof.
  intros text i [Hlo Hle] Hnonzero.
  assert (Hi : i < Zlength text).
  {
    destruct (Z.eq_dec i (Zlength text)) as [Heq | Hneq].
    - subst i.
      exfalso.
      apply Hnonzero.
      rewrite app_Znth2 by lia.
      rewrite Z.sub_diag.
      reflexivity.
    - lia.
  }
  split; [exact Hi |].
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.
Lemma sublist_snoc_at_index__prefix_scan_transitions :
  forall (text : list Z) i,
    0 <= i < Zlength text ->
    sublist 0 (i + 1) text = sublist 0 i text ++ (Znth i text 0 :: nil).
Proof.
  intros text i Hi.
  rewrite (sublist_split 0 (i + 1) i text) by lia.
  rewrite (@sublist_single Z 0 i text) by lia.
  reflexivity.
Qed.
Lemma prefix_scan_append_one__prefix_scan_transitions :
  forall (text : list Z) i seen_one zeros,
    0 <= i < Zlength text ->
    Znth i text 0 = 49 ->
    PrefixScan (sublist 0 i text) seen_one zeros ->
    PrefixScan (sublist 0 (i + 1) text) 1 zeros.
Proof.
  intros text i seen_one zeros Hi Hchar Hscan.
  rewrite sublist_snoc_at_index__prefix_scan_transitions by exact Hi.
  rewrite Hchar.
  unfold PrefixScan in Hscan |- *.
  destruct Hscan as [[Hseen [Hzero Hno]] |
                     [Hseen [before [after [Heq [Hno Hzeros]]]]]].
  - right.
    split; [reflexivity |].
    exists (sublist 0 i text), nil.
    simpl.
    repeat split; try assumption; lia.
  - right.
    split; [reflexivity |].
    exists before, (after ++ (49 :: nil)).
    split.
    + rewrite Heq.
      rewrite <- app_assoc.
      reflexivity.
    + split; [exact Hno |].
      rewrite count_occ_app.
      simpl.
      destruct (Z.eq_dec 49 48); lia.
Qed.
Lemma prefix_scan_append_zero_seen__prefix_scan_transitions :
  forall (text : list Z) i zeros,
    0 <= i < Zlength text ->
    Znth i text 0 = 48 ->
    PrefixScan (sublist 0 i text) 1 zeros ->
    PrefixScan (sublist 0 (i + 1) text) 1 (zeros + 1).
Proof.
  intros text i zeros Hi Hchar Hscan.
  rewrite sublist_snoc_at_index__prefix_scan_transitions by exact Hi.
  rewrite Hchar.
  unfold PrefixScan in Hscan |- *.
  destruct Hscan as [[Hseen _] |
                     [Hseen [before [after [Heq [Hno Hzeros]]]]]].
  - lia.
  - right.
    split; [reflexivity |].
    exists before, (after ++ (48 :: nil)).
    split.
    + rewrite Heq.
      rewrite <- app_assoc.
      reflexivity.
    + split; [exact Hno |].
      rewrite count_occ_app.
      simpl.
      destruct (Z.eq_dec 48 48); [| contradiction].
      rewrite Nat2Z.inj_add.
      simpl.
      lia.
Qed.
Lemma prefix_scan_append_zero_unseen__prefix_scan_transitions :
  forall (text : list Z) i zeros,
    0 <= i < Zlength text ->
    Znth i text 0 = 48 ->
    PrefixScan (sublist 0 i text) 0 zeros ->
    PrefixScan (sublist 0 (i + 1) text) 0 zeros.
Proof.
  intros text i zeros Hi Hchar Hscan.
  rewrite sublist_snoc_at_index__prefix_scan_transitions by exact Hi.
  rewrite Hchar.
  unfold PrefixScan in Hscan |- *.
  destruct Hscan as [[Hseen [Hzero Hno]] |
                     [Hseen [before [after [Heq [Hno Hzeros]]]]]].
  - left.
    repeat split; try assumption.
    intro Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply Hno. exact Hin.
    + simpl in Hin. lia.
  - lia.
Qed.
Lemma terminator_full_prefix__final_spec :
  forall (text : list Z) i,
    0 <= i <= Zlength text ->
    (forall j, 0 <= j < Zlength text ->
      Znth j text 0 = 48 \/ Znth j text 0 = 49) ->
    Znth i (text ++ 0 :: nil) 0 = 0 ->
    i = Zlength text /\ sublist 0 i text = text.
Proof.
  intros text i Hib Hchars Hzero.
  assert (i = Zlength text) as ->.
  { destruct (Z_lt_ge_dec i (Zlength text)) as [Hlt | Hge]; [|lia].
    assert (Znth i (text ++ 0 :: nil) 0 = Znth i text 0) as Happ.
    { unfold Znth.
      rewrite app_nth1; [reflexivity|].
      rewrite Zlength_correct in Hlt. lia. }
    specialize (Hchars i ltac:(lia)).
    rewrite Happ in Hzero.
    destruct Hchars; lia. }
  split; [reflexivity|].
  unfold sublist.
  rewrite Zlength_correct, Nat2Z.id, firstn_all.
  reflexivity.
Qed.
Lemma binary_value_snoc__final_spec :
  forall digits digit,
    BinaryValue (digits ++ digit :: nil) =
    2 * BinaryValue digits + (digit - 48).
Proof.
  intros digits digit.
  unfold BinaryValue.
  rewrite fold_left_app.
  reflexivity.
Qed.
Lemma list_last_decompose__final_spec :
  forall (A : Type) (l : list A),
    l <> nil -> exists prefix last, l = prefix ++ last :: nil.
Proof.
  intros A l.
  induction l as [|x l IH]; intros Hne.
  - contradiction.
  - destruct l as [|y l].
    + exists nil, x. reflexivity.
    + assert (y :: l <> nil) by discriminate.
      destruct (IH H) as (prefix & last & Heq).
      exists (x :: prefix), last.
      simpl. now rewrite Heq.
Qed.
Lemma binary_value_all_zero__final_spec :
  forall digits,
    Forall (fun digit => digit = 48) digits ->
    BinaryValue digits = 0.
Proof.
  intros digits Hdigits.
  induction Hdigits as [|digit digits Hdigit Hdigits IH].
  - reflexivity.
  - subst digit. simpl in *. exact IH.
Qed.
Lemma binary_positive_contains_one__final_spec :
  forall digits,
    Forall (fun digit => digit = 48 \/ digit = 49) digits ->
    BinaryValue digits > 0 ->
    In 49 digits.
Proof.
  intros digits Hbits Hpositive.
  destruct (in_dec Z.eq_dec 49 digits) as [Hin | Hnot]; [exact Hin|].
  assert (Forall (fun digit => digit = 48) digits) as Hzeros.
  { rewrite Forall_forall in Hbits |- *.
    intros digit Hin.
    specialize (Hbits digit Hin).
    destruct Hbits as [Hzero | Hone]; [exact Hzero|].
    exfalso. apply Hnot. subst digit. exact Hin. }
  pose proof (binary_value_all_zero__final_spec digits Hzeros).
  lia.
Qed.
Lemma binary_divisible64_has_six_zero_suffix__final_spec :
  forall digits,
    Forall (fun digit => digit = 48 \/ digit = 49) digits ->
    BinaryValue digits > 0 ->
    (64 | BinaryValue digits) ->
    exists prefix,
      digits = prefix ++ 48 :: 48 :: 48 :: 48 :: 48 :: 48 :: nil /\
      BinaryValue prefix > 0.
Proof.
  intros digits Hbits Hpositive [q Hvalue].
  assert (0 < q) by lia.
  assert (digits <> nil) as Hne1.
  { intros ->. unfold BinaryValue in Hpositive. simpl in Hpositive. lia. }
  destruct (list_last_decompose__final_spec _ digits Hne1)
    as (d1 & x1 & Hd1). subst digits.
  rewrite Forall_app in Hbits. destruct Hbits as [Hbits1 Hlast1].
  rewrite Forall_forall in Hlast1.
  specialize (Hlast1 x1 ltac:(simpl; auto)).
  rewrite binary_value_snoc__final_spec in Hvalue.
  destruct Hlast1 as [-> | ->]; [|lia].
  assert (BinaryValue d1 = 32 * q) as Hv1 by lia.
  assert (BinaryValue d1 > 0) as Hp1 by lia.
  assert (d1 <> nil) as Hne2.
  { intros ->. unfold BinaryValue in Hp1. simpl in Hp1. lia. }
  destruct (list_last_decompose__final_spec _ d1 Hne2)
    as (d2 & x2 & Hd2). subst d1.
  rewrite Forall_app in Hbits1. destruct Hbits1 as [Hbits2 Hlast2].
  rewrite Forall_forall in Hlast2.
  specialize (Hlast2 x2 ltac:(simpl; auto)).
  rewrite binary_value_snoc__final_spec in Hv1.
  destruct Hlast2 as [-> | ->]; [|lia].
  assert (BinaryValue d2 = 16 * q) as Hv2 by lia.
  assert (BinaryValue d2 > 0) as Hp2 by lia.
  assert (d2 <> nil) as Hne3.
  { intros ->. unfold BinaryValue in Hp2. simpl in Hp2. lia. }
  destruct (list_last_decompose__final_spec _ d2 Hne3)
    as (d3 & x3 & Hd3). subst d2.
  rewrite Forall_app in Hbits2. destruct Hbits2 as [Hbits3 Hlast3].
  rewrite Forall_forall in Hlast3.
  specialize (Hlast3 x3 ltac:(simpl; auto)).
  rewrite binary_value_snoc__final_spec in Hv2.
  destruct Hlast3 as [-> | ->]; [|lia].
  assert (BinaryValue d3 = 8 * q) as Hv3 by lia.
  assert (BinaryValue d3 > 0) as Hp3 by lia.
  assert (d3 <> nil) as Hne4.
  { intros ->. unfold BinaryValue in Hp3. simpl in Hp3. lia. }
  destruct (list_last_decompose__final_spec _ d3 Hne4)
    as (d4 & x4 & Hd4). subst d3.
  rewrite Forall_app in Hbits3. destruct Hbits3 as [Hbits4 Hlast4].
  rewrite Forall_forall in Hlast4.
  specialize (Hlast4 x4 ltac:(simpl; auto)).
  rewrite binary_value_snoc__final_spec in Hv3.
  destruct Hlast4 as [-> | ->]; [|lia].
  assert (BinaryValue d4 = 4 * q) as Hv4 by lia.
  assert (BinaryValue d4 > 0) as Hp4 by lia.
  assert (d4 <> nil) as Hne5.
  { intros ->. unfold BinaryValue in Hp4. simpl in Hp4. lia. }
  destruct (list_last_decompose__final_spec _ d4 Hne5)
    as (d5 & x5 & Hd5). subst d4.
  rewrite Forall_app in Hbits4. destruct Hbits4 as [Hbits5 Hlast5].
  rewrite Forall_forall in Hlast5.
  specialize (Hlast5 x5 ltac:(simpl; auto)).
  rewrite binary_value_snoc__final_spec in Hv4.
  destruct Hlast5 as [-> | ->]; [|lia].
  assert (BinaryValue d5 = 2 * q) as Hv5 by lia.
  assert (BinaryValue d5 > 0) as Hp5 by lia.
  assert (d5 <> nil) as Hne6.
  { intros ->. unfold BinaryValue in Hp5. simpl in Hp5. lia. }
  destruct (list_last_decompose__final_spec _ d5 Hne6)
    as (d6 & x6 & Hd6). subst d5.
  rewrite Forall_app in Hbits5. destruct Hbits5 as [Hbits6 Hlast6].
  rewrite Forall_forall in Hlast6.
  specialize (Hlast6 x6 ltac:(simpl; auto)).
  rewrite binary_value_snoc__final_spec in Hv5.
  destruct Hlast6 as [-> | ->]; [|lia].
  exists d6.
  split; [repeat rewrite <- app_assoc; reflexivity|lia].
Qed.
Lemma chosen_digits_are_bits__final_spec :
  forall text indices digits,
    (forall j, 0 <= j < Zlength text ->
      Znth j text 0 = 48 \/ Znth j text 0 = 49) ->
    Forall2
      (fun index digit =>
        0 <= index < Zlength text /\ digit = Znth index text 0)
      indices digits ->
    Forall (fun digit => digit = 48 \/ digit = 49) digits.
Proof.
  intros text indices digits Hchars Hmap.
  induction Hmap as [|index digit indices digits Hhead Htail IH].
  - constructor.
  - destruct Hhead as [Hbounds ->].
    constructor; [apply Hchars; exact Hbounds|exact IH].
Qed.
Lemma mono_inc_map_add_one__final_spec :
  forall indices,
    mono_inc indices ->
    mono_inc (map (fun index => index + 1) indices).
Proof.
  intros indices.
  induction indices as [|index indices IH]; intros Hmono.
  - apply mono_inc_nil.
  - apply mono_inc_cons in Hmono as [Hall Htail].
    simpl. apply mono_inc_cons. split.
    + rewrite Forall_map. revert Hall. apply Forall_impl.
      intros other Hlt. lia.
    + apply IH. exact Htail.
Qed.
Lemma mono_inc_map_sub_one__final_spec :
  forall indices,
    mono_inc indices ->
    mono_inc (map (fun index => index - 1) indices).
Proof.
  intros indices.
  induction indices as [|index indices IH]; intros Hmono.
  - apply mono_inc_nil.
  - apply mono_inc_cons in Hmono as [Hall Htail].
    simpl. apply mono_inc_cons. split.
    + rewrite Forall_map. revert Hall. apply Forall_impl.
      intros other Hlt. lia.
    + apply IH. exact Htail.
Qed.
Lemma indexed_mapping_indices_nonnegative__final_spec :
  forall text indices digits,
    Forall2
      (fun index digit =>
        0 <= index < Zlength text /\ digit = Znth index text 0)
      indices digits ->
    Forall (fun index => 0 <= index) indices.
Proof.
  intros text indices digits Hmap.
  induction Hmap as [|index digit indices digits Hhead Htail IH].
  - constructor.
  - constructor; [destruct Hhead; lia|exact IH].
Qed.
Lemma indexed_mapping_lift_source__final_spec :
  forall head text indices digits,
    Forall2
      (fun index digit =>
        0 <= index < Zlength text /\ digit = Znth index text 0)
      indices digits ->
    Forall2
      (fun index digit =>
        0 <= index < Zlength (head :: text) /\
        digit = Znth index (head :: text) 0)
      (map (fun index => index + 1) indices) digits.
Proof.
  intros head text indices digits Hmap.
  induction Hmap as [|index digit indices digits Hhead Htail IH].
  - constructor.
  - simpl. constructor; [|exact IH].
    destruct Hhead as [Hbounds Hdigit]. split.
    + rewrite Zlength_cons. lia.
    + rewrite Znth_cons by lia.
      replace (index + 1 - 1) with index by lia.
      exact Hdigit.
Qed.
Lemma indexed_mapping_shift_source__final_spec :
  forall head text indices digits,
    Forall (fun index => 0 < index) indices ->
    Forall2
      (fun index digit =>
        0 <= index < Zlength (head :: text) /\
        digit = Znth index (head :: text) 0)
      indices digits ->
    Forall2
      (fun index digit =>
        0 <= index < Zlength text /\ digit = Znth index text 0)
      (map (fun index => index - 1) indices) digits.
Proof.
  intros head text indices digits Hpositive Hmap.
  revert Hpositive.
  induction Hmap as [|index digit indices digits Hhead Htail IH];
    intros Hpositive.
  - constructor.
  - inversion Hpositive as [|? ? Hindex Hindices]; subst.
    simpl. constructor; [|apply IH; exact Hindices].
    destruct Hhead as [Hbounds Hdigit]. split.
    + rewrite Zlength_cons in Hbounds. lia.
    + rewrite Znth_cons in Hdigit by lia. exact Hdigit.
Qed.
Lemma indexed_mapping_count_occ_le__final_spec :
  forall text indices digits value,
    Forall2
      (fun index digit =>
        0 <= index < Zlength text /\ digit = Znth index text 0)
      indices digits ->
    mono_inc indices ->
    (count_occ Z.eq_dec digits value <=
      count_occ Z.eq_dec text value)%nat.
Proof.
  intros text.
  induction text as [|head text IH]; intros indices digits value Hmap Hmono.
  - inversion Hmap as [|index digit indices_tail digits_tail Hhead Htail]; subst.
    + simpl. lia.
    + destruct Hhead as [Hbounds _]. rewrite Zlength_nil in Hbounds. lia.
  - inversion Hmap as [|index digit indices_tail digits_tail Hhead Htail]; subst.
    + simpl. lia.
    + pose proof Hmono as Hmono_all.
      apply mono_inc_cons in Hmono as [Hgreater Hmono_tail].
      destruct Hhead as [Hbounds Hdigit].
      destruct (Z.eq_dec index 0) as [-> | Hindex].
      * rewrite Znth0_cons in Hdigit. subst digit.
        assert (Forall (fun other => 0 < other) indices_tail) as Hpositive.
        { revert Hgreater. apply Forall_impl. intros other Hlt. lia. }
        pose proof (indexed_mapping_shift_source__final_spec
          head text indices_tail digits_tail Hpositive Htail) as Hshifted.
        pose proof (IH (map (fun other => other - 1) indices_tail) digits_tail value
          Hshifted (mono_inc_map_sub_one__final_spec indices_tail Hmono_tail)) as Hcount.
        simpl. destruct (Z.eq_dec head value); lia.
      * assert (0 < index) by lia.
        assert (Forall (fun other => 0 < other) (index :: indices_tail))
          as Hpositive.
        { constructor; [lia|].
          revert Hgreater. apply Forall_impl. intros other Hlt. lia. }
        assert (Forall2
          (fun source_index source_digit =>
            0 <= source_index < Zlength (head :: text) /\
            source_digit = Znth source_index (head :: text) 0)
          (index :: indices_tail) (digit :: digits_tail)) as Hmap_all.
        { constructor; [split; assumption|exact Htail]. }
        pose proof (indexed_mapping_shift_source__final_spec
          head text (index :: indices_tail) (digit :: digits_tail)
          Hpositive Hmap_all) as Hshifted.
        pose proof (IH
          (map (fun other => other - 1) (index :: indices_tail))
          (digit :: digits_tail) value Hshifted
          (mono_inc_map_sub_one__final_spec _ Hmono_all)) as Hcount.
        eapply Nat.le_trans; [exact Hcount|].
        simpl. destruct (Z.eq_dec head value); lia.
Qed.
Lemma indexed_mapping_after_first__final_spec :
  forall before after indices selected,
    ~ In 49 before ->
    Forall2
      (fun index digit =>
        0 <= index < Zlength (before ++ 49 :: after) /\
        digit = Znth index (before ++ 49 :: after) 0)
      indices (49 :: selected) ->
    mono_inc indices ->
    exists selected_indices,
      Forall2
        (fun index digit =>
          0 <= index < Zlength after /\ digit = Znth index after 0)
        selected_indices selected /\
      mono_inc selected_indices.
Proof.
  intros before.
  induction before as [|head before IH];
    intros after indices selected Hnot Hmap Hmono.
  - simpl in Hmap.
    inversion Hmap as [|index digit indices_tail selected_tail Hhead Htail];
      subst indices digit selected_tail.
    pose proof Hmono as Hmono_all.
    apply mono_inc_cons in Hmono as [Hgreater Hmono_tail].
    destruct Hhead as [Hbounds Hdigit].
    destruct (Z.eq_dec index 0) as [-> | Hindex].
    + assert (Forall (fun other => 0 < other) indices_tail) as Hpositive.
      { revert Hgreater. apply Forall_impl. intros other Hlt. lia. }
      exists (map (fun other => other - 1) indices_tail). split.
      * eapply indexed_mapping_shift_source__final_spec; eauto.
      * apply mono_inc_map_sub_one__final_spec. exact Hmono_tail.
    + assert (Forall (fun other => 0 < other) (index :: indices_tail))
        as Hpositive.
      { constructor; [lia|].
        revert Hgreater. apply Forall_impl. intros other Hlt. lia. }
      assert (Forall2
        (fun source_index source_digit =>
          0 <= source_index < Zlength (49 :: after) /\
          source_digit = Znth source_index (49 :: after) 0)
        (index :: indices_tail) (49 :: selected)) as Hmap_all.
      { constructor; [split; assumption|exact Htail]. }
      pose proof (indexed_mapping_shift_source__final_spec
        49 after _ _ Hpositive Hmap_all) as Hshifted.
      pose proof (mono_inc_map_sub_one__final_spec _ Hmono_all) as Hshiftmono.
      inversion Hshifted as
        [|shifted_index shifted_digit shifted_indices shifted_digits
          Hshift_head Hshift_tail];
        subst shifted_index shifted_digit shifted_indices shifted_digits.
      apply mono_inc_cons in Hshiftmono as [_ Hshiftmono_tail].
      exists (map (fun other => other - 1) indices_tail). split.
      * exact Hshift_tail.
      * exact Hshiftmono_tail.
  - simpl in Hnot, Hmap.
    assert (head <> 49) as Hhead_not.
    { intros ->. apply Hnot. left. reflexivity. }
    assert (~ In 49 before) as Hbefore_not.
    { intros Hin. apply Hnot. right. exact Hin. }
    inversion Hmap as [|index digit indices_tail selected_tail Hfirst Htail];
      subst indices digit selected_tail.
    pose proof Hmono as Hmono_all.
    apply mono_inc_cons in Hmono as [Hgreater _].
    destruct Hfirst as [Hbounds Hdigit].
    assert (0 < index) as Hindex.
    { destruct (Z.eq_dec index 0) as [-> | Hne]; [|lia].
      rewrite Znth0_cons in Hdigit.
      exfalso. apply Hhead_not. symmetry. exact Hdigit. }
    assert (Forall (fun other => 0 < other) (index :: indices_tail))
      as Hpositive.
    { constructor; [exact Hindex|].
      revert Hgreater. apply Forall_impl. intros other Hlt. lia. }
    assert (Forall2
      (fun source_index source_digit =>
        0 <= source_index < Zlength (head :: before ++ 49 :: after) /\
        source_digit = Znth source_index (head :: before ++ 49 :: after) 0)
      (index :: indices_tail) (49 :: selected)) as Hmap_all.
    { constructor; [split; assumption|exact Htail]. }
    pose proof (indexed_mapping_shift_source__final_spec
      head (before ++ 49 :: after) _ _ Hpositive Hmap_all) as Hshifted.
    eapply IH; eauto using mono_inc_map_sub_one__final_spec.
Qed.
Lemma indexed_mapping_repeat_from_count__final_spec :
  forall text value n,
    (n <= count_occ Z.eq_dec text value)%nat ->
    exists indices,
      Forall2
        (fun index digit =>
          0 <= index < Zlength text /\ digit = Znth index text 0)
        indices (repeat value n) /\
      mono_inc indices.
Proof.
  intros text.
  induction text as [|head text IH]; intros value n Hcount.
  - destruct n as [|n].
    + exists nil. split; [constructor|apply mono_inc_nil].
    + simpl in Hcount. lia.
  - destruct n as [|n].
    + exists nil. split; [constructor|apply mono_inc_nil].
    + destruct (Z.eq_dec head value) as [-> | Hneq].
      * assert ((n <= count_occ Z.eq_dec text value)%nat) as Htail_count.
        { simpl in Hcount. destruct (Z.eq_dec value value); [lia|contradiction]. }
        destruct (IH value n Htail_count) as (indices & Hmap & Hmono).
        exists (0 :: map (fun index => index + 1) indices). split.
        -- simpl. constructor.
           ++ split.
              ** rewrite Zlength_cons. pose proof (Zlength_nonneg text). lia.
              ** rewrite Znth0_cons. reflexivity.
           ++ apply indexed_mapping_lift_source__final_spec. exact Hmap.
        -- apply mono_inc_cons. split.
           ++ rewrite Forall_map.
              pose proof (indexed_mapping_indices_nonnegative__final_spec
                text indices (repeat value n) Hmap) as Hnonnegative.
              revert Hnonnegative. apply Forall_impl.
              intros index Hindex. lia.
           ++ apply mono_inc_map_add_one__final_spec. exact Hmono.
      * assert ((S n <= count_occ Z.eq_dec text value)%nat) as Htail_count.
        { simpl in Hcount. destruct (Z.eq_dec head value);
            [contradiction|exact Hcount]. }
        destruct (IH value (S n) Htail_count)
          as (indices & Hmap & Hmono).
        exists (map (fun index => index + 1) indices). split.
        -- apply indexed_mapping_lift_source__final_spec. exact Hmap.
        -- apply mono_inc_map_add_one__final_spec. exact Hmono.
Qed.
Lemma indexed_mapping_under_prefix__final_spec :
  forall prefix text indices digits,
    Forall2
      (fun index digit =>
        0 <= index < Zlength text /\ digit = Znth index text 0)
      indices digits ->
    mono_inc indices ->
    exists lifted_indices,
      Forall2
        (fun index digit =>
          0 <= index < Zlength (prefix ++ text) /\
          digit = Znth index (prefix ++ text) 0)
        lifted_indices digits /\
      mono_inc lifted_indices.
Proof.
  intros prefix.
  induction prefix as [|head prefix IH];
    intros text indices digits Hmap Hmono.
  - exists indices. auto.
  - destruct (IH text indices digits Hmap Hmono)
      as (lifted_indices & Hlifted & Hlifted_mono).
    exists (map (fun index => index + 1) lifted_indices). split.
    + apply indexed_mapping_lift_source__final_spec. exact Hlifted.
    + apply mono_inc_map_add_one__final_spec. exact Hlifted_mono.
Qed.
Lemma chosen_divisible64_forces_six_source_zeros__final_spec :
  forall text indices digits seen_one zeros,
    (forall j, 0 <= j < Zlength text ->
      Znth j text 0 = 48 \/ Znth j text 0 = 49) ->
    ChosenBinaryDigits text indices digits ->
    BinaryValue digits > 0 ->
    (64 | BinaryValue digits) ->
    PrefixScan text seen_one zeros ->
    6 <= zeros.
Proof.
  intros text indices digits seen_one zeros Hchars Hchosen
    Hpositive Hdiv Hscan.
  destruct Hchosen as [_ [Hmap Hmono]].
  pose proof (chosen_digits_are_bits__final_spec
    text indices digits Hchars Hmap) as Hbits.
  destruct (binary_divisible64_has_six_zero_suffix__final_spec
    digits Hbits Hpositive Hdiv) as (prefix & Hdigits & Hprefix_positive).
  pose proof (binary_positive_contains_one__final_spec
    prefix ltac:(rewrite Hdigits, Forall_app in Hbits; tauto)
    Hprefix_positive) as Hin49.
  apply in_split in Hin49.
  destruct Hin49 as (left_digits & right_digits & Hprefix).
  subst prefix. subst digits.
  repeat rewrite <- app_assoc in Hmap.
  apply Forall2_app_inv_r in Hmap.
  destruct Hmap as (left_indices & suffix_indices & Hleft_map & Hsuffix_map & Hindices).
  subst indices.
  apply mono_inc_iff_ind in Hmono.
  rewrite mono_inc_ind_app in Hmono.
  destruct Hmono as [_ [Hsuffix_mono _]].
  apply mono_inc_iff_ind in Hsuffix_mono.
  unfold PrefixScan in Hscan.
  destruct Hscan as [[_ [_ Hno_one]] |
    [_ [before [after [Htext [Hbefore Hzeros]]]]]].
  - inversion Hsuffix_map as
      [|one_index one_digit remaining_indices remaining_digits Hone _];
      subst one_digit remaining_digits.
    destruct Hone as [Hbounds Hone].
    exfalso. apply Hno_one.
    unfold Znth in Hone. rewrite Hone.
    apply nth_In. rewrite Zlength_correct in Hbounds. lia.
  - subst text.
    destruct (indexed_mapping_after_first__final_spec
      before after suffix_indices
      (right_digits ++ 48 :: 48 :: 48 :: 48 :: 48 :: 48 :: nil)
      Hbefore Hsuffix_map Hsuffix_mono)
      as (after_indices & Hafter_map & Hafter_mono).
    pose proof (indexed_mapping_count_occ_le__final_spec
      after after_indices
      (right_digits ++ 48 :: 48 :: 48 :: 48 :: 48 :: 48 :: nil)
      48 Hafter_map Hafter_mono) as Hcount.
    rewrite count_occ_app in Hcount. simpl in Hcount.
    subst zeros. lia.
Qed.
Lemma six_source_zeros_choose_64__final_spec :
  forall text seen_one zeros,
    PrefixScan text seen_one zeros ->
    6 <= zeros ->
    exists indices,
      ChosenBinaryDigits text indices
        (49 :: 48 :: 48 :: 48 :: 48 :: 48 :: 48 :: nil) /\
      BinaryValue (49 :: 48 :: 48 :: 48 :: 48 :: 48 :: 48 :: nil) = 64.
Proof.
  intros text seen_one zeros Hscan Hsix.
  unfold PrefixScan in Hscan.
  destruct Hscan as [[_ [-> _]] |
    [_ [before [after [Htext [Hbefore Hzeros]]]]]]; [lia|].
  assert ((6 <= count_occ Z.eq_dec after (48 : Z))%nat) as Hcount by
    (subst zeros; lia).
  destruct (indexed_mapping_repeat_from_count__final_spec after 48 6 Hcount)
    as (zero_indices & Hzero_map & Hzero_mono).
  change (Forall2
    (fun index digit =>
      0 <= index < Zlength after /\ digit = Znth index after 0)
    zero_indices (48 :: 48 :: 48 :: 48 :: 48 :: 48 :: nil)) in Hzero_map.
  assert (Forall2
    (fun index digit =>
      0 <= index < Zlength (49 :: after) /\
      digit = Znth index (49 :: after) 0)
    (0 :: map (fun index => index + 1) zero_indices)
    (49 :: 48 :: 48 :: 48 :: 48 :: 48 :: 48 :: nil)) as Hfrom_first.
  { constructor.
    - split.
      + rewrite Zlength_cons. pose proof (Zlength_nonneg after). lia.
      + rewrite Znth0_cons. reflexivity.
    - apply indexed_mapping_lift_source__final_spec. exact Hzero_map. }
  assert (mono_inc (0 :: map (fun index => index + 1) zero_indices))
    as Hfrom_first_mono.
  { apply mono_inc_cons. split.
    - rewrite Forall_map.
      pose proof (indexed_mapping_indices_nonnegative__final_spec
        after zero_indices
        (48 :: 48 :: 48 :: 48 :: 48 :: 48 :: nil) Hzero_map)
        as Hnonnegative.
      revert Hnonnegative. apply Forall_impl.
      intros index Hindex. lia.
    - apply mono_inc_map_add_one__final_spec. exact Hzero_mono. }
  subst text.
  destruct (indexed_mapping_under_prefix__final_spec
    before (49 :: after)
    (0 :: map (fun index => index + 1) zero_indices)
    (49 :: 48 :: 48 :: 48 :: 48 :: 48 :: 48 :: nil)
    Hfrom_first Hfrom_first_mono) as (indices & Hindexed & Hindices_mono).
  exists indices. split.
  - unfold ChosenBinaryDigits. repeat split.
    + pose proof (Forall2_length Hindexed) as Hlength.
      rewrite Zlength_correct. simpl in Hlength. lia.
    + exact Hindexed.
    + exact Hindices_mono.
  - reflexivity.
Qed.
