Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

(* Character codes: '0' = 48, '1' = 49. *)
Definition BinaryCharacterXor (x y : Z) : Z :=
  if Z.eqb x y then 48 else 49.

Definition OneGameAction (before after : list Z) : Prop :=
  exists l r,
    0 <= l <= r /\ r < Zlength before /\
    Zlength after = Zlength before /\
    forall i, 0 <= i < Zlength before ->
      Znth i after 0 =
        if andb (l <=? i) (i <=? r)
        then BinaryCharacterXor (Znth i before 48) (Znth (i - l) before 48)
        else Znth i before 0.

Definition Pre (s t : list Z) : Prop :=
  1 <= Zlength s <= 200000 /\
  Zlength t = Zlength s /\
  Forall (fun c => c = 48 \/ c = 49) s /\
  Forall (fun c => c = 48 \/ c = 49) t.

Definition Spec (s t : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> clos_refl_trans OneGameAction s t).

Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Lemma zlength_replace_znth__game_semantics :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v.
  revert n.
  induction l; simpl in *; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma binary_character_xor_zero__game_semantics : forall x,
  (x = 48 \/ x = 49) ->
  BinaryCharacterXor x 48 = x.
Proof.
  intros x [-> | ->]; reflexivity.
Qed.
Lemma binary_character_xor_one_diff__game_semantics : forall x y,
  (x = 48 \/ x = 49) ->
  (y = 48 \/ y = 49) ->
  x <> y ->
  BinaryCharacterXor x 49 = y.
Proof.
  intros x y [-> | ->] [-> | ->]; try congruence; reflexivity.
Qed.
Lemma one_game_action_preserves_zero_prefix__game_semantics :
  forall before after bound,
    0 <= bound <= Zlength before ->
    (forall k, 0 <= k < bound -> Znth k before 0 = 48) ->
    OneGameAction before after ->
    Zlength after = Zlength before /\
    (forall k, 0 <= k < bound -> Znth k after 0 = 48).
Proof.
  intros before after bound Hbound Hzero Haction.
  destruct Haction as (l & r & Hlr & Hr & Hlen & Hpoint).
  split; [exact Hlen |].
  intros k Hk.
  rewrite Hpoint by lia.
  destruct (andb (l <=? k) (k <=? r)) eqn:Hinside.
  - apply andb_true_iff in Hinside.
    destruct Hinside as [Hlk Hkr].
    apply Z.leb_le in Hlk.
    apply Z.leb_le in Hkr.
    rewrite (Znth_indep before k 48 0) by lia.
    rewrite Hzero by exact Hk.
    rewrite (Znth_indep before (k - l) 48 0) by lia.
    rewrite Hzero by lia.
    reflexivity.
  - apply Hzero; exact Hk.
Qed.
Lemma game_reachable_preserves_zero_prefix__game_semantics :
  forall before after bound,
    0 <= bound <= Zlength before ->
    (forall k, 0 <= k < bound -> Znth k before 0 = 48) ->
    clos_refl_trans OneGameAction before after ->
    Zlength after = Zlength before /\
    (forall k, 0 <= k < bound -> Znth k after 0 = 48).
Proof.
  intros before after bound Hbound Hzero Hreach.
  unfold clos_refl_trans in Hreach.
  sets_unfold in Hreach.
  destruct Hreach as [n Hsteps].
  revert before after Hsteps Hbound Hzero.
  induction n as [|n IH]; intros before after Hsteps Hbound Hzero.
  - simpl in Hsteps.
    sets_unfold in Hsteps.
    subst after.
    split; auto.
  - simpl in Hsteps.
    sets_unfold in Hsteps.
    destruct Hsteps as [middle [Hstep Hrest]].
    pose proof
      (one_game_action_preserves_zero_prefix__game_semantics
         before middle bound Hbound Hzero Hstep) as [Hmiddle_len Hmiddle_zero].
    specialize (IH middle after Hrest ltac:(lia) Hmiddle_zero)
      as [Hafter_len Hafter_zero].
    split; [lia | exact Hafter_zero].
Qed.
Lemma one_game_action_toggle_after_first_one__game_semantics :
  forall before i q desired,
    0 <= i < q ->
    q < Zlength before ->
    Znth i before 0 = 49 ->
    (forall k, 0 <= k < i -> Znth k before 0 = 48) ->
    (forall k, 0 <= k < Zlength before ->
       Znth k before 0 = 48 \/ Znth k before 0 = 49) ->
    (desired = 48 \/ desired = 49) ->
    Znth q before 0 <> desired ->
    OneGameAction before (replace_Znth q desired before).
Proof.
  intros before i q desired Hi Hq Hfirst Hzero Hbits Hdesired Hdiff.
  exists (q - i), q.
  repeat split; try lia.
  - apply zlength_replace_znth__game_semantics.
  - intros k Hk.
    destruct (Z.eq_dec k q) as [-> | Hkq].
    + rewrite Znth_replace_Znth_Same by lia.
      assert (andb (q - i <=? q) (q <=? q) = true) as Hinside.
      { apply andb_true_iff. rewrite !Z.leb_le. lia. }
      rewrite Hinside.
      replace (q - (q - i)) with i by lia.
      rewrite (Znth_indep before q 48 0) by lia.
      rewrite (Znth_indep before i 48 0) by lia.
      rewrite Hfirst.
      symmetry.
      apply binary_character_xor_one_diff__game_semantics.
      * apply Hbits; lia.
      * exact Hdesired.
      * congruence.
    + rewrite Znth_replace_Znth_Diff by (try lia; congruence).
      destruct (andb (q - i <=? k) (k <=? q)) eqn:Hinside.
      * apply andb_true_iff in Hinside.
        destruct Hinside as [Hlo Hhi].
        apply Z.leb_le in Hlo.
        apply Z.leb_le in Hhi.
        rewrite (Znth_indep before k 48 0) by lia.
        rewrite (Znth_indep before (k - (q - i)) 48 0) by lia.
        pose proof (Hzero (k - (q - i)) ltac:(lia)) as Hshifted_zero.
        rewrite Hshifted_zero.
        symmetry.
        apply binary_character_xor_zero__game_semantics.
        apply Hbits; lia.
      * reflexivity.
Qed.
Lemma game_reachable_match_suffix_count__game_semantics :
  forall source target i (m : nat),
    0 <= i < Zlength source ->
    Zlength target = Zlength source ->
    Znth i source 0 = 49 ->
    (forall k, 0 <= k < i -> Znth k source 0 = 48) ->
    (forall k, 0 <= k < Zlength source ->
       Znth k source 0 = 48 \/ Znth k source 0 = 49) ->
    (forall k, 0 <= k < Zlength target ->
       Znth k target 0 = 48 \/ Znth k target 0 = 49) ->
    i + 1 + Z.of_nat m <= Zlength source ->
    exists current,
      clos_refl_trans OneGameAction source current /\
      Zlength current = Zlength source /\
      (forall k, 0 <= k < i -> Znth k current 0 = 48) /\
      Znth i current 0 = 49 /\
      (forall k, 0 <= k < Zlength current ->
         Znth k current 0 = 48 \/ Znth k current 0 = 49) /\
      (forall k, i < k < i + 1 + Z.of_nat m ->
         Znth k current 0 = Znth k target 0).
Proof.
  intros source target i m Hi Hlen Hfirst Hzero Hsource_bits Htarget_bits Hm.
  induction m as [|m IH].
  - exists source.
    repeat split; auto.
    + exists 0%nat. hnf. reflexivity.
    + intros; lia.
  - replace (Z.of_nat (S m)) with (Z.of_nat m + 1) in Hm |- * by lia.
    specialize (IH ltac:(lia)).
    destruct IH as
      (current & Hreach & Hcurrent_len & Hcurrent_zero & Hcurrent_first &
       Hcurrent_bits & Hmatched).
    set (q := i + 1 + Z.of_nat m).
    destruct (Z.eq_dec (Znth q current 0) (Znth q target 0)) as [Heq | Hneq].
    + exists current.
      repeat split; auto.
      intros k Hk.
      destruct (Z.eq_dec k q) as [-> | Hkq].
      * exact Heq.
      * apply Hmatched. unfold q in *; lia.
    + exists (replace_Znth q (Znth q target 0) current).
      repeat split.
      * transitivity current.
        -- exact Hreach.
        -- exists 1%nat.
           hnf.
           exists (replace_Znth q (Znth q target 0) current).
           split.
           ++ apply (one_game_action_toggle_after_first_one__game_semantics
                       current i q (Znth q target 0)).
              ** unfold q; lia.
              ** unfold q; lia.
              ** exact Hcurrent_first.
              ** exact Hcurrent_zero.
              ** exact Hcurrent_bits.
              ** apply Htarget_bits. unfold q; lia.
              ** exact Hneq.
           ++ reflexivity.
      * rewrite zlength_replace_znth__game_semantics. exact Hcurrent_len.
      * intros k Hk.
        rewrite Znth_replace_Znth_Diff.
        -- apply Hcurrent_zero; exact Hk.
        -- rewrite Hcurrent_len. unfold q; lia.
        -- rewrite Hcurrent_len. lia.
        -- unfold q; lia.
      * rewrite Znth_replace_Znth_Diff.
        -- exact Hcurrent_first.
        -- rewrite Hcurrent_len. unfold q; lia.
        -- rewrite Hcurrent_len. lia.
        -- unfold q; lia.
      * intros k Hk.
        rewrite zlength_replace_znth__game_semantics in Hk.
        destruct (Z.eq_dec k q) as [-> | Hkq].
        -- rewrite Znth_replace_Znth_Same by (rewrite Hcurrent_len; unfold q; lia).
           apply Htarget_bits. unfold q; lia.
        -- rewrite Znth_replace_Znth_Diff.
           ++ apply Hcurrent_bits; exact Hk.
           ++ rewrite Hcurrent_len. unfold q; lia.
           ++ exact Hk.
           ++ congruence.
      * intros k Hk.
        destruct (Z.eq_dec k q) as [-> | Hkq].
        -- rewrite Znth_replace_Znth_Same by (rewrite Hcurrent_len; unfold q; lia).
           reflexivity.
        -- rewrite Znth_replace_Znth_Diff.
           ++ apply Hmatched. unfold q in *; lia.
           ++ rewrite Hcurrent_len. unfold q; lia.
           ++ rewrite Hcurrent_len. unfold q in *; lia.
           ++ congruence.
Qed.
Lemma one_game_action_clear_through_first_one__game_semantics :
  forall before after i,
    0 <= i < Zlength before ->
    Zlength after = Zlength before ->
    (forall k, 0 <= k <= i -> Znth k after 0 = 48) ->
    (forall k, i < k < Zlength before ->
       Znth k after 0 = Znth k before 0) ->
    OneGameAction before after.
Proof.
  intros before after i Hi Hlen Hzero Hsuffix.
  exists 0, i.
  repeat split; try lia.
  intros k Hk.
  destruct (andb (0 <=? k) (k <=? i)) eqn:Hinside.
  - apply andb_true_iff in Hinside.
    destruct Hinside as [Hlo Hhi].
    apply Z.leb_le in Hlo.
    apply Z.leb_le in Hhi.
    rewrite Hzero by lia.
    replace (k - 0) with k by lia.
    unfold BinaryCharacterXor.
    rewrite Z.eqb_refl.
    reflexivity.
  - rewrite Hsuffix by lia.
    reflexivity.
Qed.
Lemma game_reachable_from_first_one__game_semantics :
  forall source target i,
    0 <= i < Zlength source ->
    Zlength target = Zlength source ->
    Znth i source 0 = 49 ->
    (forall k, 0 <= k < i -> Znth k source 0 = 48) ->
    (forall k, 0 <= k < Zlength source ->
       Znth k source 0 = 48 \/ Znth k source 0 = 49) ->
    (forall k, 0 <= k < Zlength target ->
       Znth k target 0 = 48 \/ Znth k target 0 = 49) ->
    (forall k, 0 <= k < i -> Znth k target 0 = 48) ->
    clos_refl_trans OneGameAction source target.
Proof.
  intros source target i Hi Hlen Hfirst Hsource_zero
         Hsource_bits Htarget_bits Htarget_zero.
  set (m := Z.to_nat (Zlength source - i - 1)).
  assert (Hm : i + 1 + Z.of_nat m = Zlength source).
  { unfold m. rewrite Z2Nat.id by lia. lia. }
  pose proof
    (game_reachable_match_suffix_count__game_semantics
       source target i m Hi Hlen Hfirst Hsource_zero
       Hsource_bits Htarget_bits ltac:(lia)) as
      (current & Hreach & Hcurrent_len & Hcurrent_zero & Hcurrent_first &
       Hcurrent_bits & Hmatched).
  destruct (Htarget_bits i ltac:(rewrite Hlen; lia)) as [Htarget_i | Htarget_i].
  - transitivity current.
    + exact Hreach.
    + exists 1%nat.
      hnf.
      exists target.
      split.
      * apply (one_game_action_clear_through_first_one__game_semantics
                 current target i).
        -- rewrite Hcurrent_len. exact Hi.
        -- lia.
        -- intros k Hk.
           destruct (Z.eq_dec k i) as [-> | Hki].
           ++ exact Htarget_i.
           ++ apply Htarget_zero; lia.
        -- intros k Hk.
           symmetry.
           apply Hmatched.
           rewrite Hm. lia.
      * reflexivity.
  - assert (current = target) as ->.
    { apply (proj2 (list_eq_ext current target 0)).
      split; [lia |].
      intros k Hk.
      destruct (Z_lt_ge_dec k i) as [Hki | Hki].
      - rewrite Hcurrent_zero by lia.
        symmetry. apply Htarget_zero. lia.
      - destruct (Z.eq_dec k i) as [-> | Hneq].
        + rewrite Hcurrent_first. symmetry. exact Htarget_i.
        + apply Hmatched. rewrite Hm. lia.
    }
    exact Hreach.
Qed.
