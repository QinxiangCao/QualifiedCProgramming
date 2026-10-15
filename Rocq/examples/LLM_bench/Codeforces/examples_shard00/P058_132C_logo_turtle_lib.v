Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition ChangedExactly (commands modified : list Z) (n : Z) : Prop :=
  Zlength modified = Zlength commands /\
  exists counts, Zlength counts = Zlength commands /\
    Forall (fun x => 0 <= x) counts /\ fold_right Z.add 0 counts = n /\
    forall i, 0 <= i < Zlength commands ->
      (Z.even (Znth i counts 0) = true ->
        Znth i modified 0 = Znth i commands 0) /\
      (Z.even (Znth i counts 0) = false ->
        ((Znth i commands 0 = 70 /\ Znth i modified 0 = 84) \/
         (Znth i commands 0 = 84 /\ Znth i modified 0 = 70))).

Definition TurtleEnd (c : list Z) (x : Z) : Prop :=
  exists states, Zlength states = Zlength c + 1 /\
    Znth 0 states (0, 1) = (0, 1) /\
    (forall i, 0 <= i < Zlength c ->
      let '(p, d) := Znth i states (0, 1) in
      Znth (i + 1) states (0, 1) =
        if Z.eqb (Znth i c 0) 84 then (p, -d) else (p + d, d)) /\
    x = fst (Znth (Zlength c) states (0, 1)).

Definition Pre (n : Z) (c : list Z) : Prop :=
  1 <= Zlength c <= 100 /\ 1 <= n <= 50 /\
  Forall (fun x => x = 70 \/ x = 84) c.

Definition Spec (n : Z) (c : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      ChangedExactly c (fst candidate) n /\
      TurtleEnd (fst candidate) (snd candidate))
    (fun candidate => Z.abs (snd candidate)) out.

Definition PrefixChangedByFlips
    (commands modified : list Z) (prefix_len flips : Z) : Prop :=
  0 <= prefix_len <= Zlength commands /\
  Zlength modified = prefix_len /\
  exists marks,
    Zlength marks = prefix_len /\
    Forall (fun x => x = 0 \/ x = 1) marks /\
    fold_right Z.add 0 marks = flips /\
    forall j, 0 <= j < prefix_len ->
      (Znth j marks 0 = 0 ->
         Znth j modified 0 = Znth j commands 0) /\
      (Znth j marks 0 = 1 ->
         ((Znth j commands 0 = 70 /\ Znth j modified 0 = 84) \/
          (Znth j commands 0 = 84 /\ Znth j modified 0 = 70))).

Definition TurtleState (commands : list Z) (position direction : Z) : Prop :=
  exists states,
    Zlength states = Zlength commands + 1 /\
    Znth 0 states (0, 1) = (0, 1) /\
    (forall i, 0 <= i < Zlength commands ->
      let '(p, d) := Znth i states (0, 1) in
      Znth (i + 1) states (0, 1) =
        if Z.eqb (Znth i commands 0) 84
        then (p, -d)
        else (p + d, d)) /\
    Znth (Zlength commands) states (0, 1) = (position, direction).

Definition PrefixReachable
    (commands : list Z) (prefix_len flips direction slot : Z) : Prop :=
  exists modified position final_direction,
    PrefixChangedByFlips commands modified prefix_len flips /\
    TurtleState modified position final_direction /\
    position = slot - Zlength commands /\
    ((direction = 0 /\ final_direction = 1) \/
     (direction = 1 /\ final_direction = -1)).

Definition TurtleWidth (commands : list Z) : Z :=
  2 * Zlength commands + 1.

Definition TurtleCellIndex
    (commands : list Z) (flips direction slot : Z) : Z :=
  (flips * 2 + direction) * TurtleWidth commands + slot.

Definition TurtleLayerMeaning
    (commands : list Z) (prefix_len change_limit : Z)
    (table : list Z) : Prop :=
  forall flips direction slot,
    0 <= flips <= change_limit ->
    0 <= direction < 2 ->
    0 <= slot < TurtleWidth commands ->
    let value := Znth (TurtleCellIndex commands flips direction slot) table 0 in
    (value = 0 \/ value = 1) /\
    (value = 1 <->
       PrefixReachable commands prefix_len flips direction slot).

Definition FlippedCommand (command flip effective : Z) : Prop :=
  (flip = 0 /\ effective = command) \/
  (flip = 1 /\
    ((command = 70 /\ effective = 84) \/
     (command = 84 /\ effective = 70))).

Definition TurtleEncodedStep
    (direction slot command next_direction next_slot : Z) : Prop :=
  (command = 84 /\ next_direction = 1 - direction /\ next_slot = slot) \/
  (command = 70 /\ next_direction = direction /\
    ((direction = 0 /\ next_slot = slot + 1) \/
     (direction = 1 /\ next_slot = slot - 1))).

Definition TurtleTransitionRank
    (commands : list Z) (flips direction slot flip : Z) : Z :=
  2 * TurtleCellIndex commands flips direction slot + flip.

Definition TurtleNextReachable
    (commands : list Z) (prefix_len change_limit done : Z)
    (next_flips next_direction next_slot : Z) : Prop :=
  exists flips direction slot flip effective,
    0 <= flips <= change_limit /\
    0 <= direction < 2 /\
    0 <= slot < TurtleWidth commands /\
    0 <= flip < 2 /\
    TurtleTransitionRank commands flips direction slot flip < done /\
    PrefixReachable commands prefix_len flips direction slot /\
    next_flips = flips + flip /\
    next_flips <= change_limit /\
    FlippedCommand (Znth prefix_len commands 0) flip effective /\
    TurtleEncodedStep direction slot effective next_direction next_slot.

Definition TurtleNextPrefix
    (commands : list Z) (prefix_len change_limit done : Z)
    (next_table : list Z) : Prop :=
  forall flips direction slot,
    0 <= flips <= change_limit ->
    0 <= direction < 2 ->
    0 <= slot < TurtleWidth commands ->
    let value := Znth (TurtleCellIndex commands flips direction slot) next_table 0 in
    (value = 0 \/ value = 1) /\
    (value = 1 <->
       TurtleNextReachable commands prefix_len change_limit done
         flips direction slot).

Definition TurtleTerminalEligible
    (commands : list Z) (change_limit flips direction slot : Z) : Prop :=
  0 <= flips <= change_limit /\
  0 <= direction < 2 /\
  0 <= slot < TurtleWidth commands /\
  Z.even (change_limit - flips) = true /\
  PrefixReachable commands (Zlength commands) flips direction slot.

Definition TurtleAnswerPrefix
    (commands : list Z) (change_limit done answer : Z) : Prop :=
  0 <= answer /\
  (forall flips direction slot,
    TurtleTerminalEligible commands change_limit flips direction slot ->
    TurtleCellIndex commands flips direction slot < done ->
    Z.abs (slot - Zlength commands) <= answer) /\
  (answer = 0 \/
   exists flips direction slot,
     TurtleTerminalEligible commands change_limit flips direction slot /\
     TurtleCellIndex commands flips direction slot < done /\
     answer = Z.abs (slot - Zlength commands)).

Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Lemma prefix_reachable_zero_iff__init_layer :
  forall commands flips direction slot,
    PrefixReachable commands 0 flips direction slot <->
    flips = 0 /\ direction = 0 /\ slot = Zlength commands.
Proof.
  intros commands flips direction slot.
  split.
  - intros (modified & position & final_direction & Hchanged & Hstate & Hposition & Hdirection).
    unfold PrefixChangedByFlips in Hchanged.
    destruct Hchanged as (_ & Hmodified & marks & Hmarks & _ & Hsum & _).
    destruct modified as [| modified_head modified_tail].
    2: rewrite Zlength_cons in Hmodified; pose proof (Zlength_nonneg modified_tail); lia.
    destruct marks as [| mark_head mark_tail].
    2: rewrite Zlength_cons in Hmarks; pose proof (Zlength_nonneg mark_tail); lia.
    simpl in Hsum.
    subst flips.
    unfold TurtleState in Hstate.
    destruct Hstate as (states & Hstates & Hinitial & _ & Hfinal).
    rewrite Zlength_nil in Hfinal.
    assert (Hpair : (position, final_direction) = (0, 1)) by congruence.
    inversion Hpair; subst position final_direction.
    split; [reflexivity|].
    split.
    + destruct Hdirection as [[Hdirection _] | [Hdirection Hbad]]; lia.
    + lia.
  - intros (Hflips & Hdirection & Hslot).
    subst flips direction slot.
    unfold PrefixReachable.
    exists (@nil Z), 0, 1.
    split.
    + unfold PrefixChangedByFlips.
      split.
      * pose proof (Zlength_nonneg commands); lia.
      * split.
        -- rewrite Zlength_nil; reflexivity.
        -- exists (@nil Z).
           split; [reflexivity|].
           split; [constructor|].
           split; [reflexivity|].
           intros j Hj. lia.
    + split.
      * unfold TurtleState.
        exists ((0, 1) :: nil).
        split; [reflexivity|].
        split; [reflexivity|].
        split.
        -- intros j Hj. exfalso. rewrite Zlength_nil in Hj. lia.
        -- reflexivity.
      * split.
        -- lia.
        -- left. split; reflexivity.
Qed.
Lemma turtle_layer_zero_table__init_layer :
  forall commands change_limit total,
    1 <= Zlength commands ->
    0 <= change_limit ->
    total = (change_limit + 1) * 2 * TurtleWidth commands ->
    TurtleLayerMeaning commands 0 change_limit
      (replace_Znth (Zlength commands) 1 (repeat 0 (Z.to_nat total))).
Proof.
  intros commands change_limit total Hcommands Hlimit Htotal.
  subst total.
  unfold TurtleLayerMeaning.
  intros flips direction slot Hflips Hdirection Hslot.
  unfold TurtleCellIndex.
  assert (Hrepeat :
    Zlength (repeat 0 (Z.to_nat ((change_limit + 1) * 2 * TurtleWidth commands))) =
      (change_limit + 1) * 2 * TurtleWidth commands).
  { rewrite Zlength_correct, repeat_length, Z2Nat.id.
    - reflexivity.
    - unfold TurtleWidth. pose proof (Zlength_nonneg commands). nia. }
  assert (Hcenter :
    0 <= Zlength commands <
      Zlength (repeat 0 (Z.to_nat ((change_limit + 1) * 2 * TurtleWidth commands)))).
  { rewrite Hrepeat. unfold TurtleWidth. nia. }
  assert (Hindex :
    0 <= (flips * 2 + direction) * TurtleWidth commands + slot <
      Zlength (repeat 0 (Z.to_nat ((change_limit + 1) * 2 * TurtleWidth commands)))).
  { rewrite Hrepeat. unfold TurtleWidth in *. pose proof (Zlength_nonneg commands). nia. }
  destruct (Z.eq_dec ((flips * 2 + direction) * TurtleWidth commands + slot)
                     (Zlength commands)) as [Heq | Hneq].
  - rewrite Heq, Znth_replace_Znth_Same by exact Hcenter.
    split; [right; reflexivity|].
    split.
    + intros Hvalue. apply prefix_reachable_zero_iff__init_layer.
      unfold TurtleWidth in Heq, Hslot.
      pose proof (Zlength_nonneg commands).
      assert (Hcoefficient : flips * 2 + direction = 0) by nia.
      repeat split; nia.
    + intros Hreachable. reflexivity.
  - rewrite Znth_replace_Znth_Diff;
      [| exact Hcenter | exact Hindex | congruence].
    rewrite Znth_repeat.
    split; [left; reflexivity|].
    split.
    + lia.
    + intro Hreachable.
      apply prefix_reachable_zero_iff__init_layer in Hreachable.
      destruct Hreachable as (Hflips0 & Hdirection0 & Hslot0).
      subst flips direction slot.
      unfold TurtleWidth in Hneq.
      lia.
Qed.
Lemma turtle_next_zero_table__init_layer :
  forall commands prefix_len change_limit total,
    TurtleNextPrefix commands prefix_len change_limit 0
      (repeat 0 (Z.to_nat total)).
Proof.
  intros commands prefix_len change_limit total.
  unfold TurtleNextPrefix.
  intros flips direction slot Hflips Hdirection Hslot.
  rewrite Znth_repeat.
  split; [left; reflexivity|].
  split.
  - lia.
  - intros (old_flips & old_direction & old_slot & flip & effective &
            Hold_flips & Hold_direction & Hold_slot & Hflip & Hrank & _).
    unfold TurtleTransitionRank, TurtleCellIndex, TurtleWidth in Hrank.
    pose proof (Zlength_nonneg commands).
    nia.
Qed.
Lemma binary_lxor_one__direction_bit :
  forall d, 0 <= d < 2 -> Z.lxor d 1 = 1 - d.
Proof.
  intros d Hd.
  assert (d = 0 \/ d = 1) as [-> | ->] by lia;
    reflexivity.
Qed.
Lemma binary_destination_bound__direction_bit :
  forall changes c flip d width pos,
    c + flip <= changes ->
    0 <= d < 2 ->
    0 < width ->
    0 <= pos < width ->
    (((c + flip) * 2 + Z.lxor d 1) * width + pos <
      ((changes + 1) * 2) * width).
Proof.
  intros changes c flip d width pos Hchanges Hd Hwidth Hpos.
  rewrite binary_lxor_one__direction_bit by exact Hd.
  assert (Hcoeff : (c + flip) * 2 + (1 - d) + 1 <= (changes + 1) * 2) by lia.
  pose proof (Z.mul_le_mono_nonneg_r
    ((c + flip) * 2 + (1 - d) + 1)
    ((changes + 1) * 2) width ltac:(lia) Hcoeff) as Hscaled.
  replace (((c + flip) * 2 + (1 - d) + 1) * width)
    with (((c + flip) * 2 + (1 - d)) * width + width) in Hscaled by ring.
  lia.
Qed.
Lemma turtle_next_prefix_write_one__next_update_core :
  forall commands prefix_len change_limit done next_table
         next_flips next_direction next_slot,
    TurtleNextPrefix commands prefix_len change_limit done next_table ->
    Zlength next_table =
      (change_limit + 1) * 2 * TurtleWidth commands ->
    0 <= next_flips <= change_limit ->
    0 <= next_direction < 2 ->
    0 <= next_slot < TurtleWidth commands ->
    TurtleNextReachable commands prefix_len change_limit (done + 1)
      next_flips next_direction next_slot ->
    (forall flips direction slot,
      0 <= flips <= change_limit ->
      0 <= direction < 2 ->
      0 <= slot < TurtleWidth commands ->
      TurtleNextReachable commands prefix_len change_limit (done + 1)
        flips direction slot ->
      ~ TurtleNextReachable commands prefix_len change_limit done
        flips direction slot ->
      flips = next_flips /\
      direction = next_direction /\ slot = next_slot) ->
    TurtleNextPrefix commands prefix_len change_limit (done + 1)
      (replace_Znth
        (TurtleCellIndex commands next_flips next_direction next_slot)
        1 next_table).
Proof.
  intros commands prefix_len change_limit done next_table
    next_flips next_direction next_slot Hprefix Hlength
    Hnext_flips Hnext_direction Hnext_slot Hnew Hunique.
  unfold TurtleNextPrefix in *.
  intros flips direction slot Hflips Hdirection Hslot.
  specialize (Hprefix flips direction slot Hflips Hdirection Hslot).
  cbn beta in Hprefix |- *.
  assert (Hwidth : 0 < TurtleWidth commands) by lia.
  assert (Hindex :
    0 <= TurtleCellIndex commands flips direction slot <
      Zlength next_table).
  { rewrite Hlength. unfold TurtleCellIndex. nia. }
  assert (Hnext_index :
    0 <= TurtleCellIndex commands next_flips next_direction next_slot <
      Zlength next_table).
  { rewrite Hlength. unfold TurtleCellIndex. nia. }
  destruct (Z.eq_dec
    (TurtleCellIndex commands flips direction slot)
    (TurtleCellIndex commands next_flips next_direction next_slot))
    as [Hsame | Hdifferent].
  - assert (Hcoefficient :
      flips * 2 + direction = next_flips * 2 + next_direction).
    { unfold TurtleCellIndex in Hsame. nia. }
    assert (Hflips_equal : flips = next_flips) by lia.
    assert (Hdirection_equal : direction = next_direction) by lia.
    assert (Hslot_equal : slot = next_slot).
    { unfold TurtleCellIndex in Hsame. nia. }
    subst flips direction slot.
    rewrite Znth_replace_Znth_Same by exact Hnext_index.
    split; [right; reflexivity|].
    split; [intros _; exact Hnew|intros _; reflexivity].
  - rewrite Znth_replace_Znth_Diff;
      [|exact Hnext_index|exact Hindex|congruence].
    destruct Hprefix as [Hvalue Hmeaning].
    split; [exact Hvalue|].
    split.
    + intro Hvalue_one.
      apply Hmeaning in Hvalue_one.
      unfold TurtleNextReachable in *.
      destruct Hvalue_one as
        (old_flips & old_direction & old_slot & flip & effective &
         Hold_flips & Hold_direction & Hold_slot & Hflip & Hrank &
         Hreachable & Hnext_flips_eq & Hchange & Hcommand & Hstep).
      exists old_flips, old_direction, old_slot, flip, effective.
      repeat split; try assumption; lia.
    + intro Hreachable_new.
      destruct (classic
        (TurtleNextReachable commands prefix_len change_limit done
          flips direction slot)) as [Hreachable_old | Hnot_old].
      * apply Hmeaning. exact Hreachable_old.
      * specialize (Hunique flips direction slot Hflips Hdirection Hslot
          Hreachable_new Hnot_old).
        destruct Hunique as [-> [-> ->]]. contradiction.
Qed.
Lemma turtle_transition_new_cell_unique__next_update_core :
  forall commands prefix_len change_limit done
         old_flips old_direction old_slot selected_flip effective
         next_flips next_direction next_slot,
    0 <= old_flips <= change_limit ->
    0 <= old_direction < 2 ->
    0 <= old_slot < TurtleWidth commands ->
    0 <= selected_flip < 2 ->
    TurtleTransitionRank commands old_flips old_direction old_slot
      selected_flip = done ->
    PrefixReachable commands prefix_len old_flips old_direction old_slot ->
    next_flips = old_flips + selected_flip ->
    next_flips <= change_limit ->
    FlippedCommand (Znth prefix_len commands 0) selected_flip effective ->
    TurtleEncodedStep old_direction old_slot effective
      next_direction next_slot ->
    forall flips direction slot,
      0 <= flips <= change_limit ->
      0 <= direction < 2 ->
      0 <= slot < TurtleWidth commands ->
      TurtleNextReachable commands prefix_len change_limit (done + 1)
        flips direction slot ->
      ~ TurtleNextReachable commands prefix_len change_limit done
        flips direction slot ->
      flips = next_flips /\
      direction = next_direction /\ slot = next_slot.
Proof.
  intros commands prefix_len change_limit done
    old_flips old_direction old_slot selected_flip effective
    next_flips next_direction next_slot
    Hold_flips Hold_direction Hold_slot Hselected_flip Hrank
    Hreachable Hnext_flips Hchange Hcommand Hstep
    flips direction slot Hflips Hdirection Hslot Hnew Hnot_old.
  unfold TurtleNextReachable in Hnew.
  destruct Hnew as
    (candidate_flips & candidate_direction & candidate_slot & candidate_flip &
     candidate_effective & Hcandidate_flips & Hcandidate_direction &
     Hcandidate_slot & Hcandidate_flip & Hcandidate_rank &
     Hcandidate_reachable & Hflips_result & Hcandidate_change &
     Hcandidate_command & Hcandidate_step).
  assert (Hcandidate_not_before :
    ~ TurtleTransitionRank commands candidate_flips candidate_direction
        candidate_slot candidate_flip < done).
  { intro Hbefore. apply Hnot_old.
    unfold TurtleNextReachable.
    exists candidate_flips, candidate_direction, candidate_slot,
      candidate_flip, candidate_effective.
    refine (conj Hcandidate_flips _).
    refine (conj Hcandidate_direction _).
    refine (conj Hcandidate_slot _).
    refine (conj Hcandidate_flip _).
    refine (conj Hbefore _).
    refine (conj Hcandidate_reachable _).
    refine (conj Hflips_result _).
    refine (conj Hcandidate_change _).
    exact (conj Hcandidate_command Hcandidate_step). }
  assert (Hcandidate_rank_equal :
    TurtleTransitionRank commands candidate_flips candidate_direction
      candidate_slot candidate_flip = done) by lia.
  assert (Hcell_equal :
    TurtleCellIndex commands candidate_flips candidate_direction candidate_slot =
    TurtleCellIndex commands old_flips old_direction old_slot).
  { unfold TurtleTransitionRank in Hcandidate_rank_equal, Hrank. lia. }
  assert (Hflip_equal : candidate_flip = selected_flip).
  { unfold TurtleTransitionRank in Hcandidate_rank_equal, Hrank. lia. }
  assert (Hwidth : 0 < TurtleWidth commands) by lia.
  assert (Hcoefficient :
    candidate_flips * 2 + candidate_direction =
      old_flips * 2 + old_direction).
  { unfold TurtleCellIndex in Hcell_equal. nia. }
  assert (Hold_flips_equal : candidate_flips = old_flips) by lia.
  assert (Hold_direction_equal : candidate_direction = old_direction) by lia.
  assert (Hold_slot_equal : candidate_slot = old_slot).
  { unfold TurtleCellIndex in Hcell_equal. nia. }
  subst candidate_flips candidate_direction candidate_slot candidate_flip.
  assert (Heffective : candidate_effective = effective).
  { unfold FlippedCommand in Hcandidate_command, Hcommand.
    intuition congruence. }
  subst candidate_effective.
  split; [lia|].
  unfold TurtleEncodedStep in Hcandidate_step, Hstep.
  intuition congruence.
Qed.
Lemma turtle_next_prefix_write_transition__next_update_core :
  forall commands prefix_len change_limit done next_table
         old_flips old_direction old_slot selected_flip effective
         next_flips next_direction next_slot,
    TurtleNextPrefix commands prefix_len change_limit done next_table ->
    Zlength next_table =
      (change_limit + 1) * 2 * TurtleWidth commands ->
    0 <= old_flips <= change_limit ->
    0 <= old_direction < 2 ->
    0 <= old_slot < TurtleWidth commands ->
    0 <= selected_flip < 2 ->
    TurtleTransitionRank commands old_flips old_direction old_slot
      selected_flip = done ->
    PrefixReachable commands prefix_len old_flips old_direction old_slot ->
    next_flips = old_flips + selected_flip ->
    next_flips <= change_limit ->
    FlippedCommand (Znth prefix_len commands 0) selected_flip effective ->
    TurtleEncodedStep old_direction old_slot effective
      next_direction next_slot ->
    0 <= next_flips <= change_limit ->
    0 <= next_direction < 2 ->
    0 <= next_slot < TurtleWidth commands ->
    TurtleNextPrefix commands prefix_len change_limit (done + 1)
      (replace_Znth
        (TurtleCellIndex commands next_flips next_direction next_slot)
        1 next_table).
Proof.
  intros commands prefix_len change_limit done next_table
    old_flips old_direction old_slot selected_flip effective
    next_flips next_direction next_slot Hprefix Hlength
    Hold_flips Hold_direction Hold_slot Hselected_flip Hrank
    Hreachable Hnext_flips Hchange Hcommand Hstep
    Hnext_flips_bounds Hnext_direction Hnext_slot.
  assert (Hrank_before :
    TurtleTransitionRank commands old_flips old_direction old_slot
      selected_flip < done + 1).
  { rewrite Hrank. apply Z.lt_succ_diag_r. }
  eapply turtle_next_prefix_write_one__next_update_core;
    [exact Hprefix | exact Hlength | exact Hnext_flips_bounds |
     exact Hnext_direction | exact Hnext_slot | |].
  - unfold TurtleNextReachable.
    exists old_flips, old_direction, old_slot, selected_flip, effective.
    refine (conj Hold_flips _).
    refine (conj Hold_direction _).
    refine (conj Hold_slot _).
    refine (conj Hselected_flip _).
    refine (conj Hrank_before _).
    refine (conj Hreachable _).
    refine (conj Hnext_flips _).
    refine (conj Hchange _).
    exact (conj Hcommand Hstep).
  - eapply (turtle_transition_new_cell_unique__next_update_core
      commands prefix_len change_limit done
      old_flips old_direction old_slot selected_flip effective
      next_flips next_direction next_slot).
    + exact Hold_flips.
    + exact Hold_direction.
    + exact Hold_slot.
    + exact Hselected_flip.
    + exact Hrank.
    + exact Hreachable.
    + exact Hnext_flips.
    + exact Hchange.
    + exact Hcommand.
    + exact Hstep.
Qed.
Lemma turtle_next_prefix_skip_rank__next_noop :
  forall commands prefix_len change_limit done next_table,
    TurtleNextPrefix commands prefix_len change_limit done next_table ->
    (forall flips direction slot flip effective
            next_flips next_direction next_slot,
      0 <= flips <= change_limit ->
      0 <= direction < 2 ->
      0 <= slot < TurtleWidth commands ->
      0 <= flip < 2 ->
      TurtleTransitionRank commands flips direction slot flip = done ->
      PrefixReachable commands prefix_len flips direction slot ->
      next_flips = flips + flip ->
      next_flips <= change_limit ->
      FlippedCommand (Znth prefix_len commands 0) flip effective ->
      TurtleEncodedStep direction slot effective next_direction next_slot ->
      ~ (0 <= next_flips <= change_limit /\
         0 <= next_direction < 2 /\
         0 <= next_slot < TurtleWidth commands)) ->
    TurtleNextPrefix commands prefix_len change_limit (done + 1) next_table.
Proof.
  intros commands prefix_len change_limit done next_table Hprefix Hskip.
  unfold TurtleNextPrefix in *.
  intros next_flips next_direction next_slot Hnext_flips Hnext_direction Hnext_slot.
  specialize (Hprefix next_flips next_direction next_slot
    Hnext_flips Hnext_direction Hnext_slot).
  destruct Hprefix as [Hvalue Hmeaning].
  split; [exact Hvalue |].
  split.
  - intro Hvalue_one.
    apply Hmeaning in Hvalue_one.
    unfold TurtleNextReachable in *.
    destruct Hvalue_one as
      (flips & direction & slot & flip & effective &
       Hflips & Hdirection & Hslot & Hflip & Hrank & Hreachable &
       Hnext_flips_eq & Hchange & Hcommand & Hstep).
    exists flips, direction, slot, flip, effective.
    repeat split; try assumption; lia.
  - intro Hreachable_new.
    unfold TurtleNextReachable in Hreachable_new.
    destruct Hreachable_new as
      (flips & direction & slot & flip & effective &
       Hflips & Hdirection & Hslot & Hflip & Hrank & Hreachable &
       Hnext_flips_eq & Hchange & Hcommand & Hstep).
    destruct (Z.lt_trichotomy
      (TurtleTransitionRank commands flips direction slot flip) done)
      as [Hrank_old | [Hrank_eq | Hrank_after]].
    + apply Hmeaning.
      unfold TurtleNextReachable.
      exists flips, direction, slot, flip, effective.
      refine (conj Hflips _).
      refine (conj Hdirection _).
      refine (conj Hslot _).
      refine (conj Hflip _).
      refine (conj Hrank_old _).
      refine (conj Hreachable _).
      refine (conj Hnext_flips_eq _).
      refine (conj Hchange _).
      exact (conj Hcommand Hstep).
    + exfalso.
      eapply (Hskip flips direction slot flip effective
        next_flips next_direction next_slot);
        eauto.
    + lia.
Qed.
Lemma Znth_app_left__next_noop :
  forall (left right : list Z) index default,
    0 <= index < Zlength left ->
    Znth index (left ++ right) default = Znth index left default.
Proof.
  intros left.
  induction left as [|head left IH]; intros right index default Hindex.
  - rewrite Zlength_nil in Hindex. lia.
  - destruct (Z.eq_dec index 0) as [-> | Hnonzero].
    + reflexivity.
    + simpl.
      rewrite !Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hindex.
      lia.
Qed.
Lemma turtle_transition_rank_injective__next_noop :
  forall commands flips1 direction1 slot1 flip1
                  flips2 direction2 slot2 flip2,
    0 <= direction1 < 2 ->
    0 <= slot1 < TurtleWidth commands ->
    0 <= flip1 < 2 ->
    0 <= direction2 < 2 ->
    0 <= slot2 < TurtleWidth commands ->
    0 <= flip2 < 2 ->
    TurtleTransitionRank commands flips1 direction1 slot1 flip1 =
      TurtleTransitionRank commands flips2 direction2 slot2 flip2 ->
    flips1 = flips2 /\ direction1 = direction2 /\
    slot1 = slot2 /\ flip1 = flip2.
Proof.
  intros commands flips1 direction1 slot1 flip1
    flips2 direction2 slot2 flip2
    Hdirection1 Hslot1 Hflip1 Hdirection2 Hslot2 Hflip2 Hrank.
  unfold TurtleTransitionRank in Hrank.
  assert (Hflip : flip1 = flip2) by lia.
  subst flip2.
  assert (Hcell :
      TurtleCellIndex commands flips1 direction1 slot1 =
      TurtleCellIndex commands flips2 direction2 slot2) by lia.
  unfold TurtleCellIndex in Hcell.
  assert (Hwidth : 0 < TurtleWidth commands).
  { unfold TurtleWidth. pose proof (Zlength_nonneg commands). lia. }
  assert (Hmod1 :
      ((flips1 * 2 + direction1) * TurtleWidth commands + slot1)
        mod TurtleWidth commands = slot1).
  { rewrite Z.add_mod by lia.
    rewrite Z.mod_mul by lia.
    assert (Hslot1mod : slot1 mod TurtleWidth commands = slot1).
    { apply Z.mod_small. lia. }
    rewrite Hslot1mod.
    simpl.
    exact Hslot1mod. }
  assert (Hmod2 :
      ((flips2 * 2 + direction2) * TurtleWidth commands + slot2)
        mod TurtleWidth commands = slot2).
  { rewrite Z.add_mod by lia.
    rewrite Z.mod_mul by lia.
    assert (Hslot2mod : slot2 mod TurtleWidth commands = slot2).
    { apply Z.mod_small. lia. }
    rewrite Hslot2mod.
    simpl.
    exact Hslot2mod. }
  assert (Hslot : slot1 = slot2).
  { pose proof (f_equal (fun value => value mod TurtleWidth commands) Hcell) as Hmod.
    cbn beta in Hmod.
    rewrite Hmod1, Hmod2 in Hmod.
    exact Hmod. }
  subst slot2.
  assert (Hcoefficient :
      flips1 * 2 + direction1 = flips2 * 2 + direction2).
  { apply (Z.mul_reg_r _ _ (TurtleWidth commands)); [lia |].
    lia. }
  assert (Hdirection : direction1 = direction2) by lia.
  subst direction2.
  assert (Hflips : flips1 = flips2) by lia.
  repeat split; assumption.
Qed.
Lemma prefix_changed_extend__layer_swap :
  forall commands modified prefix_len flips flip effective,
    0 <= prefix_len < Zlength commands ->
    PrefixChangedByFlips commands modified prefix_len flips ->
    FlippedCommand (Znth prefix_len commands 0) flip effective ->
    PrefixChangedByFlips commands (modified ++ (effective :: nil))
      (prefix_len + 1) (flips + flip).
Proof.
  intros commands modified prefix_len flips flip effective Hprefix
    (Hplen & Hmodified & marks & Hmarks & Hmarkvals & Hsum & Hpoint)
    Hflipped.
  unfold PrefixChangedByFlips.
  split; [lia|].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - exists (marks ++ (flip :: nil)).
    split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + split.
      * apply Forall_app. split; [exact Hmarkvals|].
        constructor; [|constructor].
        unfold FlippedCommand in Hflipped.
        intuition lia.
      * split.
        -- rewrite fold_right_app. simpl.
           induction marks as [|a marks IH] in flips, Hsum |- *; simpl in *.
           ++ lia.
           ++ rewrite (IH (fold_right Z.add 0 marks) eq_refl). lia.
        -- intros j Hj.
           destruct (Z_lt_ge_dec j prefix_len) as [Hlt|Hge].
           ++ rewrite (app_Znth1 0) by lia.
              rewrite (app_Znth1 0) by lia.
              apply Hpoint. lia.
           ++ assert (j = prefix_len) by lia. subst j.
              rewrite (app_Znth2 0) by lia.
              rewrite (app_Znth2 0) by lia.
              replace (prefix_len - Zlength marks) with 0 by lia.
              replace (prefix_len - Zlength modified) with 0 by lia.
              rewrite !Znth0_cons.
              unfold FlippedCommand in Hflipped.
              intuition congruence.
Qed.
Lemma turtle_state_extend__layer_swap :
  forall modified position final_direction effective next_position next_direction,
    TurtleState modified position final_direction ->
    ((effective = 84 /\ next_position = position /\
        next_direction = - final_direction) \/
     (effective = 70 /\ next_position = position + final_direction /\
        next_direction = final_direction)) ->
    TurtleState (modified ++ (effective :: nil)) next_position next_direction.
Proof.
  intros modified position final_direction effective next_position next_direction
    (states & Hlen & Hzero & Hsteps & Hfinal) Hstep.
  pose proof (Zlength_nonneg modified) as Hmodified_nonneg.
  unfold TurtleState.
  exists (states ++ ((next_position, next_direction) :: nil)).
  split.
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
  - split.
    + rewrite (app_Znth1 (0, 1)) by (rewrite Hlen; lia).
      exact Hzero.
    + split.
      * intros j Hj.
        destruct (Z_lt_ge_dec j (Zlength modified)) as [Hlt|Hge].
        -- rewrite (app_Znth1 (0, 1)) by lia.
           rewrite (app_Znth1 (0, 1)) by (rewrite Hlen; lia).
           rewrite (app_Znth1 0) by lia.
           apply Hsteps. lia.
        -- assert (j = Zlength modified) by
             (rewrite Zlength_app, Zlength_cons, Zlength_nil in Hj; lia).
           subst j.
           rewrite (app_Znth1 (0, 1)) by (rewrite Hlen; lia).
           rewrite Hfinal.
           rewrite (app_Znth2 (0, 1)) by (rewrite Hlen; lia).
           replace (Zlength modified + 1 - Zlength states) with 0 by lia.
           rewrite Znth0_cons.
           rewrite (app_Znth2 0) by lia.
           replace (Zlength modified - Zlength modified) with 0 by lia.
           rewrite Znth0_cons.
           destruct Hstep as [(? & ? & ?)|(? & ? & ?)]; subst;
             rewrite ?Z.eqb_refl; simpl; try reflexivity;
             assert (Z.eqb 70 84 = false) by reflexivity;
             rewrite H; reflexivity.
      * rewrite (app_Znth2 (0, 1)).
        -- replace (Zlength (modified ++ (effective :: nil)) - Zlength states) with 0
             by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
           rewrite Znth0_cons. reflexivity.
        -- rewrite Hlen, Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.
Lemma turtle_state_endpoint_bound__layer_swap :
  forall modified position direction,
    TurtleState modified position direction ->
    - Zlength modified <= position <= Zlength modified /\
    (direction = 1 \/ direction = -1).
Proof.
  intros modified position direction
    (states & Hlen & Hzero & Hsteps & Hfinal).
  pose proof (Zlength_nonneg modified) as Hmodified_nonneg.
  assert (Hinv : forall m : nat,
    Z.of_nat m <= Zlength modified ->
    let st := Znth (Z.of_nat m) states (0, 1) in
    - Z.of_nat m <= fst st <= Z.of_nat m /\
    (snd st = 1 \/ snd st = -1)).
  {
    intros m.
    induction m as [|m IH].
    - intros _. simpl Z.of_nat.
      rewrite Hzero. simpl. lia.
    - intros Hm.
      rewrite Nat2Z.inj_succ in Hm |- *.
      specialize (IH ltac:(lia)).
      specialize (Hsteps (Z.of_nat m) ltac:(lia)).
      destruct (Znth (Z.of_nat m) states (0, 1)) as [p d] eqn:Hpd.
      simpl in IH, Hsteps.
      change (- (Z.of_nat m + 1) <=
        fst (Znth (Z.of_nat m + 1) states (0, 1)) <= Z.of_nat m + 1 /\
        (snd (Znth (Z.of_nat m + 1) states (0, 1)) = 1 \/
         snd (Znth (Z.of_nat m + 1) states (0, 1)) = -1)).
      rewrite Hsteps.
      destruct (Z.eqb (Znth (Z.of_nat m) modified 0) 84) eqn:Hcommand.
      * simpl. destruct IH as [Hp Hdirs]. split.
        -- lia.
        -- destruct Hdirs as [Hd|Hd]; [right; lia|left; lia].
      * simpl. destruct IH as [Hp Hdirs]. split.
        -- destruct Hdirs as [Hd|Hd]; lia.
        -- destruct Hdirs as [Hd|Hd]; [left; lia|right; lia].
  }
  specialize (Hinv (Z.to_nat (Zlength modified)) ltac:(lia)).
  rewrite Z2Nat.id in Hinv by lia.
  rewrite Hfinal in Hinv. exact Hinv.
Qed.
Lemma turtle_state_unextend__layer_swap :
  forall modified effective next_position next_direction,
    (effective = 70 \/ effective = 84) ->
    TurtleState (modified ++ (effective :: nil))
      next_position next_direction ->
    exists position direction,
      TurtleState modified position direction /\
      ((effective = 84 /\ next_position = position /\
          next_direction = - direction) \/
       (effective = 70 /\ next_position = position + direction /\
          next_direction = direction)).
Proof.
  intros modified effective next_position next_direction Heffective
    (states & Hlen & Hzero & Hsteps & Hfinal).
  pose proof (Zlength_nonneg modified) as Hmodified_nonneg.
  set (position := fst (Znth (Zlength modified) states (0, 1))).
  set (direction := snd (Znth (Zlength modified) states (0, 1))).
  exists position, direction.
  split.
  - unfold TurtleState.
    exists (sublist 0 (Zlength modified + 1) states).
    split.
    + rewrite Zlength_sublist by (rewrite Hlen, Zlength_app,
        Zlength_cons, Zlength_nil; lia). lia.
    + split.
      * rewrite Znth_sublist0 by lia. exact Hzero.
      * split.
        -- intros j Hj.
           rewrite Znth_sublist0 by lia.
           rewrite Znth_sublist0 by lia.
           specialize (Hsteps j ltac:(
             rewrite Zlength_app, Zlength_cons, Zlength_nil; lia)).
           rewrite (app_Znth1 0) in Hsteps by lia.
           exact Hsteps.
        -- unfold position, direction.
           rewrite Znth_sublist0 by lia.
           destruct (Znth (Zlength modified) states (0, 1)); reflexivity.
  - specialize (Hsteps (Zlength modified) ltac:(
      rewrite Zlength_app, Zlength_cons, Zlength_nil; lia)).
    rewrite (app_Znth2 0) in Hsteps by lia.
    replace (Zlength modified - Zlength modified) with 0 in Hsteps by lia.
    rewrite Znth0_cons in Hsteps.
    assert (Hlast : Znth (Zlength modified + 1) states (0, 1) =
        (next_position, next_direction)).
    {
      rewrite <- Hfinal.
      replace (Zlength modified + 1)
        with (Zlength (modified ++ effective :: nil)) by
        (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      reflexivity.
    }
    rewrite Hlast in Hsteps.
    unfold position, direction.
    destruct (Znth (Zlength modified) states (0, 1)) as [p d].
    simpl in Hsteps |- *.
    destruct Heffective as [Heff|Heff].
    + subst effective. right. repeat split; try reflexivity.
      simpl in Hsteps. exact (f_equal fst Hsteps).
      simpl in Hsteps. exact (f_equal snd Hsteps).
    + subst effective. left. repeat split; try reflexivity.
      rewrite Z.eqb_refl in Hsteps.
      exact (f_equal fst Hsteps).
      rewrite Z.eqb_refl in Hsteps.
      exact (f_equal snd Hsteps).
Qed.
Lemma fold_right_add_app_single__layer_swap :
  forall xs x,
    fold_right Z.add 0 (xs ++ (x :: nil)) =
    fold_right Z.add 0 xs + x.
Proof.
  induction xs as [|a xs IH]; intros x; simpl; [lia|].
  rewrite IH. lia.
Qed.
Lemma prefix_changed_unextend__layer_swap :
  forall commands modified prefix_len total_flips,
    0 <= prefix_len < Zlength commands ->
    PrefixChangedByFlips commands modified (prefix_len + 1) total_flips ->
    exists before flips flip effective,
      modified = before ++ (effective :: nil) /\
      total_flips = flips + flip /\
      PrefixChangedByFlips commands before prefix_len flips /\
      FlippedCommand (Znth prefix_len commands 0) flip effective.
Proof.
  intros commands modified prefix_len total_flips Hprefix
    (Hplen & Hmodified & marks & Hmarks & Hmarkvals & Hsum & Hpoint).
  pose proof (Zlength_nonneg modified) as Hmodified_nonneg.
  assert (Hmod_decomp : modified =
      sublist 0 prefix_len modified ++
      (Znth prefix_len modified 0 :: nil)).
  {
    transitivity (sublist 0 (prefix_len + 1) modified).
    - symmetry. apply sublist_self. lia.
    - rewrite (sublist_split 0 (prefix_len + 1) prefix_len modified)
        by lia.
      rewrite (sublist_single 0) by lia. reflexivity.
  }
  assert (Hmarks_decomp : marks =
      sublist 0 prefix_len marks ++
      (Znth prefix_len marks 0 :: nil)).
  {
    transitivity (sublist 0 (prefix_len + 1) marks).
    - symmetry. apply sublist_self. lia.
    - rewrite (sublist_split 0 (prefix_len + 1) prefix_len marks)
        by lia.
      rewrite (sublist_single 0) by lia. reflexivity.
  }
  exists (sublist 0 prefix_len modified),
    (fold_right Z.add 0 (sublist 0 prefix_len marks)),
    (Znth prefix_len marks 0), (Znth prefix_len modified 0).
  split; [exact Hmod_decomp|].
  split.
  - rewrite Hmarks_decomp, fold_right_add_app_single__layer_swap in Hsum.
    lia.
  - split.
    + unfold PrefixChangedByFlips.
      split; [lia|].
      split.
      * rewrite Zlength_sublist by lia. lia.
      * exists (sublist 0 prefix_len marks).
        split.
        -- rewrite Zlength_sublist by lia. lia.
        -- split.
           ++ rewrite Hmarks_decomp in Hmarkvals.
              apply Forall_app in Hmarkvals. exact (proj1 Hmarkvals).
           ++ split; [reflexivity|].
              intros j Hj.
              rewrite Znth_sublist0 by lia.
              rewrite Znth_sublist0 by lia.
              apply Hpoint. lia.
    + unfold FlippedCommand.
      assert (Hlastmark : Znth prefix_len marks 0 = 0 \/
          Znth prefix_len marks 0 = 1).
      {
        rewrite Hmarks_decomp in Hmarkvals.
        apply Forall_app in Hmarkvals.
        pose proof (proj2 Hmarkvals) as Htail.
        inversion Htail as [|x l Hlast Hrest]. exact Hlast.
      }
      specialize (Hpoint prefix_len ltac:(lia)).
      destruct Hlastmark as [Hflip|Hflip].
      * left. split; [exact Hflip|].
        apply (proj1 Hpoint Hflip).
      * right. split; [exact Hflip|].
        apply (proj2 Hpoint Hflip).
Qed.
Lemma fold_right_add_nonneg__layer_swap :
  forall xs,
    Forall (fun x => 0 <= x) xs ->
    0 <= fold_right Z.add 0 xs.
Proof.
  intros xs Hxs. induction Hxs; simpl; lia.
Qed.
Lemma prefix_changed_flips_nonneg__layer_swap :
  forall commands modified prefix_len flips,
    PrefixChangedByFlips commands modified prefix_len flips ->
    0 <= flips.
Proof.
  intros commands modified prefix_len flips
    (_ & _ & marks & _ & Hmarks & Hsum & _).
  assert (Hnonneg : Forall (fun x => 0 <= x) marks).
  {
    eapply Forall_impl; [|exact Hmarks].
    intros x [Hx|Hx]; lia.
  }
  pose proof (fold_right_add_nonneg__layer_swap marks Hnonneg).
  lia.
Qed.
Lemma turtle_next_complete_reachable_iff__layer_swap :
  forall commands prefix_len change_limit next_flips next_direction next_slot,
    0 <= prefix_len < Zlength commands ->
    0 <= change_limit ->
    (forall k, 0 <= k < Zlength commands ->
      Znth k commands 0 = 70 \/ Znth k commands 0 = 84) ->
    0 <= next_flips <= change_limit ->
    0 <= next_direction < 2 ->
    0 <= next_slot < TurtleWidth commands ->
    (TurtleNextReachable commands prefix_len change_limit
      ((((change_limit + 1) * 2) * TurtleWidth commands) * 2)
      next_flips next_direction next_slot <->
     PrefixReachable commands (prefix_len + 1)
      next_flips next_direction next_slot).
Proof.
  intros commands prefix_len change_limit next_flips next_direction next_slot
    Hprefix Hchange Halphabet Hnextflips Hnextdir Hnextslot.
  split.
  - intros (flips & direction & slot & flip & effective & Hflips & Hdir &
      Hslot & Hflip & Hrank & Hreachable & Hnextflips_eq &
      Hnextflips_le & Hflipped & Hencoded).
    destruct Hreachable as
      (modified & position & final_direction & Hchanged & Hstate &
       Hposition & Hdirection).
    assert (Hchanged_next : PrefixChangedByFlips commands
      (modified ++ (effective :: nil)) (prefix_len + 1) next_flips).
    {
      rewrite Hnextflips_eq.
      eapply prefix_changed_extend__layer_swap; eauto.
    }
    unfold PrefixReachable.
    destruct Hdirection as [(Hdir0 & Hfinal0)|(Hdir1 & Hfinal1)];
      destruct Hencoded as
        [(Heffective & Hnextdirection & Hnextslot_eq)|
         (Heffective & Hnextdirection & Hmove)];
      subst direction final_direction effective.
    + exists (modified ++ (84 :: nil)), (next_slot - Zlength commands), (-1).
      split; [exact Hchanged_next|]. split.
      * eapply turtle_state_extend__layer_swap; [exact Hstate|].
        left. repeat split; lia.
      * split; [lia|]. right. split; lia.
    + destruct Hmove as [(Hdir_again & Hnextslot_eq)|
                         (Hdir_bad & Hnextslot_eq)]; try lia.
      exists (modified ++ (70 :: nil)), (next_slot - Zlength commands), 1.
      split; [exact Hchanged_next|]. split.
      * eapply turtle_state_extend__layer_swap; [exact Hstate|].
        right. repeat split; lia.
      * split; [lia|]. left. split; lia.
    + exists (modified ++ (84 :: nil)), (next_slot - Zlength commands), 1.
      split; [exact Hchanged_next|]. split.
      * eapply turtle_state_extend__layer_swap; [exact Hstate|].
        left. repeat split; lia.
      * split; [lia|]. left. split; lia.
    + destruct Hmove as [(Hdir_bad & Hnextslot_eq)|
                         (Hdir_again & Hnextslot_eq)]; try lia.
      exists (modified ++ (70 :: nil)), (next_slot - Zlength commands), (-1).
      split; [exact Hchanged_next|]. split.
      * eapply turtle_state_extend__layer_swap; [exact Hstate|].
        right. repeat split; lia.
      * split; [lia|]. right. split; lia.
  - intros (modified & next_position & final_direction & Hchanged & Hstate &
      Hposition & Hdirection).
    destruct (prefix_changed_unextend__layer_swap commands modified prefix_len
      next_flips Hprefix Hchanged) as
      (before & flips & flip & effective & Hmodified & Hflips_eq &
       Hchanged_before & Hflipped).
    assert (Heffective : effective = 70 \/ effective = 84).
    {
      unfold FlippedCommand in Hflipped.
      destruct Hflipped as [(Hflip0 & Heff)|(Hflip1 & Hcases)].
      - subst effective.
        exact (Halphabet prefix_len Hprefix).
      - destruct Hcases as [(Hcmd70 & Heff84)|(Hcmd84 & Heff70)];
          subst; auto.
    }
    rewrite Hmodified in Hstate.
    destruct (turtle_state_unextend__layer_swap before effective
      next_position final_direction Heffective Hstate) as
      (position & direction_value & Hstate_before & Hstep).
    pose proof (turtle_state_endpoint_bound__layer_swap before position
      direction_value Hstate_before) as Hendpoint.
    destruct Hendpoint as (Hposition_bound & Hdirection_value).
    pose proof Hchanged_before as Hchanged_before_copy.
    destruct Hchanged_before as
      (Hbefore_prefix & Hbefore_len & marks & Hmarks_len & Hmarks_vals &
       Hmarks_sum & Hbefore_point).
    assert (Hflips_nonneg : 0 <= flips).
    {
      exact (prefix_changed_flips_nonneg__layer_swap commands before
        prefix_len flips Hchanged_before_copy).
    }
    assert (Hwidth_positive : 0 < TurtleWidth commands).
    { unfold TurtleWidth. pose proof (Zlength_nonneg commands). lia. }
    assert (Hflip_bounds : 0 <= flip < 2).
    {
      pose proof Hflipped as Hflipped_copy.
      unfold FlippedCommand in Hflipped_copy.
      intuition lia.
    }
    assert (Hflips_bounds : 0 <= flips <= change_limit) by lia.
    assert (Hslot_bounds :
      0 <= position + Zlength commands < TurtleWidth commands).
    { unfold TurtleWidth. lia. }
    destruct Hdirection_value as [Hdirection_plus|Hdirection_minus].
    + exists flips, 0, (position + Zlength commands), flip, effective.
      split; [exact Hflips_bounds|]. split; [lia|]. split.
      * exact Hslot_bounds.
      * split; [lia|]. split.
        -- unfold TurtleTransitionRank, TurtleCellIndex.
           nia.
        -- split.
           ++ unfold PrefixReachable.
              exists before, position, direction_value.
              split; [exact Hchanged_before_copy|].
              split; [exact Hstate_before|]. split; [lia|].
              left. split; lia.
           ++ split; [lia|]. split; [lia|].
              split; [exact Hflipped|].
              destruct Hstep as
                [(Heff84 & Hnextpos & Hnextdirection)|
                 (Heff70 & Hnextpos & Hnextdirection)];
                destruct Hdirection as
                  [(Hnextdir0 & Hfinalplus)|(Hnextdir1 & Hfinalminus)];
                subst direction_value final_direction;
                unfold TurtleEncodedStep.
              ** left. repeat split; try exact Heff84; lia.
              ** lia.
              ** right. repeat split; try exact Heff70; try lia.
              ** lia.
    + exists flips, 1, (position + Zlength commands), flip, effective.
      split; [exact Hflips_bounds|]. split; [lia|]. split.
      * exact Hslot_bounds.
      * split; [lia|]. split.
        -- unfold TurtleTransitionRank, TurtleCellIndex.
           nia.
        -- split.
           ++ unfold PrefixReachable.
              exists before, position, direction_value.
              split; [exact Hchanged_before_copy|].
              split; [exact Hstate_before|]. split; [lia|].
              right. split; lia.
           ++ split; [lia|]. split; [lia|].
              split; [exact Hflipped|].
              destruct Hstep as
                [(Heff84 & Hnextpos & Hnextdirection)|
                 (Heff70 & Hnextpos & Hnextdirection)];
                destruct Hdirection as
                  [(Hnextdir0 & Hfinalplus)|(Hnextdir1 & Hfinalminus)];
                subst direction_value final_direction;
                unfold TurtleEncodedStep.
              ** lia.
              ** left. repeat split; try exact Heff84; lia.
              ** lia.
              ** right. repeat split; try exact Heff70; try lia.
Qed.
Lemma turtle_next_complete_layer__layer_swap :
  forall commands prefix_len change_limit next_table,
    0 <= prefix_len < Zlength commands ->
    0 <= change_limit ->
    (forall k, 0 <= k < Zlength commands ->
      Znth k commands 0 = 70 \/ Znth k commands 0 = 84) ->
    TurtleNextPrefix commands prefix_len change_limit
      ((((change_limit + 1) * 2) * TurtleWidth commands) * 2) next_table ->
    TurtleLayerMeaning commands (prefix_len + 1) change_limit next_table.
Proof.
  intros commands prefix_len change_limit next_table Hprefix Hchange
    Halphabet Hnext.
  unfold TurtleLayerMeaning.
  intros flips direction slot Hflips Hdirection Hslot.
  unfold TurtleNextPrefix in Hnext.
  specialize (Hnext flips direction slot Hflips Hdirection Hslot).
  destruct Hnext as [Hbit Hmeaning].
  split; [exact Hbit|].
  rewrite Hmeaning.
  apply turtle_next_complete_reachable_iff__layer_swap; auto.
Qed.
Lemma turtle_answer_prefix_zero__answer_init :
  forall commands change_limit,
    TurtleAnswerPrefix commands change_limit 0 0.
Proof.
  intros commands change_limit.
  unfold TurtleAnswerPrefix.
  split.
  - lia.
  - split.
    + intros flips direction slot Helig Hdone.
      unfold TurtleTerminalEligible in Helig.
      destruct Helig as (Hflips & Hdirection & Hslot & Heven & Hreachable).
      unfold TurtleCellIndex, TurtleWidth in Hdone, Hslot.
      assert (Hfactor : 0 <= flips * 2 + direction) by lia.
      assert (Hwidth : 0 <= 2 * Zlength commands + 1) by lia.
      assert (Hproduct :
        0 <= (flips * 2 + direction) * (2 * Zlength commands + 1)).
      { apply Z.mul_nonneg_nonneg; assumption. }
      lia.
    + left; reflexivity.
Qed.
Lemma land_one_zero_even__answer_position :
  forall value, Z.land value 1 = 0 -> Z.even value = true.
Proof.
  intros value Hland.
  replace 1 with (Z.ones 1) in Hland by reflexivity.
  rewrite Z.land_ones in Hland by lia.
  simpl in Hland.
  apply Z.even_spec.
  apply Z.mod_divide in Hland; [|lia].
  destruct Hland as [factor Hfactor].
  exists factor.
  change (value = factor * 2) in Hfactor.
  rewrite Z.mul_comm in Hfactor.
  exact Hfactor.
Qed.
Lemma turtle_cell_index_same_slot__answer_position :
  forall commands flips1 direction1 slot1 flips2 direction2 slot2,
    0 < TurtleWidth commands ->
    0 <= slot1 < TurtleWidth commands ->
    0 <= slot2 < TurtleWidth commands ->
    TurtleCellIndex commands flips1 direction1 slot1 =
      TurtleCellIndex commands flips2 direction2 slot2 ->
    slot1 = slot2.
Proof.
  intros commands flips1 direction1 slot1 flips2 direction2 slot2
    Hwidth Hslot1 Hslot2 Hindex.
  unfold TurtleCellIndex in Hindex.
  assert (Hleft :
    (((flips1 * 2 + direction1) * TurtleWidth commands + slot1)
      mod TurtleWidth commands) = slot1).
  { rewrite Z.add_mod by lia.
    rewrite Z.mod_mul by lia.
    rewrite Z.add_0_l.
    rewrite Z.mod_mod by lia.
    apply Z.mod_small. exact Hslot1. }
  assert (Hright :
    (((flips2 * 2 + direction2) * TurtleWidth commands + slot2)
      mod TurtleWidth commands) = slot2).
  { rewrite Z.add_mod by lia.
    rewrite Z.mod_mul by lia.
    rewrite Z.add_0_l.
    rewrite Z.mod_mod by lia.
    apply Z.mod_small. exact Hslot2. }
  pose proof (f_equal (fun value => value mod TurtleWidth commands) Hindex) as Hmod.
  cbn in Hmod.
  rewrite Hleft, Hright in Hmod.
  exact Hmod.
Qed.
Lemma turtle_layer_nonzero_terminal__answer_position :
  forall commands change_limit table flips direction slot,
    TurtleLayerMeaning commands (Zlength commands) change_limit table ->
    0 <= flips <= change_limit ->
    0 <= direction < 2 ->
    0 <= slot < TurtleWidth commands ->
    Z.even (change_limit - flips) = true ->
    Znth (TurtleCellIndex commands flips direction slot) table 0 <> 0 ->
    TurtleTerminalEligible commands change_limit flips direction slot.
Proof.
  intros commands change_limit table flips direction slot
    Hlayer Hflips Hdirection Hslot Heven Hnonzero.
  unfold TurtleTerminalEligible.
  split; [exact Hflips|].
  split; [exact Hdirection|].
  split; [exact Hslot|].
  split; [exact Heven|].
  unfold TurtleLayerMeaning in Hlayer.
  specialize (Hlayer flips direction slot Hflips Hdirection Hslot).
  destruct Hlayer as [Hvalue Hmeaning].
  apply Hmeaning.
  destruct Hvalue as [Hzero | Hone]; [contradiction|exact Hone].
Qed.
Lemma turtle_terminal_cell_one__answer_position :
  forall commands change_limit table flips direction slot,
    TurtleLayerMeaning commands (Zlength commands) change_limit table ->
    TurtleTerminalEligible commands change_limit flips direction slot ->
    Znth (TurtleCellIndex commands flips direction slot) table 0 = 1.
Proof.
  intros commands change_limit table flips direction slot Hlayer Heligible.
  unfold TurtleTerminalEligible in Heligible.
  destruct Heligible as [Hflips [Hdirection [Hslot [_ Hreachable]]]].
  unfold TurtleLayerMeaning in Hlayer.
  specialize (Hlayer flips direction slot Hflips Hdirection Hslot).
  destruct Hlayer as [_ Hmeaning].
  apply Hmeaning.
  exact Hreachable.
Qed.
Lemma turtle_answer_prefix_consume_cell__answer_position :
  forall commands change_limit done old_answer new_answer,
    TurtleAnswerPrefix commands change_limit done old_answer ->
    old_answer <= new_answer ->
    (forall flips direction slot,
      TurtleTerminalEligible commands change_limit flips direction slot ->
      TurtleCellIndex commands flips direction slot = done ->
      Z.abs (slot - Zlength commands) <= new_answer) ->
    (new_answer = old_answer \/
     exists flips direction slot,
       TurtleTerminalEligible commands change_limit flips direction slot /\
       TurtleCellIndex commands flips direction slot = done /\
       new_answer = Z.abs (slot - Zlength commands)) ->
    TurtleAnswerPrefix commands change_limit (done + 1) new_answer.
Proof.
  intros commands change_limit done old_answer new_answer
    Hprefix Hold_le Hnew_bound Hattained.
  unfold TurtleAnswerPrefix in Hprefix |- *.
  destruct Hprefix as [Hold_nonnegative [Hold_bound Hold_attained]].
  split; [lia|].
  split.
  - intros flips direction slot Heligible Hbefore.
    destruct (Z_lt_ge_dec
      (TurtleCellIndex commands flips direction slot) done) as [Hold | Hnew].
    + eapply Z.le_trans.
      * exact (Hold_bound flips direction slot Heligible Hold).
      * exact Hold_le.
    + apply Hnew_bound with (flips := flips) (direction := direction) (slot := slot).
      * exact Heligible.
      * lia.
  - destruct Hattained as [-> | Hnew_attained].
    + destruct Hold_attained as [Hzero | Hold_attained].
      * left; exact Hzero.
      * right.
        destruct Hold_attained as
          [flips [direction [slot [Heligible [Hbefore Hvalue]]]]].
        exists flips, direction, slot.
        split; [exact Heligible|].
        split; [lia|exact Hvalue].
    + right.
      destruct Hnew_attained as
        [flips [direction [slot [Heligible [Hindex Hvalue]]]]].
      exists flips, direction, slot.
      split; [exact Heligible|].
      split; [lia|exact Hvalue].
Qed.
Lemma turtle_answer_prefix_skip_ineligible__answer_loop_exits :
  forall commands change_limit c answer,
    0 <= c ->
    c <= change_limit ->
    0 < TurtleWidth commands ->
    Z.land (change_limit - c) 1 <> 0 ->
    TurtleAnswerPrefix commands change_limit
      ((c * 2) * TurtleWidth commands) answer ->
    TurtleAnswerPrefix commands change_limit
      (((c + 1) * 2) * TurtleWidth commands) answer.
Proof.
  intros commands change_limit c answer Hc Hcle HW Hodd Hprefix.
  unfold TurtleAnswerPrefix in *.
  destruct Hprefix as [Hans_nonneg [Hbound Hwitness]].
  split; [exact Hans_nonneg |].
  split.
  - intros flips direction slot Heligible Hnew.
    destruct (Z_lt_ge_dec
      (TurtleCellIndex commands flips direction slot)
      ((c * 2) * TurtleWidth commands)) as [Hold | Hold].
    + eapply Hbound; eauto.
    + exfalso.
      unfold TurtleTerminalEligible in Heligible.
      destruct Heligible as
        [Hflips [Hdirection [Hslot [Heven Hreachable]]]].
      unfold TurtleCellIndex in Hold, Hnew.
      assert (flips = c) as Hflips_eq by nia.
      subst flips.
      apply Hodd.
      apply Z.even_spec in Heven.
      destruct Heven as [q Hq].
      replace 1 with (Z.ones 1) by reflexivity.
      rewrite Z.land_ones by lia.
      simpl.
      apply Z.mod_divide; [lia |].
      exists q.
      nia.
  - destruct Hwitness as [Hzero | Hwitness].
    + left. exact Hzero.
    + right.
      destruct Hwitness as
        [flips [direction [slot [Heligible [Hold Hans]]]]].
      exists flips, direction, slot.
      split; [exact Heligible |].
      split; [nia | exact Hans].
Qed.
Lemma change_counts_compress__final_spec :
  forall commands modified counts,
    Zlength modified = Zlength commands ->
    Zlength counts = Zlength commands ->
    Forall (fun x => 0 <= x) counts ->
    (forall i, 0 <= i < Zlength commands ->
      (Z.even (Znth i counts 0) = true ->
        Znth i modified 0 = Znth i commands 0) /\
      (Z.even (Znth i counts 0) = false ->
        ((Znth i commands 0 = 70 /\ Znth i modified 0 = 84) \/
         (Znth i commands 0 = 84 /\ Znth i modified 0 = 70)))) ->
    exists marks,
      Zlength marks = Zlength commands /\
      Forall (fun x => x = 0 \/ x = 1) marks /\
      fold_right Z.add 0 marks <= fold_right Z.add 0 counts /\
      Z.even (fold_right Z.add 0 counts - fold_right Z.add 0 marks) = true /\
      (forall i, 0 <= i < Zlength commands ->
        (Znth i marks 0 = 0 ->
          Znth i modified 0 = Znth i commands 0) /\
        (Znth i marks 0 = 1 ->
          ((Znth i commands 0 = 70 /\ Znth i modified 0 = 84) \/
           (Znth i commands 0 = 84 /\ Znth i modified 0 = 70)))).
Proof.
  induction commands as [|command commands IH]; intros modified counts Hmodified Hcounts Hnonneg Hpoint.
  - rewrite !Zlength_correct in Hmodified, Hcounts.
    destruct modified; simpl in Hmodified; try lia.
    destruct counts; simpl in Hcounts; try lia.
    exists nil. split; [reflexivity|]. split; [constructor|]. split; [lia|].
    split; [reflexivity|].
    intros i Hi. rewrite Zlength_nil in Hi. lia.
  - rewrite !Zlength_correct in Hmodified, Hcounts.
    destruct modified as [|modified_hd modified]; simpl in Hmodified; try lia.
    destruct counts as [|count counts]; simpl in Hcounts; try lia.
    inversion Hnonneg as [|? ? Hcount Hcounts_nonneg]; subst.
    assert (Hhead := Hpoint 0).
    rewrite !Znth0_cons in Hhead.
    specialize (Hhead ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg commands); lia)).
    assert (Htail : forall i, 0 <= i < Zlength commands ->
      (Z.even (Znth i counts 0) = true -> Znth i modified 0 = Znth i commands 0) /\
      (Z.even (Znth i counts 0) = false ->
        ((Znth i commands 0 = 70 /\ Znth i modified 0 = 84) \/
         (Znth i commands 0 = 84 /\ Znth i modified 0 = 70)))).
    { intros i Hi. specialize (Hpoint (i + 1)).
      rewrite !Znth_cons in Hpoint by lia.
      replace (i + 1 - 1) with i in Hpoint by lia.
      apply Hpoint. rewrite Zlength_cons. lia. }
    specialize (IH modified counts ltac:(rewrite !Zlength_correct; lia)
      ltac:(rewrite !Zlength_correct; lia) Hcounts_nonneg Htail).
    destruct IH as [marks [Hmarks_len [Hmarks_values [Hmarks_le [Hparity Hmarks_point]]]]].
    destruct (Z.even count) eqn:Hcount_even.
    + exists (0 :: marks). split.
      * rewrite !Zlength_cons, Hmarks_len. reflexivity.
      * split; [constructor; [left; reflexivity | exact Hmarks_values]|].
        split; [simpl; lia|]. split.
        -- simpl. replace (count + fold_right Z.add 0 counts - fold_right Z.add 0 marks)
          with (count + (fold_right Z.add 0 counts - fold_right Z.add 0 marks)) by lia.
           rewrite Z.even_add, Hcount_even, Hparity. reflexivity.
        -- intros i Hi. destruct (Z.eq_dec i 0) as [-> | Hine].
           ++ rewrite !Znth0_cons. split; [intros _; exact (proj1 Hhead eq_refl) | lia].
           ++ assert (0 < i) by lia.
              rewrite !Znth_cons by lia.
              apply Hmarks_point. rewrite Zlength_cons in Hi. lia.
    + exists (1 :: marks). split.
      * rewrite !Zlength_cons, Hmarks_len. reflexivity.
      * split; [constructor; [right; reflexivity | exact Hmarks_values]|].
        split.
        -- change (1 + fold_right Z.add 0 marks <= count + fold_right Z.add 0 counts).
           assert (count <> 0) by (intros ->; discriminate). lia.
        -- split.
           ++ change (Z.even (count + fold_right Z.add 0 counts -
                (1 + fold_right Z.add 0 marks)) = true).
              replace (count + fold_right Z.add 0 counts - (1 + fold_right Z.add 0 marks))
                with ((count - 1) + (fold_right Z.add 0 counts - fold_right Z.add 0 marks)) by lia.
              rewrite Z.even_add, Z.even_sub, Hcount_even, Hparity. reflexivity.
           ++ intros i Hi. destruct (Z.eq_dec i 0) as [-> | Hine].
              ** rewrite !Znth0_cons. split; [lia | intros _; exact (proj2 Hhead eq_refl)].
              ** assert (0 < i) by lia.
                 rewrite !Znth_cons by lia.
                 apply Hmarks_point. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma change_counts_expand__final_spec :
  forall commands modified marks n,
    commands <> nil ->
    Zlength modified = Zlength commands ->
    Zlength marks = Zlength commands ->
    Forall (fun x => x = 0 \/ x = 1) marks ->
    fold_right Z.add 0 marks <= n ->
    Z.even (n - fold_right Z.add 0 marks) = true ->
    (forall i, 0 <= i < Zlength commands ->
      (Znth i marks 0 = 0 -> Znth i modified 0 = Znth i commands 0) /\
      (Znth i marks 0 = 1 ->
        ((Znth i commands 0 = 70 /\ Znth i modified 0 = 84) \/
         (Znth i commands 0 = 84 /\ Znth i modified 0 = 70)))) ->
    exists counts,
      Zlength counts = Zlength commands /\
      Forall (fun x => 0 <= x) counts /\
      fold_right Z.add 0 counts = n /\
      forall i, 0 <= i < Zlength commands ->
        (Z.even (Znth i counts 0) = true ->
          Znth i modified 0 = Znth i commands 0) /\
        (Z.even (Znth i counts 0) = false ->
          ((Znth i commands 0 = 70 /\ Znth i modified 0 = 84) \/
           (Znth i commands 0 = 84 /\ Znth i modified 0 = 70))).
Proof.
  intros [|command commands] modified marks n Hcommands Hmodified Hmarks_len Hmarks_values Hle Heven Hpoint;
    [contradiction|].
  rewrite !Zlength_correct in Hmodified, Hmarks_len.
  destruct modified as [|modified_hd modified]; simpl in Hmodified; try lia.
  destruct marks as [|mark marks]; simpl in Hmarks_len; try lia.
  inversion Hmarks_values as [|? ? Hmark Hmarks]; subst.
  set (padding := n - fold_right Z.add 0 (mark :: marks)).
  exists ((mark + padding) :: marks).
  split.
  - rewrite !Zlength_correct. simpl. lia.
  - split.
    + constructor.
      * change (0 <= mark + padding). unfold padding.
        change (mark + fold_right Z.add 0 marks <= n) in Hle.
        change (0 <= mark + (n - (mark + fold_right Z.add 0 marks))). lia.
      * eapply Forall_impl; [|exact Hmarks].
        intros x Hx. destruct Hx; subst; lia.
    + split.
      * unfold padding. simpl. lia.
      * intros i Hi. specialize (Hpoint i Hi).
        assert (Hmark_at : Znth i (mark :: marks) 0 = 0 \/ Znth i (mark :: marks) 0 = 1).
        { apply (proj1 (Forall_Znth (fun x => x = 0 \/ x = 1) 0 (mark :: marks))).
          - constructor; assumption.
          - rewrite !Zlength_correct in Hi |- *. simpl in *. lia. }
        assert (Heven_at : Z.even (Znth i ((mark + padding) :: marks) 0) =
                           Z.even (Znth i (mark :: marks) 0)).
        { destruct (Z.eq_dec i 0) as [-> | Hine].
          - rewrite !Znth0_cons. unfold padding.
            rewrite Z.even_add, Heven. destruct (Z.even mark); reflexivity.
          - assert (0 < i) by lia. rewrite !Znth_cons by lia. reflexivity. }
        rewrite Heven_at. destruct Hmark_at as [Hzero | Hone]; rewrite Hzero || rewrite Hone.
        -- split; [intros _; exact (proj1 Hpoint Hzero) | discriminate].
        -- split; [discriminate | intros _; exact (proj2 Hpoint Hone)].
Qed.
Lemma turtle_state_direction_pm1__final_spec :
  forall commands position direction,
    TurtleState commands position direction ->
    direction = 1 \/ direction = -1.
Proof.
  intros commands position direction Hstate.
  unfold TurtleState in Hstate.
  destruct Hstate as [states [Hlen [Hstart [Hstep Hend]]]].
  assert (Hdir : forall i, 0 <= i <= Zlength commands ->
      snd (Znth i states (0, 1)) = 1 \/ snd (Znth i states (0, 1)) = -1).
  { intros i Hi.
    remember (Z.to_nat i) as ni eqn:Hni.
    replace i with (Z.of_nat ni) in Hi |- * by lia. clear Hni i.
    induction ni as [|ni IH].
    - simpl. rewrite Hstart. simpl. auto.
    - replace (Z.of_nat (S ni)) with (Z.of_nat ni + 1) by (rewrite Nat2Z.inj_succ; lia).
      assert (Hbound : 0 <= Z.of_nat ni < Zlength commands) by lia.
      specialize (Hstep (Z.of_nat ni) Hbound).
      destruct (Znth (Z.of_nat ni) states (0, 1)) as [p d] eqn:Hpd.
      simpl in Hstep.
      rewrite Hstep. destruct (Z.eqb (Znth (Z.of_nat ni) commands 0) 84); simpl.
      + specialize (IH ltac:(lia)). simpl in IH.
        destruct IH; [right | left]; lia.
      + specialize (IH ltac:(lia)). simpl in IH. exact IH. }
  specialize (Hdir (Zlength commands) ltac:(pose proof (Zlength_nonneg commands); lia)).
  rewrite Hend in Hdir. simpl in Hdir. exact Hdir.
Qed.
Lemma turtle_state_to_end__final_spec :
  forall commands position direction,
    TurtleState commands position direction -> TurtleEnd commands position.
Proof.
  intros commands position direction Hstate.
  unfold TurtleState in Hstate. unfold TurtleEnd.
  destruct Hstate as [states [Hlen [Hstart [Hstep Hend]]]].
  exists states. repeat split; try assumption.
  rewrite Hend. reflexivity.
Qed.
Lemma turtle_end_to_state__final_spec :
  forall commands position,
    TurtleEnd commands position ->
    exists direction, TurtleState commands position direction.
Proof.
  intros commands position Hend.
  unfold TurtleEnd in Hend.
  destruct Hend as [states [Hlen [Hstart [Hstep Hposition]]]].
  exists (snd (Znth (Zlength commands) states (0, 1))).
  unfold TurtleState. exists states. repeat split; try assumption.
  destruct (Znth (Zlength commands) states (0, 1)) as [p d] eqn:Hterminal.
  simpl in Hposition. subst p. reflexivity.
Qed.
Lemma fold_right_nonnegative__final_spec :
  forall values, Forall (fun x => 0 <= x) values ->
    0 <= fold_right Z.add 0 values.
Proof.
  intros values Hvalues. induction Hvalues; simpl; lia.
Qed.
Lemma turtle_state_position_bound__final_spec :
  forall commands position direction,
    TurtleState commands position direction ->
    - Zlength commands <= position <= Zlength commands.
Proof.
  intros commands position direction Hstate.
  unfold TurtleState in Hstate.
  destruct Hstate as [states [Hlen [Hstart [Hstep Hend]]]].
  assert (Hinv : forall i, 0 <= i <= Zlength commands ->
      -i <= fst (Znth i states (0, 1)) <= i /\
      (snd (Znth i states (0, 1)) = 1 \/ snd (Znth i states (0, 1)) = -1)).
  { intros i Hi.
    remember (Z.to_nat i) as ni eqn:Hni.
    replace i with (Z.of_nat ni) in Hi |- * by lia. clear Hni i.
    induction ni as [|ni IH].
    - simpl. rewrite Hstart. simpl. lia.
    - replace (Z.of_nat (S ni)) with (Z.of_nat ni + 1) by (rewrite Nat2Z.inj_succ; lia).
      assert (Hbound : 0 <= Z.of_nat ni < Zlength commands) by lia.
      specialize (Hstep (Z.of_nat ni) Hbound).
      destruct (Znth (Z.of_nat ni) states (0, 1)) as [p d] eqn:Hpd.
      simpl in Hstep.
      specialize (IH ltac:(lia)). simpl in IH.
      rewrite Hstep. destruct (Z.eqb (Znth (Z.of_nat ni) commands 0) 84); simpl; nia. }
  specialize (Hinv (Zlength commands) ltac:(pose proof (Zlength_nonneg commands); lia)).
  rewrite Hend in Hinv. simpl in Hinv. tauto.
Qed.
Lemma turtle_state_exists__final_spec :
  forall commands, exists position direction,
    TurtleState commands position direction.
Proof.
  intros commands.
  set (step := fun (state : Z * Z) (command : Z) =>
    let '(p, d) := state in
    if Z.eqb command 84 then (p, -d) else (p + d, d)).
  set (run := fix run (cs : list Z) (state : Z * Z) {struct cs} : list (Z * Z) :=
    match cs with
    | nil => state :: nil
    | command :: tail => state :: run tail (step state command)
    end).
  assert (Hrun_len : forall cs state,
      Zlength (run cs state) = Zlength cs + 1).
  { intros cs. induction cs as [|command tail IH]; intros state.
    - cbn [run]. rewrite !Zlength_cons, !Zlength_nil. lia.
    - cbn [run]. rewrite !Zlength_cons, IH. lia. }
  assert (Hrun_head : forall cs state, Znth 0 (run cs state) (0, 1) = state).
  { intros [|command tail] state; cbn [run]; apply Znth0_cons. }
  assert (Hrun_step : forall cs state i,
      0 <= i < Zlength cs ->
      Znth (i + 1) (run cs state) (0, 1) =
      step (Znth i (run cs state) (0, 1)) (Znth i cs 0)).
  { intros cs. induction cs as [|command tail IH]; intros state i Hi.
    - rewrite Zlength_nil in Hi. lia.
    - destruct (Z.eq_dec i 0) as [-> | Hine].
      + cbn [run]. rewrite !Znth0_cons. rewrite Znth_cons by lia.
        replace (0 + 1 - 1) with 0 by lia. apply Hrun_head.
      + assert (0 < i) by lia.
        cbn [run]. rewrite !Znth_cons by lia.
        replace (i + 1 - 1) with ((i - 1) + 1) by lia.
        apply IH. rewrite Zlength_cons in Hi. lia. }
  set (states := run commands (0, 1)).
  set (terminal := Znth (Zlength commands) states (0, 1)).
  exists (fst terminal), (snd terminal).
  unfold TurtleState. exists states. repeat split.
  - unfold states. apply Hrun_len.
  - unfold states. apply Hrun_head.
  - intros i Hi. unfold states. rewrite Hrun_step by exact Hi.
    unfold step. destruct (Znth i (run commands (0, 1)) (0, 1)); reflexivity.
  - unfold terminal. destruct (Znth (Zlength commands) states (0, 1)); reflexivity.
Qed.
Lemma changed_exactly_exists__final_spec :
  forall commands n,
    commands <> nil ->
    0 <= n ->
    Forall (fun x => x = 70 \/ x = 84) commands ->
    exists modified, ChangedExactly commands modified n.
Proof.
  intros [|command commands] n Hcommands Hn Halphabet; [contradiction|].
  inversion Halphabet as [|? ? Hcommand Hcommands_alpha]; subst.
  set (zeros := repeat 0%Z (length commands)).
  assert (Hzeros_len : Zlength zeros = Zlength commands).
  { unfold zeros. rewrite !Zlength_correct, repeat_length. reflexivity. }
  assert (Hzeros_nonneg : Forall (fun x => 0 <= x) zeros).
  { assert (forall m, Forall (fun x : Z => 0 <= x) (repeat 0 m)) as Hrepeat.
    { intros m. induction m as [|m IH]; simpl.
      - apply Forall_nil.
      - apply Forall_cons; [lia | exact IH]. }
    unfold zeros. apply Hrepeat. }
  assert (Hzeros_sum : fold_right Z.add 0 zeros = 0).
  { assert (forall m, fold_right Z.add 0 (repeat 0 m) = 0) as Hrepeat_sum.
    { intros m. induction m; simpl; auto. }
    unfold zeros. apply Hrepeat_sum. }
  destruct (Z.even n) eqn:Hparity.
  - exists (command :: commands). unfold ChangedExactly.
    split; [reflexivity|]. exists (n :: zeros). split.
    + rewrite !Zlength_cons, Hzeros_len. reflexivity.
    + split; [constructor; assumption|]. split.
      * simpl. rewrite Hzeros_sum. lia.
      * intros i Hi. destruct (Z.eq_dec i 0) as [-> | Hine].
        -- rewrite !Znth0_cons. split; [intros _; reflexivity | intros Hfalse; rewrite Hparity in Hfalse; discriminate].
        -- assert (0 < i) by lia. rewrite !Znth_cons by lia.
           unfold zeros. rewrite Znth_repeat. split; [intros _; reflexivity | discriminate].
  - destruct Hcommand as [-> | ->].
    + exists (84 :: commands). unfold ChangedExactly.
      split; [reflexivity|]. exists (n :: zeros). split.
      * rewrite !Zlength_cons, Hzeros_len. reflexivity.
      * split; [constructor; assumption|]. split.
        -- simpl. rewrite Hzeros_sum. lia.
        -- intros i Hi. destruct (Z.eq_dec i 0) as [-> | Hine].
           ++ rewrite !Znth0_cons. split.
              ** intros Htrue. rewrite Hparity in Htrue. discriminate.
              ** intros _. left. auto.
           ++ assert (0 < i) by lia. rewrite !Znth_cons by lia.
              unfold zeros. rewrite Znth_repeat. split; [intros _; reflexivity | discriminate].
    + exists (70 :: commands). unfold ChangedExactly.
      split; [reflexivity|]. exists (n :: zeros). split.
      * rewrite !Zlength_cons, Hzeros_len. reflexivity.
      * split; [constructor; assumption|]. split.
        -- simpl. rewrite Hzeros_sum. lia.
        -- intros i Hi. destruct (Z.eq_dec i 0) as [-> | Hine].
           ++ rewrite !Znth0_cons. split.
              ** intros Htrue. rewrite Hparity in Htrue. discriminate.
              ** intros _. right. auto.
           ++ assert (0 < i) by lia. rewrite !Znth_cons by lia.
              unfold zeros. rewrite Znth_repeat. split; [intros _; reflexivity | discriminate].
Qed.
Lemma turtle_answer_complete_spec__final_spec :
  forall commands change_limit table answer,
    Pre change_limit commands ->
    TurtleLayerMeaning commands (Zlength commands) change_limit table ->
    TurtleAnswerPrefix commands change_limit
      (((change_limit + 1) * 2) * TurtleWidth commands) answer ->
    Spec change_limit commands answer.
Proof.
  intros commands change_limit table answer Hpre Hlayer Hanswer.
  unfold Pre in Hpre.
  destruct Hpre as [[Hlen_lower Hlen_upper] [[Hchange_lower Hchange_upper] Halphabet]].
  assert (Hcommands_nonempty : commands <> nil).
  { intros ->. rewrite Zlength_nil in Hlen_lower. lia. }
  assert (Hcell_complete : forall flips direction slot,
      0 <= flips <= change_limit ->
      0 <= direction < 2 ->
      0 <= slot < TurtleWidth commands ->
      TurtleCellIndex commands flips direction slot <
        ((change_limit + 1) * 2) * TurtleWidth commands).
  { intros flips direction slot Hflips Hdirection Hslot.
    unfold TurtleCellIndex, TurtleWidth in *. nia. }
  assert (Hcandidate_to_terminal : forall modified position,
      ChangedExactly commands modified change_limit ->
      TurtleEnd modified position ->
      exists flips direction slot,
        TurtleTerminalEligible commands change_limit flips direction slot /\
        position = slot - Zlength commands).
  { intros modified position Hchanged Hend.
    unfold ChangedExactly in Hchanged.
    destruct Hchanged as [Hmodified_len [counts [Hcounts_len [Hcounts_nonneg [Hcounts_sum Hcounts_point]]]]].
    pose proof (change_counts_compress__final_spec commands modified counts
      Hmodified_len Hcounts_len Hcounts_nonneg Hcounts_point) as Hcompress.
    destruct Hcompress as [marks [Hmarks_len [Hmarks_values [Hmarks_le [Hmarks_parity Hmarks_point]]]]].
    assert (Hmarks_nonnegative : Forall (fun x => 0 <= x) marks).
    { eapply Forall_impl; [|exact Hmarks_values].
      intros x Hx. destruct Hx; subst; lia. }
    pose proof (fold_right_nonnegative__final_spec marks Hmarks_nonnegative) as Hflips_nonnegative.
    destruct (turtle_end_to_state__final_spec modified position Hend) as [final_direction Hstate].
    pose proof (turtle_state_direction_pm1__final_spec modified position final_direction Hstate) as Hdirection_pm1.
    pose proof (turtle_state_position_bound__final_spec modified position final_direction Hstate) as Hposition_bound.
    assert (Hposition_bound_commands : - Zlength commands <= position <= Zlength commands) by lia.
    destruct Hdirection_pm1 as [Hdirection | Hdirection].
    - exists (fold_right Z.add 0 marks), 0, (position + Zlength commands).
      split.
      + unfold TurtleTerminalEligible. split; [lia|]. split; [lia|].
        split; [unfold TurtleWidth; lia|]. split.
        * rewrite Hcounts_sum in Hmarks_parity. exact Hmarks_parity.
        * unfold PrefixReachable. exists modified, position, final_direction.
          split.
          -- unfold PrefixChangedByFlips. split; [lia|]. split; [exact Hmodified_len|].
             exists marks. split; [exact Hmarks_len|]. split; [exact Hmarks_values|].
             split; [reflexivity|]. exact Hmarks_point.
          -- split; [exact Hstate|]. split; [lia|]. left. split; [reflexivity|exact Hdirection].
      + lia.
    - exists (fold_right Z.add 0 marks), 1, (position + Zlength commands).
      split.
      + unfold TurtleTerminalEligible. split; [lia|]. split; [lia|].
        split; [unfold TurtleWidth; lia|]. split.
        * rewrite Hcounts_sum in Hmarks_parity. exact Hmarks_parity.
        * unfold PrefixReachable. exists modified, position, final_direction.
          split.
          -- unfold PrefixChangedByFlips. split; [lia|]. split; [exact Hmodified_len|].
             exists marks. split; [exact Hmarks_len|]. split; [exact Hmarks_values|].
             split; [reflexivity|]. exact Hmarks_point.
          -- split; [exact Hstate|]. split; [lia|]. right. split; [reflexivity|exact Hdirection].
      + lia. }
  assert (Hterminal_to_candidate : forall flips direction slot,
      TurtleTerminalEligible commands change_limit flips direction slot ->
      exists modified position,
        ChangedExactly commands modified change_limit /\
        TurtleEnd modified position /\
        position = slot - Zlength commands).
  { intros flips direction slot Heligible.
    unfold TurtleTerminalEligible in Heligible.
    destruct Heligible as [Hflips [Hdirection [Hslot [Hparity Hreachable]]]].
    unfold PrefixReachable in Hreachable.
    destruct Hreachable as [modified [position [final_direction
      [Hprefix [Hstate [Hposition Hfinal_direction]]]]]].
    unfold PrefixChangedByFlips in Hprefix.
    destruct Hprefix as [Hprefix_bounds [Hmodified_len [marks
      [Hmarks_len [Hmarks_values [Hmarks_sum Hmarks_point]]]]]].
    pose proof (change_counts_expand__final_spec commands modified marks change_limit
      Hcommands_nonempty Hmodified_len Hmarks_len Hmarks_values ltac:(lia)
      ltac:(rewrite Hmarks_sum; exact Hparity) Hmarks_point) as Hexpand.
    destruct Hexpand as [counts [Hcounts_len [Hcounts_nonnegative [Hcounts_sum Hcounts_point]]]].
    exists modified, position. split.
    - unfold ChangedExactly. split; [exact Hmodified_len|].
      exists counts. split; [exact Hcounts_len|]. split; [exact Hcounts_nonnegative|].
      split; [exact Hcounts_sum|]. exact Hcounts_point.
    - split.
      + apply (turtle_state_to_end__final_spec modified position final_direction Hstate).
      + exact Hposition. }
  unfold TurtleAnswerPrefix in Hanswer.
  destruct Hanswer as [Hanswer_nonnegative [Hanswer_upper Hanswer_attained]].
  unfold Spec, max_value_of_subset, max_object_of_subset.
  destruct Hanswer_attained as [Hanswer_zero | Hanswer_attained].
  - destruct (changed_exactly_exists__final_spec commands change_limit
      Hcommands_nonempty ltac:(lia) Halphabet) as [modified Hchanged].
    destruct (turtle_state_exists__final_spec modified) as [position [direction Hstate]].
    pose proof (turtle_state_to_end__final_spec modified position direction Hstate) as Hend.
    destruct (Hcandidate_to_terminal modified position Hchanged Hend)
      as [current_flips [current_direction [current_slot [Hcurrent_eligible Hposition]]]].
    pose proof (Hanswer_upper current_flips current_direction current_slot Hcurrent_eligible
      (Hcell_complete current_flips current_direction current_slot
        (proj1 Hcurrent_eligible) (proj1 (proj2 Hcurrent_eligible))
        (proj1 (proj2 (proj2 Hcurrent_eligible))))) as Hcurrent_upper.
    assert (Hposition_abs_zero : Z.abs position = 0).
    { rewrite Hposition. rewrite Hanswer_zero in Hcurrent_upper.
      pose proof (Z.abs_nonneg (current_slot - Zlength commands)). lia. }
    exists (modified, position). split.
    + split.
      * split; assumption.
      * intros [other_modified other_position] [Hother_changed Hother_end].
        destruct (Hcandidate_to_terminal other_modified other_position
          Hother_changed Hother_end) as [flips [dir [slot [Heligible Hother_position]]]].
        specialize (Hanswer_upper flips dir slot Heligible
          (Hcell_complete flips dir slot
            (proj1 Heligible) (proj1 (proj2 Heligible))
            (proj1 (proj2 (proj2 Heligible))))).
        simpl. subst other_position. rewrite Hposition_abs_zero, Hanswer_zero in *. exact Hanswer_upper.
    + simpl. rewrite Hposition_abs_zero, Hanswer_zero. reflexivity.
  - destruct Hanswer_attained as [flips [direction [slot
      [Heligible [Hcell_before Hanswer_value]]]]].
    destruct (Hterminal_to_candidate flips direction slot Heligible)
      as [modified [position [Hchanged [Hend Hposition]]]].
    exists (modified, position). split.
    + split.
      * split; assumption.
      * intros [other_modified other_position] [Hother_changed Hother_end].
        destruct (Hcandidate_to_terminal other_modified other_position
          Hother_changed Hother_end) as [other_flips [other_direction [other_slot
          [Hother_eligible Hother_position]]]].
        specialize (Hanswer_upper other_flips other_direction other_slot Hother_eligible
          (Hcell_complete other_flips other_direction other_slot
            (proj1 Hother_eligible) (proj1 (proj2 Hother_eligible))
            (proj1 (proj2 (proj2 Hother_eligible))))).
        simpl. subst other_position. rewrite Hposition, <- Hanswer_value. exact Hanswer_upper.
    + simpl. rewrite Hposition. symmetry. exact Hanswer_value.
Qed.
Lemma command_alphabet_from_Znth__final_spec :
  forall commands,
    (forall i, 0 <= i < Zlength commands ->
      Znth i commands 0 = 70 \/ Znth i commands 0 = 84) ->
    Forall (fun x => x = 70 \/ x = 84) commands.
Proof.
  intros commands Hpoint.
  apply (proj2 (Forall_Znth (fun x => x = 70 \/ x = 84) 0 commands)).
  exact Hpoint.
Qed.
