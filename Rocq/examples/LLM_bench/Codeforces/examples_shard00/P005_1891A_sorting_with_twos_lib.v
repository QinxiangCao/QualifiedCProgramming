Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition PowerOfTwoPrefix (len n : Z) : Prop :=
  exists m : Z, 0 <= m /\ len = Z.pow 2 m /\ len <= n.

Definition OnePrefixDecrement (before after : list Z) : Prop :=
  exists len,
    PowerOfTwoPrefix len (Zlength before) /\
    Zlength after = Zlength before /\
    forall i, 0 <= i < Zlength before ->
      Znth i after 0 = if i <? len then Znth i before 0 - 1 else Znth i before 0.

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 20 /\
  Forall (fun x => 0 <= x <= 1000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\
  (out = 1 <-> exists final,
    clos_refl_trans OnePrefixDecrement a final /\ mono_nondec final).

Definition NonPowerOfTwo (x : Z) : Prop :=
  ~ exists m : Z, 0 <= m /\ x = Z.pow 2 m.

Definition SortingWithTwosPrefix (a : list Z) (upto : Z) : Prop :=
  forall i, 1 <= i < upto ->
    Znth (i - 1) a 0 <= Znth i a 0 \/
    PowerOfTwoPrefix i (Zlength a).

Require Import Coq.micromega.Lia.
Lemma pow_land_pred_zero__power_classification (m : Z) :
  0 <= m -> Z.land (Z.pow 2 m) (Z.pow 2 m - 1) = 0.
Proof.
  intros Hm.
  change (Z.land (Z.pow 2 m) (Z.pred (Z.pow 2 m)) = 0).
  rewrite <- Z.ones_equiv.
  rewrite Z.land_ones by exact Hm.
  apply Z.mod_same.
  apply Z.pow_nonzero.
  - discriminate.
  - exact Hm.
Qed.
Lemma land_pred_power_iff__power_classification (x : Z) :
  1 <= x <= 20 ->
  (Z.land x (x - 1) = 0 <->
   exists m : Z, 0 <= m /\ x = Z.pow 2 m).
Proof.
  intros Hrange.
  split.
  - intros Hland.
    assert (Hcases :
      x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/
      x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/
      x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/
      x = 16 \/ x = 17 \/ x = 18 \/ x = 19 \/ x = 20) by lia.
    destruct Hcases as
      [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
      [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]].
    all: vm_compute in Hland.
    all: try discriminate Hland.
    + exists 0; split; [lia | reflexivity].
    + exists 1; split; [lia | reflexivity].
    + exists 2; split; [lia | reflexivity].
    + exists 3; split; [lia | reflexivity].
    + exists 4; split; [lia | reflexivity].
  - intros (m & Hm & ->).
    apply pow_land_pred_zero__power_classification.
    exact Hm.
Qed.
Lemma Zlength_map__final_success :
  forall (A B : Type) (f : A -> B) (l : list A),
    Zlength (map f l) = Zlength l.
Proof.
  intros.
  rewrite !Zlength_correct, length_map.
  reflexivity.
Qed.
Lemma Znth_map_inbounds__final_success :
  forall (A B : Type) (f : A -> B) (l : list A)
    (i : Z) (da : A) (db : B),
    0 <= i < Zlength l ->
    Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f da)).
  - apply nth_indep.
    rewrite length_map.
    rewrite Zlength_correct in Hi.
    lia.
  - apply map_nth.
Qed.
Lemma one_prefix_decrement_exists__final_success :
  forall (before : list Z) (len : Z),
    PowerOfTwoPrefix len (Zlength before) ->
    exists after,
      OnePrefixDecrement before after /\
      forall i, 0 <= i < Zlength before ->
        Znth i after 0 =
          if i <? len then Znth i before 0 - 1 else Znth i before 0.
Proof.
  intros before len Hpow.
  destruct Hpow as (m & Hm & Hlenpow & Hlen).
  set (after :=
    map (fun x => x - 1) (sublist 0 len before) ++
    sublist len (Zlength before) before).
  exists after.
  assert (Hlen0 : 0 <= len) by
    (subst len; apply Z.pow_nonneg; lia).
  assert (Hafterlen : Zlength after = Zlength before).
  { unfold after.
    rewrite Zlength_app, Zlength_map__final_success.
    rewrite !Zlength_sublist by lia.
    lia. }
  split.
  - unfold OnePrefixDecrement.
    exists len.
    split.
    + exists m. repeat split; assumption.
    + split; [exact Hafterlen |].
      intros i Hi.
      unfold after.
      destruct (i <? len) eqn:Hilt.
      * apply Z.ltb_lt in Hilt.
        rewrite app_Znth1 by
          (rewrite Zlength_map__final_success, Zlength_sublist; lia).
        rewrite (Znth_map_inbounds__final_success
          Z Z (fun x => x - 1) (sublist 0 len before) i 0 0) by
          (rewrite Zlength_sublist; lia).
        rewrite Znth_sublist by lia.
        replace (i + 0) with i by lia.
        reflexivity.
      * apply Z.ltb_ge in Hilt.
        rewrite app_Znth2 by
          (rewrite Zlength_map__final_success, Zlength_sublist; lia).
        rewrite Zlength_map__final_success, Zlength_sublist by lia.
        rewrite Znth_sublist by lia.
        replace (i - (len - 0) + len) with i by lia.
        reflexivity.
  - intros i Hi.
    destruct (i <? len) eqn:Hilt.
    + apply Z.ltb_lt in Hilt.
      unfold after.
      rewrite app_Znth1 by
        (rewrite Zlength_map__final_success, Zlength_sublist; lia).
      rewrite (Znth_map_inbounds__final_success
        Z Z (fun x => x - 1) (sublist 0 len before) i 0 0) by
        (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist by lia.
      replace (i + 0) with i by lia.
      reflexivity.
    + apply Z.ltb_ge in Hilt.
      unfold after.
      rewrite app_Znth2 by
        (rewrite Zlength_map__final_success, Zlength_sublist; lia).
      rewrite Zlength_map__final_success, Zlength_sublist by lia.
      rewrite Znth_sublist by lia.
      replace (i - (len - 0) + len) with i by lia.
      reflexivity.
Qed.
Lemma repeat_prefix_decrement__final_success :
  forall (before : list Z) (len : Z) (k : nat),
    PowerOfTwoPrefix len (Zlength before) ->
    exists after,
      clos_refl_trans OnePrefixDecrement before after /\
      Zlength after = Zlength before /\
      forall i, 0 <= i < Zlength before ->
        Znth i after 0 =
          if i <? len
          then Znth i before 0 - Z.of_nat k
          else Znth i before 0.
Proof.
  intros before len k.
  revert before.
  induction k as [|k IH]; intros before Hpow.
  - exists before.
    split.
    + exists 0%nat.
      hnf.
      reflexivity.
    + split; [reflexivity |].
      intros i Hi.
      destruct (i <? len); simpl; lia.
  - destruct (IH before Hpow) as (mid & Hreach & Hmidlen & Hmid).
    assert (Hpowmid : PowerOfTwoPrefix len (Zlength mid)).
    { rewrite Hmidlen. exact Hpow. }
    destruct (one_prefix_decrement_exists__final_success mid len Hpowmid)
      as (after & Hstep & Hafter).
    exists after.
    split.
    + transitivity mid.
      * exact Hreach.
      * exists 1%nat.
        hnf.
        exists after.
        split; [exact Hstep | reflexivity].
    + split.
      * destruct Hstep as (step_len & _ & Hstep_length & _).
        rewrite Hstep_length, Hmidlen.
        reflexivity.
      * intros i Hi.
        assert (Himid : 0 <= i < Zlength mid) by
          (rewrite Hmidlen; exact Hi).
        specialize (Hafter i Himid).
        specialize (Hmid i Hi).
        destruct (i <? len); simpl in *; lia.
Qed.
Lemma sorting_prefix_reachable_upto__final_success :
  forall (n : nat) (a : list Z),
    Z.of_nat (S n) <= Zlength a ->
    SortingWithTwosPrefix a (Z.of_nat (S n)) ->
    exists final,
      clos_refl_trans OnePrefixDecrement a final /\
      Zlength final = Zlength a /\
      (forall j, 1 <= j < Z.of_nat (S n) ->
        Znth (j - 1) final 0 <= Znth j final 0) /\
      (forall j, Z.of_nat (S n) - 1 <= j < Zlength a ->
        Znth j final 0 = Znth j a 0).
Proof.
  induction n as [|n IH]; intros a Halen Hsort.
  - exists a.
    split.
    + exists 0%nat. hnf. reflexivity.
    + split; [reflexivity |].
      split.
      * intros j Hj. simpl in Hj. lia.
      * intros j Hj. reflexivity.
  - assert (Hprevlen : Z.of_nat (S n) <= Zlength a) by
      (simpl in Halen |-; lia).
    assert (Hprevsort : SortingWithTwosPrefix a (Z.of_nat (S n))).
    { intros j Hj. apply Hsort. simpl in *. lia. }
    destruct (IH a Hprevlen Hprevsort)
      as (mid & Hreach & Hmidlen & Hsorted & Htail).
    set (b := Z.of_nat (S n)).
    destruct (Z_le_gt_dec (Znth (b - 1) mid 0) (Znth b mid 0))
      as [Hboundary | Hboundary].
    + exists mid.
      split; [exact Hreach |].
      split; [exact Hmidlen |].
      split.
      * intros j Hj.
        destruct (Z_lt_ge_dec j b) as [Hjb | Hjb].
        -- apply Hsorted. unfold b in *. lia.
        -- assert (j = b) by (unfold b in *; simpl in Hj; lia).
           subst j. exact Hboundary.
      * intros j Hj.
        apply Htail. unfold b in *.
        rewrite !Nat2Z.inj_succ in Hj |- *.
        lia.
    + assert (Hbpos : 1 <= b) by (unfold b; lia).
      assert (Hblen : b < Zlength a) by
        (unfold b in *; simpl in Halen; lia).
      specialize (Hsort b).
      assert (Hbcur : 1 <= b < Z.of_nat (S (S n))) by
        (unfold b; simpl; lia).
      specialize (Hsort Hbcur).
      destruct Hsort as [Horiginal | Hpower].
      * assert (Htail_left : Znth (b - 1) mid 0 = Znth (b - 1) a 0).
        { apply Htail. unfold b in *. lia. }
        assert (Htail_right : Znth b mid 0 = Znth b a 0).
        { apply Htail. unfold b in *. lia. }
        rewrite Htail_left, Htail_right in Hboundary.
        lia.
      * assert (Hpowermid : PowerOfTwoPrefix b (Zlength mid)).
        { rewrite Hmidlen. exact Hpower. }
        set (gap := Znth (b - 1) mid 0 - Znth b mid 0).
        assert (Hgap : 0 < gap) by (unfold gap; lia).
        destruct (repeat_prefix_decrement__final_success
          mid b (Z.to_nat gap) Hpowermid)
          as (final & Hsteps & Hfinallen & Hfinal).
        exists final.
        split.
        -- transitivity mid; assumption.
        -- split.
           ++ rewrite Hfinallen, Hmidlen. reflexivity.
           ++ split.
              ** intros j Hj.
                 destruct (Z_lt_ge_dec j b) as [Hjb | Hjb].
                 --- assert (Hj0 : 0 <= j - 1 < Zlength mid) by
                       (rewrite Hmidlen; unfold b in *; simpl in Hj; lia).
                     assert (Hj1 : 0 <= j < Zlength mid) by
                       (rewrite Hmidlen; unfold b in *; simpl in Hj; lia).
                     pose proof (Hfinal (j - 1) Hj0) as Hfinal_left.
                     pose proof (Hfinal j Hj1) as Hfinal_right.
                     assert (Hlt0 : (j - 1 <? b) = true) by
                       (apply Z.ltb_lt; lia).
                     assert (Hlt1 : (j <? b) = true) by
                       (apply Z.ltb_lt; lia).
                     rewrite Hlt0 in Hfinal_left.
                     rewrite Hlt1 in Hfinal_right.
                     rewrite Hfinal_left, Hfinal_right.
                     pose proof (Hsorted j) as Hord.
                     assert (Hordarg : 1 <= j < Z.of_nat (S n)) by
                       (unfold b in *; lia).
                     specialize (Hord Hordarg).
                     lia.
                 --- assert (Hjb_eq : j = b) by
                       (unfold b in *; simpl in Hj; lia).
                     subst j.
                     assert (Hbminus : 0 <= b - 1 < Zlength mid) by
                       (rewrite Hmidlen; lia).
                     assert (Hbindex : 0 <= b < Zlength mid) by
                       (rewrite Hmidlen; lia).
                     pose proof (Hfinal (b - 1) Hbminus) as Hfinal_left.
                     pose proof (Hfinal b Hbindex) as Hfinal_right.
                     assert (Hlt : (b - 1 <? b) = true) by
                       (apply Z.ltb_lt; lia).
                     assert (Hge : (b <? b) = false) by
                       (apply Z.ltb_ge; lia).
                     rewrite Hlt in Hfinal_left.
                     rewrite Hge in Hfinal_right.
                     rewrite Hfinal_left, Hfinal_right.
                     rewrite Z2Nat.id by lia.
                     unfold gap.
                     lia.
              ** intros j Hj.
                 assert (Hjmid : 0 <= j < Zlength mid) by
                   (rewrite Hmidlen; lia).
                 specialize (Hfinal j Hjmid).
                 assert (Hge : (j <? b) = false) by
                   (apply Z.ltb_ge; lia).
                 rewrite Hge in Hfinal.
                 rewrite Hfinal.
                 apply Htail. unfold b in *.
                 rewrite !Nat2Z.inj_succ in Hj |- *.
                 lia.
Qed.
Lemma sorting_prefix_reachable_monotone__final_success :
  forall (a : list Z),
    1 <= Zlength a ->
    SortingWithTwosPrefix a (Zlength a) ->
    exists final,
      clos_refl_trans OnePrefixDecrement a final /\
      mono_nondec final.
Proof.
  intros a Hlen Hsort.
  destruct a as [|x xs].
  - rewrite Zlength_nil in Hlen. lia.
  - assert (Hshape : Zlength (x :: xs) = Z.of_nat (S (length xs))).
    { rewrite Zlength_correct. reflexivity. }
    destruct (sorting_prefix_reachable_upto__final_success
      (length xs) (x :: xs))
      as (final & Hreach & Hfinallen & Hsorted & Htail).
    + rewrite <- Hshape. lia.
    + rewrite <- Hshape. exact Hsort.
    + exists final.
      split; [exact Hreach |].
      apply (proj2 (mono_nondec_iff_adjacent final)).
      intros i Hi Hii.
      specialize (Hsorted (i + 1)).
      assert (Harg : 1 <= i + 1 < Z.of_nat (S (length xs))) by
        (rewrite <- Hshape, <- Hfinallen; lia).
      specialize (Hsorted Harg).
      replace (i + 1 - 1) with i in Hsorted by lia.
      exact Hsorted.
Qed.
Lemma one_prefix_decrement_preserves_nonpower_descent__final_failure :
  forall before after i,
    OnePrefixDecrement before after ->
    NonPowerOfTwo i ->
    1 <= i < Zlength before ->
    Znth (i - 1) before 0 > Znth i before 0 ->
    Zlength after = Zlength before /\
    Znth (i - 1) after 0 > Znth i after 0.
Proof.
  intros before after i Hstep Hnonpower Hi Hdescent.
  unfold OnePrefixDecrement in Hstep.
  destruct Hstep as (len & (m & Hm & Hlenpow & Hlenbound) & Hlength & Hvalues).
  split; [exact Hlength|].
  assert (Hineqlen : i <> len).
  { intro Heq.
    apply Hnonpower.
    exists m.
    split; [exact Hm|].
    lia. }
  pose proof (Hvalues (i - 1) ltac:(lia)) as Hleft.
  pose proof (Hvalues i ltac:(lia)) as Hright.
  destruct (Z_lt_ge_dec i len) as [Hilt|Hige].
  - assert (Hleftb : (i - 1 <? len) = true) by (apply Z.ltb_lt; lia).
    assert (Hrightb : (i <? len) = true) by (apply Z.ltb_lt; lia).
    rewrite Hleftb in Hleft.
    rewrite Hrightb in Hright.
    lia.
  - assert (Hleftb : (i - 1 <? len) = false) by (apply Z.ltb_ge; lia).
    assert (Hrightb : (i <? len) = false) by (apply Z.ltb_ge; lia).
    rewrite Hleftb in Hleft.
    rewrite Hrightb in Hright.
    lia.
Qed.
Lemma reachable_preserves_nonpower_descent__final_failure :
  forall before after i,
    clos_refl_trans OnePrefixDecrement before after ->
    NonPowerOfTwo i ->
    1 <= i < Zlength before ->
    Znth (i - 1) before 0 > Znth i before 0 ->
    Zlength after = Zlength before /\
    Znth (i - 1) after 0 > Znth i after 0.
Proof.
  intros before after i Hreach.
  unfold clos_refl_trans in Hreach.
  sets_unfold in Hreach.
  destruct Hreach as [n Hsteps].
  revert before after Hsteps i.
  induction n as [|n IH]; intros before after Hsteps i Hnonpower Hi Hdescent.
  - simpl in Hsteps.
    sets_unfold in Hsteps.
    subst after.
    split; [reflexivity|exact Hdescent].
  - simpl in Hsteps.
    sets_unfold in Hsteps.
    destruct Hsteps as [middle [Hstep Hrest]].
    pose proof
      (one_prefix_decrement_preserves_nonpower_descent__final_failure
         before middle i Hstep Hnonpower Hi Hdescent)
      as [Hmiddlelength Hmiddledescent].
    specialize (IH middle after Hrest i Hnonpower ltac:(lia) Hmiddledescent)
      as [Hafterlength Hafterdescent].
    split; [lia|exact Hafterdescent].
Qed.
Lemma reachable_nonpower_descent_refutes_mono__final_failure :
  forall before i,
    NonPowerOfTwo i ->
    1 <= i < Zlength before ->
    Znth (i - 1) before 0 > Znth i before 0 ->
    ~ exists after,
        clos_refl_trans OnePrefixDecrement before after /\
        mono_nondec after.
Proof.
  intros before i Hnonpower Hi Hdescent
    (after & Hreach & Hmono).
  pose proof
    (reachable_preserves_nonpower_descent__final_failure
       before after i Hreach Hnonpower Hi Hdescent)
    as [Hlength Hafterdescent].
  unfold mono_nondec in Hmono.
  specialize (Hmono (i - 1) i ltac:(lia) ltac:(lia) ltac:(lia)).
  lia.
Qed.
