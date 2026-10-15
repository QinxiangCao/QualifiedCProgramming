Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition SameBitsExcept (x y b : Z) : Prop :=
  forall k, 0 <= k -> k <> b -> Z.testbit x k = Z.testbit y k.

Definition OneBitSwap (n : Z) (before after : list Z) : Prop :=
  exists i j b xi xj yi yj,
    0 <= i < n /\ 0 <= j < n /\ 0 <= b /\
    xi = Znth i before 0 /\ xj = Znth j before 0 /\
    yi = Znth i after 0 /\ yj = Znth j after 0 /\
    Zlength after = Zlength before /\
    (forall k, 0 <= k < n -> k <> i -> k <> j ->
       Znth k after 0 = Znth k before 0) /\
    SameBitsExcept xi yi b /\ SameBitsExcept xj yj b /\
    Z.testbit yi b = Z.testbit xj b /\
    Z.testbit yj b = Z.testbit xi b.

Definition ReachableByBitSwaps (n : Z) (a out : list Z) : Prop :=
  clos_refl_trans (OneBitSwap n) a out.

Definition ArraySpread (a : list Z) (d : Z) : Prop :=
  max_value_of_subset Z.le
    (fun endpoints : Z * Z => In (fst endpoints) a /\ In (snd endpoints) a)
    (fun endpoints => snd endpoints - fst endpoints) d.

Definition Pre (a : list Z) : Prop :=
  3 <= Zlength a <= 512 /\
  Forall (fun x => 0 <= x < 1024) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      ReachableByBitSwaps (Zlength a) a (fst candidate) /\
      ArraySpread (fst candidate) (snd candidate))
    snd out.

(** Mathematical meaning of the two accumulators after [i] loop iterations.
    The AND accumulator starts at the first input element, so its observed
    prefix has length [max 1 i]; the OR accumulator starts from zero. *)
Definition BitwiseScanState
    (a : list Z) (i acc_or acc_and : Z) : Prop :=
  0 <= i <= Zlength a /\
  (forall b, 0 <= b ->
    (Z.testbit acc_or b = true <->
      exists j, 0 <= j < i /\ Z.testbit (Znth j a 0) b = true)) /\
  (forall b, 0 <= b ->
    (Z.testbit acc_and b = true <->
      forall j, 0 <= j < Z.max 1 i ->
        Z.testbit (Znth j a 0) b = true)).

Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical_Prop.
Lemma bitwise_scan_state_zero__scan_core :
  forall a,
    1 <= Zlength a ->
    BitwiseScanState a 0 0 (Znth 0 a 0).
Proof.
  intros a Ha.
  unfold BitwiseScanState.
  split; [lia|].
  split.
  - intros b Hb.
    split.
    + rewrite Z.testbit_0_l.
      discriminate.
    + intros (j & Hj & _).
      lia.
  - intros b Hb.
    cbn.
    split.
    + intros Hbit j Hj.
      replace j with 0 by lia.
      exact Hbit.
    + intros Hall.
      apply Hall.
      lia.
Qed.
Lemma bitwise_scan_state_succ__scan_core :
  forall a i acc_or acc_and,
    0 <= i < Zlength a ->
    BitwiseScanState a i acc_or acc_and ->
    BitwiseScanState a (i + 1)
      (Z.lor acc_or (Znth i a 0))
      (Z.land acc_and (Znth i a 0)).
Proof.
  intros a i acc_or acc_and Hi Hstate.
  unfold BitwiseScanState in *.
  destruct Hstate as (Hi_len & Hor & Hand).
  split; [lia|].
  split.
  - intros b Hb.
    rewrite Z.lor_spec, Bool.orb_true_iff, Hor by exact Hb.
    split.
    + intros [(j & Hj & Hbit) | Hbit].
      * exists j. split; [lia|exact Hbit].
      * exists i. split; [lia|exact Hbit].
    + intros (j & Hj & Hbit).
      assert (j < i \/ j = i) by lia.
      destruct H as [Hlt | ->].
      * left. exists j. split; [lia|exact Hbit].
      * right. exact Hbit.
  - intros b Hb.
    rewrite Z.land_spec, Bool.andb_true_iff, Hand by exact Hb.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + cbn.
      split.
      * intros [_ Hbit] j Hj.
        replace j with 0 by lia.
        exact Hbit.
      * intros Hall.
        split.
        -- intros j Hj.
           apply Hall. lia.
        -- apply Hall. lia.
    + assert (1 <= i) by lia.
      rewrite (Z.max_r 1 i) by lia.
      rewrite (Z.max_r 1 (i + 1)) by lia.
      split.
      * intros [Hold Hbit] j Hj.
        assert (j < i \/ j = i) by lia.
        destruct H0 as [Hlt | ->].
        -- apply Hold. lia.
        -- exact Hbit.
      * intros Hall.
        split.
        -- intros j Hj. apply Hall. lia.
        -- apply Hall. lia.
Qed.
Lemma bounded_mask_1024__scan_core :
  forall x,
    0 <= x < 1024 ->
    Z.land x 1023 = x.
Proof.
  intros x Hx.
  change (Z.land x (Z.ones 10) = x).
  rewrite Z.land_ones by lia.
  change (x mod 1024 = x).
  apply Z.mod_small.
  lia.
Qed.
Lemma bounded_lor_land__scan_core :
  forall x y,
    0 <= x < 1024 ->
    0 <= y < 1024 ->
    (0 <= Z.lor x y < 1024) /\
    (0 <= Z.land x y < 1024).
Proof.
  intros x y Hx Hy.
  pose proof (bounded_mask_1024__scan_core x Hx) as Hxm.
  pose proof (bounded_mask_1024__scan_core y Hy) as Hym.
  split.
  - split.
    + apply Z.lor_nonneg. tauto.
    + assert (Hmask : Z.land (Z.lor x y) 1023 = Z.lor x y).
      { rewrite Z.land_lor_distr_l, Hxm, Hym. reflexivity. }
      change (Z.land (Z.lor x y) (Z.ones 10) = Z.lor x y) in Hmask.
      rewrite Z.land_ones in Hmask by lia.
      change ((Z.lor x y) mod 1024 = Z.lor x y) in Hmask.
      pose proof (Z.mod_pos_bound (Z.lor x y) 1024 ltac:(lia)).
      lia.
  - split.
    + apply Z.land_nonneg. tauto.
    + assert (Hmask : Z.land (Z.land x y) 1023 = Z.land x y).
      { rewrite <- Z.land_assoc, Hym. reflexivity. }
      change (Z.land (Z.land x y) (Z.ones 10) = Z.land x y) in Hmask.
      rewrite Z.land_ones in Hmask by lia.
      change ((Z.land x y) mod 1024 = Z.land x y) in Hmask.
      pose proof (Z.mod_pos_bound (Z.land x y) 1024 ltac:(lia)).
      lia.
Qed.
Lemma bit_write_same__final_result :
  forall x b (v : bool), 0 <= b ->
    Z.testbit (if v then Z.setbit x b else Z.clearbit x b) b = v.
Proof.
  intros x b [] Hb; simpl.
  - apply Z.setbit_eq; lia.
  - apply Z.clearbit_eq.
Qed.
Lemma bit_write_other__final_result :
  forall x b (v : bool) k, 0 <= b -> k <> b ->
    Z.testbit (if v then Z.setbit x b else Z.clearbit x b) k =
    Z.testbit x k.
Proof.
  intros x b [] k Hb Hneq; simpl.
  - apply Z.setbit_neq; lia.
  - apply Z.clearbit_neq; lia.
Qed.
Lemma Zlength_replace_Znth__final_result :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. revert n.
  induction l as [|a l IH]; simpl; intros n; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n) as [|n0].
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IH (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IH by lia.
    rewrite IH. lia.
Qed.
Lemma one_bit_swap_construct__final_result :
  forall n l i j b,
    Zlength l = n -> 0 <= i < n -> 0 <= j < n -> i <> j -> 0 <= b ->
    let xi := Znth i l 0 in
    let xj := Znth j l 0 in
    let yi := if Z.testbit xj b then Z.setbit xi b else Z.clearbit xi b in
    let yj := if Z.testbit xi b then Z.setbit xj b else Z.clearbit xj b in
    OneBitSwap n l (replace_Znth j yj (replace_Znth i yi l)).
Proof.
  intros n l i j b Hlen Hi Hj Hij Hb.
  cbn.
  set (xi := Znth i l 0).
  set (xj := Znth j l 0).
  set (yi := if Z.testbit xj b then Z.setbit xi b else Z.clearbit xi b).
  set (yj := if Z.testbit xi b then Z.setbit xj b else Z.clearbit xj b).
  exists i, j, b, xi, xj, yi, yj.
  repeat split; try assumption; try lia.
  - subst yi yj xi xj.
    set (inner := replace_Znth i
      (if Z.testbit (Znth j l 0) b
       then Z.setbit (Znth i l 0) b else Z.clearbit (Znth i l 0) b) l).
    assert (Hjinner : 0 <= j < Zlength inner).
    { subst inner. rewrite Zlength_replace_Znth__final_result. lia. }
    assert (Hiinner : 0 <= i < Zlength inner).
    { subst inner. rewrite Zlength_replace_Znth__final_result. lia. }
    assert (Hji : j <> i) by lia.
    rewrite (@Znth_replace_Znth_Diff Z 0 inner j i
      (if Z.testbit (Znth i l 0) b
       then Z.setbit (Znth j l 0) b else Z.clearbit (Znth j l 0) b)
      Hjinner Hiinner Hji).
    subst inner.
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  - subst yi yj xi xj.
    rewrite Znth_replace_Znth_Same by
      (repeat rewrite Zlength_replace_Znth__final_result; lia).
    reflexivity.
  - repeat rewrite Zlength_replace_Znth__final_result. reflexivity.
  - intros k Hk Hki Hkj.
    assert (Hjinner : 0 <= j < Zlength (replace_Znth i yi l)).
    { rewrite Zlength_replace_Znth__final_result. lia. }
    assert (Hkinner : 0 <= k < Zlength (replace_Znth i yi l)).
    { rewrite Zlength_replace_Znth__final_result. lia. }
    assert (Hil : 0 <= i < Zlength l) by lia.
    assert (Hkl : 0 <= k < Zlength l) by lia.
    rewrite (@Znth_replace_Znth_Diff Z 0 (replace_Znth i yi l) j k yj
      Hjinner Hkinner (fun H => Hkj (eq_sym H))).
    rewrite (@Znth_replace_Znth_Diff Z 0 l i k yi Hil Hkl
      (fun H => Hki (eq_sym H))).
    reflexivity.
  - subst yi xi. intros k Hk Hneq.
    symmetry. apply bit_write_other__final_result; lia.
  - subst yj xj. intros k Hk Hneq.
    symmetry. apply bit_write_other__final_result; lia.
  - subst yi. apply bit_write_same__final_result; lia.
  - subst yj. apply bit_write_same__final_result; lia.
Qed.
Lemma one_bit_swap_occurs_iff__final_result :
  forall n before after,
    OneBitSwap n before after ->
    Zlength before = n ->
    Zlength after = Zlength before /\
    forall b, 0 <= b -> forall v,
      (exists k, 0 <= k < Zlength before /\
        Z.testbit (Znth k before 0) b = v) <->
      (exists k, 0 <= k < Zlength after /\
        Z.testbit (Znth k after 0) b = v).
Proof.
  intros n before after Hswap Hbase.
  destruct Hswap as
    (i & j & sb & xi & xj & yi & yj & Hi & Hj & Hsb & Hxi & Hxj & Hyi & Hyj &
     Hlen & Hother & Hsamei & Hsamej & Hbit_i & Hbit_j).
  split; [exact Hlen|].
  intros b Hb0 v; split; intros (k & Hk & Hkv).
  - destruct (Z.eq_dec b sb) as [->|Hb].
    + destruct (Z.eq_dec k i) as [->|Hki].
      * exists j. split; [lia|].
        rewrite <- Hyj, Hbit_j, Hxi. exact Hkv.
      * destruct (Z.eq_dec k j) as [->|Hkj].
        -- exists i. split; [lia|].
           rewrite <- Hyi, Hbit_i, Hxj. exact Hkv.
        -- exists k. split; [rewrite Hlen; exact Hk|].
           rewrite Hother by lia. exact Hkv.
    + destruct (Z.eq_dec k i) as [->|Hki].
      * exists i. split; [lia|].
        rewrite <- Hyi. rewrite <- Hsamei by lia. rewrite Hxi. exact Hkv.
      * destruct (Z.eq_dec k j) as [->|Hkj].
        -- exists j. split; [lia|].
           rewrite <- Hyj. rewrite <- Hsamej by lia. rewrite Hxj. exact Hkv.
        -- exists k. split; [rewrite Hlen; exact Hk|].
           rewrite Hother by lia. exact Hkv.
  - destruct (Z.eq_dec b sb) as [->|Hb].
    + destruct (Z.eq_dec k i) as [->|Hki].
      * exists j. split; [lia|].
        rewrite <- Hxj, <- Hbit_i, Hyi. exact Hkv.
      * destruct (Z.eq_dec k j) as [->|Hkj].
        -- exists i. split; [lia|].
           rewrite <- Hxi, <- Hbit_j, Hyj. exact Hkv.
        -- exists k. split; [rewrite <- Hlen; exact Hk|].
           rewrite Hother in Hkv by lia. exact Hkv.
    + destruct (Z.eq_dec k i) as [->|Hki].
      * exists i. split; [lia|].
        rewrite <- Hxi, Hsamei by lia. rewrite Hyi. exact Hkv.
      * destruct (Z.eq_dec k j) as [->|Hkj].
        -- exists j. split; [lia|].
           rewrite <- Hxj, Hsamej by lia. rewrite Hyj. exact Hkv.
        -- exists k. split; [rewrite <- Hlen; exact Hk|].
           rewrite Hother in Hkv by lia. exact Hkv.
Qed.
Lemma reachable_preserves_bit_counts__final_result :
  forall n a out,
    Zlength a = n ->
    ReachableByBitSwaps n a out ->
    Zlength out = Zlength a /\
    forall b, 0 <= b -> forall v,
      (exists k, 0 <= k < Zlength a /\
        Z.testbit (Znth k a 0) b = v) <->
      (exists k, 0 <= k < Zlength out /\
        Z.testbit (Znth k out 0) b = v).
Proof.
  intros n a out Hbase Hreach.
  unfold ReachableByBitSwaps in Hreach.
  induction_1n Hreach.
  - split; [reflexivity|tauto].
  - match goal with
    | Hstep : OneBitSwap n ?before ?mid,
      Hb : Zlength ?before = n |- _ =>
        pose proof (one_bit_swap_occurs_iff__final_result
          n before mid Hstep Hb) as [Hlenbm Hoccbm];
        assert (Hmid : Zlength mid = n) by lia;
        pose proof (IHrt Hmid) as [Hlenmo Hoccmo];
        split; [lia|];
        intros b Hb0 v;
        rewrite (Hoccbm b Hb0 v), (Hoccmo b Hb0 v);
        reflexivity
    end.
Qed.
Lemma one_swap_reachable__final_result :
  forall n a b,
    OneBitSwap n a b -> ReachableByBitSwaps n a b.
Proof.
  intros n a b H.
  unfold ReachableByBitSwaps, clos_refl_trans.
  exists 1%nat. simpl. sets_unfold.
  exists b. split; [exact H|reflexivity].
Qed.
Lemma force_bit_once__final_result :
  forall n l t s b,
    Zlength l = n -> 0 <= t < n -> 0 <= s < n -> t <> s -> 0 <= b ->
    exists out,
      ReachableByBitSwaps n l out /\
      Zlength out = n /\
      Z.testbit (Znth t out 0) b = Z.testbit (Znth s l 0) b /\
      (forall k q, 0 <= k < n -> 0 <= q -> q <> b ->
        Z.testbit (Znth k out 0) q = Z.testbit (Znth k l 0) q) /\
      (forall k, 0 <= k < n -> k <> t -> k <> s ->
        Znth k out 0 = Znth k l 0).
Proof.
  intros n l t s b Hlen Ht Hs Hts Hb.
  set (xt := Znth t l 0).
  set (xs := Znth s l 0).
  set (yt := if Z.testbit xs b then Z.setbit xt b else Z.clearbit xt b).
  set (ys := if Z.testbit xt b then Z.setbit xs b else Z.clearbit xs b).
  set (out := replace_Znth s ys (replace_Znth t yt l)).
  exists out.
  assert (Hswap : OneBitSwap n l out).
  { subst out ys yt xs xt.
    apply one_bit_swap_construct__final_result; assumption. }
  split.
  - apply one_swap_reachable__final_result; exact Hswap.
  - split.
    + subst out. repeat rewrite Zlength_replace_Znth__final_result. exact Hlen.
    + split.
      * subst out ys yt xs xt.
        assert (Hsinner : 0 <= s < Zlength
          (replace_Znth t
            (if Z.testbit (Znth s l 0) b
             then Z.setbit (Znth t l 0) b
             else Z.clearbit (Znth t l 0) b) l)).
        { rewrite Zlength_replace_Znth__final_result. lia. }
        assert (Htinner : 0 <= t < Zlength
          (replace_Znth t
            (if Z.testbit (Znth s l 0) b
             then Z.setbit (Znth t l 0) b
             else Z.clearbit (Znth t l 0) b) l)).
        { rewrite Zlength_replace_Znth__final_result. lia. }
        rewrite (@Znth_replace_Znth_Diff Z 0 _ s t _
          Hsinner Htinner (fun H => Hts (eq_sym H))).
        rewrite Znth_replace_Znth_Same by lia.
        apply bit_write_same__final_result; lia.
      * split.
        -- intros k q Hk Hq Hqb.
           subst out ys yt xs xt.
           destruct (Z.eq_dec k t) as [->|Hkt].
           ++ assert (Hsinner : 0 <= s < Zlength
                (replace_Znth t
                  (if Z.testbit (Znth s l 0) b
                   then Z.setbit (Znth t l 0) b
                   else Z.clearbit (Znth t l 0) b) l)).
              { rewrite Zlength_replace_Znth__final_result. lia. }
              assert (Htinner : 0 <= t < Zlength
                (replace_Znth t
                  (if Z.testbit (Znth s l 0) b
                   then Z.setbit (Znth t l 0) b
                   else Z.clearbit (Znth t l 0) b) l)).
              { rewrite Zlength_replace_Znth__final_result. lia. }
              rewrite (@Znth_replace_Znth_Diff Z 0 _ s t _
                Hsinner Htinner (fun H => Hts (eq_sym H))).
              rewrite Znth_replace_Znth_Same by lia.
              apply bit_write_other__final_result; lia.
           ++ destruct (Z.eq_dec k s) as [->|Hks].
              ** rewrite Znth_replace_Znth_Same by
                   (rewrite Zlength_replace_Znth__final_result; lia).
                 apply bit_write_other__final_result; lia.
              ** assert (Hsinner : 0 <= s < Zlength (replace_Znth t
                    (if Z.testbit (Znth s l 0) b
                     then Z.setbit (Znth t l 0) b
                     else Z.clearbit (Znth t l 0) b) l)).
                 { rewrite Zlength_replace_Znth__final_result. lia. }
                 assert (Hkinner : 0 <= k < Zlength (replace_Znth t
                    (if Z.testbit (Znth s l 0) b
                     then Z.setbit (Znth t l 0) b
                     else Z.clearbit (Znth t l 0) b) l)).
                 { rewrite Zlength_replace_Znth__final_result. lia. }
                 rewrite (@Znth_replace_Znth_Diff Z 0 _ s k _
                   Hsinner Hkinner (fun H => Hks (eq_sym H))).
                 rewrite Znth_replace_Znth_Diff by lia.
                 reflexivity.
        -- intros k Hk Hkt Hks.
        subst out ys yt xs xt.
           assert (Hsinner : 0 <= s < Zlength (replace_Znth t
              (if Z.testbit (Znth s l 0) b
               then Z.setbit (Znth t l 0) b
               else Z.clearbit (Znth t l 0) b) l)).
           { rewrite Zlength_replace_Znth__final_result. lia. }
           assert (Hkinner : 0 <= k < Zlength (replace_Znth t
              (if Z.testbit (Znth s l 0) b
               then Z.setbit (Znth t l 0) b
               else Z.clearbit (Znth t l 0) b) l)).
           { rewrite Zlength_replace_Znth__final_result. lia. }
           rewrite (@Znth_replace_Znth_Diff Z 0 _ s k _
             Hsinner Hkinner (fun H => Hks (eq_sym H))).
           rewrite Znth_replace_Znth_Diff by lia.
           reflexivity.
Qed.
Lemma canonical_extrema_prefix__final_result :
  forall (m : nat) n a all_or all_and,
    (m <= 10)%nat -> Zlength a = n -> 3 <= n ->
    BitwiseScanState a n all_or all_and ->
    exists out,
      ReachableByBitSwaps n a out /\
      Zlength out = n /\
      (forall b, 0 <= b < Z.of_nat m ->
        Z.testbit (Znth 0 out 0) b = Z.testbit all_or b /\
        Z.testbit (Znth 1 out 0) b = Z.testbit all_and b).
Proof.
  intros m; induction m as [|m IH]; intros n a all_or all_and Hm Hlen Hn Hscan.
  - exists a. split; [reflexivity|]. split; [exact Hlen|]. intros b Hb. lia.
  - assert (Hm10 : (m <= 10)%nat) by lia.
    destruct (IH n a all_or all_and Hm10 Hlen Hn Hscan)
      as (cur & Hreach & Hcurlen & Hprefix).
    destruct Hscan as [Hscanbounds [HOr HAnd]].
    set (b := Z.of_nat m).
    assert (Hb : 0 <= b) by (subst b; lia).
    pose proof (reachable_preserves_bit_counts__final_result
      n a cur Hlen Hreach) as [_ Hprofile].

    assert (HORphase : exists cur1,
      ReachableByBitSwaps n cur cur1 /\ Zlength cur1 = n /\
      Z.testbit (Znth 0 cur1 0) b = Z.testbit all_or b /\
      (forall k q, 0 <= k < n -> 0 <= q -> q <> b ->
        Z.testbit (Znth k cur1 0) q = Z.testbit (Znth k cur 0) q)).
    {
      destruct (Z.testbit (Znth 0 cur 0) b) eqn:Hcur0;
      destruct (Z.testbit all_or b) eqn:Hor.
      - exists cur. split; [reflexivity|]. split; [exact Hcurlen|].
        split; [congruence|]. intros; reflexivity.
      - exfalso.
        assert (Houtocc : exists k, 0 <= k < Zlength cur /\
          Z.testbit (Znth k cur 0) b = true).
        { exists 0. split; [lia|exact Hcur0]. }
        apply (proj2 (Hprofile b Hb true)) in Houtocc.
        destruct Houtocc as (k & Hk & Hkbit).
        assert (HorigN : exists j, 0 <= j < n /\
            Z.testbit (Znth j a 0) b = true).
        { exists k. split; [lia|exact Hkbit]. }
        apply (proj2 (HOr b Hb)) in HorigN.
        rewrite Hor in HorigN. discriminate.
      - assert (Haocc : exists k, 0 <= k < Zlength a /\
          Z.testbit (Znth k a 0) b = true).
        { pose proof (proj1 (HOr b Hb) Hor) as (k & Hk & Hkbit).
          exists k. split; [lia|exact Hkbit]. }
        apply (proj1 (Hprofile b Hb true)) in Haocc.
        destruct Haocc as (s & Hs & Hsbit).
        assert (Hs0 : s <> 0).
        { intro Heq. subst s. rewrite Hcur0 in Hsbit. discriminate. }
        destruct (force_bit_once__final_result n cur 0 s b
          Hcurlen ltac:(lia) ltac:(lia) ltac:(lia) Hb)
          as (cur1 & Hr1 & Hlen1 & Hbit1 & Hcols1 & Hpos1).
        exists cur1. repeat split; try assumption.
        rewrite Hbit1, Hsbit. reflexivity.
      - exists cur. split; [reflexivity|]. split; [exact Hcurlen|].
        split; [congruence|]. intros; reflexivity.
    }
    destruct HORphase as (cur1 & Hr1 & Hlen1 & Hcur1or & Hcols1).
    assert (Hreach1 : ReachableByBitSwaps n a cur1).
    { etransitivity; eauto. }
    pose proof (reachable_preserves_bit_counts__final_result
      n a cur1 Hlen Hreach1) as [_ Hprofile1].

    assert (HANDphase : exists cur2,
      ReachableByBitSwaps n cur1 cur2 /\ Zlength cur2 = n /\
      Z.testbit (Znth 0 cur2 0) b = Z.testbit all_or b /\
      Z.testbit (Znth 1 cur2 0) b = Z.testbit all_and b /\
      (forall k q, 0 <= k < n -> 0 <= q -> q <> b ->
        Z.testbit (Znth k cur2 0) q = Z.testbit (Znth k cur1 0) q)).
    {
      destruct (Z.testbit (Znth 1 cur1 0) b) eqn:Hcur1;
      destruct (Z.testbit all_and b) eqn:Hand.
      - exists cur1. split; [reflexivity|]. split; [exact Hlen1|].
        split; [exact Hcur1or|].
        split; [congruence|]. intros; reflexivity.
      - assert (Hnotall : ~(forall j, 0 <= j < Z.max 1 n ->
            Z.testbit (Znth j a 0) b = true)).
        { intro Hall.
          pose proof (proj2 (HAnd b Hb) Hall) as Hbad.
          rewrite Hand in Hbad. discriminate. }
        apply not_all_ex_not in Hnotall.
        destruct Hnotall as [s Hsnot].
        apply imply_to_and in Hsnot.
        destruct Hsnot as [Hsrange Hsnot].
        assert (Hsrange' : 0 <= s < n).
        { rewrite Z.max_r in Hsrange by lia. exact Hsrange. }
        assert (Hsbit : Z.testbit (Znth s a 0) b = false).
        { destruct (Z.testbit (Znth s a 0) b); tauto. }
        assert (Haocc : exists k, 0 <= k < Zlength a /\
            Z.testbit (Znth k a 0) b = false).
        { exists s. split; [lia|exact Hsbit]. }
        apply (proj1 (Hprofile1 b Hb false)) in Haocc.
        destruct Haocc as (s1 & Hs1range & Hs1bit).
        assert (Hs11 : s1 <> 1).
        { intro Heq. subst s1. rewrite Hcur1 in Hs1bit. discriminate. }
        assert (Hortrue : Z.testbit all_or b = true).
        { assert (Hcurtrue : exists k, 0 <= k < Zlength cur1 /\
              Z.testbit (Znth k cur1 0) b = true).
          { exists 1. split; [lia|exact Hcur1]. }
          apply (proj2 (Hprofile1 b Hb true)) in Hcurtrue.
          destruct Hcurtrue as (k & Hk & Hkbit).
          apply (proj2 (HOr b Hb)). exists k. split; [lia|exact Hkbit]. }
        assert (Hs10 : s1 <> 0).
        { intro Heq. subst s1. rewrite Hcur1or, Hortrue in Hs1bit. discriminate. }
        destruct (force_bit_once__final_result n cur1 1 s1 b
          Hlen1 ltac:(lia) ltac:(lia) ltac:(lia) Hb)
          as (cur2 & Hr2 & Hlen2 & Hbit2 & Hcols2 & Hpos2).
        exists cur2. repeat split; try assumption.
        + rewrite Hpos2 by lia. exact Hcur1or.
        + rewrite Hbit2, Hs1bit. reflexivity.
      - exfalso.
        assert (Houtocc : exists k, 0 <= k < Zlength cur1 /\
          Z.testbit (Znth k cur1 0) b = false).
        { exists 1. split; [lia|exact Hcur1]. }
        apply (proj2 (Hprofile1 b Hb false)) in Houtocc.
        destruct Houtocc as (s & Hs & Hsfalse).
        pose proof (proj1 (HAnd b Hb) Hand) as Hall.
        specialize (Hall s ltac:(rewrite Z.max_r by lia; lia)).
        rewrite Hall in Hsfalse. discriminate.
      - exists cur1. split; [reflexivity|]. split; [exact Hlen1|].
        split; [exact Hcur1or|].
        split; [congruence|]. intros; reflexivity.
    }
    destruct HANDphase as
      (cur2 & Hr2 & Hlen2 & Hcur2or & Hcur2and & Hcols2).
    exists cur2. split.
    { etransitivity; [exact Hreach1|exact Hr2]. }
    split; [exact Hlen2|].
    intros q Hq.
    rewrite Nat2Z.inj_succ in Hq.
    destruct (Z.eq_dec q b) as [Heq|Hqb].
    + subst q. split; [exact Hcur2or|exact Hcur2and].
    + assert (Hqm : 0 <= q < Z.of_nat m) by (subst b; lia).
      specialize (Hprefix q Hqm).
      destruct Hprefix as [Hpreor Hpreand].
      split.
      * rewrite Hcols2 by lia. rewrite Hcols1 by lia. exact Hpreor.
      * rewrite Hcols2 by lia. rewrite Hcols1 by lia. exact Hpreand.
Qed.
Lemma bounded_testbit_high_false__final_result :
  forall x b, 0 <= x < 1024 -> 10 <= b -> Z.testbit x b = false.
Proof.
  intros x b Hx Hb.
  apply Z.bits_above_log2; [lia|].
  assert (Hlog : Z.log2 x <= Z.log2 1023).
  { apply Z.log2_le_mono; lia. }
  change (Z.log2 1023) with 9 in Hlog. lia.
Qed.
Lemma canonical_extrema_reachable__final_result :
  forall n a all_or all_and,
    Zlength a = n -> 3 <= n ->
    (forall k, 0 <= k < n -> 0 <= Znth k a 0 < 1024) ->
    0 <= all_or < 1024 -> 0 <= all_and < 1024 ->
    BitwiseScanState a n all_or all_and ->
    exists out,
      ReachableByBitSwaps n a out /\ Zlength out = n /\
      Znth 0 out 0 = all_or /\ Znth 1 out 0 = all_and.
Proof.
  intros n a all_or all_and Hlen Hn HaBounds HorBounds HandBounds Hscan.
  destruct (canonical_extrema_prefix__final_result
    10%nat n a all_or all_and ltac:(lia) Hlen Hn Hscan)
    as (out & Hreach & Houtlen & Hbits).
  pose proof (reachable_preserves_bit_counts__final_result
    n a out Hlen Hreach) as [_ Hprofile].
  exists out. repeat split; try assumption.
  - apply Z.bits_inj'. intros b Hb.
    destruct (Z_lt_ge_dec b 10) as [Hblow|Hbhigh].
    + pose proof (Hbits b ltac:(lia)) as [Hbit0 Hbit1]. exact Hbit0.
    + assert (Houtocc : exists k, 0 <= k < Zlength out /\
          Z.testbit (Znth k out 0) b = Z.testbit (Znth 0 out 0) b).
      { exists 0. split; [lia|reflexivity]. }
      apply (proj2 (Hprofile b Hb (Z.testbit (Znth 0 out 0) b))) in Houtocc.
      destruct Houtocc as (k & Hk & Hkbit).
      rewrite <- Hkbit.
      rewrite (bounded_testbit_high_false__final_result (Znth k a 0) b)
        by (try apply HaBounds; lia).
      symmetry. apply bounded_testbit_high_false__final_result; lia.
  - apply Z.bits_inj'. intros b Hb.
    destruct (Z_lt_ge_dec b 10) as [Hblow|Hbhigh].
    + pose proof (Hbits b ltac:(lia)) as [Hbit0 Hbit1]. exact Hbit1.
    + assert (Houtocc : exists k, 0 <= k < Zlength out /\
          Z.testbit (Znth k out 0) b = Z.testbit (Znth 1 out 0) b).
      { exists 1. split; [lia|reflexivity]. }
      apply (proj2 (Hprofile b Hb (Z.testbit (Znth 1 out 0) b))) in Houtocc.
      destruct Houtocc as (k & Hk & Hkbit).
      rewrite <- Hkbit.
      rewrite (bounded_testbit_high_false__final_result (Znth k a 0) b)
        by (try apply HaBounds; lia).
      symmetry. apply bounded_testbit_high_false__final_result; lia.
Qed.
Lemma land_le_nonnegative__final_result :
  forall x y, 0 <= x -> 0 <= y ->
    Z.land x y <= x /\ Z.land x y <= y.
Proof.
  intros x y Hx Hy.
  destruct x as [|px|px], y as [|py|py]; simpl in *; try lia.
  split.
  - change (Z.of_N (N.land (N.pos px) (N.pos py)) <= Z.of_N (N.pos px)).
    apply (proj1 (N2Z.inj_le _ _)). apply N.land_le_l.
  - change (Z.of_N (N.land (N.pos px) (N.pos py)) <= Z.of_N (N.pos py)).
    apply (proj1 (N2Z.inj_le _ _)). apply N.land_le_r.
Qed.
Lemma In_Znth_index__final_result :
  forall (l : list Z) x, In x l ->
    exists k, 0 <= k < Zlength l /\ Znth k l 0 = x.
Proof.
  intros l x Hin.
  destruct (@In_nth Z l x 0 Hin) as (k & Hk & Hnth).
  exists (Z.of_nat k). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma reachable_elements_bounded_by_scan_extrema__final_result :
  forall n a out all_or all_and,
    Zlength a = n ->
    (forall k, 0 <= k < n -> 0 <= Znth k a 0 < 1024) ->
    0 <= all_or < 1024 -> 0 <= all_and < 1024 ->
    BitwiseScanState a n all_or all_and ->
    ReachableByBitSwaps n a out ->
    forall x, In x out -> all_and <= x <= all_or.
Proof.
  intros n a out all_or all_and Hlen HaBounds HorBounds HandBounds
    Hscan Hreach x Hinx.
  destruct Hscan as [Hscanbounds [HOr HAnd]].
  pose proof (reachable_preserves_bit_counts__final_result
    n a out Hlen Hreach) as [Houtlen Hprofile].
  destruct (In_Znth_index__final_result out x Hinx)
    as (k & Hk & Hkx).
  assert (Hx_or : Z.land x all_or = x).
  {
    apply Z.bits_inj'. intros b Hb.
    rewrite Z.land_spec by lia.
    destruct (Z.testbit x b) eqn:Hxbit; simpl.
    - assert (Houtocc : exists j, 0 <= j < Zlength out /\
          Z.testbit (Znth j out 0) b = true).
      { exists k. split; [exact Hk|rewrite Hkx; exact Hxbit]. }
      apply (proj2 (Hprofile b Hb true)) in Houtocc.
      destruct Houtocc as (j & Hj & Hjbit).
      assert (HorigN : exists j, 0 <= j < n /\
          Z.testbit (Znth j a 0) b = true).
      { exists j. split; [lia|exact Hjbit]. }
      apply (proj2 (HOr b Hb)) in HorigN.
      rewrite HorigN. reflexivity.
    - reflexivity.
  }
  assert (Hxnonneg : 0 <= x).
  { rewrite <- Hx_or. apply Z.land_nonneg. right. lia. }
  assert (Hxle : x <= all_or).
  { pose proof (land_le_nonnegative__final_result x all_or Hxnonneg ltac:(lia))
      as [_ Hle]. rewrite Hx_or in Hle. exact Hle. }
  assert (Hand_x : Z.land all_and x = all_and).
  {
    apply Z.bits_inj'. intros b Hb.
    rewrite Z.land_spec by lia.
    destruct (Z.testbit all_and b) eqn:Handbit; simpl.
    - pose proof (proj1 (HAnd b Hb) Handbit) as Hall.
      destruct (Z.testbit x b) eqn:Hxbit; [reflexivity|].
      assert (Houtocc : exists j, 0 <= j < Zlength out /\
          Z.testbit (Znth j out 0) b = false).
      { exists k. split; [exact Hk|rewrite Hkx; exact Hxbit]. }
      apply (proj2 (Hprofile b Hb false)) in Houtocc.
      destruct Houtocc as (j & Hj & Hjbit).
      specialize (Hall j ltac:(rewrite Z.max_r by lia; lia)).
      rewrite Hall in Hjbit. discriminate.
    - reflexivity.
  }
  assert (Handle : all_and <= x).
  { pose proof (land_le_nonnegative__final_result all_and x ltac:(lia) Hxnonneg)
      as [_ Hle]. rewrite Hand_x in Hle. exact Hle. }
  lia.
Qed.
Lemma array_spread_from_extrema_bounds__final_result :
  forall out all_and all_or,
    In all_and out -> In all_or out ->
    (forall x, In x out -> all_and <= x <= all_or) ->
    ArraySpread out (all_or - all_and).
Proof.
  intros out all_and all_or HinAnd HinOr Hbounds.
  unfold ArraySpread, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  exists (all_and, all_or). split.
  - split.
    + simpl. split; assumption.
    + intros [x y] [Hx Hy]. simpl in *.
      pose proof (Hbounds x Hx).
      pose proof (Hbounds y Hy). lia.
  - reflexivity.
Qed.
Lemma bitwise_scan_final_implies_spec__final_result :
  forall n a all_or all_and,
    Zlength a = n -> 3 <= n ->
    (forall k, 0 <= k < n -> 0 <= Znth k a 0 < 1024) ->
    0 <= all_or < 1024 -> 0 <= all_and < 1024 ->
    BitwiseScanState a n all_or all_and ->
    Spec a (all_or - all_and).
Proof.
  intros n a all_or all_and Hlen Hn HaBounds HorBounds HandBounds Hscan.
  destruct (canonical_extrema_reachable__final_result
    n a all_or all_and Hlen Hn HaBounds HorBounds HandBounds Hscan)
    as (best & HbestReach & HbestLen & HbestOr & HbestAnd).
  assert (HinOr : In all_or best).
  { rewrite <- HbestOr. apply nth_In with (d := 0%Z).
    rewrite Zlength_correct in HbestLen. lia. }
  assert (HinAnd : In all_and best).
  { rewrite <- HbestAnd. apply nth_In with (d := 0%Z).
    rewrite Zlength_correct in HbestLen. lia. }
  assert (HbestBounds : forall x, In x best -> all_and <= x <= all_or).
  { intros x Hinx.
    exact (reachable_elements_bounded_by_scan_extrema__final_result
      n a best all_or all_and Hlen HaBounds HorBounds HandBounds
      Hscan HbestReach x Hinx). }
  assert (HbestSpread : ArraySpread best (all_or - all_and)).
  { apply array_spread_from_extrema_bounds__final_result; assumption. }
  unfold Spec, MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
  exists (best, all_or - all_and). split.
  - split.
    + simpl. split.
      * rewrite Hlen. exact HbestReach.
      * exact HbestSpread.
    + intros [other d] [HotherReach HotherSpread]. simpl in *.
      rewrite Hlen in HotherReach.
      unfold ArraySpread, MaxMin.max_value_of_subset,
        MaxMin.max_object_of_subset in HotherSpread.
      destruct HotherSpread as ([x y] & [[Hx Hy] Hmax] & Hd).
      simpl in Hx, Hy, Hmax, Hd.
      pose proof (reachable_elements_bounded_by_scan_extrema__final_result
        n a other all_or all_and Hlen HaBounds HorBounds HandBounds
        Hscan HotherReach x Hx) as Hxbounds.
      pose proof (reachable_elements_bounded_by_scan_extrema__final_result
        n a other all_or all_and Hlen HaBounds HorBounds HandBounds
        Hscan HotherReach y Hy) as Hybounds.
      lia.
  - reflexivity.
Qed.
