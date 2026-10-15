Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition ReachInRounds (m rounds : Z) (a b : list Z) : Prop :=
  Forall2 (fun before after =>
    exists inc, 0 <= inc <= rounds /\
      after = (before + inc) mod m) a b.

Definition Pre (m : Z) (a : list Z) : Prop :=
  1 <= m <= 300000 /\
  1 <= Zlength a <= 300000 /\
  Forall (fun x => 0 <= x < m) a.

Definition Feasible (m : Z) (a : list Z) (rounds : Z) : Prop :=
  exists b,
    ReachInRounds m rounds a b /\
    mono_nondec b.

Definition GreedyPrefixState
    (m : Z) (a : list Z) (rounds i last : Z) : Prop :=
  0 <= i <= Zlength a /\
  0 <= last < m /\
  ((i = 0 /\ last = 0) \/
   (0 < i /\
    exists b,
      ReachInRounds m rounds (sublist 0 i a) b /\
      mono_nondec b /\
      Zlength b = i /\
      Znth (i - 1) b 0 = last /\
      forall other,
        ReachInRounds m rounds (sublist 0 i a) other /\
        mono_nondec other ->
        last <= Znth (i - 1) other 0)).

Definition Spec (m : Z) (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : Z * list Z =>
      ReachInRounds m (fst candidate) a (snd candidate) /\
      mono_nondec (snd candidate))
    fst out.

Definition SearchState
    (m : Z) (a : list Z) (lo hi ans : Z) : Prop :=
  Feasible m a ans /\
  lo <= ans /\
  exists out,
    Spec m a out /\
    ((lo <= out <= hi) \/ out = ans).

Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Zwf.
Require Import Coq.Logic.Classical_Prop.
Lemma Znth_app_left__feasible_prefix :
  forall (l1 l2 : list Z) (d i : Z),
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma Znth_app_last__feasible_prefix :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma sublist_snoc__feasible_prefix :
  forall (a : list Z) i,
    0 <= i < Zlength a ->
    sublist 0 (i + 1) a = sublist 0 i a ++ Znth i a 0 :: nil.
Proof.
  intros a i Hi.
  rewrite (sublist_split 0 (i + 1) i a) by lia.
  rewrite (sublist_single 0 i a) by lia.
  reflexivity.
Qed.
Lemma mono_nondec_app_left__feasible_prefix :
  forall (l1 l2 : list Z),
    mono_nondec (l1 ++ l2) -> mono_nondec l1.
Proof.
  intros l1 l2 Hmono p q Hp Hpq Hq.
  unfold mono_nondec in Hmono.
  rewrite <- (Znth_app_left__feasible_prefix l1 l2 0 p) by lia.
  rewrite <- (Znth_app_left__feasible_prefix l1 l2 0 q) by lia.
  apply Hmono; try lia.
  rewrite Zlength_app.
  pose proof (Zlength_nonneg l2).
  lia.
Qed.
Lemma mono_nondec_snoc__feasible_prefix :
  forall (l : list Z) last x,
    mono_nondec l ->
    0 < Zlength l ->
    Znth (Zlength l - 1) l 0 = last ->
    last <= x ->
    mono_nondec (l ++ x :: nil).
Proof.
  intros l last x Hmono Hlen Hlast Hlx p q Hp Hpq Hq.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
  destruct (Z_lt_ge_dec q (Zlength l)) as [Hql | Hql].
  - rewrite Znth_app_left__feasible_prefix by lia.
    rewrite Znth_app_left__feasible_prefix by lia.
    apply Hmono; lia.
  - assert (q = Zlength l) by lia; subst q.
    rewrite Znth_app_last__feasible_prefix.
    destruct (Z_lt_ge_dec p (Zlength l)) as [Hpl | Hpl].
    + rewrite Znth_app_left__feasible_prefix by lia.
      etransitivity; [| exact Hlx].
      rewrite <- Hlast.
      apply Hmono; lia.
    + assert (p = Zlength l) by lia; subst p.
      rewrite Znth_app_last__feasible_prefix.
      lia.
Qed.
Lemma mono_nondec_snoc_boundary__feasible_prefix :
  forall (l : list Z) x,
    0 < Zlength l ->
    mono_nondec (l ++ x :: nil) ->
    Znth (Zlength l - 1) l 0 <= x.
Proof.
  intros l x Hlen Hmono.
  unfold mono_nondec in Hmono.
  specialize (Hmono (Zlength l - 1) (Zlength l)).
  rewrite Znth_app_left__feasible_prefix in Hmono by lia.
  rewrite Znth_app_last__feasible_prefix in Hmono.
  apply Hmono; try lia.
  rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.
Lemma reach_in_rounds_snoc__feasible_prefix :
  forall m rounds a i b x inc,
    0 <= i < Zlength a ->
    ReachInRounds m rounds (sublist 0 i a) b ->
    0 <= inc <= rounds ->
    x = (Znth i a 0 + inc) mod m ->
    ReachInRounds m rounds (sublist 0 (i + 1) a) (b ++ x :: nil).
Proof.
  intros m rounds a i b x inc Hi Hreach Hinc Hx.
  rewrite sublist_snoc__feasible_prefix by exact Hi.
  unfold ReachInRounds in *.
  apply Forall2_app; [exact Hreach |].
  constructor; [| constructor].
  exists inc. split; [exact Hinc | exact Hx].
Qed.
Lemma reach_in_rounds_snoc_inv__feasible_prefix :
  forall m rounds a i other,
    0 <= i < Zlength a ->
    ReachInRounds m rounds (sublist 0 (i + 1) a) other ->
    exists prefix endpoint inc,
      other = prefix ++ endpoint :: nil /\
      ReachInRounds m rounds (sublist 0 i a) prefix /\
      0 <= inc <= rounds /\
      endpoint = (Znth i a 0 + inc) mod m.
Proof.
  intros m rounds a i other Hi Hreach.
  rewrite sublist_snoc__feasible_prefix in Hreach by exact Hi.
  unfold ReachInRounds in *.
  apply Forall2_app_inv_l in Hreach.
  destruct Hreach as (prefix & tail & Hprefix & Htail & Heq).
  subst other.
  inversion Htail as [| ai endpoint l1 l2 Hendpoint Hnil]; subst.
  inversion Hnil; subst.
  destruct Hendpoint as (inc & Hinc & Heq).
  exists prefix, endpoint, inc.
  split; [reflexivity |].
  split; [exact Hprefix |].
  split; [exact Hinc | exact Heq].
Qed.
Lemma greedy_prefix_extend__feasible_prefix :
  forall m a rounds i last next inc,
    0 < m ->
    0 <= i < Zlength a ->
    GreedyPrefixState m a rounds i last ->
    0 <= next < m ->
    last <= next ->
    0 <= inc <= rounds ->
    next = (Znth i a 0 + inc) mod m ->
    (forall endpoint competing_inc,
      0 <= competing_inc <= rounds ->
      endpoint = (Znth i a 0 + competing_inc) mod m ->
      last <= endpoint ->
      next <= endpoint) ->
    GreedyPrefixState m a rounds (i + 1) next.
Proof.
  intros m a rounds i last next inc Hm Hi Hstate Hnext Hlastnext
    Hinc Hnexteq Hminimal.
  unfold GreedyPrefixState in Hstate |- *.
  destruct Hstate as (Hiold & Hlastbound & Hprefix).
  assert (Hold : exists b,
      ReachInRounds m rounds (sublist 0 i a) b /\
      mono_nondec b /\
      Zlength b = i /\
      Znth (i - 1) b 0 = last /\
      forall other,
        ReachInRounds m rounds (sublist 0 i a) other /\
        mono_nondec other ->
        last <= Znth (i - 1) other 0).
  { destruct Hprefix as [[-> ->] | (Hipos & b & Hb)].
    - exists nil.
      split.
      + unfold ReachInRounds. constructor.
      + split.
        * apply mono_nondec_nil.
        * split; [reflexivity |].
          split; [reflexivity |].
          intros other Hother.
          destruct Hother as [Hreach _].
          unfold ReachInRounds in Hreach.
          rewrite Zsublist_nil in Hreach by lia.
          inversion Hreach; reflexivity.
    - exists b. exact Hb. }
  destruct Hold as (b & Hreach & Hmono & Hlen & Hblast & Holdminimal).
  repeat split; try lia.
  right. split; [lia |].
  exists (b ++ next :: nil).
  repeat split.
  - eapply reach_in_rounds_snoc__feasible_prefix; eauto.
  - destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
    + assert (b = nil) as ->.
      { destruct b as [| z b']; [reflexivity |].
        rewrite Zlength_cons in Hlen.
        pose proof (Zlength_nonneg b'). lia. }
      apply mono_nondec_single.
    + eapply mono_nondec_snoc__feasible_prefix with (last := last).
      * exact Hmono.
      * rewrite Hlen. lia.
      * rewrite Hlen. exact Hblast.
      * exact Hlastnext.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen. lia.
  - replace (i + 1 - 1) with (Zlength b) by lia.
    apply Znth_app_last__feasible_prefix.
  - intros other [Hotherreach Hothermono].
    destruct (reach_in_rounds_snoc_inv__feasible_prefix
      m rounds a i other Hi Hotherreach)
      as (prefix & endpoint & competing_inc & -> & Hprefixreach & Hcomp & Hendpoint).
    replace (i + 1 - 1) with (Zlength prefix).
    2: {
      unfold ReachInRounds in Hprefixreach.
      assert (Hzeq : Zlength (sublist 0 i a) = Zlength prefix).
      { rewrite !Zlength_correct. f_equal.
        apply Forall2_length in Hprefixreach. exact Hprefixreach. }
      rewrite Zlength_sublist in Hzeq by lia.
      lia. }
    rewrite Znth_app_last__feasible_prefix.
    apply Hminimal with competing_inc; try assumption.
    destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
    + assert (last = 0) as Hlastzero.
      { destruct Hprefix as [[Hzero Hlast] | [Hpositive _]]; lia. }
      rewrite Hendpoint, Hlastzero.
      pose proof (Z.mod_pos_bound (Znth i a 0 + competing_inc) m Hm).
      lia.
    + assert (Hplen : Zlength prefix = i).
      { unfold ReachInRounds in Hprefixreach.
        assert (Hzeq : Zlength (sublist 0 i a) = Zlength prefix).
        { rewrite !Zlength_correct. f_equal.
          apply Forall2_length in Hprefixreach. exact Hprefixreach. }
        rewrite Zlength_sublist in Hzeq by lia.
        lia. }
      specialize (Holdminimal prefix).
      assert (Hprefixmono : mono_nondec prefix).
      { eapply mono_nondec_app_left__feasible_prefix; eauto. }
      specialize (Holdminimal (conj Hprefixreach Hprefixmono)).
      assert (Hboundary : Znth (Zlength prefix - 1) prefix 0 <= endpoint).
      { eapply mono_nondec_snoc_boundary__feasible_prefix; eauto. lia. }
      rewrite Hplen in Hboundary.
      lia.
Qed.
Lemma mod_once__feasible_prefix :
  forall t m,
    0 < m -> 0 <= t < 2 * m -> m <= t ->
    t mod m = t - m.
Proof.
  intros t m Hm Hrange Hge.
  replace t with ((t - m) + m) by lia.
  rewrite Z.add_mod by lia.
  rewrite Z.mod_same by lia.
  rewrite Z.add_0_r.
  rewrite Z.mod_mod by lia.
  rewrite Z.mod_small by lia.
  lia.
Qed.
Lemma Forall2_Znth__feasible_results {A B : Type} :
  forall (R : A -> B -> Prop) a b da db i,
    Forall2 R a b ->
    0 <= i < Zlength a ->
    R (Znth i a da) (Znth i b db).
Proof.
  intros R a b da db i Hforall.
  revert i.
  induction Hforall as [| x y a b Hxy Hforall IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hine].
    + rewrite !Znth0_cons. exact Hxy.
    + rewrite !Znth_cons by lia.
      apply IH. lia.
Qed.
Lemma Forall2_sublist0__feasible_results {A B : Type} :
  forall (R : A -> B -> Prop) a b k,
    Forall2 R a b ->
    0 <= k ->
    Forall2 R (sublist 0 k a) (sublist 0 k b).
Proof.
  intros R a b k Hforall.
  revert k.
  induction Hforall as [| x y a b Hxy Hforall IH]; intros k Hk.
  - unfold sublist. rewrite !firstn_nil. simpl. constructor.
  - destruct (Z.eq_dec k 0) as [-> | Hkne].
    + unfold sublist. simpl. constructor.
    + rewrite !sublist_cons1 by lia.
      constructor; [exact Hxy |].
      apply IH. lia.
Qed.
Lemma ReachInRounds_Zlength__feasible_results :
  forall m rounds a b,
    ReachInRounds m rounds a b ->
    Zlength a = Zlength b.
Proof.
  intros m rounds a b Hreach.
  unfold ReachInRounds in Hreach.
  apply Forall2_length in Hreach.
  rewrite !Zlength_correct.
  lia.
Qed.
Lemma ReachInRounds_Znth__feasible_results :
  forall m rounds a b i,
    ReachInRounds m rounds a b ->
    0 <= i < Zlength a ->
    exists inc,
      0 <= inc <= rounds /\
      Znth i b 0 = (Znth i a 0 + inc) mod m.
Proof.
  intros m rounds a b i Hreach Hi.
  unfold ReachInRounds in Hreach.
  exact (@Forall2_Znth__feasible_results Z Z
    (fun before after =>
      exists inc, 0 <= inc <= rounds /\
        after = (before + inc) mod m)
    a b 0 0 i Hreach Hi).
Qed.
Lemma ReachInRounds_sublist0__feasible_results :
  forall m rounds a b k,
    ReachInRounds m rounds a b ->
    0 <= k <= Zlength a ->
    ReachInRounds m rounds (sublist 0 k a) (sublist 0 k b).
Proof.
  intros m rounds a b k Hreach Hk.
  unfold ReachInRounds in *.
  apply Forall2_sublist0__feasible_results; auto; lia.
Qed.
Lemma mono_nondec_sublist0__feasible_results :
  forall b k,
    mono_nondec b ->
    0 <= k <= Zlength b ->
    mono_nondec (sublist 0 k b).
Proof.
  intros b k Hmono Hk p q Hp Hpq Hq.
  rewrite Zlength_sublist0 in Hq by lia.
  rewrite !Znth_sublist0 by lia.
  apply Hmono; lia.
Qed.
Lemma greedy_prefix_complete_feasible__feasible_results :
  forall m a rounds i last,
    0 < Zlength a ->
    Zlength a <= i ->
    GreedyPrefixState m a rounds i last ->
    Feasible m a rounds.
Proof.
  intros m a rounds i last Hnonempty Hdone Hstate.
  unfold GreedyPrefixState in Hstate.
  destruct Hstate as [Hi [_ Hstate]].
  assert (Hi_eq : i = Zlength a) by lia.
  destruct Hstate as [[Hzero _] |
    [Hpos [b [Hreach [Hmono _]]]]].
  - lia.
  - unfold Feasible.
    exists b.
    subst i.
    rewrite sublist_self in Hreach by reflexivity.
    auto.
Qed.
Lemma greedy_prefix_failure_infeasible__feasible_results :
  forall m a rounds i last,
    1 <= m ->
    0 <= rounds ->
    0 <= Znth i a 0 ->
    i < Zlength a ->
    Znth i a 0 + rounds < last ->
    Znth i a 0 + rounds < m ->
    GreedyPrefixState m a rounds i last ->
    ~ Feasible m a rounds.
Proof.
  intros m a rounds i last Hm Hrounds Hai Hi Hbelow Hnowrap Hstate.
  intros [b [Hreach Hmono]].
  unfold GreedyPrefixState in Hstate.
  destruct Hstate as [Hibounds [_ Hstate]].
  destruct Hstate as [[Hi0 Hlast0] |
    [Hipos [prefix [Hprefix [Hprefix_mono
      [Hprefix_len [Hprefix_last Hminimal]]]]]]].
  - lia.
  - pose proof
      (ReachInRounds_Zlength__feasible_results
        m rounds a b Hreach) as Hlength.
    assert (Hprefix_reach :
      ReachInRounds m rounds
        (sublist 0 i a) (sublist 0 i b)).
    { apply ReachInRounds_sublist0__feasible_results; auto; lia. }
    assert (Hprefix_order : mono_nondec (sublist 0 i b)).
    { apply mono_nondec_sublist0__feasible_results; auto; lia. }
    pose proof (Hminimal (sublist 0 i b)
      (conj Hprefix_reach Hprefix_order)) as Hlast_lower.
    rewrite Znth_sublist0 in Hlast_lower by lia.
    assert (Hordered : Znth (i - 1) b 0 <= Znth i b 0).
    { apply Hmono; lia. }
    destruct
      (ReachInRounds_Znth__feasible_results
        m rounds a b i Hreach ltac:(lia))
      as [inc [Hinc Hcurrent]].
    rewrite Z.mod_small in Hcurrent by lia.
    lia.
Qed.
Lemma feasible_at_modulus_minus_one__solver_boundary :
  forall m a,
    1 <= m ->
    (forall i, 0 <= i < Zlength a -> 0 <= Znth i a 0 < m) ->
    Feasible m a (m - 1).
Proof.
  intros m a Hm Hbounds.
  assert (Ha : Forall (fun x => 0 <= x < m) a).
  {
    apply (proj2 (Forall_Znth (fun x => 0 <= x < m) 0 a)).
    exact Hbounds.
  }
  clear Hbounds.
  exists (map (fun _ => m - 1) a).
  split.
  - unfold ReachInRounds.
    induction Ha as [|x xs Hx Hxs IH].
    + constructor.
    + constructor.
      * exists (m - 1 - x).
        split; [lia|].
        replace (x + (m - 1 - x)) with (m - 1) by lia.
        rewrite Z.mod_small; lia.
      * exact IH.
  - clear Ha.
    induction a as [|x xs IH].
    + apply mono_nondec_nil.
    + simpl.
      apply (proj2 (mono_nondec_cons (m - 1) (map (fun _ : Z => m - 1) xs))).
      split.
      * apply Forall_forall.
        intros y Hy.
        apply in_map_iff in Hy.
        destruct Hy as [z [-> _]].
        lia.
      * exact IH.
Qed.
Lemma bounded_minimum_feasible_round__solver_boundary :
  forall m a upper,
    a <> nil ->
    Feasible m a upper ->
    exists out, Spec m a out /\ 0 <= out <= upper.
Proof.
  intros m a upper Hnonempty Hupper.
  assert (Hround_nonneg : forall rounds, Feasible m a rounds -> 0 <= rounds).
  {
    intros rounds [b [Hreach _]].
    destruct a as [|x xs]; [contradiction|].
    inversion Hreach as [|x' y' xs' ys' Hxy Htail]; subst.
    destruct Hxy as [inc [[Hinc0 Hincupper] _]].
    lia.
  }
  assert (Hleast : forall x, Feasible m a x ->
      exists y, Feasible m a y /\ y <= x /\
        forall z, Feasible m a z -> y <= z).
  {
    intro x.
    pattern x.
    apply (well_founded_induction (Zwf_well_founded 0)).
    intros current IH Hcurrent.
    destruct (classic (exists smaller, Feasible m a smaller /\ smaller < current))
      as [[smaller [Hsmaller Hlt]] | Hnone].
    - assert (Hrel : Zwf 0 smaller current).
      { unfold Zwf. split; [apply Hround_nonneg in Hcurrent; lia|exact Hlt]. }
      destruct (IH smaller Hrel Hsmaller) as [y [Hy [Hysmall Hmin]]].
      exists y.
      split; [exact Hy|].
      split; [lia|exact Hmin].
    - exists current.
      split; [exact Hcurrent|].
      split; [lia|].
      intros z Hz.
      destruct (Z_lt_ge_dec z current) as [Hlt|Hge]; [exfalso|lia].
      apply Hnone.
      exists z; split; assumption.
  }
  destruct (Hleast upper Hupper) as [out [Hout [Hout_upper Hminimal]]].
  destruct Hout as [b [Hreach Hmono]].
  exists out.
  split.
  - unfold Spec, min_value_of_subset, min_object_of_subset.
    exists (out, b).
    split.
    + split.
      * simpl. split; assumption.
      * intros [rounds other] Hcandidate.
        simpl in *.
        apply Hminimal.
        exists other.
        exact Hcandidate.
    + reflexivity.
  - split.
    + apply Hround_nonneg.
      exists b; split; assumption.
    + exact Hout_upper.
Qed.
Lemma search_state_closed_interval__solver_boundary :
  forall m a lo hi ans,
    lo > hi ->
    SearchState m a lo hi ans ->
    Spec m a ans.
Proof.
  intros m a lo hi ans Hclosed [_ [_ [out [Hspec Hwhere]]]].
  destruct Hwhere as [[Hlo Hhi] | Heq].
  - lia.
  - subst out. exact Hspec.
Qed.
Lemma feasible_monotone_rounds__solver_transitions :
  forall m a rounds1 rounds2,
    rounds1 <= rounds2 ->
    Feasible m a rounds1 ->
    Feasible m a rounds2.
Proof.
  intros m a rounds1 rounds2 Hrounds [b [Hreach Hmono]].
  assert (Hreach2 : ReachInRounds m rounds2 a b).
  { clear Hmono.
    unfold ReachInRounds in *.
    induction Hreach.
    - constructor.
    - constructor.
      + destruct H as [inc [[Hinc0 Hinc1] Heq]].
        exists inc; repeat split; try lia; exact Heq.
      + exact IHHreach. }
  exists b; split; assumption.
Qed.
Lemma spec_le_any_feasible_round__solver_transitions :
  forall m a out rounds,
    Spec m a out ->
    Feasible m a rounds ->
    out <= rounds.
Proof.
  intros m a out rounds Hspec [b [Hreach Hmono]].
  unfold Spec, min_value_of_subset, min_object_of_subset in Hspec.
  destruct Hspec as [[best best_list] [[[Hbest_reach Hbest_mono] Hleast] Heq]].
  simpl in Heq; subst best.
  specialize (Hleast (rounds, b)).
  simpl in Hleast.
  apply Hleast; split; assumption.
Qed.
Lemma spec_is_feasible_round__solver_transitions :
  forall m a out,
    Spec m a out ->
    Feasible m a out.
Proof.
  intros m a out Hspec.
  unfold Spec, min_value_of_subset, min_object_of_subset in Hspec.
  destruct Hspec as [[best best_list] [[[Hreach Hmono] Hleast] Heq]].
  simpl in Heq; subst best.
  exists best_list; split; assumption.
Qed.
Lemma search_state_feasible_mid_step__solver_transitions :
  forall m a lo hi ans mid,
    SearchState m a lo hi ans ->
    Feasible m a mid ->
    SearchState m a lo (mid - 1) mid.
Proof.
  intros m a lo hi ans mid
    [Hans_feasible [Hlo_ans [out [Hspec Hout]]]] Hmid_feasible.
  pose proof
    (spec_le_any_feasible_round__solver_transitions
       m a out mid Hspec Hmid_feasible) as Hout_mid.
  assert (Hlo_out : lo <= out).
  { destruct Hout as [[Hlo_out Hout_hi] | Hout_ans]; [exact Hlo_out | lia]. }
  repeat split.
  - exact Hmid_feasible.
  - lia.
  - exists out; split; [exact Hspec |].
    destruct (Z.eq_dec out mid) as [Heq | Hneq].
    + right; exact Heq.
    + left; lia.
Qed.
Lemma search_state_infeasible_mid_step__solver_transitions :
  forall m a lo hi ans mid,
    SearchState m a lo hi ans ->
    ~ Feasible m a mid ->
    SearchState m a (mid + 1) hi ans.
Proof.
  intros m a lo hi ans mid
    [Hans_feasible [Hlo_ans [out [Hspec Hout]]]] Hmid_infeasible.
  assert (Hmid_ans : mid < ans).
  { destruct (Z_le_gt_dec ans mid) as [Hans_mid | Hmid_ans]; [| lia].
    exfalso; apply Hmid_infeasible.
    eapply feasible_monotone_rounds__solver_transitions; eauto. }
  repeat split.
  - exact Hans_feasible.
  - lia.
  - exists out; split; [exact Hspec |].
    destruct Hout as [[Hlo_out Hout_hi] | Hout_ans].
    + left; split; [| exact Hout_hi].
      assert (Hout_feasible : Feasible m a out).
      { apply spec_is_feasible_round__solver_transitions; exact Hspec. }
      destruct (Z_le_gt_dec out mid) as [Hout_mid | Hmid_out]; [| lia].
      exfalso; apply Hmid_infeasible.
      eapply feasible_monotone_rounds__solver_transitions; eauto.
    + right; exact Hout_ans.
Qed.
Lemma midpoint_bounds__solver_transitions :
  forall lo hi,
    0 <= lo ->
    lo <= hi ->
    lo <= (lo + hi) ÷ 2 <= hi.
Proof.
  intros lo hi Hlo0 Hlo_hi.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (Z.div_mod (lo + hi) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (lo + hi) 2 ltac:(lia)) as Hmod.
  lia.
Qed.
