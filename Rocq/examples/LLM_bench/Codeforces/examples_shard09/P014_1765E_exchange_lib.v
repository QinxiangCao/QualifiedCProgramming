Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Per-case signature: solve_case(n,a,b:Z)->Z. Output is the minimum quests
   from which a legal sequence of sell/buy exchanges can reach n silver. *)
Definition ExchangeStep (a b : Z) (s1 s2 : Z*Z) : Prop :=
  let '(g,x):=s1 in let '(g',x'):=s2 in
  (g>=1 /\ g' = g - 1 /\ x' = x + a) \/ (x >= b /\ g' = g + 1 /\ x' = x - b).
Definition ReachesSilver (n a b q : Z) : Prop :=
  exists states : list (Z*Z),
    states<>[] /\ Znth 0 states (0,0)=(q,0) /\
    (forall i, 0 <= i < Zlength states - 1 ->
       ExchangeStep a b (Znth i states (0,0)) (Znth (i+1) states (0,0))) /\
    let '(g,x):=Znth (Zlength states-1) states (0,0) in g>=0 /\ x>=n.
Definition Pre (n a b : Z) : Prop :=
  (* Stated explicitly in the P014 solver Require, which therefore omits the
     Pre(...) call:
       1 <= n <= 10000000 /\ 1 <= a <= 50 /\ 1 <= b <= 50. *)
  True.
Definition Spec (n a b out : Z) : Prop := min_value_of_subset Z.le (fun q=>q>=0 /\ ReachesSilver n a b q) (fun x => x) out.

Require Import Coq.micromega.Lia.
Lemma exchange_prepend_steps__exchange_minimum :
  forall a b (s1 s2 : Z * Z) states,
    states <> [] ->
    Znth 0 states (0, 0) = s2 ->
    ExchangeStep a b s1 s2 ->
    (forall i, 0 <= i < Zlength states - 1 ->
       ExchangeStep a b (Znth i states (0, 0))
                        (Znth (i + 1) states (0, 0))) ->
    forall i, 0 <= i < Zlength (s1 :: states) - 1 ->
      ExchangeStep a b (Znth i (s1 :: states) (0, 0))
                       (Znth (i + 1) (s1 :: states) (0, 0)).
Proof.
  intros a b s1 s2 states Hne Hhead Hfirst Hsteps i Hi.
  destruct (Z.eq_dec i 0) as [-> | Hnz].
  - rewrite Znth0_cons.
    rewrite Znth_cons by lia.
    replace (0 + 1 - 1) with 0 by lia.
    now rewrite Hhead.
  - rewrite !Znth_cons by lia.
    replace (i + 1 - 1) with i by lia.
    specialize (Hsteps (i - 1)).
    replace (i - 1 + 1) with i in Hsteps by lia.
    apply Hsteps.
    rewrite Zlength_cons in Hi.
    lia.
Qed.
Lemma exchange_prepend_last__exchange_minimum :
  forall (s : Z * Z) states,
    states <> [] ->
    Znth (Zlength (s :: states) - 1) (s :: states) (0, 0) =
    Znth (Zlength states - 1) states (0, 0).
Proof.
  intros s states Hne.
  destruct states as [|t rest]; [contradiction|].
  rewrite !Zlength_cons.
  rewrite Znth_cons by (pose proof (Zlength_nonneg rest); lia).
  f_equal.
  lia.
Qed.
Lemma exchange_sell_path__exchange_minimum :
  forall a b (k : nat) x,
    exists states : list (Z * Z),
      states <> [] /\
      Znth 0 states (0, 0) = (Z.of_nat k, x) /\
      (forall i, 0 <= i < Zlength states - 1 ->
         ExchangeStep a b (Znth i states (0, 0))
                          (Znth (i + 1) states (0, 0))) /\
      Znth (Zlength states - 1) states (0, 0) =
        (0, x + a * Z.of_nat k).
Proof.
  intros a b k.
  induction k as [|k IH]; intros x.
  - exists [(0, x)].
    split; [discriminate|].
    split; [reflexivity|].
    split.
    + intros i Hi.
      rewrite Zlength_cons, Zlength_nil in Hi.
      lia.
    + rewrite Zlength_cons, Zlength_nil.
      replace (Z.succ 0 - 1) with 0 by lia.
      rewrite Znth0_cons.
      simpl.
      f_equal; lia.
  - destruct (IH (x + a)) as (states & Hne & Hhead & Hsteps & Hlast).
    exists ((Z.of_nat (S k), x) :: states).
    split; [discriminate|].
    split; [reflexivity|].
    split.
    + eapply exchange_prepend_steps__exchange_minimum; eauto.
      unfold ExchangeStep.
      left.
      rewrite Nat2Z.inj_succ.
      nia.
    + rewrite exchange_prepend_last__exchange_minimum by exact Hne.
      rewrite Hlast, Nat2Z.inj_succ.
      f_equal.
      nia.
Qed.
Lemma exchange_sell_trace__exchange_minimum :
  forall n a b q,
    1 <= a -> 0 <= q -> n <= a * q -> ReachesSilver n a b q.
Proof.
  intros n a b q Ha Hq Hn.
  destruct (exchange_sell_path__exchange_minimum a b (Z.to_nat q) 0)
    as (states & Hne & Hhead & Hsteps & Hlast).
  rewrite Z2Nat.id in Hhead, Hlast by lia.
  exists states.
  split; [exact Hne|].
  split; [exact Hhead|].
  split; [exact Hsteps|].
  rewrite Hlast.
  simpl.
  nia.
Qed.
Lemma exchange_path_potential__exchange_minimum :
  forall a b states (start final : Z * Z),
    0 <= a -> a <= b ->
    states <> [] ->
    Znth 0 states (0, 0) = start ->
    (forall i, 0 <= i < Zlength states - 1 ->
       ExchangeStep a b (Znth i states (0, 0))
                        (Znth (i + 1) states (0, 0))) ->
    Znth (Zlength states - 1) states (0, 0) = final ->
    a * fst final + snd final <= a * fst start + snd start.
Proof.
  intros a b states.
  induction states as [|s1 rest IH]; intros start final Ha Hab Hne Hhead Hsteps Hlast.
  - contradiction.
  - destruct rest as [|s2 rest].
    + simpl in Hhead, Hlast.
      subst start final.
      lia.
    + assert (Hfirst : ExchangeStep a b s1 s2).
      { specialize (Hsteps 0).
        rewrite Znth0_cons, Znth_cons in Hsteps by lia.
        replace (0 + 1 - 1) with 0 in Hsteps by lia.
        rewrite Znth0_cons in Hsteps.
        apply Hsteps.
        repeat rewrite Zlength_cons.
        pose proof (Zlength_nonneg rest).
        lia. }
      assert (Htail : forall i, 0 <= i < Zlength (s2 :: rest) - 1 ->
          ExchangeStep a b (Znth i (s2 :: rest) (0, 0))
                           (Znth (i + 1) (s2 :: rest) (0, 0))).
      { intros i Hi.
        specialize (Hsteps (i + 1)).
        rewrite (Znth_cons (0, 0) (i + 1) s1 (s2 :: rest)) in Hsteps by lia.
        rewrite (Znth_cons (0, 0) (i + 1 + 1) s1 (s2 :: rest)) in Hsteps by lia.
        replace (i + 1 - 1) with i in Hsteps by lia.
        replace (i + 1 + 1 - 1) with (i + 1) in Hsteps by lia.
        apply Hsteps.
        rewrite !Zlength_cons in *.
        lia. }
      assert (Hlast_tail :
          Znth (Zlength (s2 :: rest) - 1) (s2 :: rest) (0, 0) = final).
      { rewrite <- Hlast.
        symmetry.
        apply exchange_prepend_last__exchange_minimum.
        discriminate. }
      specialize (IH s2 final Ha Hab ltac:(discriminate) ltac:(reflexivity)
                     Htail Hlast_tail).
      rewrite Znth0_cons in Hhead.
      subst start.
      destruct s1 as [g1 x1], s2 as [g2 x2].
      simpl in *.
      unfold ExchangeStep in Hfirst.
      destruct Hfirst as [(? & ? & ?) | (? & ? & ?)]; subst; nia.
Qed.
Lemma exchange_nonprofitable_lower_bound__exchange_minimum :
  forall n a b q,
    0 <= a -> a <= b -> ReachesSilver n a b q -> n <= a * q.
Proof.
  intros n a b q Ha Hab Hreach.
  destruct Hreach as (states & Hne & Hhead & Hsteps & Hfinal).
  destruct (Znth (Zlength states - 1) states (0, 0)) as [g x] eqn:Hlast.
  simpl in Hfinal.
  destruct Hfinal as [Hg Hx].
  pose proof (exchange_path_potential__exchange_minimum
                a b states (q, 0) (g, x) Ha Hab Hne Hhead Hsteps Hlast) as Hpot.
  simpl in Hpot.
  nia.
Qed.
Lemma exchange_cycle_path__exchange_minimum :
  forall a b (k : nat) x,
    b <= x -> b <= a ->
    exists states : list (Z * Z),
      states <> [] /\
      Znth 0 states (0, 0) = (0, x) /\
      (forall i, 0 <= i < Zlength states - 1 ->
         ExchangeStep a b (Znth i states (0, 0))
                          (Znth (i + 1) states (0, 0))) /\
      Znth (Zlength states - 1) states (0, 0) =
        (0, x + Z.of_nat k * (a - b)).
Proof.
  intros a b k.
  induction k as [|k IH]; intros x Hxb Hba.
  - exists [(0, x)].
    split; [discriminate|].
    split; [reflexivity|].
    split.
    + intros i Hi.
      rewrite Zlength_cons, Zlength_nil in Hi.
      lia.
    + rewrite Zlength_cons, Zlength_nil.
      replace (Z.succ 0 - 1) with 0 by lia.
      rewrite Znth0_cons.
      simpl.
      f_equal; lia.
  - destruct (IH (x - b + a) ltac:(lia) Hba)
      as (states & Hne & Hhead & Hsteps & Hlast).
    exists ((0, x) :: (1, x - b) :: states).
    split; [discriminate|].
    split; [reflexivity|].
    split.
    + eapply exchange_prepend_steps__exchange_minimum.
      * discriminate.
      * reflexivity.
      * unfold ExchangeStep. right. nia.
      * eapply exchange_prepend_steps__exchange_minimum; eauto.
        unfold ExchangeStep. left. nia.
    + rewrite exchange_prepend_last__exchange_minimum by discriminate.
      rewrite exchange_prepend_last__exchange_minimum by exact Hne.
      rewrite Hlast, Nat2Z.inj_succ.
      f_equal.
      nia.
Qed.
Lemma exchange_profitable_one_reachable__exchange_minimum :
  forall n a b,
    a > b -> b >= 1 -> n >= 1 -> ReachesSilver n a b 1.
Proof.
  intros n a b Hab Hb Hn.
  destruct (exchange_cycle_path__exchange_minimum a b (Z.to_nat n) a
              ltac:(lia) ltac:(lia))
    as (states & Hne & Hhead & Hsteps & Hlast).
  exists ((1, 0) :: states).
  split; [discriminate|].
  split; [reflexivity|].
  split.
  - eapply exchange_prepend_steps__exchange_minimum; eauto.
    unfold ExchangeStep. left. nia.
  - rewrite exchange_prepend_last__exchange_minimum by exact Hne.
    rewrite Hlast, Z2Nat.id by lia.
    simpl.
    nia.
Qed.
Lemma exchange_zero_unreachable__exchange_minimum :
  forall n a b,
    b >= 1 -> n >= 1 -> ~ ReachesSilver n a b 0.
Proof.
  intros n a b Hb Hn Hreach.
  destruct Hreach as (states & Hne & Hhead & Hsteps & Hfinal).
  destruct states as [|s1 rest]; [contradiction|].
  rewrite Znth0_cons in Hhead.
  subst s1.
  destruct rest as [|s2 rest].
  - rewrite Zlength_cons, Zlength_nil in Hfinal.
    simpl in Hfinal.
    lia.
  - specialize (Hsteps 0).
    rewrite Znth0_cons, Znth_cons in Hsteps by lia.
    replace (0 + 1 - 1) with 0 in Hsteps by lia.
    rewrite Znth0_cons in Hsteps.
    assert (0 <= 0 < Zlength ((0, 0) :: s2 :: rest) - 1).
    { repeat rewrite Zlength_cons.
      pose proof (Zlength_nonneg rest).
      lia. }
    specialize (Hsteps H).
    unfold ExchangeStep in Hsteps.
    destruct s2 as [g2 x2].
    simpl in Hsteps.
    nia.
Qed.
Lemma exchange_nonprofitable_spec__exchange_minimum :
  forall n a b,
    1 <= n -> 1 <= a -> a <= b ->
    Spec n a b (((n + a) - 1) / a).
Proof.
  intros n a b Hn Ha Hab.
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists (((n + a) - 1) / a).
  split.
  - split.
    + split.
      * pose proof (Z.div_mod ((n + a) - 1) a ltac:(lia)) as Hdiv.
        pose proof (Z.mod_pos_bound ((n + a) - 1) a ltac:(lia)) as Hmod.
        nia.
      * assert (Hq0 : 0 <= ((n + a) - 1) / a).
        { pose proof (Z.div_mod ((n + a) - 1) a ltac:(lia)) as Hdiv.
          pose proof (Z.mod_pos_bound ((n + a) - 1) a ltac:(lia)) as Hmod.
          nia. }
        assert (Hcover : n <= a * (((n + a) - 1) / a)).
        { pose proof (Z.div_mod ((n + a) - 1) a ltac:(lia)) as Hdiv.
          pose proof (Z.mod_pos_bound ((n + a) - 1) a ltac:(lia)) as Hmod.
          nia. }
        apply exchange_sell_trace__exchange_minimum; lia.
    + intros q [Hq Hreach].
      simpl.
      pose proof (exchange_nonprofitable_lower_bound__exchange_minimum
                    n a b q ltac:(lia) ltac:(lia) Hreach) as Hlower.
      assert (((n + a) - 1) / a < q + 1).
      { apply Z.div_lt_upper_bound; nia. }
      lia.
  - reflexivity.
Qed.
Lemma exchange_profitable_spec__exchange_minimum :
  forall n a b,
    a > b -> b >= 1 -> n >= 1 -> Spec n a b 1.
Proof.
  intros n a b Hab Hb Hn.
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists 1.
  split.
  - split.
    + split.
      * lia.
      * apply exchange_profitable_one_reachable__exchange_minimum; lia.
    + intros q [Hq Hreach].
      simpl.
      destruct (Z.eq_dec q 0) as [-> | Hq0].
      * exfalso.
        exact (exchange_zero_unreachable__exchange_minimum n a b Hb Hn Hreach).
      * lia.
  - reflexivity.
Qed.
