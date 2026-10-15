Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition FirstOccurrence (s : list Z) (c i : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : Z =>
      0 <= candidate < Zlength s /\ Znth candidate s 0 = c)
    (fun candidate => candidate) i.

Definition ValidObfuscatedNames (s : list Z) : Prop :=
  Forall (fun c => 97 <= c <= 122) s /\
  forall c d j,
    97 <= c -> c < d -> d <= 122 ->
    FirstOccurrence s d j ->
    exists i, FirstOccurrence s c i /\ i < j.

Definition Pre (s : list Z) : Prop :=
  1 <= Zlength s <= 500 /\
  Forall (fun c => 97 <= c <= 122) s.

Definition Spec (s : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\ (out = 1 <-> ValidObfuscatedNames s).

Definition ObfuscationPrefixState (s : list Z) (processed next : Z) : Prop :=
  0 <= processed <= Zlength s /\
  97 <= next <= 122 /\
  (forall c d j,
     97 <= c -> c < d -> d <= 122 ->
     FirstOccurrence s d j -> j < processed ->
     exists k, FirstOccurrence s c k /\ k < j) /\
  (forall k, 0 <= k < processed -> Znth k s 0 <= next) /\
  (forall c, 97 <= c < next ->
     exists k, FirstOccurrence s c k /\ k < processed) /\
  (next < 122 ->
     forall k, 0 <= k < processed -> Znth k s 0 <> next).

Require Import Coq.micromega.Lia.
Lemma obfuscation_prefix_init__initialization :
  forall text,
    1 <= Zlength text ->
    (forall i, 0 <= i < Zlength text ->
      97 <= Znth i text 0 <= 122) ->
    ObfuscationPrefixState text 0 97.
Proof.
  intros text Hlength Hchars.
  unfold ObfuscationPrefixState.
  split.
  - lia.
  - split.
    + lia.
    + split.
      * intros c d j Hc Hcd Hd Hfirst Hj.
        unfold FirstOccurrence, min_value_of_subset,
          min_object_of_subset in Hfirst.
        destruct Hfirst as [candidate [Hobject Heq]].
        destruct Hobject as [Hmember Hminimal].
        destruct Hmember as [[Hcandidate_nonnegative Hcandidate_bound]
          Hcandidate_value].
        lia.
      * split.
        -- intros k Hk.
           lia.
        -- split.
           ++ intros c Hc.
              lia.
           ++ intros Hnext k Hk.
              lia.
Qed.
Lemma app_zero_nonzero_index_lt_length__prefix_transitions :
  forall (text : list Z) (i : Z),
    0 <= i <= Zlength text ->
    Znth i (text ++ (0 :: nil)) 0 <> 0 ->
    i < Zlength text.
Proof.
  intros text i Hi Hnonzero.
  destruct Hi as [Hi0 Hile].
  destruct (Z.eq_dec i (Zlength text)) as [Heq | Hneq]; [|lia].
  subst i.
  rewrite app_Znth2 in Hnonzero by lia.
  replace (Zlength text - Zlength text) with 0 in Hnonzero by lia.
  rewrite Znth0_cons in Hnonzero.
  contradiction.
Qed.
Lemma obfuscation_prefix_step_equal_increment__prefix_transitions :
  forall (text : list Z) (i next : Z),
    0 <= i < Zlength text ->
    Znth i text 0 = next ->
    next < 122 ->
    ObfuscationPrefixState text i next ->
    ObfuscationPrefixState text (i + 1) (next + 1).
Proof.
  intros text i next Hi Hcurrent Hnext Hstate.
  unfold ObfuscationPrefixState in *.
  destruct Hstate as
      [Hprocessed [Hnext_bounds
       [Horder [Hprefix [Hcomplete Habsent]]]]].
  destruct Hnext_bounds as [Hstate_next_lower Hstate_next_upper].
  repeat split.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros c d j Hc Hcd Hd Hfirst Hj.
    destruct (Z_lt_ge_dec j i) as [Hji | Hij].
    + eapply Horder; eauto.
    + assert (j = i) by lia.
      subst j.
      unfold FirstOccurrence, min_value_of_subset,
        min_object_of_subset in Hfirst.
      destruct Hfirst as [a [[[[Ha0 Halen] Havalue] Hamin] Hai]].
      subst a.
      assert (d = next) by congruence.
      subst d.
      specialize (Hcomplete c ltac:(lia)).
      destruct Hcomplete as [k [Hfirst_c Hki]].
      exists k; split; [exact Hfirst_c | lia].
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hik].
    + specialize (Hprefix k ltac:(lia)); lia.
    + assert (k = i) by lia.
      subst k; lia.
  - intros c Hc.
    destruct (Z_lt_ge_dec c next) as [Hcn | Hnc].
    + specialize (Hcomplete c ltac:(lia)).
      destruct Hcomplete as [k [Hfirst Hki]].
      exists k; split; [exact Hfirst | lia].
    + assert (c = next) by lia.
      subst c.
      exists i; split; [|lia].
      unfold FirstOccurrence, min_value_of_subset,
        min_object_of_subset.
      exists i; split; [|reflexivity].
      split.
      * split; [exact Hi | exact Hcurrent].
      * intros b [[Hb0 Hblen] Hbvalue].
        destruct (Z_lt_ge_dec b i) as [Hbi | Hib]; [|lia].
        specialize (Habsent Hnext b ltac:(lia)).
        contradiction.
  - intros Hnext_new k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hik].
    + specialize (Hprefix k ltac:(lia)); lia.
    + assert (k = i) by lia.
      subst k; lia.
Qed.
Lemma obfuscation_prefix_step_below__prefix_transitions :
  forall (text : list Z) (i next : Z),
    0 <= i < Zlength text ->
    97 <= Znth i text 0 ->
    Znth i text 0 <= next ->
    Znth i text 0 <> next ->
    ObfuscationPrefixState text i next ->
    ObfuscationPrefixState text (i + 1) next.
Proof.
  intros text i next Hi Hcurrent_lower Hcurrent_upper
    Hcurrent_neq Hstate.
  unfold ObfuscationPrefixState in *.
  destruct Hstate as
      [Hprocessed [Hnext_bounds
       [Horder [Hprefix [Hcomplete Habsent]]]]].
  destruct Hnext_bounds as [Hnext_lower Hnext_upper].
  repeat split.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros c d j Hc Hcd Hd Hfirst Hj.
    destruct (Z_lt_ge_dec j i) as [Hji | Hij].
    + eapply Horder; eauto.
    + assert (j = i) by lia.
      subst j.
      unfold FirstOccurrence, min_value_of_subset,
        min_object_of_subset in Hfirst.
      destruct Hfirst as [a [[[[Ha0 Halen] Havalue] Hamin] Hai]].
      subst a.
      assert (d = Znth i text 0) by congruence.
      subst d.
      assert (Znth i text 0 < next) by lia.
      specialize (Hcomplete c ltac:(lia)).
      destruct Hcomplete as [k [Hfirst_c Hki]].
      exists k; split; [exact Hfirst_c | lia].
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hik].
    + apply Hprefix; lia.
    + assert (k = i) by lia.
      subst k; exact Hcurrent_upper.
  - intros c Hc.
    specialize (Hcomplete c Hc).
    destruct Hcomplete as [k [Hfirst Hki]].
    exists k; split; [exact Hfirst | lia].
  - intros Hnext_lt k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hik].
    + apply Habsent; lia.
    + assert (k = i) by lia.
      subst k; exact Hcurrent_neq.
Qed.
Lemma obfuscation_prefix_step_max__prefix_transitions :
  forall (text : list Z) (i next : Z),
    0 <= i < Zlength text ->
    Znth i text 0 = next ->
    next >= 122 ->
    next <= 122 ->
    ObfuscationPrefixState text i next ->
    ObfuscationPrefixState text (i + 1) next.
Proof.
  intros text i next Hi Hcurrent Hnext_lower Hnext_upper Hstate.
  assert (next = 122) by lia.
  subst next.
  unfold ObfuscationPrefixState in *.
  destruct Hstate as
      [Hprocessed [Hnext_bounds
       [Horder [Hprefix [Hcomplete Habsent]]]]].
  destruct Hnext_bounds as [Hstate_next_lower Hstate_next_upper].
  repeat split.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros c d j Hc Hcd Hd Hfirst Hj.
    destruct (Z_lt_ge_dec j i) as [Hji | Hij].
    + eapply Horder; eauto.
    + assert (j = i) by lia.
      subst j.
      unfold FirstOccurrence, min_value_of_subset,
        min_object_of_subset in Hfirst.
      destruct Hfirst as [a [[[[Ha0 Halen] Havalue] Hamin] Hai]].
      subst a.
      assert (d = 122) by congruence.
      subst d.
      specialize (Hcomplete c ltac:(lia)).
      destruct Hcomplete as [k [Hfirst_c Hki]].
      exists k; split; [exact Hfirst_c | lia].
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hik].
    + apply Hprefix; lia.
    + assert (k = i) by lia.
      subst k; lia.
  - intros c Hc.
    specialize (Hcomplete c Hc).
    destruct Hcomplete as [k [Hfirst Hki]].
    exists k; split; [exact Hfirst | lia].
  - lia.
Qed.
Lemma app_zero_terminator_index_eq_length__final_results :
  forall (text : list Z) i,
    (forall k, 0 <= k < Zlength text -> 97 <= Znth k text 0) ->
    0 <= i <= Zlength text ->
    Znth i (text ++ 0 :: nil) 0 = 0 ->
    i = Zlength text.
Proof.
  intros text i Hlower Hi Hzero.
  destruct (Z_lt_ge_dec i (Zlength text)) as [Hlt | Hge].
  - rewrite app_Znth1 in Hzero by lia.
    specialize (Hlower i ltac:(lia)).
    lia.
  - lia.
Qed.
Lemma obfuscation_prefix_success_spec__final_results :
  forall (text : list Z) next,
    (forall k, 0 <= k < Zlength text ->
       97 <= Znth k text 0 <= 122) ->
    ObfuscationPrefixState text (Zlength text) next ->
    Spec text 1.
Proof.
  intros text next Hbounds Hstate.
  unfold Spec.
  split.
  - right; reflexivity.
  - split.
    + intros _.
      unfold ValidObfuscatedNames.
      split.
      * apply (proj2 (Forall_Znth (fun c => 97 <= c <= 122) 0 text)).
        exact Hbounds.
      * intros c d j Hc Hcd Hd Hfirst.
        destruct Hstate as [_ [_ [Hordered _]]].
        apply Hordered with (c := c) (d := d) (j := j); auto.
        unfold FirstOccurrence, min_value_of_subset,
          min_object_of_subset in Hfirst.
        destruct Hfirst as [a [[[[Ha0 Halen] Haz] Hminimal] Haj]].
        simpl in Haj.
        subst a.
        exact Halen.
    + intros _; reflexivity.
Qed.
Lemma obfuscation_prefix_failure_spec__final_results :
  forall (text : list Z) next i,
    Znth i (text ++ 0 :: nil) 0 > next ->
    (forall k, 0 <= k < Zlength text ->
       97 <= Znth k text 0 <= 122) ->
    0 <= i <= Zlength text ->
    97 <= next <= 122 ->
    ObfuscationPrefixState text i next ->
    Znth i (text ++ 0 :: nil) 0 <> 0 ->
    Spec text 0.
Proof.
  intros text next i Hgreater Hbounds Hi Hnext Hstate Hnonzero.
  assert (Hi_lt : i < Zlength text).
  {
    destruct (Z_lt_ge_dec i (Zlength text)) as [Hlt | Hge]; auto.
    assert (i = Zlength text) by lia.
    subst i.
    rewrite app_Znth2 in Hnonzero by lia.
    replace (Zlength text - Zlength text) with 0 in Hnonzero by lia.
    rewrite Znth0_cons in Hnonzero.
    contradiction.
  }
  rewrite app_Znth1 in Hgreater by lia.
  pose proof (Hbounds i ltac:(lia)) as Hcurrent_bounds.
  unfold Spec.
  split.
  - left; reflexivity.
  - split.
    + intros Habsurd; lia.
    + intros Hvalid.
      unfold ValidObfuscatedNames in Hvalid.
      destruct Hvalid as [_ Hvalid].
      destruct (min_n_in_range
                  (fun k => Znth k text 0 = Znth i text 0)
                  (Zlength text)) as [j [Hjchar [[Hj0 Hjle] Hjmin]]].
      * apply Zlength_nonneg.
      * exists i; split; [lia | reflexivity].
      * assert (Hjlt : j < Zlength text).
        {
          destruct (Z_lt_ge_dec j (Zlength text)) as [Hlt | Hge]; auto.
          assert (j = Zlength text) by lia.
          subst j.
          assert (Hzero : Znth (Zlength text) text 0 = 0).
          {
            pose proof
              (app_Znth2 0 text nil (Zlength text) ltac:(lia)) as Happ.
            rewrite app_nil_r in Happ.
            replace (Zlength text - Zlength text) with 0 in Happ by lia.
            exact Happ.
          }
          lia.
        }
        assert (Hfirst_d : FirstOccurrence text (Znth i text 0) j).
        {
          unfold FirstOccurrence, min_value_of_subset,
            min_object_of_subset.
          exists j.
          split.
          - split.
            + split; [split; assumption | exact Hjchar].
            + intros b [[Hb0 Hblt] Hbchar].
              apply Hjmin; [lia | exact Hbchar].
          - reflexivity.
        }
        destruct (Hvalid next (Znth i text 0) j) as
            [k [Hfirst_next Hkj]]; try lia; auto.
        destruct Hstate as [_ [_ [_ [_ [_ Hnext_absent]]]]].
        assert (Hnext_lt_122 : next < 122) by lia.
        specialize (Hnext_absent Hnext_lt_122 k).
        unfold FirstOccurrence, min_value_of_subset,
          min_object_of_subset in Hfirst_next.
        destruct Hfirst_next as
            [a [[[[Ha0 Halen] Haz] Hminimal] Hak]].
        simpl in Hak.
        subst a.
        assert (Hji : j <= i).
        { apply Hjmin; [lia | reflexivity]. }
        specialize (Hnext_absent ltac:(lia)).
        contradiction.
Qed.
