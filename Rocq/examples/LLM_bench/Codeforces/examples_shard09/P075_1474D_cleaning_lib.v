Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition CleanStep (a b : list Z) : Prop :=
  exists i, 0 <= i < Zlength a - 1 /\ Znth i a 0 > 0 /\ Znth (i + 1) a 0 > 0 /\
  b = replace_Znth (i + 1) (Znth (i + 1) a 0 - 1) (replace_Znth i (Znth i a 0 - 1) a).
Definition Cleanable (a : list Z) : Prop :=
  exists (base : list Z) (st : list (list Z)),
   (base = a \/ exists i, 0 <= i < Zlength a - 1 /\
      base = replace_Znth (i + 1) (Znth i a 0) (replace_Znth i (Znth (i + 1) a 0) a)) /\
   st <> [] /\ Znth 0 st [] = base /\ Forall (fun x => x = 0) (Znth (Zlength st - 1) st []) /\
   forall q, 0 <= q < Zlength st - 1 -> CleanStep (Znth q st []) (Znth (q + 1) st []).
Definition Pre (a : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P075 solver Require, which
     therefore omits the Pre(...) call:
       2 <= Zlength a <= 200000 /\ Forall(fun x => 1 <= x <= 1000000000)a. *)
  True.
Definition Spec (a : list Z) (out : Z) : Prop :=
  (out = 1 /\ Cleanable a) \/ (out = 0 /\ ~Cleanable a).

(* The logical lists used below describe the scratch tables written by the C
   implementation.  Machine ranges, physical ownership, and the equalities
   between their lengths and the current loop index stay explicit in C. *)
Definition PrefixResidualState
    (values residuals flags : list Z) : Prop :=
  Znth 0 residuals 0 = 0 /\
  Znth 0 flags 0 = 1 /\
  (forall k,
      1 <= k < Zlength residuals ->
      Znth k residuals 0 =
        Znth (k - 1) values 0 - Znth (k - 1) residuals 0) /\
  forall k,
    0 <= k < Zlength flags ->
    (Znth k flags 0 = 0 \/ Znth k flags 0 = 1) /\
    (Znth k flags 0 = 1 <->
       forall j, 0 <= j <= k -> 0 <= Znth j residuals 0).

(* [residuals] and [flags] use indices relative to the 1-based physical
   position [start].  Under the explicit C length equation, their last cell is
   physical position n+1 and hence carries the terminal zero. *)
Definition SuffixResidualState
    (values : list Z) (start : Z) (residuals flags : list Z) : Prop :=
  Znth (Zlength residuals - 1) residuals 0 = 0 /\
  Znth (Zlength flags - 1) flags 0 = 1 /\
  (forall q,
      0 <= q < Zlength residuals - 1 ->
      Znth q residuals 0 =
        Znth (start + q - 1) values 0 - Znth (q + 1) residuals 0) /\
  forall q,
    0 <= q < Zlength flags ->
    (Znth q flags 0 = 0 \/ Znth q flags 0 = 1) /\
    (Znth q flags 0 = 1 <->
       forall j, q <= j < Zlength residuals ->
         0 <= Znth j residuals 0).

Definition DirectResidualSuccess
    (pre_values okpre_values : list Z) (n : Z) : Prop :=
  Znth n okpre_values 0 = 1 /\ Znth n pre_values 0 = 0.

(* For a 1-based adjacent swap position [i], [suf_values] is the complete
   physical segment [1,n+2), so physical cell i+2 has relative index i+1. *)
Definition SwapResidualSuccess
    (values pre_values suf_values okpre_values oksuf_values : list Z)
    (i : Z) : Prop :=
  Znth (i - 1) okpre_values 0 = 1 /\
  Znth (i + 1) oksuf_values 0 = 1 /\
  let x := Znth i values 0 - Znth (i - 1) pre_values 0 in
  let y := Znth (i - 1) values 0 - x in
  0 <= x /\ 0 <= y /\ y = Znth (i + 1) suf_values 0.

Definition CheckedSwapPrefix
    (values pre_values suf_values okpre_values oksuf_values : list Z)
    (upto : Z) : Prop :=
  ~ DirectResidualSuccess pre_values okpre_values (Zlength values) /\
  forall i,
    1 <= i < upto ->
    ~ SwapResidualSuccess
        values pre_values suf_values okpre_values oksuf_values i.

Require Import Coq.micromega.Lia.

Lemma checked_swap_prefix_init :
  forall values pre_values suf_values okpre_values oksuf_values,
    ~ DirectResidualSuccess pre_values okpre_values (Zlength values) ->
    CheckedSwapPrefix
      values pre_values suf_values okpre_values oksuf_values 1.
Proof.
  intros values pre_values suf_values okpre_values oksuf_values Hdirect.
  split; [exact Hdirect |].
  intros i Hi. lia.
Qed.

Lemma checked_swap_prefix_step :
  forall values pre_values suf_values okpre_values oksuf_values upto,
    CheckedSwapPrefix
      values pre_values suf_values okpre_values oksuf_values upto ->
    ~ SwapResidualSuccess
        values pre_values suf_values okpre_values oksuf_values upto ->
    CheckedSwapPrefix
      values pre_values suf_values okpre_values oksuf_values (upto + 1).
Proof.
  intros values pre_values suf_values okpre_values oksuf_values upto
    [Hdirect Hchecked] Hcurrent.
  split; [exact Hdirect |].
  intros i Hi.
  destruct (Z_lt_ge_dec i upto) as [Hlt | Hge].
  - apply Hchecked. lia.
  - assert (i = upto) by lia. subst i. exact Hcurrent.
Qed.

Lemma prefix_residual_flag_boolean :
  forall values residuals flags k,
    PrefixResidualState values residuals flags ->
    0 <= k < Zlength flags ->
    Znth k flags 0 = 0 \/ Znth k flags 0 = 1.
Proof.
  intros values residuals flags k (_ & _ & _ & Hflags) Hk.
  exact (proj1 (Hflags k Hk)).
Qed.

Lemma suffix_residual_flag_boolean :
  forall values start residuals flags k,
    SuffixResidualState values start residuals flags ->
    0 <= k < Zlength flags ->
    Znth k flags 0 = 0 \/ Znth k flags 0 = 1.
Proof.
  intros values start residuals flags k (_ & _ & _ & Hflags) Hk.
  exact (proj1 (Hflags k Hk)).
Qed.

Require Import Coq.Relations.Relation_Operators.
Lemma prefix_residual_state_init__prefix_construction :
  forall values,
    PrefixResidualState values [0] [1].
Proof.
  intros values.
  unfold PrefixResidualState.
  split; [reflexivity |].
  split; [reflexivity |].
  split.
  - intros k Hk.
    rewrite Zlength_cons, Zlength_nil in Hk.
    lia.
  - intros k Hk.
    rewrite Zlength_cons, Zlength_nil in Hk.
    assert (k = 0) by lia.
    subst k.
    rewrite !Znth0_cons.
    split.
    + right. reflexivity.
    + split.
      * intros _. intros j Hj.
        assert (j = 0) by lia.
        subst j. rewrite Znth0_cons. lia.
      * intros _. reflexivity.
Qed.
Lemma prefix_residual_init_bound__prefix_construction :
  forall k,
    0 <= k < 1 ->
    (-1000000000) * k <= Znth k [0] 0 <= 1000000000 * k.
Proof.
  intros k Hk.
  assert (k = 0) by lia.
  subst k.
  rewrite Znth0_cons.
  lia.
Qed.
Lemma replace_Znth_app_last__prefix_construction :
  forall (l : list Z) old value,
    replace_Znth (Zlength l) value (l ++ [old]) =
    l ++ [value].
Proof.
  intros l old value.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (Zlength l - Zlength l) with 0 by lia.
  reflexivity.
Qed.
Lemma prefix_residual_extend_core__prefix_construction :
  forall values residuals flags i r f,
    1 <= i ->
    Zlength residuals = i ->
    Zlength flags = i ->
    PrefixResidualState values residuals flags ->
    r = Znth (i - 1) values 0 - Znth (i - 1) residuals 0 ->
    (f = 0 \/ f = 1) ->
    (f = 1 <->
      forall j, 0 <= j <= i -> 0 <= Znth j (residuals ++ [r]) 0) ->
    PrefixResidualState values (residuals ++ [r]) (flags ++ [f]).
Proof.
  intros values residuals flags i r f Hi Hreslen Hflagslen
    (Hres0 & Hflag0 & Hrec & Hflags) Hr Hfbool Hfiff.
  unfold PrefixResidualState.
  split.
  - rewrite app_Znth1 by lia. exact Hres0.
  - split.
    + rewrite app_Znth1 by lia. exact Hflag0.
    + split.
      * intros k Hk.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
        -- rewrite app_Znth1 by lia.
           rewrite app_Znth1 by lia.
           apply Hrec. lia.
        -- assert (k = i) by lia. subst k.
           rewrite app_Znth2 by lia.
           replace (i - Zlength residuals) with 0 by lia.
           simpl.
           rewrite app_Znth1 by lia.
           exact Hr.
      * intros k Hk.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
        -- rewrite app_Znth1 by lia.
           destruct (Hflags k ltac:(lia)) as [Hbool Holdiff].
           split; [exact Hbool |].
           split.
           ++ intros Hflag j Hj.
              rewrite app_Znth1 by lia.
              apply (proj1 Holdiff Hflag). lia.
           ++ intros Hall.
              apply (proj2 Holdiff).
              intros j Hj.
              specialize (Hall j Hj).
              rewrite app_Znth1 in Hall by lia.
              exact Hall.
        -- assert (k = i) by lia. subst k.
           rewrite app_Znth2 by lia.
           replace (i - Zlength flags) with 0 by lia.
           simpl.
           split; assumption.
Qed.
Lemma prefix_residual_extend_bound__prefix_construction :
  forall values residuals i r n,
    n = Zlength values ->
    1 <= i <= n ->
    Zlength residuals = i ->
    (forall k, 0 <= k < n ->
      1 <= Znth k values 0 <= 1000000000) ->
    (forall k, 0 <= k < i ->
      (-1000000000) * k <= Znth k residuals 0 <= 1000000000 * k) ->
    r = Znth (i - 1) values 0 - Znth (i - 1) residuals 0 ->
    forall k, 0 <= k < i + 1 ->
      (-1000000000) * k <= Znth k (residuals ++ [r]) 0 <=
        1000000000 * k.
Proof.
  intros values residuals i r n Hn Hi Hreslen Hvalues Hbound Hr k Hk.
  destruct (Z_lt_ge_dec k i) as [Hki | Hki].
  - rewrite app_Znth1 by lia.
    apply Hbound. lia.
  - assert (k = i) by lia. subst k.
    rewrite app_Znth2 by lia.
    replace (i - Zlength residuals) with 0 by lia.
    rewrite Znth0_cons.
    rewrite Hr.
    specialize (Hvalues (i - 1) ltac:(lia)).
    specialize (Hbound (i - 1) ltac:(lia)).
    split.
    + lia.
    + lia.
Qed.
Lemma prefix_residual_extend_prior_false__prefix_construction :
  forall values residuals flags i r,
    1 <= i ->
    Zlength residuals = i ->
    Zlength flags = i ->
    PrefixResidualState values residuals flags ->
    r = Znth (i - 1) values 0 - Znth (i - 1) residuals 0 ->
    Znth (i - 1) flags 0 = 0 ->
    PrefixResidualState values (residuals ++ [r]) (flags ++ [0]).
Proof.
  intros values residuals flags i r Hi Hreslen Hflagslen Hstate Hr Hfalse.
  eapply prefix_residual_extend_core__prefix_construction;
    try eassumption; try (left; reflexivity).
  split.
  - lia.
  - intros Hall.
    destruct Hstate as (_ & _ & _ & Hflags).
    destruct (Hflags (i - 1) ltac:(lia)) as (_ & Hiff).
    assert (Hone : Znth (i - 1) flags 0 = 1).
    { apply (proj2 Hiff).
      intros j Hj.
      specialize (Hall j ltac:(lia)).
      rewrite app_Znth1 in Hall by lia.
      exact Hall. }
    lia.
Qed.
Lemma prefix_residual_extend_success__prefix_construction :
  forall values residuals flags i r,
    1 <= i ->
    Zlength residuals = i ->
    Zlength flags = i ->
    PrefixResidualState values residuals flags ->
    r = Znth (i - 1) values 0 - Znth (i - 1) residuals 0 ->
    Znth (i - 1) flags 0 <> 0 ->
    0 <= r ->
    PrefixResidualState values (residuals ++ [r]) (flags ++ [1]).
Proof.
  intros values residuals flags i r Hi Hreslen Hflagslen Hstate Hr
    Hprev_nonzero Hrnonneg.
  eapply prefix_residual_extend_core__prefix_construction;
    try eassumption; try (right; reflexivity).
  split.
  - intros _. intros j Hj.
    destruct Hstate as (_ & _ & _ & Hflags).
    destruct (Z.eq_dec j i) as [Hji | Hji].
    + subst j.
      rewrite app_Znth2 by lia.
      replace (i - Zlength residuals) with 0 by lia.
      simpl. exact Hrnonneg.
    + assert (Hjold : 0 <= j <= i - 1) by lia.
      rewrite app_Znth1 by lia.
      destruct (Hflags (i - 1) ltac:(lia)) as (Hbool & Hiff).
      assert (Hone : Znth (i - 1) flags 0 = 1) by
        (destruct Hbool; [contradiction | assumption]).
      apply (proj1 Hiff Hone). exact Hjold.
  - intros _. reflexivity.
Qed.
Lemma prefix_residual_extend_current_false__prefix_construction :
  forall values residuals flags i r,
    1 <= i ->
    Zlength residuals = i ->
    Zlength flags = i ->
    PrefixResidualState values residuals flags ->
    r = Znth (i - 1) values 0 - Znth (i - 1) residuals 0 ->
    r < 0 ->
    PrefixResidualState values (residuals ++ [r]) (flags ++ [0]).
Proof.
  intros values residuals flags i r Hi Hreslen Hflagslen Hstate Hr Hrneg.
  eapply prefix_residual_extend_core__prefix_construction;
    try eassumption; try (left; reflexivity).
  split.
  - lia.
  - intros Hall.
    specialize (Hall i ltac:(lia)).
    rewrite app_Znth2 in Hall by lia.
    replace (i - Zlength residuals) with 0 in Hall by lia.
    rewrite Znth0_cons in Hall.
    lia.
Qed.
Lemma suffix_residual_state_terminal_init__suffix_setup :
  forall values,
    SuffixResidualState values (Zlength values + 1) [0] [1].
Proof.
  intros values. unfold SuffixResidualState.
  split.
  - simpl. reflexivity.
  - split.
    + simpl. reflexivity.
    + split.
      * intros q Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
      * intros q Hq. rewrite Zlength_cons, Zlength_nil in Hq.
        assert (q = 0) by lia. subst q. simpl.
        split.
        -- right. reflexivity.
        -- split.
           ++ intros _ j Hj. rewrite Zlength_cons, Zlength_nil in Hj.
              assert (j = 0) by lia. subst j.
              rewrite Znth0_cons. lia.
           ++ intros _. reflexivity.
Qed.
Lemma replace_Znth_app_last__suffix_step :
  forall (prefix : list Z) old value,
    replace_Znth (Zlength prefix) value (prefix ++ [old]) =
    prefix ++ [value].
Proof.
  intros prefix old value.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (Zlength prefix - Zlength prefix) with 0 by lia.
  reflexivity.
Qed.
Lemma suffix_residual_prepend_core__suffix_step :
  forall values start residuals flags new_residual new_flag,
    Zlength residuals = Zlength flags ->
    0 < Zlength residuals ->
    SuffixResidualState values (start + 1) residuals flags ->
    new_residual =
      Znth (start - 1) values 0 - Znth 0 residuals 0 ->
    (new_flag = 0 \/ new_flag = 1) ->
    (new_flag = 1 <->
      Znth 0 flags 0 = 1 /\ 0 <= new_residual) ->
    SuffixResidualState values start
      (new_residual :: residuals) (new_flag :: flags).
Proof.
  intros values start residuals flags new_residual new_flag
    Hlength Hpositive Hstate Hresidual Hboolean Hflag.
  destruct Hstate as (Hres_end & Hflag_end & Hrec & Hflags).
  unfold SuffixResidualState.
  rewrite !Zlength_cons.
  split.
  - rewrite Znth_cons by lia.
    replace (Z.succ (Zlength residuals) - 1 - 1)
      with (Zlength residuals - 1) by lia.
    exact Hres_end.
  - split.
    + rewrite Znth_cons by (rewrite <- Hlength; lia).
      replace (Z.succ (Zlength flags) - 1 - 1)
        with (Zlength flags - 1) by lia.
      exact Hflag_end.
    + split.
      * intros q Hq.
        destruct (Z.eq_dec q 0) as [Eq | Neq].
        -- subst q. rewrite Znth0_cons.
           rewrite Znth_cons by lia.
           replace (0 + 1 - 1) with 0 by lia.
           replace (start + 0 - 1) with (start - 1) by lia.
           exact Hresidual.
        -- assert (Hqpos : 0 < q) by lia.
           rewrite !Znth_cons by lia.
           replace (q + 1 - 1) with q by lia.
           specialize (Hrec (q - 1)).
           replace (start + 1 + (q - 1) - 1)
             with (start + q - 1) in Hrec by lia.
           replace (q - 1 + 1) with q in Hrec by lia.
           apply Hrec. lia.
      * intros q Hq.
        destruct (Z.eq_dec q 0) as [Eq | Neq].
        -- subst q. rewrite Znth0_cons. split; [exact Hboolean |].
           split.
           ++ intros Hnew j Hj.
              apply Hflag in Hnew. destruct Hnew as (Hold & Hnew_nonneg).
              destruct (Z.eq_dec j 0) as [Ej | Nej].
              ** subst j. rewrite Znth0_cons. exact Hnew_nonneg.
              ** rewrite Znth_cons by lia.
                 apply (proj1 (proj2 (Hflags 0 ltac:(lia))) Hold).
                 lia.
           ++ intros Hall. apply Hflag. split.
              ** apply (proj2 (proj2 (Hflags 0 ltac:(lia)))).
                 intros j Hj.
                 specialize (Hall (j + 1)).
                 rewrite Znth_cons in Hall by lia.
                 replace (j + 1 - 1) with j in Hall by lia.
                 apply Hall. lia.
              ** specialize (Hall 0 ltac:(lia)).
                 rewrite Znth0_cons in Hall. exact Hall.
        -- assert (Hqpos : 0 < q) by lia.
           rewrite Znth_cons by lia.
           destruct (Hflags (q - 1) ltac:(lia)) as (Hbool_old & Hiff_old).
           split; [exact Hbool_old |].
           split.
           ++ intros Hold j Hj.
              rewrite Znth_cons by lia.
              apply (proj1 Hiff_old Hold). lia.
           ++ intros Hall. apply (proj2 Hiff_old).
              intros j Hj.
              specialize (Hall (j + 1)).
              rewrite Znth_cons in Hall by lia.
              replace (j + 1 - 1) with j in Hall by lia.
              apply Hall. lia.
Qed.
Lemma suffix_residual_prepend_bound__suffix_step :
  forall n i residuals new_residual,
    Zlength residuals = n + 1 - i ->
    (-1000000000 * (n - i + 1) <= new_residual /\
      new_residual <= 1000000000 * (n - i + 1)) ->
    (forall q, 0 <= q < Zlength residuals ->
      -1000000000 * (n - i - q) <= Znth q residuals 0 /\
      Znth q residuals 0 <= 1000000000 * (n - i - q)) ->
    forall q, 0 <= q < Zlength (new_residual :: residuals) ->
      -1000000000 * (n - (i - 1) - q) <=
        Znth q (new_residual :: residuals) 0 /\
      Znth q (new_residual :: residuals) 0 <=
        1000000000 * (n - (i - 1) - q).
Proof.
  intros n i residuals new_residual Hlength Hnew Hold q Hq.
  rewrite Zlength_cons in Hq.
  destruct (Z.eq_dec q 0) as [Eq | Neq].
  - subst q. rewrite Znth0_cons. lia.
  - assert (Hqpos : 0 < q) by lia.
    rewrite Znth_cons by lia.
    specialize (Hold (q - 1)).
    replace (q - 1) with (q - 1) by lia.
    specialize (Hold ltac:(lia)).
    lia.
Qed.
Lemma residual_ok_from__final_result : Z -> list Z -> Prop.
Proof. exact (fix go (prev : Z) (xs : list Z) : Prop :=
    match xs with
    | nil => prev = 0
    | x :: tl => 0 <= x - prev /\ go (x - prev) tl
    end). Defined.
Lemma ResidualOK__final_result : list Z -> Prop.
Proof. exact (fun xs => residual_ok_from__final_result 0 xs). Defined.
Lemma Zlength_replace_Znth__final_result :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l. induction l as [|x xs IH]; intros n v; simpl; auto.
  unfold replace_Znth in *. destruct (Z.to_nat n); simpl.
  - rewrite !Zlength_cons. lia.
  - rewrite !Zlength_cons.
    specialize (IH (Z.of_nat n0) v).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IH by lia.
    rewrite IH. lia.
Qed.
Lemma residual_ok_reverse_clean_step__final_result :
  forall a b prev,
    CleanStep a b ->
    residual_ok_from__final_result prev b ->
    residual_ok_from__final_result prev a.
Proof.
  induction a as [|x xs IH]; intros b prev Hstep Hok.
  - destruct Hstep as (i & Hi & _). rewrite Zlength_nil in Hi. lia.
  - destruct Hstep as (i & Hi & Hx & Hy & Heq).
    destruct (Z.eq_dec i 0) as [Ei|Eni].
    + subst i. destruct xs as [|y ys].
      { rewrite Zlength_cons, Zlength_nil in Hi. lia. }
      assert (Eb : b = (x - 1) :: (y - 1) :: ys).
      { rewrite Heq. change ((x - 1) :: (y - 1) :: ys =
          (x - 1) :: (y - 1) :: ys). reflexivity. }
      clear Heq. subst b. simpl in Hok |- *. destruct Hok as (H1 & H2 & Htl).
      replace (y - 1 - (x - 1 - prev)) with (y - (x - prev)) in Htl by lia.
      repeat split; try lia. exact Htl.
    + assert (Hip : 0 < i) by lia.
      set (bt := replace_Znth (i - 1 + 1)
          (Znth (i - 1 + 1) xs 0 - 1)
          (replace_Znth (i - 1) (Znth (i - 1) xs 0 - 1) xs)).
      assert (Estep : CleanStep xs bt).
      { unfold CleanStep, bt. exists (i - 1).
        rewrite Zlength_cons in Hi. repeat split; try lia.
        - rewrite Znth_cons in Hx by lia.
          replace (i - 1) with (i - 1) in Hx by lia. exact Hx.
        - rewrite Znth_cons in Hy by lia.
          replace (i + 1 - 1) with i in Hy by lia.
          replace (i - 1 + 1) with i by lia. exact Hy.
      }
      assert (Eb : b = x :: bt).
      { unfold bt. rewrite Heq.
        repeat (rewrite replace_Znth_cons by lia).
        repeat (rewrite Znth_cons by lia).
        replace (i - 1 + 1) with i by lia.
        replace (i + 1 - 1) with i by lia.
        reflexivity. }
      clear Heq. subst b. simpl in Hok |- *. destruct Hok as (Hhead & Htail).
      split; [exact Hhead|]. eapply IH; eauto.
Qed.
Lemma CleanReach__final_result : list Z -> list Z -> Prop.
Proof. exact (clos_refl_trans_1n (list Z) CleanStep). Defined.
Lemma clean_reach_cons_zero__final_result :
  forall a b, CleanReach__final_result a b ->
    CleanReach__final_result (0 :: a) (0 :: b).
Proof.
  intros a b H; induction H as [a|a b c Hab Hbc IH].
  - constructor.
  - econstructor; [|exact IH].
    destruct Hab as (i & Hi & Hx & Hy & Heq).
    unfold CleanStep. exists (i + 1).
    simpl. rewrite !Zlength_cons in *. repeat split; try lia.
    + rewrite Znth_cons by lia. replace (i + 1 - 1) with i by lia. exact Hx.
    + rewrite Znth_cons by lia. replace (i + 1 + 1 - 1) with (i + 1) by lia.
      exact Hy.
    + rewrite Heq. repeat (rewrite replace_Znth_cons by lia).
      repeat (rewrite Znth_cons by lia).
      replace (i + 1 - 1) with i by lia.
      replace (i + 1 + 1 - 1) with (i + 1) by lia. reflexivity.
Qed.
Lemma residual_ok_reach_zero__final_result :
  forall len a, length a = len -> ResidualOK__final_result a ->
    exists z, Forall (fun v => v = 0) z /\ CleanReach__final_result a z.
Proof.
  induction len as [|len IHlen]; intros a Hlen Hok.
  - destruct a; [|discriminate]. exists nil. split; constructor.
  - destruct a as [|x xs]; [discriminate|].
    destruct xs as [|y ys].
    + unfold ResidualOK__final_result in Hok. simpl in Hok.
      destruct Hok as (Hx & Ex). assert (Ex0 : x = 0) by lia. subst x.
      exists (0 :: nil). split.
      * constructor; [reflexivity|constructor].
      * constructor.
    + unfold ResidualOK__final_result in Hok. simpl in Hok.
      simpl in Hlen.
      destruct Hok as (Hx & Hy & Htail).
      assert (Ex : x = Z.of_nat (Z.to_nat x)) by lia.
      remember (Z.to_nat x) as nx eqn:Enx.
      rewrite Ex in Hx, Hy, Htail |- *.
      clear x Ex Enx.
      revert y ys Hlen Hy Htail.
      induction nx as [|nx IHnx]; intros y ys Hlen Hy Htail.
      * assert (Hlen_tail : length (y :: ys) = len).
        { simpl. apply Nat.succ_inj in Hlen. exact Hlen. }
        assert (Hok_tail : ResidualOK__final_result (y :: ys)).
        { unfold ResidualOK__final_result. simpl.
          replace (y - 0) with y by lia.
          replace (y - (Z.of_nat 0 - 0)) with y in Hy by lia.
          replace (y - (Z.of_nat 0 - 0)) with y in Htail by lia.
          split; [exact Hy|exact Htail]. }
        destruct (IHlen (y :: ys) Hlen_tail Hok_tail) as (z & Hz0 & Hzreach).
        exists (0 :: z). split.
        -- constructor; auto.
        -- apply clean_reach_cons_zero__final_result. exact Hzreach.
      * assert (Hypos : Z.gt y 0) by lia.
        assert (Hheadpos : Z.gt (Z.of_nat (S nx)) 0) by lia.
        assert (Hy_dec : 0 <= (y - 1) - Z.of_nat nx) by lia.
        assert (Htail_dec :
          residual_ok_from__final_result ((y - 1) - Z.of_nat nx) ys).
        { replace ((y - 1) - Z.of_nat nx) with
            (y - Z.of_nat (S nx)) by lia. exact Htail. }
        assert (Htail_dec' :
          residual_ok_from__final_result ((y - 1) - (Z.of_nat nx - 0)) ys).
        { replace ((y - 1) - (Z.of_nat nx - 0)) with
            ((y - 1) - Z.of_nat nx) by lia. exact Htail_dec. }
        destruct (IHnx ltac:(lia) (y - 1) ys Hlen ltac:(lia) Htail_dec')
          as (z & Hz0 & Hzreach).
        exists z. split; [exact Hz0|].
        eapply rt1n_trans with (y := Z.of_nat nx :: (y - 1) :: ys).
        -- unfold CleanStep. exists 0. rewrite !Zlength_cons.
           repeat split.
           ++ pose proof (Zlength_nonneg ys). lia.
           ++ pose proof (Zlength_nonneg ys). lia.
           ++ rewrite Znth_cons by lia. replace (0 + 1 - 1) with 0 by lia.
              rewrite Znth0_cons. exact Hypos.
           ++ change (Z.of_nat nx :: (y - 1) :: ys =
                (Z.of_nat (S nx) - 1) :: (y - 1) :: ys).
              f_equal. lia.
        -- exact Hzreach.
Qed.
Lemma residual_ok_all_zero__final_result :
  forall a, Forall (fun v => v = 0) a -> ResidualOK__final_result a.
Proof.
  intros a H; induction H.
  - reflexivity.
  - subst x. simpl. split; [lia|exact IHForall].
Qed.
Lemma trace_residual_ok__final_result :
  forall st,
    st <> nil ->
    (forall q, 0 <= q < Zlength st - 1 ->
      CleanStep (Znth q st nil) (Znth (q + 1) st nil)) ->
    ResidualOK__final_result (Znth (Zlength st - 1) st nil) ->
    ResidualOK__final_result (Znth 0 st nil).
Proof.
  induction st as [|a st IH]; intros Hne Hsteps Hlast; [contradiction|].
  destruct st as [|b tl].
  - rewrite !Znth0_cons. exact Hlast.
  - assert (Hab : CleanStep a b).
    { specialize (Hsteps 0).
      rewrite Znth0_cons in Hsteps.
      rewrite Znth_cons in Hsteps by lia.
      replace (0 + 1 - 1) with 0 in Hsteps by lia.
      rewrite Znth0_cons in Hsteps.
      apply Hsteps. rewrite !Zlength_cons.
      pose proof (Zlength_nonneg tl). lia. }
    assert (Htailsteps : forall q,
      0 <= q < Zlength (b :: tl) - 1 ->
      CleanStep (Znth q (b :: tl) nil) (Znth (q + 1) (b :: tl) nil)).
    { intros q Hq. specialize (Hsteps (q + 1)).
      rewrite !Znth_cons in Hsteps by lia.
      replace (q + 1 - 1) with q in Hsteps by lia.
      replace (q + 1 + 1 - 1) with (q + 1) in Hsteps by lia.
      replace (Znth (q + 1 + 1) (a :: b :: tl) nil) with
        (Znth (q + 1) (b :: tl) nil) in Hsteps.
      2: { rewrite (@Znth_cons (list Z) nil (q + 1 + 1) a (b :: tl)) by lia.
           replace (q + 1 + 1 - 1) with (q + 1) by lia. reflexivity. }
      apply Hsteps. rewrite !Zlength_cons in *. lia. }
    assert (Hlasttail :
      ResidualOK__final_result
        (Znth (Zlength (b :: tl) - 1) (b :: tl) nil)).
    { rewrite Znth_cons in Hlast by
        (rewrite !Zlength_cons; pose proof (Zlength_nonneg tl); lia).
      replace (Zlength (a :: b :: tl) - 1 - 1) with
        (Zlength (b :: tl) - 1) in Hlast by
        (rewrite !Zlength_cons; lia).
      exact Hlast. }
    assert (Hb : ResidualOK__final_result b).
    { change (ResidualOK__final_result (Znth 0 (b :: tl) nil)).
      eapply IH; eauto. discriminate. }
    rewrite Znth0_cons.
    eapply residual_ok_reverse_clean_step__final_result; eauto.
Qed.
Lemma clean_reach_trace__final_result :
  forall a z, CleanReach__final_result a z ->
    exists st,
      st <> nil /\
      Znth 0 st nil = a /\
      Znth (Zlength st - 1) st nil = z /\
      forall q, 0 <= q < Zlength st - 1 ->
        CleanStep (Znth q st nil) (Znth (q + 1) st nil).
Proof.
  intros a z Hreach; induction Hreach as [a|a b c Hab Hbc IHreach].
  - exists (a :: nil). split; [discriminate|]. split.
    + rewrite Znth0_cons. reflexivity.
    + split.
      * rewrite Zlength_cons, Zlength_nil.
      replace (0 + 1 - 1) with 0 by lia. rewrite Znth0_cons. reflexivity.
      * intros q Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
  - destruct IHreach as (st & Hne & Hfirst & Hlast & Hsteps).
    exists (a :: st). split; [discriminate|]. split.
    + rewrite Znth0_cons. reflexivity.
    + split.
      * assert (Hlenpos : 0 < Zlength st).
      { destruct st; [contradiction|rewrite Zlength_cons; pose proof (Zlength_nonneg st); lia]. }
      rewrite Znth_cons by (rewrite Zlength_cons; lia).
      replace (Zlength (a :: st) - 1 - 1) with (Zlength st - 1) by
        (rewrite Zlength_cons; lia).
      exact Hlast.
      * intros q Hq. destruct (Z.eq_dec q 0) as [Eq|Neq].
        -- subst q. rewrite Znth0_cons.
           rewrite Znth_cons by lia. replace (0 + 1 - 1) with 0 by lia.
           rewrite Hfirst. exact Hab.
        -- assert (Hqpos : 0 < q) by lia.
           specialize (Hsteps (q - 1)).
           rewrite !Znth_cons by lia.
           replace (q - 1) with (q - 1) by lia.
           replace (q - 1 + 1) with q in Hsteps by lia.
           replace (q + 1 - 1) with q by lia.
           apply Hsteps.
           rewrite Zlength_cons in Hq. lia.
Qed.
Lemma direct_cleanable_implies_residual_ok__final_result :
  forall a,
    (exists st,
      st <> nil /\ Znth 0 st nil = a /\
      Forall (fun x => x = 0) (Znth (Zlength st - 1) st nil) /\
      forall q, 0 <= q < Zlength st - 1 ->
        CleanStep (Znth q st nil) (Znth (q + 1) st nil)) ->
    ResidualOK__final_result a.
Proof.
  intros a (st & Hne & Hfirst & Hz & Hsteps).
  rewrite <- Hfirst.
  eapply trace_residual_ok__final_result; eauto.
  apply residual_ok_all_zero__final_result. exact Hz.
Qed.
Lemma residual_ok_from_recurrence__final_result :
  forall a prev (r : Z -> Z),
    r 0 = prev ->
    (forall k, 0 <= k < Zlength a ->
      r (k + 1) = Znth k a 0 - r k /\ 0 <= r (k + 1)) ->
    r (Zlength a) = 0 ->
    residual_ok_from__final_result prev a.
Proof.
  induction a as [|x xs IH]; intros prev r Hr0 Hrec Hend.
  - rewrite Zlength_nil in Hend. rewrite <- Hr0. exact Hend.
  - assert (Hzero := Hrec 0).
    rewrite Znth0_cons in Hzero.
    specialize (Hzero ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg xs); lia)).
    destruct Hzero as (Hr1 & Hr1nonneg).
    rewrite Hr0 in Hr1.
    simpl. split.
    + rewrite <- Hr1. exact Hr1nonneg.
    + apply IH with (r := fun k => r (k + 1)).
      * exact Hr1.
      * intros k Hk. specialize (Hrec (k + 1)).
        rewrite Znth_cons in Hrec by lia.
        replace (k + 1 - 1) with k in Hrec by lia.
        specialize (Hrec ltac:(rewrite Zlength_cons; lia)).
        replace (k + 1 + 1) with ((k + 1) + 1) in Hrec by lia.
        exact Hrec.
      * rewrite Zlength_cons in Hend.
        replace (Zlength xs + 1) with (Zlength xs + 1) in Hend by lia.
        exact Hend.
Qed.
Lemma residual_ok_recurrence_facts__final_result :
  forall a prev (r : Z -> Z),
    0 <= prev ->
    r 0 = prev ->
    (forall k, 0 <= k < Zlength a ->
      r (k + 1) = Znth k a 0 - r k) ->
    residual_ok_from__final_result prev a ->
    (forall k, 0 <= k <= Zlength a -> 0 <= r k) /\
    r (Zlength a) = 0.
Proof.
  induction a as [|x xs IH]; intros prev r Hprev Hr0 Hrec Hok.
  - split.
    + intros k Hk. rewrite Zlength_nil in Hk. replace k with 0 by lia.
      rewrite Hr0. exact Hprev.
    + rewrite Zlength_nil. rewrite Hr0. exact Hok.
  - simpl in Hok. destruct Hok as (Hnext & Htail).
    assert (Hr1 : r 1 = x - prev).
    { specialize (Hrec 0).
      rewrite Znth0_cons in Hrec.
      specialize (Hrec ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg xs); lia)).
      replace (0 + 1) with 1 in Hrec by lia.
      rewrite Hr0 in Hrec. exact Hrec. }
    destruct (IH (x - prev) (fun k => r (k + 1)) Hnext Hr1)
      as (Hnonneg_tail & Hend_tail).
    + intros k Hk. specialize (Hrec (k + 1)).
      rewrite Znth_cons in Hrec by lia.
      replace (k + 1 - 1) with k in Hrec by lia.
      apply Hrec. rewrite Zlength_cons. lia.
    + exact Htail.
    + split.
      * intros k Hk. destruct (Z.eq_dec k 0) as [Ek|Enk].
        -- subst k. rewrite Hr0. exact Hprev.
        -- specialize (Hnonneg_tail (k - 1)).
           replace (k - 1 + 1) with k in Hnonneg_tail by lia.
           apply Hnonneg_tail. rewrite Zlength_cons in Hk. lia.
      * rewrite Zlength_cons.
        replace (Zlength xs + 1) with (Zlength xs + 1) by lia.
        exact Hend_tail.
Qed.
Lemma DirectCleanable__final_result : list Z -> Prop.
Proof. exact (fun a => exists st,
    st <> nil /\ Znth 0 st nil = a /\
    Forall (fun x => x = 0) (Znth (Zlength st - 1) st nil) /\
    forall q, 0 <= q < Zlength st - 1 ->
      CleanStep (Znth q st nil) (Znth (q + 1) st nil)). Defined.
Lemma direct_cleanable_residual_ok_iff__final_result :
  forall a, DirectCleanable__final_result a <-> ResidualOK__final_result a.
Proof.
  intro a. split.
  - apply direct_cleanable_implies_residual_ok__final_result.
  - intro Hok.
    destruct (residual_ok_reach_zero__final_result (length a) a eq_refl Hok)
      as (z & Hz & Hreach).
    destruct (clean_reach_trace__final_result _ _ Hreach)
      as (st & Hne & Hfirst & Hlast & Hsteps).
    exists st. repeat split; try assumption.
    rewrite Hlast. exact Hz.
Qed.
Lemma cleanable_direct_iff__final_result :
  forall values pre_values okpre_values,
    Zlength pre_values = Zlength values + 1 ->
    Zlength okpre_values = Zlength values + 1 ->
    PrefixResidualState values pre_values okpre_values ->
    (DirectCleanable__final_result values <->
      DirectResidualSuccess pre_values okpre_values (Zlength values)).
Proof.
  intros values pre_values okpre_values Hprelen Hoklen Hstate.
  destruct Hstate as (Hpre0 & Hok0 & Hrec & Hflags).
  rewrite direct_cleanable_residual_ok_iff__final_result.
  split.
  - intro Hres.
    destruct (residual_ok_recurrence_facts__final_result values 0
      (fun k => Znth k pre_values 0) ltac:(lia) Hpre0)
      as (Hnonneg & Hend).
    + intros k Hk. specialize (Hrec (k + 1)).
      replace (k + 1 - 1) with k in Hrec by lia.
      apply Hrec. rewrite Hprelen. lia.
    + exact Hres.
    + unfold DirectResidualSuccess. split.
      * destruct (Hflags (Zlength values)) as (_ & Hiff).
        -- rewrite Hoklen. pose proof (Zlength_nonneg values). lia.
        -- apply Hiff. intros j Hj. apply Hnonneg. exact Hj.
      * exact Hend.
  - intros (Hokend & Hpreend).
    apply residual_ok_from_recurrence__final_result with
      (r := fun k => Znth k pre_values 0).
    + exact Hpre0.
    + intros k Hk. split.
      * specialize (Hrec (k + 1)).
        replace (k + 1 - 1) with k in Hrec by lia.
        apply Hrec. rewrite Hprelen. lia.
      * destruct (Hflags (Zlength values)) as (_ & Hiff).
        -- rewrite Hoklen. pose proof (Zlength_nonneg values). lia.
        -- pose proof (proj1 Hiff Hokend) as Hall.
           apply Hall. lia.
    + exact Hpreend.
Qed.
Lemma residuals_from__final_result : Z -> list Z -> list Z.
Proof. exact (fix go (prev : Z) (a : list Z) : list Z :=
    prev :: match a with
            | nil => nil
            | x :: xs => go (x - prev) xs
            end). Defined.
Lemma canonical_residuals__final_result : list Z -> list Z.
Proof. exact (fun a => residuals_from__final_result 0 a). Defined.
Lemma residuals_from_zero__final_result :
  forall a prev, Znth 0 (residuals_from__final_result prev a) 0 = prev.
Proof. intros. destruct a; simpl; rewrite Znth0_cons; reflexivity. Qed.
Lemma residuals_from_recurrence__final_result :
  forall a prev k,
    0 <= k < Zlength a ->
    Znth (k + 1) (residuals_from__final_result prev a) 0 =
      Znth k a 0 - Znth k (residuals_from__final_result prev a) 0.
Proof.
  induction a as [|x xs IH]; intros prev k Hk;
    [rewrite Zlength_nil in Hk; lia|].
  destruct (Z.eq_dec k 0) as [Ek|Enk].
  - subst k. simpl. rewrite Znth0_cons.
    rewrite Znth_cons by lia. replace (0 + 1 - 1) with 0 by lia.
    rewrite residuals_from_zero__final_result. rewrite Znth0_cons. reflexivity.
  - assert (Hkpos : 0 < k) by lia.
    simpl.
    rewrite !Znth_cons by lia.
    replace (k + 1 - 1) with k by lia.
    replace (k - 1) with (k - 1) by lia.
    replace k with (k - 1 + 1) by lia.
    replace (k - 1 + 1 - 1) with (k - 1) by lia.
    apply IH. rewrite Zlength_cons in Hk. lia.
Qed.
Lemma swap1__final_result : list Z -> Z -> list Z.
Proof. exact (fun a i => replace_Znth i (Znth (i - 1) a 0)
    (replace_Znth (i - 1) (Znth i a 0) a)). Defined.
Lemma swap1_length__final_result :
  forall a i, Zlength (swap1__final_result a i) = Zlength a.
Proof.
  intros. unfold swap1__final_result. rewrite !Zlength_replace_Znth__final_result. reflexivity.
Qed.
Lemma swap1_left__final_result :
  forall a i, 1 <= i < Zlength a ->
    Znth (i - 1) (swap1__final_result a i) 0 = Znth i a 0.
Proof.
  intros a i Hi. unfold swap1__final_result.
  rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth__final_result; lia).
  rewrite Znth_replace_Znth_Same; lia.
Qed.
Lemma swap1_right__final_result :
  forall a i, 1 <= i < Zlength a ->
    Znth i (swap1__final_result a i) 0 = Znth (i - 1) a 0.
Proof.
  intros a i Hi. unfold swap1__final_result.
  rewrite Znth_replace_Znth_Same; [reflexivity|rewrite Zlength_replace_Znth__final_result; lia].
Qed.
Lemma swap1_other__final_result :
  forall a i k, 1 <= i < Zlength a -> 0 <= k < Zlength a ->
    k <> i - 1 -> k <> i ->
    Znth k (swap1__final_result a i) 0 = Znth k a 0.
Proof.
  intros a i k Hi Hk Hleft Hright. unfold swap1__final_result.
  rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth__final_result; lia).
  rewrite Znth_replace_Znth_Diff; lia.
Qed.
Lemma cleanable_cases__final_result :
  forall a,
    Cleanable a <->
      DirectCleanable__final_result a \/
      exists i, 1 <= i < Zlength a /\
        DirectCleanable__final_result (swap1__final_result a i).
Proof.
  intros a. unfold Cleanable, DirectCleanable__final_result.
  split.
  - intros (base & st & Hbase & Hne & Hfirst & Hlast & Hsteps).
    destruct Hbase as [Hbase | (j & Hj & Hbase)].
    + left. exists st. subst base. repeat split; assumption.
    + right. exists (j + 1). split; [lia|]. exists st.
      subst base. split; [exact Hne|]. split.
      * unfold swap1__final_result. replace (j + 1 - 1) with j by lia.
        exact Hfirst.
      * split; assumption.
  - intros [Hdir | (i & Hi & st & Hne & Hfirst & Hlast & Hsteps)].
    + destruct Hdir as (st & Hne & Hfirst & Hlast & Hsteps).
      exists a, st. split; [left; reflexivity|]. repeat split; assumption.
    + exists (swap1__final_result a i), st. split.
      * right. exists (i - 1). split; [lia|].
        unfold swap1__final_result. replace (i - 1 + 1) with i by lia. reflexivity.
      * repeat split; assumption.
Qed.
Lemma recurrence_unique_interval__final_result :
  forall (f g : Z -> Z) lo hi,
    f lo = g lo ->
    (forall k, lo <= k < hi -> f (k + 1) = g (k + 1) <-> f k = g k) ->
    forall k, lo <= k <= hi -> f k = g k.
Proof.
  intros f g lo hi Hlo Hstep k Hk.
  remember (Z.to_nat (k - lo)) as n eqn:En.
  assert (Ek : k = lo + Z.of_nat n) by lia.
  subst k. clear En.
  induction n as [|n IH].
  - replace (lo + Z.of_nat 0) with lo by lia. exact Hlo.
  - replace (lo + Z.of_nat (S n)) with ((lo + Z.of_nat n) + 1) by lia.
    apply (proj2 (Hstep (lo + Z.of_nat n) ltac:(lia))).
    apply IH. lia.
Qed.
Lemma recurrence_unique_interval_backward__final_result :
  forall (f g : Z -> Z) lo hi,
    f hi = g hi ->
    (forall k, lo <= k < hi -> f (k + 1) = g (k + 1) <-> f k = g k) ->
    forall k, lo <= k <= hi -> f k = g k.
Proof.
  intros f g lo hi Hhi Hstep k Hk.
  remember (Z.to_nat (hi - k)) as n eqn:En.
  assert (Ek : k + Z.of_nat n = hi) by lia.
  clear En. revert k Hk Ek.
  induction n as [|n IH]; intros k Hk Ek.
  - replace k with hi by lia. exact Hhi.
  - apply (proj1 (Hstep k ltac:(lia))).
    apply IH; lia.
Qed.
Lemma cleanable_one_swap_iff__final_result :
  forall values pre suf okpre oksuf i,
    1 <= i < Zlength values ->
    Zlength pre = Zlength values + 1 ->
    Zlength suf = Zlength values + 1 ->
    Zlength okpre = Zlength values + 1 ->
    Zlength oksuf = Zlength values + 1 ->
    PrefixResidualState values pre okpre ->
    SuffixResidualState values 1 suf oksuf ->
    (DirectCleanable__final_result (swap1__final_result values i) <->
      SwapResidualSuccess values pre suf okpre oksuf i).
Proof.
  intros values pre suf okpre oksuf i Hi Hprelen Hsuflen Hokprelen Hoksuflen
    Hprefix Hsuffix.
  destruct Hprefix as (Hpre0 & Hokpre0 & Hprerec & Hpreflags).
  destruct Hsuffix as (Hsufend & Hoksufend & Hsufrec & Hsuffixflags).
  assert (Hsufterminal : Znth (Zlength values) suf 0 = 0).
  { replace (Zlength values) with (Zlength suf - 1) by lia. exact Hsufend. }
  rewrite direct_cleanable_residual_ok_iff__final_result.
  set (sw := swap1__final_result values i).
  set (r := fun k => Znth k (canonical_residuals__final_result sw) 0).
  assert (Hr0 : r 0 = 0).
  { unfold r, canonical_residuals__final_result.
    apply residuals_from_zero__final_result. }
  assert (Hrrec : forall k, 0 <= k < Zlength values ->
      r (k + 1) = Znth k sw 0 - r k).
  { intros k Hk. unfold r. apply residuals_from_recurrence__final_result.
    unfold sw. rewrite swap1_length__final_result. exact Hk. }
  assert (Hprefixeq : forall k, 0 <= k <= i - 1 -> r k = Znth k pre 0).
  { apply recurrence_unique_interval__final_result with (lo := 0) (hi := i - 1).
    - rewrite Hr0, Hpre0. reflexivity.
    - intros k Hk. split; intro Heq.
      + rewrite Hrrec in Heq by lia.
        specialize (Hprerec (k + 1)).
        replace (k + 1 - 1) with k in Hprerec by lia.
        rewrite Hprerec in Heq by (rewrite Hprelen; lia).
        assert (Hsw : Znth k sw 0 = Znth k values 0).
        { unfold sw. apply swap1_other__final_result; try lia. }
        rewrite Hsw in Heq. lia.
      + rewrite Hrrec by lia.
        specialize (Hprerec (k + 1)).
        replace (k + 1 - 1) with k in Hprerec by lia.
        rewrite Hprerec by (rewrite Hprelen; lia).
        assert (Hsw : Znth k sw 0 = Znth k values 0).
        { unfold sw. apply swap1_other__final_result; try lia. }
        rewrite Hsw. lia. }
  assert (Hsuf_forward : forall k, i + 1 <= k < Zlength values ->
      Znth (k + 1) suf 0 = Znth k values 0 - Znth k suf 0).
  { intros k Hk. specialize (Hsufrec k).
    replace (1 + k - 1) with k in Hsufrec by lia.
    specialize (Hsufrec ltac:(rewrite Hsuflen; lia)). lia. }
  assert (Hri : r i = Znth i values 0 - Znth (i - 1) pre 0).
  { specialize (Hrrec (i - 1) ltac:(lia)) as H.
    replace (i - 1 + 1) with i in H by lia.
    unfold sw in H. rewrite swap1_left__final_result in H by exact Hi.
    rewrite (Hprefixeq (i - 1) ltac:(lia)) in H. exact H. }
  assert (Hri1 : r (i + 1) = Znth (i - 1) values 0 - r i).
  { specialize (Hrrec i ltac:(lia)) as H.
    unfold sw in H. rewrite swap1_right__final_result in H by exact Hi. exact H. }
  assert (Hsame_step : forall k, i + 1 <= k < Zlength values ->
      (r (k + 1) = Znth (k + 1) suf 0 <-> r k = Znth k suf 0)).
  { intros k Hk. rewrite Hrrec by lia. rewrite Hsuf_forward by lia.
    assert (Hsw : Znth k sw 0 = Znth k values 0).
    { unfold sw. apply swap1_other__final_result; try lia. }
    rewrite Hsw. lia. }
  split.
  - intro Hres.
    destruct (residual_ok_recurrence_facts__final_result sw 0 r
      ltac:(lia) Hr0) as (Hrnonneg & Hrend).
    + intros k Hk. apply Hrrec. unfold sw in Hk.
      rewrite swap1_length__final_result in Hk. exact Hk.
    + exact Hres.
    + assert (Hsufeq : forall k, i + 1 <= k <= Zlength values ->
          r k = Znth k suf 0).
      { apply recurrence_unique_interval_backward__final_result with
          (lo := i + 1) (hi := Zlength values).
        - unfold sw in Hrend. rewrite swap1_length__final_result in Hrend.
          rewrite Hrend, Hsufterminal. reflexivity.
        - exact Hsame_step. }
      unfold SwapResidualSuccess. cbn. repeat split.
      * destruct (Hpreflags (i - 1)) as (_ & Hiff); [rewrite Hokprelen; lia|].
        apply Hiff. intros j Hj. rewrite <- Hprefixeq by lia.
        apply Hrnonneg. unfold sw. rewrite swap1_length__final_result. lia.
      * destruct (Hsuffixflags (i + 1)) as (_ & Hiff); [rewrite Hoksuflen; lia|].
        apply Hiff. intros j Hj. rewrite <- Hsufeq by lia.
        apply Hrnonneg. unfold sw. rewrite swap1_length__final_result. lia.
      * rewrite <- Hri. apply Hrnonneg. unfold sw. rewrite swap1_length__final_result. lia.
      * rewrite <- Hri. rewrite <- Hri1.
        apply Hrnonneg. unfold sw. rewrite swap1_length__final_result. lia.
      * rewrite <- Hsufeq by lia. rewrite Hri1, Hri. reflexivity.
  - unfold SwapResidualSuccess. cbn.
    intros (Hokpre & Hoksuf & Hxnonneg & Hynonneg & Hy).
    assert (Hsufeq : forall k, i + 1 <= k <= Zlength values ->
        r k = Znth k suf 0).
    { apply recurrence_unique_interval__final_result with
        (lo := i + 1) (hi := Zlength values).
      - rewrite Hri1, Hri. exact Hy.
      - exact Hsame_step. }
    apply residual_ok_from_recurrence__final_result with (r := r).
    + exact Hr0.
    + intros k Hk.
      assert (Hkvalues : 0 <= k < Zlength values).
      { unfold sw in Hk. rewrite swap1_length__final_result in Hk. exact Hk. }
      split.
      * apply Hrrec. exact Hkvalues.
      * destruct (Z_le_gt_dec (k + 1) (i - 1)) as [Hbefore|Hafter].
        -- rewrite Hprefixeq by lia.
           destruct (Hpreflags (i - 1)) as (_ & Hiff); [rewrite Hokprelen; lia|].
           pose proof (proj1 Hiff Hokpre) as Hall. apply Hall. lia.
        -- destruct (Z.eq_dec (k + 1) i) as [Eki|Eki].
           ++ rewrite Eki, Hri. exact Hxnonneg.
           ++ assert (Hlater : i + 1 <= k + 1) by lia.
              rewrite (Hsufeq (k + 1) ltac:(lia)).
              destruct (Hsuffixflags (i + 1)) as (_ & Hiff);
                [rewrite Hoksuflen; lia|].
              pose proof (proj1 Hiff Hoksuf) as Hall. apply Hall.
              rewrite Hsuflen. lia.
    + unfold sw. rewrite swap1_length__final_result.
      rewrite (Hsufeq (Zlength values) ltac:(lia)). exact Hsufterminal.
Qed.
Lemma cleanable_residual_characterization__final_result :
  forall values pre suf okpre oksuf,
    Zlength pre = Zlength values + 1 ->
    Zlength suf = Zlength values + 1 ->
    Zlength okpre = Zlength values + 1 ->
    Zlength oksuf = Zlength values + 1 ->
    PrefixResidualState values pre okpre ->
    SuffixResidualState values 1 suf oksuf ->
    (Cleanable values <->
      DirectResidualSuccess pre okpre (Zlength values) \/
      exists i, 1 <= i < Zlength values /\
        SwapResidualSuccess values pre suf okpre oksuf i).
Proof.
  intros values pre suf okpre oksuf Hprelen Hsuflen Hokprelen Hoksuflen
    Hprefix Hsuffix.
  rewrite cleanable_cases__final_result.
  rewrite (cleanable_direct_iff__final_result values pre okpre
    Hprelen Hokprelen Hprefix).
  split.
  - intros [Hdirect | (i & Hi & Hswap)].
    + left. exact Hdirect.
    + right. exists i. split; [exact Hi|].
      apply (proj1 (cleanable_one_swap_iff__final_result values pre suf okpre oksuf i
        Hi Hprelen Hsuflen Hokprelen Hoksuflen Hprefix Hsuffix)). exact Hswap.
  - intros [Hdirect | (i & Hi & Hswap)].
    + left. exact Hdirect.
    + right. exists i. split; [exact Hi|].
      apply (proj2 (cleanable_one_swap_iff__final_result values pre suf okpre oksuf i
        Hi Hprelen Hsuflen Hokprelen Hoksuflen Hprefix Hsuffix)). exact Hswap.
Qed.
