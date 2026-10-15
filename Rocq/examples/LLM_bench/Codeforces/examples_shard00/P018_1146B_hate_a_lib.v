Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Local Open Scope Z_scope.

Definition GeneratesHatedAString (source given : list Z) : Prop :=
  given = source ++ filter (fun c => negb (Z.eqb c 97)) source.

Definition Pre (given : list Z) : Prop :=
  1 <= Zlength given <= 100000 /\
  Forall (fun c => 97 <= c <= 122) given.

Definition Spec (given : list Z) (out : option (list Z)) : Prop :=
  (exists source, out = Some source /\ GeneratesHatedAString source given) \/
  (out = None /\ forall source, ~ GeneratesHatedAString source given).

Definition FilteredPrefix
    (given : list Z) (i : Z) (filtered : list Z) : Prop :=
  filtered = filter (fun c => negb (Z.eqb c 97)) (sublist 0 i given).

Definition NoAInterval (given : list Z) (lo hi : Z) : Prop :=
  forall j, lo <= j < hi -> Znth j given 0 <> 97.

Definition MatchedSuffixPrefix
    (filtered given : list Z) (prefix matched : Z) : Prop :=
  forall j,
    0 <= j < matched ->
    Znth j filtered 0 = Znth (prefix + j) given 0.

Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Lemma filtered_prefix_step_non_a__filter_update :
  forall given i filtered,
    0 <= i < Zlength given ->
    Znth i given 0 <> 97 ->
    FilteredPrefix given i filtered ->
    FilteredPrefix given (i + 1) (filtered ++ (Znth i given 0 :: nil)).
Proof.
  intros given i filtered Hi Hneq Hprefix.
  unfold FilteredPrefix in *.
  rewrite (sublist_split 0 (i + 1) i given) by lia.
  rewrite (@sublist_single Z 0 i given) by lia.
  rewrite filter_app.
  simpl.
  assert (Heqb : Z.eqb (Znth i given 0) 97 = false).
  { apply Z.eqb_neq. exact Hneq. }
  rewrite Heqb.
  simpl.
  rewrite Hprefix.
  reflexivity.
Qed.
Lemma filtered_prefix_step_a__filter_update :
  forall given i filtered,
    0 <= i < Zlength given ->
    Znth i given 0 = 97 ->
    FilteredPrefix given i filtered ->
    FilteredPrefix given (i + 1) filtered.
Proof.
  intros given i filtered Hi Heq Hprefix.
  unfold FilteredPrefix in *.
  rewrite (sublist_split 0 (i + 1) i given) by lia.
  rewrite (@sublist_single Z 0 i given) by lia.
  rewrite filter_app.
  simpl.
  assert (Heqb : Z.eqb (Znth i given 0) 97 = true).
  { apply Z.eqb_eq. exact Heq. }
  rewrite Heqb.
  simpl.
  rewrite app_nil_r.
  exact Hprefix.
Qed.
Lemma nonnegative_land_one_zero_div2__parity_setup :
  forall k,
    0 <= k ->
    Z.land k 1 = 0 ->
    0 <= Z.quot k 2 /\
    k = 2 * Z.quot k 2 /\
    Z.quot k 2 <= k.
Proof.
  intros k Hnonneg Hland.
  assert (Hquot_div : Z.quot k 2 = k / 2).
  {
    apply Z.quot_div_nonneg; lia.
  }
  assert (Hquot_nonneg : 0 <= k / 2).
  {
    apply Z.div_pos; lia.
  }
  assert (Hmod : k mod 2 = 0).
  {
    replace 1 with (Z.ones 1) in Hland by reflexivity.
    rewrite Z.land_ones in Hland by lia.
    simpl in Hland.
    exact Hland.
  }
  assert (Hexact : k = 2 * (k / 2)).
  {
    apply (proj2 (Z.div_exact k 2 ltac:(lia))).
    exact Hmod.
  }
  repeat split; rewrite Hquot_div; lia.
Qed.
Lemma generates_filter_twice__result_spec :
  forall source given,
    GeneratesHatedAString source given ->
    filter (fun c => negb (Z.eqb c 97)) given =
      filter (fun c => negb (Z.eqb c 97)) source ++
      filter (fun c => negb (Z.eqb c 97)) source /\
    Zlength (filter (fun c => negb (Z.eqb c 97)) given) =
      2 * Zlength (filter (fun c => negb (Z.eqb c 97)) source).
Proof.
  intros source given Hgen.
  unfold GeneratesHatedAString in Hgen.
  subst given.
  rewrite List.filter_app.
  assert (Hid :
      filter (fun c => negb (Z.eqb c 97))
        (filter (fun c => negb (Z.eqb c 97)) source) =
      filter (fun c => negb (Z.eqb c 97)) source).
  { apply List.forallb_filter_id.
    apply List.forallb_filter. }
  rewrite Hid.
  split; [reflexivity |].
  rewrite Zlength_app.
  lia.
Qed.
Lemma filter_contains_no_a__result_spec :
  forall l j,
    0 <= j < Zlength (filter (fun c => negb (Z.eqb c 97)) l) ->
    Znth j (filter (fun c => negb (Z.eqb c 97)) l) 0 <> 97.
Proof.
  intros l j Hj Heq.
  assert (Hin : List.In (Znth j (filter (fun c => negb (Z.eqb c 97)) l) 0)
                         (filter (fun c => negb (Z.eqb c 97)) l)).
  { apply List.nth_In.
    unfold Znth.
    rewrite Zlength_correct in Hj.
    lia. }
  apply List.filter_In in Hin as [_ Hkeep].
  rewrite Heq in Hkeep.
  vm_compute in Hkeep.
  discriminate.
Qed.
Lemma generates_prefix_suffix_shape__result_spec :
  forall source given,
    GeneratesHatedAString source given ->
    let fs := filter (fun c => negb (Z.eqb c 97)) source in
    Zlength given = Zlength source + Zlength fs /\
    (forall j, 0 <= j < Zlength fs ->
       Znth (Zlength source + j) given 0 = Znth j fs 0) /\
    (forall j, 0 <= j < Zlength fs ->
       Znth j (filter (fun c => negb (Z.eqb c 97)) given) 0 =
       Znth j fs 0).
Proof.
  intros source given Hgen fs.
  unfold GeneratesHatedAString in Hgen.
  subst given.
  split.
  - rewrite Zlength_app. reflexivity.
  - split; intros j Hj.
    + rewrite app_Znth2 by lia.
      replace (Zlength source + j - Zlength source) with j by lia.
      reflexivity.
    + rewrite List.filter_app.
      rewrite app_Znth1 by exact Hj.
      reflexivity.
Qed.
Lemma filter_no_a_interval__result_spec :
  forall given lo hi,
    0 <= lo <= hi ->
    hi <= Zlength given ->
    NoAInterval given lo hi ->
    filter (fun c => negb (Z.eqb c 97)) (sublist lo hi given) =
    sublist lo hi given.
Proof.
  intros given lo hi Hbounds Hhi Hno.
  apply List.forallb_filter_id.
  apply List.forallb_forall.
  intros x Hin.
  destruct (List.In_nth _ _ 0 Hin) as [m [Hm Hnth]].
  assert (Hidx : 0 <= Z.of_nat m < hi - lo).
  { assert (Hlen : Zlength (sublist lo hi given) = hi - lo).
    { apply Zlength_sublist. lia. }
    rewrite Zlength_correct in Hlen.
    lia. }
  assert (Hznth : Znth (Z.of_nat m) (sublist lo hi given) 0 = x).
  { unfold Znth. rewrite Nat2Z.id. exact Hnth. }
  apply negb_true_iff.
  apply Z.eqb_neq.
  intro Hx.
  pose proof (Hno (lo + Z.of_nat m) ltac:(lia)) as Hneq.
  apply Hneq.
  rewrite <- Hx, <- Hznth.
  rewrite Znth_sublist by lia.
  f_equal.
  lia.
Qed.
Lemma matched_result_shape__result_spec :
  forall given n prefix suffix filtered,
    n = Zlength given ->
    0 <= prefix <= n ->
    0 <= suffix ->
    prefix = n - suffix ->
    Zlength filtered = 2 * suffix ->
    FilteredPrefix given n filtered ->
    NoAInterval given prefix n ->
    MatchedSuffixPrefix filtered given prefix suffix ->
    given = sublist 0 prefix given ++
            filter (fun c => negb (Z.eqb c 97)) (sublist 0 prefix given).
Proof.
  intros given n prefix suffix filtered Hn Hprefix Hsuffix Hprefixeq
         Hflen Hfiltered Hno Hmatched.
  set (result := sublist 0 prefix given).
  set (tail := sublist prefix n given).
  assert (Hsplit : given = result ++ tail).
  { unfold result, tail.
    pose proof (sublist_split 0 n prefix given ltac:(lia) ltac:(lia)) as Hsplit0.
    rewrite (sublist_self given n Hn) in Hsplit0.
    exact Hsplit0. }
  assert (Htail_len : Zlength tail = suffix).
  { unfold tail. rewrite Zlength_sublist by lia. lia. }
  assert (Htail_filter :
      filter (fun c => negb (Z.eqb c 97)) tail = tail).
  { unfold tail.
    apply filter_no_a_interval__result_spec; try lia.
    exact Hno. }
  assert (Hfiltered_eq :
      filtered = filter (fun c => negb (Z.eqb c 97)) given).
  { unfold FilteredPrefix in Hfiltered.
    rewrite (sublist_self given n Hn) in Hfiltered.
    exact Hfiltered. }
  assert (Hdecomp :
      filtered =
        filter (fun c => negb (Z.eqb c 97)) result ++ tail).
  { rewrite Hfiltered_eq, Hsplit, List.filter_app, Htail_filter.
    reflexivity. }
  assert (Hresult_filter_len :
      Zlength (filter (fun c => negb (Z.eqb c 97)) result) = suffix).
  { rewrite Hdecomp, Zlength_app, Htail_len in Hflen.
    lia. }
  assert (Hresult_filter :
      filter (fun c => negb (Z.eqb c 97)) result = tail).
  { apply (proj2 (list_eq_ext _ _ 0)).
    split; [lia |].
    intros j Hj.
    unfold MatchedSuffixPrefix in Hmatched.
    specialize (Hmatched j ltac:(lia)).
    rewrite Hdecomp in Hmatched.
    rewrite app_Znth1 in Hmatched by lia.
    unfold tail.
    rewrite Znth_sublist by lia.
    replace (j + prefix) with (prefix + j) by lia.
    exact Hmatched. }
  rewrite Hsplit, Hresult_filter.
  reflexivity.
Qed.
Lemma even_land_one__result_spec :
  forall z, Z.land (2 * z) 1 = 0.
Proof.
  intros z.
  change (Z.land (2 * z) (Z.ones 1) = 0).
  rewrite Z.land_ones by lia.
  change ((2 * z) mod 2 = 0).
  rewrite Z.mul_comm.
  apply Z.mod_mul; lia.
Qed.
Lemma Zlength_replace_Znth__result_spec :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros.
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
Lemma written_prefix__result_spec :
  forall given result prefix,
    0 <= prefix <= Zlength given ->
    prefix = Zlength result ->
    given = result ++ filter (fun c => negb (Z.eqb c 97)) result ->
    sublist 0 (Zlength result + 1)
      (replace_Znth prefix 0 (given ++ (0 :: nil))) =
    result ++ (0 :: nil).
Proof.
  intros given result prefix Hprefix Hprefixlen Hgiven.
  apply (proj2 (list_eq_ext _ _ 0)).
  assert (Hreplen :
      Zlength (replace_Znth prefix 0 (given ++ (0 :: nil))) =
      Zlength given + 1).
  { rewrite Zlength_replace_Znth__result_spec, Zlength_app, Zlength_cons, Zlength_nil.
    lia. }
  split.
  - rewrite Zlength_sublist by lia.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - intros j Hj.
    assert (Hsub_len :
      Zlength
        (sublist 0 (Zlength result + 1)
          (replace_Znth prefix 0 (given ++ (0 :: nil)))) =
      Zlength result + 1).
    { rewrite Zlength_sublist by lia. lia. }
    rewrite Hsub_len in Hj.
    rewrite (Znth_sublist0 0 j (Zlength result + 1)
      (replace_Znth prefix 0 (given ++ (0 :: nil)))) by lia.
    destruct (Z.lt_ge_cases j prefix) as [Hlt | Hge].
    + rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_app, ?Zlength_cons,
                                               ?Zlength_nil; lia).
      rewrite app_Znth1 by lia.
      rewrite Hgiven.
      rewrite app_Znth1 by lia.
      rewrite app_Znth1 by lia.
      reflexivity.
    + assert (j = prefix) by lia. subst j.
      rewrite Znth_replace_Znth_Same by (rewrite Zlength_app, Zlength_cons,
                                               Zlength_nil; lia).
      rewrite Hprefixlen.
      rewrite app_Znth2 by lia.
      replace (Zlength result - Zlength result) with 0 by lia.
      reflexivity.
Qed.
