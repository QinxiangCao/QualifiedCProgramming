Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib Array2Lib.
Local Open Scope Z_scope.
Import naive_C_Rules.
Local Open Scope sac.

#[local] Instance finite_index_pair (n : Z) :
    Finite (fun p : Z * Z => 0 <= fst p < n /\ 0 <= snd p < n) :=
  Finite_prod (fun i : Z => 0 <= i < n) (fun j : Z => 0 <= j < n).

Definition Inversions (a : list Z) (x count : Z) : Prop :=
  count = #(fun p : Z * Z =>
    (0 <= fst p < Zlength a /\ 0 <= snd p < Zlength a) /\
    fst p < snd p /\
    Z.lxor (Znth (fst p) a 0) x > Z.lxor (Znth (snd p) a 0) x).

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 300000 /\
  Forall (fun x => 0 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z * Z) : Prop :=
  min_value_of_subset
    (fun left right : Z * Z =>
      fst left < fst right \/
      fst left = fst right /\ snd left <= snd right)
    (fun candidate : Z * Z =>
      0 <= snd candidate /\ Inversions a (snd candidate) (fst candidate))
    (fun candidate => candidate) out.

Definition BitAt (value bit : Z) : Z :=
  Z.land (Z.shiftr value bit) 1.

Definition SameHigherBits
    (segment : list Z) (upper bit i j : Z) : Prop :=
  forall k,
    bit < k <= upper ->
    BitAt (Znth i segment 0) k = BitAt (Znth j segment 0) k.

Definition BitContribution
    (segment : list Z) (upper bit choice count : Z) : Prop :=
  count = #(fun p : Z * Z =>
    (0 <= fst p < Zlength segment /\ 0 <= snd p < Zlength segment) /\
    fst p < snd p /\
    SameHigherBits segment upper bit (fst p) (snd p) /\
    ((choice = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                    BitAt (Znth (snd p) segment 0) bit = 0) \/
     (choice = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                    BitAt (Znth (snd p) segment 0) bit = 1))).

Definition CostAt (costs : list (list Z)) (bit choice : Z) : Z :=
  Znth choice (Znth bit costs nil) 0.

Definition CostBound (costs : list (list Z)) (limit : Z) : Prop :=
  0 <= limit /\
  Zlength costs = 30 /\
  forall bit choice,
    0 <= bit < 30 -> 0 <= choice < 2 ->
    0 <= CostAt costs bit choice <= limit.

Definition CostTable (input : list Z) (costs : list (list Z)) : Prop :=
  Zlength costs = 30 /\
  (forall bit, 0 <= bit < 30 -> Zlength (Znth bit costs nil) = 2) /\
  (forall bit choice,
    0 <= bit < 30 -> 0 <= choice < 2 ->
    BitContribution input 29 bit choice (CostAt costs bit choice)).

Definition SolveEffect
    (before after : list Z) (cost_before cost_after : list (list Z))
    (l r bit : Z) : Prop :=
  Zlength after = Zlength before /\
  sublist 0 l after = sublist 0 l before /\
  sublist r (Zlength before) after = sublist r (Zlength before) before /\
  Permutation (sublist l r before) (sublist l r after) /\
  Zlength cost_before = 30 /\ Zlength cost_after = 30 /\
  (forall b, 0 <= b < 30 ->
    Zlength (Znth b cost_before nil) = 2 /\
    Zlength (Znth b cost_after nil) = 2) /\
  (forall b choice,
    0 <= b < 30 -> 0 <= choice < 2 ->
    ((0 <= b <= bit /\
      exists delta,
        BitContribution (sublist l r before) bit b choice delta /\
        CostAt cost_after b choice = CostAt cost_before b choice + delta) \/
     (~ (0 <= b <= bit) /\
      CostAt cost_after b choice = CostAt cost_before b choice))) /\
  ((l = 0 /\ r = Zlength before /\ bit = 29 /\
    (forall b choice,
      0 <= b < 30 -> 0 <= choice < 2 -> CostAt cost_before b choice = 0)) ->
    CostTable before cost_after).

Definition SolveCountPrefix
    (before : list Z) (entry_costs current_costs : list (list Z))
    (l i bit zeros ones : Z) : Prop :=
  zeros = #(fun k : Z =>
    l <= k < i /\ BitAt (Znth k before 0) bit = 0) /\
  ones = #(fun k : Z =>
    l <= k < i /\ BitAt (Znth k before 0) bit = 1) /\
  Zlength entry_costs = 30 /\ Zlength current_costs = 30 /\
  (forall b, 0 <= b < 30 ->
    Zlength (Znth b entry_costs nil) = 2 /\
    Zlength (Znth b current_costs nil) = 2) /\
  (forall b choice,
    0 <= b < 30 -> 0 <= choice < 2 ->
    ((b = bit /\
      exists delta,
        BitContribution (sublist l i before) bit bit choice delta /\
        CostAt current_costs b choice = CostAt entry_costs b choice + delta) \/
     (b <> bit /\
      CostAt current_costs b choice = CostAt entry_costs b choice))).

Definition BitIs (bit choice value : Z) : bool :=
  Z.eqb (BitAt value bit) choice.

Definition InitializedSlice
    (cells : list (option Z)) (lo hi : Z) (values : list Z) : Prop :=
  sublist lo hi cells = map (@Some Z) values.

Definition StablePartitionPrefix
    (before : list Z) (scratch : list (option Z))
    (l r bit source_done write_end phase : Z) : Prop :=
  (phase = 0 /\
   InitializedSlice scratch l write_end
     (filter (BitIs bit 0) (sublist l source_done before))) \/
  (phase = 1 /\
   InitializedSlice scratch l write_end
     (filter (BitIs bit 0) (sublist l r before) ++
      filter (BitIs bit 1) (sublist l source_done before))).

Definition PartitionCopyBack
    (before current partitioned : list Z) (l r copied : Z) : Prop :=
  Zlength current = Zlength before /\
  Zlength partitioned = r - l /\
  sublist 0 l current = sublist 0 l before /\
  sublist l copied current = sublist 0 (copied - l) partitioned /\
  sublist copied (Zlength before) current =
    sublist copied (Zlength before) before /\
  Permutation (sublist l r before) partitioned.

Definition InputCopyPrefix
    (input : list Z) (working_cells : list (option Z)) (copied : Z) : Prop :=
  InitializedSlice working_cells 0 copied (sublist 0 copied input).

Definition ZeroCostPrefix
    (cost_cells : list (list (option Z))) (next_row : Z) : Prop :=
  Zlength cost_cells = 30 /\
  (forall row, 0 <= row < 30 -> Zlength (Znth row cost_cells nil) = 2) /\
  (forall row choice,
    0 <= row < next_row -> 0 <= choice < 2 ->
    Znth choice (Znth row cost_cells nil) None = Some 0).

Definition CostArrayMixed : Z -> Z -> Z -> list (list (option Z)) -> Assertion :=
  Int64Array2.mixed_full.

Definition XorChoicePrefix
    (input : list Z) (costs : list (list Z))
    (next_bit inv x : Z) : Prop :=
  CostTable input costs /\
  inv = SumLib.Sum.sum (fun bit : Z => 0 <= bit < next_bit)
    (fun bit => Z.min (CostAt costs bit 0) (CostAt costs bit 1)) /\
  x = SumLib.Sum.sum (fun bit : Z => 0 <= bit < next_bit /\
                    CostAt costs bit 1 < CostAt costs bit 0)
    (fun bit => 2 ^ bit).

Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Ring.
Lemma Znth_default_irrelevant__solve_counting :
  forall (A : Type) (values : list A) i (d1 d2 : A),
    0 <= i < Zlength values ->
    Znth i values d1 = Znth i values d2.
Proof.
  intros A values i d1 d2 Hi.
  apply Znth_indep.
  exact Hi.
Qed.
Lemma set_card_empty__solve_counting :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma bit_contribution_empty__solve_counting :
  forall segment lo bit,
    BitContribution (sublist lo lo segment) bit bit 0 0 /\
    BitContribution (sublist lo lo segment) bit bit 1 0.
Proof.
  intros segment lo bit.
  unfold BitContribution.
  rewrite Zsublist_nil by lia.
  simpl Zlength.
  split; symmetry; apply set_card_empty__solve_counting; intros [x y] Hpair;
    cbn [fst snd] in Hpair;
    destruct Hpair as [[Hx _] _]; destruct Hx as [Hx0 Hxlt];
    change (x < 0) in Hxlt; lia.
Qed.
Lemma solve_count_prefix_empty__solve_counting :
  forall before costs l bit,
    Zlength costs = 30 ->
    (forall b, 0 <= b < 30 -> Zlength (Znth b costs nil) = 2) ->
    SolveCountPrefix before costs costs l l bit 0 0.
Proof.
  intros before costs l bit Hlen Hrows.
  unfold SolveCountPrefix.
  split; [| split; [| split; [| split; [| split]]]].
  - symmetry. apply set_card_empty__solve_counting. intros k [Hk _]. lia.
  - symmetry. apply set_card_empty__solve_counting. intros k [Hk _]. lia.
  - exact Hlen.
  - exact Hlen.
  - intros b Hb. split; apply Hrows; exact Hb.
  - intros b choice Hb Hchoice.
    destruct (Z.eq_dec b bit) as [-> | Hne].
    + left. split; [reflexivity |]. exists 0. split.
      * assert (choice = 0 \/ choice = 1) by lia.
        destruct H as [-> | ->];
          apply bit_contribution_empty__solve_counting.
      * lia.
    + right. split; [exact Hne | reflexivity].
Qed.
Lemma cost_bound_monotone__solve_counting :
  forall costs old_limit new_limit,
    CostBound costs old_limit -> old_limit <= new_limit ->
    CostBound costs new_limit.
Proof.
  intros costs old_limit new_limit Hbound Hle.
  unfold CostBound in *.
  destruct Hbound as [Hold_nonneg [Hlen Hcells]].
  split; [lia | split; [exact Hlen |]].
  intros bit choice Hbit Hchoice.
  specialize (Hcells bit choice Hbit Hchoice).
  lia.
Qed.
Lemma store_array_rec_split_to_rec__solve_counting :
  forall (A : Type) (storeA : addr -> Z -> A -> Assertion)
         x lo mid hi (values : list A),
    lo <= mid <= hi ->
    store_array_rec storeA x lo hi values |--
      store_array_rec storeA x lo mid
        (sublist 0 (mid - lo) values) **
      store_array_rec storeA x mid hi
        (sublist (mid - lo) (hi - lo) values).
Proof.
  intros A storeA x lo mid hi values Hbounds.
  generalize dependent lo. revert mid hi.
  induction values as [|a values IH]; intros; simpl store_array_rec.
  - do 2 rewrite Zsublist_of_nil.
    simpl store_array_rec. LLM_pre_process ltac:(lia).
  - prop_apply (store_array_rec_length A storeA x lo hi (a :: values)).
    Intros_p Hlen.
    destruct (Z_lt_ge_dec mid (lo + 1)).
    + assert (mid = lo) by lia; subst mid.
      rewrite Zsublist_nil by lia.
      replace (lo - lo) with 0 by lia.
      rewrite sublist_cons1; try lia.
      simpl store_array_rec.
      rewrite sublist_self by
        (rewrite Zlength_correct; simpl in Hlen; lia).
      LLM_pre_process ltac:(lia).
      simpl in Hlen; lia.
    + rewrite sublist_cons1 by lia.
      rewrite sublist_cons2; try lia.
      2:{ rewrite Zlength_correct, Hlen. lia. }
      replace (mid - lo - 1) with (mid - (lo + 1)) by lia.
      replace (hi - lo - 1) with (hi - (lo + 1)) by lia.
      cbn [store_array_rec].
      sep_apply_l_atomic (IH mid hi (lo + 1) ltac:(lia)).
      simpl store_array_rec.
      LLM_pre_process ltac:(lia).
Qed.
Lemma int64array2_rec_shift__solve_counting :
  forall x m shift lo hi rows,
    store_array_rec (Int64Array2.row_store m) x lo hi rows |--
    store_array_rec (Int64Array2.row_store m)
      (x + shift * (m * sizeof(INT64)))
      (lo - shift) (hi - shift) rows.
Proof.
  intros x m shift lo hi rows.
  generalize dependent lo. revert hi.
  induction rows as [|row rows IH]; intros; simpl store_array_rec.
  - LLM_pre_process ltac:(lia).
  - unfold Int64Array2.row_store, Int64Array2.row_addr.
    rewrite sizeof_int64 in *.
    replace (x + shift * (m * 8) + (lo - shift) * m * 8) with
      (x + lo * m * 8) by ring.
    cancel (Int64Array2.ElemArray.full (x + lo * m * 8) m row).
    sep_apply_l_atomic (IH hi (lo + 1)).
    replace (lo + 1 - shift) with (lo - shift + 1) by lia.
    LLM_pre_process ltac:(lia).
Qed.
Lemma set_card_iff__solve_counting :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros z.
      rewrite <- (@enum_ok A P FP z), <- (@enum_ok A Q FQ z).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun _ acc => 1 + acc) 0 l =
            1 + fold_right (fun _ acc => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma finite_iff__solve_counting
    {A : Type} (P Q : A -> Prop) (FP : Finite P)
    (Heq : forall x, Q x <-> P x) : Finite Q.
Proof.
  refine {| enum := @enum A P FP |}.
  - intros x. split.
    + intros HQ. apply (proj1 (@enum_ok A P FP x)). apply (proj1 (Heq x)). exact HQ.
    + intros Hin. apply (proj2 (Heq x)). apply (proj2 (@enum_ok A P FP x)). exact Hin.
  - exact (@enum_nodup A P FP).
Qed.
Lemma set_card_bijection__solve_counting :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
         (FP : Finite P) (FQ : Finite Q) (f : A -> B) (g : B -> A),
    (forall x, P x -> Q (f x)) ->
    (forall y, Q y -> P (g y)) ->
    (forall x, P x -> g (f x) = x) ->
    (forall y, Q y -> f (g y) = y) ->
    @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f g Hf Hg Hgf Hfg.
  unfold set_card, SumLib.Sum.sum.
  assert (Hnodup_map : NoDup (map f (@enum A P FP))).
  {
    assert (Hgeneral : forall xs : list A,
      NoDup xs -> (forall x, In x xs -> P x) -> NoDup (map f xs)).
    {
      intros xs Hnodup.
      induction Hnodup as [|x xs Hnotin Hnodup IH]; intros Hall; simpl.
      - constructor.
      - constructor.
        + intro Hin. apply in_map_iff in Hin.
          destruct Hin as [y [Hfy Hy]].
          apply Hnotin.
          assert (HPx : P x) by (apply Hall; left; reflexivity).
          assert (HPy : P y) by (apply Hall; right; exact Hy).
          assert (Hxy : x = y).
          { rewrite <- (Hgf x HPx), <- (Hgf y HPy). congruence. }
          rewrite Hxy. exact Hy.
        + apply IH. intros y Hy. apply Hall. right. exact Hy.
    }
    apply Hgeneral.
    - exact (@enum_nodup A P FP).
    - intros x Hx. apply (proj2 (@enum_ok A P FP x)). exact Hx.
  }
  assert (Hperm : Permutation (map f (@enum A P FP)) (@enum B Q FQ)).
  {
    apply NoDup_Permutation.
    - exact Hnodup_map.
    - exact (@enum_nodup B Q FQ).
    - intros y. rewrite <- (@enum_ok B Q FQ y), in_map_iff.
      split.
      + intros [x [<- Hx]].
        apply Hf. apply (proj2 (@enum_ok A P FP x)). exact Hx.
      + intros Hy.
        exists (g y). split; [exact (Hfg y Hy) |].
        apply (proj1 (@enum_ok A P FP (g y))). apply Hg. exact Hy.
  }
  assert (Hcount : forall (C : Type) (xs : list C),
    fold_right (fun _ (acc : Z) => 1 + acc) 0 xs = Z.of_nat (length xs)).
  {
    intros C xs. induction xs as [|x xs IH].
    - reflexivity.
    - cbn [fold_right length]. rewrite IH, Nat2Z.inj_succ. lia.
  }
  rewrite !Hcount.
  rewrite <- (Permutation_length Hperm), length_map.
  reflexivity.
Qed.
Lemma set_card_disjoint_or__solve_counting :
  forall {A : Type} (P Q : A -> Prop)
         (FP : Finite P) (FQ : Finite Q) (FU : Finite (fun x => P x \/ Q x)),
    (forall x, ~ (P x /\ Q x)) ->
    @set_card A (fun x => P x \/ Q x) FU =
    @set_card A P FP + @set_card A Q FQ.
Proof.
  intros A P Q FP FQ FU Hdisj.
  unfold set_card, SumLib.Sum.sum.
  set (E := @enum A (fun x => P x \/ Q x) FU).
  set (EP := filter (fun x => if prop_dec (P x) then true else false) E).
  set (EQ := filter (fun x => if prop_dec (Q x) then true else false) E).
  assert (Hpart : Permutation E (EP ++ EQ)).
  {
    apply NoDup_Permutation.
    - subst E. exact (@enum_nodup A (fun x => P x \/ Q x) FU).
    - apply NoDup_app.
      repeat split.
      + subst EP. apply NoDup_filter.
        subst E. exact (@enum_nodup A (fun x => P x \/ Q x) FU).
      + subst EQ. apply NoDup_filter.
        subst E. exact (@enum_nodup A (fun x => P x \/ Q x) FU).
      + intros x HxP HxQ.
        subst EP EQ. rewrite !filter_In in *.
        destruct HxP as [_ HP], HxQ as [_ HQ].
        destruct (prop_dec (P x)); destruct (prop_dec (Q x));
          simpl in *; try discriminate; try contradiction.
        apply (Hdisj x). tauto.
    - intros x. subst EP EQ E.
      rewrite in_app_iff, !filter_In, <- (@enum_ok A (fun x => P x \/ Q x) FU x).
      destruct (prop_dec (P x)); destruct (prop_dec (Q x)); simpl; tauto.
  }
  assert (HpermP : Permutation EP (@enum A P FP)).
  {
    apply NoDup_Permutation.
    - subst EP E. apply NoDup_filter. exact (@enum_nodup A (fun x => P x \/ Q x) FU).
    - exact (@enum_nodup A P FP).
    - intros x. subst EP E. rewrite filter_In, <- !enum_ok.
      split.
      + intros [_ Htest]. destruct (prop_dec (P x)); simpl in Htest;
          [assumption | discriminate].
      + intros HP. split; [left; exact HP |].
        destruct (prop_dec (P x)); simpl; [reflexivity | contradiction].
  }
  assert (HpermQ : Permutation EQ (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - subst EQ E. apply NoDup_filter. exact (@enum_nodup A (fun x => P x \/ Q x) FU).
    - exact (@enum_nodup A Q FQ).
    - intros x. subst EQ E. rewrite filter_In, <- !enum_ok.
      split.
      + intros [_ Htest]. destruct (prop_dec (Q x)); simpl in Htest;
          [assumption | discriminate].
      + intros HQ. split; [right; exact HQ |].
        destruct (prop_dec (Q x)); simpl; [reflexivity | contradiction].
  }
  assert (Hcount : forall (C : Type) (xs : list C),
    fold_right (fun _ (acc : Z) => 1 + acc) 0 xs = Z.of_nat (length xs)).
  {
    intros C xs. induction xs as [|x xs IH].
    - reflexivity.
    - cbn [fold_right length]. rewrite IH, Nat2Z.inj_succ. lia.
  }
  rewrite !Hcount.
  rewrite (Permutation_length Hpart), length_app,
    (Permutation_length HpermP), (Permutation_length HpermQ), Nat2Z.inj_add.
  reflexivity.
Qed.
Lemma set_card_sublist_bit_shift__solve_counting :
  forall before l i bit choice,
    0 <= l <= i -> i <= Zlength before ->
    #(fun k : Z => l <= k < i /\ BitAt (Znth k before 0) bit = choice) =
    #(fun x : Z =>
        0 <= x < Zlength (sublist l i before) /\
        BitAt (Znth x (sublist l i before) 0) bit = choice).
Proof.
  intros before l i bit choice Hli Hilen.
  eapply set_card_bijection__solve_counting
    with (f := fun k => k - l) (g := fun x => x + l).
  - intros k [Hk Hbit].
    rewrite Zlength_sublist by lia.
    split; [lia |].
    rewrite Znth_sublist by lia.
    replace (k - l + l) with k by lia. exact Hbit.
  - intros x [Hx Hbit].
    rewrite Zlength_sublist in Hx by lia.
    split; [lia |].
    rewrite Znth_sublist in Hbit by lia.
    exact Hbit.
  - intros k Hk. lia.
  - intros x Hx. lia.
Qed.
Lemma bit_contribution_append_one__solve_counting :
  forall segment bit choice delta v added,
    (choice = 0 \/ choice = 1) ->
    BitContribution segment bit bit choice delta ->
    BitAt v bit = choice ->
    added = #(fun x : Z =>
      0 <= x < Zlength segment /\
      BitAt (Znth x segment 0) bit = 1 - choice) ->
    BitContribution (segment ++ v :: nil) bit bit choice (delta + added).
Proof.
  intros segment bit choice delta v added Hchoice Hdelta Hv Hadd.
  unfold BitContribution in *.
  subst delta added.
  rewrite Zlength_app_cons.
  set (New := fun p : Z * Z =>
    (0 <= fst p < Zlength segment + 1 /\
     0 <= snd p < Zlength segment + 1) /\
    fst p < snd p /\
    SameHigherBits (segment ++ v :: nil) bit bit (fst p) (snd p) /\
    ((choice = 0 /\ BitAt (Znth (fst p) (segment ++ v :: nil) 0) bit = 1 /\
                     BitAt (Znth (snd p) (segment ++ v :: nil) 0) bit = 0) \/
     (choice = 1 /\ BitAt (Znth (fst p) (segment ++ v :: nil) 0) bit = 0 /\
                     BitAt (Znth (snd p) (segment ++ v :: nil) 0) bit = 1))).
  set (Old := fun p : Z * Z =>
    (0 <= fst p < Zlength segment /\ 0 <= snd p < Zlength segment) /\
    fst p < snd p /\
    SameHigherBits (segment ++ v :: nil) bit bit (fst p) (snd p) /\
    ((choice = 0 /\ BitAt (Znth (fst p) (segment ++ v :: nil) 0) bit = 1 /\
                     BitAt (Znth (snd p) (segment ++ v :: nil) 0) bit = 0) \/
     (choice = 1 /\ BitAt (Znth (fst p) (segment ++ v :: nil) 0) bit = 0 /\
                     BitAt (Znth (snd p) (segment ++ v :: nil) 0) bit = 1))).
  set (Added := fun p : Z * Z =>
    (0 <= fst p < Zlength segment + 1 /\
     0 <= snd p < Zlength segment + 1) /\
    snd p = Zlength segment /\
    fst p < Zlength segment /\
    BitAt (Znth (fst p) (segment ++ v :: nil) 0) bit = 1 - choice).
  assert (Hnew_split :
    @set_card (Z * Z) New _ =
    @set_card (Z * Z) Old _ + @set_card (Z * Z) Added _).
  {
    assert (FUnion : Finite (fun p => Old p \/ Added p)).
    {
      eapply finite_iff__solve_counting with
        (P := fun p : Z * Z =>
          (0 <= fst p < Zlength segment + 1 /\
           0 <= snd p < Zlength segment + 1) /\
          (Old p \/ Added p)).
      - typeclasses eauto.
      - intros [x y]. subst Old Added. cbn [fst snd]. split; intros H.
        + destruct H as [H | H]; destruct H as [[Hx Hy] Hrest];
            repeat split; try lia; tauto.
        + tauto.
    }
    rewrite (@set_card_iff__solve_counting (Z * Z) New
      (fun p => Old p \/ Added p) _ FUnion);
      [| intros [x y]; subst New Old Added; cbn [fst snd];
         unfold SameHigherBits; split; intros H].
    - apply (@set_card_disjoint_or__solve_counting
        (Z * Z) Old Added _ _ FUnion).
      intros [x y] [Hold Hadd]. subst Old Added. cbn [fst snd] in *.
      lia.
    - destruct H as [[Hx Hy] [Hxy [Hhigher Hbits]]].
      destruct Hchoice as [-> | ->]; cbn in *.
      + destruct Hbits as [[_ [Hbx Hby]] | [Hbad _]]; [|lia].
        destruct (Z_lt_ge_dec y (Zlength segment)).
        * left. repeat split; try lia; try assumption.
        * right. repeat split; try lia; try assumption.
      + destruct Hbits as [[Hbad _] | [_ [Hbx Hby]]]; [lia|].
        destruct (Z_lt_ge_dec y (Zlength segment)).
        * left. repeat split; try lia; try assumption.
        * right. repeat split; try lia; try assumption.
    - destruct H as [Hold | Hadd].
      + destruct Hold as [[Hx Hy] [Hxy [Hhigher Hbits]]].
        repeat split; try lia; try assumption.
      + destruct Hadd as [[Hx Hy] [Hyend [Hxlt Hbx]]].
        subst y. repeat split; try lia.
        destruct Hchoice as [-> | ->]; cbn in *.
        * left. repeat split; try lia; try assumption.
          rewrite app_Znth2 by lia.
          replace (Zlength segment - Zlength segment) with 0 by lia.
          rewrite Znth0_cons. exact Hv.
        * right. repeat split; try lia; try assumption.
          rewrite app_Znth2 by lia.
          replace (Zlength segment - Zlength segment) with 0 by lia.
          rewrite Znth0_cons. exact Hv.
  }
  rewrite Hnew_split.
  assert (Hold_eq : @set_card (Z * Z) Old _ =
    #(fun p : Z * Z =>
      (0 <= fst p < Zlength segment /\ 0 <= snd p < Zlength segment) /\
      fst p < snd p /\ SameHigherBits segment bit bit (fst p) (snd p) /\
      ((choice = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                       BitAt (Znth (snd p) segment 0) bit = 0) \/
       (choice = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                       BitAt (Znth (snd p) segment 0) bit = 1)))).
  {
    apply set_card_iff__solve_counting. intros [x y]. subst Old.
    cbn [fst snd]. unfold SameHigherBits.
    split; intros H; destruct H as [[Hx Hy] [Hxy [Hhigher Hbits]]].
    - split; [exact (conj Hx Hy) |]. split; [exact Hxy |].
      split; [intros; lia |].
      destruct Hbits as [[Hc [Hbx Hby]] | [Hc [Hbx Hby]]].
      + left. repeat split; try assumption;
          rewrite app_Znth1 in * by lia; assumption.
      + right. repeat split; try assumption;
          rewrite app_Znth1 in * by lia; assumption.
    - split; [exact (conj Hx Hy) |]. split; [exact Hxy |].
      split; [intros; lia |].
      destruct Hbits as [[Hc [Hbx Hby]] | [Hc [Hbx Hby]]].
      + left. repeat split; try assumption;
          rewrite app_Znth1 by lia; assumption.
      + right. repeat split; try assumption;
          rewrite app_Znth1 by lia; assumption.
  }
  rewrite Hold_eq.
  assert (Hadded_eq : @set_card (Z * Z) Added _ =
    #(fun x : Z => 0 <= x < Zlength segment /\
                    BitAt (Znth x segment 0) bit = 1 - choice)).
  {
    eapply set_card_bijection__solve_counting
      with (f := fun p => fst p) (g := fun x => (x, Zlength segment)).
    - intros [x y] Haddp. subst Added. cbn [fst snd] in *.
      destruct Haddp as [[Hx Hy] [-> [Hxlt Hbit]]]. split; [lia |].
      rewrite app_Znth1 in Hbit by lia. exact Hbit.
    - intros x [Hx Hbit]. subst Added. cbn [fst snd].
      repeat split; try lia. rewrite app_Znth1 by lia. exact Hbit.
    - intros [x y] Haddp. subst Added. cbn [fst snd] in *.
      destruct Haddp as [_ [-> _]]. reflexivity.
    - intros x Hx. reflexivity.
  }
  rewrite Hadded_eq. reflexivity.
Qed.
Lemma bit_contribution_append_noadd__solve_counting :
  forall segment bit choice delta v,
    (choice = 0 \/ choice = 1) ->
    BitContribution segment bit bit choice delta ->
    BitAt v bit <> choice ->
    BitContribution (segment ++ v :: nil) bit bit choice delta.
Proof.
  intros segment bit choice delta v Hchoice Hdelta Hv.
  unfold BitContribution in *.
  rewrite Zlength_app_cons.
  rewrite Hdelta.
  apply set_card_iff__solve_counting.
  intros [x y]. cbn [fst snd]. unfold SameHigherBits.
  split; intros H.
  - destruct H as [[Hx Hy] [Hxy [Hhigher Hbits]]].
    assert (Hyold : y < Zlength segment).
    {
      destruct (Z_lt_ge_dec y (Zlength segment)); [assumption |].
      assert (y = Zlength segment) by lia; subst y.
      destruct Hchoice as [-> | ->]; cbn in *;
        destruct Hbits as [[Hc [Hbx Hby]] | [Hc [Hbx Hby]]]; try lia;
        rewrite app_Znth2 in Hby by lia;
        replace (Zlength segment - Zlength segment) with 0 in Hby by lia;
        rewrite Znth0_cons in Hby; contradiction.
    }
    assert (Hbounds : (0 <= x < Zlength segment + 1) /\
                      (0 <= y < Zlength segment + 1)) by
      (destruct Hx; destruct Hy; split; split; lia).
    split; [exact Hbounds |]. split; [exact Hxy |]. split; [intros; lia |].
    destruct Hbits as [[Hc [Hbx Hby]] | [Hc [Hbx Hby]]].
    + left. repeat split; try assumption;
        rewrite app_Znth1 in * by lia; assumption.
    + right. repeat split; try assumption;
        rewrite app_Znth1 in * by lia; assumption.
  - destruct H as [[Hx Hy] [Hxy [Hhigher Hbits]]].
    assert (Hyold : y < Zlength segment).
    {
      destruct (Z_lt_ge_dec y (Zlength segment)); [assumption |].
      assert (y = Zlength segment) by lia; subst y.
      destruct Hchoice as [-> | ->]; cbn in *;
        destruct Hbits as [[Hc [Hbx Hby]] | [Hc [Hbx Hby]]]; try lia;
        rewrite app_Znth2 in Hby by lia;
        replace (Zlength segment - Zlength segment) with 0 in Hby by lia;
        rewrite Znth0_cons in Hby; contradiction.
    }
    assert (Hbounds : (0 <= x < Zlength segment) /\
                      (0 <= y < Zlength segment)) by
      (destruct Hx; destruct Hy; split; split; lia).
    split; [exact Hbounds |]. split; [exact Hxy |]. split; [intros; lia |].
    destruct Hbits as [[Hc [Hbx Hby]] | [Hc [Hbx Hby]]].
    + left. split; [exact Hc |]. split.
      * rewrite app_Znth1 in Hbx by lia. exact Hbx.
      * rewrite app_Znth1 in Hby by lia. exact Hby.
    + right. split; [exact Hc |]. split.
      * rewrite app_Znth1 in Hbx by lia. exact Hbx.
      * rewrite app_Znth1 in Hby by lia. exact Hby.
Qed.
Lemma set_card_Z_as_sum__solve_counting :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_true__solve_counting :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__solve_counting.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [_ | Hnot]; [lia | contradiction].
Qed.
Lemma set_card_Z_extend_false__solve_counting :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__solve_counting.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [Hp | _]; [contradiction | lia].
Qed.
Lemma solve_count_prefix_step_one__solve_counting :
  forall before entry current l i bit zeros ones,
    0 <= l <= i -> i < Zlength before -> 0 <= bit < 30 ->
    SolveCountPrefix before entry current l i bit zeros ones ->
    BitAt (Znth i before 0) bit = 1 ->
    SolveCountPrefix before entry
      (replace_Znth bit
        (replace_Znth 1 (CostAt current bit 1 + zeros)
          (Znth bit current nil)) current)
      l (i + 1) bit zeros (ones + 1).
Proof.
  intros before entry current l i bit zeros ones Hli Hib Hbit Hsolve Hnew.
  unfold SolveCountPrefix in *.
  destruct Hsolve as [Hzero [Hone [Hentry [Hcurrent [Hrows Hcells]]]]].
  split.
  - rewrite (set_card_Z_extend_false__solve_counting l i
      (fun k => BitAt (Znth k before 0) bit = 0)); [exact Hzero | lia |].
    intro Hbad. lia.
  - split.
    + rewrite (set_card_Z_extend_true__solve_counting l i
        (fun k => BitAt (Znth k before 0) bit = 1)); [lia | lia | exact Hnew].
    + split; [exact Hentry |].
      split.
      * rewrite Zlength_replace_Znth. exact Hcurrent.
      * split.
        -- intros b Hb. specialize (Hrows b Hb) as [Hentryrow Hcurrow].
           split; [exact Hentryrow |].
           destruct (Z.eq_dec b bit) as [-> | Hne].
           ++ rewrite Znth_replace_Znth_Same by lia.
              rewrite Zlength_replace_Znth. exact Hcurrow.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hcurrow.
        -- intros b c Hb Hc.
           specialize (Hcells b c Hb Hc).
           destruct (Z.eq_dec b bit) as [-> | Hne].
           ++ left. split; [reflexivity |].
              destruct Hcells as [[_ [delta [Hcontrib Hcost]]] | [Hbad _]];
                [| contradiction].
              destruct (Z.eq_dec c 1) as [-> | Hcne].
              ** exists (delta + zeros). split.
                 --- assert (Hsegment_count :
                       zeros = #(fun x : Z =>
                         0 <= x < Zlength (sublist l i before) /\
                         BitAt (Znth x (sublist l i before) 0) bit = 0)).
                     { rewrite <- (set_card_sublist_bit_shift__solve_counting
                         before l i bit 0) by lia. exact Hzero. }
                     assert (Hsub : sublist l (i + 1) before =
                       sublist l i before ++ Znth i before 0 :: nil).
                     { rewrite (sublist_split l (i + 1) i before) by lia.
                       rewrite (sublist_single 0 i before) by lia. reflexivity. }
                     rewrite Hsub.
                     eapply bit_contribution_append_one__solve_counting;
                       [right; reflexivity | exact Hcontrib | exact Hnew |].
                     replace (1 - 1) with 0 by lia. exact Hsegment_count.
                 --- unfold CostAt in *.
                     pose proof (Hrows bit Hbit) as [_ Hrowlen].
                     rewrite Znth_replace_Znth_Same by lia.
                     rewrite Znth_replace_Znth_Same by lia.
                     lia.
              ** assert (c = 0) by lia; subst c.
                 exists delta. split.
                 --- assert (Hsub : sublist l (i + 1) before =
                       sublist l i before ++ Znth i before 0 :: nil).
                     { rewrite (sublist_split l (i + 1) i before) by lia.
                       rewrite (sublist_single 0 i before) by lia. reflexivity. }
                     rewrite Hsub.
                     eapply bit_contribution_append_noadd__solve_counting;
                       [left; reflexivity | exact Hcontrib | lia].
                 --- unfold CostAt in *.
                     pose proof (Hrows bit Hbit) as [_ Hrowlen].
                     rewrite Znth_replace_Znth_Same by lia.
                     rewrite Znth_replace_Znth_Diff by lia.
                     exact Hcost.
           ++ right. split; [exact Hne |].
              destruct Hcells as [[Heq _] | [_ Hcost]]; [contradiction |].
              unfold CostAt in *.
              rewrite Znth_replace_Znth_Diff by lia.
              exact Hcost.
Qed.
Lemma solve_count_prefix_step_zero__solve_counting :
  forall before entry current l i bit zeros ones,
    0 <= l <= i -> i < Zlength before -> 0 <= bit < 30 ->
    SolveCountPrefix before entry current l i bit zeros ones ->
    BitAt (Znth i before 0) bit = 0 ->
    SolveCountPrefix before entry
      (replace_Znth bit
        (replace_Znth 0 (CostAt current bit 0 + ones)
          (Znth bit current nil)) current)
      l (i + 1) bit (zeros + 1) ones.
Proof.
  intros before entry current l i bit zeros ones Hli Hib Hbit Hsolve Hnew.
  unfold SolveCountPrefix in *.
  destruct Hsolve as [Hzero [Hone [Hentry [Hcurrent [Hrows Hcells]]]]].
  split.
  - rewrite (set_card_Z_extend_true__solve_counting l i
      (fun k => BitAt (Znth k before 0) bit = 0)); [lia | lia | exact Hnew].
  - split.
    + rewrite (set_card_Z_extend_false__solve_counting l i
        (fun k => BitAt (Znth k before 0) bit = 1)); [exact Hone | lia |].
      intro Hbad. lia.
    + split; [exact Hentry |].
      split.
      * rewrite Zlength_replace_Znth. exact Hcurrent.
      * split.
        -- intros b Hb. specialize (Hrows b Hb) as [Hentryrow Hcurrow].
           split; [exact Hentryrow |].
           destruct (Z.eq_dec b bit) as [-> | Hne].
           ++ rewrite Znth_replace_Znth_Same by lia.
              rewrite Zlength_replace_Znth. exact Hcurrow.
           ++ rewrite Znth_replace_Znth_Diff by lia. exact Hcurrow.
        -- intros b c Hb Hc.
           specialize (Hcells b c Hb Hc).
           destruct (Z.eq_dec b bit) as [-> | Hne].
           ++ left. split; [reflexivity |].
              destruct Hcells as [[_ [delta [Hcontrib Hcost]]] | [Hbad _]];
                [| contradiction].
              destruct (Z.eq_dec c 0) as [-> | Hcne].
              ** exists (delta + ones). split.
                 --- assert (Hsegment_count :
                       ones = #(fun x : Z =>
                         0 <= x < Zlength (sublist l i before) /\
                         BitAt (Znth x (sublist l i before) 0) bit = 1)).
                     { rewrite <- (set_card_sublist_bit_shift__solve_counting
                         before l i bit 1) by lia. exact Hone. }
                     assert (Hsub : sublist l (i + 1) before =
                       sublist l i before ++ Znth i before 0 :: nil).
                     { rewrite (sublist_split l (i + 1) i before) by lia.
                       rewrite (sublist_single 0 i before) by lia. reflexivity. }
                     rewrite Hsub.
                     eapply bit_contribution_append_one__solve_counting;
                       [left; reflexivity | exact Hcontrib | exact Hnew |].
                     replace (1 - 0) with 1 by lia. exact Hsegment_count.
                 --- unfold CostAt in *.
                     pose proof (Hrows bit Hbit) as [_ Hrowlen].
                     rewrite Znth_replace_Znth_Same by lia.
                     rewrite Znth_replace_Znth_Same by lia.
                     lia.
              ** assert (c = 1) by lia; subst c.
                 exists delta. split.
                 --- assert (Hsub : sublist l (i + 1) before =
                       sublist l i before ++ Znth i before 0 :: nil).
                     { rewrite (sublist_split l (i + 1) i before) by lia.
                       rewrite (sublist_single 0 i before) by lia. reflexivity. }
                     rewrite Hsub.
                     eapply bit_contribution_append_noadd__solve_counting;
                       [right; reflexivity | exact Hcontrib | lia].
                 --- unfold CostAt in *.
                     pose proof (Hrows bit Hbit) as [_ Hrowlen].
                     rewrite Znth_replace_Znth_Same by lia.
                     rewrite Znth_replace_Znth_Diff by lia.
                     exact Hcost.
           ++ right. split; [exact Hne |].
              destruct Hcells as [[Heq _] | [_ Hcost]]; [contradiction |].
              unfold CostAt in *.
              rewrite Znth_replace_Znth_Diff by lia.
              exact Hcost.
Qed.
Lemma cost_bound_update_cell__solve_counting :
  forall costs bit choice inc old_limit new_limit,
    0 <= bit < 30 -> 0 <= choice < 2 ->
    Zlength (Znth bit costs nil) = 2 ->
    0 <= inc -> old_limit + inc <= new_limit ->
    CostBound costs old_limit ->
    CostBound
      (replace_Znth bit
        (replace_Znth choice (CostAt costs bit choice + inc)
          (Znth bit costs nil)) costs) new_limit.
Proof.
  intros costs bit choice inc old_limit new_limit Hbit Hchoice Hrow
    Hinc Hlimits Hbound.
  unfold CostBound in *.
  destruct Hbound as [Holdnonneg [Hlen Hcells]].
  split; [lia |]. split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - intros b c Hb Hc.
    destruct (Z.eq_dec b bit) as [-> | Hbne].
    + destruct (Z.eq_dec c choice) as [-> | Hcne].
      * specialize (Hcells bit choice Hbit Hchoice).
        unfold CostAt in *.
        rewrite Znth_replace_Znth_Same by lia.
        rewrite Znth_replace_Znth_Same by lia.
        lia.
      * specialize (Hcells bit c Hbit Hc).
        unfold CostAt in *.
        rewrite Znth_replace_Znth_Same by lia.
        rewrite Znth_replace_Znth_Diff by lia.
        lia.
    + specialize (Hcells b c Hb Hc).
      unfold CostAt in *.
      rewrite Znth_replace_Znth_Diff by lia.
      lia.
Qed.
Lemma sublist_replace_Znth_prefix__solve_counting :
  forall {A : Type} (d v : A) (l : list A) i,
    0 <= i <= Zlength l ->
    sublist 0 i (replace_Znth i v l) = sublist 0 i l.
Proof.
  intros A d v l i Hi.
  destruct (Z.eq_dec i (Zlength l)) as [-> | Hne].
  - rewrite replace_Znth_nothing by lia. reflexivity.
  - apply (proj2 (list_eq_ext _ _ d)). split.
    + rewrite !Zlength_sublist0; try rewrite Zlength_replace_Znth; lia.
    + intros k Hk.
      rewrite Zlength_sublist0 in Hk by (rewrite Zlength_replace_Znth; lia).
      rewrite !Znth_sublist0 by (try rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia. reflexivity.
Qed.
Lemma sublist_replace_Znth_suffix__solve_counting :
  forall {A : Type} (d v : A) (l : list A) i hi,
    0 <= i < hi -> hi <= Zlength l ->
    sublist (i + 1) hi (replace_Znth i v l) = sublist (i + 1) hi l.
Proof.
  intros A d v l i hi Hih Hhi.
  apply (proj2 (list_eq_ext _ _ d)). split.
  - rewrite !Zlength_sublist; try rewrite Zlength_replace_Znth; lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by (rewrite Zlength_replace_Znth; lia).
    rewrite !Znth_sublist by lia.
    rewrite Znth_replace_Znth_Diff by lia. reflexivity.
Qed.
Lemma bit_at_one_of_nonzero__solve_counting :
  forall value bit, BitAt value bit <> 0 -> BitAt value bit = 1.
Proof.
  intros value bit Hnonzero.
  unfold BitAt in *.
  change (Z.land (Z.shiftr value bit) (Z.ones 1) <> 0) in Hnonzero.
  change (Z.land (Z.shiftr value bit) (Z.ones 1) = 1).
  rewrite Z.land_ones in * by lia.
  change (Z.shiftr value bit mod 2 <> 0) in Hnonzero.
  change (Z.shiftr value bit mod 2 = 1).
  pose proof (Z.mod_pos_bound (Z.shiftr value bit) 2 ltac:(lia)).
  lia.
Qed.
Lemma store_array_rec_merge__solve_counting :
  forall (A : Type) (storeA : addr -> Z -> A -> Assertion)
         x lo mid hi (left right : list A),
    store_array_rec storeA x lo mid left **
    store_array_rec storeA x mid hi right |--
    store_array_rec storeA x lo hi (left ++ right).
Proof.
  intros A storeA x lo mid hi left.
  generalize dependent lo.
  induction left as [|a left IH]; intros lo right; simpl store_array_rec.
  - LLM_pre_process ltac:(lia || nia).
    replace lo with mid by lia. reflexivity.
  - cancel (storeA x lo a).
    sep_apply_l_atomic (IH (lo + 1) right).
    LLM_pre_process ltac:(lia || nia).
Qed.
Lemma int64array2_row_cells_merge__solve_counting :
  forall x row v0 v1,
    row = v0 :: v1 :: nil ->
    (x + 0 * sizeof(INT64)) # Int64 |-> v0 **
    (x + 1 * sizeof(INT64)) # Int64 |-> v1 |--
    Int64Array.full x 2 row.
Proof.
  intros x row v0 v1 ->.
  unfold Int64Array.full, store_array.
  cbn [store_array_rec].
  rewrite sizeof_int64.
  LLM_pre_process ltac:(lia || nia).
Qed.
Lemma int64array2_pieces_merge__solve_counting :
  forall x bit prefix row suffix,
    store_array_rec (Int64Array2.row_store 2) x 0 bit prefix **
    Int64Array.full (Int64Array2.row_addr x 2 bit) 2 row **
    store_array_rec (Int64Array2.row_store 2) x (bit + 1) 30 suffix |--
    Int64Array2.full x 30 2 (prefix ++ row :: suffix).
Proof.
  intros x bit prefix row suffix.
  unfold Int64Array2.full, store_array.
  change
    (store_array_rec (Int64Array2.row_store 2) x 0 bit prefix **
     Int64Array2.row_store 2 x bit row **
     store_array_rec (Int64Array2.row_store 2) x (bit + 1) 30 suffix |--
     store_array_rec (Int64Array2.row_store 2) x 0 30
       (prefix ++ row :: suffix)).
  assert (Hsingle : Int64Array2.row_store 2 x bit row |--
    store_array_rec (Int64Array2.row_store 2) x bit (bit + 1)
      (row :: nil)).
  {
    cbn [store_array_rec].
    LLM_pre_process ltac:(lia || nia).
  }
  sep_apply_l_atomic Hsingle.
  sep_apply_l_atomic
    (store_array_rec_merge__solve_counting
      (list Z) (Int64Array2.row_store 2) x bit (bit + 1) 30
      (row :: nil) suffix).
  sep_apply_l_atomic
    (store_array_rec_merge__solve_counting
      (list Z) (Int64Array2.row_store 2) x 0 bit 30
      prefix (row :: suffix)).
  reflexivity.
Qed.
Lemma sublist_replace_Znth_before__stable_partition :
  forall {A : Type} (xs : list A) (d v : A) lo hi idx,
    0 <= lo <= hi -> hi <= idx -> idx < Zlength xs ->
    sublist lo hi (replace_Znth idx v xs) = sublist lo hi xs.
Proof.
  intros A xs d v lo hi idx Hlo Hhi Hidx.
  apply (proj2 (list_eq_ext _ _ d)). split.
  - rewrite !Zlength_sublist; try rewrite Zlength_replace_Znth; lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by (rewrite Zlength_replace_Znth; lia).
    rewrite !Znth_sublist by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Diff by lia. reflexivity.
Qed.
Lemma Znth_map__stable_partition :
  forall {A B : Type} (f : A -> B) xs (da : A) (db : B) i,
    0 <= i < Zlength xs -> Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia. apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Zlength_Zrange_aux__stable_partition :
  forall low m, Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. rewrite Zlength_correct. f_equal.
  revert low. induction m as [|m IH]; intros; simpl; congruence.
Qed.
Lemma Zlength_Zrange__stable_partition :
  forall low high, low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hrange. unfold Zrange.
  rewrite Zlength_Zrange_aux__stable_partition. lia.
Qed.
Lemma Znth_Zrange_aux__stable_partition :
  forall m low i, 0 <= i < Z.of_nat m ->
    Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia|]. simpl.
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__stable_partition :
  forall low high i, low <= high -> 0 <= i < high - low ->
    Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hrange Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__stable_partition by lia. lia.
Qed.
Lemma map_Znth_Zrange_sublist__stable_partition :
  forall {A : Type} (xs : list A) (d : A) lo hi,
    0 <= lo <= hi -> hi <= Zlength xs ->
    map (fun k => Znth k xs d) (Zrange lo hi) = sublist lo hi xs.
Proof.
  intros A xs d lo hi Hlo Hhi.
  apply (proj2 (list_eq_ext _ _ d)). split.
  - rewrite Zlength_correct, length_map, <- Zlength_correct,
      Zlength_Zrange__stable_partition by lia.
    rewrite Zlength_sublist by lia. lia.
  - intros j Hj.
    rewrite Zlength_correct, length_map, <- Zlength_correct,
      Zlength_Zrange__stable_partition in Hj by lia.
    rewrite (@Znth_map__stable_partition Z A
      (fun k => Znth k xs d) (Zrange lo hi) 0 d j) by
      (rewrite Zlength_Zrange__stable_partition by lia; lia).
    rewrite Znth_Zrange__stable_partition by lia.
    rewrite Znth_sublist by lia. f_equal. lia.
Qed.
Lemma filter_map_comm__stable_partition :
  forall {A B : Type} (test : B -> bool) (f : A -> B) xs,
    filter test (map f xs) = map f (filter (fun x => test (f x)) xs).
Proof.
  intros A B test f xs. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (test (f x)); simpl; rewrite IH; reflexivity.
Qed.
Lemma sum_permutation__stable_partition : forall xs ys : list Z,
  Permutation xs ys -> ListLib.sum xs = ListLib.sum ys.
Proof. intros xs ys Hperm. induction Hperm; simpl; lia. Qed.
Lemma fold_sum_map__stable_partition : forall {A : Type} (f : A -> Z) xs,
  fold_right (fun x acc => f x + acc) 0 xs = ListLib.sum (map f xs).
Proof.
  intros A f xs. induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
Lemma finite_sum_as_filter__stable_partition : forall lo hi
    (P : Z -> Prop) (F : Finite (fun i : Z => lo <= i < hi /\ P i))
    (f : Z -> Z) order,
  Permutation (Zrange lo hi) order ->
  @SumLib.Sum.sum Z (fun i : Z => lo <= i < hi /\ P i) F f =
  ListLib.sum (map f
    (filter (fun i => if prop_dec (P i) then true else false) order)).
Proof.
  intros lo hi P F f order Hperm. unfold SumLib.Sum.sum.
  rewrite fold_sum_map__stable_partition.
  apply sum_permutation__stable_partition. apply Permutation_map.
  apply NoDup_Permutation.
  - apply enum_nodup.
  - apply NoDup_filter. eapply Permutation_NoDup; [exact Hperm|].
    apply NoDup_Zrange.
  - intros x. rewrite <- enum_ok, filter_In. split.
    + intros [Hrange HP]. split.
      * eapply Permutation_in; [exact Hperm|]. apply In_Zrange. exact Hrange.
      * destruct (prop_dec (P x)) as [_|Hnot]; [reflexivity|contradiction].
    + intros [Hin Htest]. split.
      * apply In_Zrange. eapply Permutation_in;
          [apply Permutation_sym; exact Hperm|exact Hin].
      * destruct (prop_dec (P x)) as [HP|Hnot]; [exact HP|discriminate].
Qed.
Lemma sum_ones_length__stable_partition : forall {A : Type} (xs : list A),
  ListLib.sum (map (fun _ => 1) xs) = Zlength xs.
Proof.
  intros A xs. induction xs as [|x xs IH]; [reflexivity|].
  rewrite Zlength_cons. change (1 + ListLib.sum (map (fun _ : A => 1) xs) =
    Zlength xs + 1). rewrite IH. lia.
Qed.
Lemma set_card_as_filter_length__stable_partition : forall lo hi
    (P : Z -> Prop) (F : Finite (fun i : Z => lo <= i < hi /\ P i)) order,
  Permutation (Zrange lo hi) order ->
  @set_card Z (fun i : Z => lo <= i < hi /\ P i) F =
  Zlength (filter (fun i => if prop_dec (P i) then true else false) order).
Proof.
  intros lo hi P F order Hperm. unfold set_card.
  rewrite (finite_sum_as_filter__stable_partition lo hi P F
    (fun _ => 1) order Hperm).
  apply sum_ones_length__stable_partition.
Qed.
Lemma set_card_bit_slice_filter__stable_partition :
  forall before l r bit class,
    0 <= l -> l <= r -> r <= Zlength before ->
    #(fun k : Z => l <= k < r /\ BitAt (Znth k before 0) bit = class) =
    Zlength (filter (BitIs bit class) (sublist l r before)).
Proof.
  intros before l r bit class Hl Hlr Hr.
  rewrite (set_card_as_filter_length__stable_partition l r
    (fun k => BitAt (Znth k before 0) bit = class)
    _ (Zrange l r) (Permutation_refl _)).
  assert (Htest :
    (fun k : Z => if prop_dec (BitAt (Znth k before 0) bit = class)
      then true else false) =
    (fun k => BitIs bit class (Znth k before 0))).
  { apply functional_extensionality. intro k. unfold BitIs.
    destruct (prop_dec (BitAt (Znth k before 0) bit = class));
      [apply Z.eqb_eq in e|apply Z.eqb_neq in n]; congruence. }
  rewrite Htest.
  transitivity (Zlength (map (fun k => Znth k before 0)
    (filter (fun k => BitIs bit class (Znth k before 0)) (Zrange l r)))).
  - rewrite !Zlength_correct, length_map. reflexivity.
  - rewrite <- filter_map_comm__stable_partition.
    rewrite map_Znth_Zrange_sublist__stable_partition by lia. reflexivity.
Qed.
Lemma bit_at_binary__stable_partition : forall value bit,
  BitAt value bit = 0 \/ BitAt value bit = 1.
Proof.
  intros value bit. unfold BitAt.
  change (Z.land (Z.shiftr value bit) (Z.ones 1) = 0 \/
          Z.land (Z.shiftr value bit) (Z.ones 1) = 1).
  rewrite Z.land_ones by lia.
  destruct (Z.mod_pos_bound (Z.shiftr value bit) 2 ltac:(lia)) as [Hlo Hhi].
  destruct (Z.lt_trichotomy (Z.shiftr value bit mod 2) 1)
    as [Hlt | [Heq | Hgt]].
  - left. apply Z.le_antisymm;
      [apply (proj1 (Z.lt_succ_r _ 0)); exact Hlt|exact Hlo].
  - right. exact Heq.
  - exfalso. pose proof (proj1 (Z.lt_succ_r _ 1) Hhi) as Hle. lia.
Qed.
Lemma filter_bit_lengths__stable_partition : forall xs bit,
  Zlength (filter (BitIs bit 0) xs) +
  Zlength (filter (BitIs bit 1) xs) = Zlength xs.
Proof.
  intros xs bit. induction xs as [|x xs IH]; simpl; [reflexivity|].
  destruct (bit_at_binary__stable_partition x bit) as [Hz|Ho].
  - unfold BitIs in *. rewrite Hz. simpl. rewrite !Zlength_cons. lia.
  - unfold BitIs in *. rewrite Ho. simpl. rewrite !Zlength_cons. lia.
Qed.
Lemma sublist_replace_Znth_step__stable_partition :
  forall {A : Type} (xs : list A) (d v : A) lo idx,
    0 <= lo <= idx -> idx < Zlength xs ->
    sublist lo (idx + 1) (replace_Znth idx v xs) =
      sublist lo idx xs ++ v :: nil.
Proof.
  intros A xs d v lo idx Hlo Hidx.
  rewrite (sublist_split lo (idx + 1) idx) by
    (try rewrite Zlength_replace_Znth; lia).
  rewrite (sublist_replace_Znth_before__stable_partition xs d v lo idx idx)
    by lia.
  rewrite (@sublist_single A d idx (replace_Znth idx v xs)) by
    (rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Same by lia. reflexivity.
Qed.
Lemma set_card_empty__solve_base_exits :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:He; [reflexivity |].
  exfalso. apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)). rewrite He. simpl. auto.
Qed.
Lemma bit_contribution_short__solve_base_exits :
  forall segment upper bit choice,
    Zlength segment <= 1 -> BitContribution segment upper bit choice 0.
Proof.
  intros segment upper bit choice Hlen.
  unfold BitContribution. symmetry.
  apply set_card_empty__solve_base_exits.
  intros [i j] [[[Hi0 Hi] [Hj0 Hj]] [Hij _]]. simpl in *.
  lia.
Qed.
Lemma solve_effect_negative__solve_base_exits :
  forall before costs l r bit d,
    bit < 0 -> -1 <= bit -> 0 <= l <= r -> r <= Zlength before ->
    Zlength costs = 30 ->
    (forall b, 0 <= b < 30 -> Zlength (Znth b costs d) = 2) ->
    SolveEffect before before costs costs l r bit.
Proof.
  intros before costs l r bit d Hneg Hm1 Hlr Hr Hlen Hrows.
  assert (Hbit : bit = -1) by lia. subst bit.
  unfold SolveEffect.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [reflexivity |].
  split; [apply Permutation_refl |].
  split; [exact Hlen |].
  split; [exact Hlen |].
  split.
  - intros b0 Hb. split.
    + specialize (Hrows b0 Hb) as Hr0.
      rewrite (Znth_indep costs b0 d (@nil Z)) in Hr0 by lia.
      exact Hr0.
    + specialize (Hrows b0 Hb) as Hr0.
      rewrite (Znth_indep costs b0 d (@nil Z)) in Hr0 by lia.
      exact Hr0.
  - split.
    + intros b0 choice Hb Hchoice. right. split; [lia | reflexivity].
    + intros [Hl0 [Hrfull [Hbad Hzero]]]. lia.
Qed.
Lemma solve_effect_short__solve_base_exits :
  forall before costs l r bit d,
    0 <= bit < 30 -> 0 <= l <= r -> r <= Zlength before -> r - l <= 1 ->
    Zlength costs = 30 ->
    (forall b, 0 <= b < 30 -> Zlength (Znth b costs d) = 2) ->
    SolveEffect before before costs costs l r bit.
Proof.
  intros before costs l r bit d Hbit Hlr Hr Hshort Hlen Hrows.
  assert (Hseg : Zlength (sublist l r before) <= 1).
  { rewrite Zlength_sublist by lia. lia. }
  unfold SolveEffect.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [reflexivity |].
  split; [apply Permutation_refl |].
  split; [exact Hlen |].
  split; [exact Hlen |].
  split.
  - intros b0 Hb. split.
    + specialize (Hrows b0 Hb) as Hr0.
      rewrite (Znth_indep costs b0 d (@nil Z)) in Hr0 by lia.
      exact Hr0.
    + specialize (Hrows b0 Hb) as Hr0.
      rewrite (Znth_indep costs b0 d (@nil Z)) in Hr0 by lia.
      exact Hr0.
  - split.
    + intros b0 choice Hb Hchoice.
      destruct (Z_le_gt_dec b0 bit) as [Hle | Hgt].
      * left. split; [lia |]. exists 0. split.
        -- apply bit_contribution_short__solve_base_exits. exact Hseg.
        -- lia.
      * right. split; [lia | reflexivity].
    + intros [Hl0 [Hrfull [Hbit29 Hzero]]].
      unfold CostTable.
      split; [exact Hlen |]. split.
      * intros b0 Hb.
        specialize (Hrows b0 Hb) as Hr0.
        rewrite (Znth_indep costs b0 d (@nil Z)) in Hr0 by lia.
        exact Hr0.
      * intros b0 choice Hb Hchoice.
        specialize (Hzero b0 choice Hb Hchoice).
        rewrite Hzero.
        apply bit_contribution_short__solve_base_exits.
        subst l. subst r. lia.
Qed.
Lemma bit_at_binary__solve_base_exits :
  forall value bit, BitAt value bit = 0 \/ BitAt value bit = 1.
Proof.
  intros value bit. unfold BitAt.
  change (Z.land (Z.shiftr value bit) (Z.ones 1) = 0 \/
          Z.land (Z.shiftr value bit) (Z.ones 1) = 1).
  rewrite Z.land_ones by lia.
  destruct (Z.mod_pos_bound (Z.shiftr value bit) 2 ltac:(lia)) as [Hlo Hhi].
  destruct (Z.lt_trichotomy (Z.shiftr value bit mod 2) 1)
    as [Hlt | [Heq | Hgt]].
  - left. apply Z.le_antisymm.
    + apply (proj1 (Z.lt_succ_r _ 0)). exact Hlt.
    + exact Hlo.
  - right. exact Heq.
  - exfalso.
    pose proof (proj1 (Z.lt_succ_r _ 1) Hhi) as Hle.
    exact (Z.lt_irrefl 1 (Z.lt_le_trans _ _ _ Hgt Hle)).
Qed.
Lemma filter_bit_partition_permutation__solve_base_exits :
  forall xs bit,
    Permutation xs
      (filter (BitIs bit 0) xs ++ filter (BitIs bit 1) xs).
Proof.
  intros xs bit. induction xs as [|x xs IH]; simpl.
  - apply Permutation_refl.
  - destruct (bit_at_binary__solve_base_exits x bit) as [Hz | Ho].
    + unfold BitIs. rewrite Hz. simpl.
      apply perm_skip. exact IH.
    + unfold BitIs. rewrite Ho. simpl.
      eapply Permutation_trans.
      * apply perm_skip. exact IH.
      * apply Permutation_middle.
Qed.
Lemma filter_bit_partition_length__solve_base_exits :
  forall xs bit,
    Zlength (filter (BitIs bit 0) xs ++ filter (BitIs bit 1) xs) =
    Zlength xs.
Proof.
  intros xs bit.
  rewrite !Zlength_correct.
  f_equal. apply Permutation_length.
  symmetry. apply filter_bit_partition_permutation__solve_base_exits.
Qed.
Lemma Znth_map__solve_base_exits :
  forall {A B : Type} (f : A -> B) xs (da : A) (db : B) i,
    0 <= i < Zlength xs ->
    Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma initialized_slice_pointwise__solve_base_exits :
  forall cells lo hi values (d : option Z),
    0 <= lo <= hi -> hi <= Zlength cells ->
    InitializedSlice cells lo hi values ->
    forall k, lo <= k < hi ->
      Znth k cells d = Some (Znth (k - lo) values 0).
Proof.
  intros cells lo hi values d Hrange Hhi Hinit k Hk.
  unfold InitializedSlice in Hinit.
  assert (Hj : 0 <= k - lo < Zlength (sublist lo hi cells)).
  { rewrite Zlength_sublist by lia. lia. }
  pose proof (f_equal (fun xs => Znth (k - lo) xs d) Hinit) as Hnth.
  cbn beta in Hnth.
  rewrite Znth_sublist in Hnth by lia.
  rewrite (Znth_map__solve_base_exits (@Some Z) values 0 d (k - lo)) in Hnth by
    (rewrite Zlength_correct,
       <- (@length_map Z (option Z) (@Some Z) values), <- Zlength_correct;
     rewrite <- Hinit, Zlength_sublist by lia; lia).
  replace (k - lo + lo) with k in Hnth by lia.
  exact Hnth.
Qed.
Lemma partition_copy_back_init__solve_base_exits :
  forall before scratch l r bit p d,
    0 <= l <= r -> r <= Zlength before ->
    Zlength scratch = Zlength before -> p = r ->
    StablePartitionPrefix before scratch l r bit r p 1 ->
    let partitioned :=
      filter (BitIs bit 0) (sublist l r before) ++
      filter (BitIs bit 1) (sublist l r before) in
    Zlength partitioned = r - l /\
    (forall k, l <= k < r ->
      Znth k scratch d = Some (Znth (k - l) partitioned 0)) /\
    PartitionCopyBack before before partitioned l r l.
Proof.
  intros before scratch l r bit p d Hlr Hr Hscratch Hp Hstable.
  cbn zeta.
  assert (Hpartlen :
    Zlength (filter (BitIs bit 0) (sublist l r before) ++
      filter (BitIs bit 1) (sublist l r before)) = r - l).
  { rewrite filter_bit_partition_length__solve_base_exits.
    rewrite Zlength_sublist by lia. lia. }
  assert (Hinit : InitializedSlice scratch l r
    (filter (BitIs bit 0) (sublist l r before) ++
     filter (BitIs bit 1) (sublist l r before))).
  { unfold StablePartitionPrefix in Hstable.
    destruct Hstable as [[Hbad _] | [_ Hgood]]; [lia |].
    subst p. exact Hgood. }
  split; [exact Hpartlen |].
  split.
  - eapply initialized_slice_pointwise__solve_base_exits; eauto. lia.
  - unfold PartitionCopyBack.
    split; [reflexivity |].
    split; [exact Hpartlen |].
    split; [reflexivity |].
    split.
    + rewrite !Zsublist_nil by lia. reflexivity.
    + split; [reflexivity |].
      apply filter_bit_partition_permutation__solve_base_exits.
Qed.
Lemma partition_copy_back_extend__solve_base_exits :
  forall before current partitioned l r i value,
    0 <= l <= i -> i < r -> r <= Zlength current ->
    value = Znth (i - l) partitioned 0 ->
    PartitionCopyBack before current partitioned l r i ->
    PartitionCopyBack before (replace_Znth i value current)
      partitioned l r (i + 1).
Proof.
  intros before current partitioned l r i value Hli Hir Hr Hvalue Hcopy.
  unfold PartitionCopyBack in *.
  destruct Hcopy as [Hlen [Hplen [Hpre [Hseg [Hpost Hperm]]]]].
  repeat split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - exact Hplen.
  - rewrite <- Hpre.
    apply (proj2 (list_eq_ext _ _ 0)). split.
    + rewrite !Zlength_sublist0; try rewrite Zlength_replace_Znth; lia.
    + intros k Hk. rewrite Zlength_sublist0 in Hk by
        (rewrite Zlength_replace_Znth; lia).
      rewrite !Znth_sublist0 by (try rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia. reflexivity.
  - rewrite (sublist_split l (i + 1) i (replace_Znth i value current)) by
      (try rewrite Zlength_replace_Znth; lia).
    rewrite (sublist_single 0 i (replace_Znth i value current)) by
      (rewrite Zlength_replace_Znth; lia).
    assert (Hprefix : sublist l i (replace_Znth i value current) =
      sublist l i current).
    { apply (proj2 (list_eq_ext _ _ 0)). split.
      - rewrite !Zlength_sublist; try rewrite Zlength_replace_Znth; lia.
      - intros k Hk. rewrite Zlength_sublist in Hk by
          (rewrite Zlength_replace_Znth; lia).
        rewrite !Znth_sublist by lia.
        rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
    rewrite Hprefix, Znth_replace_Znth_Same by lia.
    replace (i + 1 - l) with (i - l + 1) by lia.
    rewrite (sublist_split 0 (i - l + 1) (i - l) partitioned) by lia.
    rewrite (sublist_single 0 (i - l) partitioned) by lia.
    rewrite Hseg, Hvalue. reflexivity.
  - apply (proj2 (list_eq_ext _ _ 0)). split.
    + rewrite !Zlength_sublist; try rewrite Zlength_replace_Znth; lia.
    + intros k Hk. rewrite Zlength_sublist in Hk by
        (rewrite Zlength_replace_Znth; lia).
      rewrite !Znth_sublist by lia.
      rewrite Znth_replace_Znth_Diff by lia.
      pose proof (f_equal (fun xs => Znth (k + 1) xs 0) Hpost) as Hkpost.
      cbn beta in Hkpost.
      rewrite !Znth_sublist in Hkpost by lia.
      replace (k + 1 + i) with (k + (i + 1)) in Hkpost by lia.
      exact Hkpost.
  - exact Hperm.
Qed.
Lemma cost_bound_monotone__solve_base_exits :
  forall costs old_limit new_limit,
    CostBound costs old_limit -> old_limit <= new_limit ->
    CostBound costs new_limit.
Proof.
  intros costs old_limit new_limit Hbound Hle.
  unfold CostBound in *.
  destruct Hbound as [Hold_nonneg [Hlen Hcells]].
  split; [lia | split; [exact Hlen |]].
  intros bit choice Hbit Hchoice.
  specialize (Hcells bit choice Hbit Hchoice).
  lia.
Qed.
Lemma replace_Znth_value_bounds__solve_base_exits :
  forall xs i value n,
    Zlength xs = n -> 0 <= i < n -> 0 <= value <= 1000000000 ->
    (forall k, 0 <= k < n -> 0 <= Znth k xs 0 <= 1000000000) ->
    forall k, 0 <= k < n ->
      0 <= Znth k (replace_Znth i value xs) 0 <= 1000000000.
Proof.
  intros xs i value n Hlen Hi Hvalue Hall k Hk.
  destruct (Z.eq_dec k i) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by lia. exact Hvalue.
  - rewrite Znth_replace_Znth_Diff by lia. apply Hall. exact Hk.
Qed.
Lemma cost_bound_row_shape_nonnegative__solve_base_exits :
  forall costs limit d,
    Zlength costs = 30 ->
    (forall b, 0 <= b < 30 -> Zlength (Znth b costs nil) = 2) ->
    CostBound costs limit ->
    forall b, 0 <= b < 30 ->
      (Zlength (Znth b costs d) = 2 /\
       0 <= Znth 0 (Znth b costs d) 0) /\
      0 <= Znth 1 (Znth b costs d) 0.
Proof.
  intros costs limit d Hlen Hrows Hbound b Hb.
  rewrite (Znth_indep costs b d nil) by lia.
  unfold CostBound in Hbound.
  destruct Hbound as [_ [_ Hcells]].
  specialize (Hrows b Hb).
  specialize (Hcells b 0 Hb ltac:(lia)) as Hzero.
  specialize (Hcells b 1 Hb ltac:(lia)) as Hone.
  unfold CostAt in Hzero, Hone.
  tauto.
Qed.
Lemma In_Znth_Zlength__solve_base_exits :
  forall (A : Type) (xs : list A) (x d : A),
    In x xs ->
    exists k, 0 <= k < Zlength xs /\ Znth k xs d = x.
Proof.
  intros A xs x d Hin.
  apply In_nth with (d := d) in Hin as [n [Hn Hnth]].
  exists (Z.of_nat n). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma partition_values_bound__solve_base_exits :
  forall before l r bit partitioned,
    0 <= l <= r -> r <= Zlength before ->
    partitioned =
      filter (BitIs bit 0) (sublist l r before) ++
      filter (BitIs bit 1) (sublist l r before) ->
    (forall k, 0 <= k < Zlength before ->
      0 <= Znth k before 0 <= 1000000000) ->
    forall k, 0 <= k < Zlength partitioned ->
      0 <= Znth k partitioned 0 <= 1000000000.
Proof.
  intros before l r bit partitioned Hlr Hr -> Hall k Hk.
  set (part :=
    filter (BitIs bit 0) (sublist l r before) ++
    filter (BitIs bit 1) (sublist l r before)).
  assert (Hinpart : In (Znth k part 0) part).
  { apply Znth_In_Zlength. exact Hk. }
  assert (Hinseg : In (Znth k part 0) (sublist l r before)).
  { eapply Permutation_in.
    - symmetry. apply filter_bit_partition_permutation__solve_base_exits.
    - exact Hinpart. }
  destruct (In_Znth_Zlength__solve_base_exits
    Z (sublist l r before) (Znth k part 0) 0 Hinseg)
    as [q [Hq Hvalue]].
  rewrite Zlength_sublist in Hq by lia.
  rewrite Znth_sublist in Hvalue by lia.
  rewrite <- Hvalue. apply Hall. lia.
Qed.
Lemma stable_partition_complete_write_end__solve_base_exits :
  forall before scratch l r bit p,
    0 <= l <= p -> p <= r -> r <= Zlength scratch ->
    r <= Zlength before ->
    StablePartitionPrefix before scratch l r bit r p 1 ->
    p = r.
Proof.
  intros before scratch l r bit p Hlp Hpr Hr Hbefore Hstable.
  unfold StablePartitionPrefix in Hstable.
  destruct Hstable as [[Hbad _] | [_ Hinit]]; [lia |].
  unfold InitializedSlice in Hinit.
  pose proof (f_equal (@length (option Z)) Hinit) as Hlen.
  rewrite sublist_length in Hlen by lia.
  rewrite length_map in Hlen.
  assert (Hpart :
    Zlength
      (filter (BitIs bit 0) (sublist l r before) ++
       filter (BitIs bit 1) (sublist l r before)) = r - l).
  { rewrite filter_bit_partition_length__solve_base_exits.
    rewrite Zlength_sublist by lia. lia. }
  rewrite !Zlength_correct in Hpart.
  lia.
Qed.
Lemma selected_indices_function__solve_recursive :
  { f : (Z -> bool) -> list Z -> Z -> list Z | True }.
Proof.
  refine (exist _
    (fix go (test : Z -> bool) (xs : list Z) (base : Z) {struct xs} : list Z :=
      match xs with
      | nil => nil
      | x :: tl =>
          if test x
          then base :: go test tl (base + 1)
          else go test tl (base + 1)
      end) I).
Defined.
Lemma square_partition_budget__solve_recursive :
  forall capacity bit l mid r,
    0 <= bit -> l <= mid -> mid <= r ->
    ((capacity + (r - l) * (r - l)) +
       bit * (mid - l) * (mid - l)) +
       bit * (r - mid) * (r - mid) <=
    capacity + (bit + 1) * (r - l) * (r - l).
Proof.
  intros capacity bit l mid r Hbit Hlm Hmr.
  assert ((mid - l) * (mid - l) + (r - mid) * (r - mid) <=
          (r - l) * (r - l)) by nia.
  nia.
Qed.
Lemma selected_indices_function_cons__solve_recursive :
  forall test x xs base,
    proj1_sig selected_indices_function__solve_recursive test (x :: xs) base =
    if test x
    then base :: proj1_sig selected_indices_function__solve_recursive
      test xs (base + 1)
    else proj1_sig selected_indices_function__solve_recursive
      test xs (base + 1).
Proof.
  intros. unfold selected_indices_function__solve_recursive. reflexivity.
Qed.
Lemma selected_indices_length__solve_recursive :
  forall test xs base,
    Zlength (proj1_sig selected_indices_function__solve_recursive test xs base) =
    Zlength (filter test xs).
Proof.
  intros test xs; induction xs as [|x xs IH]; intros base; simpl.
  - reflexivity.
  - destruct (test x); simpl.
    + rewrite !Zlength_cons, IH. reflexivity.
    + apply IH.
Qed.
Lemma Znth_map__solve_recursive :
  forall {A B : Type} (f : A -> B) xs (da : A) (db : B) i,
    0 <= i < Zlength xs ->
    Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma map_Some_injective__solve_recursive :
  forall {A : Type} (xs ys : list A),
    map (@Some A) xs = map (@Some A) ys -> xs = ys.
Proof.
  intros A xs. induction xs as [|x xs IH]; intros [|y ys] H; simpl in H;
    try discriminate; [reflexivity|].
  inversion H. f_equal. apply IH. assumption.
Qed.
Lemma initialized_slice_from_pointwise__solve_recursive :
  forall cells lo hi values (d : option Z),
    0 <= lo <= hi -> hi <= Zlength cells ->
    Zlength values = hi - lo ->
    (forall k, lo <= k < hi ->
      Znth k cells d = Some (Znth (k - lo) values 0)) ->
    InitializedSlice cells lo hi values.
Proof.
  intros cells lo hi values d Hrange Hhi Hlen Hpoint.
  unfold InitializedSlice.
  apply (proj2 (list_eq_ext _ _ d)). split.
  - rewrite Zlength_sublist by lia.
    rewrite Zlength_correct, map_length, <- Zlength_correct. lia.
  - intros j Hj.
    rewrite Zlength_sublist in Hj by lia.
    rewrite Znth_sublist by lia.
    rewrite (Znth_map__solve_recursive (@Some Z) values 0 d j) by lia.
    specialize (Hpoint (j + lo) ltac:(lia)).
    replace (j + lo - lo) with j in Hpoint by lia.
    exact Hpoint.
Qed.
Lemma materialized_stable_partition__solve_recursive :
  forall before scratch partitioned l r bit p (d : option Z),
    0 <= l <= r -> r <= Zlength scratch ->
    Zlength partitioned = r - l ->
    (forall k, l <= k < r ->
      Znth k scratch d = Some (Znth (k - l) partitioned 0)) ->
    StablePartitionPrefix before scratch l r bit r p 1 ->
    p = r ->
    partitioned =
      filter (BitIs bit 0) (sublist l r before) ++
      filter (BitIs bit 1) (sublist l r before).
Proof.
  intros before scratch partitioned l r bit p d Hrange Hscratch Hlen
    Hpoint Hstable Hp.
  assert (Hmat : InitializedSlice scratch l r partitioned).
  { eapply initialized_slice_from_pointwise__solve_recursive; eauto. }
  unfold StablePartitionPrefix in Hstable.
  destruct Hstable as [[Hbad _] | [_ Hstable]]; [lia|].
  subst p. unfold InitializedSlice in Hmat, Hstable.
  apply map_Some_injective__solve_recursive.
  rewrite <- Hmat, <- Hstable. reflexivity.
Qed.
Lemma selected_indices_bounds__solve_recursive :
  forall test xs base i,
    In i (proj1_sig selected_indices_function__solve_recursive test xs base) ->
    base <= i < base + Zlength xs.
Proof.
  intros test xs; induction xs as [|x xs IH]; intros base i Hin; simpl in Hin.
  - contradiction.
  - destruct (test x) eqn:Hx; simpl in Hin.
    + destruct Hin as [<- | Hin].
      * rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
      * specialize (IH (base + 1) i Hin).
        rewrite Zlength_cons. lia.
    + specialize (IH (base + 1) i Hin).
      rewrite Zlength_cons. lia.
Qed.
Lemma selected_indices_member__solve_recursive :
  forall test xs base i,
    In i (proj1_sig selected_indices_function__solve_recursive test xs base) <->
    base <= i < base + Zlength xs /\
    test (Znth (i - base) xs 0) = true.
Proof.
  intros test xs; induction xs as [|x xs IH]; intros base i; simpl.
  - rewrite Zlength_nil. split; [contradiction | lia].
  - destruct (test x) eqn:Hx; simpl.
    + rewrite IH. rewrite Zlength_cons. split.
      * intros [<- | [[Hlo Hhi] Htest]].
        -- split; [pose proof (Zlength_nonneg xs); lia |].
           replace (base - base) with 0 by lia. rewrite Znth0_cons. exact Hx.
        -- split; [lia |].
           rewrite Znth_cons by lia.
           replace (i - base - 1) with (i - (base + 1)) by lia.
           exact Htest.
      * intros [[Hlo Hhi] Htest].
        destruct (Z.eq_dec i base) as [-> | Hneq]; [left; reflexivity | right].
        split; [lia |].
        rewrite Znth_cons in Htest by lia.
        replace (i - base - 1) with (i - (base + 1)) in Htest by lia.
        exact Htest.
    + rewrite IH. rewrite Zlength_cons. split.
      * intros [[Hlo Hhi] Htest]. split; [lia |].
        rewrite Znth_cons by lia.
        replace (i - base - 1) with (i - (base + 1)) by lia.
        exact Htest.
      * intros [[Hlo Hhi] Htest].
        assert (i <> base).
        { intro Heq. subst i. replace (base - base) with 0 in Htest by lia.
          rewrite Znth0_cons in Htest. congruence. }
        split; [lia |].
        rewrite Znth_cons in Htest by lia.
        replace (i - base - 1) with (i - (base + 1)) in Htest by lia.
        exact Htest.
Qed.
Lemma selected_indices_monotone__solve_recursive :
  forall test xs base,
    mono_inc
      (proj1_sig selected_indices_function__solve_recursive test xs base).
Proof.
  intros test xs; induction xs as [|x xs IH]; intros base; simpl.
  - apply mono_inc_nil.
  - destruct (test x) eqn:Hx.
    + apply (proj2 (mono_inc_cons base _)). split.
      * apply Forall_forall. intros y Hy.
        pose proof (selected_indices_bounds__solve_recursive
          test xs (base + 1) y Hy). lia.
      * apply IH.
    + apply IH.
Qed.
Lemma selected_indices_from_value__solve_recursive :
  forall test xs base j,
    0 <= j < Zlength (filter test xs) ->
    Znth j (filter test xs) 0 =
    Znth (Znth j (proj1_sig selected_indices_function__solve_recursive test xs base) 0 - base)
      xs 0.
Proof.
  intros test xs; induction xs as [|x xs IH]; intros base j Hj;
    cbn [selected_indices_function__solve_recursive] in *.
  - rewrite Zlength_nil in Hj. lia.
  - destruct (test x) eqn:Hx;
      cbn [selected_indices_function__solve_recursive] in *.
    + destruct (Z.eq_dec j 0) as [-> | Hj0].
      * unfold filter at 1. rewrite Hx, Znth0_cons.
        rewrite selected_indices_function_cons__solve_recursive, Hx.
        rewrite !Znth0_cons.
        replace (base - base) with 0 by lia. rewrite Znth0_cons. reflexivity.
      * set (tailinds :=
          proj1_sig selected_indices_function__solve_recursive test xs (base + 1)).
        unfold filter at 1. rewrite Hx, Znth_cons by lia.
        rewrite selected_indices_function_cons__solve_recursive, Hx.
        fold tailinds.
        rewrite (Znth_cons 0 j base tailinds) by lia.
        assert (Hfilterlen :
          Zlength (filter test (x :: xs)) =
          1 + Zlength (filter test xs)).
        { change (Zlength
            (if test x then x :: filter test xs else filter test xs) =
            1 + Zlength (filter test xs)).
          rewrite Hx, Zlength_cons. lia. }
        specialize (IH (base + 1) (j - 1) ltac:(lia)).
        assert (Hin : In (Znth (j - 1) tailinds 0) tailinds).
        { unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
          rewrite Z2Nat.id by lia. rewrite <- Zlength_correct.
          unfold tailinds. rewrite selected_indices_length__solve_recursive. lia. }
        pose proof (selected_indices_bounds__solve_recursive
          test xs (base + 1) (Znth (j - 1) tailinds 0) Hin) as Hbound.
        rewrite (Znth_cons 0 (Znth (j - 1) tailinds 0 - base) x xs)
          by lia.
        replace
          (Znth (j - 1) tailinds 0 - base - 1)
          with
          (Znth (j - 1) tailinds 0 - (base + 1)) by lia.
        unfold tailinds.
        exact IH.
    + assert (Hfilter : filter test (x :: xs) = filter test xs).
      { simpl. rewrite Hx. reflexivity. }
      rewrite Hfilter in Hj |- *.
      set (tailinds :=
        proj1_sig selected_indices_function__solve_recursive test xs (base + 1)).
      rewrite selected_indices_function_cons__solve_recursive, Hx.
      fold tailinds.
      assert (Hin : In (Znth j tailinds 0) tailinds).
      { unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
        rewrite Z2Nat.id by lia. rewrite <- Zlength_correct.
        unfold tailinds. rewrite selected_indices_length__solve_recursive. lia. }
      pose proof (selected_indices_bounds__solve_recursive
        test xs (base + 1) (Znth j tailinds 0) Hin) as Hbound.
      rewrite (Znth_cons 0 (Znth j tailinds 0 - base) x xs) by lia.
      specialize (IH (base + 1) j Hj).
      replace
        (Znth j tailinds 0 - base - 1)
        with
        (Znth j tailinds 0 - (base + 1)) by lia.
      unfold tailinds.
      exact IH.
Qed.
Lemma selected_indices_value__solve_recursive :
  forall test xs j,
    0 <= j < Zlength (filter test xs) ->
    Znth j (filter test xs) 0 =
    Znth (Znth j (proj1_sig selected_indices_function__solve_recursive test xs 0) 0) xs 0.
Proof.
  intros test xs j Hj.
  unfold selected_indices_function__solve_recursive.
  pose proof (selected_indices_from_value__solve_recursive test xs 0 j Hj).
  replace
    (Znth j (proj1_sig selected_indices_function__solve_recursive test xs 0) 0 - 0)
    with (Znth j (proj1_sig selected_indices_function__solve_recursive test xs 0) 0)
    in H by lia.
  exact H.
Qed.
Lemma selected_index_at__solve_recursive :
  forall test xs j,
    0 <= j < Zlength (filter test xs) ->
    0 <= Znth j (proj1_sig selected_indices_function__solve_recursive test xs 0) 0 < Zlength xs /\
    test (Znth (Znth j (proj1_sig selected_indices_function__solve_recursive test xs 0) 0) xs 0) = true.
Proof.
  intros test xs j Hj.
  assert (Hin : In (Znth j (proj1_sig selected_indices_function__solve_recursive test xs 0) 0)
    (proj1_sig selected_indices_function__solve_recursive test xs 0)).
  { unfold Znth. apply nth_In. apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia. rewrite <- Zlength_correct.
    unfold selected_indices_function__solve_recursive.
    rewrite selected_indices_length__solve_recursive. exact (proj2 Hj). }
  apply (proj1 (selected_indices_member__solve_recursive test xs 0 _)) in Hin.
  replace
    (Znth j (proj1_sig selected_indices_function__solve_recursive test xs 0) 0 - 0)
    with (Znth j (proj1_sig selected_indices_function__solve_recursive test xs 0) 0)
    in Hin by lia.
  exact Hin.
Qed.
Lemma selected_index_surjective__solve_recursive :
  forall test xs i,
    0 <= i < Zlength xs ->
    test (Znth i xs 0) = true ->
    exists j,
      0 <= j < Zlength (filter test xs) /\
      Znth j (proj1_sig selected_indices_function__solve_recursive test xs 0) 0 = i.
Proof.
  intros test xs i Hi Htest.
  assert (Hin : In i (proj1_sig selected_indices_function__solve_recursive test xs 0)).
  { unfold selected_indices_function__solve_recursive.
    apply (proj2 (selected_indices_member__solve_recursive test xs 0 i)).
    replace (i - 0) with i by lia. auto. }
  destruct (In_nth (proj1_sig selected_indices_function__solve_recursive test xs 0) i 0 Hin)
    as [n [Hn Hnth]].
  exists (Z.of_nat n). split.
  - split; [lia |].
    assert (Hnz : Z.of_nat n <
      Zlength (proj1_sig selected_indices_function__solve_recursive test xs 0)).
    { rewrite Zlength_correct. lia. }
    unfold selected_indices_function__solve_recursive in Hnz.
    rewrite selected_indices_length__solve_recursive in Hnz. exact Hnz.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma set_card_as_Zlength_enum__solve_recursive :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    @set_card A P FP = Zlength (@enum A P FP).
Proof.
  intros A P FP. unfold set_card, SumLib.Sum.sum.
  rewrite Zlength_correct.
  assert (Hfold : forall xs : list A,
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
    Z.of_nat (List.length xs)).
  { intros xs. induction xs as [|x xs IH].
    - reflexivity.
    - change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
        Z.of_nat (S (List.length xs))).
      rewrite IH, Nat2Z.inj_succ. lia. }
  apply Hfold.
Qed.
Lemma set_card_bijection__solve_recursive :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q) (f : A -> B),
    (forall x, P x -> Q (f x)) ->
    (forall y, Q y -> exists x, P x /\ f x = y) ->
    (forall x y, P x -> P y -> f x = f y -> x = y) ->
    @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f Hmap Hsurj Hinj.
  rewrite !set_card_as_Zlength_enum__solve_recursive.
  rewrite !Zlength_correct. f_equal.
  rewrite <- map_length with (f := f) (l := @enum A P FP).
  apply Permutation_length, NoDup_Permutation.
  - apply Injective_map_NoDup_in.
    + intros x y Hx Hy Hxy. apply Hinj.
      * apply (proj2 (@enum_ok A P FP x)); exact Hx.
      * apply (proj2 (@enum_ok A P FP y)); exact Hy.
      * exact Hxy.
    + exact (@enum_nodup A P FP).
  - exact (@enum_nodup B Q FQ).
  - intro y. rewrite in_map_iff, <- (@enum_ok B Q FQ y). split.
    + intros [x [<- Hx]]. apply Hmap.
      apply (proj2 (@enum_ok A P FP x)); exact Hx.
    + intro Hy. destruct (Hsurj y Hy) as [x [Hx Hxy]].
      exists x. split; [exact Hxy |].
      apply (proj1 (@enum_ok A P FP x)); exact Hx.
Qed.
Lemma set_card_disjoint_union__solve_recursive :
  forall {A : Type} (R P Q : A -> Prop)
      (FR : Finite R) (FP : Finite P) (FQ : Finite Q),
    (forall x, R x <-> P x \/ Q x) ->
    (forall x, ~ (P x /\ Q x)) ->
    @set_card A R FR = @set_card A P FP + @set_card A Q FQ.
Proof.
  intros A R P Q FR FP FQ Hunion Hdisjoint.
  rewrite !set_card_as_Zlength_enum__solve_recursive.
  rewrite !Zlength_correct, <- Nat2Z.inj_add. f_equal.
  rewrite <- length_app. apply Permutation_length, NoDup_Permutation.
  - exact (@enum_nodup A R FR).
  - apply NoDup_app. repeat split.
    + exact (@enum_nodup A P FP).
    + exact (@enum_nodup A Q FQ).
    + intros x HxP HxQ. apply (Hdisjoint x). split.
      * apply (proj2 (@enum_ok A P FP x)); exact HxP.
      * apply (proj2 (@enum_ok A Q FQ x)); exact HxQ.
  - intro x. rewrite in_app_iff.
    rewrite <- (@enum_ok A R FR x), <- (@enum_ok A P FP x),
      <- (@enum_ok A Q FQ x). apply Hunion.
Qed.
Lemma bit_at_binary__solve_recursive :
  forall value bit, BitAt value bit = 0 \/ BitAt value bit = 1.
Proof.
  intros value bit. unfold BitAt.
  change (Z.land (Z.shiftr value bit) (Z.ones 1) = 0 \/
          Z.land (Z.shiftr value bit) (Z.ones 1) = 1).
  rewrite Z.land_ones by lia.
  destruct (Z.mod_pos_bound (Z.shiftr value bit) 2 ltac:(lia)) as [Hlo Hhi].
  destruct (Z.lt_trichotomy (Z.shiftr value bit mod 2) 1)
    as [Hlt | [Heq | Hgt]].
  - left. apply Z.le_antisymm.
    + apply (proj1 (Z.lt_succ_r _ 0)). exact Hlt.
    + exact Hlo.
  - right. exact Heq.
  - exfalso.
    pose proof (proj1 (Z.lt_succ_r _ 1) Hhi) as Hle.
    exact (Z.lt_irrefl 1 (Z.lt_le_trans _ _ _ Hgt Hle)).
Qed.
Lemma bit_is_true__solve_recursive :
  forall bit choice value,
    BitIs bit choice value = true <-> BitAt value bit = choice.
Proof.
  intros. unfold BitIs. apply Z.eqb_eq.
Qed.
Lemma contribution_pred_function__solve_recursive :
  { pred : list Z -> Z -> Z -> Z -> Z * Z -> Prop | True }.
Proof.
  refine (exist _ (fun segment upper bit choice p =>
    (0 <= fst p < Zlength segment /\ 0 <= snd p < Zlength segment) /\
    fst p < snd p /\
    SameHigherBits segment upper bit (fst p) (snd p) /\
    ((choice = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                    BitAt (Znth (snd p) segment 0) bit = 0) \/
     (choice = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                    BitAt (Znth (snd p) segment 0) bit = 1))) I).
Defined.
Lemma contribution_at_function__solve_recursive :
  { pred : list Z -> Z -> Z -> Z -> Z -> Z * Z -> Prop | True }.
Proof.
  refine (exist _ (fun segment upper bit choice class p =>
    proj1_sig contribution_pred_function__solve_recursive
      segment upper bit choice p /\
    BitAt (Znth (fst p) segment 0) upper = class) I).
Defined.
Lemma contribution_filter_bijection__solve_recursive :
  forall segment upper bit choice class,
    bit < upper ->
    (class = 0 \/ class = 1) ->
    #(proj1_sig contribution_pred_function__solve_recursive
        (filter (BitIs upper class) segment) (upper - 1) bit choice) =
    #(proj1_sig contribution_at_function__solve_recursive segment upper bit choice class).
Proof.
  intros segment upper bit choice class Hbit Hclass.
  set (test := BitIs upper class).
  set (inds := proj1_sig selected_indices_function__solve_recursive test segment 0).
  set (f := fun q : Z * Z =>
    (Znth (fst q) inds 0, Znth (snd q) inds 0)).
  eapply set_card_bijection__solve_recursive with (f := f).
  - intros [u v] Hq. unfold contribution_pred_function__solve_recursive in Hq.
    unfold contribution_at_function__solve_recursive,
      contribution_pred_function__solve_recursive.
    cbn [fst snd] in Hq |- *.
    destruct Hq as [[[Hu0 Hu1] [Hv0 Hv1]] [Huv [Hhigh Hdir]]].
    assert (Hlen : Zlength inds = Zlength (filter test segment)).
    { unfold inds.
      apply selected_indices_length__solve_recursive. }
    unfold test in Hlen.
    assert (Hiu := selected_index_at__solve_recursive test segment u
      ltac:(unfold test; exact (conj Hu0 Hu1))).
    assert (Hiv := selected_index_at__solve_recursive test segment v
      ltac:(unfold test; exact (conj Hv0 Hv1))).
    destruct Hiu as [Hiu Hitestu]. destruct Hiv as [Hiv Hitestv].
    assert (Hvalu := selected_indices_value__solve_recursive test segment u
      ltac:(unfold test; exact (conj Hu0 Hu1))).
    assert (Hvalv := selected_indices_value__solve_recursive test segment v
      ltac:(unfold test; exact (conj Hv0 Hv1))).
    assert (Hmono := selected_indices_monotone__solve_recursive test segment 0).
    unfold inds in Hmono.
    unfold mono_inc in Hmono.
    assert (Hord : Znth u inds 0 < Znth v inds 0).
    { unfold inds. apply Hmono.
      - exact Hu0.
      - exact Huv.
      - rewrite selected_indices_length__solve_recursive.
        unfold test. exact Hv1. }
    unfold f. cbn [fst snd].
    fold inds in Hitestu, Hitestv, Hvalu, Hvalv.
    split.
    + split.
      * split; assumption.
      * split; [exact Hord |]. split.
        -- intros k Hk.
           destruct (Z.eq_dec k upper) as [-> | Hneq].
           ++ apply bit_is_true__solve_recursive in Hitestu.
              apply bit_is_true__solve_recursive in Hitestv.
              unfold test in Hitestu, Hitestv.
              transitivity class.
              ** exact Hitestu.
              ** symmetry. exact Hitestv.
           ++ specialize (Hhigh k ltac:(lia)).
              fold test in Hhigh.
              cbn [fst snd] in Hhigh |- *.
              rewrite Hvalu, Hvalv in Hhigh. exact Hhigh.
        -- fold test in Hdir. cbn [fst snd] in Hdir |- *.
           rewrite Hvalu, Hvalv in Hdir. exact Hdir.
    + apply bit_is_true__solve_recursive in Hitestu.
      unfold test in Hitestu. exact Hitestu.
  - intros [i j] Hy. unfold contribution_at_function__solve_recursive in Hy.
    destruct Hy as [Hy Hclassi].
    unfold contribution_pred_function__solve_recursive in Hy.
    cbn [fst snd] in Hy, Hclassi |- *.
    destruct Hy as [[[Hi0 Hi1] [Hj0 Hj1]] [Hij [Hhigh Hdir]]].
    cbn [fst snd] in Hi0, Hi1, Hj0, Hj1, Hij, Hhigh, Hdir.
    assert (Hclassj : BitAt (Znth j segment 0) upper = class).
    { specialize (Hhigh upper ltac:(lia)). rewrite <- Hhigh. exact Hclassi. }
    assert (Htesti : test (Znth i segment 0) = true).
    { unfold test. apply bit_is_true__solve_recursive. exact Hclassi. }
    assert (Htestj : test (Znth j segment 0) = true).
    { unfold test. apply bit_is_true__solve_recursive. exact Hclassj. }
    destruct (selected_index_surjective__solve_recursive test segment i
      ltac:(exact (conj Hi0 Hi1)) Htesti) as [u [Hu Hui]].
    destruct (selected_index_surjective__solve_recursive test segment j
      ltac:(exact (conj Hj0 Hj1)) Htestj) as [v [Hv HVj]].
    exists (u, v). split.
    + unfold contribution_pred_function__solve_recursive. cbn [fst snd].
      assert (Hvalu := selected_indices_value__solve_recursive test segment u Hu).
      assert (Hvalv := selected_indices_value__solve_recursive test segment v Hv).
      assert (Hmono := selected_indices_monotone__solve_recursive test segment 0).
      unfold mono_inc in Hmono.
      assert (Huv : u < v).
      { destruct (Z.lt_trichotomy u v) as [Hlt | [Heq | Hgt]]; [exact Hlt | |].
        - subst v. lia.
        - assert (Hulen :
              u < Zlength (proj1_sig selected_indices_function__solve_recursive test segment 0)).
          { rewrite selected_indices_length__solve_recursive. exact (proj2 Hu). }
          pose proof (Hmono v u (proj1 Hv) Hgt Hulen).
          unfold inds in Hui, HVj.
          rewrite Hui, HVj in H. lia. }
      split.
      * split; [exact Hu | exact Hv].
      * split; [exact Huv |]. split.
        -- intros k Hk. specialize (Hhigh k ltac:(lia)).
           unfold test in Hvalu, Hvalv, Hui, HVj |- *.
           cbn [fst snd].
           rewrite Hvalu, Hvalv, Hui, HVj. exact Hhigh.
        -- unfold test in Hvalu, Hvalv, Hui, HVj |- *.
           cbn [fst snd].
           rewrite Hvalu, Hvalv, Hui, HVj. exact Hdir.
    + unfold f, inds. cbn [fst snd]. rewrite Hui, HVj. reflexivity.
  - intros [u1 v1] [u2 v2] Hu Hv Hf.
    unfold f in Hf. cbn [fst snd] in Hf.
    unfold contribution_pred_function__solve_recursive in Hu, Hv.
    cbn [fst snd] in Hu, Hv.
    destruct Hu as [[[Hu10 Hu11] [Hv10 Hv11]] _].
    destruct Hv as [[[Hu20 Hu21] [Hv20 Hv21]] _].
    injection Hf as HEu HEv. f_equal.
    + destruct (Z.lt_trichotomy u1 u2) as [Hlt | [Heq | Hgt]]; [|exact Heq|].
      * assert (Hmono := selected_indices_monotone__solve_recursive test segment 0).
        unfold mono_inc in Hmono.
        assert (Hlen : u2 < Zlength (proj1_sig selected_indices_function__solve_recursive test segment 0)).
        { rewrite selected_indices_length__solve_recursive. exact Hu21. }
        pose proof (Hmono u1 u2 Hu10 Hlt Hlen).
        unfold inds in HEu.
        lia.
      * assert (Hmono := selected_indices_monotone__solve_recursive test segment 0).
        unfold mono_inc in Hmono.
        assert (Hlen : u1 < Zlength (proj1_sig selected_indices_function__solve_recursive test segment 0)).
        { rewrite selected_indices_length__solve_recursive. exact Hu11. }
        pose proof (Hmono u2 u1 Hu20 Hgt Hlen).
        unfold inds in HEu. lia.
    + destruct (Z.lt_trichotomy v1 v2) as [Hlt | [Heq | Hgt]]; [|exact Heq|].
      * assert (Hmono := selected_indices_monotone__solve_recursive test segment 0).
        unfold mono_inc in Hmono.
        assert (Hlen : v2 < Zlength (proj1_sig selected_indices_function__solve_recursive test segment 0)).
        { rewrite selected_indices_length__solve_recursive. exact Hv21. }
        pose proof (Hmono v1 v2 Hv10 Hlt Hlen).
        unfold inds in HEv. lia.
      * assert (Hmono := selected_indices_monotone__solve_recursive test segment 0).
        unfold mono_inc in Hmono.
        assert (Hlen : v1 < Zlength (proj1_sig selected_indices_function__solve_recursive test segment 0)).
        { rewrite selected_indices_length__solve_recursive. exact Hv11. }
        pose proof (Hmono v2 v1 Hv20 Hgt Hlen).
        unfold inds in HEv. lia.
Qed.
Lemma bit_contribution_partition__solve_recursive :
  forall segment upper bit choice count0 count1,
    bit < upper ->
    BitContribution (filter (BitIs upper 0) segment)
      (upper - 1) bit choice count0 ->
    BitContribution (filter (BitIs upper 1) segment)
      (upper - 1) bit choice count1 ->
    BitContribution segment upper bit choice (count0 + count1).
Proof.
  intros segment upper bit choice count0 count1 Hbit Hcount0 Hcount1.
  change (count0 = #(proj1_sig contribution_pred_function__solve_recursive
    (filter (BitIs upper 0) segment) (upper - 1) bit choice)) in Hcount0.
  change (count1 = #(proj1_sig contribution_pred_function__solve_recursive
    (filter (BitIs upper 1) segment) (upper - 1) bit choice)) in Hcount1.
  change (count0 + count1 =
    #(proj1_sig contribution_pred_function__solve_recursive segment upper bit choice)).
  rewrite Hcount0, Hcount1.
  rewrite (contribution_filter_bijection__solve_recursive
    segment upper bit choice 0 Hbit (or_introl eq_refl)).
  rewrite (contribution_filter_bijection__solve_recursive
    segment upper bit choice 1 Hbit (or_intror eq_refl)).
  symmetry.
  eapply set_card_disjoint_union__solve_recursive.
  - intros [i j]. split.
    + intro HR. destruct (bit_at_binary__solve_recursive
        (Znth i segment 0) upper) as [Hz | Ho].
      * left. split; assumption.
      * right. split; assumption.
    + intros [[HR _] | [HR _]]; exact HR.
  - intros [i j] [[_ Hz] [_ Ho]]. congruence.
Qed.
Lemma selected_indices_injective__solve_recursive :
  forall test xs i j,
    0 <= i < Zlength (filter test xs) ->
    0 <= j < Zlength (filter test xs) ->
    Znth i (proj1_sig selected_indices_function__solve_recursive test xs 0) 0 =
    Znth j (proj1_sig selected_indices_function__solve_recursive test xs 0) 0 ->
    i = j.
Proof.
  intros test xs i j Hi Hj Heq.
  destruct (Z.lt_trichotomy i j) as [Hij | [Hij | Hij]]; [|exact Hij|].
  - assert (Hmono := selected_indices_monotone__solve_recursive test xs 0).
    unfold mono_inc in Hmono.
    assert (Hjlen :
      j < Zlength (proj1_sig selected_indices_function__solve_recursive test xs 0)).
    { rewrite selected_indices_length__solve_recursive. exact (proj2 Hj). }
    specialize (Hmono i j (proj1 Hi) Hij Hjlen).
    lia.
  - assert (Hmono := selected_indices_monotone__solve_recursive test xs 0).
    unfold mono_inc in Hmono.
    assert (Hilen :
      i < Zlength (proj1_sig selected_indices_function__solve_recursive test xs 0)).
    { rewrite selected_indices_length__solve_recursive. exact (proj2 Hi). }
    specialize (Hmono j i (proj1 Hj) Hij Hilen).
    lia.
Qed.
Lemma Zrange_aux_length__solve_recursive :
  forall low n, List.length (Zrange_aux low n) = n.
Proof.
  intros low n. revert low. induction n; intros; simpl; congruence.
Qed.
Lemma set_card_Z_range__solve_recursive :
  forall low high, low <= high ->
    @set_card Z (fun z : Z => low <= z < high) (finite_Z_range low high) =
    high - low.
Proof.
  intros low high Hrange.
  rewrite set_card_as_Zlength_enum__solve_recursive.
  rewrite Zlength_correct.
  cbn [finite_Z_range].
  change (Z.of_nat (List.length (Zrange low high)) = high - low).
  unfold Zrange.
  rewrite Zrange_aux_length__solve_recursive, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma set_card_bit_slice_filter__solve_recursive :
  forall before l r bit class,
    0 <= l -> l <= r -> r <= Zlength before ->
    #(fun k : Z =>
      l <= k < r /\ BitAt (Znth k before 0) bit = class) =
    Zlength (filter (BitIs bit class) (sublist l r before)).
Proof.
  intros before l r bit class Hl Hlr Hr.
  set (segment := sublist l r before).
  set (test := BitIs bit class).
  set (f := fun j : Z =>
    l + Znth j (proj1_sig selected_indices_function__solve_recursive test segment 0) 0).
  transitivity (#(fun j : Z =>
    0 <= j < Zlength (filter test segment))).
  - symmetry. eapply set_card_bijection__solve_recursive with (f := f).
    + intros j Hj. unfold f.
      destruct (selected_index_at__solve_recursive test segment j Hj)
        as [Hidx Htest].
      assert (Hseglen : Zlength segment = r - l).
      { unfold segment. apply Zlength_sublist. lia. }
      rewrite Hseglen in Hidx.
      split; [lia|].
      apply bit_is_true__solve_recursive in Htest.
      unfold test in Htest. unfold segment in Htest.
      rewrite Znth_sublist in Htest.
      2: exact Hl.
      2: exact Hidx.
      replace (l + Znth j (proj1_sig selected_indices_function__solve_recursive test segment 0) 0)
        with (Znth j (proj1_sig selected_indices_function__solve_recursive test segment 0) 0 + l)
        by lia.
      exact Htest.
    + intros k [Hk Hbit].
      assert (Hi : 0 <= k - l < Zlength segment).
      { unfold segment. rewrite Zlength_sublist by lia. lia. }
      assert (Htest : test (Znth (k - l) segment 0) = true).
      { unfold test, segment. apply bit_is_true__solve_recursive.
        rewrite Znth_sublist by lia.
        replace (k - l + l) with k by lia. exact Hbit. }
      destruct (selected_index_surjective__solve_recursive
        test segment (k - l) Hi Htest) as [j [Hj Hval]].
      exists j. split; [exact Hj|]. unfold f. rewrite Hval. lia.
    + intros i j Hi Hj Hij.
      unfold f in Hij.
      apply (selected_indices_injective__solve_recursive test segment i j Hi Hj).
      lia.
  - transitivity (@set_card Z
      (fun j : Z => 0 <= j < Zlength (filter test segment))
      (finite_Z_range 0 (Zlength (filter test segment)))).
    + eapply set_card_bijection__solve_recursive with (f := fun j : Z => j).
      * auto.
      * intros j Hj. exists j. auto.
      * intros i j Hi Hj Hij. exact Hij.
    + rewrite set_card_Z_range__solve_recursive.
      * lia.
      * apply Zlength_nonneg.
Qed.
Lemma filter_bit_lengths__solve_recursive :
  forall xs bit,
    Zlength (filter (BitIs bit 0) xs) +
    Zlength (filter (BitIs bit 1) xs) = Zlength xs.
Proof.
  intros xs bit. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (bit_at_binary__solve_recursive x bit) as [Hz | Ho].
    + unfold BitIs in *. rewrite Hz. simpl.
      rewrite !Zlength_cons. lia.
    + unfold BitIs in *. rewrite Ho. simpl.
      rewrite !Zlength_cons. lia.
Qed.
Lemma sublist_nested__solve_recursive :
  forall {A : Type} (xs : list A) (d : A) outer_lo outer_hi lo hi,
    0 <= outer_lo <= lo -> lo <= hi <= outer_hi ->
    outer_hi <= Zlength xs ->
    sublist lo hi xs =
    sublist (lo - outer_lo) (hi - outer_lo)
      (sublist outer_lo outer_hi xs).
Proof.
  intros A xs d outer_lo outer_hi lo hi Hlo Hhi Houter.
  apply (proj2 (list_eq_ext _ _ d)). split.
  - rewrite (Zlength_sublist lo hi xs) by lia.
    rewrite (Zlength_sublist (lo - outer_lo) (hi - outer_lo)
      (sublist outer_lo outer_hi xs)).
    + lia.
    + rewrite Zlength_sublist by lia. lia.
  - intros j Hj. rewrite Zlength_sublist in Hj by lia.
    rewrite (Znth_sublist d lo j hi xs) by lia.
    rewrite (Znth_sublist d (lo - outer_lo) j (hi - outer_lo)
      (sublist outer_lo outer_hi xs)) by lia.
    rewrite (Znth_sublist d outer_lo (j + (lo - outer_lo)) outer_hi xs)
      by lia.
    f_equal. lia.
Qed.
Lemma sublist_prefix_eq__solve_recursive :
  forall {A : Type} (xs ys : list A) (d : A) small big,
    Zlength xs = Zlength ys ->
    0 <= small <= big -> big <= Zlength xs ->
    sublist 0 big xs = sublist 0 big ys ->
    sublist 0 small xs = sublist 0 small ys.
Proof.
  intros A xs ys d small big Hlen Hrange Hbig Heq.
  rewrite (sublist_nested__solve_recursive xs d 0 big 0 small) by lia.
  rewrite (sublist_nested__solve_recursive ys d 0 big 0 small) by lia.
  rewrite Heq. reflexivity.
Qed.
Lemma sublist_suffix_eq__solve_recursive :
  forall {A : Type} (xs ys : list A) (d : A) big small,
    Zlength xs = Zlength ys ->
    0 <= big <= small -> small <= Zlength xs ->
    sublist big (Zlength xs) xs = sublist big (Zlength ys) ys ->
    sublist small (Zlength xs) xs = sublist small (Zlength ys) ys.
Proof.
  intros A xs ys d big small Hlen Hrange Hsmall Heq.
  rewrite (sublist_nested__solve_recursive xs d big (Zlength xs)
    small (Zlength xs)) by lia.
  rewrite (sublist_nested__solve_recursive ys d big (Zlength ys)
    small (Zlength ys)) by lia.
  rewrite Heq, Hlen. reflexivity.
Qed.
Lemma solve_effect_shape_compose_partition__solve_recursive :
  forall before partition_before partitioned first_after after
      costs1 costs2 costs3 l mid r bit,
    0 <= l <= mid -> mid <= r -> r <= Zlength before ->
    PartitionCopyBack before partition_before partitioned l r r ->
    SolveEffect partition_before first_after costs1 costs2 l mid bit ->
    SolveEffect first_after after costs2 costs3 mid r bit ->
    Zlength after = Zlength before /\
    sublist 0 l after = sublist 0 l before /\
    sublist r (Zlength before) after = sublist r (Zlength before) before /\
    Permutation (sublist l r before) (sublist l r after).
Proof.
  intros before partition_before partitioned first_after after
    costs1 costs2 costs3 l mid r bit Hl Hmr Hr Hcopy Hleft Hright.
  unfold PartitionCopyBack in Hcopy.
  destruct Hcopy as [Hplen [Hpartlen [Hcopy_pre [Hcopy_seg
    [Hcopy_post Hcopy_perm]]]]].
  unfold SolveEffect in Hleft, Hright.
  destruct Hleft as [Hflen [Hleft_pre [Hleft_post [Hleft_perm _]]]].
  destruct Hright as [Halen [Hright_pre [Hright_post [Hright_perm _]]]].
  assert (Haf : Zlength after = Zlength first_after) by exact Halen.
  assert (Hfp : Zlength first_after = Zlength partition_before) by exact Hflen.
  assert (Hap : Zlength after = Zlength partition_before) by lia.
  assert (Hpb : Zlength partition_before = Zlength before) by exact Hplen.
  assert (Hpartseg : sublist l r partition_before = partitioned).
  { rewrite Hcopy_seg. apply sublist_self. symmetry. exact Hpartlen. }
  assert (Hright_pre_l : sublist 0 l after = sublist 0 l first_after).
  { eapply (sublist_prefix_eq__solve_recursive after first_after 0 l mid).
    - exact Halen.
    - lia.
    - lia.
    - exact Hright_pre. }
  assert (Hleft_post_r :
    sublist r (Zlength first_after) first_after =
    sublist r (Zlength partition_before) partition_before).
  { eapply (sublist_suffix_eq__solve_recursive
      first_after partition_before 0 mid r).
    - exact Hflen.
    - lia.
    - lia.
    - rewrite Hflen. exact Hleft_post. }
  assert (Hleft_right : sublist mid r first_after =
    sublist mid r partition_before).
  { rewrite (sublist_nested__solve_recursive first_after 0 mid
      (Zlength first_after) mid r) by lia.
    rewrite (sublist_nested__solve_recursive partition_before 0 mid
      (Zlength partition_before) mid r) by lia.
    rewrite Hfp, Hleft_post. reflexivity. }
  assert (Hright_left : sublist l mid after = sublist l mid first_after).
  { rewrite (sublist_nested__solve_recursive after 0 0 mid l mid) by lia.
    rewrite (sublist_nested__solve_recursive first_after 0 0 mid l mid) by lia.
    rewrite Hright_pre. reflexivity. }
  repeat split.
  - lia.
  - rewrite Hright_pre_l, Hleft_pre, Hcopy_pre. reflexivity.
  - replace (Zlength before) with (Zlength first_after) at 1 by lia.
    rewrite Hright_post, Hleft_post_r, Hpb, Hcopy_post. reflexivity.
  - eapply Permutation_trans; [exact Hcopy_perm|].
    rewrite <- Hpartseg.
    rewrite (sublist_split l r mid partition_before) by lia.
    rewrite (sublist_split l r mid after) by lia.
    apply Permutation_app.
    + rewrite Hright_left. exact Hleft_perm.
    + rewrite <- Hleft_right. exact Hright_perm.
Qed.
Lemma solve_effect_compose_partition__solve_recursive :
  forall before partition_before partitioned scratch first_after after
      cost_before counted_costs first_cost cost_after
      l mid r bit zeros ones p (d : option Z),
    0 <= l <= mid -> mid <= r -> r <= Zlength before ->
    Zlength scratch = Zlength before ->
    Zlength partitioned = r - l ->
    (forall k, l <= k < r ->
      Znth k scratch d = Some (Znth (k - l) partitioned 0)) ->
    mid = l + zeros -> p = r ->
    SolveCountPrefix before cost_before counted_costs l r bit zeros ones ->
    StablePartitionPrefix before scratch l r bit r p 1 ->
    PartitionCopyBack before partition_before partitioned l r r ->
    SolveEffect partition_before first_after counted_costs first_cost
      l mid (bit - 1) ->
    SolveEffect first_after after first_cost cost_after
      mid r (bit - 1) ->
    SolveEffect before after cost_before cost_after l r bit.
Proof.
  intros before partition_before partitioned scratch first_after after
    cost_before counted_costs first_cost cost_after
    l mid r bit zeros ones p d Hl Hmr Hr Hscratchlen Hpartlen Hpoint
    Hmid Hp Hcount Hstable Hcopy Hleft Hright.
  assert (Hstable_mat := materialized_stable_partition__solve_recursive
    before scratch partitioned l r bit p d).
  specialize (Hstable_mat ltac:(lia) ltac:(lia) Hpartlen Hpoint Hstable Hp).
  assert (Hzero_card := set_card_bit_slice_filter__solve_recursive
    before l r bit 0 (proj1 Hl) ltac:(lia) Hr).
  assert (Hfilter_lengths := filter_bit_lengths__solve_recursive
    (sublist l r before) bit).
  unfold SolveCountPrefix in Hcount.
  destruct Hcount as [Hzero [Hone [Hcb_len [Hcc_len
    [Hcount_rows Hcount_delta]]]]].
  rewrite Hzero_card in Hzero.
  assert (Hleft_len :
    Zlength (filter (BitIs bit 0) (sublist l r before)) = mid - l)
    by lia.
  assert (Hright_len :
    Zlength (filter (BitIs bit 1) (sublist l r before)) = r - mid)
    by (rewrite Zlength_sublist in Hfilter_lengths by lia; lia).
  unfold PartitionCopyBack in Hcopy.
  destruct Hcopy as [Hplen [Hpartition_len [Hcopy_pre [Hcopy_seg
    [Hcopy_post Hcopy_perm]]]]].
  assert (Hpartseg : sublist l r partition_before = partitioned).
  { rewrite Hcopy_seg. apply sublist_self. symmetry. exact Hpartition_len. }
  assert (Hleftseg : sublist l mid partition_before =
    filter (BitIs bit 0) (sublist l r before)).
  { rewrite (sublist_nested__solve_recursive partition_before 0 l r l mid)
      by lia.
    rewrite Hpartseg, Hstable_mat, <- Hleft_len.
    replace (l - l) with 0 by lia.
    apply sublist_app_exact1. }
  assert (Hrightseg_partition : sublist mid r partition_before =
    filter (BitIs bit 1) (sublist l r before)).
  { rewrite (sublist_nested__solve_recursive partition_before 0 l r mid r)
      by lia.
    rewrite Hpartseg, Hstable_mat.
    rewrite (sublist_split_app_r (mid - l) (r - l)
      (Zlength (filter (BitIs bit 0) (sublist l r before)))
      (filter (BitIs bit 0) (sublist l r before))
      (filter (BitIs bit 1) (sublist l r before))) by lia.
    replace (mid - l -
      Zlength (filter (BitIs bit 0) (sublist l r before))) with 0 by lia.
    replace (r - l -
      Zlength (filter (BitIs bit 0) (sublist l r before)))
      with (Zlength (filter (BitIs bit 1) (sublist l r before))) by lia.
    apply sublist_self. reflexivity. }
  pose proof Hleft as Hleft_full.
  pose proof Hright as Hright_full.
  unfold SolveEffect in Hleft, Hright |- *.
  destruct Hleft as [Hflen [Hleft_pre [Hleft_post [Hleft_perm
    [Hcc_len' [Hfc_len [Hleft_rows [Hleft_delta Hleft_table]]]]]]]].
  destruct Hright as [Halen [Hright_pre [Hright_post [Hright_perm
    [Hfc_len' [Hca_len [Hright_rows [Hright_delta Hright_table]]]]]]]].
  assert (Hrightseg : sublist mid r first_after =
    filter (BitIs bit 1) (sublist l r before)).
  { rewrite (sublist_nested__solve_recursive first_after 0 mid
      (Zlength first_after) mid r) by lia.
    rewrite (sublist_nested__solve_recursive partition_before 0 mid
      (Zlength partition_before) mid r) in Hrightseg_partition by lia.
    rewrite Hflen, Hleft_post.
    exact Hrightseg_partition. }
  assert (Hshape := solve_effect_shape_compose_partition__solve_recursive
    before partition_before partitioned first_after after
    counted_costs first_cost cost_after l mid r (bit - 1)
    Hl Hmr Hr).
  assert (Hcopy_full : PartitionCopyBack before partition_before partitioned l r r).
  { unfold PartitionCopyBack. repeat split; assumption. }
  specialize (Hshape Hcopy_full Hleft_full Hright_full).
  destruct Hshape as [Hfinal_len [Hfinal_pre [Hfinal_post Hfinal_perm]]].
  repeat split.
  - exact Hfinal_len.
  - exact Hfinal_pre.
  - exact Hfinal_post.
  - exact Hfinal_perm.
  - exact Hcb_len.
  - exact Hca_len.
  - exact (proj1 (Hcount_rows b H)).
  - exact (proj2 (Hright_rows b H)).
  -
    intros b choice Hb Hchoice.
    destruct (Z.eq_dec b bit) as [-> | Hne].
    + left. split; [lia|].
      specialize (Hcount_delta bit choice Hb Hchoice).
      specialize (Hleft_delta bit choice Hb Hchoice).
      specialize (Hright_delta bit choice Hb Hchoice).
      destruct Hcount_delta as [[_ [delta [Hdelta Hcost0]]] | [Hbad _]];
        [|contradiction].
      destruct Hleft_delta as [[Hbad _] | [_ Hcost1]]; [lia|].
      destruct Hright_delta as [[Hbad _] | [_ Hcost2]]; [lia|].
      exists delta. split; [exact Hdelta|]. lia.
    + destruct (Z_le_gt_dec b (bit - 1)) as [Hlow | Hhigh].
      * left. split; [lia|].
        specialize (Hcount_delta b choice Hb Hchoice).
        specialize (Hleft_delta b choice Hb Hchoice).
        specialize (Hright_delta b choice Hb Hchoice).
        destruct Hcount_delta as [[Heq _] | [_ Hcost0]]; [contradiction|].
        destruct Hleft_delta as [[_ [delta0 [Hdelta0 Hcost1]]] | [Hbad _]];
          [|lia].
        destruct Hright_delta as [[_ [delta1 [Hdelta1 Hcost2]]] | [Hbad _]];
          [|lia].
        rewrite Hleftseg in Hdelta0. rewrite Hrightseg in Hdelta1.
        exists (delta0 + delta1). split.
        -- eapply bit_contribution_partition__solve_recursive; eauto. lia.
        -- lia.
      * right. split; [lia|].
        specialize (Hcount_delta b choice Hb Hchoice).
        specialize (Hleft_delta b choice Hb Hchoice).
        specialize (Hright_delta b choice Hb Hchoice).
        destruct Hcount_delta as [[Heq _] | [_ Hcost0]]; [contradiction|].
        destruct Hleft_delta as [[Hbad _] | [_ Hcost1]]; [lia|].
        destruct Hright_delta as [[Hbad _] | [_ Hcost2]]; [lia|].
        lia.
  - exact Hca_len.
  - intros b Hb. exact (proj2 (Hright_rows b Hb)).
  - intros b choice Hb Hchoice.
      destruct H as [Hl0 [Hrfull [Hbit29 Hzero_cost]]].
      specialize (Hcount_delta b choice Hb Hchoice).
      specialize (Hleft_delta b choice Hb Hchoice).
      specialize (Hright_delta b choice Hb Hchoice).
      destruct (Z.eq_dec b bit) as [-> | Hne].
      * destruct Hcount_delta as [[_ [delta [Hdelta Hcost0]]] | [Hbad _]];
          [|contradiction].
        destruct Hleft_delta as [[Hbad _] | [_ Hcost1]]; [lia|].
        destruct Hright_delta as [[Hbad _] | [_ Hcost2]]; [lia|].
        unfold CostAt in Hzero_cost.
        specialize (Hzero_cost bit choice Hb Hchoice).
        unfold CostAt in Hcost0, Hcost1, Hcost2 |- *.
        rewrite Hl0, Hrfull in Hdelta.
        rewrite sublist_self in Hdelta by reflexivity.
        rewrite Hbit29 in Hdelta. rewrite Hzero_cost in Hcost0.
        replace (Znth choice (Znth bit cost_after nil) 0) with delta by lia.
        rewrite Hbit29. exact Hdelta.
      * assert (Hlow : b <= bit - 1) by lia.
        destruct Hcount_delta as [[Heq _] | [_ Hcost0]]; [contradiction|].
        destruct Hleft_delta as [[_ [delta0 [Hdelta0 Hcost1]]] | [Hbad _]];
          [|lia].
        destruct Hright_delta as [[_ [delta1 [Hdelta1 Hcost2]]] | [Hbad _]];
          [|lia].
        rewrite Hleftseg in Hdelta0. rewrite Hrightseg in Hdelta1.
        assert (Hdelta := bit_contribution_partition__solve_recursive
          (sublist l r before) bit b choice delta0 delta1 ltac:(lia)
          Hdelta0 Hdelta1).
        unfold CostAt in Hzero_cost.
        specialize (Hzero_cost b choice Hb Hchoice).
        unfold CostAt in Hcost0, Hcost1, Hcost2 |- *.
        rewrite Hl0, Hrfull in Hdelta.
        rewrite sublist_self in Hdelta by reflexivity.
        rewrite Hbit29 in Hdelta. rewrite Hzero_cost in Hcost0.
        replace (Znth choice (Znth b cost_after nil) 0) with
          (delta0 + delta1) by lia.
        exact Hdelta.
Qed.
Lemma input_copy_prefix_extend__solver_copy_init :
  forall (input : list Z) (cells : list (option Z)) i,
    0 <= i < Zlength input ->
    Zlength cells = Zlength input ->
    InputCopyPrefix input cells i ->
    InputCopyPrefix input
      (replace_Znth i (Some (Znth i input 0)) cells) (i + 1).
Proof.
  intros input cells i Hi Hlen Hprefix.
  unfold InputCopyPrefix, InitializedSlice in *.
  rewrite (sublist_split 0 (i + 1) i
    (replace_Znth i (Some (Znth i input 0)) cells)) by
    (try rewrite Zlength_replace_Znth; lia).
  rewrite (@sublist_single (option Z) None i
    (replace_Znth i (Some (Znth i input 0)) cells)) by
    (rewrite Zlength_replace_Znth; lia).
  assert (Hreplace_prefix :
    sublist 0 i (replace_Znth i (Some (Znth i input 0)) cells) =
    sublist 0 i cells).
  {
    apply (proj2 (list_eq_ext _ _ None)).
    split.
    - rewrite !Zlength_sublist0; try rewrite Zlength_replace_Znth; lia.
    - intros k Hk.
      rewrite Zlength_sublist0 in Hk by
        (rewrite Zlength_replace_Znth; lia).
      rewrite !Znth_sublist0 by
        (try rewrite Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia.
      reflexivity.
  }
  rewrite Hreplace_prefix.
  rewrite Znth_replace_Znth_Same by lia.
  rewrite (sublist_split 0 (i + 1) i input) by lia.
  rewrite (sublist_single 0 i input) by lia.
  rewrite map_app.
  simpl.
  rewrite Hprefix.
  reflexivity.
Qed.
Lemma input_copy_prefix_complete__solver_copy_init :
  forall (input : list Z) (cells : list (option Z)),
    Zlength cells = Zlength input ->
    InputCopyPrefix input cells (Zlength input) ->
    cells = map (@Some Z) input.
Proof.
  intros input cells Hlen Hprefix.
  unfold InputCopyPrefix, InitializedSlice in Hprefix.
  rewrite (sublist_self cells (Zlength input)) in Hprefix by exact (eq_sym Hlen).
  rewrite (sublist_self input (Zlength input)) in Hprefix by reflexivity.
  exact Hprefix.
Qed.
Lemma undef_cost_rows_shift__solver_zero_cost :
  forall x m offset lo hi len,
  store_undef_array_rec (Int64Array2.undef_row_store m)
    x (lo + offset) hi len |--
  store_undef_array_rec (Int64Array2.undef_row_store m)
    (x + offset * m * sizeof(INT64)) lo (hi - offset) len.
Proof.
  intros x m offset lo hi len.
  revert x lo hi.
  induction len; intros; simpl.
  - Intros_p H.
    split_pure_spatial.
    + cancel emp.
    + dump_pre_spatial. lia.
  - unfold Int64Array2.undef_row_store, Int64Array2.row_addr.
    replace (x + (lo + offset) * m * sizeof ( INT64 ))
      with (x + offset * m * sizeof(INT64) + lo * m * sizeof(INT64)) by nia.
    replace (lo + offset + 1) with (lo + 1 + offset) by lia.
    sep_apply (IHlen x (lo + 1) hi).
    cancel (Int64Array.undef_full
      (x + offset * m * sizeof(INT64) + lo * m * sizeof(INT64)) m).
    change (store_undef_array_rec (Int64Array2.undef_row_store m)
      (x + offset * m * sizeof(INT64)) (lo + 1) (hi - offset) len |--
      store_undef_array_rec (Int64Array2.undef_row_store m)
      (x + offset * m * sizeof(INT64)) (lo + 1) (hi - offset) len).
    cancel (store_undef_array_rec (Int64Array2.undef_row_store m)
      (x + offset * m * sizeof(INT64)) (lo + 1) (hi - offset) len).
Qed.
Lemma undef_cost_table_unfold__solver_zero_cost : forall x n,
  1 <= n ->
  Int64Array2.undef_full x n 2 |--
  (x + 0 * sizeof(INT64)) # Int64 |->_ **
  (x + 1 * sizeof(INT64)) # Int64 |->_ **
  Int64Array2.undef_full (x + sizeof(INT64) * 2) (n - 1) 2.
Proof.
  intros x n Hn.
  unfold Int64Array2.undef_full, store_undef_array.
  replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
  simpl.
  unfold Int64Array2.undef_row_store, Int64Array2.row_addr.
  replace (x + 0 * 2 * sizeof(INT64)) with x by lia.
  sep_apply (undef_cost_rows_shift__solver_zero_cost
    x 2 1 0 n (Z.to_nat (n - 1))).
  sep_apply_l_atomic (Int64Array.undef_full_unfold x 1 (@nil Z)).
  - dump_pre_spatial. lia.
  - unfold Int64Array.undef_seg, store_undef_array_rec.
    simpl.
    Intros_p Hdone.
    cancel ((x + 0 * sizeof(INT64)) # Int64 |->_).
    cancel ((x + 1 * sizeof(INT64)) # Int64 |->_).
    change (store_undef_array_rec (Int64Array2.undef_row_store 2)
      (x + sizeof(INT64) * 2) 0 (n - 1) (Z.to_nat (n - 1)) |--
      store_undef_array_rec (Int64Array2.undef_row_store 2)
      (x + sizeof(INT64) * 2) 0 (n - 1) (Z.to_nat (n - 1))).
    cancel (store_undef_array_rec (Int64Array2.undef_row_store 2)
      (x + sizeof(INT64) * 2) 0 (n - 1) (Z.to_nat (n - 1))).
Qed.
Lemma cost_rows_rec_snoc__solver_zero_cost : forall x lo hi rows row,
  Zlength rows = hi - lo ->
  store_array_rec (Int64Array2.row_store 2) x lo hi rows **
  Int64Array2.row_store 2 x hi row |--
  store_array_rec (Int64Array2.row_store 2) x lo (hi + 1)
    (rows ++ row :: nil).
Proof.
  intros x lo hi rows.
  revert lo hi.
  induction rows as [|a rows IH]; intros lo hi row Hlen.
  - simpl in Hlen.
    simpl [store_array_rec].
    Intros_p Hlo.
    Intros_p Hnil.
    subst hi.
    split_pure_spatial.
    + unfold Int64Array2.row_store, Int64Array2.row_addr.
      cancel.
    + split_pures; dump_pre_spatial; auto; lia.
  - simpl in Hlen.
    simpl [store_array_rec].
    sep_apply (IH (lo + 1) hi row).
    + cancel (Int64Array2.row_store 2 x lo a).
      cancel (store_array_rec (Int64Array2.row_store 2) x
        (lo + 1) (hi + 1) (rows ++ row :: nil)).
    + rewrite Zlength_cons in Hlen. lia.
Qed.
Lemma full_cost_rows_snoc__solver_zero_cost : forall x n rows row,
  Zlength rows = n ->
  Int64Array2.full x n 2 rows **
  Int64Array.full (x + n * (sizeof(INT64) * 2)) 2 row |--
  Int64Array2.full x (n + 1) 2 (rows ++ row :: nil).
Proof.
  intros x n rows row Hlen.
  unfold Int64Array2.full, store_array.
  replace (x + n * (sizeof(INT64) * 2))
    with (x + n * 2 * sizeof(INT64)) by nia.
  change (store_array_rec (Int64Array2.row_store 2) x 0 n rows **
    Int64Array2.row_store 2 x n row |--
    store_array_rec (Int64Array2.row_store 2) x 0 (n + 1)
      (rows ++ row :: nil)).
  apply (cost_rows_rec_snoc__solver_zero_cost x 0 n rows row); try lia.
Qed.
Lemma int64_zero_row_full__solver_zero_cost : forall x,
  (x + 0 * sizeof(INT64)) # Int64 |-> 0 **
  (x + 1 * sizeof(INT64)) # Int64 |-> 0 |--
  Int64Array.full x 2 (0 :: 0 :: nil).
Proof.
  intros x.
  unfold Int64Array.full, store_array.
  simpl [store_array_rec].
  split_pure_spatial.
  - cancel ((x + 0 * sizeof(INT64)) # Int64 |-> 0).
    cancel ((x + 1 * sizeof(INT64)) # Int64 |-> 0).
  - split_pures; dump_pre_spatial; auto; lia.
Qed.
Lemma Znth_app_left__solver_zero_cost :
  forall (A : Type) (l1 l2 : list A) (d : A) (i : Z),
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros A l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma Znth_app_last__solver_zero_cost :
  forall (A : Type) (l : list A) (d x : A),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros A l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma zero_rows_extend__solver_zero_cost : forall rows d b,
  Zlength rows = b ->
  (forall row, 0 <= row < b ->
    (Zlength (Znth row rows d) = 2 /\ Znth 0 (Znth row rows d) 0 = 0) /\
    Znth 1 (Znth row rows d) 0 = 0) ->
  Zlength (rows ++ (0 :: 0 :: nil) :: nil) = b + 1 /\
  (forall row, 0 <= row < b + 1 ->
    (Zlength (Znth row (rows ++ (0 :: 0 :: nil) :: nil) d) = 2 /\
     Znth 0 (Znth row (rows ++ (0 :: 0 :: nil) :: nil) d) 0 = 0) /\
    Znth 1 (Znth row (rows ++ (0 :: 0 :: nil) :: nil) d) 0 = 0).
Proof.
  intros rows d b Hlen Hrows.
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - intros row Hrow.
    destruct (Z_lt_dec row b) as [Hlt | Hge].
    + rewrite Znth_app_left__solver_zero_cost by lia.
      apply Hrows. lia.
    + assert (row = b) by lia. subst row.
      rewrite <- Hlen.
      rewrite Znth_app_last__solver_zero_cost.
      repeat split; reflexivity.
Qed.
Lemma zero_cost_prefix_extend__solver_zero_cost : forall cells b,
  0 <= b < 30 ->
  ZeroCostPrefix cells b ->
  ZeroCostPrefix (replace_Znth b (Some 0 :: Some 0 :: nil) cells) (b + 1).
Proof.
  intros cells b Hb [Hlen [Hrows Hzero]].
  unfold ZeroCostPrefix.
  repeat split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - intros row Hrow.
    destruct (Z.eq_dec row b) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia. reflexivity.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply Hrows. lia.
  - intros row choice Hrow Hchoice.
    destruct (Z.eq_dec row b) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      assert (choice = 0 \/ choice = 1) by lia.
      destruct H as [-> | ->]; reflexivity.
    + rewrite Znth_replace_Znth_Diff by lia.
      apply Hzero; lia.
Qed.
Lemma zero_cost_prefix_complete__solver_zero_cost : forall rows d,
  Zlength rows = 30 ->
  (forall b, 0 <= b < 30 ->
    (Zlength (Znth b rows d) = 2 /\ Znth 0 (Znth b rows d) 0 = 0) /\
    Znth 1 (Znth b rows d) 0 = 0) ->
  CostBound rows 0.
Proof.
  intros rows d Hlen Hrows.
  unfold CostBound, CostAt.
  split; [lia |].
  split; [exact Hlen |].
  intros bit choice Hbit Hchoice.
  specialize (Hrows bit Hbit) as [[Hrowlen Hzero] Hone].
  assert (Hbitr : 0 <= bit < Zlength rows) by lia.
  pose proof (Znth_indep rows bit d (@nil Z) Hbitr) as Hindep.
  rewrite Hindep in Hzero, Hone.
  assert (choice = 0 \/ choice = 1) by lia.
  destruct H as [-> | ->].
  - rewrite Hzero. lia.
  - rewrite Hone. lia.
Qed.
Lemma solve_effect_full_range_cost_table__solver_solve_transition :
  forall before after cost_before cost_after n,
    SolveEffect before after cost_before cost_after 0 n 29 ->
    n = Zlength before ->
    (forall bit choice,
      0 <= bit < 30 -> 0 <= choice < 2 ->
      CostAt cost_before bit choice = 0) ->
    CostTable before cost_after.
Proof.
  intros before after cost_before cost_after n Heffect Hn Hzero.
  unfold SolveEffect in Heffect.
  destruct Heffect as
    [_ [_ [_ [_ [_ [_ [_ [_ Hfull]]]]]]]].
  apply Hfull.
  subst n.
  repeat split; try reflexivity.
  exact Hzero.
Qed.
Lemma xor_choice_prefix_zero__solver_solve_transition :
  forall input costs,
    CostTable input costs ->
    XorChoicePrefix input costs 0 0 0.
Proof.
  intros input costs Htable.
  unfold XorChoicePrefix.
  split; [exact Htable |].
  split; reflexivity.
Qed.
Lemma fold_ones_length__solver_choice_loop :
  forall {A : Type} (xs : list A),
    List.fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
      Z.of_nat (List.length xs).
Proof.
  intros A xs.
  induction xs as [|x xs IH]; [reflexivity |].
  change (1 + List.fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
    Z.of_nat (S (List.length xs))).
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.
Lemma store_array_rec_rebase__solver_choice_loop : forall rows p q m lo lo' hi hi',
  p + lo * m * 8 = q + lo' * m * 8 ->
  hi - lo = hi' - lo' ->
  store_array_rec
    (fun (x : addr) (i : Z) (row : list Z) =>
      Int64Array2.ElemArray.full (x + i * m * 8) m row)
    p lo hi rows |--
  store_array_rec
    (fun (x : addr) (i : Z) (row : list Z) =>
      Int64Array2.ElemArray.full (x + i * m * 8) m row)
    q lo' hi' rows.
Proof.
  induction rows as [|a rows IH]; intros; simpl.
  - LLM_pre_process ltac:(lia || nia).
  - rewrite <- H.
    cancel (Int64Array2.ElemArray.full (p + lo * m * 8) m a).
    apply IH; nia.
Qed.
Lemma store_array_rec_decompose__solver_choice_loop : forall prefix row suffix p m lo hi,
  store_array_rec
    (fun (x : addr) (i : Z) (r : list Z) =>
      Int64Array2.ElemArray.full (x + i * m * 8) m r)
    p lo hi (prefix ++ row :: suffix) |--
  store_array_rec
    (fun (x : addr) (i : Z) (r : list Z) =>
      Int64Array2.ElemArray.full (x + i * m * 8) m r)
    p lo (lo + Zlength prefix) prefix **
  Int64Array2.ElemArray.full (p + (lo + Zlength prefix) * m * 8) m row **
  store_array_rec
    (fun (x : addr) (i : Z) (r : list Z) =>
      Int64Array2.ElemArray.full (x + i * m * 8) m r)
    p (lo + Zlength prefix + 1) hi suffix.
Proof.
  induction prefix as [|a prefix IH]; intros; simpl.
  - rewrite Zlength_nil.
    replace (lo + 0) with lo by lia.
    LLM_pre_process ltac:(lia || nia).
  - rewrite Zlength_cons.
    replace (Z.succ (Zlength prefix)) with (Zlength prefix + 1) by lia.
    replace (lo + (Zlength prefix + 1)) with ((lo + 1) + Zlength prefix) by lia.
    cancel (Int64Array2.ElemArray.full (p + lo * m * 8) m a).
    sep_apply_l_atomic (IH row suffix p m (lo + 1) hi).
    cancel.
Qed.
Lemma store_array_rec_compose__solver_choice_loop : forall prefix row suffix p m lo hi,
  store_array_rec
    (fun (x : addr) (i : Z) (r : list Z) =>
      Int64Array2.ElemArray.full (x + i * m * 8) m r)
    p lo (lo + Zlength prefix) prefix **
  Int64Array2.ElemArray.full (p + (lo + Zlength prefix) * m * 8) m row **
  store_array_rec
    (fun (x : addr) (i : Z) (r : list Z) =>
      Int64Array2.ElemArray.full (x + i * m * 8) m r)
    p (lo + Zlength prefix + 1) hi suffix |--
  store_array_rec
    (fun (x : addr) (i : Z) (r : list Z) =>
      Int64Array2.ElemArray.full (x + i * m * 8) m r)
    p lo hi (prefix ++ row :: suffix).
Proof.
  induction prefix as [|a prefix IH]; intros; simpl.
  - rewrite Zlength_nil.
    replace (lo + 0) with lo by lia.
    LLM_pre_process ltac:(lia || nia).
  - rewrite Zlength_cons.
    replace (Z.succ (Zlength prefix)) with (Zlength prefix + 1) by lia.
    replace (lo + (Zlength prefix + 1)) with ((lo + 1) + Zlength prefix) by lia.
    cancel (Int64Array2.ElemArray.full (p + lo * m * 8) m a).
    sep_apply_l_atomic (IH row suffix p m (lo + 1) hi).
    cancel.
Qed.
Lemma int64_row_two_expose__solver_choice_loop : forall p z0 z1,
  Int64Array2.ElemArray.full p 2 (z0 :: z1 :: nil) |--
  p # Int64 |-> z0 ** (p + 8) # Int64 |-> z1.
Proof.
  intros.
  unfold Int64Array2.ElemArray.full, store_array.
  simpl.
  replace (p + 0 * 8) with p by lia.
  replace (p + 1 * 8) with (p + 8) by lia.
  LLM_pre_process ltac:(lia || nia).
  replace (p + 0) with p by lia.
  cancel.
Qed.
Lemma int64_row_two_compose__solver_choice_loop : forall p z0 z1,
  p # Int64 |-> z0 ** (p + 8) # Int64 |-> z1 |--
  Int64Array2.ElemArray.full p 2 (z0 :: z1 :: nil).
Proof.
  intros.
  unfold Int64Array2.ElemArray.full, store_array.
  simpl.
  replace (p + 0 * 8) with p by lia.
  replace (p + 1 * 8) with (p + 8) by lia.
  replace (p + 0) with p by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; reflexivity.
Qed.
Lemma int64_cost_table_expose__solver_choice_loop : forall p rows b d,
  Zlength rows = 30 ->
  0 <= b < 30 ->
  Zlength (Znth b rows d) = 2 ->
  Int64Array2.full p 30 2 rows |--
  Int64Array2.full p b 2 (sublist 0 b rows) **
  (p + b * 16 + 0) # Int64 |-> Znth 0 (Znth b rows d) 0 **
  (p + b * 16 + 8) # Int64 |-> Znth 1 (Znth b rows d) 0 **
  Int64Array2.full (p + (b + 1) * 16) (30 - b - 1) 2
    (sublist (b + 1) 30 rows).
Proof.
  intros p rows b d Hlen Hb Hrowlen.
  assert (Hrows : rows =
    sublist 0 b rows ++ Znth b rows d :: sublist (b + 1) 30 rows).
  {
    rewrite <- (sublist_self rows 30 (eq_sym Hlen)) at 1.
    rewrite (sublist_split 0 30 b rows) by lia.
    rewrite (sublist_split b 30 (b + 1) rows) by lia.
    rewrite (sublist_single d b rows) by lia.
    simpl. reflexivity.
  }
  unfold Int64Array2.full, Int64Array2.row_store, Int64Array2.row_addr.
  rewrite Hrows at 1.
  unfold store_array.
  sep_apply_l_atomic
    (store_array_rec_decompose__solver_choice_loop
      (sublist 0 b rows) (Znth b rows d)
      (sublist (b + 1) 30 rows) p 2 0 30).
  rewrite Zlength_sublist by lia.
  remember (Znth b rows d) as row eqn:Hrow.
  destruct row as [|z0 row].
  - rewrite Zlength_nil in Hrowlen; lia.
  - rewrite Zlength_cons in Hrowlen.
    destruct row as [|z1 row].
    + rewrite Zlength_nil in Hrowlen; lia.
    + rewrite Zlength_cons in Hrowlen.
      destruct row as [|z2 row].
      2: { rewrite Zlength_cons in Hrowlen. pose proof (Zlength_nonneg row); lia. }
      rewrite Zlength_nil in Hrowlen.
  replace (0 + (b - 0)) with b by lia.
  sep_apply_l_atomic (int64_row_two_expose__solver_choice_loop
    (p + b * 2 * 8) z0 z1).
  sep_apply_l_atomic
    (store_array_rec_rebase__solver_choice_loop
      (sublist (b + 1) 30 rows) p (p + (b + 1) * 16)
      2 (b + 1) 0 30 (30 - b - 1) ltac:(nia) ltac:(nia)).
  simpl Znth.
  replace (p + b * 2 * 8) with (p + b * 16 + 0) by ring.
  replace (p + b * 16 + 0 + 8) with (p + b * 16 + 8) by ring.
  change (sizeof ( INT64 )) with 8.
  change (Znth 0 (z0 :: z1 :: nil) 0) with z0.
  change (Znth 1 (z0 :: z1 :: nil) 0) with z1.
  cancel.
Qed.
Lemma int64_cost_table_merge__solver_choice_loop : forall p rows b d,
  Zlength rows = 30 ->
  0 <= b < 30 ->
  Zlength (Znth b rows d) = 2 ->
  Int64Array2.full p b 2 (sublist 0 b rows) **
  (p + b * 16 + 0) # Int64 |-> Znth 0 (Znth b rows d) 0 **
  (p + b * 16 + 8) # Int64 |-> Znth 1 (Znth b rows d) 0 **
  Int64Array2.full (p + (b + 1) * 16) (30 - b - 1) 2
    (sublist (b + 1) 30 rows) |--
  Int64Array2.full p 30 2 rows.
Proof.
  intros p rows b d Hlen Hb Hrowlen.
  assert (Hrows : rows =
    sublist 0 b rows ++ Znth b rows d :: sublist (b + 1) 30 rows).
  {
    rewrite <- (sublist_self rows 30 (eq_sym Hlen)) at 1.
    rewrite (sublist_split 0 30 b rows) by lia.
    rewrite (sublist_split b 30 (b + 1) rows) by lia.
    rewrite (sublist_single d b rows) by lia.
    simpl. reflexivity.
  }
  remember (Znth b rows d) as row eqn:Hrow.
  destruct row as [|z0 row].
  - rewrite Zlength_nil in Hrowlen; lia.
  - rewrite Zlength_cons in Hrowlen.
    destruct row as [|z1 row].
    + rewrite Zlength_nil in Hrowlen; lia.
    + rewrite Zlength_cons in Hrowlen.
      destruct row as [|z2 row].
      2: { rewrite Zlength_cons in Hrowlen. pose proof (Zlength_nonneg row); lia. }
      rewrite Zlength_nil in Hrowlen.
  transitivity (Int64Array2.full p 30 2
    (sublist 0 b rows ++ (z0 :: z1 :: nil) :: sublist (b + 1) 30 rows)).
  2: { rewrite <- Hrows. cancel. }
  unfold Int64Array2.full, Int64Array2.row_store, Int64Array2.row_addr.
  unfold store_array.
  sep_apply_l_atomic
    (store_array_rec_rebase__solver_choice_loop
      (sublist (b + 1) 30 rows) (p + (b + 1) * 16) p
      2 0 (b + 1) (30 - b - 1) 30 ltac:(nia) ltac:(nia)).
  replace (p + b * 16 + 0) with (p + b * 2 * 8) by ring.
  replace (p + b * 16 + 8) with (p + b * 2 * 8 + 8) by ring.
  change (sizeof ( INT64 )) with 8.
  change (Znth 0 (z0 :: z1 :: nil) 0) with z0.
  change (Znth 1 (z0 :: z1 :: nil) 0) with z1.
  sep_apply_left (int64_row_two_compose__solver_choice_loop
    (p + b * 2 * 8) z0 z1).
  pose proof
    (store_array_rec_compose__solver_choice_loop
      (sublist 0 b rows) (z0 :: z1 :: nil)
      (sublist (b + 1) 30 rows) p 2 0 30) as Hcomp.
  rewrite Zlength_sublist in Hcomp by lia.
  replace (0 + (b - 0)) with b in Hcomp by lia.
  sep_apply_left Hcomp.
  cancel.
Qed.
Lemma chosen_contribution_unique_bit__solver_choice_loop :
  forall segment bit1 bit2 choice1 choice2 p,
    0 <= bit1 <= 29 ->
    0 <= bit2 <= 29 ->
    (fst p < snd p /\
     SameHigherBits segment 29 bit1 (fst p) (snd p) /\
     ((choice1 = 0 /\ BitAt (Znth (fst p) segment 0) bit1 = 1 /\
                       BitAt (Znth (snd p) segment 0) bit1 = 0) \/
      (choice1 = 1 /\ BitAt (Znth (fst p) segment 0) bit1 = 0 /\
                       BitAt (Znth (snd p) segment 0) bit1 = 1))) ->
    (fst p < snd p /\
     SameHigherBits segment 29 bit2 (fst p) (snd p) /\
     ((choice2 = 0 /\ BitAt (Znth (fst p) segment 0) bit2 = 1 /\
                       BitAt (Znth (snd p) segment 0) bit2 = 0) \/
      (choice2 = 1 /\ BitAt (Znth (fst p) segment 0) bit2 = 0 /\
                       BitAt (Znth (snd p) segment 0) bit2 = 1))) ->
    bit1 = bit2.
Proof.
  intros segment bit1 bit2 choice1 choice2 p Hbit1 Hbit2 H1 H2.
  destruct H1 as [_ [Hsame1 Hdir1]];
  destruct H2 as [_ [Hsame2 Hdir2]].
  all: destruct (Z_lt_ge_dec bit1 bit2); [|destruct (Z_lt_ge_dec bit2 bit1)];
    try lia.
  all: first
    [ pose proof (Hsame1 bit2 ltac:(lia)) as Heq
    | pose proof (Hsame2 bit1 ltac:(lia)) as Heq ].
  all: destruct Hdir1 as [[_ [Ha1 Hb1]] | [_ [Ha1 Hb1]]];
    destruct Hdir2 as [[_ [Ha2 Hb2]] | [_ [Ha2 Hb2]]]; lia.
Qed.
Lemma chosen_contribution_cost_card__solver_choice_loop :
  forall segment costs bit,
    CostTable segment costs ->
    0 <= bit < 30 ->
    Z.min (CostAt costs bit 0) (CostAt costs bit 1) =
      #(fun p : Z * Z =>
        (0 <= fst p < Zlength segment /\
         0 <= snd p < Zlength segment) /\
        if prop_dec (CostAt costs bit 1 < CostAt costs bit 0)
        then fst p < snd p /\
          SameHigherBits segment 29 bit (fst p) (snd p) /\
          (1 = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                   BitAt (Znth (snd p) segment 0) bit = 0 \/
           1 = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                   BitAt (Znth (snd p) segment 0) bit = 1)
        else fst p < snd p /\
          SameHigherBits segment 29 bit (fst p) (snd p) /\
          (0 = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                   BitAt (Znth (snd p) segment 0) bit = 0 \/
           0 = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                   BitAt (Znth (snd p) segment 0) bit = 1)).
Proof.
  intros segment costs bit Htable Hbit.
  unfold CostTable in Htable.
  destruct Htable as [_ [_ Hcontrib]].
  pose proof (Hcontrib bit 0 Hbit ltac:(lia)) as H0.
  pose proof (Hcontrib bit 1 Hbit ltac:(lia)) as H1.
  unfold BitContribution in H0, H1.
  destruct (prop_dec (CostAt costs bit 1 < CostAt costs bit 0)) as [Hlt | Hnlt].
  - rewrite Z.min_r by lia.
    exact H1.
  - rewrite Z.min_l by lia.
    exact H0.
Qed.
Lemma chosen_contribution_sum_bound__solver_choice_loop :
  forall segment costs next,
    0 <= next <= 30 ->
    SumLib.Sum.sum (fun bit : Z => 0 <= bit < next)
      (fun bit => #(fun p : Z * Z =>
        (0 <= fst p < Zlength segment /\
         0 <= snd p < Zlength segment) /\
        if prop_dec (CostAt costs bit 1 < CostAt costs bit 0)
        then fst p < snd p /\
          SameHigherBits segment 29 bit (fst p) (snd p) /\
          (1 = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                   BitAt (Znth (snd p) segment 0) bit = 0 \/
           1 = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                   BitAt (Znth (snd p) segment 0) bit = 1)
        else fst p < snd p /\
          SameHigherBits segment 29 bit (fst p) (snd p) /\
          (0 = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                   BitAt (Znth (snd p) segment 0) bit = 0 \/
           0 = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                   BitAt (Znth (snd p) segment 0) bit = 1))) <=
      Zlength segment * Zlength segment.
Proof.
  intros segment costs next Hnext.
  unfold set_card, SumLib.Sum.sum.
  set (bits := @enum Z (fun bit : Z => 0 <= bit < next)
    (finite_Z_range 0 next)).
  set (pairs := @enum (Z * Z)
    (fun p : Z * Z =>
      0 <= fst p < Zlength segment /\ 0 <= snd p < Zlength segment)
    (finite_index_pair (Zlength segment))).
  set (selected := fun bit =>
    @enum (Z * Z)
      (fun p : Z * Z =>
        (0 <= fst p < Zlength segment /\
         0 <= snd p < Zlength segment) /\
        if prop_dec (CostAt costs bit 1 < CostAt costs bit 0)
        then fst p < snd p /\
          SameHigherBits segment 29 bit (fst p) (snd p) /\
          (1 = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                   BitAt (Znth (snd p) segment 0) bit = 0 \/
           1 = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                   BitAt (Znth (snd p) segment 0) bit = 1)
        else fst p < snd p /\
          SameHigherBits segment 29 bit (fst p) (snd p) /\
          (0 = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                   BitAt (Znth (snd p) segment 0) bit = 0 \/
           0 = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                   BitAt (Znth (snd p) segment 0) bit = 1))
      (Finite_subset
        (fun p : Z * Z =>
          0 <= fst p < Zlength segment /\
          0 <= snd p < Zlength segment)
        (fun p : Z * Z =>
          if prop_dec (CostAt costs bit 1 < CostAt costs bit 0)
          then fst p < snd p /\
            SameHigherBits segment 29 bit (fst p) (snd p) /\
            (1 = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                     BitAt (Znth (snd p) segment 0) bit = 0 \/
             1 = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                     BitAt (Znth (snd p) segment 0) bit = 1)
          else fst p < snd p /\
            SameHigherBits segment 29 bit (fst p) (snd p) /\
            (0 = 0 /\ BitAt (Znth (fst p) segment 0) bit = 1 /\
                     BitAt (Znth (snd p) segment 0) bit = 0 \/
             0 = 1 /\ BitAt (Znth (fst p) segment 0) bit = 0 /\
                     BitAt (Znth (snd p) segment 0) bit = 1)))).
  assert (Hfold :
    fold_right
      (fun bit acc =>
        fold_right (fun (_ : Z * Z) (z : Z) => 1 + z) 0
          (selected bit) + acc)
      0 bits =
    Z.of_nat (List.length (concat (map selected bits)))).
  {
    induction bits as [|bit bits IH]; [reflexivity |].
    change
      (fold_right (fun (_ : Z * Z) (z : Z) => 1 + z) 0
          (selected bit) +
        fold_right
          (fun bit0 acc =>
            fold_right (fun (_ : Z * Z) (z : Z) => 1 + z) 0
              (selected bit0) + acc) 0 bits =
       Z.of_nat (List.length
         (selected bit ++ concat (map selected bits)))).
    rewrite fold_ones_length__solver_choice_loop.
    rewrite app_length, Nat2Z.inj_add, IH. reflexivity.
  }
  change
    (fold_right
      (fun bit acc =>
        fold_right (fun (_ : Z * Z) (z : Z) => 1 + z) 0
          (selected bit) + acc)
      0 bits <= Zlength segment * Zlength segment).
  rewrite Hfold.
  assert (Hpairslen : Z.of_nat (List.length pairs) =
      Zlength segment * Zlength segment).
  {
    assert (Hprod : forall (xs ys : list Z),
      List.length (list_prod xs ys) =
        (List.length xs * List.length ys)%nat).
    { intros xs ys. induction xs as [|z xs IH]; simpl; [reflexivity |].
      rewrite app_length, length_map, IH. lia. }
    assert (Haux : forall low m, List.length (Zrange_aux low m) = m).
    { intros low m. revert low. induction m; intros; simpl; congruence. }
    unfold pairs, finite_index_pair.
    change (Z.of_nat (List.length
      (list_prod (Zrange 0 (Zlength segment))
        (Zrange 0 (Zlength segment)))) =
      Zlength segment * Zlength segment).
    rewrite Hprod.
    unfold Zrange.
    rewrite !Haux, Nat2Z.inj_mul, !Z2Nat.id by
      (pose proof (Zlength_nonneg segment); lia).
    ring.
  }
  rewrite <- Hpairslen.
  apply Nat2Z.inj_le.
  apply NoDup_incl_length.
  - assert (Hnodup : forall bs,
      incl bs bits ->
      NoDup bs -> NoDup (concat (map selected bs))).
    {
      intros bs Hincl Hbs. induction Hbs as [|bit bs' Hnotin Hbits IH].
      - constructor.
      - simpl. apply NoDup_app.
        + apply enum_nodup.
        + apply IH. intros z Hz. apply Hincl. right. exact Hz.
        + intros p Hp Htail.
          apply in_concat in Htail.
          destruct Htail as [ys [Hys Hpys]].
          apply in_map_iff in Hys.
          destruct Hys as [bit' [Hys Hbit']]. subst ys.
          assert (Hbneq : bit <> bit') by
            (intro Heq; subst bit'; contradiction).
          assert (Hbitrange : 0 <= bit < next).
          { apply (proj2 (@enum_ok Z (fun z : Z => 0 <= z < next)
                (finite_Z_range 0 next) bit)).
            unfold bits. apply Hincl. left. reflexivity. }
          assert (Hbit'range : 0 <= bit' < next).
          { apply (proj2 (@enum_ok Z (fun z : Z => 0 <= z < next)
                (finite_Z_range 0 next) bit')).
            unfold bits. apply Hincl. right. exact Hbit'. }
          apply (proj2 (enum_ok p)) in Hp.
          apply (proj2 (enum_ok p)) in Hpys.
          destruct Hp as [_ Hp]. destruct Hpys as [_ Hpys].
          destruct (prop_dec (CostAt costs bit 1 < CostAt costs bit 0));
          destruct (prop_dec (CostAt costs bit' 1 < CostAt costs bit' 0)).
          all: first
            [ pose proof (chosen_contribution_unique_bit__solver_choice_loop
                segment bit bit' 1 1 p ltac:(lia) ltac:(lia) Hp Hpys)
            | pose proof (chosen_contribution_unique_bit__solver_choice_loop
                segment bit bit' 1 0 p ltac:(lia) ltac:(lia) Hp Hpys)
            | pose proof (chosen_contribution_unique_bit__solver_choice_loop
                segment bit bit' 0 1 p ltac:(lia) ltac:(lia) Hp Hpys)
            | pose proof (chosen_contribution_unique_bit__solver_choice_loop
                segment bit bit' 0 0 p ltac:(lia) ltac:(lia) Hp Hpys) ]; contradiction.
    }
    apply Hnodup.
    + intros z Hz. exact Hz.
    + apply enum_nodup.
  - intros p Hp.
    apply in_concat in Hp.
    destruct Hp as [ys [Hys Hpys]].
    apply in_map_iff in Hys.
    destruct Hys as [bit [Hys Hbit]]. subst ys.
    apply (proj1 (enum_ok p)).
    apply (proj2 (enum_ok p)) in Hpys.
    exact (proj1 Hpys).
Qed.
Lemma fold_filter_powers_bound__solver_choice_loop :
  forall n start (P : Z -> Prop),
    0 <= start ->
    0 <= fold_right (fun bit acc => 2 ^ bit + acc) 0
      (filter (fun bit => if prop_dec (P bit) then true else false)
        (Zrange_aux start n)) <=
      2 ^ (start + Z.of_nat n) - 2 ^ start.
Proof.
  induction n as [|n IH]; intros start P Hstart.
  - simpl. replace (start + 0) with start by lia. lia.
  - simpl Zrange_aux.
    destruct (prop_dec (P start)) as [HP | HP] eqn:Hdec;
      simpl; rewrite Hdec; simpl.
    + specialize (IH (start + 1) P ltac:(lia)).
      pose proof (Nat2Z.inj_succ n) as Hsucc.
      change (Z.pos (Pos.of_succ_nat n) = Z.succ (Z.of_nat n)) in Hsucc.
      rewrite Hsucc.
      replace (start + Z.succ (Z.of_nat n)) with
        ((start + 1) + Z.of_nat n) by lia.
      replace (2 ^ (start + 1)) with (2 * 2 ^ start) in IH.
      2: { rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. ring. }
      assert (0 <= 2 ^ start) by (apply Z.pow_nonneg; lia).
      nia.
    + specialize (IH (start + 1) P ltac:(lia)).
      pose proof (Nat2Z.inj_succ n) as Hsucc.
      change (Z.pos (Pos.of_succ_nat n) = Z.succ (Z.of_nat n)) in Hsucc.
      rewrite Hsucc.
      replace (start + Z.succ (Z.of_nat n)) with
        ((start + 1) + Z.of_nat n) by lia.
      replace (2 ^ (start + 1)) with (2 * 2 ^ start) in IH.
      2: { rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. ring. }
      assert (0 <= 2 ^ start) by (apply Z.pow_nonneg; lia).
      nia.
Qed.
Lemma filtered_power_sum_bound__solver_choice_loop :
  forall b (P : Z -> Prop),
    0 <= b ->
    0 <= SumLib.Sum.sum (fun bit => 0 <= bit < b /\ P bit)
      (fun bit => 2 ^ bit) < 2 ^ b.
Proof.
  intros b P Hb.
  unfold SumLib.Sum.sum.
  change (0 <= fold_right (fun bit acc => 2 ^ bit + acc) 0
      (filter (fun bit => if prop_dec (P bit) then true else false)
        (Zrange 0 b)) < 2 ^ b).
  unfold Zrange.
  replace (b - 0) with b by lia.
  pose proof (fold_filter_powers_bound__solver_choice_loop
    (Z.to_nat b) 0 P ltac:(lia)) as Hbound.
  rewrite Z2Nat.id in Hbound by lia.
  simpl in Hbound.
  assert (0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  destruct Hbound as [Hlower Hupper].
  split; [exact Hlower |].
  replace (0 + b) with b in Hupper by lia.
  change (2 ^ 0) with 1 in Hupper.
  assert (Hstep : 2 ^ b - 1 < 2 ^ b) by lia.
  exact (Z.le_lt_trans _ _ _ Hupper Hstep).
Qed.
Lemma xor_choice_prefix_bounds__solver_choice_loop :
  forall input costs next inv x,
    XorChoicePrefix input costs next inv x ->
    0 <= next <= 30 ->
    0 <= inv <= Zlength input * Zlength input /\
    0 <= x < 2 ^ next.
Proof.
  intros input costs next inv x [Htable [Hinv Hx]] Hnext.
  split.
  - assert (Hnonneg :
      0 <= SumLib.Sum.sum (fun bit : Z => 0 <= bit < next)
        (fun bit => Z.min (CostAt costs bit 0) (CostAt costs bit 1))).
    { apply SumLib.Sum.sum_nonneg. intros bit Hbit.
      unfold CostTable in Htable.
      destruct Htable as [_ [_ Hcontrib]].
      pose proof (Hcontrib bit 0 ltac:(lia) ltac:(lia)) as H0.
      pose proof (Hcontrib bit 1 ltac:(lia) ltac:(lia)) as H1.
      unfold BitContribution in H0, H1.
      assert (HB0 : 0 <= CostAt costs bit 0).
      { rewrite H0. unfold set_card, SumLib.Sum.sum.
        rewrite fold_ones_length__solver_choice_loop. lia. }
      assert (HB1 : 0 <= CostAt costs bit 1).
      { rewrite H1. unfold set_card, SumLib.Sum.sum.
        rewrite fold_ones_length__solver_choice_loop. lia. }
      lia. }
    pose proof (chosen_contribution_sum_bound__solver_choice_loop
      input costs next Hnext) as Hupper.
    assert (Heq :
      SumLib.Sum.sum (fun bit : Z => 0 <= bit < next)
        (fun bit => Z.min (CostAt costs bit 0) (CostAt costs bit 1)) =
      SumLib.Sum.sum (fun bit : Z => 0 <= bit < next)
        (fun bit => #(fun p : Z * Z =>
          (0 <= fst p < Zlength input /\ 0 <= snd p < Zlength input) /\
          if prop_dec (CostAt costs bit 1 < CostAt costs bit 0)
          then fst p < snd p /\ SameHigherBits input 29 bit (fst p) (snd p) /\
            (1 = 0 /\ BitAt (Znth (fst p) input 0) bit = 1 /\
                     BitAt (Znth (snd p) input 0) bit = 0 \/
             1 = 1 /\ BitAt (Znth (fst p) input 0) bit = 0 /\
                     BitAt (Znth (snd p) input 0) bit = 1)
          else fst p < snd p /\ SameHigherBits input 29 bit (fst p) (snd p) /\
            (0 = 0 /\ BitAt (Znth (fst p) input 0) bit = 1 /\
                     BitAt (Znth (snd p) input 0) bit = 0 \/
             0 = 1 /\ BitAt (Znth (fst p) input 0) bit = 0 /\
                     BitAt (Znth (snd p) input 0) bit = 1)))).
    { apply SumLib.Sum.sum_ext. intros bit Hbit.
      apply chosen_contribution_cost_card__solver_choice_loop.
      - exact Htable.
      - lia. }
    rewrite Heq in Hnonneg.
    rewrite Heq in Hinv.
    lia.
  - rewrite Hx.
    apply filtered_power_sum_bound__solver_choice_loop.
    lia.
Qed.
Lemma set_card_as_Zlength__solver_choice_loop :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    @set_card A P FP = Z.of_nat (List.length (@enum A P FP)).
Proof.
  intros A P FP. unfold set_card, SumLib.Sum.sum.
  apply fold_ones_length__solver_choice_loop.
Qed.
Lemma set_card_nonnegative__solver_choice_loop :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    0 <= @set_card A P FP.
Proof.
  intros A P FP. rewrite set_card_as_Zlength__solver_choice_loop. lia.
Qed.
Lemma set_card_subset_le__solver_choice_loop :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x -> Q x) ->
    @set_card A P FP <= @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hsub.
  rewrite !set_card_as_Zlength__solver_choice_loop.
  apply Nat2Z.inj_le.
  apply NoDup_incl_length.
  - exact (@enum_nodup A P FP).
  - intros x Hx.
    apply (proj1 (@enum_ok A Q FQ x)), Hsub.
    apply (proj2 (@enum_ok A P FP x)); exact Hx.
Qed.
Lemma set_card_product__solver_choice_loop :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q),
    @set_card (A * B) (fun p => P (fst p) /\ Q (snd p))
      (@Finite_prod A B P Q FP FQ) =
    @set_card A P FP * @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ.
  rewrite !set_card_as_Zlength__solver_choice_loop.
  assert (Hprod : forall (xs : list A) (ys : list B),
    List.length (list_prod xs ys) =
      (List.length xs * List.length ys)%nat).
  { intros xs ys. induction xs as [|x xs IH]; simpl; [reflexivity |].
    rewrite app_length, length_map, IH. lia. }
  change (Z.of_nat (List.length
      (list_prod (@enum A P FP) (@enum B Q FQ))) =
    Z.of_nat (List.length (@enum A P FP)) *
      Z.of_nat (List.length (@enum B Q FQ))).
  rewrite Hprod, Nat2Z.inj_mul. reflexivity.
Qed.
Lemma Zrange_aux_length__solver_choice_loop :
  forall low m, List.length (Zrange_aux low m) = m.
Proof.
  intros low m. revert low. induction m; intros; simpl; congruence.
Qed.
Lemma set_card_Z_range__solver_choice_loop :
  forall low high, low <= high ->
    @set_card Z (fun z => low <= z < high) (finite_Z_range low high) =
      high - low.
Proof.
  intros low high Hrange.
  rewrite set_card_as_Zlength__solver_choice_loop.
  change (Z.of_nat (List.length (Zrange low high)) = high - low).
  unfold Zrange.
  rewrite Zrange_aux_length__solver_choice_loop, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma set_card_bounded_pairs__solver_choice_loop :
  forall n, 0 <= n ->
    #(fun p : Z * Z =>
      0 <= fst p < n /\ 0 <= snd p < n) = n * n.
Proof.
  intros n Hn.
  change
    (@set_card (Z * Z)
      (fun p : Z * Z =>
        0 <= fst p < n /\ 0 <= snd p < n)
      (finite_index_pair n) = n * n).
  unfold finite_index_pair.
  rewrite (@set_card_product__solver_choice_loop
    Z Z
    (fun x : Z => 0 <= x < n)
    (fun x : Z => 0 <= x < n)
    (finite_Z_range 0 n) (finite_Z_range 0 n)).
  rewrite !set_card_Z_range__solver_choice_loop by lia.
  ring.
Qed.
Lemma bit_contribution_pair_bound__solver_choice_loop :
  forall segment upper bit choice count,
    BitContribution segment upper bit choice count ->
    0 <= count <= Zlength segment * Zlength segment.
Proof.
  intros segment upper bit choice count Hcontrib.
  unfold BitContribution in Hcontrib.
  subst count.
  split.
  - apply set_card_nonnegative__solver_choice_loop.
  - eapply Z.le_trans.
    + apply set_card_subset_le__solver_choice_loop.
      intros p Hp. exact (proj1 Hp).
    + rewrite set_card_bounded_pairs__solver_choice_loop by
        apply Zlength_nonneg.
      lia.
Qed.
Lemma sum_Z_range_filter_extend_right__solver_choice_loop :
  forall low high (P : Z -> Prop) f,
    low <= high ->
    SumLib.Sum.sum (fun z => low <= z < high + 1 /\ P z) f =
    SumLib.Sum.sum (fun z => low <= z < high /\ P z) f +
      if prop_dec (P high) then f high else 0.
Proof.
  intros low high P f Hrange.
  unfold SumLib.Sum.sum.
  change
    (fold_right (fun z acc => f z + acc) 0
       (filter (fun z => if prop_dec (P z) then true else false)
          (Zrange low (high + 1))) =
     fold_right (fun z acc => f z + acc) 0
       (filter (fun z => if prop_dec (P z) then true else false)
          (Zrange low high)) +
       if prop_dec (P high) then f high else 0).
  unfold Zrange.
  replace (Z.to_nat (high + 1 - low)) with
    (Z.to_nat (high - low) + 1)%nat by lia.
  rewrite Zrange_aux_app.
  replace (low + Z.of_nat (Z.to_nat (high - low))) with high by lia.
  rewrite filter_app, fold_Zsum_app.
  simpl.
  destruct (prop_dec (P high)); simpl; ring.
Qed.
Lemma xor_choice_prefix_step_one__solver_choice_loop :
  forall input costs b inv x,
    XorChoicePrefix input costs b inv x ->
    0 <= b < 30 ->
    CostAt costs b 1 < CostAt costs b 0 ->
    XorChoicePrefix input costs (b + 1)
      (inv + CostAt costs b 1) (x + 2 ^ b).
Proof.
  intros input costs b inv x [Htable [Hinv Hx]] Hb Hchoice.
  unfold XorChoicePrefix.
  split; [exact Htable | split].
  - rewrite Hinv.
    rewrite (sum_Z_range_extend_right 0 b) by lia.
    rewrite Z.min_r by lia.
    reflexivity.
  - rewrite Hx.
    rewrite (sum_Z_range_filter_extend_right__solver_choice_loop
      0 b (fun bit => CostAt costs bit 1 < CostAt costs bit 0)
      (fun bit => 2 ^ bit)) by lia.
    destruct (prop_dec (CostAt costs b 1 < CostAt costs b 0));
      [ring | contradiction].
Qed.
Lemma xor_choice_prefix_step_zero__solver_choice_loop :
  forall input costs b inv x,
    XorChoicePrefix input costs b inv x ->
    0 <= b < 30 ->
    CostAt costs b 0 <= CostAt costs b 1 ->
    XorChoicePrefix input costs (b + 1)
      (inv + CostAt costs b 0) x.
Proof.
  intros input costs b inv x [Htable [Hinv Hx]] Hb Hchoice.
  unfold XorChoicePrefix.
  split; [exact Htable | split].
  - rewrite Hinv.
    rewrite (sum_Z_range_extend_right 0 b) by lia.
    rewrite Z.min_l by lia.
    reflexivity.
  - rewrite Hx.
    rewrite (sum_Z_range_filter_extend_right__solver_choice_loop
      0 b (fun bit => CostAt costs bit 1 < CostAt costs bit 0)
      (fun bit => 2 ^ bit)) by lia.
    destruct (prop_dec (CostAt costs b 1 < CostAt costs b 0));
      [lia | ring].
Qed.
Lemma bit_mask_singleton_bounds__solver_choice_loop :
  forall x b,
    0 <= b < 30 ->
    0 <= x < 2 ^ b ->
    signed_last_nbits (Z.shiftl 1 b) 32 = 2 ^ b /\
    Z.lor x (signed_last_nbits (Z.shiftl 1 b) 32) = x + 2 ^ b /\
    0 <= Z.lor x (signed_last_nbits (Z.shiftl 1 b) 32) < 1073741824.
Proof.
  intros x b Hb Hx.
  assert (Hpow_nonneg : 0 <= 2 ^ b) by (apply Z.pow_nonneg; lia).
  assert (Hpow_lt : 2 ^ b < 2 ^ 30).
  { apply Z.pow_lt_mono_r; lia. }
  assert (Hsigned : signed_last_nbits (Z.shiftl 1 b) 32 = 2 ^ b).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mul_1_l.
    apply signed_last_nbits_eq.
    - lia.
    - split.
      + assert (0 < 2 ^ 31) by (apply Z.pow_pos_nonneg; lia). lia.
      + eapply Z.lt_trans; [exact Hpow_lt |].
        apply Z.pow_lt_mono_r; lia. }
  assert (Hland : Z.land x (2 ^ b) = 0).
  { apply Z.bits_inj'. intros m Hm.
    rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec b m) as [-> | Hne].
    - rewrite Z.pow2_bits_true by lia.
      rewrite (proj2 (Z.testbit_false x m ltac:(lia))).
      + reflexivity.
      + replace (x / 2 ^ m) with 0 by
          (symmetry; apply Z.div_small; lia).
        reflexivity.
    - rewrite Z.pow2_bits_false by lia.
      destruct (Z.testbit x m); reflexivity. }
  split; [exact Hsigned |].
  rewrite Hsigned.
  assert (Hlor : Z.lor x (2 ^ b) = x + 2 ^ b).
  { pose proof (Z.add_lor_land x (2 ^ b)) as Hadd.
    rewrite Hland in Hadd. lia. }
  split; [exact Hlor |].
  rewrite Hlor.
  assert (Htwopow : 2 * 2 ^ b = 2 ^ (b + 1)).
  { rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. ring. }
  assert (Hnextpow : 2 ^ (b + 1) <= 2 ^ 30).
  { apply Z.pow_le_mono_r; lia. }
  change (2 ^ 30) with 1073741824 in Hpow_lt.
  change (2 ^ 30) with 1073741824 in Hnextpow.
  nia.
Qed.
Lemma set_card_extensional__solver_final :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros x.
      rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
            1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma finite_sum_subset_as_cond__solver_final :
  forall {A : Type} (base extra : A -> Prop)
    (FB : Finite base) (FS : Finite (fun x => base x /\ extra x))
    (f : A -> Z),
    @SumLib.Sum.sum A (fun x => base x /\ extra x) FS f =
    @SumLib.Sum.sum A base FB
      (fun x => if prop_dec (extra x) then f x else 0).
Proof.
  intros A base extra FB FS f.
  unfold SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A (fun x => base x /\ extra x) FS)
    (filter (fun x => if prop_dec (extra x) then true else false)
      (@enum A base FB))).
  {
    apply NoDup_Permutation.
    - apply enum_nodup.
    - apply NoDup_filter_bool. apply enum_nodup.
    - intros x. rewrite filter_In.
      rewrite <- (@enum_ok A (fun x => base x /\ extra x) FS x).
      rewrite <- (@enum_ok A base FB x).
      destruct (prop_dec (extra x)) as [Hextra | Hextra]; simpl.
      + tauto.
      + split.
        * intros [_ Hbad]. contradiction.
        * intros [_ Hbad]. discriminate.
  }
  assert (Hfoldperm :
    fold_right (fun x acc => f x + acc) 0
      (@enum A (fun x => base x /\ extra x) FS) =
    fold_right (fun x acc => f x + acc) 0
      (filter (fun x => if prop_dec (extra x) then true else false)
        (@enum A base FB))).
  {
    induction Hperm.
    - reflexivity.
    - simpl. rewrite IHHperm. reflexivity.
    - simpl. ring.
    - etransitivity; eassumption.
  }
  rewrite Hfoldperm. clear Hperm Hfoldperm FS.
  induction (@enum A base FB) as [|x xs IH]; [reflexivity |].
  destruct (prop_dec (extra x)) as [Hextra | Hextra] eqn:Hdec;
    cbn [filter fold_right]; rewrite Hdec; simpl; rewrite IH; reflexivity.
Qed.
Lemma finite_sum_predicate_extensional__solver_final :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q)
    (f : A -> Z),
    (forall x, P x <-> Q x) ->
    @SumLib.Sum.sum A P FP f = @SumLib.Sum.sum A Q FQ f.
Proof.
  intros A P Q FP FQ f Hequiv.
  unfold SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros x.
      rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - simpl. rewrite IHHperm. reflexivity.
  - simpl. ring.
  - etransitivity; eassumption.
Qed.
Lemma bit_at_testbit__solver_final :
  forall value bit, 0 <= bit ->
    BitAt value bit = Z.b2z (Z.testbit value bit).
Proof.
  intros value bit Hbit.
  unfold BitAt.
  replace 1 with (Z.ones 1) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  symmetry. apply Z.testbit_spec'; lia.
Qed.
Lemma binary_mask_monotone__solver_final :
  forall n (P Q : Z -> Prop),
    (forall bit, 0 <= bit < n -> P bit -> Q bit) ->
    @SumLib.Sum.sum Z (fun bit => 0 <= bit < n /\ P bit)
      (finite_Z_range' 0 n P) (fun bit => 2 ^ bit) <=
    @SumLib.Sum.sum Z (fun bit => 0 <= bit < n /\ Q bit)
      (finite_Z_range' 0 n Q) (fun bit => 2 ^ bit).
Proof.
  intros n P Q Hsub.
  rewrite (finite_sum_subset_as_cond__solver_final
    (fun bit : Z => 0 <= bit < n) P
    (finite_Z_range 0 n) (finite_Z_range' 0 n P)).
  rewrite (finite_sum_subset_as_cond__solver_final
    (fun bit : Z => 0 <= bit < n) Q
    (finite_Z_range 0 n) (finite_Z_range' 0 n Q)).
  apply sum_Z_range_le. intros bit Hbit.
  destruct (prop_dec (P bit)) as [HP | HNP];
    destruct (prop_dec (Q bit)) as [HQ | HNQ]; simpl;
    try lia; exfalso; eauto.
Qed.
Lemma binary_mask_spec__solver_final :
  forall (n : nat) (P : Z -> Prop),
    let mask := @SumLib.Sum.sum Z
      (fun bit : Z => 0 <= bit < Z.of_nat n /\ P bit)
      (finite_Z_range' 0 (Z.of_nat n) P)
      (fun bit => 2 ^ bit) in
    0 <= mask < 2 ^ Z.of_nat n /\
    forall bit, 0 <= bit < Z.of_nat n ->
      BitAt mask bit = if prop_dec (P bit) then 1 else 0.
Proof.
  induction n as [|n IH]; intros P; cbn [Z.of_nat].
  - rewrite (finite_sum_subset_as_cond__solver_final
      (fun bit : Z => 0 <= bit < 0) P
      (finite_Z_range 0 0) (finite_Z_range' 0 0 P)).
    rewrite sum_Z_range_empty by lia. cbn.
    split; [lia |]. intros bit Hbit. lia.
  - set (N := Z.of_nat n).
    replace (Z.pos (Pos.of_succ_nat n)) with (N + 1)
      by (unfold N; lia).
    set (tail := @SumLib.Sum.sum Z
      (fun bit : Z => 0 <= bit < N /\ P (bit + 1))
      (finite_Z_range' 0 N (fun bit => P (bit + 1)))
      (fun bit => 2 ^ bit)).
    assert (Hmask :
      @SumLib.Sum.sum Z (fun bit : Z => 0 <= bit < N + 1 /\ P bit)
        (finite_Z_range' 0 (N + 1) P)
        (fun bit => 2 ^ bit) =
      (if prop_dec (P 0) then 1 else 0) + 2 * tail).
    {
      rewrite (finite_sum_subset_as_cond__solver_final
        (fun bit : Z => 0 <= bit < N + 1) P
        (finite_Z_range 0 (N + 1)) (finite_Z_range' 0 (N + 1) P)).
      rewrite sum_Z_range_cons by lia.
      rewrite sum_Z_range_shift_1.
      unfold tail.
      rewrite (finite_sum_subset_as_cond__solver_final
        (fun bit : Z => 0 <= bit < N) (fun bit => P (bit + 1))
        (finite_Z_range 0 N)
        (finite_Z_range' 0 N (fun bit => P (bit + 1)))).
      apply f_equal2; [destruct (prop_dec (P 0)); reflexivity |].
      transitivity (SumLib.Sum.sum (fun bit : Z => 0 <= bit < N)
        (fun bit => 2 *
          (if prop_dec (P (bit + 1)) then 2 ^ bit else 0))).
      - apply sum_Z_range_ext. intros bit Hbit.
        replace (1 + bit) with (bit + 1) by lia.
        destruct (prop_dec (P (bit + 1))); simpl.
        + replace (bit + 1) with (Z.succ bit) by lia.
          rewrite Z.pow_succ_r by lia. reflexivity.
        + reflexivity.
      - rewrite sum_Z_range_factor_l. reflexivity.
    }
    change (0 <= @SumLib.Sum.sum Z
      (fun bit : Z => 0 <= bit < N + 1 /\ P bit)
      (finite_Z_range' 0 (N + 1) P)
      (fun bit => 2 ^ bit) < 2 ^ (N + 1) /\
      forall bit, 0 <= bit < N + 1 ->
        BitAt (@SumLib.Sum.sum Z
          (fun bit0 : Z => 0 <= bit0 < N + 1 /\ P bit0)
          (finite_Z_range' 0 (N + 1) P)
          (fun bit0 => 2 ^ bit0)) bit =
        (if prop_dec (P bit) then 1 else 0)).
    rewrite Hmask.
    specialize (IH (fun bit => P (bit + 1))).
    cbn zeta in IH. fold tail in IH.
    destruct IH as (Htail & IHbits).
    assert (Htail' : 0 <= tail < 2 ^ N).
    { unfold tail, N. exact Htail. }
    split.
    + replace (2 ^ (N + 1)) with (2 ^ N * 2).
      2: { replace (N + 1) with (Z.succ N) by lia.
           rewrite Z.pow_succ_r by lia. ring. }
      destruct (prop_dec (P 0)) eqn:Hdec; split;
        pose proof (Z.pow_pos_nonneg 2 N ltac:(lia) ltac:(lia)); lia.
    + intros bit Hbit.
      destruct (Z.eq_dec bit 0) as [-> | Hbit0].
      * rewrite bit_at_testbit__solver_final by lia.
        destruct (prop_dec (P 0));
          rewrite Z.testbit_odd, Z.shiftr_0_r, Z.odd_add, Z.odd_mul;
          cbn; reflexivity.
      * assert (Hbitpos : 0 < bit) by lia.
        set (k := bit - 1).
        assert (Hk : 0 <= k < N) by (unfold k; lia).
        replace bit with (k + 1) by (unfold k; lia).
        rewrite !bit_at_testbit__solver_final by lia.
        rewrite <- (Z.shiftr_spec
          ((if prop_dec (P 0) then 1 else 0) + 2 * tail) 1 k) by lia.
        assert (Hshift :
          Z.shiftr ((if prop_dec (P 0) then 1 else 0) + 2 * tail) 1 = tail).
        {
          rewrite Z.shiftr_div_pow2 by lia. cbn [Z.pow].
          destruct (prop_dec (P 0)).
          - symmetry. apply Z.div_unique with (r := 1); lia.
          - symmetry. apply Z.div_unique with (r := 0); lia.
        }
        rewrite Hshift.
        rewrite <- !bit_at_testbit__solver_final by lia.
        apply IHbits. exact Hk.
Qed.
Lemma set_card_subset_as_sum__solver_final :
  forall {A : Type} (base extra : A -> Prop)
    (FB : Finite base) (FS : Finite (fun x => base x /\ extra x)),
    @set_card A (fun x => base x /\ extra x) FS =
    @SumLib.Sum.sum A base FB
      (fun x => if prop_dec (extra x) then 1 else 0).
Proof.
  intros A base extra FB FS.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A (fun x => base x /\ extra x) FS)
    (filter (fun x => if prop_dec (extra x) then true else false)
      (@enum A base FB))).
  {
    apply NoDup_Permutation.
    - apply enum_nodup.
    - apply NoDup_filter_bool. apply enum_nodup.
    - intros x. rewrite filter_In.
      rewrite <- (@enum_ok A (fun x => base x /\ extra x) FS x).
      rewrite <- (@enum_ok A base FB x).
      destruct (prop_dec (extra x)) as [Hextra | Hextra]; simpl.
      + tauto.
      + split.
        * intros [_ Hbad]. contradiction.
        * intros [_ Hbad]. discriminate.
  }
  assert (Hfoldperm :
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0
      (@enum A (fun x => base x /\ extra x) FS) =
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0
      (filter (fun x => if prop_dec (extra x) then true else false)
        (@enum A base FB))).
  {
    induction Hperm.
    - reflexivity.
    - change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
              1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l').
      f_equal. exact IHHperm.
    - simpl. lia.
    - etransitivity; eassumption.
  }
  rewrite Hfoldperm. clear Hperm Hfoldperm FS.
  induction (@enum A base FB) as [|x xs IH]; [reflexivity |].
  destruct (prop_dec (extra x)) as [Hextra | Hextra] eqn:Hdec.
  - cbn [filter fold_right]. rewrite Hdec.
    change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0
              (filter (fun y => if prop_dec (extra y) then true else false) xs) =
            1 + fold_right (fun y acc =>
              (if prop_dec (extra y) then 1 else 0) + acc) 0 xs).
    f_equal. exact IH.
  - cbn [filter fold_right]. rewrite Hdec.
    change (fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0
              (filter (fun y => if prop_dec (extra y) then true else false) xs) =
            fold_right (fun y acc =>
              (if prop_dec (extra y) then 1 else 0) + acc) 0 xs).
    exact IH.
Qed.
Lemma finite_sum_swap__solver_final :
  forall {A B : Type} (PA : A -> Prop) (PB : B -> Prop)
    (FA : Finite PA) (FB : Finite PB) (f : A -> B -> Z),
    @SumLib.Sum.sum A PA FA
      (fun a => @SumLib.Sum.sum B PB FB (fun b => f a b)) =
    @SumLib.Sum.sum B PB FB
      (fun b => @SumLib.Sum.sum A PA FA (fun a => f a b)).
Proof.
  intros A B PA PB FA FB f.
  unfold SumLib.Sum.sum.
  induction (@enum A PA FA) as [|a xs IH]; simpl.
  - induction (@enum B PB FB); simpl; [reflexivity |]. exact IHl.
  - rewrite IH. clear IH.
    induction (@enum B PB FB) as [|b ys IH]; simpl; [reflexivity |].
    rewrite <- IH. ring.
Qed.
Lemma lxor_cancel_common__solver_final :
  forall a c x,
    Z.lxor (Z.lxor a x) (Z.lxor c x) = Z.lxor a c.
Proof.
  intros a c x.
  apply Z.bits_inj'. intros bit Hbit.
  repeat rewrite Z.lxor_spec.
  destruct (Z.testbit a bit), (Z.testbit c bit), (Z.testbit x bit);
    reflexivity.
Qed.
Lemma lxor_bounded_30__solver_final :
  forall a c,
    0 <= a < 2 ^ 30 -> 0 <= c < 2 ^ 30 ->
    0 <= Z.lxor a c < 2 ^ 30.
Proof.
  intros a c Ha Hc.
  split.
  - apply Z.lxor_nonneg. tauto.
  - destruct (Z.eq_dec a 0) as [-> | Ha0].
    + rewrite Z.lxor_0_l. lia.
    + destruct (Z.eq_dec c 0) as [-> | Hc0].
      * rewrite Z.lxor_0_r. lia.
      * apply Z.log2_lt_cancel.
        rewrite Z.log2_pow2 by lia.
        eapply Z.le_lt_trans.
        -- apply Z.log2_lxor; lia.
        -- apply Z.max_lub_lt.
           ++ apply (proj1 (Z.log2_lt_pow2 a 30 ltac:(lia))); lia.
           ++ apply (proj1 (Z.log2_lt_pow2 c 30 ltac:(lia))); lia.
Qed.
Lemma highest_diff_bit__solver_final :
  forall a c,
    0 <= a < 2 ^ 30 -> 0 <= c < 2 ^ 30 -> a <> c ->
    let bit := Z.log2 (Z.lxor a c) in
    0 <= bit < 30 /\
    Z.testbit a bit <> Z.testbit c bit /\
    forall k, bit < k -> Z.testbit a k = Z.testbit c k.
Proof.
  intros a c Ha Hc Hneq. cbn zeta.
  pose proof (lxor_bounded_30__solver_final a c Ha Hc) as Hd.
  assert (Hd0 : Z.lxor a c <> 0).
  { intro Hzero. apply Hneq. apply Z.lxor_eq. exact Hzero. }
  assert (Hdpos : 0 < Z.lxor a c) by lia.
  split.
  - split; [apply Z.log2_nonneg |].
    apply (proj1 (Z.log2_lt_pow2 (Z.lxor a c) 30 ltac:(lia))). lia.
  - split.
    + assert (Htop : Z.testbit (Z.lxor a c) (Z.log2 (Z.lxor a c)) = true)
        by (apply Z.bit_log2; lia).
      rewrite Z.lxor_spec in Htop.
      destruct (Z.testbit a (Z.log2 (Z.lxor a c))),
        (Z.testbit c (Z.log2 (Z.lxor a c))); simpl in Htop;
        congruence.
    + intros k Hk.
      assert (Hzero : Z.testbit (Z.lxor a c) k = false).
      { apply Z.bits_above_log2; lia. }
      rewrite Z.lxor_spec in Hzero.
      destruct (Z.testbit a k), (Z.testbit c k); simpl in Hzero;
        congruence.
Qed.
Lemma nonnegative_order_by_highest_diff__solver_final :
  forall u v,
    0 <= u -> 0 <= v -> u <> v ->
    let bit := Z.log2 (Z.lxor u v) in
    (u > v <-> Z.testbit u bit = true).
Proof.
  intros u v Hu Hv Hneq. cbn zeta.
  assert (Hd0 : Z.lxor u v <> 0).
  { intro Hzero. apply Hneq. apply Z.lxor_eq. exact Hzero. }
  assert (Hdpos : 0 < Z.lxor u v).
  { assert (Hdnonneg : 0 <= Z.lxor u v).
    { apply Z.lxor_nonneg. split; intros; assumption. }
    lia. }
  set (bit := Z.log2 (Z.lxor u v)).
  assert (Hbit : 0 <= bit) by (unfold bit; apply Z.log2_nonneg).
  assert (Hdiff : Z.testbit u bit <> Z.testbit v bit).
  { assert (Htop : Z.testbit (Z.lxor u v) bit = true).
    { unfold bit. apply Z.bit_log2. lia. }
    rewrite Z.lxor_spec in Htop.
    destruct (Z.testbit u bit), (Z.testbit v bit); simpl in Htop;
      congruence. }
  assert (Hhigher : forall k, bit < k -> Z.testbit u k = Z.testbit v k).
  { intros k Hk.
    assert (Hzero : Z.testbit (Z.lxor u v) k = false).
    { unfold bit in Hk. apply Z.bits_above_log2; lia. }
    rewrite Z.lxor_spec in Hzero.
    destruct (Z.testbit u k), (Z.testbit v k); simpl in Hzero;
      congruence. }
  assert (Hshift : Z.shiftr u (bit + 1) = Z.shiftr v (bit + 1)).
  { apply Z.bits_inj'. intros k Hk.
    rewrite !Z.shiftr_spec by lia.
    apply Hhigher. lia. }
  set (p := 2 ^ bit).
  set (common := Z.shiftr u (bit + 1)).
  assert (Hp : 0 < p) by (unfold p; apply Z.pow_pos_nonneg; lia).
  assert (Hudiv : u / p = 2 * common + Z.b2z (Z.testbit u bit)).
  { pose proof (Z.div2_odd (Z.shiftr u bit)) as Hdec.
    rewrite <- Z.testbit_odd in Hdec.
    rewrite Z.div2_div in Hdec.
    replace 2 with (2 ^ 1) in Hdec by reflexivity.
    rewrite <- Z.shiftr_div_pow2 in Hdec by lia.
    rewrite Z.shiftr_shiftr in Hdec by lia.
    fold common in Hdec.
    unfold p. rewrite <- Z.shiftr_div_pow2 by lia. exact Hdec. }
  assert (Hvdiv : v / p = 2 * common + Z.b2z (Z.testbit v bit)).
  { pose proof (Z.div2_odd (Z.shiftr v bit)) as Hdec.
    rewrite <- Z.testbit_odd in Hdec.
    rewrite Z.div2_div in Hdec.
    replace 2 with (2 ^ 1) in Hdec by reflexivity.
    rewrite <- Z.shiftr_div_pow2 in Hdec by lia.
    rewrite Z.shiftr_shiftr in Hdec by lia.
    rewrite <- Hshift in Hdec.
    fold common in Hdec.
    unfold p. rewrite <- Z.shiftr_div_pow2 by lia. exact Hdec. }
  pose proof (Z.div_mod u p ltac:(lia)) as Hu_dec.
  pose proof (Z.div_mod v p ltac:(lia)) as Hv_dec.
  pose proof (Z.mod_pos_bound u p Hp) as Hu_mod.
  pose proof (Z.mod_pos_bound v p Hp) as Hv_mod.
  destruct (Z.testbit u bit) eqn:Hub;
    destruct (Z.testbit v bit) eqn:Hvb; simpl in *; try contradiction;
    lia.
Qed.
Lemma binary_low_mask_le__solver_final :
  forall y, 0 <= y ->
    @SumLib.Sum.sum Z
      (fun bit : Z => 0 <= bit < 30 /\ BitAt y bit = 1)
      (finite_Z_range' 0 30 (fun bit => BitAt y bit = 1))
      (fun bit => 2 ^ bit) <= y.
Proof.
  intros y Hy.
  pose proof (binary_mask_spec__solver_final 30%nat
    (fun bit => BitAt y bit = 1)) as Hmask.
  cbn [Z.of_nat] in Hmask.
  destruct Hmask as (Hbound & Hbits).
  set (mask := @SumLib.Sum.sum Z
    (fun bit : Z => 0 <= bit < 30 /\ BitAt y bit = 1)
    (finite_Z_range' 0 30 (fun bit => BitAt y bit = 1))
    (fun bit => 2 ^ bit)) in *.
  assert (Hbound' : 0 <= mask < 2 ^ 30).
  { unfold mask. exact Hbound. }
  assert (Hbits' : forall bit, 0 <= bit < 30 ->
    BitAt mask bit =
      if prop_dec (BitAt y bit = 1) then 1 else 0).
  { unfold mask. exact Hbits. }
  destruct (Z_le_gt_dec mask y) as [Hle | Hgt]; [exact Hle |].
  assert (Hybound : 0 <= y < 2 ^ 30) by lia.
  assert (Hneq : mask <> y) by lia.
  pose proof (highest_diff_bit__solver_final mask y Hbound' Hybound Hneq)
    as (Htop & Hdiff & Hhigher).
  set (top := Z.log2 (Z.lxor mask y)) in *.
  pose proof (nonnegative_order_by_highest_diff__solver_final
    mask y ltac:(lia) Hy Hneq) as Horder.
  fold top in Horder.
  assert (Hmaskbit : Z.testbit mask top = true).
  { apply Horder. lia. }
  specialize (Hbits' top Htop).
  rewrite bit_at_testbit__solver_final in Hbits' by lia.
  rewrite Hmaskbit in Hbits'. cbn in Hbits'.
  destruct (prop_dec (BitAt y top = 1)) as [Hybit | Hybit].
  - rewrite bit_at_testbit__solver_final in Hybit by lia.
    destruct (Z.testbit y top); simpl in Hybit; try lia.
    exfalso. apply Hdiff. rewrite Hmaskbit. reflexivity.
  - lia.
Qed.
Lemma xor_order_bit_choice__solver_final :
  forall a c x,
    0 <= a < 2 ^ 30 -> 0 <= c < 2 ^ 30 -> 0 <= x -> a <> c ->
    let bit := Z.log2 (Z.lxor a c) in
    (Z.lxor a x > Z.lxor c x <->
      (BitAt x bit = 0 /\ BitAt a bit = 1 /\ BitAt c bit = 0) \/
      (BitAt x bit = 1 /\ BitAt a bit = 0 /\ BitAt c bit = 1)).
Proof.
  intros a c x Ha Hc Hx Hneq. cbn zeta.
  pose proof (highest_diff_bit__solver_final a c Ha Hc Hneq)
    as (Hbit & Hdiff & Hhigher).
  assert (Hax : 0 <= Z.lxor a x).
  { apply Z.lxor_nonneg. split; intros; lia. }
  assert (Hcx : 0 <= Z.lxor c x).
  { apply Z.lxor_nonneg. split; intros; lia. }
  assert (Haxcx : Z.lxor a x <> Z.lxor c x).
  { intro Heq.
    assert (Hzero : Z.lxor (Z.lxor a x) (Z.lxor c x) = 0).
    { rewrite Heq. apply Z.lxor_nilpotent. }
    rewrite lxor_cancel_common__solver_final in Hzero.
    apply Hneq. apply Z.lxor_eq. exact Hzero. }
  pose proof (nonnegative_order_by_highest_diff__solver_final
    (Z.lxor a x) (Z.lxor c x) Hax Hcx Haxcx) as Hord.
  cbn zeta in Hord.
  rewrite lxor_cancel_common__solver_final in Hord.
  change (Z.lxor a x > Z.lxor c x <->
    Z.testbit (Z.lxor a x) (Z.log2 (Z.lxor a c)) = true) in Hord.
  rewrite Z.lxor_spec in Hord.
  rewrite !bit_at_testbit__solver_final by lia.
  destruct (Z.testbit a (Z.log2 (Z.lxor a c))) eqn:Hab;
    destruct (Z.testbit c (Z.log2 (Z.lxor a c))) eqn:Hcb;
    destruct (Z.testbit x (Z.log2 (Z.lxor a c))) eqn:Hxb;
    simpl in *; intuition congruence.
Qed.
Lemma pair_inversion_bit_partition__solver_final :
  forall input p x,
    (0 <= fst p < Zlength input /\ 0 <= snd p < Zlength input) ->
    (forall i, 0 <= i < Zlength input ->
      0 <= Znth i input 0 <= 1000000000) ->
    0 <= x ->
    SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
      (fun bit =>
        if prop_dec
          (SameHigherBits input 29 bit (fst p) (snd p) /\
           ((BitAt x bit = 0 /\ BitAt (Znth (fst p) input 0) bit = 1 /\
                              BitAt (Znth (snd p) input 0) bit = 0) \/
            (BitAt x bit = 1 /\ BitAt (Znth (fst p) input 0) bit = 0 /\
                              BitAt (Znth (snd p) input 0) bit = 1)))
        then 1 else 0) =
    if prop_dec
      (Z.lxor (Znth (fst p) input 0) x >
       Z.lxor (Znth (snd p) input 0) x)
    then 1 else 0.
Proof.
  intros input [i j] x [[Hi0 Hi] [Hj0 Hj]] Hvals Hx. simpl in *.
  set (a := Znth i input 0).
  set (c := Znth j input 0).
  specialize (Hvals i ltac:(lia)) as Ha0.
  specialize (Hvals j ltac:(lia)) as Hc0.
  assert (Ha : 0 <= a < 2 ^ 30) by (unfold a; change (2 ^ 30) with 1073741824; lia).
  assert (Hc : 0 <= c < 2 ^ 30) by (unfold c; change (2 ^ 30) with 1073741824; lia).
  destruct (Z.eq_dec a c) as [Heq | Hneq].
  - assert (Hzero : SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
        (fun bit =>
          if prop_dec
            (SameHigherBits input 29 bit i j /\
             ((BitAt x bit = 0 /\ BitAt a bit = 1 /\ BitAt c bit = 0) \/
              (BitAt x bit = 1 /\ BitAt a bit = 0 /\ BitAt c bit = 1)))
          then 1 else 0) = 0).
    { apply sum_Z_range_eq_zero. intros bit Hbit.
      destruct (prop_dec
        (SameHigherBits input 29 bit i j /\
         ((BitAt x bit = 0 /\ BitAt a bit = 1 /\ BitAt c bit = 0) \/
          (BitAt x bit = 1 /\ BitAt a bit = 0 /\ BitAt c bit = 1))))
        as [[_ Hcases] | Hnot]; [|reflexivity].
      rewrite Heq in Hcases. destruct Hcases as [(_ & H1 & H0) | (_ & H0 & H1)];
        lia. }
    change (SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
      (fun bit =>
        if prop_dec
          (SameHigherBits input 29 bit i j /\
           ((BitAt x bit = 0 /\ BitAt a bit = 1 /\ BitAt c bit = 0) \/
            (BitAt x bit = 1 /\ BitAt a bit = 0 /\ BitAt c bit = 1)))
        then 1 else 0) =
      (if prop_dec (Z.lxor a x > Z.lxor c x) then 1 else 0)).
    rewrite Hzero, Heq.
    destruct (prop_dec (Z.lxor c x > Z.lxor c x)); [lia | reflexivity].
  - pose proof (highest_diff_bit__solver_final a c Ha Hc Hneq)
      as (Hbit & Hdiff & Hhigher).
    set (top := Z.log2 (Z.lxor a c)) in *.
    assert (Hsame : SameHigherBits input 29 top i j).
    { intros k Hk. unfold a, c in Hhigher.
      rewrite !bit_at_testbit__solver_final by lia.
      rewrite Hhigher by lia. reflexivity. }
    assert (Hchoice :
      (Z.lxor a x > Z.lxor c x <->
       (BitAt x top = 0 /\ BitAt a top = 1 /\ BitAt c top = 0) \/
       (BitAt x top = 1 /\ BitAt a top = 0 /\ BitAt c top = 1))).
    { unfold top. apply xor_order_bit_choice__solver_final; assumption. }
    assert (Hoff : forall bit, 0 <= bit < 30 -> bit <> top ->
      ~ (SameHigherBits input 29 bit i j /\
         ((BitAt x bit = 0 /\ BitAt a bit = 1 /\ BitAt c bit = 0) \/
          (BitAt x bit = 1 /\ BitAt a bit = 0 /\ BitAt c bit = 1)))).
    { intros bit Hbr Hne [Hsamebit Hcases].
      destruct (Z_lt_dec bit top) as [Hlt | Hnlt].
      - specialize (Hsamebit top ltac:(lia)).
        fold a c in Hsamebit.
        rewrite !bit_at_testbit__solver_final in Hsamebit by lia.
        apply Hdiff. destruct (Z.testbit a top), (Z.testbit c top);
          simpl in Hsamebit; congruence.
      - assert (Hgt : top < bit) by lia.
        assert (Heqbit : BitAt a bit = BitAt c bit).
        { rewrite !bit_at_testbit__solver_final by lia.
          rewrite Hhigher by lia. reflexivity. }
        destruct Hcases as [(_ & H1 & H0) | (_ & H0 & H1)]; lia. }
    rewrite (sum_Z_range_split 0 top 30) by lia.
    rewrite (sum_Z_range_cons top 30) by lia.
    assert (Hleft : SumLib.Sum.sum (fun bit : Z => 0 <= bit < top)
        (fun bit =>
          if prop_dec
            (SameHigherBits input 29 bit i j /\
             ((BitAt x bit = 0 /\ BitAt a bit = 1 /\ BitAt c bit = 0) \/
              (BitAt x bit = 1 /\ BitAt a bit = 0 /\ BitAt c bit = 1)))
          then 1 else 0) = 0).
    { apply sum_Z_range_eq_zero. intros bit Hbr.
      destruct (prop_dec
        (SameHigherBits input 29 bit i j /\
         ((BitAt x bit = 0 /\ BitAt a bit = 1 /\ BitAt c bit = 0) \/
          (BitAt x bit = 1 /\ BitAt a bit = 0 /\ BitAt c bit = 1))));
        [exfalso; apply (Hoff bit); [lia | lia | assumption] | reflexivity]. }
    assert (Hright : SumLib.Sum.sum (fun bit : Z => top + 1 <= bit < 30)
        (fun bit =>
          if prop_dec
            (SameHigherBits input 29 bit i j /\
             ((BitAt x bit = 0 /\ BitAt a bit = 1 /\ BitAt c bit = 0) \/
              (BitAt x bit = 1 /\ BitAt a bit = 0 /\ BitAt c bit = 1)))
          then 1 else 0) = 0).
    { apply sum_Z_range_eq_zero. intros bit Hbr.
      destruct (prop_dec
        (SameHigherBits input 29 bit i j /\
         ((BitAt x bit = 0 /\ BitAt a bit = 1 /\ BitAt c bit = 0) \/
          (BitAt x bit = 1 /\ BitAt a bit = 0 /\ BitAt c bit = 1))));
        [exfalso; apply (Hoff bit); [lia | lia | assumption] | reflexivity]. }
    rewrite Hleft, Hright. ring_simplify.
    destruct (prop_dec
      (SameHigherBits input 29 top i j /\
       ((BitAt x top = 0 /\ BitAt a top = 1 /\ BitAt c top = 0) \/
        (BitAt x top = 1 /\ BitAt a top = 0 /\ BitAt c top = 1))))
      as [[_ Hcase] | Hnot];
      destruct (prop_dec (Z.lxor a x > Z.lxor c x)) as [Hinv | Hinv];
      try reflexivity; exfalso; [apply Hinv; apply Hchoice; exact Hcase |
        apply Hnot; split; [exact Hsame | apply Hchoice; exact Hinv]].
Qed.
Lemma bit_at_range__solver_final :
  forall value bit, 0 <= bit -> 0 <= BitAt value bit < 2.
Proof.
  intros value bit Hbit.
  rewrite bit_at_testbit__solver_final by exact Hbit.
  destruct (Z.testbit value bit); simpl; lia.
Qed.
Lemma bit_contributions_sum_inversions__solver_final :
  forall input costs x,
    (forall i, 0 <= i < Zlength input ->
      0 <= Znth i input 0 <= 1000000000) ->
    0 <= x -> CostTable input costs ->
    Inversions input x
      (SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
        (fun bit => CostAt costs bit (BitAt x bit))).
Proof.
  intros input costs x Hvals Hx Htable.
  destruct Htable as (Hlen & Hrows & Hcost).
  unfold Inversions.
  transitivity (SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
    (fun bit =>
      #(fun p : Z * Z =>
        (0 <= fst p < Zlength input /\ 0 <= snd p < Zlength input) /\
        fst p < snd p /\
        SameHigherBits input 29 bit (fst p) (snd p) /\
        ((BitAt x bit = 0 /\ BitAt (Znth (fst p) input 0) bit = 1 /\
                            BitAt (Znth (snd p) input 0) bit = 0) \/
         (BitAt x bit = 1 /\ BitAt (Znth (fst p) input 0) bit = 0 /\
                            BitAt (Znth (snd p) input 0) bit = 1))))).
  - apply SumLib.Sum.sum_ext. intros bit Hbit.
    specialize (Hcost bit (BitAt x bit) Hbit
      (bit_at_range__solver_final x bit ltac:(lia))).
    unfold BitContribution in Hcost.
    rewrite Hcost. apply set_card_extensional__solver_final.
    intros [i j]. simpl. tauto.
  - transitivity (SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
      (fun bit =>
        SumLib.Sum.sum
          (fun p : Z * Z =>
            0 <= fst p < Zlength input /\ 0 <= snd p < Zlength input)
          (fun p =>
            if prop_dec
              (fst p < snd p /\
               SameHigherBits input 29 bit (fst p) (snd p) /\
               ((BitAt x bit = 0 /\ BitAt (Znth (fst p) input 0) bit = 1 /\
                                   BitAt (Znth (snd p) input 0) bit = 0) \/
                (BitAt x bit = 1 /\ BitAt (Znth (fst p) input 0) bit = 0 /\
                                   BitAt (Znth (snd p) input 0) bit = 1)))
            then 1 else 0))).
    { apply SumLib.Sum.sum_ext. intros bit Hbit.
      apply set_card_subset_as_sum__solver_final. }
    rewrite finite_sum_swap__solver_final.
    rewrite (@set_card_subset_as_sum__solver_final (Z * Z)
      (fun p =>
        0 <= fst p < Zlength input /\ 0 <= snd p < Zlength input)
      (fun p =>
        fst p < snd p /\
        Z.lxor (Znth (fst p) input 0) x > Z.lxor (Znth (snd p) input 0) x)
      (finite_index_pair (Zlength input)) _).
    apply SumLib.Sum.sum_ext. intros [i j] [[Hi0 Hi] [Hj0 Hj]]. simpl in *.
    destruct (prop_dec (i < j)) as [Hij | Hnij].
    + assert (Hpartition := pair_inversion_bit_partition__solver_final
        input (i, j) x ltac:(simpl; tauto) Hvals Hx).
      simpl in Hpartition.
      transitivity (SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
        (fun bit =>
          if prop_dec
            (SameHigherBits input 29 bit i j /\
             ((BitAt x bit = 0 /\ BitAt (Znth i input 0) bit = 1 /\
                                 BitAt (Znth j input 0) bit = 0) \/
              (BitAt x bit = 1 /\ BitAt (Znth i input 0) bit = 0 /\
                                 BitAt (Znth j input 0) bit = 1)))
          then 1 else 0)).
      * apply SumLib.Sum.sum_ext. intros bit Hbit.
        destruct (prop_dec
          (i < j /\ SameHigherBits input 29 bit i j /\
           ((BitAt x bit = 0 /\ BitAt (Znth i input 0) bit = 1 /\
                               BitAt (Znth j input 0) bit = 0) \/
            (BitAt x bit = 1 /\ BitAt (Znth i input 0) bit = 0 /\
                               BitAt (Znth j input 0) bit = 1)))) as [Hall | Hnotall];
          destruct (prop_dec
          (SameHigherBits input 29 bit i j /\
           ((BitAt x bit = 0 /\ BitAt (Znth i input 0) bit = 1 /\
                               BitAt (Znth j input 0) bit = 0) \/
            (BitAt x bit = 1 /\ BitAt (Znth i input 0) bit = 0 /\
                               BitAt (Znth j input 0) bit = 1)))) as [Hrest | Hnotrest];
          try reflexivity; exfalso; tauto.
      * rewrite Hpartition.
        destruct (prop_dec
          (i < j /\ Z.lxor (Znth i input 0) x > Z.lxor (Znth j input 0) x));
          destruct (prop_dec
          (Z.lxor (Znth i input 0) x > Z.lxor (Znth j input 0) x));
          try reflexivity; exfalso; tauto.
    + assert (Hzero : SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
        (fun bit =>
          if prop_dec
            (i < j /\ SameHigherBits input 29 bit i j /\
             ((BitAt x bit = 0 /\ BitAt (Znth i input 0) bit = 1 /\
                                 BitAt (Znth j input 0) bit = 0) \/
              (BitAt x bit = 1 /\ BitAt (Znth i input 0) bit = 0 /\
                                 BitAt (Znth j input 0) bit = 1)))
          then 1 else 0) = 0).
      { apply sum_Z_range_eq_zero. intros bit Hbit.
        destruct (prop_dec
          (i < j /\ SameHigherBits input 29 bit i j /\
           ((BitAt x bit = 0 /\ BitAt (Znth i input 0) bit = 1 /\
                               BitAt (Znth j input 0) bit = 0) \/
            (BitAt x bit = 1 /\ BitAt (Znth i input 0) bit = 0 /\
                               BitAt (Znth j input 0) bit = 1))));
          [exfalso; tauto | reflexivity]. }
      rewrite Hzero.
      destruct (prop_dec
        (i < j /\ Z.lxor (Znth i input 0) x > Z.lxor (Znth j input 0) x));
        [exfalso; tauto | reflexivity].
Qed.
Lemma xor_choice_prefix_complete_spec__solver_final :
  forall input costs inv x,
    (forall i, 0 <= i < Zlength input ->
      0 <= Znth i input 0 <= 1000000000) ->
    XorChoicePrefix input costs 30 inv x ->
    Spec input (inv, x).
Proof.
  intros input costs inv x Hvals Hprefix.
  destruct Hprefix as (Htable & Hinv & Hx).
  set (strict := fun bit => CostAt costs bit 1 < CostAt costs bit 0).
  set (xmask := @SumLib.Sum.sum Z
    (fun bit : Z => 0 <= bit < 30 /\ strict bit)
    (finite_Z_range' 0 30 strict) (fun bit => 2 ^ bit)).
  assert (Hxmask : x = xmask).
  {
    rewrite Hx. unfold xmask, strict.
    apply finite_sum_predicate_extensional__solver_final.
    intros bit. tauto.
  }
  pose proof (binary_mask_spec__solver_final 30%nat strict) as Hmaskspec.
  cbn [Z.of_nat] in Hmaskspec.
  destruct Hmaskspec as (Hxmaskbound & Hxmaskbits).
  assert (Hxbound : 0 <= x < 2 ^ 30).
  { rewrite Hxmask. unfold xmask. exact Hxmaskbound. }
  assert (Hxbits : forall bit, 0 <= bit < 30 ->
    BitAt x bit = if prop_dec (strict bit) then 1 else 0).
  { intros bit Hbit. rewrite Hxmask. unfold xmask.
    apply Hxmaskbits. exact Hbit. }
  assert (Hcostx :
    SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
      (fun bit => CostAt costs bit (BitAt x bit)) =
    SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
      (fun bit => Z.min (CostAt costs bit 0) (CostAt costs bit 1))).
  {
    apply sum_Z_range_ext. intros bit Hbit.
    specialize (Hxbits bit Hbit).
    unfold strict in Hxbits.
    destruct (prop_dec
      (CostAt costs bit 1 < CostAt costs bit 0)) as [Hlt | Hnlt].
    - cbn in Hxbits. rewrite Hxbits. rewrite Z.min_r by lia. reflexivity.
    - cbn in Hxbits. rewrite Hxbits. rewrite Z.min_l by lia. reflexivity.
  }
  assert (Hinvx : Inversions input x inv).
  {
    pose proof (bit_contributions_sum_inversions__solver_final
      input costs x Hvals ltac:(lia) Htable) as Hcalc.
    rewrite Hcostx in Hcalc. rewrite <- Hinv in Hcalc. exact Hcalc.
  }
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists (inv, x). split.
  - split.
    + change (0 <= x /\ Inversions input x inv).
      split; [lia | exact Hinvx].
    + intros [other_inv other_x] [Hotherx Hotherinv]. simpl in *.
      pose proof (bit_contributions_sum_inversions__solver_final
        input costs other_x Hvals Hotherx Htable) as Hothercalc.
      assert (Hothercount : other_inv =
        SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
          (fun bit => CostAt costs bit (BitAt other_x bit))).
      { unfold Inversions in Hotherinv, Hothercalc. lia. }
      assert (Hminle :
        SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
          (fun bit => Z.min (CostAt costs bit 0) (CostAt costs bit 1)) <=
        SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
          (fun bit => CostAt costs bit (BitAt other_x bit))).
      {
        apply sum_Z_range_le. intros bit Hbit.
        pose proof (bit_at_range__solver_final other_x bit ltac:(lia)) as Hchoice.
        assert (BitAt other_x bit = 0 \/ BitAt other_x bit = 1) by lia.
        destruct H as [H | H]; rewrite H.
        - apply Z.le_min_l.
        - apply Z.le_min_r.
      }
      assert (Hle : inv <= other_inv) by (rewrite Hinv, Hothercount; exact Hminle).
      destruct (Z_lt_dec inv other_inv) as [Hlt | Hnlt].
      * left. exact Hlt.
      * right. split; [lia |].
        assert (Heq : inv = other_inv) by lia.
        assert (Hnonnegdiff : forall bit, 0 <= bit < 30 ->
          0 <= CostAt costs bit (BitAt other_x bit) -
            Z.min (CostAt costs bit 0) (CostAt costs bit 1)).
        {
          intros bit Hbit.
          pose proof (bit_at_range__solver_final other_x bit ltac:(lia)) as Hchoice.
          assert (BitAt other_x bit = 0 \/ BitAt other_x bit = 1) by lia.
          destruct H as [H | H]; rewrite H.
          - pose proof (Z.le_min_l (CostAt costs bit 0)
              (CostAt costs bit 1)). lia.
          - pose proof (Z.le_min_r (CostAt costs bit 0)
              (CostAt costs bit 1)). lia.
        }
        assert (Hsumdiff :
          SumLib.Sum.sum (fun bit : Z => 0 <= bit < 30)
            (fun bit => CostAt costs bit (BitAt other_x bit) -
              Z.min (CostAt costs bit 0) (CostAt costs bit 1)) = 0).
        {
          rewrite sum_Z_range_sub, <- Hothercount, <- Hinv. lia.
        }
        pose proof (SumLib.Sum.sum_nonneg_eq_zero_elim
          (fun bit : Z => 0 <= bit < 30)
          (fun bit => CostAt costs bit (BitAt other_x bit) -
            Z.min (CostAt costs bit 0) (CostAt costs bit 1))
          Hnonnegdiff Hsumdiff) as Hpointzero.
        assert (Hstrictsubset : forall bit, 0 <= bit < 30 ->
          strict bit -> BitAt other_x bit = 1).
        {
          intros bit Hbit Hstrict.
          specialize (Hpointzero bit Hbit).
          unfold strict in Hstrict.
          cbn beta in Hpointzero.
          rewrite Z.min_r in Hpointzero by lia.
          pose proof (bit_at_range__solver_final other_x bit ltac:(lia)) as Hchoice.
          assert (BitAt other_x bit = 0 \/ BitAt other_x bit = 1) by lia.
          destruct H as [H | H]; [rewrite H in Hpointzero; lia | exact H].
        }
        assert (Hmaskle : xmask <=
          @SumLib.Sum.sum Z
            (fun bit : Z => 0 <= bit < 30 /\ BitAt other_x bit = 1)
            (finite_Z_range' 0 30
              (fun bit => BitAt other_x bit = 1))
            (fun bit => 2 ^ bit)).
        {
          unfold xmask.
          apply binary_mask_monotone__solver_final.
          exact Hstrictsubset.
        }
        rewrite Hxmask.
        eapply Z.le_trans; [exact Hmaskle |].
        apply binary_low_mask_le__solver_final. exact Hotherx.
  - reflexivity.
Qed.
