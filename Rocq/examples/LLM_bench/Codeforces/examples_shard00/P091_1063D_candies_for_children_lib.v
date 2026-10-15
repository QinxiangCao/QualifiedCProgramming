Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition CandyTaken (sweet : Z -> Prop) (friend remaining taken : Z) : Prop :=
  (sweet friend /\ ((remaining >= 2 /\ taken = 2) \/ (remaining = 1 /\ taken = 1))) \/
  (~ sweet friend /\ remaining >= 1 /\ taken = 1).

Definition CandyObservation (n l r k : Z) (sweet : Z -> Prop) : Prop :=
  (forall p, sweet p -> 1 <= p <= n) /\
  exists friends remaining taken steps,
    Zlength friends = steps /\ Zlength remaining = steps + 1 /\
    Zlength taken = steps /\ Znth 0 friends 0 = l /\ Znth 0 remaining 0 = k /\
    (forall i, 0 <= i < steps ->
      CandyTaken sweet (Znth i friends 0) (Znth i remaining 0) (Znth i taken 0) /\
      Znth (i+1) remaining 0 = Znth i remaining 0 - Znth i taken 0 /\
      (i+1 < steps -> Znth (i+1) friends 0 = 1 + (Znth i friends 0 mod n))) /\
    Znth (steps-1) friends 0 = r /\ Znth steps remaining 0 = 0.

Definition Pre (n l r k : Z) : Prop :=
  1 <= n <= 100000000000 /\ 1 <= k <= 100000000000 /\
  1 <= l <= n /\ 1 <= r <= n.

Definition Spec (n l r k out : Z) : Prop :=
  (out = -1 /\ forall sweet, ~ CandyObservation n l r k sweet) \/
  max_value_of_subset Z.le
    (fun candidate : (Z -> Prop) * Z =>
      CandyObservation n l r k (fst candidate) /\
      snd candidate = #(fun p : Z => 1 <= p < n + 1 /\ fst candidate p))
    snd out.

Definition QuotientBlock (k L R q : Z) : Prop :=
  forall num, L <= num <= R -> q = (k - 1) / num.

Definition MaxResult (a b out : Z) : Prop := out = Z.max a b.

Definition MinResult (a b out : Z) : Prop := out = Z.min a b.

Definition CandyArithmeticCandidate
    (n x k num add : Z) : Prop :=
  n <= num <= 2 * n /\
  (add = 0 \/ add = 1) /\
  let q := (k - 1) / num in
  let h := k - x + add - q * num in
  add <= h <= x /\
  h <= num - n /\
  num - n - h <= n - x.

Definition CandySearchPrefix
    (n x k upto best : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun candidate : Z * Z =>
       CandyArithmeticCandidate n x k (fst candidate) (snd candidate) /\
       fst candidate < upto)
    (fun candidate => fst candidate - n)
    (-1) best.

Definition CandySearchBlock
    (n x k L R phase best : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun candidate : Z * Z =>
       CandyArithmeticCandidate n x k (fst candidate) (snd candidate) /\
       (fst candidate < L \/
        (L <= fst candidate <= R /\ snd candidate < phase)))
    (fun candidate => fst candidate - n)
    (-1) best.

Definition CandyFeasibleInterval
    (n x k L R q add lo hi : Z) : Prop :=
  forall num,
    L <= num <= R ->
    (CandyArithmeticCandidate n x k num add <-> lo <= num <= hi).

Definition CandyArithmeticBest (n x k best : Z) : Prop :=
  CandySearchPrefix n x k (2 * n + 1) best.

Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Psatz.
Lemma candy_bit_cases__solver_final_semantics :
  forall (sweet : Z -> Prop) p,
    (sweet p /\ (if prop_dec (sweet p) then 1 else 0) = 1) \/
    (~ sweet p /\ (if prop_dec (sweet p) then 1 else 0) = 0).
Proof.
  intros sweet p.
  destruct (prop_dec (sweet p)); auto.
Qed.
Lemma candy_position_bounds__solver_final_semantics :
  forall n l i, 0 < n ->
    1 <= 1 + (l - 1 + i) mod n <= n.
Proof.
  intros n l i Hn.
  pose proof (Z.mod_pos_bound (l - 1 + i) n Hn). lia.
Qed.
Lemma candy_position_zero__solver_final_semantics :
  forall n l, 0 < n -> 1 <= l <= n ->
    1 + (l - 1 + 0) mod n = l.
Proof.
  intros n l Hn Hl.
  replace (l - 1 + 0) with (l - 1) by ring.
  rewrite Z.mod_small; lia.
Qed.
Lemma candy_position_period__solver_final_semantics :
  forall n l i, n <> 0 ->
    1 + (l - 1 + (i + n)) mod n = 1 + (l - 1 + i) mod n.
Proof.
  intros n l i Hn.
  replace (l - 1 + (i + n)) with ((l - 1 + i) + 1 * n) by ring.
  rewrite Z.mod_add; auto.
Qed.
Lemma candy_position_multiple_period__solver_final_semantics :
  forall n l i q, n <> 0 ->
    1 + (l - 1 + (i + q * n)) mod n = 1 + (l - 1 + i) mod n.
Proof.
  intros n l i q Hn.
  replace (l - 1 + (i + q * n)) with ((l - 1 + i) + q * n) by ring.
  rewrite Z.mod_add; auto.
Qed.
Lemma candy_position_succ__solver_final_semantics :
  forall n l i, 0 < n ->
    1 + (l - 1 + (i + 1)) mod n =
    1 + ((1 + (l - 1 + i) mod n) mod n).
Proof.
  intros n l i Hn.
  replace (l - 1 + (i + 1)) with ((l - 1 + i) + 1) by ring.
  destruct (Z.eq_dec n 1) as [-> | Hneq].
  - repeat rewrite Z.mod_1_r. reflexivity.
  - rewrite (Z.add_mod (l - 1 + i) 1 n) by lia.
    assert (Hmod1 : 1 mod n = 1) by (apply Z.mod_small; lia).
    rewrite Hmod1.
    replace ((l - 1 + i) mod n + 1) with
      (1 + (l - 1 + i) mod n) by ring.
    reflexivity.
Qed.
Lemma set_card_by_nodup_list__solver_final_semantics :
  forall {A : Type} (P : A -> Prop) `{Finite A P} (xs : list A),
    NoDup xs ->
    (forall x, P x <-> In x xs) ->
    set_card P = Zlength xs.
Proof.
  intros A P HP xs Hnodup Hxs.
  assert (Hperm : Permutation (@enum A P HP) xs).
  {
    apply NoDup_Permutation.
    - apply enum_nodup.
    - exact Hnodup.
    - intros x. rewrite <- Hxs. symmetry. apply enum_ok.
  }
  unfold set_card, sum.
  assert (Hfold : forall ys : list A,
      fold_right (fun _ acc => 1 + acc) 0 ys = Zlength ys).
  {
    intros ys. induction ys as [|y ys IH].
    - cbn [fold_right]. rewrite Zlength_nil. reflexivity.
    - cbn [fold_right]. rewrite IH, Zlength_cons. lia.
  }
  rewrite Hfold, !Zlength_correct.
  f_equal. now apply Permutation_length in Hperm.
Qed.
Lemma Zlength_map__solver_final_semantics :
  forall {A B : Type} (f : A -> B) xs,
    Zlength (map f xs) = Zlength xs.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Zlength_Zrange_aux__solver_final_semantics :
  forall low m, Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low. induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__solver_final_semantics :
  forall low high, low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__solver_final_semantics. lia.
Qed.
Lemma candy_position_injective_range__solver_final_semantics :
  forall n l i j,
    0 < n -> 0 <= i < n -> 0 <= j < n ->
    1 + (l - 1 + i) mod n = 1 + (l - 1 + j) mod n ->
    i = j.
Proof.
  intros n l i j Hn Hi Hj Heq.
  assert (Hrem : (i - j) mod n = 0).
  {
    assert ((l - 1 + i) mod n = (l - 1 + j) mod n) by lia.
    replace (i - j) with ((l - 1 + i) - (l - 1 + j)) by ring.
    rewrite Zminus_mod, H, Z.sub_diag, Zmod_0_l; lia.
  }
  apply Z.mod_divide in Hrem; [|lia].
  destruct Hrem as [q Hq].
  assert (-1 < q < 1) by nia.
  assert (q = 0) by lia. subst q. nia.
Qed.
Lemma candy_cycle_nodup__solver_final_semantics :
  forall n l, 0 < n ->
    NoDup
      (map (fun i : Z => 1 + (l - 1 + i) mod n) (Zrange 0 n)).
Proof.
  intros n l Hn.
  apply Injective_map_NoDup_in.
  - intros i j Hi Hj Heq.
    apply In_Zrange in Hi. apply In_Zrange in Hj.
    eapply candy_position_injective_range__solver_final_semantics; eauto.
  - apply NoDup_Zrange.
Qed.
Lemma candy_cycle_permutation__solver_final_semantics :
  forall n l, 0 < n ->
    Permutation
      (map (fun i : Z => 1 + (l - 1 + i) mod n) (Zrange 0 n))
      (Zrange 1 (n + 1)).
Proof.
  intros n l Hn. apply NoDup_Permutation_bis.
  - apply candy_cycle_nodup__solver_final_semantics. exact Hn.
  - rewrite length_map.
    assert (Hlen : length (Zrange 1 (n + 1)) = length (Zrange 0 n)).
    {
      apply Nat2Z.inj. rewrite <- !Zlength_correct.
      rewrite !Zlength_Zrange__solver_final_semantics by lia. lia.
    }
    lia.
  - intros p Hp. apply in_map_iff in Hp.
    destruct Hp as [i [<- Hi]].
    apply In_Zrange.
    pose proof (candy_position_bounds__solver_final_semantics n l i Hn). lia.
Qed.
Lemma candy_cycle_sweet_count__solver_final_semantics :
  forall n l (sweet : Z -> Prop), 0 < n ->
    set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p) =
    Zlength
      (filter (fun p => if prop_dec (sweet p) then true else false)
        (map (fun i : Z => 1 + (l - 1 + i) mod n) (Zrange 0 n))).
Proof.
  intros n l sweet Hn.
  apply set_card_by_nodup_list__solver_final_semantics.
  - apply NoDup_filter. apply candy_cycle_nodup__solver_final_semantics. exact Hn.
  - intros p. rewrite filter_In. split.
    + intros [Hp Hsweet]. split.
      * eapply Permutation_in.
        -- apply Permutation_sym.
           apply candy_cycle_permutation__solver_final_semantics. exact Hn.
        -- apply In_Zrange. lia.
      * destruct (prop_dec (sweet p)); [reflexivity | contradiction].
    + intros [Hin Htest]. split.
      * apply In_Zrange.
        eapply Permutation_in.
        -- apply candy_cycle_permutation__solver_final_semantics. exact Hn.
        -- exact Hin.
      * destruct (prop_dec (sweet p)); [exact s | discriminate].
Qed.
Lemma Znth_map__solver_final_semantics :
  forall {A B : Type} (f : A -> B) xs (da : A) (db : B) i,
    0 <= i < Zlength xs ->
    Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [|a xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Znth_Zrange_aux__solver_final_semantics :
  forall m low i, 0 <= i < Z.of_nat m ->
    Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__solver_final_semantics :
  forall low high i, low <= high -> 0 <= i < high - low ->
    Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__solver_final_semantics by lia. lia.
Qed.
Lemma candy_friends_trace__solver_final_semantics :
  forall n l friends steps,
    0 < n -> 1 <= l <= n ->
    Zlength friends = steps -> Znth 0 friends 0 = l ->
    (forall i, 0 <= i < steps -> i + 1 < steps ->
       Znth (i + 1) friends 0 = 1 + (Znth i friends 0 mod n)) ->
    forall i, 0 <= i < steps ->
      Znth i friends 0 = 1 + (l - 1 + i) mod n.
Proof.
  intros n l friends steps Hn Hl Hlen Hzero Hnext i Hi.
  assert (Hpoint : forall m : nat, Z.of_nat m < steps ->
      Znth (Z.of_nat m) friends 0 =
      1 + (l - 1 + Z.of_nat m) mod n).
  {
    induction m as [|m IH]; intros Hm.
    - simpl. rewrite Hzero.
      symmetry. apply candy_position_zero__solver_final_semantics; lia.
    - rewrite Nat2Z.inj_succ.
      change (Znth (Z.of_nat m + 1) friends 0 =
        1 + (l - 1 + (Z.of_nat m + 1)) mod n).
      rewrite Hnext by lia.
      rewrite IH by lia.
      symmetry. apply candy_position_succ__solver_final_semantics. exact Hn.
  }
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  apply Hpoint. lia.
Qed.
Lemma candy_remaining_prefix__solver_final_semantics :
  forall remaining taken steps k,
    0 <= steps -> Znth 0 remaining 0 = k ->
    (forall i, 0 <= i < steps ->
       Znth (i + 1) remaining 0 =
       Znth i remaining 0 - Znth i taken 0) ->
    forall m, 0 <= m <= steps ->
      Znth m remaining 0 =
      k - sum (fun i : Z => 0 <= i < m) (fun i => Znth i taken 0).
Proof.
  intros remaining taken steps k Hsteps Hzero Hnext m Hm.
  assert (Hnat : forall j : nat, Z.of_nat j <= steps ->
      Znth (Z.of_nat j) remaining 0 =
      k - sum (fun i : Z => 0 <= i < Z.of_nat j)
              (fun i => Znth i taken 0)).
  {
    induction j as [|j IH]; intros Hj.
    - simpl. rewrite Hzero, sum_Z_range_empty by lia. lia.
    - rewrite Nat2Z.inj_succ.
      change (Znth (Z.of_nat j + 1) remaining 0 =
        k - sum (fun i : Z => 0 <= i < Z.of_nat j + 1)
                (fun i => Znth i taken 0)).
      rewrite Hnext by lia.
      rewrite IH by lia.
      rewrite sum_Z_range_extend_right by lia. lia.
  }
  replace m with (Z.of_nat (Z.to_nat m)) by lia.
  apply Hnat. lia.
Qed.
Lemma candy_taken_total__solver_final_semantics :
  forall remaining taken steps k,
    0 <= steps -> Znth 0 remaining 0 = k ->
    (forall i, 0 <= i < steps ->
       Znth (i + 1) remaining 0 =
       Znth i remaining 0 - Znth i taken 0) ->
    Znth steps remaining 0 = 0 ->
    sum (fun i : Z => 0 <= i < steps) (fun i => Znth i taken 0) = k.
Proof.
  intros remaining taken steps k Hsteps Hzero Hnext Hend.
  pose proof (candy_remaining_prefix__solver_final_semantics
    remaining taken steps k Hsteps Hzero Hnext steps ltac:(lia)).
  rewrite Hend in H. lia.
Qed.
Lemma candy_distance_endpoint__solver_final_semantics :
  forall n l r x,
    0 < n -> 1 <= r <= n ->
    x = (r - l + n) mod n + 1 ->
    1 + (l - 1 + (x - 1)) mod n = r.
Proof.
  intros n l r x Hn Hr Hx. subst x.
  replace (l - 1 + ((r - l + n) mod n + 1 - 1)) with
    (l - 1 + (r - l + n) mod n) by ring.
  rewrite Zplus_mod_idemp_r.
  replace (l - 1 + (r - l + n)) with ((r - 1) + 1 * n) by ring.
  rewrite Z.mod_add by lia.
  rewrite Z.mod_small; lia.
Qed.
Lemma candy_steps_decompose__solver_final_semantics :
  forall n l r x steps,
    0 < n -> 1 <= r <= n -> 1 <= x <= n -> 1 <= steps ->
    x = (r - l + n) mod n + 1 ->
    1 + (l - 1 + (steps - 1)) mod n = r ->
    exists cycles, 0 <= cycles /\ steps = cycles * n + x.
Proof.
  intros n l r x steps Hn Hr Hx Hsteps Hxdef Hend.
  pose proof (candy_distance_endpoint__solver_final_semantics
    n l r x Hn Hr Hxdef) as Hdist.
  assert (Hrem : (steps - x) mod n = 0).
  {
    assert ((l - 1 + (steps - 1)) mod n =
            (l - 1 + (x - 1)) mod n) by lia.
    replace (steps - x) with
      ((l - 1 + (steps - 1)) - (l - 1 + (x - 1))) by ring.
    rewrite Zminus_mod, H, Z.sub_diag, Zmod_0_l; lia.
  }
  apply Z.mod_divide in Hrem; [|lia].
  destruct Hrem as [cycles Hcycles].
  exists cycles. split; nia.
Qed.
Lemma candy_filter_count__solver_final_semantics :
  forall (sweet : Z -> Prop) xs,
    Zlength (filter (fun p => if prop_dec (sweet p) then true else false) xs) =
    fold_right
      (fun p acc => (if prop_dec (sweet p) then 1 else 0) + acc) 0 xs.
Proof.
  intros sweet xs. induction xs as [|p xs IH].
  - simpl. rewrite Zlength_nil. reflexivity.
  - simpl. destruct (prop_dec (sweet p)); simpl.
    + rewrite Zlength_cons. unfold Z.succ. rewrite IH. apply Z.add_comm.
    + exact IH.
Qed.
Lemma candy_fold_right_map__solver_final_semantics :
  forall {A B C : Type} (f : B -> C -> C) (g : A -> B) (z : C) xs,
    fold_right f z (map g xs) =
    fold_right (fun x acc => f (g x) acc) z xs.
Proof.
  intros A B C f g z xs. induction xs as [|x xs IH]; simpl; congruence.
Qed.
Lemma candy_one_cycle_sum__solver_final_semantics :
  forall n l (sweet : Z -> Prop), 0 < n ->
    sum (fun i : Z => 0 <= i < n)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) =
    set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p).
Proof.
  intros n l sweet Hn.
  rewrite sum_range_unfold.
  rewrite (candy_cycle_sweet_count__solver_final_semantics n l sweet Hn).
  rewrite candy_filter_count__solver_final_semantics.
  rewrite candy_fold_right_map__solver_final_semantics. reflexivity.
Qed.
Lemma candy_bit_period__solver_final_semantics :
  forall n l sweet i, 0 < n ->
    (if prop_dec (sweet (1 + (l - 1 + (i + n)) mod n)) then 1 else 0) =
    (if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0).
Proof.
  intros n l sweet i Hn.
  rewrite candy_position_period__solver_final_semantics by lia. reflexivity.
Qed.
Lemma candy_bit_multiple_period__solver_final_semantics :
  forall n l sweet i q, 0 < n ->
    (if prop_dec (sweet (1 + (l - 1 + (i + q * n)) mod n)) then 1 else 0) =
    (if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0).
Proof.
  intros n l sweet i q Hn.
  replace (l - 1 + (i + q * n)) with ((l - 1 + i) + q * n) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma candy_cycles_sum_nat__solver_final_semantics :
  forall m n l sweet, 0 < n ->
    sum (fun i : Z => 0 <= i < Z.of_nat m * n)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) =
    Z.of_nat m * set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p).
Proof.
  intros m n l sweet Hn. induction m as [|m IH].
  - simpl. rewrite sum_Z_range_empty by lia. ring.
  - rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat m)) with (Z.of_nat m + 1) by lia.
    replace ((Z.of_nat m + 1) * n) with (Z.of_nat m * n + n) by ring.
    rewrite (sum_Z_range_split 0 (Z.of_nat m * n)
      (Z.of_nat m * n + n)) by lia.
    rewrite IH.
    assert (Hshift :
      sum (fun i : Z => Z.of_nat m * n <= i < Z.of_nat m * n + n)
        (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) =
      sum (fun i : Z => 0 <= i < n)
        (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0)).
    {
      transitivity
        (sum (fun i : Z => 0 <= i < n)
          (fun i => if prop_dec
            (sweet (1 + (l - 1 + (i + Z.of_nat m * n)) mod n))
            then 1 else 0)).
      - pose proof (sum_Z_range_shift 0 n (Z.of_nat m * n)
          (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n))
            then 1 else 0)) as Hs.
        replace (0 + Z.of_nat m * n) with (Z.of_nat m * n) in Hs by ring.
        replace (n + Z.of_nat m * n) with (Z.of_nat m * n + n) in Hs by ring.
        exact Hs.
      - apply sum_Z_range_ext. intros i Hi.
        replace (i + Z.of_nat m * n) with (i + Z.of_nat m * n) by ring.
        apply candy_bit_multiple_period__solver_final_semantics. exact Hn.
    }
    rewrite Hshift, candy_one_cycle_sum__solver_final_semantics by exact Hn.
    ring.
Qed.
Lemma candy_cycles_sum__solver_final_semantics :
  forall cycles n l sweet, 0 <= cycles -> 0 < n ->
    sum (fun i : Z => 0 <= i < cycles * n)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) =
    cycles * set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p).
Proof.
  intros cycles n l sweet Hcycles Hn.
  replace cycles with (Z.of_nat (Z.to_nat cycles)) by lia.
  apply candy_cycles_sum_nat__solver_final_semantics. exact Hn.
Qed.
Lemma candy_cycles_prefix_sum__solver_final_semantics :
  forall cycles n l x sweet, 0 <= cycles -> 0 < n -> 0 <= x <= n ->
    sum (fun i : Z => 0 <= i < cycles * n + x)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) =
    cycles * set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p) +
    sum (fun i : Z => 0 <= i < x)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0).
Proof.
  intros cycles n l x sweet Hcycles Hn Hx.
  rewrite (sum_Z_range_split 0 (cycles * n) (cycles * n + x)) by nia.
  rewrite candy_cycles_sum__solver_final_semantics by assumption.
  assert (Hshift :
    sum (fun i : Z => cycles * n <= i < cycles * n + x)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) =
    sum (fun i : Z => 0 <= i < x)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0)).
  {
    transitivity
      (sum (fun i : Z => 0 <= i < x)
        (fun i => if prop_dec
          (sweet (1 + (l - 1 + (i + cycles * n)) mod n))
          then 1 else 0)).
    - pose proof (sum_Z_range_shift 0 x (cycles * n)
        (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n))
          then 1 else 0)) as Hs.
      replace (0 + cycles * n) with (cycles * n) in Hs by ring.
      replace (x + cycles * n) with (cycles * n + x) in Hs by ring.
      exact Hs.
    - apply sum_Z_range_ext. intros i Hi.
      apply candy_bit_multiple_period__solver_final_semantics. exact Hn.
  }
  rewrite Hshift. reflexivity.
Qed.
Lemma candy_prefix_count_bounds__solver_final_semantics :
  forall n l x sweet, 0 < n -> 0 <= x <= n ->
    let h := sum (fun i : Z => 0 <= i < x)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) in
    let s := set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p) in
    0 <= h <= x /\ h <= s /\ 0 <= s - h <= n - x.
Proof.
  intros n l x sweet Hn Hx. cbn zeta.
  pose proof (sum_Z_range_bounds 0 x
    (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0)
    0 1 ltac:(lia)) as Hhead.
  specialize (Hhead ltac:(intros i Hi; destruct
    (candy_bit_cases__solver_final_semantics sweet
      (1 + (l - 1 + i) mod n)) as [[_ Hbit] | [_ Hbit]];
    rewrite Hbit; lia)).
  pose proof (sum_Z_range_bounds x n
    (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0)
    0 1 ltac:(lia)) as Htail.
  specialize (Htail ltac:(intros i Hi; destruct
    (candy_bit_cases__solver_final_semantics sweet
      (1 + (l - 1 + i) mod n)) as [[_ Hbit] | [_ Hbit]];
    rewrite Hbit; lia)).
  pose proof (candy_one_cycle_sum__solver_final_semantics n l sweet Hn) as Hone.
  rewrite (sum_Z_range_split 0 x n) in Hone by lia.
  nia.
Qed.
Lemma candy_steps_positive__solver_final_semantics :
  forall friends steps l,
    1 <= l -> Zlength friends = steps -> Znth 0 friends 0 = l ->
    1 <= steps.
Proof.
  intros friends steps l Hl Hlen Hhead.
  pose proof (Zlength_nonneg friends).
  assert (0 <= steps) by lia.
  destruct friends as [|a friends].
  - rewrite Zlength_nil in Hlen. unfold Znth in Hhead. simpl in Hhead. lia.
  - rewrite Zlength_cons in Hlen. unfold Z.succ in Hlen.
    pose proof (Zlength_nonneg friends). lia.
Qed.
Lemma candy_taken_pointwise__solver_final_semantics :
  forall n sweet friends remaining taken steps add,
    1 <= steps ->
    (add = 0 \/ add = 1) ->
    (add = 1 <->
      sweet (Znth (steps - 1) friends 0) /\
      Znth (steps - 1) remaining 0 = 1) ->
    (forall i, 0 <= i < steps ->
      CandyTaken sweet (Znth i friends 0) (Znth i remaining 0)
        (Znth i taken 0) /\
      Znth (i + 1) remaining 0 =
        Znth i remaining 0 - Znth i taken 0 /\
      (i + 1 < steps ->
        Znth (i + 1) friends 0 = 1 + (Znth i friends 0 mod n))) ->
    forall i, 0 <= i < steps ->
      Znth i taken 0 =
      1 + (if prop_dec (sweet (Znth i friends 0)) then 1 else 0) -
      (if Z.eq_dec i (steps - 1) then add else 0).
Proof.
  intros n sweet friends remaining taken steps add Hsteps Hadd Haddone Hrun i Hi.
  pose proof (Hrun i Hi) as Hcur.
  destruct Hcur as [Htake [Hrem _]].
  destruct (Z.eq_dec i (steps - 1)) as [Heq | Hneq].
  - subst i. destruct Htake as [[Hs [[Hr Htwo] | [Hr Hone]]] |
      [Hns [Hr Hone]]].
    + destruct (candy_bit_cases__solver_final_semantics sweet
        (Znth (steps - 1) friends 0)) as [[_ Hb] | [Hcontra _]];
        [|contradiction].
      assert (add = 0) by
        (destruct Hadd; [assumption | exfalso; apply (proj1 Haddone) in H;
         destruct H; lia]).
      destruct (Z.eq_dec (steps - 1) (steps - 1)); [rewrite Hb; lia | contradiction].
    + destruct (candy_bit_cases__solver_final_semantics sweet
        (Znth (steps - 1) friends 0)) as [[_ Hb] | [Hcontra _]];
        [|contradiction].
      assert (add = 1) by (apply (proj2 Haddone); auto).
      destruct (Z.eq_dec (steps - 1) (steps - 1)); [rewrite Hb; lia | contradiction].
    + destruct (candy_bit_cases__solver_final_semantics sweet
        (Znth (steps - 1) friends 0)) as [[Hcontra _] | [_ Hb]];
        [contradiction|].
      assert (add = 0) by
        (destruct Hadd; [assumption | exfalso; apply (proj1 Haddone) in H;
         destruct H as [Hsweet _]; contradiction]).
      destruct (Z.eq_dec (steps - 1) (steps - 1)); [rewrite Hb; lia | contradiction].
  - assert (Hbefore : i + 1 < steps) by lia.
    specialize (Hrun (i + 1) ltac:(lia)) as [Htake_next _].
    assert (Hremaining_next : 1 <= Znth (i + 1) remaining 0).
    {
      unfold CandyTaken in Htake_next.
      destruct Htake_next as [[_ [[Hr _] | [Hr _]]] | [_ [Hr _]]]; lia.
    }
    destruct Htake as [[Hs [[Hr Htwo] | [Hr Hone]]] |
      [Hns [Hr Hone]]].
    + destruct (candy_bit_cases__solver_final_semantics sweet
        (Znth i friends 0)) as [[_ Hb] | [Hcontra _]];
        [|contradiction].
      destruct (Z.eq_dec i (steps - 1)); [contradiction | rewrite Hb; lia].
    + exfalso. lia.
    + destruct (candy_bit_cases__solver_final_semantics sweet
        (Znth i friends 0)) as [[Hcontra _] | [_ Hb]];
        [contradiction|].
      destruct (Z.eq_dec i (steps - 1)); [contradiction | rewrite Hb; lia].
Qed.
Lemma candy_last_indicator_sum__solver_final_semantics :
  forall steps add, 1 <= steps ->
    sum (fun i : Z => 0 <= i < steps)
      (fun i => if Z.eq_dec i (steps - 1) then add else 0) = add.
Proof.
  intros steps add Hsteps.
  rewrite (sum_Z_range_split 0 (steps - 1) steps) by lia.
  rewrite sum_Z_range_eq_zero.
  - pose proof (sum_Z_range_single (steps - 1)
      (fun i => if Z.eq_dec i (steps - 1) then add else 0)) as Hsingle.
    replace (steps - 1 + 1) with steps in Hsingle by ring.
    rewrite Hsingle.
    destruct (Z.eq_dec (steps - 1) (steps - 1)); lia.
  - intros i Hi. destruct (Z.eq_dec i (steps - 1)); lia.
Qed.
Lemma candy_taken_sum_formula__solver_final_semantics :
  forall n l sweet friends remaining taken steps add,
    0 < n -> 1 <= steps ->
    (add = 0 \/ add = 1) ->
    (add = 1 <->
      sweet (Znth (steps - 1) friends 0) /\
      Znth (steps - 1) remaining 0 = 1) ->
    (forall i, 0 <= i < steps ->
      CandyTaken sweet (Znth i friends 0) (Znth i remaining 0)
        (Znth i taken 0) /\
      Znth (i + 1) remaining 0 =
        Znth i remaining 0 - Znth i taken 0 /\
      (i + 1 < steps ->
        Znth (i + 1) friends 0 = 1 + (Znth i friends 0 mod n))) ->
    (forall i, 0 <= i < steps ->
      Znth i friends 0 = 1 + (l - 1 + i) mod n) ->
    sum (fun i : Z => 0 <= i < steps) (fun i => Znth i taken 0) =
    steps +
      sum (fun i : Z => 0 <= i < steps)
        (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) -
      add.
Proof.
  intros n l sweet friends remaining taken steps add Hn Hsteps Hadd
    Haddone Hrun Hfriends.
  transitivity
    (sum (fun i : Z => 0 <= i < steps)
      (fun i =>
        (1 + (if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0)) -
        (if Z.eq_dec i (steps - 1) then add else 0))).
  - apply sum_Z_range_ext. intros i Hi.
    rewrite <- Hfriends by exact Hi.
    apply candy_taken_pointwise__solver_final_semantics with
      (n := n) (remaining := remaining); assumption.
  - rewrite sum_Z_range_sub, sum_Z_range_add.
    rewrite sum_Z_range_const by lia.
    rewrite candy_last_indicator_sum__solver_final_semantics by exact Hsteps.
    ring.
Qed.
Lemma candy_observation_to_arithmetic__solver_final_semantics :
  forall n l r x k sweet,
    0 < n -> 1 <= l <= n -> 1 <= r <= n -> 1 <= x <= n ->
    x = (r - l + n) mod n + 1 ->
    CandyObservation n l r k sweet ->
    exists add,
      CandyArithmeticCandidate n x k
        (n + set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p)) add.
Proof.
  intros n l r x k sweet Hn Hl Hr Hx Hxdef Hobs.
  unfold CandyObservation in Hobs.
  destruct Hobs as [Hsbound
    [friends [remaining [taken [steps
      [Hfriendslen [Hremaininglen [Htakenlen [Hfriend0 [Hremaining0
        [Hrun [Hfriendlast Hremaininglast]]]]]]]]]]]].
  assert (Hsteps : 1 <= steps).
  {
    eapply candy_steps_positive__solver_final_semantics.
    - exact (proj1 Hl).
    - exact Hfriendslen.
    - exact Hfriend0.
  }
  assert (Hfriendtrace : forall i, 0 <= i < steps ->
      Znth i friends 0 = 1 + (l - 1 + i) mod n).
  {
    eapply candy_friends_trace__solver_final_semantics; eauto.
    intros i Hi Hnext. specialize (Hrun i Hi). tauto.
  }
  assert (Hlasttrace : 1 + (l - 1 + (steps - 1)) mod n = r).
  { rewrite <- Hfriendlast. symmetry. apply Hfriendtrace. lia. }
  destruct (candy_steps_decompose__solver_final_semantics
    n l r x steps Hn Hr Hx Hsteps Hxdef Hlasttrace)
    as [cycles [Hcycles Hstepsform]].
  set (s := set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p)).
  set (h := sum (fun i : Z => 0 <= i < x)
    (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0)).
  pose proof (candy_prefix_count_bounds__solver_final_semantics
    n l x sweet Hn ltac:(lia)) as Hbounds.
  fold h s in Hbounds.
  destruct Hbounds as [Hh [Hhs Htail]].
  set (add := if prop_dec
    (sweet (Znth (steps - 1) friends 0) /\
     Znth (steps - 1) remaining 0 = 1) then 1 else 0).
  assert (Hadd : add = 0 \/ add = 1).
  {
    unfold add. destruct (prop_dec
      (sweet (Znth (steps - 1) friends 0) /\
       Znth (steps - 1) remaining 0 = 1)); auto.
  }
  assert (Haddone : add = 1 <->
      sweet (Znth (steps - 1) friends 0) /\
      Znth (steps - 1) remaining 0 = 1).
  {
    unfold add. destruct (prop_dec
      (sweet (Znth (steps - 1) friends 0) /\
       Znth (steps - 1) remaining 0 = 1)) as [Hy | Hno].
    - split; auto.
    - split; intros H; [discriminate | contradiction].
  }
  assert (Htotal :
    sum (fun i : Z => 0 <= i < steps) (fun i => Znth i taken 0) = k).
  {
    eapply candy_taken_total__solver_final_semantics; eauto; try lia.
    intros i Hi. specialize (Hrun i Hi). tauto.
  }
  pose proof (candy_taken_sum_formula__solver_final_semantics
    n l sweet friends remaining taken steps add Hn Hsteps Hadd Haddone
    Hrun Hfriendtrace) as Hformula.
  assert (Hvisits :
    sum (fun i : Z => 0 <= i < steps)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) =
    cycles * s + h).
  {
    rewrite Hstepsform.
    unfold s, h.
    apply candy_cycles_prefix_sum__solver_final_semantics; lia.
  }
  assert (Hk : k = cycles * (n + s) + x + h - add) by nia.
  assert (Haddh : add <= h).
  {
    destruct Hadd as [-> | ->]; [lia |].
    assert (Hspecial :
      sweet (Znth (steps - 1) friends 0) /\
      Znth (steps - 1) remaining 0 = 1) by
      (apply (proj1 Haddone); reflexivity).
    destruct Hspecial as [Hslast _].
    assert (Hbitlast :
      (if prop_dec (sweet (1 + (l - 1 + (x - 1)) mod n)) then 1 else 0) = 1).
    {
      destruct (candy_bit_cases__solver_final_semantics sweet
        (1 + (l - 1 + (x - 1)) mod n)) as [[_ Hb] | [Hns _]]; [exact Hb |].
      exfalso. apply Hns.
      pose proof (candy_distance_endpoint__solver_final_semantics
        n l r x Hn Hr Hxdef) as Hxpos.
      rewrite Hxpos, <- Hfriendlast. exact Hslast.
    }
    assert (Hprefix_last :
      sum (fun i : Z => 0 <= i < x)
        (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) >= 1).
    {
      rewrite (sum_Z_range_split 0 (x - 1) x) by lia.
      pose proof (sum_Z_range_bounds 0 (x - 1)
        (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0)
        0 1 ltac:(lia)) as Hbnd.
      specialize (Hbnd ltac:(intros i Hi; destruct
        (candy_bit_cases__solver_final_semantics sweet
          (1 + (l - 1 + i) mod n)) as [[_ Hb] | [_ Hb]];
        rewrite Hb; lia)).
      pose proof (sum_Z_range_single (x - 1)
        (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0))
        as Hsingle.
      replace (x - 1 + 1) with x in Hsingle by ring.
      rewrite Hsingle, Hbitlast. lia.
    }
    fold h in Hprefix_last. lia.
  }
  assert (Hsrange : 0 <= s <= n) by nia.
  assert (Hq : (k - 1) / (n + s) = cycles).
  {
    symmetry. apply Z.div_unique with (r := x + h - add - 1); nia.
  }
  exists add. unfold CandyArithmeticCandidate.
  fold s. rewrite Hq. repeat split; nia.
Qed.
Lemma candy_selected_indices__solver_final_semantics :
  forall n x s h add,
    0 < n -> 1 <= x <= n -> (add = 0 \/ add = 1) ->
    add <= h <= x -> h <= s -> 0 <= s - h <= n - x ->
    exists idxs,
      NoDup idxs /\ Zlength idxs = s /\
      (forall i, In i idxs -> 0 <= i < n) /\
      (forall i, 0 <= i < n ->
        (In i idxs <->
          0 <= i < h - add \/
          (add = 1 /\ i = x - 1) \/
          x <= i < x + (s - h))).
Proof.
  intros n x s h add Hn Hx Hadd Hh Hhs Htail.
  destruct Hadd as [-> | ->].
  - exists (Zrange 0 h ++ Zrange x (x + (s - h))).
    split; [|split; [|split]].
    + apply NoDup_app. repeat split.
      * apply NoDup_Zrange.
      * apply NoDup_Zrange.
      * intros i Hi Hj. apply In_Zrange in Hi. apply In_Zrange in Hj. lia.
    + rewrite Zlength_app, !Zlength_Zrange__solver_final_semantics by lia. lia.
    + intros j Hj. apply in_app_iff in Hj.
      destruct Hj as [Hj | Hj]; apply In_Zrange in Hj; lia.
    + intros j Hj. rewrite in_app_iff, !In_Zrange. simpl.
      replace (h - 0) with h by ring.
      assert (0 <> 1) by lia. tauto.
  - exists (Zrange 0 (h - 1) ++ (x - 1 :: nil) ++
      Zrange x (x + (s - h))).
    split; [|split; [|split]].
    + apply NoDup_app. repeat split.
      * apply NoDup_Zrange.
      * apply NoDup_app. repeat split.
        -- constructor; [simpl; tauto | constructor].
        -- apply NoDup_Zrange.
        -- intros i Hi Hj. simpl in Hi. apply In_Zrange in Hj.
           destruct Hi as [Heq | []]. subst i. lia.
      * intros i Hi Hj. apply In_Zrange in Hi. apply in_app_iff in Hj.
        destruct Hj as [Hj | Hj].
        -- simpl in Hj. destruct Hj as [Heq | []]. subst i. lia.
        -- apply In_Zrange in Hj. lia.
    + rewrite !Zlength_app, !Zlength_Zrange__solver_final_semantics by lia.
      rewrite Zlength_cons, Zlength_nil. unfold Z.succ. lia.
    + intros j Hj. repeat rewrite in_app_iff in Hj.
      destruct Hj as [Hj | [Hj | Hj]].
      * apply In_Zrange in Hj. lia.
      * simpl in Hj. destruct Hj as [Heq | []]. subst j. lia.
      * apply In_Zrange in Hj. lia.
    + intros j Hj. repeat rewrite in_app_iff. rewrite !In_Zrange. simpl.
      split.
      * intros [Ha | [[Hb | []] | Hc]].
        -- left. exact Ha.
        -- right. left. split; [reflexivity | lia].
        -- right. right. exact Hc.
      * intros [Ha | [[_ Hb] | Hc]].
        -- left. exact Ha.
        -- right. left. left. lia.
        -- right. right. exact Hc.
Qed.
Lemma candy_indices_to_sweet__solver_final_semantics :
  forall n l s idxs,
    0 < n -> NoDup idxs -> Zlength idxs = s ->
    (forall i, In i idxs -> 0 <= i < n) ->
    exists sweet : Z -> Prop,
      (forall p, sweet p -> 1 <= p <= n) /\
      set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p) = s /\
      (forall i, 0 <= i < n ->
        (sweet (1 + (l - 1 + i) mod n) <-> In i idxs)).
Proof.
  intros n l s idxs Hn Hnodup Hlen Hinrange.
  exists (fun p => In p
    (map (fun i : Z => 1 + (l - 1 + i) mod n) idxs)).
  assert (Hmapnodup : NoDup
    (map (fun i : Z => 1 + (l - 1 + i) mod n) idxs)).
  {
    apply Injective_map_NoDup_in.
    - intros i j Hi Hj Heq.
      eapply candy_position_injective_range__solver_final_semantics; eauto.
    - exact Hnodup.
  }
  split.
  - intros p Hp. apply in_map_iff in Hp.
    destruct Hp as [i [<- Hi]].
    pose proof (candy_position_bounds__solver_final_semantics n l i Hn). lia.
  - split.
    + rewrite (set_card_by_nodup_list__solver_final_semantics
        (fun p : Z => 1 <= p < n + 1 /\
          In p (map (fun i : Z => 1 + (l - 1 + i) mod n) idxs))
        (map (fun i : Z => 1 + (l - 1 + i) mod n) idxs)).
      * rewrite Zlength_map__solver_final_semantics. exact Hlen.
      * exact Hmapnodup.
      * intros p. split.
        -- intros [_ Hp]. exact Hp.
        -- intros Hp. split; [|exact Hp].
           apply in_map_iff in Hp. destruct Hp as [i [<- Hi]].
           pose proof (candy_position_bounds__solver_final_semantics n l i Hn). lia.
    + intros i Hi. split.
      * intros Hsweet. apply in_map_iff in Hsweet.
        destruct Hsweet as [j [Heq Hj]].
        assert (Hjrange : 0 <= j < n) by (apply Hinrange; exact Hj).
        assert (j = i).
        {
          eapply candy_position_injective_range__solver_final_semantics; eauto.
        }
        subst j. exact Hj.
      * intros Hiin. apply in_map_iff.
        exists i. split; [reflexivity | exact Hiin].
Qed.
Lemma candy_selected_prefix_count__solver_final_semantics :
  forall n l x s h add sweet idxs,
    0 < n -> 1 <= x <= n -> (add = 0 \/ add = 1) ->
    add <= h <= x -> h <= s -> 0 <= s - h <= n - x ->
    (forall i, 0 <= i < n ->
      (sweet (1 + (l - 1 + i) mod n) <-> In i idxs)) ->
    (forall i, 0 <= i < n ->
      (In i idxs <->
        0 <= i < h - add \/
        (add = 1 /\ i = x - 1) \/
        x <= i < x + (s - h))) ->
    sum (fun i : Z => 0 <= i < x)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) = h /\
    (add = 1 -> sweet (1 + (l - 1 + (x - 1)) mod n)).
Proof.
  intros n l x s h add sweet idxs Hn Hx Hadd Hh Hhs Htail Hsweet Hidx.
  destruct Hadd as [Hadd | Hadd]; subst add.
  - split; [|discriminate].
    rewrite (sum_Z_range_split 0 h x) by lia.
    assert (Hones :
      sum (fun i : Z => 0 <= i < h)
        (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) = h).
    {
      transitivity (sum (fun i : Z => 0 <= i < h) (fun _ => 1)).
      - apply sum_Z_range_ext. intros i Hi.
        destruct (candy_bit_cases__solver_final_semantics sweet
          (1 + (l - 1 + i) mod n)) as [[_ Hb] | [Hns Hb]]; [exact Hb |].
        exfalso. apply Hns. apply Hsweet; [lia |]. apply Hidx; [lia |].
        left. lia.
      - rewrite sum_Z_range_const by lia. ring.
    }
    assert (Hzeros :
      sum (fun i : Z => h <= i < x)
        (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) = 0).
    {
      apply sum_Z_range_eq_zero. intros i Hi.
      destruct (candy_bit_cases__solver_final_semantics sweet
        (1 + (l - 1 + i) mod n)) as [[Hs Hb] | [_ Hb]]; [|exact Hb].
      exfalso. apply Hsweet in Hs; [|lia]. apply Hidx in Hs; [|lia].
      destruct Hs as [Ha | [[Hbad _] | Hc]]; lia.
    }
    rewrite Hones, Hzeros. lia.
  - split.
    + rewrite (sum_Z_range_split 0 (h - 1) x) by lia.
      rewrite (sum_Z_range_split (h - 1) (x - 1) x) by lia.
      assert (Hones :
        sum (fun i : Z => 0 <= i < h - 1)
          (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) =
        h - 1).
      {
        transitivity (sum (fun i : Z => 0 <= i < h - 1) (fun _ => 1)).
        - apply sum_Z_range_ext. intros i Hi.
          destruct (candy_bit_cases__solver_final_semantics sweet
            (1 + (l - 1 + i) mod n)) as [[_ Hb] | [Hns Hb]]; [exact Hb |].
          exfalso. apply Hns. apply Hsweet; [lia |]. apply Hidx; [lia |].
          left. lia.
        - rewrite sum_Z_range_const by lia. ring.
      }
      assert (Hzeros :
        sum (fun i : Z => h - 1 <= i < x - 1)
          (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) = 0).
      {
        apply sum_Z_range_eq_zero. intros i Hi.
        destruct (candy_bit_cases__solver_final_semantics sweet
          (1 + (l - 1 + i) mod n)) as [[Hs Hb] | [_ Hb]]; [|exact Hb].
        exfalso. apply Hsweet in Hs; [|lia]. apply Hidx in Hs; [|lia].
        destruct Hs as [Ha | [[_ Hbpos] | Hc]]; lia.
      }
      assert (Hlast :
        sum (fun i : Z => x - 1 <= i < x)
          (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) = 1).
      {
        pose proof (sum_Z_range_single (x - 1)
          (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0))
          as Hsingle.
        replace (x - 1 + 1) with x in Hsingle by ring.
        rewrite Hsingle.
        destruct (candy_bit_cases__solver_final_semantics sweet
          (1 + (l - 1 + (x - 1)) mod n)) as [[_ Hb] | [Hns Hb]]; [exact Hb |].
        exfalso. apply Hns. apply Hsweet; [lia |]. apply Hidx; [lia |].
        right. left. split; lia.
      }
      rewrite Hones, Hzeros, Hlast. lia.
    + intros _. apply Hsweet; [lia |]. apply Hidx; [lia |].
      right. left. split; lia.
Qed.
Lemma candy_Znth_map_Zrange__solver_final_semantics :
  forall (f : Z -> Z) high d i,
    0 <= high -> 0 <= i < high ->
    Znth i (map f (Zrange 0 high)) d = f i.
Proof.
  intros f high d i Hhigh Hi.
  rewrite Znth_map__solver_final_semantics with (da := 0).
  - rewrite Znth_Zrange__solver_final_semantics by lia. reflexivity.
  - rewrite Zlength_Zrange__solver_final_semantics by lia. lia.
Qed.
Lemma candy_build_observation__solver_final_semantics :
  forall n l r x k s add (sweet : Z -> Prop),
    0 < n -> 1 <= k -> 1 <= l <= n -> 1 <= r <= n -> 1 <= x <= n ->
    x = (r - l + n) mod n + 1 ->
    CandyArithmeticCandidate n x k (n + s) add ->
    (forall p, sweet p -> 1 <= p <= n) ->
    set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p) = s ->
    sum (fun i : Z => 0 <= i < x)
      (fun i => if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0) =
      k - x + add - ((k - 1) / (n + s)) * (n + s) ->
    (add = 1 -> sweet (1 + (l - 1 + (x - 1)) mod n)) ->
    CandyObservation n l r k sweet.
Proof.
  intros n l r x k s add sweet Hn Hk Hl Hr Hx Hxdef Hcand
    Hsweetbound Hcard Hprefix Hlastsweet.
  unfold CandyArithmeticCandidate in Hcand. cbn zeta in Hcand.
  destruct Hcand as [Hnum [Hadd [Hh [Hhs Htail]]]].
  set (q := (k - 1) / (n + s)).
  set (h := k - x + add - q * (n + s)).
  fold q h in Hh, Hhs, Htail, Hprefix.
  assert (Hs : 0 <= s <= n) by nia.
  assert (Hq : 0 <= q).
  {
    unfold q. apply Z_div_nonneg_nonneg; lia.
  }
  set (steps := q * n + x).
  assert (Hsteps : 1 <= steps) by (unfold steps; nia).
  set (bit := fun i : Z =>
    if prop_dec (sweet (1 + (l - 1 + i) mod n)) then 1 else 0).
  set (takefun := fun i : Z =>
    1 + bit i - (if Z.eq_dec i (steps - 1) then add else 0)).
  assert (Hbitlast : add = 1 -> bit (steps - 1) = 1).
  {
    intros Hadd1. unfold bit.
    assert (Hpos :
      1 + (l - 1 + (steps - 1)) mod n =
      1 + (l - 1 + (x - 1)) mod n).
    {
      unfold steps.
      replace (q * n + x - 1) with ((x - 1) + q * n) by ring.
      apply candy_position_multiple_period__solver_final_semantics. lia.
    }
    rewrite Hpos.
    destruct (candy_bit_cases__solver_final_semantics sweet
      (1 + (l - 1 + (x - 1)) mod n)) as [[_ Hb] | [Hns Hb]].
    - exact Hb.
    - exfalso. apply Hns. apply Hlastsweet. exact Hadd1.
  }
  assert (Htakebounds : forall i, 0 <= i < steps -> 1 <= takefun i <= 2).
  {
    intros i Hi. unfold takefun.
    destruct (Z.eq_dec i (steps - 1)) as [Heq | Hneq].
    - subst i. destruct Hadd as [-> | ->].
      + destruct (candy_bit_cases__solver_final_semantics sweet
          (1 + (l - 1 + (steps - 1)) mod n)) as [[_ Hb] | [_ Hb]].
        * assert (bit (steps - 1) = 1) by (unfold bit; exact Hb).
          rewrite H. lia.
        * assert (bit (steps - 1) = 0) by (unfold bit; exact Hb).
          rewrite H. lia.
      + rewrite Hbitlast by reflexivity. lia.
    - destruct (candy_bit_cases__solver_final_semantics sweet
        (1 + (l - 1 + i) mod n)) as [[_ Hb] | [_ Hb]].
      + assert (bit i = 1) by (unfold bit; exact Hb). rewrite H. lia.
      + assert (bit i = 0) by (unfold bit; exact Hb). rewrite H. lia.
  }
  assert (Htotal :
    sum (fun i : Z => 0 <= i < steps) takefun = k).
  {
    unfold takefun.
    rewrite sum_Z_range_sub, sum_Z_range_add.
    rewrite sum_Z_range_const by lia.
    rewrite candy_last_indicator_sum__solver_final_semantics by exact Hsteps.
    assert (Hvisits : sum (fun i : Z => 0 <= i < steps) bit = q * s + h).
    {
      unfold steps, bit.
      rewrite candy_cycles_prefix_sum__solver_final_semantics by lia.
      rewrite Hcard, Hprefix. fold q h. reflexivity.
    }
    fold bit. rewrite Hvisits. unfold h, steps. ring.
  }
  set (friends := map (fun i : Z => 1 + (l - 1 + i) mod n)
    (Zrange 0 steps)).
  set (taken := map takefun (Zrange 0 steps)).
  set (remaining := map
    (fun j : Z => k - sum (fun i : Z => 0 <= i < j) takefun)
    (Zrange 0 (steps + 1))).
  split; [exact Hsweetbound |].
  exists friends, remaining, taken, steps.
  assert (Hfriendslen : Zlength friends = steps).
  {
    unfold friends. rewrite Zlength_map__solver_final_semantics.
    rewrite Zlength_Zrange__solver_final_semantics by lia. lia.
  }
  assert (Htakenlen : Zlength taken = steps).
  {
    unfold taken. rewrite Zlength_map__solver_final_semantics.
    rewrite Zlength_Zrange__solver_final_semantics by lia. lia.
  }
  assert (Hremaininglen : Zlength remaining = steps + 1).
  {
    unfold remaining. rewrite Zlength_map__solver_final_semantics.
    rewrite Zlength_Zrange__solver_final_semantics by lia. lia.
  }
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - exact Hfriendslen.
  - exact Hremaininglen.
  - exact Htakenlen.
  - unfold friends. rewrite candy_Znth_map_Zrange__solver_final_semantics by lia.
    apply candy_position_zero__solver_final_semantics; assumption.
  - unfold remaining. rewrite candy_Znth_map_Zrange__solver_final_semantics by lia.
    rewrite sum_Z_range_empty by lia. lia.
  - intros i Hi.
    assert (Hfriendi : Znth i friends 0 = 1 + (l - 1 + i) mod n).
    { unfold friends. rewrite candy_Znth_map_Zrange__solver_final_semantics by lia.
      reflexivity. }
    assert (Htakeni : Znth i taken 0 = takefun i).
    { unfold taken. rewrite candy_Znth_map_Zrange__solver_final_semantics by lia.
      reflexivity. }
    assert (Hremi : Znth i remaining 0 =
      k - sum (fun j : Z => 0 <= j < i) takefun).
    { unfold remaining. rewrite candy_Znth_map_Zrange__solver_final_semantics by lia.
      reflexivity. }
    assert (Hremnext : Znth (i + 1) remaining 0 =
      k - sum (fun j : Z => 0 <= j < i + 1) takefun).
    { unfold remaining. rewrite candy_Znth_map_Zrange__solver_final_semantics by lia.
      reflexivity. }
    assert (Hsuffix : Znth i remaining 0 =
      sum (fun j : Z => i <= j < steps) takefun).
    {
      rewrite Hremi, <- Htotal.
      rewrite (sum_Z_range_split 0 i steps) by lia. ring.
    }
    assert (Hfuture_nonneg : 0 <=
      sum (fun j : Z => i + 1 <= j < steps) takefun).
    {
      pose proof (sum_Z_range_lower_bound (i + 1) steps takefun 1
        ltac:(lia) ltac:(intros j Hj; specialize (Htakebounds j ltac:(lia)); lia)).
      lia.
    }
    assert (Hcurrent : Znth i remaining 0 =
      takefun i + sum (fun j : Z => i + 1 <= j < steps) takefun).
    {
      rewrite Hsuffix, sum_Z_range_cons by lia. reflexivity.
    }
    split.
    + unfold CandyTaken. rewrite Hfriendi, Htakeni.
      destruct (candy_bit_cases__solver_final_semantics sweet
        (1 + (l - 1 + i) mod n)) as [[Hswi Hbi] | [Hnswi Hbi]].
      * assert (Hbiti : bit i = 1) by (unfold bit; exact Hbi).
        left. split; [exact Hswi |].
        unfold takefun. rewrite Hbiti.
        destruct (Z.eq_dec i (steps - 1)) as [Heq | Hneq].
        -- subst i. destruct Hadd as [-> | ->].
           ++ assert (Htv : takefun (steps - 1) = 2).
              { unfold takefun. rewrite Hbiti.
                destruct (Z.eq_dec (steps - 1) (steps - 1)); lia. }
              left. split; [rewrite Htv in Hcurrent; lia | lia].
           ++ assert (Htv : takefun (steps - 1) = 1).
              { unfold takefun. rewrite Hbiti.
                destruct (Z.eq_dec (steps - 1) (steps - 1)); lia. }
              right. split; [|lia].
              rewrite Htv in Hcurrent.
              rewrite sum_Z_range_empty in Hcurrent by lia. lia.
        -- assert (Htv : takefun i = 2).
           { unfold takefun. rewrite Hbiti.
             destruct (Z.eq_dec i (steps - 1)); [contradiction | lia]. }
           left. split; [rewrite Htv in Hcurrent; lia | lia].
      * assert (Hbiti : bit i = 0) by (unfold bit; exact Hbi).
        assert (Htv : takefun i = 1).
        {
          unfold takefun. rewrite Hbiti.
          destruct (Z.eq_dec i (steps - 1)) as [Heq | Hneq].
          - subst i. destruct Hadd as [-> | Hadd1]; [lia |].
            exfalso. apply Hnswi.
            pose proof (Hlastsweet Hadd1) as Hsx.
            unfold steps.
            replace (q * n + x - 1) with ((x - 1) + q * n) by ring.
            rewrite candy_position_multiple_period__solver_final_semantics by lia.
            exact Hsx.
          - lia.
        }
        right. split; [exact Hnswi |]. split; [|lia].
        rewrite Htv in Hcurrent. lia.
    + split.
      * rewrite Hremnext, Hremi, Htakeni.
        rewrite sum_Z_range_extend_right by lia. ring.
      * intros Hinext.
        unfold friends.
        rewrite !candy_Znth_map_Zrange__solver_final_semantics by lia.
        apply candy_position_succ__solver_final_semantics. exact Hn.
  - unfold friends. rewrite candy_Znth_map_Zrange__solver_final_semantics by lia.
    unfold steps.
    replace (q * n + x - 1) with ((x - 1) + q * n) by ring.
    rewrite candy_position_multiple_period__solver_final_semantics by lia.
    apply candy_distance_endpoint__solver_final_semantics; assumption.
  - unfold remaining. rewrite candy_Znth_map_Zrange__solver_final_semantics by lia.
    rewrite Htotal. lia.
Qed.
Lemma candy_observation_arithmetic_equiv__solver_final_semantics :
  forall n l r x k s,
    0 < n -> 1 <= k -> 1 <= l <= n -> 1 <= r <= n -> 1 <= x <= n ->
    x = (r - l + n) mod n + 1 ->
    ((exists sweet : Z -> Prop,
        CandyObservation n l r k sweet /\
        set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p) = s) <->
     exists add, CandyArithmeticCandidate n x k (n + s) add).
Proof.
  intros n l r x k s Hn Hk Hl Hr Hx Hxdef. split.
  - intros [sweet [Hobs Hcard]].
    destruct (candy_observation_to_arithmetic__solver_final_semantics
      n l r x k sweet Hn Hl Hr Hx Hxdef Hobs) as [add Hcand].
    exists add. rewrite Hcard in Hcand. exact Hcand.
  - intros [add Hcand].
    pose proof Hcand as Hparts.
    unfold CandyArithmeticCandidate in Hparts. cbn zeta in Hparts.
    destruct Hparts as [Hnum [Hadd [Hh [Hhs Htail]]]].
    set (q := (k - 1) / (n + s)).
    set (h := k - x + add - q * (n + s)).
    fold q h in Hh, Hhs, Htail.
    destruct (candy_selected_indices__solver_final_semantics
      n x s h add Hn Hx Hadd Hh ltac:(nia) ltac:(nia))
      as [idxs [Hnodup [Hlen [Hinrange Hidx]]]].
    destruct (candy_indices_to_sweet__solver_final_semantics
      n l s idxs Hn Hnodup Hlen Hinrange)
      as [sweet [Hsbound [Hcard Hsweet]]].
    destruct (candy_selected_prefix_count__solver_final_semantics
      n l x s h add sweet idxs Hn Hx Hadd Hh ltac:(nia) ltac:(nia)
      Hsweet Hidx) as [Hprefix Hlastsweet].
    exists sweet. split; [|exact Hcard].
    eapply candy_build_observation__solver_final_semantics; eauto.
Qed.
Lemma candy_max_transport__solver_final_semantics :
  forall n l r x k best,
    0 < n -> 1 <= k -> 1 <= l <= n -> 1 <= r <= n -> 1 <= x <= n ->
    x = (r - l + n) mod n + 1 ->
    CandySearchPrefix n x k (2 * n + 1) best ->
    Spec n l r k best.
Proof.
  intros n l r x k best Hn Hk Hl Hr Hx Hxdef Hsearch.
  unfold CandySearchPrefix, max_value_of_subset_with_default in Hsearch.
  unfold Spec.
  destruct Hsearch as [[Hmaximum Hdefault] | [Hupper Hbest]].
  - right. unfold max_value_of_subset, max_object_of_subset in *.
    destruct Hmaximum as [[num add] [[[Hcand Hupto] Hdom] Hscore]].
    simpl in Hscore. subst best.
    assert (Hexists : exists sweet : Z -> Prop,
        CandyObservation n l r k sweet /\
        set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p) = num - n).
    {
      apply (proj2 (candy_observation_arithmetic_equiv__solver_final_semantics
        n l r x k (num - n) Hn Hk Hl Hr Hx Hxdef)).
      exists add. replace (n + (num - n)) with num by ring. exact Hcand.
    }
    destruct Hexists as [sweet [Hobs Hcard]].
    exists (sweet, num - n). split.
    + split.
      * simpl. split; [exact Hobs | symmetry; exact Hcard].
      * intros [sweet' score'] Hcandidate. simpl.
        destruct Hcandidate as [Hobs' Hscorecard]. simpl in Hobs', Hscorecard.
        assert (Hexists' : exists add',
          CandyArithmeticCandidate n x k (n + score') add').
        {
          apply (proj1 (candy_observation_arithmetic_equiv__solver_final_semantics
            n l r x k score' Hn Hk Hl Hr Hx Hxdef)).
          exists sweet'. split; [exact Hobs' |]. symmetry. exact Hscorecard.
        }
        destruct Hexists' as [add' Hcand'].
        specialize (Hdom (n + score', add')).
        assert (Hupto' : n + score' < 2 * n + 1).
        { unfold CandyArithmeticCandidate in Hcand'. cbn zeta in Hcand'. nia. }
        specialize (Hdom ltac:(split; [exact Hcand' | exact Hupto'])).
        simpl in Hdom. lia.
    + reflexivity.
  - left. split.
    + symmetry. exact Hbest.
    + intros sweet Hobs.
      set (score := set_card (fun p : Z => 1 <= p < n + 1 /\ sweet p)).
      assert (Hexists : exists add,
          CandyArithmeticCandidate n x k (n + score) add).
      {
        apply (proj1 (candy_observation_arithmetic_equiv__solver_final_semantics
          n l r x k score Hn Hk Hl Hr Hx Hxdef)).
        exists sweet. split; [exact Hobs | reflexivity].
      }
      destruct Hexists as [add Hcand].
      specialize (Hupper (n + score, add)).
      assert (Hupto : n + score < 2 * n + 1).
      { unfold CandyArithmeticCandidate in Hcand. cbn zeta in Hcand. nia. }
      specialize (Hupper ltac:(split; [exact Hcand | exact Hupto])).
      simpl in Hupper.
      unfold CandyArithmeticCandidate in Hcand. cbn zeta in Hcand. nia.
Qed.
Lemma z_le_div_iff_mul_le__check_feasible_intervals :
  forall a b z : Z, 0 <= a -> 0 < b -> (z <= a ÷ b <-> b * z <= a).
Proof.
  intros a b z Ha Hb.
  split.
  - intros Hz.
    pose proof (Z.mul_le_mono_nonneg_l z (a ÷ b) b (Z.lt_le_incl _ _ Hb) Hz).
    assert (Hb0 : b <> 0) by lia.
    pose proof (Z.mul_quot_le a b Ha Hb0).
    lia.
  - intros Hz.
    apply Z.quot_le_lower_bound; assumption.
Qed.
Lemma z_ceil_characterization__check_feasible_intervals :
  forall a d r z : Z,
    0 < d ->
    (r - 1) * d < a ->
    a <= r * d ->
    (r <= z <-> a <= d * z).
Proof.
  intros a d r z Hd Hrlo Hrhi.
  split.
  - intros Hrz.
    pose proof (Z.mul_le_mono_nonneg_r r z d (Z.lt_le_incl _ _ Hd) Hrz).
    lia.
  - intros Haz.
    assert ((r - 1) * d < z * d) by lia.
    apply (proj2 (Z.mul_lt_mono_pos_r d (r - 1) z Hd)) in H.
    lia.
Qed.
Lemma candy_prefix_to_phase0_block__solver_quotient_routes :
  forall n x k L R best,
    CandySearchPrefix n x k L best ->
    CandySearchBlock n x k L R 0 best.
Proof.
  intros n x k L R best Hprefix.
  unfold CandySearchPrefix in Hprefix.
  unfold CandySearchBlock.
  assert (Heq : forall candidate : Z * Z,
      (CandyArithmeticCandidate n x k (fst candidate) (snd candidate) /\
       fst candidate < L) <->
      (CandyArithmeticCandidate n x k (fst candidate) (snd candidate) /\
       (fst candidate < L \/
        (L <= fst candidate <= R /\ snd candidate < 0)))).
  {
    intros [num add]. simpl.
    split.
    - intros [Hcandidate Hlt].
      split; [exact Hcandidate | left; exact Hlt].
    - intros [Hcandidate [Hlt | [_ Hadd]]].
      + split; assumption.
      + unfold CandyArithmeticCandidate in Hcandidate.
        destruct Hcandidate as [_ [[Hadd0 | Hadd1] _]];
          subst add; lia.
  }
  unfold max_value_of_subset_with_default in *.
  unfold max_value_of_subset, max_object_of_subset in *.
  destruct Hprefix as [[[candidate [[Hmember Hgreatest] Hvalue]] Hdefault]
                       | [Hbounded Hvalue]].
  - left. split.
    + exists candidate. split.
      * split.
        -- apply (proj1 (Heq candidate)); exact Hmember.
        -- intros other Hother.
           apply Hgreatest.
           apply (proj2 (Heq other)); exact Hother.
      * exact Hvalue.
    + exact Hdefault.
  - right. split.
    + intros candidate Hmember.
      apply Hbounded.
      apply (proj2 (Heq candidate)); exact Hmember.
    + exact Hvalue.
Qed.
Lemma quotient_block_plateau__solver_quotient_routes :
  forall z L,
    0 <= z ->
    0 < L ->
    0 < z / L ->
    L <= z / (z / L) /\
    forall num, L <= num <= z / (z / L) -> z / L = z / num.
Proof.
  intros z L Hz HL Hq.
  set (q := z / L) in *.
  assert (HqL : q * L <= z).
  {
    subst q.
    rewrite Z.mul_comm.
    apply Z.mul_div_le; lia.
  }
  assert (HLend : L <= z / q).
  {
    apply Z.div_le_lower_bound; nia.
  }
  split; [exact HLend |].
  intros num [HnumL Hnumend].
  assert (Hnumpos : 0 < num) by lia.
  assert (Hqnum : q * num <= z).
  {
    pose proof (Z.mul_div_le z q ltac:(lia)) as Hend.
    nia.
  }
  assert (Hlower : q <= z / num).
  {
    apply Z.div_le_lower_bound; nia.
  }
  assert (Hzupper : z < L * (q + 1)).
  {
    pose proof (Z.mod_pos_bound z L ltac:(lia)) as Hmod.
    pose proof (Z.div_mod z L ltac:(lia)) as Hdecomp.
    fold q in Hdecomp.
    nia.
  }
  assert (Hupper : z / num < q + 1).
  {
    apply Z.div_lt_upper_bound; nia.
  }
  lia.
Qed.
Lemma quotient_block_zero__solver_quotient_routes :
  forall k L R,
    0 <= k - 1 ->
    0 < L ->
    (k - 1) / L = 0 ->
    QuotientBlock k L R 0.
Proof.
  intros k L R Hz HL Hzero.
  unfold QuotientBlock.
  intros num [HnumL HnumR].
  assert (Hnumpos : 0 < num) by lia.
  assert (Hzlt : k - 1 < L).
  {
    pose proof (Z.mod_pos_bound (k - 1) L ltac:(lia)) as Hmod.
    pose proof (Z.div_mod (k - 1) L ltac:(lia)) as Hdecomp.
    rewrite Hzero in Hdecomp.
    nia.
  }
  assert (Hnonneg : 0 <= (k - 1) / num).
  {
    apply Z.div_pos; lia.
  }
  assert (Hltone : (k - 1) / num < 1).
  {
    apply Z.div_lt_upper_bound; nia.
  }
  lia.
Qed.
Lemma candy_max_bound__check_block_updates : forall (P : Z * Z -> Prop) n b,
  max_value_of_subset_with_default Z.le P (fun c => fst c - n) (-1) b ->
  forall c, P c -> fst c - n <= b.
Proof.
  intros P n b [[ [a [[Ha Hbound] Heq]] Hd] | [Hbound Heq]] c Hc.
  - specialize (Hbound c Hc). lia.
  - specialize (Hbound c Hc). lia.
Qed.
Lemma candy_phase_preserve__check_block_updates : forall n x k L R p b,
  CandySearchBlock n x k L R p b ->
  (forall num, L <= num <= R -> CandyArithmeticCandidate n x k num p -> num - n <= b) ->
  CandySearchBlock n x k L R (p+1) b.
Proof.
  intros n x k L R p b Hold Hnew.
  pose proof (candy_max_bound__check_block_updates _ _ _ Hold) as Hbound.
  assert (Hb : forall c : Z * Z,
    CandyArithmeticCandidate n x k (fst c) (snd c) /\
      (fst c < L \/ (L <= fst c <= R /\ snd c < p+1)) -> fst c-n <= b).
  { intros [num add] [Hc [Hl | [Hr Hp]]]; simpl in *.
    - apply (Hbound (num,add)). simpl. auto.
    - destruct (Z_lt_ge_dec add p).
      + apply (Hbound (num,add)). simpl. auto.
      + assert (add=p) by lia. subst add. apply Hnew; auto. }
  unfold CandySearchBlock in *.
  destruct Hold as [[ [a [[Ha Hba] Heq]] Hd] | [Hba Heq]].
  - left. split; [|exact Hd]. exists a. split; [|exact Heq].
    split.
    + destruct Ha as [Hc [Hl | [Hr Hp]]]; split; auto; right; split; auto; lia.
    + intros c Hc. specialize (Hb c Hc). lia.
  - right. split; [|exact Heq]. intros c Hc. specialize (Hb c Hc). lia.
Qed.
Lemma candy_search_block_phase_update__check_block_updates : forall n x k L R q p lo hi b,
  L <= lo -> hi <= R -> lo <= hi -> b < hi-n -> -1 <= b ->
  CandyFeasibleInterval n x k L R q p lo hi ->
  CandySearchBlock n x k L R p b ->
  CandySearchBlock n x k L R (p+1) (hi-n).
Proof.
  intros n x k L R q p lo hi b HL HR Hlh Hbetter Hd Hinterval Hold.
  pose proof (candy_max_bound__check_block_updates _ _ _ Hold) as Hbound.
  unfold CandySearchBlock. left. split; [|lia].
  exists (hi,p). split; [|reflexivity]. split.
  - simpl. split.
    + apply (proj2 (Hinterval hi ltac:(lia))). lia.
    + right. change (L <= hi <= R /\ p < p+1). repeat split; lia.
  - intros [num add] [Hc [Hl | [Hr Hp]]]; simpl in *.
    + specialize (Hbound (num,add) ltac:(simpl; auto)). simpl in Hbound. lia.
    + destruct (Z_lt_ge_dec add p).
      * specialize (Hbound (num,add) ltac:(simpl; auto)). simpl in Hbound. lia.
      * assert (add=p) by lia. subst add.
        apply (proj1 (Hinterval num Hr)) in Hc. lia.
Qed.
Lemma candy_phase2_block_to_prefix__solver_init_close :
  forall n x k cur R best,
    cur <= R ->
    CandySearchBlock n x k cur R 2 best ->
    CandySearchPrefix n x k (R + 1) best.
Proof.
  intros n x k cur R best HcurR Hblock.
  unfold CandySearchBlock in Hblock.
  unfold CandySearchPrefix.
  eapply (max_default_eq_forward Z.le).
  - exact Hblock.
  - intros [num add] [Hcandidate Hrange].
    exists (num, add).
    split.
    + split; [exact Hcandidate |].
      destruct Hrange as [Hlt | [Hbounds Hadd]]; lia.
    + lia.
  - intros [num add] [Hcandidate Hlt].
    exists (num, add).
    split.
    + split; [exact Hcandidate |].
      destruct (Z_lt_ge_dec num cur) as [Hnum | Hnum].
      * left; exact Hnum.
      * right.
        cbn in Hlt |-.
        split.
        -- split.
           ++ cbn; lia.
           ++ cbn; lia.
        --
        unfold CandyArithmeticCandidate in Hcandidate.
        cbn in Hcandidate.
        destruct Hcandidate as [_ [[Hadd | Hadd] _]]; subst add; cbn; lia.
    + lia.
Qed.
Lemma candy_search_block_skip_infeasible__check_qzero_returns :
  forall n x k L R add best,
  QuotientBlock k L R 0 ->
  (k - x + add < add \/ x < k - x + add) ->
  CandySearchBlock n x k L R add best ->
  CandySearchBlock n x k L R (add + 1) best.
Proof.
  intros n x k L R add best Hq Hbad Hbest.
  assert (Hempty : forall num, L <= num <= R ->
    ~ CandyArithmeticCandidate n x k num add).
  { intros num Hr Hc. specialize (Hq num Hr).
    unfold CandyArithmeticCandidate in Hc.
    rewrite <- Hq in Hc. simpl in Hc.
    destruct Hc as [_ [_ [Hc _]]]. destruct Hbad; lia. }
  assert (Heq : forall c : Z * Z,
    (CandyArithmeticCandidate n x k (fst c) (snd c) /\
      (fst c < L \/ (L <= fst c <= R /\ snd c < add + 1))) <->
    (CandyArithmeticCandidate n x k (fst c) (snd c) /\
      (fst c < L \/ (L <= fst c <= R /\ snd c < add)))).
  { intros [num a]; simpl. split.
    - intros [Hc [Hl|[Hr Ha]]]; split; auto.
      destruct (Z.eq_dec a add) as [He|He].
      + subst a. exfalso. exact (Hempty num Hr Hc).
      + right. split; auto. lia.
    - intros [Hc [Hl|[Hr Ha]]]; split; auto.
      right. split; auto. lia. }
  unfold CandySearchBlock, max_value_of_subset_with_default,
    max_value_of_subset, max_object_of_subset in *.
  destruct Hbest as [[[c [[Hc Hmax] Hvalue]] Hbound]|[Hmax Hvalue]].
  - left. split; [|exact Hbound]. exists c. split; [|exact Hvalue].
    split.
    + apply (proj2 (Heq c)). exact Hc.
    + intros b Hb. apply Hmax. apply (proj1 (Heq b)). exact Hb.
  - right. split; [|exact Hvalue].
    intros b Hb. apply Hmax. apply (proj1 (Heq b)). exact Hb.
Qed.
