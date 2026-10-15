Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition BiteStep (m : Z) (a b : list Z) : Prop :=
  exists chosen : list Z, NoDup chosen /\ Zlength chosen <= m /\ (Forall (fun i => 0 <= i < (Zlength a)) chosen) /\
  Forall (fun i => Znth i a 0 > 0) chosen /\ Zlength b = Zlength a /\
  forall i, 0 <= i < Zlength a -> Znth i b 0 = if existsb (Z.eqb i) chosen then Znth i a 0 - 1 else Znth i a 0.
Definition Eatable (A B l t m r : Z) : Prop :=
  l <= r /\ exists st : list (list Z), 1 <= Zlength st <= t + 1 /\
  Znth 0 st [] = map (fun i => A + (l + i - 1) * B) (Zrange 0 (r - l + 1)) /\
  (forall q, 0 <= q < Zlength st - 1 -> BiteStep m (Znth q st []) (Znth (q + 1) st [])) /\
  Forall (fun x => x = 0) (Znth (Zlength st - 1) st []).
Definition QueryAnswer (A B : Z) (q : Z * Z * Z) (ans : Z) : Prop :=
  let ' (l, t, m) := q in
  (ans = (- 1) /\ ~Eatable A B l t m l) \/
  (ans >= l /\ Eatable A B l t m ans /\ ~Eatable A B l t m (ans + 1)).
Definition Pre (A B : Z) (queries : list (Z * Z * Z)) : Prop :=
  (* Stated explicitly in the P065 solver Require, so dropped here:
       1 <= Zlength queries <= 100000 /\
       Forall (fun q => let ' (l, t, m) := q in 1 <= l <= 1000000 /\ 1 <= t <= 1000000 /\ 1 <= m <= 1000000) queries /\
       1 <= A <= 1000000 /\
       1 <= B <= 1000000  *)
  True.

Definition Spec (A B : Z) (queries : list (Z * Z * Z)) (out : list Z) : Prop :=
  Zlength out = Zlength queries /\ forall i, 0 <= i < Zlength queries ->
  QueryAnswer A B (Znth i queries (0, 0, 0)) (Znth i out 0).

Require Import Coq.micromega.Lia.
Lemma count_true__query_semantic_core : list bool -> nat.
Proof.
  exact (fix go bs :=
    match bs with
    | [] => O
    | b :: bs' => if b then S (go bs') else go bs'
    end).
Defined.
Lemma count_eq__query_semantic_core : Z -> list Z -> nat.
Proof.
  exact (fun v => fix go xs :=
    match xs with
    | [] => O
    | x :: xs' => if Z.eqb x v then S (go xs') else go xs'
    end).
Defined.
Lemma count_other_pos__query_semantic_core : Z -> list Z -> nat.
Proof.
  exact (fun v => fix go xs :=
    match xs with
    | [] => O
    | x :: xs' =>
        if Z.eqb x v then go xs'
        else if Z.ltb 0 x then S (go xs') else go xs'
    end).
Defined.
Lemma greedy_mask__query_semantic_core : Z -> nat -> list Z -> list bool.
Proof.
  exact (fun v => fix go quota xs {struct xs} :=
    match xs with
    | [] => []
    | x :: xs' =>
        if Z.eqb x v then true :: go quota xs'
        else if Z.ltb 0 x then
          match quota with
          | O => false :: go O xs'
          | S quota' => true :: go quota' xs'
          end
        else false :: go quota xs'
    end).
Defined.
Lemma true_indices_from__query_semantic_core : Z -> list bool -> list Z.
Proof.
  exact (fix go p bs {struct bs} :=
    match bs with
    | [] => []
    | b :: bs' =>
        if b then p :: go (p + 1) bs' else go (p + 1) bs'
    end).
Defined.
Lemma apply_mask__query_semantic_core : list Z -> list bool -> list Z.
Proof.
  exact (fix go xs bs {struct xs} :=
    match xs, bs with
    | x :: xs', b :: bs' => (if b then x - 1 else x) :: go xs' bs'
    | _, _ => []
    end).
Defined.
Lemma BiteSteps__query_semantic_core : Z -> list (list Z) -> Prop.
Proof.
  exact (fun m => fix go st :=
    match st with
    | [] => True
    | a :: tail =>
        match tail with
        | [] => True
        | b :: _ => BiteStep m a b /\ go tail
        end
    end).
Defined.
Lemma greedy_mask_length__query_semantic_core : forall v q xs,
  length (greedy_mask__query_semantic_core v q xs) = length xs.
Proof.
  intros v q xs. revert q.
  induction xs as [|x xs IH]; intros q; simpl; auto.
  destruct (Z.eqb x v); simpl; auto.
  destruct (Z.ltb 0 x); simpl; auto.
  destruct q; simpl; auto.
Qed.
Lemma single_indicator_sum__query_semantic_core : forall n c,
  0 <= c < n ->
  @SumLib.Sum.sum Z (fun i => 0 <= i < n) (SumLib.ZRange.finite_Z_range 0 n)
    (fun i => if Z.eqb i c then 1 else 0) = 1.
Proof.
  intros n c Hc.
  rewrite (sum_Z_range_split 0 c n) by lia.
  rewrite sum_Z_range_eq_zero.
  2:{ intros i Hi. destruct (Z.eqb i c) eqn:Hic; [|reflexivity].
      apply Z.eqb_eq in Hic. lia. }
  rewrite sum_Z_range_cons by lia.
  rewrite Z.eqb_refl.
  rewrite sum_Z_range_eq_zero.
  - lia.
  - intros i Hi. destruct (Z.eqb i c) eqn:Hic; [|reflexivity].
    apply Z.eqb_eq in Hic. lia.
Qed.
Lemma chosen_indicator_sum__query_semantic_core : forall n chosen,
  NoDup chosen ->
  Forall (fun i => 0 <= i < n) chosen ->
  @SumLib.Sum.sum Z (fun i => 0 <= i < n) (SumLib.ZRange.finite_Z_range 0 n)
    (fun i => if existsb (Z.eqb i) chosen then 1 else 0) =
  Zlength chosen.
Proof.
  intros n chosen Hnd Hrange.
  induction Hnd as [|c cs Hnot Hnd IH].
  - simpl. rewrite sum_Z_range_zero. reflexivity.
  - inversion Hrange as [|? ? Hc Hcs]; subst.
    simpl existsb.
    transitivity
      (@SumLib.Sum.sum Z (fun i => 0 <= i < n) (SumLib.ZRange.finite_Z_range 0 n)
        (fun i => (if Z.eqb i c then 1 else 0) +
                  (if existsb (Z.eqb i) cs then 1 else 0))).
    + apply sum_Z_range_ext. intros i Hi.
      destruct (Z.eqb i c) eqn:Hic; simpl.
      * apply Z.eqb_eq in Hic. subst i.
        destruct (existsb (Z.eqb c) cs) eqn:Hmem; [|reflexivity].
        apply existsb_exists in Hmem.
        destruct Hmem as [x [Hxin Heq]].
        apply Z.eqb_eq in Heq. subst x. contradiction.
      * destruct (existsb (Z.eqb i) cs); reflexivity.
    + rewrite sum_Z_range_add.
      rewrite single_indicator_sum__query_semantic_core by exact Hc.
      rewrite IH by exact Hcs.
      rewrite Zlength_cons. lia.
Qed.
Lemma BiteStep_sum_bound__query_semantic_core : forall m a b,
  BiteStep m a b ->
  ListLib.sum a <= ListLib.sum b + m.
Proof.
  intros m a b Hstep.
  destruct Hstep as [chosen [Hnd [Hcap [Hrange [Hpos [Hlen Hpoint]]]]]].
  rewrite list_sum_as_Z_range_sum.
  eapply Z.le_trans with
    (m := @SumLib.Sum.sum Z (fun i => 0 <= i < Zlength a)
      (SumLib.ZRange.finite_Z_range 0 (Zlength a))
      (fun i => Znth i b 0 +
        (if existsb (Z.eqb i) chosen then 1 else 0))).
  - apply sum_Z_range_le. intros i Hi.
    rewrite Hpoint by exact Hi.
    destruct (existsb (Z.eqb i) chosen); lia.
  - rewrite sum_Z_range_add.
    replace (@SumLib.Sum.sum Z (fun i => 0 <= i < Zlength a)
      (SumLib.ZRange.finite_Z_range 0 (Zlength a))
      (fun i => Znth i b 0)) with (ListLib.sum b).
    2:{ rewrite list_sum_as_Z_range_sum, Hlen. reflexivity. }
    rewrite chosen_indicator_sum__query_semantic_core by assumption.
    lia.
Qed.
Lemma BiteStep_length__query_semantic_core : forall m a b,
  BiteStep m a b -> Zlength b = Zlength a.
Proof.
  intros m a b [chosen [_ [_ [_ [_ [Hlen _]]]]]]. exact Hlen.
Qed.
Lemma BiteStep_coord_bound__query_semantic_core : forall m a b i,
  BiteStep m a b ->
  0 <= i < Zlength a ->
  Znth i a 0 <= Znth i b 0 + 1.
Proof.
  intros m a b i [chosen [_ [_ [_ [_ [_ Hpoint]]]]]] Hi.
  rewrite Hpoint by exact Hi.
  destruct (existsb (Z.eqb i) chosen); lia.
Qed.
Lemma temporal_bounds_nat__query_semantic_core : forall n st m,
  (S n <= length st)%nat ->
  (forall q, 0 <= q < Zlength st - 1 ->
    BiteStep m (Znth q st []) (Znth (q + 1) st [])) ->
  Zlength (Znth (Z.of_nat n) st []) = Zlength (Znth 0 st []) /\
  (forall i, 0 <= i < Zlength (Znth 0 st []) ->
    Znth i (Znth 0 st []) 0 <=
    Znth i (Znth (Z.of_nat n) st []) 0 + Z.of_nat n) /\
  ListLib.sum (Znth 0 st []) <=
    ListLib.sum (Znth (Z.of_nat n) st []) + Z.of_nat n * m.
Proof.
  induction n as [|n IH]; intros st m Hlen Htrans.
  - rewrite Nat2Z.inj_0. repeat split; intros; lia.
  - assert (Hlen' : (S n <= length st)%nat) by lia.
    destruct (IH st m Hlen' Htrans) as [Hstate [Hcoord Hsum]].
    assert (Hq : 0 <= Z.of_nat n < Zlength st - 1).
    { rewrite Zlength_correct. lia. }
    specialize (Htrans (Z.of_nat n) Hq).
    assert (Hnextlen := BiteStep_length__query_semantic_core _ _ _ Htrans).
    rewrite Nat2Z.inj_succ.
    split.
    + etransitivity; [exact Hnextlen | exact Hstate].
    + split.
      * intros i Hi.
        specialize (Hcoord i Hi).
        pose proof (BiteStep_coord_bound__query_semantic_core _ _ _ i Htrans) as Hone.
        specialize (Hone ltac:(rewrite Hstate; exact Hi)).
        assert (Hone' :
          Znth i (Znth (Z.of_nat n) st []) 0 <=
          Znth i (Znth (Z.of_nat n + 1) st []) 0 + 1) by exact Hone.
        change (Znth i (Znth 0 st []) 0 <=
          Znth i (Znth (Z.of_nat n + 1) st []) 0 + (Z.of_nat n + 1)).
        nia.
      * pose proof (BiteStep_sum_bound__query_semantic_core _ _ _ Htrans) as Hone.
        change (ListLib.sum (Znth 0 st []) <=
          ListLib.sum (Znth (Z.of_nat n + 1) st []) +
          (Z.of_nat n + 1) * m).
        eapply Z.le_trans; [exact Hsum |]. nia.
Qed.
Lemma sum_Forall_zero__query_semantic_core : forall xs,
  Forall (fun x : Z => x = 0) xs -> ListLib.sum xs = 0.
Proof.
  intros xs H. induction H; simpl; lia.
Qed.
Lemma Eatable_resource_bounds__query_semantic_core : forall A B l t m r,
  0 <= m ->
  Eatable A B l t m r ->
  let init := map (fun i => A + (l + i - 1) * B)
    (Zrange 0 (r - l + 1)) in
  (forall i, 0 <= i < Zlength init -> Znth i init 0 <= t) /\
  ListLib.sum init <= t * m.
Proof.
  intros A B l t m r Hm [Hlr [st [Hstlen [Hinit [Htrans Hfinal]]]]].
  simpl.
  set (n := Z.to_nat (Zlength st - 1)).
  assert (HnZ : Z.of_nat n = Zlength st - 1).
  { unfold n. rewrite Z2Nat.id; lia. }
  assert (Hnlen : (S n <= length st)%nat).
  { apply Nat2Z.inj_le. rewrite Nat2Z.inj_succ, HnZ, <- Zlength_correct.
    lia. }
  destruct (temporal_bounds_nat__query_semantic_core n st m Hnlen Htrans)
    as [Hlastlen [Hcoord Hsum]].
  rewrite HnZ in Hlastlen, Hcoord, Hsum.
  rewrite Hinit in Hlastlen, Hcoord, Hsum.
  split.
  - intros i Hi. specialize (Hcoord i Hi).
    pose proof (Forall_Znth_Zlength (fun x : Z => x = 0)
      (Znth (Zlength st - 1) st []) 0 i Hfinal) as Hz.
    specialize (Hz ltac:(rewrite Hlastlen; exact Hi)).
    rewrite Hz in Hcoord.
    lia.
  - rewrite (sum_Forall_zero__query_semantic_core _ Hfinal) in Hsum.
    nia.
Qed.
Lemma true_indices_length__query_semantic_core : forall p bs,
  length (true_indices_from__query_semantic_core p bs) =
  count_true__query_semantic_core bs.
Proof.
  intros p bs. revert p.
  induction bs as [|b bs IH]; intros p; simpl; auto.
  destruct b; simpl; rewrite IH; auto.
Qed.
Lemma apply_mask_length__query_semantic_core : forall xs bs,
  length bs = length xs ->
  length (apply_mask__query_semantic_core xs bs) = length xs.
Proof.
  induction xs as [|x xs IH]; intros [|b bs] Hlen; simpl in *; try lia; auto.
Qed.
Lemma greedy_mask_count__query_semantic_core : forall v q xs,
  count_true__query_semantic_core (greedy_mask__query_semantic_core v q xs) =
  (count_eq__query_semantic_core v xs +
   Nat.min q (count_other_pos__query_semantic_core v xs))%nat.
Proof.
  intros v q xs. revert q.
  induction xs as [|x xs IH]; intros q; simpl.
  - rewrite Nat.min_0_r. reflexivity.
  - destruct (Z.eqb x v) eqn:Heq; simpl.
    + rewrite IH. lia.
    + destruct (Z.ltb 0 x) eqn:Hpos; simpl.
      * destruct q as [|q']; simpl.
        -- rewrite IH. reflexivity.
        -- rewrite IH.
           destruct (le_dec q' (count_other_pos__query_semantic_core v xs)).
           ++ rewrite Nat.min_l by lia. lia.
           ++ rewrite Nat.min_r by lia. lia.
      * rewrite IH. reflexivity.
Qed.
Lemma true_indices_range__query_semantic_core : forall p bs,
  Forall (fun i => p <= i < p + Z.of_nat (length bs))
    (true_indices_from__query_semantic_core p bs).
Proof.
  intros p bs. revert p.
  induction bs as [|b bs IH]; intros p; simpl.
  - constructor.
  - destruct b.
    + constructor.
      * lia.
      * rewrite Forall_forall. intros i Hin.
        pose proof (IH (p + 1)) as Hr.
        rewrite Forall_forall in Hr. specialize (Hr i Hin). lia.
    + rewrite Forall_forall. intros i Hin.
      pose proof (IH (p + 1)) as Hr.
      rewrite Forall_forall in Hr. specialize (Hr i Hin). lia.
Qed.
Lemma true_indices_nodup__query_semantic_core : forall p bs,
  NoDup (true_indices_from__query_semantic_core p bs).
Proof.
  intros p bs. revert p.
  induction bs as [|b bs IH]; intros p; simpl.
  - constructor.
  - destruct b.
    + constructor.
      * intro Hin.
        pose proof (true_indices_range__query_semantic_core (p + 1) bs) as Hr.
        rewrite Forall_forall in Hr.
        specialize (Hr p Hin). lia.
      * apply IH.
    + apply IH.
Qed.
Lemma true_indices_shift__query_semantic_core : forall p k bs,
  true_indices_from__query_semantic_core (p + k) bs =
  map (fun j => j + k) (true_indices_from__query_semantic_core p bs).
Proof.
  intros p k bs. revert p.
  induction bs as [|b bs IH]; intros p; simpl; auto.
  destruct b; simpl.
  - f_equal. replace (p + k + 1) with (p + 1 + k) by lia.
    apply IH.
  - replace (p + k + 1) with (p + 1 + k) by lia. apply IH.
Qed.
Lemma existsb_map__query_semantic_core : forall {A B} (f : B -> bool) (g : A -> B) xs,
  existsb f (map g xs) = existsb (fun x => f (g x)) xs.
Proof.
  intros A B f g xs. induction xs; simpl; auto. rewrite IHxs. reflexivity.
Qed.
Lemma existsb_ext__query_semantic_core : forall {A} (f g : A -> bool) xs,
  (forall x, f x = g x) -> existsb f xs = existsb g xs.
Proof.
  intros A f g xs Hfg. induction xs; simpl; auto.
  rewrite Hfg, IHxs. reflexivity.
Qed.
Lemma true_indices_existsb__query_semantic_core : forall bs i,
  0 <= i < Z.of_nat (length bs) ->
  existsb (Z.eqb i) (true_indices_from__query_semantic_core 0 bs) =
  Znth i bs false.
Proof.
  induction bs as [|b bs IH]; intros i Hi; simpl in Hi; try lia.
  destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. simpl. destruct b; [reflexivity |].
    destruct (existsb (Z.eqb 0)
      (true_indices_from__query_semantic_core 1 bs)) eqn:Hex; [|reflexivity].
    apply existsb_exists in Hex. destruct Hex as [j [Hin Heq]].
    apply Z.eqb_eq in Heq. subst j.
    pose proof (true_indices_range__query_semantic_core 1 bs) as Hr.
    rewrite Forall_forall in Hr. specialize (Hr 0 Hin). lia.
  - assert (1 <= i) by lia.
    rewrite Znth_cons by lia.
    replace (i - 1) with (i + -1) by lia.
    simpl true_indices_from__query_semantic_core.
    destruct b; simpl.
    + destruct (Z.eqb i 0) eqn:Hio.
      * apply Z.eqb_eq in Hio. contradiction.
      * simpl.
      replace (true_indices_from__query_semantic_core 1 bs)
        with (map (fun j => j + 1)
                  (true_indices_from__query_semantic_core 0 bs)).
      2: { symmetry. apply (true_indices_shift__query_semantic_core 0 1 bs). }
      rewrite existsb_map__query_semantic_core.
      rewrite <- IH by (simpl in Hi; lia).
      apply existsb_ext__query_semantic_core. intros j.
      destruct (Z.eqb i (j + 1)) eqn:Hlhs;
        destruct (Z.eqb (i - 1) j) eqn:Hrhs; auto.
      { apply Z.eqb_eq in Hlhs. apply Z.eqb_neq in Hrhs.
        assert (i - 1 = j) by lia. contradiction. }
      { apply Z.eqb_neq in Hlhs. apply Z.eqb_eq in Hrhs.
        assert (i = j + 1) by lia. contradiction. }
    + replace (true_indices_from__query_semantic_core 1 bs)
        with (map (fun j => j + 1)
                  (true_indices_from__query_semantic_core 0 bs)).
      2: { symmetry. apply (true_indices_shift__query_semantic_core 0 1 bs). }
      rewrite existsb_map__query_semantic_core.
      rewrite <- IH by (simpl in Hi; lia).
      apply existsb_ext__query_semantic_core. intros j.
      destruct (Z.eqb i (j + 1)) eqn:Hlhs;
        destruct (Z.eqb (i - 1) j) eqn:Hrhs; auto.
      { apply Z.eqb_eq in Hlhs. apply Z.eqb_neq in Hrhs.
        assert (i - 1 = j) by lia. contradiction. }
      { apply Z.eqb_neq in Hlhs. apply Z.eqb_eq in Hrhs.
        assert (i = j + 1) by lia. contradiction. }
Qed.
Lemma apply_mask_Znth__query_semantic_core : forall xs bs i,
  length bs = length xs ->
  0 <= i < Zlength xs ->
  Znth i (apply_mask__query_semantic_core xs bs) 0 =
  if Znth i bs false then Znth i xs 0 - 1 else Znth i xs 0.
Proof.
  induction xs as [|x xs IH]; intros bs i Hlen Hi; destruct bs as [|b bs].
  - rewrite Zlength_nil in Hi. lia.
  - simpl in Hlen. discriminate.
  - simpl in Hlen. discriminate.
  - simpl in Hlen, Hi |- *.
    rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + repeat rewrite Znth0_cons. destruct b; reflexivity.
    + assert (1 <= i) by lia.
      repeat rewrite Znth_cons by lia.
      apply IH; simpl in *; lia.
Qed.
Lemma greedy_mask_positive__query_semantic_core : forall v q xs i,
  0 < v ->
  0 <= i < Zlength xs ->
  Znth i (greedy_mask__query_semantic_core v q xs) false = true ->
  0 < Znth i xs 0.
Proof.
  intros v q xs. revert q.
  induction xs as [|x xs IH]; intros q i Hv Hi Hsel.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite Znth0_cons.
      cbn [greedy_mask__query_semantic_core] in Hsel.
      destruct (Z.eqb x v) eqn:Heq.
      * apply Z.eqb_eq in Heq. lia.
      * destruct (Z.ltb 0 x) eqn:Hpos.
        -- apply Z.ltb_lt in Hpos. exact Hpos.
        -- destruct q; discriminate.
    + assert (1 <= i) by lia.
      rewrite Znth_cons by lia.
      cbn [greedy_mask__query_semantic_core] in Hsel.
      destruct (Z.eqb x v) eqn:Heq.
      * rewrite Znth_cons in Hsel by lia. eapply IH; eauto; lia.
      * destruct (Z.ltb 0 x) eqn:Hpos.
        -- destruct q.
           ++ rewrite Znth_cons in Hsel by lia. eapply IH; eauto; lia.
           ++ rewrite Znth_cons in Hsel by lia. eapply IH; eauto; lia.
        -- rewrite Znth_cons in Hsel by lia. eapply IH; eauto; lia.
Qed.
Lemma bite_step_from_mask__query_semantic_core : forall m xs bs,
  length bs = length xs ->
  Z.of_nat (count_true__query_semantic_core bs) <= m ->
  (forall i, 0 <= i < Zlength xs ->
     Znth i bs false = true -> 0 < Znth i xs 0) ->
  BiteStep m xs (apply_mask__query_semantic_core xs bs).
Proof.
  intros m xs bs Hlen Hcap Hpos.
  exists (true_indices_from__query_semantic_core 0 bs).
  repeat split.
  - apply true_indices_nodup__query_semantic_core.
  - rewrite Zlength_correct, true_indices_length__query_semantic_core. exact Hcap.
  - rewrite Forall_forall. intros i Hin.
    pose proof (true_indices_range__query_semantic_core 0 bs) as Hr.
    rewrite Forall_forall in Hr.
    specialize (Hr i Hin). rewrite Hlen in Hr. rewrite Zlength_correct. lia.
  - rewrite Forall_forall. intros i Hin.
    assert (Hi : 0 <= i < Zlength xs).
    { pose proof (true_indices_range__query_semantic_core 0 bs) as Hr.
      rewrite Forall_forall in Hr. specialize (Hr i Hin).
      rewrite Hlen in Hr. rewrite Zlength_correct. lia. }
    assert (Hsel : Znth i bs false = true).
    { assert (Hir : 0 <= i < Z.of_nat (length bs)).
      { pose proof (true_indices_range__query_semantic_core 0 bs) as Hr.
        rewrite Forall_forall in Hr. specialize (Hr i Hin). lia. }
      pose proof (true_indices_existsb__query_semantic_core bs i Hir) as Heq.
      assert (Hex : existsb (Z.eqb i)
        (true_indices_from__query_semantic_core 0 bs) = true).
      { apply existsb_exists. exists i. split; [exact Hin | apply Z.eqb_refl]. }
      congruence. }
    pose proof (Hpos i Hi Hsel). lia.
  - rewrite !Zlength_correct. f_equal.
    apply apply_mask_length__query_semantic_core. exact Hlen.
  - intros i Hi. rewrite apply_mask_Znth__query_semantic_core by auto.
    rewrite <- true_indices_existsb__query_semantic_core.
    + reflexivity.
    + rewrite Hlen. rewrite <- Zlength_correct. exact Hi.
Qed.
Lemma sum_apply_mask__query_semantic_core : forall xs bs,
  length bs = length xs ->
  ListLib.sum (apply_mask__query_semantic_core xs bs) =
  ListLib.sum xs - Z.of_nat (count_true__query_semantic_core bs).
Proof.
  induction xs as [|x xs IH]; intros bs Hlen; destruct bs as [|b bs].
  - reflexivity.
  - simpl in Hlen. discriminate.
  - simpl in Hlen. discriminate.
  - simpl in Hlen |- *. destruct b; simpl.
    + rewrite IH by lia. lia.
    + rewrite IH by lia. lia.
Qed.
Lemma count_eq_weight_le_sum__query_semantic_core : forall v xs,
  0 < v ->
  Forall (fun x => 0 <= x) xs ->
  Z.of_nat (count_eq__query_semantic_core v xs) * v <= ListLib.sum xs.
Proof.
  intros v xs Hv Hnonneg.
  induction xs as [|x xs IH]; simpl; [lia |].
  inversion Hnonneg as [|? ? Hx Hxs]; subst.
  specialize (IH Hxs).
  destruct (Z.eqb x v) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst x. rewrite Nat2Z.inj_succ. lia.
  - lia.
Qed.
Lemma positive_count_sum_bound__query_semantic_core : forall v xs,
  0 < v ->
  Forall (fun x => 0 <= x <= v) xs ->
  ListLib.sum xs <=
  v * Z.of_nat
    ((count_eq__query_semantic_core v xs +
      count_other_pos__query_semantic_core v xs)%nat).
Proof.
  intros v xs Hv Hbounds.
  induction xs as [|x xs IH]; simpl; [lia |].
  inversion Hbounds as [|? ? Hx Hxs]; subst.
  specialize (IH Hxs).
  destruct (Z.eqb x v) eqn:Heq.
  - apply Z.eqb_eq in Heq. subst x. rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
    lia.
  - destruct (Z.ltb 0 x) eqn:Hpos.
    + apply Z.ltb_lt in Hpos. rewrite Nat2Z.inj_add, Nat2Z.inj_succ. lia.
    + apply Z.ltb_ge in Hpos. assert (x = 0) by lia. subst x.
      rewrite Nat2Z.inj_add. lia.
Qed.
Lemma greedy_mask_selected_count__query_semantic_core : forall v (m : nat) xs,
  (count_eq__query_semantic_core v xs <= m)%nat ->
  count_true__query_semantic_core
    (greedy_mask__query_semantic_core v
      (m - count_eq__query_semantic_core v xs) xs) =
  Nat.min m
    (count_eq__query_semantic_core v xs +
     count_other_pos__query_semantic_core v xs).
Proof.
  intros v m xs Hle.
  rewrite greedy_mask_count__query_semantic_core.
  set (a := count_eq__query_semantic_core v xs).
  set (b := count_other_pos__query_semantic_core v xs).
  destruct (le_dec (m - a) b).
  - rewrite Nat.min_l by lia.
    rewrite Nat.min_l by lia. lia.
  - rewrite Nat.min_r by lia.
    rewrite Nat.min_r by lia. lia.
Qed.
Lemma count_eq_le_capacity__query_semantic_core : forall v (m : nat) xs,
  0 < v ->
  Forall (fun x => 0 <= x) xs ->
  ListLib.sum xs <= v * Z.of_nat m ->
  (count_eq__query_semantic_core v xs <= m)%nat.
Proof.
  intros v m xs Hv Hnonneg Hsum.
  pose proof (count_eq_weight_le_sum__query_semantic_core v xs Hv Hnonneg).
  apply Nat2Z.inj_le. nia.
Qed.
Lemma greedy_mask_capacity__query_semantic_core : forall v (m : nat) xs,
  0 < v ->
  Forall (fun x => 0 <= x) xs ->
  ListLib.sum xs <= v * Z.of_nat m ->
  Z.of_nat (count_true__query_semantic_core
    (greedy_mask__query_semantic_core v
      (m - count_eq__query_semantic_core v xs) xs)) <= Z.of_nat m.
Proof.
  intros v m xs Hv Hnonneg Hsum.
  pose proof (count_eq_le_capacity__query_semantic_core v m xs Hv Hnonneg Hsum) as Hce.
  rewrite greedy_mask_selected_count__query_semantic_core by exact Hce.
  apply Nat2Z.inj_le.
  destruct (le_dec m
    (count_eq__query_semantic_core v xs +
     count_other_pos__query_semantic_core v xs)).
  - rewrite Nat.min_l by lia. lia.
  - rewrite Nat.min_r by lia. lia.
Qed.
Lemma greedy_apply_bounds__query_semantic_core : forall v q xs,
  0 < v ->
  Forall (fun x => 0 <= x <= v) xs ->
  Forall (fun x => 0 <= x <= v - 1)
    (apply_mask__query_semantic_core xs
      (greedy_mask__query_semantic_core v q xs)).
Proof.
  intros v q xs. revert q.
  induction xs as [|x xs IH]; intros q Hv Hbounds.
  - simpl. constructor.
  - inversion Hbounds as [|? ? Hx Hxs]; subst.
    cbn [greedy_mask__query_semantic_core].
    destruct (Z.eqb x v) eqn:Heq.
    + simpl. constructor.
      * apply Z.eqb_eq in Heq. lia.
      * apply IH; assumption.
    + destruct (Z.ltb 0 x) eqn:Hpos.
      * apply Z.ltb_lt in Hpos. destruct q as [|q']; simpl; constructor.
        -- lia.
        -- apply IH; assumption.
        -- lia.
        -- apply IH; assumption.
      * apply Z.ltb_ge in Hpos. simpl. constructor.
        -- lia.
        -- apply IH; assumption.
Qed.
Lemma greedy_next_sum_bound__query_semantic_core : forall v (m : nat) xs,
  0 < v ->
  Forall (fun x => 0 <= x <= v) xs ->
  ListLib.sum xs <= v * Z.of_nat m ->
  ListLib.sum
    (apply_mask__query_semantic_core xs
      (greedy_mask__query_semantic_core v
        (m - count_eq__query_semantic_core v xs) xs)) <=
  (v - 1) * Z.of_nat m.
Proof.
  intros v m xs Hv Hbounds Hsum.
  assert (Hnonneg : Forall (fun x => 0 <= x) xs).
  { rewrite Forall_forall in Hbounds |- *. intros x Hin.
    specialize (Hbounds x Hin). lia. }
  pose proof (count_eq_le_capacity__query_semantic_core v m xs Hv Hnonneg Hsum) as Hce.
  rewrite sum_apply_mask__query_semantic_core by apply greedy_mask_length__query_semantic_core.
  rewrite greedy_mask_selected_count__query_semantic_core by exact Hce.
  pose proof (positive_count_sum_bound__query_semantic_core v xs Hv Hbounds) as Hpossum.
  set (p := (count_eq__query_semantic_core v xs +
    count_other_pos__query_semantic_core v xs)%nat) in *.
  destruct (le_dec m p).
  - rewrite Nat.min_l by lia. nia.
  - rewrite Nat.min_r by lia. nia.
Qed.
Lemma greedy_one_step__query_semantic_core : forall v (m : nat) xs,
  0 < v ->
  Forall (fun x => 0 <= x <= v) xs ->
  ListLib.sum xs <= v * Z.of_nat m ->
  BiteStep (Z.of_nat m) xs
    (apply_mask__query_semantic_core xs
      (greedy_mask__query_semantic_core v
        (m - count_eq__query_semantic_core v xs) xs)) /\
  Forall (fun x => 0 <= x <= v - 1)
    (apply_mask__query_semantic_core xs
      (greedy_mask__query_semantic_core v
        (m - count_eq__query_semantic_core v xs) xs)) /\
  ListLib.sum
    (apply_mask__query_semantic_core xs
      (greedy_mask__query_semantic_core v
        (m - count_eq__query_semantic_core v xs) xs)) <=
  (v - 1) * Z.of_nat m.
Proof.
  intros v m xs Hv Hbounds Hsum.
  assert (Hnonneg : Forall (fun x => 0 <= x) xs).
  { rewrite Forall_forall in Hbounds |- *. intros x Hin.
    specialize (Hbounds x Hin). lia. }
  repeat split.
  - apply bite_step_from_mask__query_semantic_core.
    + apply greedy_mask_length__query_semantic_core.
    + apply greedy_mask_capacity__query_semantic_core; assumption.
    + intros i Hi Hsel.
      eapply greedy_mask_positive__query_semantic_core; eauto.
  - apply greedy_apply_bounds__query_semantic_core; assumption.
  - apply greedy_next_sum_bound__query_semantic_core; assumption.
Qed.
Lemma Forall_zero__query_semantic_core : forall xs,
  Forall (fun x => 0 <= x <= 0) xs ->
  Forall (fun x => x = 0) xs.
Proof.
  intros xs H. rewrite Forall_forall in H |- *.
  intros x Hin. specialize (H x Hin). lia.
Qed.
Lemma BiteSteps_prepend__query_semantic_core : forall m x y xs,
  BiteStep m x y ->
  BiteSteps__query_semantic_core m (y :: xs) ->
  BiteSteps__query_semantic_core m (x :: y :: xs).
Proof.
  intros m x y xs Hxy Hsteps.
  destruct xs; simpl in *; tauto.
Qed.
Lemma schedule_exists__query_semantic_core : forall (n m : nat) xs,
  Forall (fun x => 0 <= x <= Z.of_nat n) xs ->
  ListLib.sum xs <= Z.of_nat n * Z.of_nat m ->
  exists st : list (list Z),
    length st = S n /\
    hd [] st = xs /\
    BiteSteps__query_semantic_core (Z.of_nat m) st /\
    Forall (fun x => x = 0) (last st []).
Proof.
  induction n as [|n IH]; intros m xs Hbounds Hsum.
  - exists [xs]. simpl. repeat split; auto.
    apply Forall_zero__query_semantic_core. exact Hbounds.
  - set (v := Z.of_nat (S n)).
    pose proof (greedy_one_step__query_semantic_core v m xs ltac:(unfold v; lia)
      Hbounds Hsum) as [Hstep [Hnext_bounds Hnext_sum]].
    set (ys := apply_mask__query_semantic_core xs
      (greedy_mask__query_semantic_core v
        (m - count_eq__query_semantic_core v xs) xs)) in *.
    assert (Hv : v - 1 = Z.of_nat n) by (unfold v; lia).
    rewrite Hv in Hnext_bounds, Hnext_sum.
    destruct (IH m ys Hnext_bounds Hnext_sum)
      as [st [Hlen [Hhd [Hsteps Hlast]]]].
    exists (xs :: st). split.
    + simpl. lia.
    + split.
      * reflexivity.
      * split.
        -- destruct st as [|z st']; simpl in Hlen; [lia |].
           simpl in Hhd. subst z.
           apply BiteSteps_prepend__query_semantic_core; assumption.
        -- destruct st; simpl in Hlen; [lia |]. simpl. exact Hlast.
Qed.
Lemma Znth_last__query_semantic_core : forall {A : Type} (xs : list A) d,
  xs <> [] -> Znth (Zlength xs - 1) xs d = last xs d.
Proof.
  intros A xs. induction xs as [|x xs IH]; intros d Hne; [contradiction |].
  destruct xs as [|y ys].
  - simpl. rewrite Znth0_cons. reflexivity.
  - rewrite Zlength_cons.
    rewrite Znth_cons by (rewrite Zlength_cons; pose proof (Zlength_nonneg ys); lia).
    replace (Z.succ (Zlength (y :: ys)) - 1 - 1)
      with (Zlength (y :: ys) - 1) by lia.
    change (Znth (Zlength (y :: ys) - 1) (y :: ys) d = last (y :: ys) d).
    apply IH. discriminate.
Qed.
Lemma BiteSteps_Znth__query_semantic_core : forall m st q,
  BiteSteps__query_semantic_core m st ->
  0 <= q < Zlength st - 1 ->
  BiteStep m (Znth q st []) (Znth (q + 1) st []).
Proof.
  intros m st. induction st as [|a tail IH]; intros q Hsteps Hq.
  - rewrite Zlength_nil in Hq. lia.
  - destruct tail as [|b rest].
    + rewrite Zlength_cons, Zlength_nil in Hq. lia.
    + simpl in Hsteps. destruct Hsteps as [Hab Htail].
      destruct (Z.eq_dec q 0) as [-> | Hq0].
      * rewrite !Znth0_cons. rewrite Znth_cons by lia.
        replace (0 + 1 - 1) with 0 by lia. rewrite Znth0_cons. exact Hab.
      * assert (Hfirst : Znth q (a :: b :: rest) [] =
          Znth (q - 1) (b :: rest) []).
        { rewrite Znth_cons by lia. reflexivity. }
        assert (Hsecond : Znth (q + 1) (a :: b :: rest) [] =
          Znth q (b :: rest) []).
        { rewrite Znth_cons by lia. f_equal. lia. }
        rewrite Hfirst, Hsecond.
        assert (Hqtail : 0 <= q - 1 < Zlength (b :: rest) - 1).
        { rewrite Zlength_cons in Hq. lia. }
        pose proof (IH (q - 1) Htail Hqtail) as HH.
        replace (q - 1 + 1) with q in HH by lia. exact HH.
Qed.
Lemma sum_map_affine_aux__query_semantic_core : forall low n C B,
  ListLib.sum (map (fun i => C + i * B) (Zrange_aux low n)) =
  Z.of_nat n * C + B * ListLib.sum (Zrange_aux low n).
Proof.
  intros low n. revert low. induction n as [|n IH]; intros low C B.
  - simpl. ring.
  - rewrite Nat2Z.inj_succ. simpl. rewrite IH. ring.
Qed.
Lemma twice_sum_Zrange_aux__query_semantic_core : forall low n,
  ListLib.sum (Zrange_aux low n) + ListLib.sum (Zrange_aux low n) =
  Z.of_nat n * (2 * low + Z.of_nat n - 1).
Proof.
  intros low n. revert low. induction n as [|n IH]; intros low.
  - simpl. ring.
  - rewrite Nat2Z.inj_succ.
    simpl Zrange_aux. simpl ListLib.sum.
    replace (low + ListLib.sum (Zrange_aux (low + 1) n) +
             (low + ListLib.sum (Zrange_aux (low + 1) n)))
      with (2 * low +
            (ListLib.sum (Zrange_aux (low + 1) n) +
             ListLib.sum (Zrange_aux (low + 1) n))) by ring.
    rewrite IH. ring.
Qed.
Lemma twice_sum_Zrange_zero__query_semantic_core : forall n,
  0 <= n -> 2 * ListLib.sum (Zrange 0 n) = n * (n - 1).
Proof.
  intros n Hn. unfold Zrange.
  replace (2 * ListLib.sum (Zrange_aux 0 (Z.to_nat (n - 0))))
    with (ListLib.sum (Zrange_aux 0 (Z.to_nat (n - 0))) +
          ListLib.sum (Zrange_aux 0 (Z.to_nat (n - 0)))) by ring.
  rewrite twice_sum_Zrange_aux__query_semantic_core, Z2Nat.id by lia. ring.
Qed.
Lemma arithmetic_list_sum__query_semantic_core : forall A B l r,
  l <= r ->
  ListLib.sum
    (map (fun i => A + (l + i - 1) * B) (Zrange 0 (r - l + 1))) =
  ((A + (l - 1) * B + A + (r - 1) * B) * (r - l + 1)) / 2.
Proof.
  intros A B l r Hlr.
  set (n := r - l + 1).
  set (C := A + (l - 1) * B).
  assert (Hfun : forall i, A + (l + i - 1) * B = C + i * B).
  { intros i. unfold C. ring. }
  assert (Hsum :
    ListLib.sum (map (fun i => A + (l + i - 1) * B) (Zrange 0 n)) =
    n * C + B * ListLib.sum (Zrange 0 n)).
  { erewrite map_ext; [|intros; apply Hfun].
    unfold Zrange. rewrite sum_map_affine_aux__query_semantic_core, Z2Nat.id by lia.
    ring. }
  assert (Htwice := twice_sum_Zrange_zero__query_semantic_core n ltac:(unfold n; lia)).
  rewrite Hsum.
  assert (Hprod :
    (A + (l - 1) * B + A + (r - 1) * B) * (r - l + 1) =
    2 * (n * C + B * ListLib.sum (Zrange 0 n))).
  { unfold n, C in Htwice |- *. nia. }
  assert (Hdiv :
    (2 * (n * C + B * ListLib.sum (Zrange 0 n))) / 2 =
    n * C + B * ListLib.sum (Zrange 0 n)).
  { rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
  transitivity ((2 * (n * C + B * ListLib.sum (Zrange 0 n))) / 2).
  - symmetry. exact Hdiv.
  - f_equal. symmetry. exact Hprod.
Qed.
Lemma arithmetic_list_bounds__query_semantic_core : forall A B l r t,
  1 <= A -> 1 <= B -> 1 <= l -> l <= r ->
  A + (r - 1) * B <= t ->
  Forall (fun x => 0 <= x <= t)
    (map (fun i => A + (l + i - 1) * B) (Zrange 0 (r - l + 1))).
Proof.
  intros A B l r t HA HB Hl Hlr Hend.
  rewrite Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [i [Heq Hi]]. subst x.
  apply <- In_Zrange in Hi. nia.
Qed.
Lemma Eatable_from_resources__query_semantic_core : forall A B l t m r,
  1 <= t -> 1 <= m -> l <= r ->
  Forall (fun x => 0 <= x <= t)
    (map (fun i => A + (l + i - 1) * B) (Zrange 0 (r - l + 1))) ->
  ListLib.sum
    (map (fun i => A + (l + i - 1) * B) (Zrange 0 (r - l + 1))) <= t * m ->
  Eatable A B l t m r.
Proof.
  intros A B l t m r Ht Hm Hlr Hbounds Hsum.
  set (init := map (fun i => A + (l + i - 1) * B)
    (Zrange 0 (r - l + 1))) in *.
  assert (HtZ : Z.of_nat (Z.to_nat t) = t) by (rewrite Z2Nat.id; lia).
  assert (HmZ : Z.of_nat (Z.to_nat m) = m) by (rewrite Z2Nat.id; lia).
  destruct (schedule_exists__query_semantic_core (Z.to_nat t) (Z.to_nat m) init)
    as [st [Hlen [Hhd [Hsteps Hlast]]]].
  - rewrite HtZ. exact Hbounds.
  - rewrite HtZ, HmZ. exact Hsum.
  - rewrite HmZ in Hsteps.
    split; [exact Hlr |]. exists st.
    assert (Hstne : st <> []).
    { intro He. subst st. simpl in Hlen. lia. }
    split.
    + rewrite Zlength_correct, Hlen, Nat2Z.inj_succ, HtZ. lia.
    + split.
      * destruct st as [|s st']; [contradiction |].
        simpl in Hhd. rewrite Znth0_cons. exact Hhd.
      * split.
        -- intros q Hq. apply BiteSteps_Znth__query_semantic_core; assumption.
        -- rewrite Znth_last__query_semantic_core by exact Hstne. exact Hlast.
Qed.
Lemma Zlength_map__query_semantic_core : forall {A B : Type} (f : A -> B) xs,
  Zlength (map f xs) = Zlength xs.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Zlength_Zrange_aux__query_semantic_core : forall low n,
  Zlength (Zrange_aux low n) = Z.of_nat n.
Proof.
  intros low n. revert low. induction n as [|n IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__query_semantic_core : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high H. unfold Zrange.
  rewrite Zlength_Zrange_aux__query_semantic_core, Z2Nat.id by lia. lia.
Qed.
Lemma Znth_Zrange_aux__query_semantic_core : forall n low i,
  0 <= i < Z.of_nat n -> Znth i (Zrange_aux low n) 0 = low + i.
Proof.
  induction n as [|n IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia. rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia).
    lia.
Qed.
Lemma Znth_Zrange__query_semantic_core : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__query_semantic_core by (rewrite Z2Nat.id by lia; lia). lia.
Qed.
Lemma Znth_map__query_semantic_core : forall {A B : Type} (f : A -> B) xs
    (da : A) (db : B) i,
  0 <= i < Zlength xs -> Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A0 B0 f xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia. apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.
Lemma arithmetic_segment_eatable_iff__query_semantic_core : forall A B l t m r,
  1 <= A -> 1 <= B -> 1 <= l -> 1 <= t -> 1 <= m -> l <= r ->
  (Eatable A B l t m r <->
   A + (r - 1) * B <= t /\
   ((A + (l - 1) * B + A + (r - 1) * B) * (r - l + 1)) / 2 <= t * m).
Proof.
  intros A B l t m r HA HB Hl Ht Hm Hlr. split.
  - intros He.
    destruct (Eatable_resource_bounds__query_semantic_core A B l t m r ltac:(lia) He)
      as [Hpoint Hsum].
    set (init := map (fun i => A + (l + i - 1) * B)
      (Zrange 0 (r - l + 1))) in *.
    assert (Hlen : Zlength init = r - l + 1).
    { unfold init. rewrite Zlength_map__query_semantic_core, Zlength_Zrange__query_semantic_core by lia. lia. }
    assert (Hi : 0 <= r - l < Zlength init) by lia.
    specialize (Hpoint (r - l) Hi).
    unfold init in Hpoint.
    rewrite (@Znth_map__query_semantic_core Z Z
      (fun i => A + (l + i - 1) * B) (Zrange 0 (r - l + 1))
      0 0 (r - l)) in Hpoint by
      (rewrite Zlength_Zrange__query_semantic_core by lia; lia).
    rewrite Znth_Zrange__query_semantic_core in Hpoint by lia.
    split.
    + replace (A + (l + (0 + (r - l)) - 1) * B)
        with (A + (r - 1) * B) in Hpoint by ring. exact Hpoint.
    + rewrite <- arithmetic_list_sum__query_semantic_core by exact Hlr. exact Hsum.
  - intros [Hheight Hbudget].
    apply Eatable_from_resources__query_semantic_core; try assumption.
    + apply arithmetic_list_bounds__query_semantic_core; assumption.
    + rewrite arithmetic_list_sum__query_semantic_core by exact Hlr. exact Hbudget.
Qed.
Lemma sum_map_Zrange__query_semantic_core : forall f low high,
  ListLib.sum (map f (Zrange low high)) =
  @SumLib.Sum.sum Z (fun i => low <= i < high)
    (SumLib.ZRange.finite_Z_range low high) f.
Proof.
  intros f low high. rewrite sum_range_unfold.
  unfold ListLib.sum.
  generalize (Zrange low high) as xs. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma arithmetic_list_sum_monotone__query_semantic_core : forall A B l r1 r2,
  1 <= A -> 1 <= B -> 1 <= l -> l <= r1 -> r1 <= r2 ->
  ListLib.sum
    (map (fun i => A + (l + i - 1) * B) (Zrange 0 (r1 - l + 1))) <=
  ListLib.sum
    (map (fun i => A + (l + i - 1) * B) (Zrange 0 (r2 - l + 1))).
Proof.
  intros A B l r1 r2 HA HB Hl Hlr1 Hr.
  rewrite !sum_map_Zrange__query_semantic_core.
  rewrite (sum_Z_range_split 0 (r1 - l + 1) (r2 - l + 1)) by lia.
  assert (Hnonneg :
    0 <= @SumLib.Sum.sum Z
      (fun i => r1 - l + 1 <= i < r2 - l + 1)
      (SumLib.ZRange.finite_Z_range (r1 - l + 1) (r2 - l + 1))
      (fun i => A + (l + i - 1) * B)).
  { apply SumLib.Sum.sum_nonneg. intros i Hi. nia. }
  lia.
Qed.
Lemma Eatable_downward__query_semantic_core : forall A B l t m r1 r2,
  1 <= A -> 1 <= B -> 1 <= l -> 1 <= t -> 1 <= m ->
  l <= r1 -> r1 <= r2 ->
  Eatable A B l t m r2 -> Eatable A B l t m r1.
Proof.
  intros A B l t m r1 r2 HA HB Hl Ht Hm Hlr1 Hr He2.
  pose proof (proj1 (arithmetic_segment_eatable_iff__query_semantic_core
    A B l t m r2 HA HB Hl Ht Hm ltac:(lia)) He2) as [Hheight2 Hbudget2].
  apply Eatable_from_resources__query_semantic_core; try assumption.
  - apply arithmetic_list_bounds__query_semantic_core; try assumption. nia.
  - eapply Z.le_trans.
    + apply arithmetic_list_sum_monotone__query_semantic_core; eauto.
    + rewrite arithmetic_list_sum__query_semantic_core by lia. exact Hbudget2.
Qed.
Lemma query_answer_feasible_lower__query_semantic_core : forall A B l t m r ans,
  1 <= A -> 1 <= B -> 1 <= l -> 1 <= t -> 1 <= m -> l <= r ->
  Eatable A B l t m r ->
  QueryAnswer A B (l, t, m) ans -> r <= ans.
Proof.
  intros A B l t m r ans HA HB Hl Ht Hm Hlr He HQ.
  unfold QueryAnswer in HQ. destruct HQ as [[Hans Hnotl] | [Hans [Heans Hnotnext]]].
  - subst ans. exfalso. apply Hnotl.
    eapply Eatable_downward__query_semantic_core with (r2 := r); eauto; lia.
  - destruct (Z_le_gt_dec r ans); [assumption |].
    exfalso. apply Hnotnext.
    eapply Eatable_downward__query_semantic_core with (r2 := r); eauto; lia.
Qed.
Lemma query_answer_infeasible_upper__query_semantic_core : forall A B l t m r ans,
  1 <= A -> 1 <= B -> 1 <= l -> 1 <= t -> 1 <= m -> l <= r ->
  ~ Eatable A B l t m r ->
  QueryAnswer A B (l, t, m) ans -> ans < r.
Proof.
  intros A B l t m r ans HA HB Hl Ht Hm Hlr Hnot HQ.
  unfold QueryAnswer in HQ. destruct HQ as [[Hans _] | [Hans [Heans _]]].
  - subst ans. lia.
  - destruct (Z_lt_ge_dec ans r); [assumption |].
    exfalso. apply Hnot.
    eapply Eatable_downward__query_semantic_core with (r2 := ans); eauto; lia.
Qed.
Lemma query_answer_height_infeasible_upper__query_semantic_core : forall A B l t m r ans,
  1 <= A -> 1 <= B -> 1 <= l -> 1 <= t -> 1 <= m -> l <= r ->
  A + (r - 1) * B > t ->
  QueryAnswer A B (l, t, m) ans -> ans < r.
Proof.
  intros A B l t m r ans HA HB Hl Ht Hm Hlr Hheight HQ.
  apply query_answer_infeasible_upper__query_semantic_core with (A := A) (B := B)
    (l := l) (t := t) (m := m); try assumption.
  intro He. apply (proj1 (arithmetic_segment_eatable_iff__query_semantic_core
    A B l t m r HA HB Hl Ht Hm Hlr)) in He. lia.
Qed.
Lemma query_answer_budget_infeasible_upper__query_semantic_core : forall A B l t m r ans,
  1 <= A -> 1 <= B -> 1 <= l -> 1 <= t -> 1 <= m -> l <= r ->
  ((A + (l - 1) * B + A + (r - 1) * B) * (r - l + 1)) / 2 > t * m ->
  QueryAnswer A B (l, t, m) ans -> ans < r.
Proof.
  intros A B l t m r ans HA HB Hl Ht Hm Hlr Hbudget HQ.
  apply query_answer_infeasible_upper__query_semantic_core with (A := A) (B := B)
    (l := l) (t := t) (m := m); try assumption.
  intro He. apply (proj1 (arithmetic_segment_eatable_iff__query_semantic_core
    A B l t m r HA HB Hl Ht Hm Hlr)) in He. lia.
Qed.
Lemma predicate_max_nat__query_semantic_core : forall (P : Z -> Prop) l n,
  P l -> ~ P (l + Z.of_nat n + 1) ->
  exists ans, l <= ans <= l + Z.of_nat n /\ P ans /\ ~ P (ans + 1).
Proof.
  intros P l n. induction n as [|n IH]; intros Hl Hupper.
  - exists l. split; [rewrite Nat2Z.inj_0; lia |]. split; [exact Hl |].
    replace (l + 1) with (l + Z.of_nat 0 + 1) by lia. exact Hupper.
  - assert (Hsucc : Z.of_nat (S n) = Z.of_nat n + 1) by
      apply Nat2Z.inj_succ.
    destruct (classic (P (l + Z.of_nat n + 1))) as [HP | Hnot].
    + exists (l + Z.of_nat n + 1). split.
      * rewrite Hsucc. lia.
      * split; [exact HP |].
        replace (l + Z.of_nat n + 1 + 1)
          with (l + Z.of_nat (S n) + 1) by (rewrite Hsucc; lia).
        exact Hupper.
    + destruct (IH Hl Hnot) as [ans [Hbounds [HPans Hnext]]].
      exists ans. split; [rewrite Hsucc; lia |]. split; assumption.
Qed.
Lemma query_answer_exists_bounded__query_semantic_core : forall A B l t m U,
  1 <= l -> l <= U ->
  Eatable A B l t m l ->
  ~ Eatable A B l t m (U + 1) ->
  exists ans, l <= ans <= U /\ QueryAnswer A B (l, t, m) ans.
Proof.
  intros A B l t m U Hl Hlu Hel Hupper.
  assert (HU : Z.of_nat (Z.to_nat (U - l)) = U - l).
  { rewrite Z2Nat.id; lia. }
  destruct (predicate_max_nat__query_semantic_core (fun r => Eatable A B l t m r)
    l (Z.to_nat (U - l)) Hel) as [ans [Hbounds [He Hnext]]].
  - rewrite HU. replace (l + (U - l) + 1) with (U + 1) by lia.
    exact Hupper.
  - exists ans. split.
    + rewrite HU in Hbounds. lia.
    + destruct Hbounds as [Hlo Hhi].
      unfold QueryAnswer. right. split; [lia |].
      split; [exact He | exact Hnext].
Qed.
Lemma midpoint_bounds__query_semantic_core : forall lo hi,
  lo < hi ->
  lo + 1 <= lo + (hi - lo + 1) / 2 <= hi.
Proof.
  intros lo hi Hlt. split.
  - assert (1 <= (hi - lo + 1) / 2).
    { apply Z.div_le_lower_bound; lia. }
    lia.
  - assert ((hi - lo + 1) / 2 <= hi - lo).
    { apply Z.div_le_upper_bound; lia. }
    lia.
Qed.
Lemma query_answer_exists_standard__query_semantic_core : forall A B l t m,
  1 <= A -> 1 <= B -> 1 <= l <= 1000000 ->
  1 <= t <= 1000000 -> 1 <= m ->
  A + (l - 1) * B <= t ->
  exists ans, l <= ans <= 2000000 /\ QueryAnswer A B (l, t, m) ans.
Proof.
  intros A B l t m HA HB Hl Ht Hm Hheight.
  assert (Hel : Eatable A B l t m l).
  { apply (proj2 (arithmetic_segment_eatable_iff__query_semantic_core
      A B l t m l HA HB (proj1 Hl) (proj1 Ht) Hm ltac:(lia))).
    split; [exact Hheight |].
    replace (l - l + 1) with 1 by ring.
    rewrite Z.mul_1_r.
    replace (A + (l - 1) * B + A + (l - 1) * B)
      with (2 * (A + (l - 1) * B)) by ring.
    rewrite Z.mul_comm, Z.div_mul by lia. nia. }
  assert (Hupper : ~ Eatable A B l t m 2000001).
  { intro He.
    pose proof (proj1 (arithmetic_segment_eatable_iff__query_semantic_core
      A B l t m 2000001 HA HB (proj1 Hl) (proj1 Ht) Hm ltac:(lia)) He)
      as [Hheight_upper _].
    nia. }
  apply query_answer_exists_bounded__query_semantic_core with
    (A := A) (B := B) (l := l) (t := t) (m := m) (U := 2000000);
    try assumption; lia.
Qed.
Lemma query_answer_minus_one_height__query_semantic_core : forall A B l t m,
  1 <= A -> 1 <= B -> 1 <= l -> 1 <= t -> 1 <= m ->
  A + (l - 1) * B > t ->
  QueryAnswer A B (l, t, m) (-1).
Proof.
  intros A B l t m HA HB Hl Ht Hm Hheight.
  unfold QueryAnswer. left. split; [reflexivity |].
  intro He.
  pose proof (proj1 (arithmetic_segment_eatable_iff__query_semantic_core
    A B l t m l HA HB Hl Ht Hm ltac:(lia)) He) as [Hle _].
  lia.
Qed.
