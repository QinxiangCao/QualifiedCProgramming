Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition DecimalRep (x : Z) (d : list Z) : Prop :=
  d <> [] /\ Znth 0 d 0 <> 0 /\ Forall (fun z => 0 <= z <= 9) d /\
  fold_left (fun a z => 10 * a + z) d 0 = x.
Definition ChangedDigits (x c : Z) : Prop :=
  exists a b L, DecimalRep x a /\ DecimalRep (x + 1) b /\ L = Z.max (Zlength a) (Zlength b) /\
    c = #(fun i : Z => 0 <= i < L /\
      Znth (i - (L - Zlength a)) a 0 <> Znth (i - (L - Zlength b)) b 0).
Definition Pre (l r : Z) : Prop :=
  (* Every clause below is stated explicitly in the P041 solver Require, which
     therefore omits the Pre(l, r) call:
       1<=l<r /\ r<=1000000000. *)
  True.
Definition Spec (l r out : Z) : Prop :=
  exists f, (forall x, l <= x < r -> ChangedDigits x (f x)) /\ out = sum_range l (r - 1) f.

(* The contribution of the decimal places 10^0, ..., 10^(k-1).
   [next] is the first place value not yet included. *)
Definition DecimalPlacePrefix (x next total : Z) : Prop :=
  exists k,
    0 <= k <= 10 /\
    next = Z.pow 10 k /\
    total = sum_range 0 (k - 1) (fun d => x / Z.pow 10 d).

(* Once the next decimal place is larger than [x], every remaining quotient
   is zero, so the prefix is the complete digit-change count up to [x]. *)
Definition DecimalPrefixTotal (x total : Z) : Prop :=
  exists next,
    x < next /\ DecimalPlacePrefix x next total.

Require Import Coq.micromega.Lia.
Require Import Coq.Numbers.DecimalNat.
Lemma decimal_place_prefix_init__changed_upto :
  forall x, DecimalPlacePrefix x 1 0.
Proof.
  intros x.
  unfold DecimalPlacePrefix.
  exists 0.
  split; [lia |].
  split; [reflexivity |].
  unfold sum_range.
  rewrite sum_Z_range_empty by lia.
  reflexivity.
Qed.
Lemma decimal_place_prefix_step__changed_upto :
  forall x p total,
    1 <= x <= 1000000000 ->
    1 <= p <= x ->
    DecimalPlacePrefix x p total ->
    DecimalPlacePrefix x (p * 10) (total + x / p).
Proof.
  intros x p total Hx Hp Hprefix.
  unfold DecimalPlacePrefix in *.
  destruct Hprefix as (k & Hk & Hpower & Htotal).
  assert (Hklt : k < 10).
  {
    assert (k <> 10).
    {
      intros ->.
      cbn in Hpower.
      lia.
    }
    lia.
  }
  exists (k + 1).
  split; [lia |].
  split.
  - replace (k + 1) with (Z.succ k) by lia.
    rewrite Z.pow_succ_r by lia.
    lia.
  - unfold sum_range in *.
    replace (k - 1 + 1) with k in Htotal by lia.
    replace (k + 1 - 1 + 1) with (k + 1) by lia.
    rewrite sum_Z_range_extend_right by lia.
    rewrite <- Htotal, <- Hpower.
    reflexivity.
Qed.
Lemma decimal_quotient_bound__changed_upto :
  forall x d,
    0 <= x <= 1000000000 ->
    0 <= d <= 9 ->
    x / Z.pow 10 d <= Z.pow 10 (9 - d).
Proof.
  intros x d Hx Hd.
  apply Z.div_le_upper_bound.
  - apply Z.pow_pos_nonneg; lia.
  - change (0 <= x <= Z.pow 10 9) in Hx.
    replace 9 with (d + (9 - d)) in Hx by lia.
    rewrite Z.pow_add_r in Hx by lia.
    nia.
Qed.
Lemma decimal_place_prefix_step_bound__changed_upto :
  forall x p total,
    1 <= x <= 1000000000 ->
    1 <= p <= x ->
    DecimalPlacePrefix x p total ->
    total + x / p <= 1111111111.
Proof.
  intros x p total Hx Hp Hprefix.
  unfold DecimalPlacePrefix in Hprefix.
  destruct Hprefix as (k & Hk & Hpower & Htotal).
  assert (Hklt : k < 10).
  {
    assert (k <> 10).
    {
      intros ->.
      cbn in Hpower.
      lia.
    }
    lia.
  }
  unfold sum_range in Htotal.
  replace (k - 1 + 1) with k in Htotal by lia.
  assert (Hpartial :
    total + x / p =
    sum (fun d : Z => 0 <= d < k + 1) (fun d => x / Z.pow 10 d)).
  {
    rewrite sum_Z_range_extend_right by lia.
    rewrite <- Htotal, <- Hpower.
    reflexivity.
  }
  rewrite Hpartial.
  assert (Hextend :
    sum (fun d : Z => 0 <= d < k + 1) (fun d => x / Z.pow 10 d) <=
    sum (fun d : Z => 0 <= d < 10) (fun d => x / Z.pow 10 d)).
  {
    rewrite (sum_Z_range_split 0 (k + 1) 10) by lia.
    assert (0 <=
      sum (fun d : Z => k + 1 <= d < 10) (fun d => x / Z.pow 10 d)).
    {
      apply sum_nonneg.
      intros d Hd.
      apply Z_div_nonneg_nonneg.
      - lia.
      - apply Z.pow_nonneg; lia.
    }
    lia.
  }
  eapply Z.le_trans; [exact Hextend |].
  eapply Z.le_trans.
  - apply sum_Z_range_le.
    intros d Hd.
    apply decimal_quotient_bound__changed_upto; lia.
  - rewrite sum_range_unfold.
    vm_compute.
    discriminate.
Qed.
Lemma set_card_iff__solver_result :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  { apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intro x. rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      apply Hequiv. }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun _ acc => 1 + acc) 0 l =
            1 + fold_right (fun _ acc => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma decimal_digits_fold__solver_result :
  let value := fix value (d : Decimal.uint) : Z :=
    match d with
    | Decimal.Nil => 0
    | Decimal.D0 t => 10 * value t
    | Decimal.D1 t => 1 + 10 * value t
    | Decimal.D2 t => 2 + 10 * value t
    | Decimal.D3 t => 3 + 10 * value t
    | Decimal.D4 t => 4 + 10 * value t
    | Decimal.D5 t => 5 + 10 * value t
    | Decimal.D6 t => 6 + 10 * value t
    | Decimal.D7 t => 7 + 10 * value t
    | Decimal.D8 t => 8 + 10 * value t
    | Decimal.D9 t => 9 + 10 * value t
    end in
  let digits := fix digits (d : Decimal.uint) : list Z :=
    match d with
    | Decimal.Nil => []
    | Decimal.D0 t => digits t ++ [0]
    | Decimal.D1 t => digits t ++ [1]
    | Decimal.D2 t => digits t ++ [2]
    | Decimal.D3 t => digits t ++ [3]
    | Decimal.D4 t => digits t ++ [4]
    | Decimal.D5 t => digits t ++ [5]
    | Decimal.D6 t => digits t ++ [6]
    | Decimal.D7 t => digits t ++ [7]
    | Decimal.D8 t => digits t ++ [8]
    | Decimal.D9 t => digits t ++ [9]
    end in
  forall d, fold_left (fun a z => 10 * a + z) (digits d) 0 = value d.
Proof.
  cbn zeta. intro d. induction d; cbn.
  - reflexivity.
  - rewrite fold_left_app. simpl fold_left.
    match type of IHd with ?L = ?R => change (10 * L + 0 = 10 * R) end.
    rewrite IHd. ring.
  - rewrite fold_left_app. simpl fold_left.
    match type of IHd with ?L = ?R => change (10 * L + 1 = 1 + 10 * R) end.
    rewrite IHd. ring.
  - rewrite fold_left_app. simpl fold_left.
    match type of IHd with ?L = ?R => change (10 * L + 2 = 2 + 10 * R) end.
    rewrite IHd. ring.
  - rewrite fold_left_app. simpl fold_left.
    match type of IHd with ?L = ?R => change (10 * L + 3 = 3 + 10 * R) end.
    rewrite IHd. ring.
  - rewrite fold_left_app. simpl fold_left.
    match type of IHd with ?L = ?R => change (10 * L + 4 = 4 + 10 * R) end.
    rewrite IHd. ring.
  - rewrite fold_left_app. simpl fold_left.
    match type of IHd with ?L = ?R => change (10 * L + 5 = 5 + 10 * R) end.
    rewrite IHd. ring.
  - rewrite fold_left_app. simpl fold_left.
    match type of IHd with ?L = ?R => change (10 * L + 6 = 6 + 10 * R) end.
    rewrite IHd. ring.
  - rewrite fold_left_app. simpl fold_left.
    match type of IHd with ?L = ?R => change (10 * L + 7 = 7 + 10 * R) end.
    rewrite IHd. ring.
  - rewrite fold_left_app. simpl fold_left.
    match type of IHd with ?L = ?R => change (10 * L + 8 = 8 + 10 * R) end.
    rewrite IHd. ring.
  - rewrite fold_left_app. simpl fold_left.
    match type of IHd with ?L = ?R => change (10 * L + 9 = 9 + 10 * R) end.
    rewrite IHd. ring.
Qed.
Lemma decimal_digits_bounds__solver_result :
  let digits := fix digits (d : Decimal.uint) : list Z :=
    match d with
    | Decimal.Nil => []
    | Decimal.D0 t => digits t ++ [0]
    | Decimal.D1 t => digits t ++ [1]
    | Decimal.D2 t => digits t ++ [2]
    | Decimal.D3 t => digits t ++ [3]
    | Decimal.D4 t => digits t ++ [4]
    | Decimal.D5 t => digits t ++ [5]
    | Decimal.D6 t => digits t ++ [6]
    | Decimal.D7 t => digits t ++ [7]
    | Decimal.D8 t => digits t ++ [8]
    | Decimal.D9 t => digits t ++ [9]
    end in
  forall d, Forall (fun z : Z => 0 <= z <= 9) (digits d).
Proof.
  cbn zeta. intro d. induction d; cbn.
  - constructor.
  - rewrite Forall_app. cbn.
    split; [exact IHd|repeat constructor; lia].
  - rewrite Forall_app. cbn.
    split; [exact IHd|repeat constructor; lia].
  - rewrite Forall_app. cbn.
    split; [exact IHd|repeat constructor; lia].
  - rewrite Forall_app. cbn.
    split; [exact IHd|repeat constructor; lia].
  - rewrite Forall_app. cbn.
    split; [exact IHd|repeat constructor; lia].
  - rewrite Forall_app. cbn.
    split; [exact IHd|repeat constructor; lia].
  - rewrite Forall_app. cbn.
    split; [exact IHd|repeat constructor; lia].
  - rewrite Forall_app. cbn.
    split; [exact IHd|repeat constructor; lia].
  - rewrite Forall_app. cbn.
    split; [exact IHd|repeat constructor; lia].
  - rewrite Forall_app. cbn.
    split; [exact IHd|repeat constructor; lia].
Qed.
Lemma decimal_list_canonical_append__solver_result :
  forall (a : list Z) x,
    (a ++ [x] <> [] /\ Znth 0 (a ++ [x]) 0 <> 0) <->
    (a <> [] /\ Znth 0 a 0 <> 0) \/ (a = [] /\ x <> 0).
Proof.
  intros [|h t] x; unfold Znth; cbn; intuition congruence.
Qed.
Lemma decimal_digits_canonical_succ__solver_result :
  let digits := fix digits (d : Decimal.uint) : list Z :=
    match d with
    | Decimal.Nil => []
    | Decimal.D0 t => digits t ++ [0]
    | Decimal.D1 t => digits t ++ [1]
    | Decimal.D2 t => digits t ++ [2]
    | Decimal.D3 t => digits t ++ [3]
    | Decimal.D4 t => digits t ++ [4]
    | Decimal.D5 t => digits t ++ [5]
    | Decimal.D6 t => digits t ++ [6]
    | Decimal.D7 t => digits t ++ [7]
    | Decimal.D8 t => digits t ++ [8]
    | Decimal.D9 t => digits t ++ [9]
    end in
  forall d,
    digits d <> [] /\ Znth 0 (digits d) 0 <> 0 ->
    digits (Decimal.Little.succ d) <> [] /\
      Znth 0 (digits (Decimal.Little.succ d)) 0 <> 0.
Proof.
  cbn zeta. intro d. induction d; cbn [Decimal.Little.succ]; intro Hcan.
  - destruct Hcan as [Hbad _]. exfalso. apply Hbad. reflexivity.
  - rewrite decimal_list_canonical_append__solver_result in *.
    destruct Hcan as [Hcan | [-> Hbad]].
    + left. exact Hcan.
    + exfalso. lia.
  - rewrite decimal_list_canonical_append__solver_result in *.
    destruct Hcan as [Hcan | [-> Hx]].
    + left. exact Hcan.
    + right. split; [reflexivity|lia].
  - rewrite decimal_list_canonical_append__solver_result in *.
    destruct Hcan as [Hcan | [-> Hx]].
    + left. exact Hcan.
    + right. split; [reflexivity|lia].
  - rewrite decimal_list_canonical_append__solver_result in *.
    destruct Hcan as [Hcan | [-> Hx]].
    + left. exact Hcan.
    + right. split; [reflexivity|lia].
  - rewrite decimal_list_canonical_append__solver_result in *.
    destruct Hcan as [Hcan | [-> Hx]].
    + left. exact Hcan.
    + right. split; [reflexivity|lia].
  - rewrite decimal_list_canonical_append__solver_result in *.
    destruct Hcan as [Hcan | [-> Hx]].
    + left. exact Hcan.
    + right. split; [reflexivity|lia].
  - rewrite decimal_list_canonical_append__solver_result in *.
    destruct Hcan as [Hcan | [-> Hx]].
    + left. exact Hcan.
    + right. split; [reflexivity|lia].
  - rewrite decimal_list_canonical_append__solver_result in *.
    destruct Hcan as [Hcan | [-> Hx]].
    + left. exact Hcan.
    + right. split; [reflexivity|lia].
  - rewrite decimal_list_canonical_append__solver_result in *.
    destruct Hcan as [Hcan | [-> Hx]].
    + left. exact Hcan.
    + right. split; [reflexivity|lia].
  - rewrite decimal_list_canonical_append__solver_result in Hcan |- *.
    destruct Hcan as [Htail | [Hnil _]].
    + left. apply IHd. exact Htail.
    + assert (Hd : d = Decimal.Nil).
      { destruct d; [reflexivity|..]; cbn in Hnil;
          exfalso; apply app_eq_nil in Hnil as [_ Hbad]; discriminate. }
      subst d. cbn [Decimal.Little.succ]. left. split.
      * discriminate.
      * unfold Znth. cbn. discriminate.
Qed.
Lemma decimal_digits_to_lu_canonical__solver_result :
  let digits := fix digits (d : Decimal.uint) : list Z :=
    match d with
    | Decimal.Nil => []
    | Decimal.D0 t => digits t ++ [0]
    | Decimal.D1 t => digits t ++ [1]
    | Decimal.D2 t => digits t ++ [2]
    | Decimal.D3 t => digits t ++ [3]
    | Decimal.D4 t => digits t ++ [4]
    | Decimal.D5 t => digits t ++ [5]
    | Decimal.D6 t => digits t ++ [6]
    | Decimal.D7 t => digits t ++ [7]
    | Decimal.D8 t => digits t ++ [8]
    | Decimal.D9 t => digits t ++ [9]
    end in
  forall n, (0 < n)%nat ->
    digits (DecimalNat.Unsigned.to_lu n) <> [] /\
      Znth 0 (digits (DecimalNat.Unsigned.to_lu n)) 0 <> 0.
Proof.
  cbn zeta. intro n. induction n as [|n IH]; intro Hn; [lia|].
  destruct n as [|n].
  - cbn [DecimalNat.Unsigned.to_lu Decimal.Little.succ].
    split; [discriminate|]. unfold Znth. cbn. discriminate.
  - cbn [DecimalNat.Unsigned.to_lu].
    apply decimal_digits_canonical_succ__solver_result.
    apply IH. lia.
Qed.
Lemma set_card_Z_as_sum__solver_result :
  forall (low high : Z) (P : Z -> Prop),
    #(fun x : Z => low <= x < high /\ P x) =
    SumLib.Sum.sum (fun x : Z => low <= x < high)
      (fun x => if prop_dec (P x) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall xs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun x => if prop_dec (P x) then true else false) xs) =
    fold_right (fun x acc : Z =>
      (if prop_dec (P x) then 1 else 0) + acc) 0 xs).
  { induction xs as [|x xs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P x)); simpl.
    - exact (f_equal (fun z : Z => 1 + z) IH).
    - exact IH. }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_true__solver_result :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun x : Z => low <= x < high + 1 /\ P x) =
    #(fun x : Z => low <= x < high /\ P x) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__solver_result.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)); [lia | contradiction].
Qed.
Lemma decimal_list_diff_append__solver_result :
  forall a b x y,
    (a = [] <-> b = []) -> x <> y ->
    #(fun i : Z =>
        0 <= i < Z.max (Zlength (a ++ [x])) (Zlength (b ++ [y])) /\
        Znth (i - (Z.max (Zlength (a ++ [x])) (Zlength (b ++ [y])) -
                    Zlength (a ++ [x]))) (a ++ [x]) 0 <>
        Znth (i - (Z.max (Zlength (a ++ [x])) (Zlength (b ++ [y])) -
                    Zlength (b ++ [y]))) (b ++ [y]) 0) =
    #(fun i : Z =>
        0 <= i < Z.max (Zlength a) (Zlength b) /\
        Znth (i - (Z.max (Zlength a) (Zlength b) - Zlength a)) a 0 <>
        Znth (i - (Z.max (Zlength a) (Zlength b) - Zlength b)) b 0) + 1.
Proof.
  intros a b x y Hnil Hxy.
  rewrite !Zlength_app_cons.
  set (la := Zlength a). set (lb := Zlength b). set (L := Z.max la lb).
  assert (Hla : 0 <= la) by (subst la; apply Zlength_nonneg).
  assert (Hlb : 0 <= lb) by (subst lb; apply Zlength_nonneg).
  assert (HL : 0 <= L).
  { subst L. destruct (Z_le_gt_dec la lb).
    - rewrite Z.max_r by lia. lia.
    - rewrite Z.max_l by lia. lia. }
  assert (Hmax : Z.max (la + 1) (lb + 1) = L + 1).
  { subst L. destruct (Z_le_gt_dec la lb).
    - rewrite !Z.max_r by lia. lia.
    - rewrite !Z.max_l by lia. lia. }
  rewrite Hmax.
  rewrite set_card_Z_extend_true__solver_result with
      (P := fun i =>
        Znth (i - (L + 1 - (la + 1))) (a ++ [x]) 0 <>
        Znth (i - (L + 1 - (lb + 1))) (b ++ [y]) 0); [|lia|].
  2:{ replace (L + 1 - (la + 1)) with (L - la) by lia.
      replace (L + 1 - (lb + 1)) with (L - lb) by lia.
      replace (L - (L - la)) with la by lia.
      replace (L - (L - lb)) with lb by lia.
      rewrite !app_Znth2 by lia.
      replace (la - Zlength a) with 0 by (subst la; lia).
      replace (lb - Zlength b) with 0 by (subst lb; lia).
      simpl. exact Hxy. }
  f_equal.
  eapply set_card_iff__solver_result. intro i.
  replace (L + 1 - (la + 1)) with (L - la) by lia.
  replace (L + 1 - (lb + 1)) with (L - lb) by lia.
  split.
  - intros [[Hi0 HiL] Hne]. split; [lia|].
    assert (Ha : Znth (i - (L - la)) (a ++ [x]) 0 =
                 Znth (i - (L - la)) a 0).
    { destruct (Z_lt_ge_dec (i - (L - la)) 0) as [Hneg|Hnonneg].
      - destruct a as [|ah atl].
        + assert (Hbempty : b = []) by (apply Hnil; reflexivity).
          subst b. subst la lb L. simpl in HiL. lia.
        + unfold Znth. destruct (i - (L - la)); simpl in *; try lia; reflexivity.
      - apply app_Znth1. lia. }
    assert (Hb : Znth (i - (L - lb)) (b ++ [y]) 0 =
                 Znth (i - (L - lb)) b 0).
    { destruct (Z_lt_ge_dec (i - (L - lb)) 0) as [Hneg|Hnonneg].
      - destruct b as [|bh bt].
        + assert (Haempty : a = []) by (apply (proj2 Hnil); reflexivity).
          subst a. subst la lb L. simpl in HiL. lia.
        + unfold Znth. destruct (i - (L - lb)); simpl in *; try lia; reflexivity.
      - apply app_Znth1. lia. }
    now rewrite Ha, Hb in Hne.
  - intros [[Hi0 HiL] Hne]. split; [lia|].
    assert (Ha : Znth (i - (L - la)) (a ++ [x]) 0 =
                 Znth (i - (L - la)) a 0).
    { destruct (Z_lt_ge_dec (i - (L - la)) 0) as [Hneg|Hnonneg].
      - destruct a as [|ah atl].
        + assert (Hbempty : b = []) by (apply Hnil; reflexivity).
          subst b. subst la lb L. simpl in HiL. lia.
        + unfold Znth. destruct (i - (L - la)); simpl in *; try lia; reflexivity.
      - apply app_Znth1. lia. }
    assert (Hb : Znth (i - (L - lb)) (b ++ [y]) 0 =
                 Znth (i - (L - lb)) b 0).
    { destruct (Z_lt_ge_dec (i - (L - lb)) 0) as [Hneg|Hnonneg].
      - destruct b as [|bh bt].
        + assert (Haempty : a = []) by (apply (proj2 Hnil); reflexivity).
          subst a. subst la lb L. simpl in HiL. lia.
        + unfold Znth. destruct (i - (L - lb)); simpl in *; try lia; reflexivity.
      - apply app_Znth1. lia. }
    now rewrite Ha, Hb.
Qed.
Lemma decimal_list_diff_refl__solver_result :
  forall a,
    #(fun i : Z =>
        0 <= i < Z.max (Zlength a) (Zlength a) /\
        Znth (i - (Z.max (Zlength a) (Zlength a) - Zlength a)) a 0 <>
        Znth (i - (Z.max (Zlength a) (Zlength a) - Zlength a)) a 0) = 0.
Proof.
  intro a.
  replace 0 with (#(fun i : Z => 0 <= i < 0)).
  2:{ cbv [set_card SumLib.Sum.sum enum finite_Z_range Zrange Zrange_aux].
      reflexivity. }
  eapply set_card_iff__solver_result with
      (Q := fun i : Z => 0 <= i < 0).
  intro i. rewrite Z.max_id. lia.
Qed.
Lemma decimal_prefix_total_canonical_sum__solver_result :
  forall x total,
    1 <= x <= 1000000000 -> DecimalPrefixTotal x total ->
    total = sum_range 0 9 (fun d => x / Z.pow 10 d).
Proof.
  intros x total Hx [next [Hxnext [k [[Hk0 Hk10] [Hnext Htotal]]]]].
  subst next total.
  assert (Hcases : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/
                   k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10)
    by lia.
  decompose [or] Hcases; subst k;
    cbv [sum_range SumLib.Sum.sum enum finite_Z_range Zrange Zrange_aux
         Z.to_nat Pos.to_nat Pos.iter_op Z.pow Z.pow_pos Pos.iter] in *;
    cbn in *.
  all: try lia.
  all: try (rewrite (Z.div_small x 1000000000) by lia).
  all: try (rewrite (Z.div_small x 100000000) by lia).
  all: try (rewrite (Z.div_small x 10000000) by lia).
  all: try (rewrite (Z.div_small x 1000000) by lia).
  all: try (rewrite (Z.div_small x 100000) by lia).
  all: try (rewrite (Z.div_small x 10000) by lia).
  all: try (rewrite (Z.div_small x 1000) by lia).
  all: try (rewrite (Z.div_small x 100) by lia).
  all: try (rewrite (Z.div_small x 10) by lia).
  all: try ring.
Qed.
Lemma sum_range_difference_telescope__solver_result :
  forall (F : Z -> Z) lo hi,
    lo <= hi ->
    sum_range lo (hi - 1) (fun x => F (x + 1) - F x) = F hi - F lo.
Proof.
  intros F lo hi Hle.
  set (n := Z.to_nat (hi - lo)).
  assert (Hhi : hi = lo + Z.of_nat n).
  { subst n. rewrite Z2Nat.id by lia. lia. }
  clearbody n.
  subst hi. clear Hle.
  unfold sum_range.
  induction n as [|n IH].
  - cbn [Z.of_nat].
    replace (lo + 0 - 1 + 1) with lo by lia.
    replace (lo + 0) with lo by lia.
    rewrite SumLib.ZRange.sum_Z_range_empty by lia. lia.
  - rewrite Nat2Z.inj_succ.
    replace (lo + (Z.of_nat n + 1) - 1 + 1) with
        (lo + Z.of_nat n + 1) by lia.
    rewrite SumLib.ZRange.sum_Z_range_extend_right by lia.
    replace (lo + Z.of_nat n - 1 + 1) with
        (lo + Z.of_nat n) in IH by lia.
    replace (lo + Z.succ (Z.of_nat n) - 1) with
        (lo + Z.of_nat n) by (unfold Z.succ; lia).
    replace (lo + Z.succ (Z.of_nat n) - 1 + 1) with
        (lo + Z.of_nat n + 1) by (unfold Z.succ; lia).
    replace (lo + Z.succ (Z.of_nat n)) with
        (lo + Z.of_nat n + 1) by (unfold Z.succ; lia).
    rewrite IH. ring.
Qed.
Lemma decimal_uint_value_succ__solver_result :
  let value := fix value (d : Decimal.uint) : Z :=
    match d with
    | Decimal.Nil => 0
    | Decimal.D0 t => 10 * value t
    | Decimal.D1 t => 1 + 10 * value t
    | Decimal.D2 t => 2 + 10 * value t
    | Decimal.D3 t => 3 + 10 * value t
    | Decimal.D4 t => 4 + 10 * value t
    | Decimal.D5 t => 5 + 10 * value t
    | Decimal.D6 t => 6 + 10 * value t
    | Decimal.D7 t => 7 + 10 * value t
    | Decimal.D8 t => 8 + 10 * value t
    | Decimal.D9 t => 9 + 10 * value t
    end in
  forall d, value (Decimal.Little.succ d) = value d + 1.
Proof.
  cbn zeta. intro d. induction d; cbn [Decimal.Little.succ]; lia.
Qed.
Lemma decimal_uint_value_to_lu__solver_result :
  let value := fix value (d : Decimal.uint) : Z :=
    match d with
    | Decimal.Nil => 0
    | Decimal.D0 t => 10 * value t
    | Decimal.D1 t => 1 + 10 * value t
    | Decimal.D2 t => 2 + 10 * value t
    | Decimal.D3 t => 3 + 10 * value t
    | Decimal.D4 t => 4 + 10 * value t
    | Decimal.D5 t => 5 + 10 * value t
    | Decimal.D6 t => 6 + 10 * value t
    | Decimal.D7 t => 7 + 10 * value t
    | Decimal.D8 t => 8 + 10 * value t
    | Decimal.D9 t => 9 + 10 * value t
    end in
  forall n, value (DecimalNat.Unsigned.to_lu n) = Z.of_nat n.
Proof.
  cbn zeta. intro n. induction n as [|n IH]; cbn [DecimalNat.Unsigned.to_lu].
  - reflexivity.
  - rewrite decimal_uint_value_succ__solver_result, IH, Nat2Z.inj_succ.
    unfold Z.succ. lia.
Qed.
Lemma decimal_uint_diff_succ__solver_result :
  let digits := fix digits (d : Decimal.uint) : list Z :=
    match d with
    | Decimal.Nil => []
    | Decimal.D0 t => digits t ++ [0]
    | Decimal.D1 t => digits t ++ [1]
    | Decimal.D2 t => digits t ++ [2]
    | Decimal.D3 t => digits t ++ [3]
    | Decimal.D4 t => digits t ++ [4]
    | Decimal.D5 t => digits t ++ [5]
    | Decimal.D6 t => digits t ++ [6]
    | Decimal.D7 t => digits t ++ [7]
    | Decimal.D8 t => digits t ++ [8]
    | Decimal.D9 t => digits t ++ [9]
    end in
  let carry := fix carry (d : Decimal.uint) : Z :=
    match d with Decimal.D9 t => 1 + carry t | _ => 1 end in
  forall d,
    #(fun i : Z =>
        0 <= i < Z.max (Zlength (digits d))
                         (Zlength (digits (Decimal.Little.succ d))) /\
        Znth (i - (Z.max (Zlength (digits d))
                         (Zlength (digits (Decimal.Little.succ d))) -
                    Zlength (digits d))) (digits d) 0 <>
        Znth (i - (Z.max (Zlength (digits d))
                         (Zlength (digits (Decimal.Little.succ d))) -
                    Zlength (digits (Decimal.Little.succ d))))
             (digits (Decimal.Little.succ d)) 0) = carry d.
Proof.
  cbn zeta. intro d. induction d; cbn [Decimal.Little.succ].
  - change (#(fun i : Z =>
        0 <= i < 1 /\ Znth (i - 1) [] 0 <> Znth i [1] 0) = 1).
    replace 1 with (#(fun i : Z => 0 <= i < 1)).
    2:{ cbv [set_card SumLib.Sum.sum enum finite_Z_range Zrange Zrange_aux].
        reflexivity. }
    eapply set_card_iff__solver_result. intro i. split.
    + tauto.
    + intro Hi. assert (i = 0) by lia. subst i. split; [exact Hi|].
      unfold Znth. cbn. discriminate.
  - rewrite decimal_list_diff_append__solver_result.
    + rewrite decimal_list_diff_refl__solver_result. lia.
    + tauto.
    + lia.
  - rewrite decimal_list_diff_append__solver_result.
    + rewrite decimal_list_diff_refl__solver_result. lia.
    + tauto.
    + lia.
  - rewrite decimal_list_diff_append__solver_result.
    + rewrite decimal_list_diff_refl__solver_result. lia.
    + tauto.
    + lia.
  - rewrite decimal_list_diff_append__solver_result.
    + rewrite decimal_list_diff_refl__solver_result. lia.
    + tauto.
    + lia.
  - rewrite decimal_list_diff_append__solver_result.
    + rewrite decimal_list_diff_refl__solver_result. lia.
    + tauto.
    + lia.
  - rewrite decimal_list_diff_append__solver_result.
    + rewrite decimal_list_diff_refl__solver_result. lia.
    + tauto.
    + lia.
  - rewrite decimal_list_diff_append__solver_result.
    + rewrite decimal_list_diff_refl__solver_result. lia.
    + tauto.
    + lia.
  - rewrite decimal_list_diff_append__solver_result.
    + rewrite decimal_list_diff_refl__solver_result. lia.
    + tauto.
    + lia.
  - rewrite decimal_list_diff_append__solver_result.
    + rewrite decimal_list_diff_refl__solver_result. lia.
    + tauto.
    + lia.
  - destruct d; cbn [Decimal.Little.succ] in *.
    + change (#(fun i : Z =>
          0 <= i < 2 /\ Znth (i - 1) [9] 0 <> Znth i [1; 0] 0) = 2).
      replace 2 with (#(fun i : Z => 0 <= i < 2)).
      2:{ cbv [set_card SumLib.Sum.sum enum finite_Z_range Zrange Zrange_aux].
          reflexivity. }
      eapply set_card_iff__solver_result. intro i. split.
      * tauto.
      * intro Hi. assert (i = 0 \/ i = 1) by lia.
        destruct H as [-> | ->].
        -- split; [exact Hi|]. unfold Znth. cbn. discriminate.
        -- split; [exact Hi|]. unfold Znth. cbn. discriminate.
    + rewrite decimal_list_diff_append__solver_result.
      * rewrite IHd. lia.
      * split; intro Hnil; apply app_eq_nil in Hnil as [_ Hbad]; discriminate.
      * discriminate.
    + rewrite decimal_list_diff_append__solver_result.
      * rewrite IHd. lia.
      * split; intro Hnil; apply app_eq_nil in Hnil as [_ Hbad]; discriminate.
      * discriminate.
    + rewrite decimal_list_diff_append__solver_result.
      * rewrite IHd. lia.
      * split; intro Hnil; apply app_eq_nil in Hnil as [_ Hbad]; discriminate.
      * discriminate.
    + rewrite decimal_list_diff_append__solver_result.
      * rewrite IHd. lia.
      * split; intro Hnil; apply app_eq_nil in Hnil as [_ Hbad]; discriminate.
      * discriminate.
    + rewrite decimal_list_diff_append__solver_result.
      * rewrite IHd. lia.
      * split; intro Hnil; apply app_eq_nil in Hnil as [_ Hbad]; discriminate.
      * discriminate.
    + rewrite decimal_list_diff_append__solver_result.
      * rewrite IHd. lia.
      * split; intro Hnil; apply app_eq_nil in Hnil as [_ Hbad]; discriminate.
      * discriminate.
    + rewrite decimal_list_diff_append__solver_result.
      * rewrite IHd. lia.
      * split; intro Hnil; apply app_eq_nil in Hnil as [_ Hbad]; discriminate.
      * discriminate.
    + rewrite decimal_list_diff_append__solver_result.
      * rewrite IHd. lia.
      * split; intro Hnil; apply app_eq_nil in Hnil as [_ Hbad]; discriminate.
      * discriminate.
    + rewrite decimal_list_diff_append__solver_result.
      * rewrite IHd. lia.
      * split; intro Hnil; apply app_eq_nil in Hnil as [_ Hbad]; discriminate.
      * discriminate.
    + rewrite decimal_list_diff_append__solver_result.
      * rewrite IHd. lia.
      * split; intro Hnil; apply app_eq_nil in Hnil as [_ Hbad]; discriminate.
      * discriminate.
Qed.
Lemma decimal_rep_to_lu__solver_result :
  let digits := fix digits (d : Decimal.uint) : list Z :=
    match d with
    | Decimal.Nil => []
    | Decimal.D0 t => digits t ++ [0]
    | Decimal.D1 t => digits t ++ [1]
    | Decimal.D2 t => digits t ++ [2]
    | Decimal.D3 t => digits t ++ [3]
    | Decimal.D4 t => digits t ++ [4]
    | Decimal.D5 t => digits t ++ [5]
    | Decimal.D6 t => digits t ++ [6]
    | Decimal.D7 t => digits t ++ [7]
    | Decimal.D8 t => digits t ++ [8]
    | Decimal.D9 t => digits t ++ [9]
    end in
  forall n, (0 < n)%nat ->
    DecimalRep (Z.of_nat n) (digits (DecimalNat.Unsigned.to_lu n)).
Proof.
  cbn zeta. intros n Hn. unfold DecimalRep.
  pose proof decimal_digits_to_lu_canonical__solver_result n Hn as Hcan.
  destruct Hcan as [Hnonempty Hhead].
  repeat split; try assumption.
  - apply decimal_digits_bounds__solver_result.
  - rewrite decimal_digits_fold__solver_result.
    apply decimal_uint_value_to_lu__solver_result.
Qed.
Lemma decimal_uint_value_nonnegative__solver_result :
  let value := fix value (d : Decimal.uint) : Z :=
    match d with
    | Decimal.Nil => 0
    | Decimal.D0 t => 10 * value t
    | Decimal.D1 t => 1 + 10 * value t
    | Decimal.D2 t => 2 + 10 * value t
    | Decimal.D3 t => 3 + 10 * value t
    | Decimal.D4 t => 4 + 10 * value t
    | Decimal.D5 t => 5 + 10 * value t
    | Decimal.D6 t => 6 + 10 * value t
    | Decimal.D7 t => 7 + 10 * value t
    | Decimal.D8 t => 8 + 10 * value t
    | Decimal.D9 t => 9 + 10 * value t
    end in
  forall d, 0 <= value d.
Proof.
  cbn zeta. intro d. induction d; cbn.
  - lia.
  - match type of IHd with 0 <= ?R => change (0 <= 10 * R) end. lia.
  - match type of IHd with 0 <= ?R => change (0 <= 1 + 10 * R) end. lia.
  - match type of IHd with 0 <= ?R => change (0 <= 2 + 10 * R) end. lia.
  - match type of IHd with 0 <= ?R => change (0 <= 3 + 10 * R) end. lia.
  - match type of IHd with 0 <= ?R => change (0 <= 4 + 10 * R) end. lia.
  - match type of IHd with 0 <= ?R => change (0 <= 5 + 10 * R) end. lia.
  - match type of IHd with 0 <= ?R => change (0 <= 6 + 10 * R) end. lia.
  - match type of IHd with 0 <= ?R => change (0 <= 7 + 10 * R) end. lia.
  - match type of IHd with 0 <= ?R => change (0 <= 8 + 10 * R) end. lia.
  - match type of IHd with 0 <= ?R => change (0 <= 9 + 10 * R) end. lia.
Qed.
Lemma decimal_digit_div10__solver_result :
  forall q k, 0 <= q -> 0 <= k < 10 -> (k + 10 * q) / 10 = q.
Proof.
  intros q k Hq Hk.
  replace (k + 10 * q) with (q * 10 + k) by ring.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by lia.
  lia.
Qed.
Lemma decimal_ten_div10__solver_result :
  forall q, (10 * q) / 10 = q.
Proof.
  intro q. rewrite Z.mul_comm, Z.div_mul; lia.
Qed.
Lemma decimal_qsum_succ__solver_result :
  let value := fix value (d : Decimal.uint) : Z :=
    match d with
    | Decimal.Nil => 0
    | Decimal.D0 t => 10 * value t
    | Decimal.D1 t => 1 + 10 * value t
    | Decimal.D2 t => 2 + 10 * value t
    | Decimal.D3 t => 3 + 10 * value t
    | Decimal.D4 t => 4 + 10 * value t
    | Decimal.D5 t => 5 + 10 * value t
    | Decimal.D6 t => 6 + 10 * value t
    | Decimal.D7 t => 7 + 10 * value t
    | Decimal.D8 t => 8 + 10 * value t
    | Decimal.D9 t => 9 + 10 * value t
    end in
  let carry := fix carry (d : Decimal.uint) : Z :=
    match d with Decimal.D9 t => 1 + carry t | _ => 1 end in
  let depth := fix depth (d : Decimal.uint) : nat :=
    match d with Decimal.D9 t => S (depth t) | _ => 1%nat end in
  let qsum := fix qsum (fuel : nat) (x : Z) : Z :=
    match fuel with 0%nat => 0 | S n => x + qsum n (x / 10) end in
  forall d fuel, (depth d <= fuel)%nat ->
    qsum fuel (value (Decimal.Little.succ d)) - qsum fuel (value d) = carry d.
Proof.
  cbn zeta. intro d. induction d; intros fuel Hfuel.
  all: destruct fuel as [|fuel]; [lia|].
  all: cbn [Decimal.Little.succ].
  - replace ((1 + 10 * 0) / 10) with 0 by reflexivity.
    replace (0 / 10) with 0 by reflexivity. ring.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    rewrite !decimal_digit_div10__solver_result by lia.
    rewrite ?decimal_ten_div10__solver_result. ring.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    rewrite !decimal_digit_div10__solver_result by lia.
    rewrite ?decimal_ten_div10__solver_result. ring.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    rewrite !decimal_digit_div10__solver_result by lia.
    rewrite ?decimal_ten_div10__solver_result. ring.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    rewrite !decimal_digit_div10__solver_result by lia.
    rewrite ?decimal_ten_div10__solver_result. ring.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    rewrite !decimal_digit_div10__solver_result by lia.
    rewrite ?decimal_ten_div10__solver_result. ring.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    rewrite !decimal_digit_div10__solver_result by lia.
    rewrite ?decimal_ten_div10__solver_result. ring.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    rewrite !decimal_digit_div10__solver_result by lia.
    rewrite ?decimal_ten_div10__solver_result. ring.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    rewrite !decimal_digit_div10__solver_result by lia.
    rewrite ?decimal_ten_div10__solver_result. ring.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    rewrite !decimal_digit_div10__solver_result by lia.
    rewrite ?decimal_ten_div10__solver_result. ring.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    pose proof decimal_uint_value_succ__solver_result d as Hsucc.
    rewrite !decimal_digit_div10__solver_result by lia.
    rewrite ?decimal_ten_div10__solver_result.
    specialize (IHd fuel ltac:(lia)). lia.
Qed.
Lemma decimal_carry_depth_bound__solver_result :
  let value := fix value (d : Decimal.uint) : Z :=
    match d with
    | Decimal.Nil => 0
    | Decimal.D0 t => 10 * value t
    | Decimal.D1 t => 1 + 10 * value t
    | Decimal.D2 t => 2 + 10 * value t
    | Decimal.D3 t => 3 + 10 * value t
    | Decimal.D4 t => 4 + 10 * value t
    | Decimal.D5 t => 5 + 10 * value t
    | Decimal.D6 t => 6 + 10 * value t
    | Decimal.D7 t => 7 + 10 * value t
    | Decimal.D8 t => 8 + 10 * value t
    | Decimal.D9 t => 9 + 10 * value t
    end in
  let depth := fix depth (d : Decimal.uint) : nat :=
    match d with Decimal.D9 t => S (depth t) | _ => 1%nat end in
  forall n d, value d < Z.pow 10 (Z.of_nat n) -> (depth d <= S n)%nat.
Proof.
  cbn zeta. intro n. induction n as [|n IH]; intro d; destruct d; cbn; intro H.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    match type of Hq with 0 <= ?Q => change (9 + 10 * Q < 1) in H end.
    lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - apply le_n_S. apply IH.
    pose proof decimal_uint_value_nonnegative__solver_result d as Hq.
    match type of Hq with 0 <= ?Q =>
      change (9 + 10 * Q < Z.pow 10 (Z.of_nat (S n))) in H
    end.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia.
    nia.
Qed.
Lemma decimal_qsum_ten_as_sum_range__solver_result :
  let qsum := fix qsum (fuel : nat) (x : Z) : Z :=
    match fuel with 0%nat => 0 | S n => x + qsum n (x / 10) end in
  forall x, 0 <= x ->
    qsum 10%nat x = sum_range 0 9 (fun d => x / Z.pow 10 d).
Proof.
  cbn zeta. intros x Hx.
  unfold sum_range.
  rewrite SumLib.ZRange.sum_range_unfold.
  unfold Zrange.
  replace (Z.to_nat (9 + 1 - 0)) with 10%nat by reflexivity.
  cbn [Zrange_aux Z.pow].
  repeat rewrite Z.div_div by lia.
  rewrite ?Z.div_1_r.
  cbn [fold_right Z.pow].
  rewrite Z.div_1_r. reflexivity.
Qed.
Lemma changed_digits_successor_sum_delta__solver_result :
  forall x, 1 <= x < 1000000000 ->
    ChangedDigits x
      (sum_range 0 9 (fun d => (x + 1) / Z.pow 10 d) -
       sum_range 0 9 (fun d => x / Z.pow 10 d)).
Proof.
  intros x Hx. unfold ChangedDigits.
  set (d := DecimalNat.Unsigned.to_lu (Z.to_nat x)).
  set (digits := (fix digits (u : Decimal.uint) : list Z :=
    match u with
    | Decimal.Nil => []
    | Decimal.D0 t => digits t ++ [0]
    | Decimal.D1 t => digits t ++ [1]
    | Decimal.D2 t => digits t ++ [2]
    | Decimal.D3 t => digits t ++ [3]
    | Decimal.D4 t => digits t ++ [4]
    | Decimal.D5 t => digits t ++ [5]
    | Decimal.D6 t => digits t ++ [6]
    | Decimal.D7 t => digits t ++ [7]
    | Decimal.D8 t => digits t ++ [8]
    | Decimal.D9 t => digits t ++ [9]
    end)).
  exists (digits d), (digits (Decimal.Little.succ d)),
    (Z.max (Zlength (digits d)) (Zlength (digits (Decimal.Little.succ d)))).
  split.
  - replace x with (Z.of_nat (Z.to_nat x)) by (rewrite Z2Nat.id by lia; reflexivity).
    apply decimal_rep_to_lu__solver_result. lia.
  - split.
    + replace (x + 1) with (Z.of_nat (S (Z.to_nat x))).
      2:{ rewrite Nat2Z.inj_succ, Z2Nat.id by lia. unfold Z.succ. lia. }
      unfold d, digits.
      apply decimal_rep_to_lu__solver_result. lia.
    + split.
      * reflexivity.
      * rewrite decimal_uint_diff_succ__solver_result.
        pose proof (decimal_carry_depth_bound__solver_result 9 d) as Hdepth.
        unfold d in Hdepth.
        specialize (Hdepth ltac:(
          rewrite decimal_uint_value_to_lu__solver_result, Z2Nat.id by lia;
          cbn [Z.pow]; lia)).
        pose proof (decimal_qsum_succ__solver_result d 10%nat Hdepth) as Hqs.
        unfold d in Hqs.
        rewrite decimal_uint_value_succ__solver_result,
                decimal_uint_value_to_lu__solver_result in Hqs.
        rewrite Z2Nat.id in Hqs by lia.
        rewrite !decimal_qsum_ten_as_sum_range__solver_result in Hqs by lia.
        exact Hqs.
Qed.
