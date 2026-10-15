Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition BeautifulParking (n : Z) (cars : list Z) : Prop :=
  Zlength cars = 2 * n - 2 /\
  Forall (fun c => 1 <= c <= 4) cars /\
  exists i make, 0 <= i /\ i + n <= Zlength cars /\
    (forall j, i <= j < i + n -> Znth j cars 0 = make) /\
    (i = 0 \/ Znth (i - 1) cars 0 <> make) /\
    (i + n = Zlength cars \/ Znth (i + n) cars 0 <> make).

Definition Pre (n : Z) : Prop :=
  3 <= n <= 30.

#[local] Instance finite_car_make : Finite (fun c : Z => 1 <= c < 5) :=
  finite_Z_range 1 5.

#[local] Instance finite_filling (n : Z) :
    Finite (fun cars : list Z =>
      Zlength cars = 2 * n - 2 /\ Forall (fun c => 1 <= c < 5) cars) :=
  Finite_bounded_lists (2 * n - 2) (fun c : Z => 1 <= c < 5).

Definition Spec (n out : Z) : Prop :=
  out = #(fun cars : list Z =>
    (Zlength cars = 2 * n - 2 /\ Forall (fun c => 1 <= c < 5) cars) /\
    BeautifulParking n cars).

Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Lemma ParkingColor__solver_result : Z -> Prop.
Proof. exact (fun x => 1 <= x < 5). Defined.
Lemma ParkingFilling__solver_result : Z -> list Z -> Prop.
Proof. exact (fun k xs =>
  Zlength xs = k /\ Forall ParkingColor__solver_result xs). Defined.
Lemma fold_ones_length__solver_result :
  forall {A : Type} (xs : list A),
    List.fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
      Z.of_nat (List.length xs).
Proof.
  intros A xs.
  induction xs as [|x xs IH]; [reflexivity|].
  change (1 + List.fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 xs =
    Z.of_nat (S (List.length xs))).
  rewrite IH, Nat2Z.inj_succ. lia.
Qed.
Lemma set_card_as_Zlength_enum__solver_result :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    @set_card A P FP = Z.of_nat (List.length (@enum A P FP)).
Proof.
  intros A P FP. unfold set_card, SumLib.Sum.sum.
  apply fold_ones_length__solver_result.
Qed.
Lemma Zrange_aux_length__solver_result :
  forall low m, List.length (Zrange_aux low m) = m.
Proof. intros low m. revert low. induction m; intros; simpl; congruence. Qed.
Lemma set_card_Z_range__solver_result :
  forall low high, low <= high ->
    @set_card Z (fun z => low <= z < high) (finite_Z_range low high) =
      high - low.
Proof.
  intros low high Hrange.
  rewrite set_card_as_Zlength_enum__solver_result.
  change (Z.of_nat (List.length (Zrange low high)) = high - low).
  unfold Zrange. rewrite Zrange_aux_length__solver_result, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma ParkingOther__solver_result : Z -> Z -> Z.
Proof. exact (fun make d => 1 + ((make - 1 + d) mod 4)). Defined.
Lemma ParkingOther_range__solver_result :
  forall make d,
    ParkingColor__solver_result make -> 1 <= d < 4 ->
    ParkingColor__solver_result (ParkingOther__solver_result make d) /\
    ParkingOther__solver_result make d <> make.
Proof.
  intros make d Hmake Hd.
  unfold ParkingColor__solver_result, ParkingOther__solver_result in *.
  pose proof (Z.mod_pos_bound (make - 1 + d) 4 ltac:(lia)) as Hmod.
  split; [lia|].
  intro Heq.
  pose proof (Z.mod_eq (make - 1 + d) 4 ltac:(lia)) as Hdiv.
  lia.
Qed.
Lemma ParkingOther_surj__solver_result :
  forall make other,
    ParkingColor__solver_result make -> ParkingColor__solver_result other ->
    other <> make ->
    exists d, 1 <= d < 4 /\ ParkingOther__solver_result make d = other.
Proof.
  intros make other Hmake Hother Hneq.
  unfold ParkingColor__solver_result in *.
  exists ((other - make) mod 4).
  assert (Hmcases : make = 1 \/ make = 2 \/ make = 3 \/ make = 4) by lia.
  assert (Hocases : other = 1 \/ other = 2 \/ other = 3 \/ other = 4) by lia.
  destruct Hmcases as [Hm|[Hm|[Hm|Hm]]]; subst make;
  destruct Hocases as [Ho|[Ho|[Ho|Ho]]]; subst other.
  all: try contradiction.
  all: split.
  all: try split.
  all: vm_compute; congruence.
Qed.
Lemma ParkingOther_inj__solver_result :
  forall make d1 d2,
    ParkingColor__solver_result make ->
    1 <= d1 < 4 -> 1 <= d2 < 4 ->
    ParkingOther__solver_result make d1 = ParkingOther__solver_result make d2 ->
    d1 = d2.
Proof.
  intros make d1 d2 Hmake Hd1 Hd2 Heq.
  unfold ParkingColor__solver_result in Hmake.
  assert (Hmcases : make = 1 \/ make = 2 \/ make = 3 \/ make = 4) by lia.
  assert (Hd1cases : d1 = 1 \/ d1 = 2 \/ d1 = 3) by lia.
  assert (Hd2cases : d2 = 1 \/ d2 = 2 \/ d2 = 3) by lia.
  destruct Hmcases as [Hm|[Hm|[Hm|Hm]]]; subst make;
  destruct Hd1cases as [H1|[H1|H1]]; subst d1;
  destruct Hd2cases as [H2|[H2|H2]]; subst d2;
    vm_compute in Heq; lia.
Qed.
Lemma ParkingEdgeRep__solver_result : Type.
Proof. exact (bool * (Z * (Z * list Z)))%type. Defined.
Lemma ParkingEdgePred__solver_result :
  Z -> ParkingEdgeRep__solver_result -> Prop.
Proof. exact (fun n r => True /\
  (ParkingColor__solver_result (fst (snd r)) /\
   ((1 <= fst (snd (snd r)) < 4) /\
    ParkingFilling__solver_result (n - 3) (snd (snd (snd r)))))). Defined.
Lemma ParkingInteriorRep__solver_result : Type.
Proof. exact (Z * (Z * (Z * (Z * list Z))))%type. Defined.
Lemma ParkingInteriorPred__solver_result :
  Z -> ParkingInteriorRep__solver_result -> Prop.
Proof. exact (fun n r => (0 <= fst r < n - 3) /\
  (ParkingColor__solver_result (fst (snd r)) /\
   ((1 <= fst (snd (snd r)) < 4) /\
    ((1 <= fst (snd (snd (snd r))) < 4) /\
     ParkingFilling__solver_result (n - 4) (snd (snd (snd (snd r)))))))). Defined.
Lemma ParkingRep__solver_result : Type.
Proof. exact (ParkingEdgeRep__solver_result + ParkingInteriorRep__solver_result)%type. Defined.
Lemma ParkingRepPred__solver_result : Z -> ParkingRep__solver_result -> Prop.
Proof. exact (fun n r => match r with
  | inl e => ParkingEdgePred__solver_result n e
  | inr i => ParkingInteriorPred__solver_result n i
  end). Defined.
Lemma finite_bool_true__solver_result : Finite (fun _ : bool => True).
Proof.
  refine {| enum := false :: true :: nil |}.
  - intros []; simpl; tauto.
  - constructor.
    + intros [H|[]]. discriminate.
    + constructor; [simpl; tauto|constructor].
Defined.
Lemma finite_sum_pred__solver_result
    {A B : Type} (P : A -> Prop) (Q : B -> Prop)
    `{Finite A P} `{Finite B Q} :
    Finite (fun s : A + B => match s with inl a => P a | inr b => Q b end).
Proof.
  refine {| enum := map inl (@enum A P _) ++ map inr (@enum B Q _) |}.
  - intros [a|b]; rewrite in_app_iff, !in_map_iff.
    + split.
      * intro Ha. left. exists a. split; [reflexivity|].
        apply (proj1 (enum_ok a)); exact Ha.
      * intros [[x [Heq Hx]]|[y [Heq Hy]]];
          [inversion Heq; subst; apply (proj2 (enum_ok a)); exact Hx|discriminate].
    + split.
      * intro Hb. right. exists b. split; [reflexivity|].
        apply (proj1 (enum_ok b)); exact Hb.
      * intros [[x [Heq Hx]]|[y [Heq Hy]]];
          [discriminate|inversion Heq; subst; apply (proj2 (enum_ok b)); exact Hy].
  - apply NoDup_app.
    + apply FinFun.Injective_map_NoDup; [intros x y H; injection H; auto|apply enum_nodup].
    + apply FinFun.Injective_map_NoDup; [intros x y H; injection H; auto|apply enum_nodup].
    + intros s Hleft Hright.
      apply in_map_iff in Hleft as [a [Heq _]].
      apply in_map_iff in Hright as [b [Heq' _]].
      subst s. discriminate.
Defined.
Lemma finite_parking_color__solver_result :
  Finite ParkingColor__solver_result.
Proof. exact (finite_Z_range 1 5). Defined.
Lemma finite_parking_d__solver_result :
  Finite (fun d : Z => 1 <= d < 4).
Proof. exact (finite_Z_range 1 4). Defined.
Lemma finite_parking_filling__solver_result (k : Z) :
  Finite (ParkingFilling__solver_result k).
Proof. exact (@Finite_bounded_lists Z k ParkingColor__solver_result
  finite_parking_color__solver_result). Defined.
Lemma finite_d_filling__solver_result (k : Z) :
  Finite (fun r : Z * list Z =>
    (1 <= fst r < 4) /\ ParkingFilling__solver_result k (snd r)).
Proof. exact (@Finite_prod Z (list Z) (fun d : Z => 1 <= d < 4)
  (ParkingFilling__solver_result k) finite_parking_d__solver_result
  (finite_parking_filling__solver_result k)). Defined.
Lemma finite_color_d_filling__solver_result (k : Z) :
  Finite (fun r : Z * (Z * list Z) =>
    ParkingColor__solver_result (fst r) /\
    ((1 <= fst (snd r) < 4) /\ ParkingFilling__solver_result k (snd (snd r)))).
Proof. exact (@Finite_prod Z (Z * list Z) ParkingColor__solver_result
    (fun r : Z * list Z =>
      (1 <= fst r < 4) /\ ParkingFilling__solver_result k (snd r))
    finite_parking_color__solver_result
    (finite_d_filling__solver_result k)). Defined.
Lemma finite_d_d_filling__solver_result (k : Z) :
  Finite (fun r : Z * (Z * list Z) =>
    (1 <= fst r < 4) /\
    ((1 <= fst (snd r) < 4) /\ ParkingFilling__solver_result k (snd (snd r)))).
Proof. exact (@Finite_prod Z (Z * list Z) (fun d : Z => 1 <= d < 4)
    (fun r : Z * list Z =>
      (1 <= fst r < 4) /\ ParkingFilling__solver_result k (snd r))
    finite_parking_d__solver_result
    (finite_d_filling__solver_result k)). Defined.
Lemma finite_color_d_d_filling__solver_result (k : Z) :
  Finite (fun r : Z * (Z * (Z * list Z)) =>
    ParkingColor__solver_result (fst r) /\
    ((1 <= fst (snd r) < 4) /\
     ((1 <= fst (snd (snd r)) < 4) /\
      ParkingFilling__solver_result k (snd (snd (snd r)))))).
Proof. exact (@Finite_prod Z (Z * (Z * list Z)) ParkingColor__solver_result
    (fun r : Z * (Z * list Z) =>
      (1 <= fst r < 4) /\
      ((1 <= fst (snd r) < 4) /\ ParkingFilling__solver_result k (snd (snd r))))
    finite_parking_color__solver_result
    (finite_d_d_filling__solver_result k)). Defined.
Lemma finite_edge_rep__solver_result (n : Z) :
  Finite (ParkingEdgePred__solver_result n).
Proof. exact (@Finite_prod bool (Z * (Z * list Z)) (fun _ : bool => True)
    (fun r : Z * (Z * list Z) =>
      ParkingColor__solver_result (fst r) /\
      ((1 <= fst (snd r) < 4) /\
       ParkingFilling__solver_result (n - 3) (snd (snd r))))
    finite_bool_true__solver_result
    (finite_color_d_filling__solver_result (n - 3))). Defined.
Lemma finite_interior_rep__solver_result (n : Z) :
  Finite (ParkingInteriorPred__solver_result n).
Proof. exact (@Finite_prod Z (Z * (Z * (Z * list Z)))
    (fun k : Z => 0 <= k < n - 3)
    (fun r : Z * (Z * (Z * list Z)) =>
      ParkingColor__solver_result (fst r) /\
      ((1 <= fst (snd r) < 4) /\
       ((1 <= fst (snd (snd r)) < 4) /\
        ParkingFilling__solver_result (n - 4) (snd (snd (snd r))))))
    (finite_Z_range 0 (n - 3))
    (finite_color_d_d_filling__solver_result (n - 4))). Defined.
Lemma finite_parking_rep__solver_result (n : Z) :
  Finite (ParkingRepPred__solver_result n).
Proof. exact (@finite_sum_pred__solver_result
    ParkingEdgeRep__solver_result ParkingInteriorRep__solver_result
    (ParkingEdgePred__solver_result n) (ParkingInteriorPred__solver_result n)
    (finite_edge_rep__solver_result n)
    (finite_interior_rep__solver_result n)). Defined.
Lemma set_card_bool_true__solver_result :
  @set_card bool (fun _ => True) finite_bool_true__solver_result = 2.
Proof. rewrite set_card_as_Zlength_enum__solver_result. reflexivity. Qed.
Lemma set_card_sum__solver_result :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q),
    @set_card (A + B)
      (fun s => match s with inl a => P a | inr b => Q b end)
      (@finite_sum_pred__solver_result A B P Q FP FQ) =
    @set_card A P FP + @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ. rewrite !set_card_as_Zlength_enum__solver_result.
  change (Z.of_nat (List.length
      (map inl (@enum A P FP) ++ map inr (@enum B Q FQ))) =
    Z.of_nat (List.length (@enum A P FP)) +
      Z.of_nat (List.length (@enum B Q FQ))).
  rewrite length_app, !length_map, Nat2Z.inj_add. reflexivity.
Qed.
Lemma set_card_bijection__solver_result :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q) (f : A -> B),
    (forall x, P x -> Q (f x)) ->
    (forall y, Q y -> exists x, P x /\ f x = y) ->
    (forall x y, P x -> P y -> f x = f y -> x = y) ->
    @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f Hmap Hsurj Hinj.
  rewrite !set_card_as_Zlength_enum__solver_result.
  f_equal.
  rewrite <- map_length with (f := f) (l := @enum A P FP).
  apply Permutation_length.
  apply NoDup_Permutation.
  - apply Injective_map_NoDup_in.
    + intros x y Hx Hy Hxy. apply Hinj.
      * apply (proj2 (@enum_ok A P FP x)); exact Hx.
      * apply (proj2 (@enum_ok A P FP y)); exact Hy.
      * exact Hxy.
    + exact (@enum_nodup A P FP).
  - exact (@enum_nodup B Q FQ).
  - intro y. rewrite in_map_iff, <- (@enum_ok B Q FQ y).
    split.
    + intros [x [<- Hx]]. apply Hmap.
      apply (proj2 (@enum_ok A P FP x)); exact Hx.
    + intro Hy. destruct (Hsurj y Hy) as [x [Hx Hxy]].
      exists x. split; [exact Hxy|].
      apply (proj1 (@enum_ok A P FP x)); exact Hx.
Qed.
Lemma set_card_product__solver_result :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
      (FP : Finite P) (FQ : Finite Q),
    @set_card (A * B) (fun p => P (fst p) /\ Q (snd p))
      (@Finite_prod A B P Q FP FQ) =
    @set_card A P FP * @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ.
  rewrite !set_card_as_Zlength_enum__solver_result.
  assert (Hprod : forall (xs : list A) (ys : list B),
    List.length (list_prod xs ys) =
      (List.length xs * List.length ys)%nat).
  { intros xs ys. induction xs as [|x xs IH]; simpl; [reflexivity|].
    rewrite app_length, length_map, IH. lia. }
  change (Z.of_nat (List.length
      (list_prod (@enum A P FP) (@enum B Q FQ))) =
    Z.of_nat (List.length (@enum A P FP)) *
      Z.of_nat (List.length (@enum B Q FQ))).
  rewrite Hprod, Nat2Z.inj_mul. reflexivity.
Qed.
Lemma length_flat_map_constant__solver_result :
  forall {A B : Type} (xs : list A) (f : A -> list B) k,
    (forall x, In x xs -> List.length (f x) = k) ->
    List.length (flat_map f xs) = (List.length xs * k)%nat.
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros f k Hf;
    [reflexivity|].
  change (List.length (f x ++ flat_map f xs) =
    (S (List.length xs) * k)%nat).
  rewrite length_app, (Hf x (or_introl eq_refl)).
  rewrite (IH f k) by (intros y Hy; apply Hf; right; exact Hy).
  simpl. lia.
Qed.
Lemma all_lists_length__solver_result :
  forall {A : Type} (alphabet : list A) k,
    List.length (all_lists k alphabet) =
      Nat.pow (List.length alphabet) k.
Proof.
  intros A alphabet k. revert alphabet.
  induction k as [|k IH]; intro alphabet; [reflexivity|].
  change (List.length
    (flat_map (fun x => map (cons x) (all_lists k alphabet)) alphabet) =
    (List.length alphabet * Nat.pow (List.length alphabet) k)%nat).
  apply length_flat_map_constant__solver_result.
  intros x Hx. rewrite length_map, IH. reflexivity.
Qed.
Lemma set_card_filling__solver_result :
  forall k, 0 <= k ->
    @set_card (list Z) (ParkingFilling__solver_result k)
      (Finite_bounded_lists k ParkingColor__solver_result) = 4 ^ k.
Proof.
  intros k Hk.
  rewrite set_card_as_Zlength_enum__solver_result.
  unfold ParkingFilling__solver_result, ParkingColor__solver_result.
  change (Z.of_nat (List.length
    (if Z.ltb k 0 then nil else all_lists (Z.to_nat k) (Zrange 1 5))) =
    4 ^ k).
  destruct (Z.ltb k 0) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. lia.
  -
  rewrite all_lists_length__solver_result.
  assert (Hlen : List.length (Zrange 1 5) = 4%nat) by reflexivity.
  rewrite Hlen, Nat2Z.inj_pow, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma set_card_color__solver_result :
  @set_card Z ParkingColor__solver_result finite_parking_color__solver_result = 4.
Proof.
  unfold ParkingColor__solver_result, finite_parking_color__solver_result.
  apply set_card_Z_range__solver_result. lia.
Qed.
Lemma set_card_d__solver_result :
  @set_card Z (fun d => 1 <= d < 4) finite_parking_d__solver_result = 3.
Proof. apply set_card_Z_range__solver_result. lia. Qed.
Lemma set_card_d_filling__solver_result :
  forall k, 0 <= k ->
    @set_card (Z * list Z)
      (fun r => (1 <= fst r < 4) /\ ParkingFilling__solver_result k (snd r))
      (finite_d_filling__solver_result k) = 3 * 4 ^ k.
Proof.
  intros k Hk.
  unfold finite_d_filling__solver_result.
  rewrite (@set_card_product__solver_result Z (list Z)
    (fun d : Z => 1 <= d < 4) (ParkingFilling__solver_result k)
    finite_parking_d__solver_result (finite_parking_filling__solver_result k)).
  rewrite set_card_d__solver_result.
  rewrite set_card_filling__solver_result by lia. reflexivity.
Qed.
Lemma set_card_color_d_filling__solver_result :
  forall k, 0 <= k ->
    @set_card (Z * (Z * list Z))
      (fun r => ParkingColor__solver_result (fst r) /\
        ((1 <= fst (snd r) < 4) /\ ParkingFilling__solver_result k (snd (snd r))))
      (finite_color_d_filling__solver_result k) = 12 * 4 ^ k.
Proof.
  intros k Hk.
  unfold finite_color_d_filling__solver_result.
  rewrite (@set_card_product__solver_result Z (Z * list Z)
    ParkingColor__solver_result
    (fun q => (1 <= fst q < 4) /\ ParkingFilling__solver_result k (snd q))
    finite_parking_color__solver_result (finite_d_filling__solver_result k)).
  rewrite set_card_color__solver_result.
  rewrite set_card_d_filling__solver_result by lia. ring.
Qed.
Lemma set_card_d_d_filling__solver_result :
  forall k, 0 <= k ->
    @set_card (Z * (Z * list Z))
      (fun r => (1 <= fst r < 4) /\
        ((1 <= fst (snd r) < 4) /\ ParkingFilling__solver_result k (snd (snd r))))
      (finite_d_d_filling__solver_result k) = 9 * 4 ^ k.
Proof.
  intros k Hk.
  unfold finite_d_d_filling__solver_result.
  rewrite (@set_card_product__solver_result Z (Z * list Z)
    (fun d : Z => 1 <= d < 4)
    (fun q => (1 <= fst q < 4) /\ ParkingFilling__solver_result k (snd q))
    finite_parking_d__solver_result (finite_d_filling__solver_result k)).
  rewrite set_card_d__solver_result.
  rewrite set_card_d_filling__solver_result by lia. ring.
Qed.
Lemma set_card_color_d_d_filling__solver_result :
  forall k, 0 <= k ->
    @set_card (Z * (Z * (Z * list Z)))
      (fun r => ParkingColor__solver_result (fst r) /\
        ((1 <= fst (snd r) < 4) /\
         ((1 <= fst (snd (snd r)) < 4) /\
          ParkingFilling__solver_result k (snd (snd (snd r))))))
      (finite_color_d_d_filling__solver_result k) = 36 * 4 ^ k.
Proof.
  intros k Hk.
  unfold finite_color_d_d_filling__solver_result.
  rewrite (@set_card_product__solver_result Z (Z * (Z * list Z))
    ParkingColor__solver_result
    (fun q => (1 <= fst q < 4) /\
      ((1 <= fst (snd q) < 4) /\ ParkingFilling__solver_result k (snd (snd q))))
    finite_parking_color__solver_result (finite_d_d_filling__solver_result k)).
  rewrite set_card_color__solver_result.
  rewrite set_card_d_d_filling__solver_result by lia. ring.
Qed.
Lemma set_card_edge_rep__solver_result :
  forall n, 3 <= n ->
    @set_card ParkingEdgeRep__solver_result
      (ParkingEdgePred__solver_result n) (finite_edge_rep__solver_result n) =
      24 * 4 ^ (n - 3).
Proof.
  intros n Hn.
  unfold finite_edge_rep__solver_result, ParkingEdgePred__solver_result,
    ParkingEdgeRep__solver_result.
  rewrite (@set_card_product__solver_result bool (Z * (Z * list Z))
    (fun _ => True)
    (fun q => ParkingColor__solver_result (fst q) /\
      ((1 <= fst (snd q) < 4) /\
       ParkingFilling__solver_result (n - 3) (snd (snd q))))
    finite_bool_true__solver_result
    (finite_color_d_filling__solver_result (n - 3))).
  rewrite set_card_bool_true__solver_result.
  rewrite set_card_color_d_filling__solver_result by lia.
  ring.
Qed.
Lemma set_card_interior_rep__solver_result :
  forall n, 4 <= n ->
    @set_card ParkingInteriorRep__solver_result
      (ParkingInteriorPred__solver_result n) (finite_interior_rep__solver_result n) =
      (n - 3) * 36 * 4 ^ (n - 4).
Proof.
  intros n Hn.
  unfold finite_interior_rep__solver_result, ParkingInteriorPred__solver_result,
    ParkingInteriorRep__solver_result.
  rewrite (@set_card_product__solver_result Z (Z * (Z * (Z * list Z)))
    (fun k => 0 <= k < n - 3)
    (fun q => ParkingColor__solver_result (fst q) /\
      ((1 <= fst (snd q) < 4) /\
       ((1 <= fst (snd (snd q)) < 4) /\
        ParkingFilling__solver_result (n - 4) (snd (snd (snd q))))))
    (finite_Z_range 0 (n - 3))
    (finite_color_d_d_filling__solver_result (n - 4))).
  rewrite set_card_Z_range__solver_result by lia.
  rewrite set_card_color_d_d_filling__solver_result by lia.
  ring.
Qed.
Lemma set_card_interior_rep_n3__solver_result :
  @set_card ParkingInteriorRep__solver_result
    (ParkingInteriorPred__solver_result 3)
    (finite_interior_rep__solver_result 3) = 0.
Proof.
  unfold finite_interior_rep__solver_result, ParkingInteriorPred__solver_result,
    ParkingInteriorRep__solver_result.
  change (@set_card (Z * (Z * (Z * (Z * list Z))))
    (fun p => (0 <= fst p < 0) /\
      (ParkingColor__solver_result (fst (snd p)) /\
       ((1 <= fst (snd (snd p)) < 4) /\
        ((1 <= fst (snd (snd (snd p))) < 4) /\
         ParkingFilling__solver_result (-1) (snd (snd (snd (snd p))))))))
    (@Finite_prod Z (Z * (Z * (Z * list Z)))
      (fun k => 0 <= k < 0)
      (fun q => ParkingColor__solver_result (fst q) /\
        ((1 <= fst (snd q) < 4) /\
         ((1 <= fst (snd (snd q)) < 4) /\
          ParkingFilling__solver_result (-1) (snd (snd (snd q))))))
      (finite_Z_range 0 0)
      (finite_color_d_d_filling__solver_result (-1))) = 0).
  rewrite (@set_card_product__solver_result Z (Z * (Z * (Z * list Z)))
    (fun k => 0 <= k < 0)
    (fun q => ParkingColor__solver_result (fst q) /\
      ((1 <= fst (snd q) < 4) /\
       ((1 <= fst (snd (snd q)) < 4) /\
        ParkingFilling__solver_result (-1) (snd (snd (snd q))))))
    (finite_Z_range 0 0)
    (finite_color_d_d_filling__solver_result (-1))).
  rewrite set_card_Z_range__solver_result by lia.
  ring.
Qed.
Lemma set_card_parking_rep__solver_result :
  forall n, 3 <= n ->
    @set_card ParkingRep__solver_result (ParkingRepPred__solver_result n)
      (finite_parking_rep__solver_result n) =
    24 * 4 ^ (n - 3) + (n - 3) * 36 * 4 ^ (n - 4).
Proof.
  intros n Hn.
  unfold finite_parking_rep__solver_result, ParkingRepPred__solver_result,
    ParkingRep__solver_result.
  rewrite (@set_card_sum__solver_result ParkingEdgeRep__solver_result
    ParkingInteriorRep__solver_result (ParkingEdgePred__solver_result n)
    (ParkingInteriorPred__solver_result n) (finite_edge_rep__solver_result n)
    (finite_interior_rep__solver_result n)).
  rewrite set_card_edge_rep__solver_result by lia.
  destruct (Z.eq_dec n 3) as [->|Hneq].
  - rewrite set_card_interior_rep_n3__solver_result. vm_compute. ring.
  - rewrite set_card_interior_rep__solver_result by lia. ring.
Qed.
Lemma Zlength_repeat_to_nat__solver_result :
  forall (x : Z) n, 0 <= n -> Zlength (repeat x (Z.to_nat n)) = n.
Proof. intros. rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. reflexivity. Qed.
Lemma Forall_repeat__solver_result :
  forall {A : Type} (P : A -> Prop) x m,
    P x -> Forall P (repeat x m).
Proof. intros A P x m H. induction m; simpl; constructor; auto. Qed.
Lemma Znth_app_left__solver_result :
  forall (l1 l2 : list Z) i d,
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 i d Hi. unfold Znth.
  rewrite app_nth1; [reflexivity|]. rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Znth_app_right__solver_result :
  forall (l1 l2 : list Z) i d,
    Zlength l1 <= i ->
    Znth i (l1 ++ l2) d = Znth (i - Zlength l1) l2 d.
Proof.
  intros l1 l2 i d Hi. unfold Znth.
  rewrite app_nth2 by (rewrite Zlength_correct in Hi; lia).
  f_equal. rewrite Zlength_correct in *. lia.
Qed.
Lemma Forall_sublist__solver_result :
  forall (P : Z -> Prop) cars lo hi,
    Forall P cars -> 0 <= lo <= hi -> hi <= Zlength cars ->
    Forall P (sublist lo hi cars).
Proof.
  intros P cars lo hi Hall Hlo Hhi.
  apply (proj2 (Forall_Znth P 0 (sublist lo hi cars))).
  intros j Hj.
  rewrite Zlength_sublist in Hj by lia.
  rewrite Znth_sublist by lia.
  apply (proj1 (Forall_Znth P 0 cars)); [exact Hall|lia].
Qed.
Lemma block_sublist_repeat__solver_result :
  forall cars i n make,
    0 <= i -> 0 <= n -> i + n <= Zlength cars ->
    (forall j, i <= j < i + n -> Znth j cars 0 = make) ->
    sublist i (i + n) cars = repeat make (Z.to_nat n).
Proof.
  intros cars i n make Hi Hn Hbound Hblock.
  apply (proj2 (list_eq_ext _ _ 0)). split.
  - rewrite Zlength_sublist by lia.
    rewrite Zlength_repeat_to_nat__solver_result by lia. lia.
  - intros j Hj.
    rewrite Zlength_sublist in Hj by lia.
    rewrite Znth_sublist by lia.
    rewrite Znth_repeat_lt by (rewrite Z2Nat.id by lia; lia).
    apply Hblock. lia.
Qed.
Lemma ParkingEdgeCars__solver_result :
  Z -> ParkingEdgeRep__solver_result -> list Z.
Proof. exact (fun n r =>
  let '(side, (make, (d, free))) := r in
  let other := ParkingOther__solver_result make d in
  if side
  then free ++ (other :: nil) ++ repeat make (Z.to_nat n)
  else repeat make (Z.to_nat n) ++ other :: free). Defined.
Lemma ParkingInteriorCars__solver_result :
  Z -> ParkingInteriorRep__solver_result -> list Z.
Proof. exact (fun n r =>
  let '(k, (make, (dl, (dr, free)))) := r in
  sublist 0 k free ++ (ParkingOther__solver_result make dl :: nil) ++
  repeat make (Z.to_nat n) ++ (ParkingOther__solver_result make dr :: nil) ++
  sublist k (n - 4) free). Defined.
Lemma ParkingCars__solver_result : Z -> ParkingRep__solver_result -> list Z.
Proof. exact (fun n r => match r with
  | inl e => ParkingEdgeCars__solver_result n e
  | inr i => ParkingInteriorCars__solver_result n i
  end). Defined.
Lemma constant_block_in_app__solver_result :
  forall pre post make n i,
    0 <= n -> Zlength pre = i ->
    forall j, i <= j < i + n ->
      Znth j (pre ++ repeat make (Z.to_nat n) ++ post) 0 = make.
Proof.
  intros pre post make n i Hn Hpre j Hj.
  rewrite Znth_app_right__solver_result by lia.
  rewrite Znth_app_left__solver_result.
  - rewrite Znth_repeat_lt by (rewrite Z2Nat.id by lia; lia). reflexivity.
  - rewrite Zlength_repeat_to_nat__solver_result by lia. lia.
Qed.
Lemma ParkingEdgeCars_valid__solver_result :
  forall n r, 3 <= n -> ParkingEdgePred__solver_result n r ->
    BeautifulParking n (ParkingEdgeCars__solver_result n r).
Proof.
  intros n [side [make [d free]]] Hn [_ [Hmake [Hd [Hfree Hallfree]]]].
  cbn in Hmake, Hd, Hfree, Hallfree.
  pose proof (ParkingOther_range__solver_result make d Hmake Hd) as [Hother Hneq].
  unfold BeautifulParking, ParkingEdgeCars__solver_result. destruct side.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil,
      Zlength_repeat_to_nat__solver_result by lia.
    repeat split; try lia.
    + apply Forall_app. split.
      * eapply Forall_impl; [|exact Hallfree].
        intros x Hx. unfold ParkingColor__solver_result in Hx. lia.
      * apply Forall_app. split.
        -- constructor; [unfold ParkingColor__solver_result in Hother; lia|constructor].
        -- apply Forall_repeat__solver_result.
           unfold ParkingColor__solver_result in Hmake. lia.
    + exists (n - 2), make. repeat split; try lia.
      * intros j Hj.
        rewrite app_assoc.
        rewrite <- (app_nil_r (repeat make (Z.to_nat n))).
        eapply constant_block_in_app__solver_result with (n := n) (i := n - 2);
          [lia|rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|exact Hj].
      * right.
        rewrite Znth_app_right__solver_result by lia.
        replace (n - 2 - 1 - Zlength free) with 0 by lia.
        cbn. exact Hneq.
  - rewrite !Zlength_app, !Zlength_cons,
      Zlength_repeat_to_nat__solver_result by lia.
    repeat split; try lia.
    + apply Forall_app. split.
      * apply Forall_repeat__solver_result.
        unfold ParkingColor__solver_result in Hmake. lia.
      * constructor; [unfold ParkingColor__solver_result in Hother; lia|].
        eapply Forall_impl; [|exact Hallfree].
        intros x Hx. unfold ParkingColor__solver_result in Hx. lia.
    + exists 0, make. repeat split; try lia.
      * intros j Hj.
        change (Znth j
          (nil ++ repeat make (Z.to_nat n) ++
           ParkingOther__solver_result make d :: free) 0 = make).
        eapply constant_block_in_app__solver_result with (n := n) (i := 0);
          [lia|rewrite Zlength_nil; lia|exact Hj].
      * right.
        rewrite Znth_app_right__solver_result by
          (rewrite Zlength_repeat_to_nat__solver_result by lia; lia).
        rewrite Zlength_repeat_to_nat__solver_result by lia.
        rewrite Z.sub_diag. cbn. exact Hneq.
Qed.
Lemma ParkingInteriorCars_valid__solver_result :
  forall n r, 3 <= n -> ParkingInteriorPred__solver_result n r ->
    BeautifulParking n (ParkingInteriorCars__solver_result n r).
Proof.
  intros n [k [make [dl [dr free]]]] Hn
    [Hk [Hmake [Hdl [Hdr [Hfree Hallfree]]]]].
  cbn in Hk, Hmake, Hdl, Hdr, Hfree, Hallfree.
  pose proof (ParkingOther_range__solver_result make dl Hmake Hdl)
    as [Hleft Hleftneq].
  pose proof (ParkingOther_range__solver_result make dr Hmake Hdr)
    as [Hright Hrightneq].
  unfold BeautifulParking, ParkingInteriorCars__solver_result.
  assert (Hsub1 : Zlength (sublist 0 k free) = k).
  { rewrite Zlength_sublist by lia. lia. }
  assert (Hsub2 : Zlength (sublist k (n - 4) free) = n - 4 - k).
  { rewrite Zlength_sublist by lia. lia. }
  rewrite !Zlength_app, !Zlength_cons, Zlength_nil,
    Zlength_repeat_to_nat__solver_result by lia.
  repeat split; try lia.
  - apply Forall_app. split.
    + eapply Forall_impl; [|eapply Forall_sublist__solver_result; eauto; lia].
      intros x Hx. unfold ParkingColor__solver_result in Hx. lia.
    + apply Forall_app. split.
      * constructor; [unfold ParkingColor__solver_result in Hleft; lia|constructor].
      * apply Forall_app. split.
        -- apply Forall_repeat__solver_result.
           unfold ParkingColor__solver_result in Hmake. lia.
        -- apply Forall_app. split.
           ++ constructor; [unfold ParkingColor__solver_result in Hright; lia|constructor].
           ++ eapply Forall_impl;
                [|eapply Forall_sublist__solver_result; eauto; lia].
              intros x Hx. unfold ParkingColor__solver_result in Hx. lia.
  - exists (k + 1), make. repeat split; try lia.
    + intros j Hj.
      rewrite app_assoc.
      eapply constant_block_in_app__solver_result with
        (pre := sublist 0 k free ++ (ParkingOther__solver_result make dl :: nil))
        (post := (ParkingOther__solver_result make dr :: nil) ++
          sublist k (n - 4) free) (n := n) (i := k + 1);
        [lia|rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|exact Hj].
    + right.
      rewrite Znth_app_right__solver_result by lia.
      replace (k + 1 - 1 - Zlength (sublist 0 k free)) with 0 by lia.
      cbn. exact Hleftneq.
    + right.
      rewrite app_assoc.
      set (pre := sublist 0 k free ++
        (ParkingOther__solver_result make dl :: nil)).
      assert (Hpre : Zlength pre = k + 1).
      { unfold pre. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      change (Znth (k + 1 + n)
        (pre ++ repeat make (Z.to_nat n) ++
         (ParkingOther__solver_result make dr :: nil) ++ sublist k (n - 4) free) 0
        <> make).
      rewrite Znth_app_right__solver_result by lia.
      rewrite Hpre.
      replace (k + 1 + n - (k + 1)) with n by lia.
      rewrite Znth_app_right__solver_result by
        (rewrite Zlength_repeat_to_nat__solver_result by lia; lia).
      rewrite Zlength_repeat_to_nat__solver_result by lia.
      rewrite Z.sub_diag.
      cbn. exact Hrightneq.
Qed.
Lemma ParkingCars_valid__solver_result :
  forall n r, 3 <= n -> ParkingRepPred__solver_result n r ->
    BeautifulParking n (ParkingCars__solver_result n r).
Proof.
  intros n [e|i] Hn Hr; simpl.
  - apply ParkingEdgeCars_valid__solver_result; assumption.
  - apply ParkingInteriorCars_valid__solver_result; assumption.
Qed.
Lemma ParkingBlock__solver_result : Z -> list Z -> Z -> Z -> Prop.
Proof. exact (fun n cars i make =>
  0 <= i /\ i + n <= Zlength cars /\
  (forall j, i <= j < i + n -> Znth j cars 0 = make) /\
  (i = 0 \/ Znth (i - 1) cars 0 <> make) /\
  (i + n = Zlength cars \/ Znth (i + n) cars 0 <> make)). Defined.
Lemma BeautifulParking_block_unique__solver_result :
  forall n cars i make k make',
    3 <= n -> Zlength cars = 2 * n - 2 ->
    ParkingBlock__solver_result n cars i make ->
    ParkingBlock__solver_result n cars k make' ->
    i = k /\ make = make'.
Proof.
  intros n cars i make k make' Hn Hlen
    [Hi [Hiend [Hiblock [Hileft Hiright]]]]
    [Hk [Hkend [Hkblock [Hkleft Hkright]]]].
  assert (Hik : i = k).
  {
    destruct (Z.lt_trichotomy i k) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
    - assert (Hoverlap : k < i + n) by lia.
      assert (Hmake : make = make').
      { rewrite <- (Hiblock k ltac:(lia)), <- (Hkblock k ltac:(lia)).
        reflexivity. }
      destruct Hkleft as [Hkzero|Hkneq]; [lia|].
      exfalso. apply Hkneq. rewrite <- Hmake.
      apply Hiblock. lia.
    - assert (Hoverlap : i < k + n) by lia.
      assert (Hmake : make = make').
      { rewrite <- (Hiblock i ltac:(lia)), <- (Hkblock i ltac:(lia)).
        reflexivity. }
      destruct Hileft as [Hizero|Hineq]; [lia|].
      exfalso. apply Hineq. rewrite Hmake.
      apply Hkblock. lia.
  }
  subst k. split; [reflexivity|].
  rewrite <- (Hiblock i ltac:(lia)), <- (Hkblock i ltac:(lia)).
  reflexivity.
Qed.
Lemma parking_decompose_left_edge__solver_result :
  forall n cars make,
    3 <= n -> Zlength cars = 2 * n - 2 ->
    (forall j, 0 <= j < n -> Znth j cars 0 = make) ->
    cars = repeat make (Z.to_nat n) ++
      Znth n cars 0 :: sublist (n + 1) (Zlength cars) cars.
Proof.
  intros n cars make Hn Hlen Hblock.
  pose proof (Zlength_nonneg cars) as Hcarslen.
  rewrite <- (sublist_self cars (Zlength cars) eq_refl) at 1.
  rewrite (sublist_split 0 (Zlength cars) n) by lia.
  assert (Hrep : sublist 0 n cars = repeat make (Z.to_nat n)).
  { replace n with (0 + n) by lia.
    eapply block_sublist_repeat__solver_result; try lia.
    intros j Hj. apply Hblock. lia. }
  rewrite Hrep.
  rewrite (sublist_split n (Zlength cars) (n + 1)) by lia.
  rewrite (sublist_single 0 n cars) by lia. reflexivity.
Qed.
Lemma parking_decompose_right_edge__solver_result :
  forall n cars make,
    3 <= n -> Zlength cars = 2 * n - 2 ->
    (forall j, n - 2 <= j < n - 2 + n -> Znth j cars 0 = make) ->
    cars = sublist 0 (n - 3) cars ++ Znth (n - 3) cars 0 ::
      repeat make (Z.to_nat n).
Proof.
  intros n cars make Hn Hlen Hblock.
  pose proof (Zlength_nonneg cars) as Hcarslen.
  rewrite <- (sublist_self cars (Zlength cars) eq_refl) at 1.
  rewrite (sublist_split 0 (Zlength cars) (n - 2)) by lia.
  rewrite (sublist_split 0 (n - 2) (n - 3)) by lia.
  assert (Hsingle : sublist (n - 3) (n - 2) cars =
    (Znth (n - 3) cars 0 :: nil)).
  { replace (n - 2) with (n - 3 + 1) by lia.
    apply sublist_single. lia. }
  rewrite Hsingle.
  assert (Hrep : sublist (n - 2) (Zlength cars) cars =
    repeat make (Z.to_nat n)).
  { replace (Zlength cars) with (n - 2 + n) by lia.
    eapply block_sublist_repeat__solver_result; try lia.
    intros j Hj. apply Hblock. lia. }
  rewrite Hrep.
  rewrite <- app_assoc. reflexivity.
Qed.
Lemma parking_decompose_interior__solver_result :
  forall n cars i make,
    3 <= n -> Zlength cars = 2 * n - 2 ->
    1 <= i -> i < n - 2 ->
    (forall j, i <= j < i + n -> Znth j cars 0 = make) ->
    cars = sublist 0 (i - 1) cars ++ (Znth (i - 1) cars 0 :: nil) ++
      repeat make (Z.to_nat n) ++ (Znth (i + n) cars 0 :: nil) ++
      sublist (i + n + 1) (Zlength cars) cars.
Proof.
  intros n cars i make Hn Hlen Hi Hilim Hblock.
  pose proof (Zlength_nonneg cars) as Hcarslen.
  rewrite <- (sublist_self cars (Zlength cars) eq_refl) at 1.
  rewrite (sublist_split 0 (Zlength cars) i) by lia.
  rewrite (sublist_split 0 i (i - 1)) by lia.
  assert (Hsingle_left : sublist (i - 1) i cars =
    (Znth (i - 1) cars 0 :: nil)).
  { pose proof (sublist_single 0 (i - 1) cars ltac:(lia)) as Hsingle.
    replace (i - 1 + 1) with i in Hsingle by lia. exact Hsingle. }
  rewrite Hsingle_left.
  rewrite (sublist_split i (Zlength cars) (i + n)) by lia.
  assert (Hrep : sublist i (i + n) cars = repeat make (Z.to_nat n)).
  { eapply block_sublist_repeat__solver_result; try lia.
    intros j Hj. apply Hblock. lia. }
  rewrite Hrep.
  rewrite (sublist_split (i + n) (Zlength cars) (i + n + 1)) by lia.
  rewrite (sublist_single 0 (i + n) cars) by lia.
  repeat rewrite <- app_assoc. reflexivity.
Qed.
Lemma ParkingValidPred__solver_result : Z -> list Z -> Prop.
Proof. exact (fun n cars => (Zlength cars = 2 * n - 2 /\
   Forall ParkingColor__solver_result cars) /\ BeautifulParking n cars). Defined.
Lemma ParkingCars_surjective__solver_result :
  forall n, 3 <= n -> forall cars,
    ParkingValidPred__solver_result n cars ->
    exists r, ParkingRepPred__solver_result n r /\
      ParkingCars__solver_result n r = cars.
Proof.
  intros n Hn cars [[Hlen Hcolors]
    [Hlen' [Hbeautcolors [i [make [Hi [Hiend
      [Hblock [Hleft Hright]]]]]]]]].
  assert (Hmake : ParkingColor__solver_result make).
  { unfold ParkingColor__solver_result.
    rewrite <- (Hblock i ltac:(lia)).
    apply (proj1 (Forall_Znth ParkingColor__solver_result 0 cars));
      [exact Hcolors|lia]. }
  destruct (Z.eq_dec i 0) as [Hi0|Hi0].
  - subst i.
    assert (Hotherneq : Znth n cars 0 <> make).
    { destruct Hright as [Heq|Hneq]; [lia|exact Hneq]. }
    assert (Hothercolor : ParkingColor__solver_result (Znth n cars 0)).
    { apply (proj1 (Forall_Znth ParkingColor__solver_result 0 cars));
        [exact Hcolors|lia]. }
    destruct (ParkingOther_surj__solver_result make (Znth n cars 0)
      Hmake Hothercolor Hotherneq) as [d [Hd Hdother]].
    assert (Hfill : ParkingFilling__solver_result (n - 3)
      (sublist (n + 1) (Zlength cars) cars)).
    { unfold ParkingFilling__solver_result. split.
      - rewrite Zlength_sublist by lia. lia.
      - eapply Forall_sublist__solver_result; eauto; lia. }
    exists (inl (false, (make, (d,
      sublist (n + 1) (Zlength cars) cars)))). split.
    + unfold ParkingRepPred__solver_result, ParkingEdgePred__solver_result.
      cbn. split; [trivial|]. split; [exact Hmake|].
      split; [exact Hd|exact Hfill].
    + unfold ParkingCars__solver_result, ParkingEdgeCars__solver_result.
      cbn -[ParkingOther__solver_result]. rewrite Hdother.
      symmetry. apply parking_decompose_left_edge__solver_result; try assumption.
  - destruct (Z.eq_dec i (n - 2)) as [Hirightedge|Hirightedge].
    + subst i.
      assert (Hotherneq : Znth (n - 3) cars 0 <> make).
      { destruct Hleft as [Heq|Hneq]; [lia|].
        replace (n - 3) with (n - 2 - 1) by lia. exact Hneq. }
      assert (Hothercolor : ParkingColor__solver_result (Znth (n - 3) cars 0)).
      { apply (proj1 (Forall_Znth ParkingColor__solver_result 0 cars));
          [exact Hcolors|lia]. }
      destruct (ParkingOther_surj__solver_result make (Znth (n - 3) cars 0)
        Hmake Hothercolor Hotherneq) as [d [Hd Hdother]].
      assert (Hfill : ParkingFilling__solver_result (n - 3)
        (sublist 0 (n - 3) cars)).
      { unfold ParkingFilling__solver_result. split.
        - rewrite Zlength_sublist by lia. lia.
        - eapply Forall_sublist__solver_result; eauto; lia. }
      exists (inl (true, (make, (d, sublist 0 (n - 3) cars)))). split.
      * unfold ParkingRepPred__solver_result, ParkingEdgePred__solver_result.
        cbn. split; [trivial|]. split; [exact Hmake|].
        split; [exact Hd|exact Hfill].
      * unfold ParkingCars__solver_result, ParkingEdgeCars__solver_result.
        cbn -[ParkingOther__solver_result]. rewrite Hdother.
        symmetry. apply parking_decompose_right_edge__solver_result; try assumption.
    + assert (Hiinterior : 1 <= i < n - 2) by lia.
      assert (Hleftneq : Znth (i - 1) cars 0 <> make).
      { destruct Hleft as [Heq|Hneq]; [lia|exact Hneq]. }
      assert (Hrightneq : Znth (i + n) cars 0 <> make).
      { destruct Hright as [Heq|Hneq]; [lia|exact Hneq]. }
      assert (Hleftcolor : ParkingColor__solver_result (Znth (i - 1) cars 0)).
      { apply (proj1 (Forall_Znth ParkingColor__solver_result 0 cars));
          [exact Hcolors|lia]. }
      assert (Hrightcolor : ParkingColor__solver_result (Znth (i + n) cars 0)).
      { apply (proj1 (Forall_Znth ParkingColor__solver_result 0 cars));
          [exact Hcolors|lia]. }
      destruct (ParkingOther_surj__solver_result make (Znth (i - 1) cars 0)
        Hmake Hleftcolor Hleftneq) as [dl [Hdl Hdlother]].
      destruct (ParkingOther_surj__solver_result make (Znth (i + n) cars 0)
        Hmake Hrightcolor Hrightneq) as [dr [Hdr Hdrother]].
      set (leftfree := sublist 0 (i - 1) cars).
      set (rightfree := sublist (i + n + 1) (Zlength cars) cars).
      set (free := leftfree ++ rightfree).
      assert (Hleftlen : Zlength leftfree = i - 1).
      { unfold leftfree. rewrite Zlength_sublist by lia. lia. }
      assert (Hrightlen : Zlength rightfree = n - i - 3).
      { unfold rightfree. rewrite Zlength_sublist by lia. lia. }
      assert (Hfreelen : Zlength free = n - 4).
      { unfold free. rewrite Zlength_app. lia. }
      assert (Hfreecolors : Forall ParkingColor__solver_result free).
      { unfold free. apply Forall_app. split;
          eapply Forall_sublist__solver_result; eauto; lia. }
      assert (Hfreeleft : sublist 0 (i - 1) free = leftfree).
      { unfold free. rewrite <- Hleftlen. apply sublist_app_exact1. }
      assert (Hfreeright : sublist (i - 1) (n - 4) free = rightfree).
      { unfold free.
        rewrite (sublist_split_app_r (i - 1) (n - 4) (i - 1)
          leftfree rightfree) by lia.
        replace (i - 1 - (i - 1)) with 0 by lia.
        replace (n - 4 - (i - 1)) with (Zlength rightfree) by lia.
        apply sublist_self. reflexivity. }
      exists (inr (i - 1, (make, (dl, (dr, free))))). split.
      * unfold ParkingRepPred__solver_result, ParkingInteriorPred__solver_result.
        cbn. split; [lia|]. split; [exact Hmake|]. split; [exact Hdl|].
        split; [exact Hdr|]. split; [exact Hfreelen|exact Hfreecolors].
      * unfold ParkingCars__solver_result, ParkingInteriorCars__solver_result.
        cbn -[ParkingOther__solver_result sublist].
        rewrite Hfreeleft, Hfreeright, Hdlother, Hdrother.
        symmetry. apply parking_decompose_interior__solver_result; try assumption.
        all: try lia.
        all: try solve [intros j Hj; apply Hblock; lia].
Qed.
Lemma ParkingStart__solver_result : Z -> ParkingRep__solver_result -> Z.
Proof. exact (fun n r => match r with
  | inl (side, _) => if side then n - 2 else 0
  | inr (k, _) => k + 1
  end). Defined.
Lemma ParkingMake__solver_result : ParkingRep__solver_result -> Z.
Proof. exact (fun r => match r with
  | inl (_, (make, _)) => make
  | inr (_, (make, _)) => make
  end). Defined.
Lemma ParkingCars_canonical_block__solver_result :
  forall n r, 3 <= n -> ParkingRepPred__solver_result n r ->
    ParkingBlock__solver_result n (ParkingCars__solver_result n r)
      (ParkingStart__solver_result n r) (ParkingMake__solver_result r).
Proof.
  intros n [[side [make [d free]]]|[k [make [dl [dr free]]]]] Hn Hr.
  - unfold ParkingRepPred__solver_result, ParkingEdgePred__solver_result in Hr.
    destruct Hr as [_ [Hmake [Hd [Hfree Hallfree]]]].
    cbn in Hmake, Hd, Hfree, Hallfree.
    pose proof (ParkingOther_range__solver_result make d Hmake Hd) as [_ Hneq].
    unfold ParkingBlock__solver_result, ParkingCars__solver_result,
      ParkingStart__solver_result, ParkingMake__solver_result,
      ParkingEdgeCars__solver_result.
    destruct side.
    + rewrite !Zlength_app, !Zlength_cons, Zlength_nil,
        Zlength_repeat_to_nat__solver_result by lia.
      repeat split; try lia.
      * intros j Hj. rewrite app_assoc.
        rewrite <- (app_nil_r (repeat make (Z.to_nat n))).
        eapply constant_block_in_app__solver_result with (n := n) (i := n - 2);
          [lia|rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|exact Hj].
      * right. rewrite Znth_app_right__solver_result by lia.
        replace (n - 2 - 1 - Zlength free) with 0 by lia.
        cbn. exact Hneq.
    + rewrite !Zlength_app, !Zlength_cons,
        Zlength_repeat_to_nat__solver_result by lia.
      repeat split; try lia.
      * intros j Hj.
        change (Znth j (nil ++ repeat make (Z.to_nat n) ++
          ParkingOther__solver_result make d :: free) 0 = make).
        eapply constant_block_in_app__solver_result with (n := n) (i := 0);
          [lia|rewrite Zlength_nil; lia|exact Hj].
      * right. rewrite Znth_app_right__solver_result by
          (rewrite Zlength_repeat_to_nat__solver_result by lia; lia).
        rewrite Zlength_repeat_to_nat__solver_result by lia.
        rewrite Z.sub_diag. cbn. exact Hneq.
  - unfold ParkingRepPred__solver_result, ParkingInteriorPred__solver_result in Hr.
    destruct Hr as [Hk [Hmake [Hdl [Hdr [Hfree Hallfree]]]]].
    cbn in Hk, Hmake, Hdl, Hdr, Hfree, Hallfree.
    pose proof (ParkingOther_range__solver_result make dl Hmake Hdl) as [_ Hlneq].
    pose proof (ParkingOther_range__solver_result make dr Hmake Hdr) as [_ Hrneq].
    unfold ParkingBlock__solver_result, ParkingCars__solver_result,
      ParkingStart__solver_result, ParkingMake__solver_result,
      ParkingInteriorCars__solver_result.
    assert (Hsub1 : Zlength (sublist 0 k free) = k).
    { rewrite Zlength_sublist by lia. lia. }
    assert (Hsub2 : Zlength (sublist k (n - 4) free) = n - 4 - k).
    { rewrite Zlength_sublist by lia. lia. }
    rewrite !Zlength_app, !Zlength_cons, Zlength_nil,
      Zlength_repeat_to_nat__solver_result by lia.
    repeat split; try lia.
    + intros j Hj. rewrite app_assoc.
      eapply constant_block_in_app__solver_result with
        (pre := sublist 0 k free ++ (ParkingOther__solver_result make dl :: nil))
        (post := (ParkingOther__solver_result make dr :: nil) ++
          sublist k (n - 4) free) (n := n) (i := k + 1);
        [lia|rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|exact Hj].
    + right. rewrite Znth_app_right__solver_result by lia.
      replace (k + 1 - 1 - Zlength (sublist 0 k free)) with 0 by lia.
      cbn. exact Hlneq.
    + right. rewrite app_assoc.
      set (pre := sublist 0 k free ++ (ParkingOther__solver_result make dl :: nil)).
      assert (Hpre : Zlength pre = k + 1).
      { unfold pre. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      change (Znth (k + 1 + n)
        (pre ++ repeat make (Z.to_nat n) ++
         (ParkingOther__solver_result make dr :: nil) ++ sublist k (n - 4) free) 0
        <> make).
      rewrite Znth_app_right__solver_result by lia.
      rewrite Hpre. replace (k + 1 + n - (k + 1)) with n by lia.
      rewrite Znth_app_right__solver_result by
        (rewrite Zlength_repeat_to_nat__solver_result by lia; lia).
      rewrite Zlength_repeat_to_nat__solver_result by lia.
      rewrite Z.sub_diag.
      cbn. exact Hrneq.
Qed.
Lemma app_parts_equal_length__solver_result :
  forall (l1 l2 r1 r2 : list Z),
    Zlength l1 = Zlength l2 -> l1 ++ r1 = l2 ++ r2 ->
    l1 = l2 /\ r1 = r2.
Proof.
  intros l1. induction l1 as [|x l1 IH]; intros l2 r1 r2 Hlen Heq.
  - destruct l2 as [|y l2].
    + cbn in Heq. split; [reflexivity|exact Heq].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct l2 as [|y l2].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + assert (Htails : Zlength l1 = Zlength l2).
      { rewrite !Zlength_correct in *. simpl in Hlen. lia. }
      cbn in Heq. inversion Heq; subst y.
      specialize (IH l2 r1 r2 Htails H1) as [Hl Hr].
      subst l2. split; congruence.
Qed.
Lemma parking_free_decompose__solver_result :
  forall (free : list Z) k len, 0 <= k <= len -> Zlength free = len ->
    free = sublist 0 k free ++ sublist k len free.
Proof.
  intros free k len Hk Hlen.
  rewrite <- (sublist_self free len (eq_sym Hlen)) at 1.
  apply sublist_split; lia.
Qed.
Lemma ParkingCars_injective__solver_result :
  forall n, 3 <= n -> forall r1 r2,
    ParkingRepPred__solver_result n r1 ->
    ParkingRepPred__solver_result n r2 ->
    ParkingCars__solver_result n r1 = ParkingCars__solver_result n r2 ->
    r1 = r2.
Proof.
  intros n Hn r1 r2 Hr1 Hr2 Hcars.
  pose proof (ParkingCars_canonical_block__solver_result n r1 Hn Hr1) as Hb1.
  pose proof (ParkingCars_canonical_block__solver_result n r2 Hn Hr2) as Hb2.
  pose proof (ParkingCars_valid__solver_result n r2 Hn Hr2) as Hv2.
  destruct Hv2 as [Hlen2 _].
  rewrite Hcars in Hb1.
  pose proof (BeautifulParking_block_unique__solver_result n
    (ParkingCars__solver_result n r2)
    (ParkingStart__solver_result n r1) (ParkingMake__solver_result r1)
    (ParkingStart__solver_result n r2) (ParkingMake__solver_result r2)
    Hn Hlen2 Hb1 Hb2) as [Hstart Hmake].
  destruct r1 as [[side1 [make1 [d1 free1]]]|[k1 [make1 [dl1 [dr1 free1]]]]];
  destruct r2 as [[side2 [make2 [d2 free2]]]|[k2 [make2 [dl2 [dr2 free2]]]]].
  - destruct side1, side2;
      unfold ParkingRepPred__solver_result, ParkingEdgePred__solver_result in *;
      cbn -[ParkingOther__solver_result] in Hr1, Hr2, Hstart, Hmake, Hcars.
    + destruct Hr1 as [_ [Hm1 [Hd1 [Hf1 _]]]].
      destruct Hr2 as [_ [Hm2 [Hd2 [Hf2 _]]]].
      subst make2.
      change (free1 ++ ((ParkingOther__solver_result make1 d1 :: nil) ++
          repeat make1 (Z.to_nat n)) =
        free2 ++ ((ParkingOther__solver_result make1 d2 :: nil) ++
          repeat make1 (Z.to_nat n))) in Hcars.
      rewrite (app_assoc free1 (ParkingOther__solver_result make1 d1 :: nil)
        (repeat make1 (Z.to_nat n))) in Hcars.
      rewrite (app_assoc free2 (ParkingOther__solver_result make1 d2 :: nil)
        (repeat make1 (Z.to_nat n))) in Hcars.
      apply app_inv_tail in Hcars.
      assert (Hflen : Zlength free1 = Zlength free2) by lia.
      pose proof (app_parts_equal_length__solver_result free1 free2
        (ParkingOther__solver_result make1 d1 :: nil)
        (ParkingOther__solver_result make1 d2 :: nil) Hflen) as Happ.
      destruct (Happ Hcars) as [Hfree Hother].
      injection Hother as Hother.
      pose proof (ParkingOther_inj__solver_result make1 d1 d2
        Hm1 Hd1 Hd2 Hother) as Hd. subst. reflexivity.
    + exfalso. lia.
    + exfalso. lia.
    + destruct Hr1 as [_ [Hm1 [Hd1 [Hf1 _]]]].
      destruct Hr2 as [_ [Hm2 [Hd2 [Hf2 _]]]].
      subst make2. apply app_inv_head in Hcars.
      injection Hcars as Hother Hfree.
      pose proof (ParkingOther_inj__solver_result make1 d1 d2
        Hm1 Hd1 Hd2 Hother) as Hd. subst. reflexivity.
  - unfold ParkingRepPred__solver_result, ParkingEdgePred__solver_result,
      ParkingInteriorPred__solver_result in *.
    destruct side1; cbn in Hr1, Hr2, Hstart; lia.
  - unfold ParkingRepPred__solver_result, ParkingEdgePred__solver_result,
      ParkingInteriorPred__solver_result in *.
    destruct side2; cbn in Hr1, Hr2, Hstart; lia.
  - unfold ParkingRepPred__solver_result, ParkingInteriorPred__solver_result in *.
    cbn -[ParkingOther__solver_result sublist] in Hr1, Hr2, Hstart, Hmake, Hcars.
    destruct Hr1 as [Hk1 [Hm1 [Hdl1 [Hdr1 [Hf1 Hall1]]]]].
    destruct Hr2 as [Hk2 [Hm2 [Hdl2 [Hdr2 [Hf2 Hall2]]]]].
    assert (Hk : k1 = k2) by lia. subst k2. subst make2.
    assert (Hleftlen : Zlength (sublist 0 k1 free1) =
        Zlength (sublist 0 k1 free2)).
    { rewrite !Zlength_sublist by lia. lia. }
    repeat rewrite <- app_assoc in Hcars.
    pose proof (app_parts_equal_length__solver_result
      (sublist 0 k1 free1) (sublist 0 k1 free2)
      ((ParkingOther__solver_result make1 dl1 :: nil) ++
       repeat make1 (Z.to_nat n) ++ (ParkingOther__solver_result make1 dr1 :: nil) ++
       sublist k1 (n - 4) free1)
      ((ParkingOther__solver_result make1 dl2 :: nil) ++
       repeat make1 (Z.to_nat n) ++ (ParkingOther__solver_result make1 dr2 :: nil) ++
       sublist k1 (n - 4) free2) Hleftlen Hcars) as [Hleft Hrest].
    cbn in Hrest. injection Hrest as Hlo Htail.
    pose proof (ParkingOther_inj__solver_result make1 dl1 dl2
      Hm1 Hdl1 Hdl2 Hlo) as Hdl. subst dl2.
    apply app_inv_head in Htail. cbn in Htail. injection Htail as Hro Hright.
    pose proof (ParkingOther_inj__solver_result make1 dr1 dr2
      Hm1 Hdr1 Hdr2 Hro) as Hdr. subst dr2.
    pose proof (parking_free_decompose__solver_result free1 k1 (n - 4)
      ltac:(lia) Hf1) as Hdec1.
    pose proof (parking_free_decompose__solver_result free2 k1 (n - 4)
      ltac:(lia) Hf2) as Hdec2.
    assert (Hfree : free1 = free2) by
      (rewrite Hdec1, Hdec2, Hleft, Hright; reflexivity).
    subst free2. reflexivity.
Qed.
Lemma ParkingCars_mapped__solver_result :
  forall n r, 3 <= n -> ParkingRepPred__solver_result n r ->
    ParkingValidPred__solver_result n (ParkingCars__solver_result n r).
Proof.
  intros n r Hn Hr.
  pose proof (ParkingCars_valid__solver_result n r Hn Hr) as Hbeautiful.
  split; [|exact Hbeautiful].
  destruct Hbeautiful as [Hlen [Hall _]]. split; [exact Hlen|].
  clear Hlen.
  induction Hall as [|c cars Hc Hall IH].
  - constructor.
  - constructor.
    + unfold ParkingColor__solver_result. lia.
    + exact IH.
Qed.
Lemma set_card_valid_parking__solver_result :
  forall n, 3 <= n ->
    @set_card ParkingRep__solver_result (ParkingRepPred__solver_result n)
      (finite_parking_rep__solver_result n) =
    #(fun cars : list Z =>
      (Zlength cars = 2 * n - 2 /\
       Forall (fun c => 1 <= c < 5) cars) /\ BeautifulParking n cars).
Proof.
  intros n Hn.
  eapply set_card_bijection__solver_result with
    (f := ParkingCars__solver_result n).
  - intros r Hr. apply ParkingCars_mapped__solver_result; assumption.
  - intros cars Hcars.
    apply ParkingCars_surjective__solver_result; assumption.
  - intros r1 r2 Hr1 Hr2 Heq.
    eapply ParkingCars_injective__solver_result; eauto.
Qed.
Lemma Spec_closed_form__solver_result :
  forall n, 3 <= n ->
    Spec n (24 * 4 ^ (n - 3) + (n - 3) * 36 * 4 ^ (n - 4)).
Proof.
  intros n Hn. unfold Spec.
  rewrite <- set_card_valid_parking__solver_result by exact Hn.
  symmetry. apply set_card_parking_rep__solver_result. exact Hn.
Qed.
