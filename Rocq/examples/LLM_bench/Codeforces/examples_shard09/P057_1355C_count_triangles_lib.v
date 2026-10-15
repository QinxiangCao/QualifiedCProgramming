Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.
Definition Pre (a b c d : Z) : Prop :=
  (* Stated explicitly in the P057 solver Require, which therefore omits the
     Pre(...) call:
       1 <= a <= b /\ b <= c /\ c <= d /\ d <= 500000. *)
  True.
Definition Spec (a b c d out : Z) : Prop :=
  let nx := b - a + 1 in let ny := c - b + 1 in let nz := d - c + 1 in
  out = #(fun q : Z => 0 <= q < nx * ny * nz /\
    let x := a + (q / (ny * nz)) mod nx in
    let y := b + (q / nz) mod ny in let z := c + q mod nz in x + y > z).

(* The loop has processed exactly the triples whose first two sides have
   sum below [next].  This is a mathematical restriction of [Spec], rather
   than a model of the loop's min/max implementation. *)
Definition TrianglePrefix (a b c d next total : Z) : Prop :=
  let nx := b - a + 1 in let ny := c - b + 1 in let nz := d - c + 1 in
  total = #(fun q : Z => 0 <= q < nx * ny * nz /\
    let x := a + (q / (ny * nz)) mod nx in
    let y := b + (q / nz) mod ny in let z := c + q mod nz in
    x + y > z /\ x + y < next).

(* Closed-form size of the newly admitted slice [x + y = s].  Keeping this
   value separate from [TrianglePrefix] gives later proofs a small bridge to
   the interval intersections computed by the C body. *)
Definition TriangleContribution (a b c d s : Z) : Z :=
  Z.max 0 (Z.min b (s - b) - Z.max a (s - c) + 1) *
  Z.max 0 (Z.min d (s - 1) - c + 1).

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Lemma set_card_empty__prefix_initialization :
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
Lemma triangle_prefix_initial__prefix_initialization :
  forall a b c d,
    1 <= a -> a <= b -> b <= c -> c <= d ->
    TrianglePrefix a b c d (a + b) 0.
Proof.
  intros a b c d Ha Hab Hbc Hcd.
  unfold TrianglePrefix.
  symmetry.
  apply set_card_empty__prefix_initialization.
  intros q Hmember.
  cbn zeta in Hmember.
  destruct Hmember as [_ [_ Hlt]].
  pose proof (Z.mod_pos_bound
    (q / ((c - b + 1) * (d - c + 1))) (b - a + 1) ltac:(lia)) as Hx.
  pose proof (Z.mod_pos_bound
    (q / (d - c + 1)) (c - b + 1) ltac:(lia)) as Hy.
  lia.
Qed.
Lemma set_card_bijection__prefix_transition :
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
    - intros y. rewrite <- (@enum_ok B Q FQ y). split.
      + intros Hin. apply in_map_iff in Hin.
        destruct Hin as [x [Hxy Hx]]. subst y.
        apply Hf. apply (proj2 (@enum_ok A P FP x)). exact Hx.
      + intros HyQ. apply in_map_iff. exists (g y). split.
        * apply Hfg. exact HyQ.
        * apply (proj1 (@enum_ok A P FP (g y))). apply Hg. exact HyQ.
  }
  assert (Hfold_count : forall (C : Type) (l : list C),
    fold_right (fun _ (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l)).
  {
    intros C l. induction l as [|x xs IH].
    - reflexivity.
    - cbn [fold_right length].
      rewrite IH, Nat2Z.inj_succ. lia.
  }
  rewrite !Hfold_count.
  rewrite <- (Permutation_length Hperm), length_map.
  reflexivity.
Qed.
Lemma set_card_ext__prefix_transition :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Heq.
  eapply set_card_bijection__prefix_transition
    with (f := fun x => x) (g := fun x => x).
  - intros x Hx. apply Heq. exact Hx.
  - intros x Hx. apply Heq. exact Hx.
  - intros. reflexivity.
  - intros. reflexivity.
Qed.
Lemma Zlength_Zrange__prefix_transition :
  forall low high, low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hrange. unfold Zrange.
  rewrite Zlength_correct.
  assert (Hlen : forall k start, length (Zrange_aux start k) = k).
  { induction k as [|k IH]; intros start; simpl; [reflexivity |].
    rewrite IH. reflexivity. }
  rewrite Hlen. lia.
Qed.
Lemma set_card_Z_rectangle__prefix_transition :
  forall xl xh yl yh,
    xl <= xh -> yl <= yh ->
    @set_card (Z * Z)
      (fun p : Z * Z => xl <= fst p < xh /\ yl <= snd p < yh)
      (@Finite_prod Z Z
        (fun x => xl <= x < xh) (fun y => yl <= y < yh)
        (finite_Z_range xl xh) (finite_Z_range yl yh)) =
      (xh - xl) * (yh - yl).
Proof.
  intros xl xh yl yh Hx Hy.
  unfold set_card, SumLib.Sum.sum.
  change
    (fold_right (fun _ (acc : Z) => 1 + acc) 0
       (list_prod (Zrange xl xh) (Zrange yl yh)) =
     (xh - xl) * (yh - yl)).
  assert (Hfold_count : forall (C : Type) (l : list C),
    fold_right (fun _ (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l)).
  {
    intros C l. induction l as [|u us IH].
    - reflexivity.
    - cbn [fold_right length]. rewrite IH, Nat2Z.inj_succ. lia.
  }
  rewrite !Hfold_count.
  rewrite length_prod.
  rewrite Nat2Z.inj_mul.
  assert (Hlenx : Z.of_nat (length (Zrange xl xh)) = xh - xl).
  {
    rewrite <- Zlength_correct.
    apply Zlength_Zrange__prefix_transition. exact Hx.
  }
  assert (Hleny : Z.of_nat (length (Zrange yl yh)) = yh - yl).
  {
    rewrite <- Zlength_correct.
    apply Zlength_Zrange__prefix_transition. exact Hy.
  }
  rewrite Hlenx, Hleny. reflexivity.
Qed.
Lemma mixed_radix_encode_decode__prefix_transition :
  forall nx ny nz ix iy iz,
    0 < nx -> 0 < ny -> 0 < nz ->
    0 <= ix < nx -> 0 <= iy < ny -> 0 <= iz < nz ->
    let q := ix * ny * nz + iy * nz + iz in
    0 <= q < nx * ny * nz /\
    (q / (ny * nz)) mod nx = ix /\
    (q / nz) mod ny = iy /\
    q mod nz = iz.
Proof.
  intros nx ny nz ix iy iz Hnx Hny Hnz Hix Hiy Hiz.
  cbn.
  assert (Hr1 : 0 <= iy * nz + iz < ny * nz) by nia.
  assert (Hr2 : 0 <= iz < nz) by lia.
  split; [nia |].
  split.
  - replace (ix * ny * nz + iy * nz + iz)
      with (ix * (ny * nz) + (iy * nz + iz)) by ring.
    rewrite Z.div_add_l by nia.
    rewrite Z.div_small by nia.
    rewrite Z.add_0_r, Z.mod_small by lia.
    reflexivity.
  - split.
    + replace (ix * ny * nz + iy * nz + iz)
        with ((ix * ny + iy) * nz + iz) by ring.
      rewrite Z.div_add_l by lia.
      rewrite Z.div_small by lia.
      rewrite Z.add_0_r.
      replace (ix * ny + iy) with (iy + ix * ny) by ring.
      rewrite Z.mod_add by lia.
      apply Z.mod_small. lia.
    + replace (ix * ny * nz + iy * nz + iz)
        with ((ix * ny + iy) * nz + iz) by ring.
      replace ((ix * ny + iy) * nz + iz)
        with (iz + (ix * ny + iy) * nz) by ring.
      rewrite Z.mod_add by lia.
      apply Z.mod_small. lia.
Qed.
Lemma mixed_radix_decode_encode__prefix_transition :
  forall nx ny nz q,
    0 < nx -> 0 < ny -> 0 < nz ->
    0 <= q < nx * ny * nz ->
    ((q / (ny * nz)) mod nx) * ny * nz +
      ((q / nz) mod ny) * nz + q mod nz = q.
Proof.
  intros nx ny nz q Hnx Hny Hnz Hq.
  assert (Hqnz : 0 <= q / nz) by (apply Z_div_nonneg_nonneg; lia).
  assert (Hqouter : 0 <= q / (ny * nz) < nx).
  { split; [apply Z_div_nonneg_nonneg; nia | apply Z.div_lt_upper_bound; nia]. }
  assert (Hq1 := Z.div_mod q nz ltac:(lia)).
  assert (Hq2 := Z.div_mod (q / nz) ny ltac:(lia)).
  assert (Hdivdiv : (q / nz) / ny = q / (ny * nz)).
  { rewrite Z.div_div by lia. f_equal. ring. }
  rewrite Z.mod_small by exact Hqouter.
  nia.
Qed.
Lemma set_card_Z_as_sum__prefix_transition :
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
Lemma set_card_Z_bounded_disjoint_or__prefix_transition :
  forall (low high : Z) (P Q : Z -> Prop),
    (forall x, low <= x < high -> ~ (P x /\ Q x)) ->
    #(fun x : Z => low <= x < high /\ (P x \/ Q x)) =
    #(fun x : Z => low <= x < high /\ P x) +
    #(fun x : Z => low <= x < high /\ Q x).
Proof.
  intros low high P Q Hdisj.
  rewrite !set_card_Z_as_sum__prefix_transition.
  rewrite <- SumLib.Sum.sum_add.
  apply SumLib.Sum.sum_ext.
  intros x Hx.
  destruct (prop_dec (P x)); destruct (prop_dec (Q x));
    destruct (prop_dec (P x \/ Q x)); try lia; try tauto.
  exfalso. apply (Hdisj x Hx). tauto.
Qed.
Lemma triangle_slice_card__prefix_transition :
  forall a b c d s,
    1 <= a <= b -> b <= c -> c <= d ->
    a + b <= s <= b + c ->
    #(fun q : Z =>
        0 <= q < (b - a + 1) * (c - b + 1) * (d - c + 1) /\
        let x := a + (q / ((c - b + 1) * (d - c + 1))) mod (b - a + 1) in
        let y := b + (q / (d - c + 1)) mod (c - b + 1) in
        let z := c + q mod (d - c + 1) in
        x + y > z /\ x + y = s) =
      Z.max 0 (Z.min b (s - b) - Z.max a (s - c) + 1) *
      Z.max 0 (Z.min d (s - 1) - c + 1).
Proof.
  intros a b c d s Hab Hbc Hcd Hs.
  destruct Hab as [Ha Hab].
  destruct Hs as [Hslow Hshigh].
  set (nx := b - a + 1).
  set (ny := c - b + 1).
  set (nz := d - c + 1).
  set (xlo := Z.max a (s - c)).
  set (xhi := Z.min b (s - b)).
  set (zhi := Z.min d (s - 1)).
  set (zup := Z.max c (zhi + 1)).
  assert (Hnx : 0 < nx) by (unfold nx; lia).
  assert (Hny : 0 < ny) by (unfold ny; lia).
  assert (Hnz : 0 < nz) by (unfold nz; lia).
  assert (Hxrange : xlo <= xhi).
  {
    unfold xlo, xhi.
    apply Z.max_lub; apply Z.min_glb; lia.
  }
  assert (Hzrange : c <= zup) by (unfold zup; apply Z.le_max_l).
  set (Slice := fun q : Z =>
    let x := a + (q / (ny * nz)) mod nx in
    let y := b + (q / nz) mod ny in
    let z := c + q mod nz in
    x + y > z /\ x + y = s).
  set (f := fun q : Z =>
    (a + (q / (ny * nz)) mod nx, c + q mod nz)).
  set (g := fun p : Z * Z =>
    (fst p - a) * ny * nz + (s - fst p - b) * nz + (snd p - c)).
  assert (Hbij :
    @set_card Z (fun q => 0 <= q < nx * ny * nz /\ Slice q)
      (finite_Z_range' 0 (nx * ny * nz) Slice) =
    @set_card (Z * Z)
      (fun p => xlo <= fst p < xhi + 1 /\ c <= snd p < zup)
      (@Finite_prod Z Z
        (fun x => xlo <= x < xhi + 1) (fun z => c <= z < zup)
        (finite_Z_range xlo (xhi + 1)) (finite_Z_range c zup))).
  {
    eapply set_card_bijection__prefix_transition with (f := f) (g := g).
    - intros q [Hq Hslice].
      unfold Slice in Hslice; cbn in Hslice.
      destruct Hslice as [Hgt Heq].
      pose proof (Z.mod_pos_bound (q / (ny * nz)) nx ltac:(lia)) as Hix.
      pose proof (Z.mod_pos_bound (q / nz) ny ltac:(lia)) as Hiy.
      pose proof (Z.mod_pos_bound q nz ltac:(lia)) as Hiz.
      unfold f; cbn.
      split.
      + split.
        * unfold xlo. apply Z.max_lub; lia.
        * assert (a + (q / (ny * nz)) mod nx <= xhi).
          { unfold xhi. apply Z.min_glb; lia. }
          lia.
      + split; [lia |].
        assert (Hzhi : c + q mod nz <= zhi).
        { unfold zhi. apply Z.min_glb; lia. }
        unfold zup. pose proof (Z.le_max_r c (zhi + 1)). lia.
    - intros [x z] [Hx Hz].
      destruct Hx as [Hxl Hxh].
      destruct Hz as [Hzc Hzup].
      cbn in Hxl, Hxh, Hzc, Hzup.
      unfold g; cbn.
      assert (Hxlo_a : a <= xlo) by (unfold xlo; apply Z.le_max_l).
      assert (Hxlo_sc : s - c <= xlo) by (unfold xlo; apply Z.le_max_r).
      assert (Hxhi_b : xhi <= b) by (unfold xhi; apply Z.le_min_l).
      assert (Hxhi_sb : xhi <= s - b) by (unfold xhi; apply Z.le_min_r).
      assert (Hzhi : z <= zhi).
      {
        destruct (Z_le_gt_dec (zhi + 1) c) as [Hempty | Hnonempty].
        - unfold zup in Hzup; fold zhi in Hzup.
          rewrite Z.max_l in Hzup by lia. lia.
        - unfold zup in Hzup; fold zhi in Hzup.
          rewrite Z.max_r in Hzup by lia.
          apply Z.lt_succ_r. exact Hzup.
      }
      assert (Hzhi_d : zhi <= d) by (unfold zhi; apply Z.le_min_l).
      assert (Hzhi_s : zhi <= s - 1) by (unfold zhi; apply Z.le_min_r).
      assert (Hixb : 0 <= x - a < nx).
      {
        split.
        - apply Z.sub_nonneg. eapply Z.le_trans; [exact Hxlo_a | exact Hxl].
        - replace nx with ((b + 1) - a) by (unfold nx; ring).
          apply Z.sub_lt_mono_r.
          eapply Z.lt_le_trans; [exact Hxh | lia].
      }
      assert (Hiyb : 0 <= s - x - b < ny) by (unfold ny; split; lia).
      assert (Hizb : 0 <= z - c < nz) by (unfold nz; split; lia).
      destruct (mixed_radix_encode_decode__prefix_transition
        nx ny nz (x - a) (s - x - b) (z - c)
        Hnx Hny Hnz Hixb Hiyb Hizb)
        as [Hq [Hdx [Hdy Hdz]]].
      split; [exact Hq |].
      unfold Slice; cbn.
      rewrite Hdx, Hdy, Hdz. nia.
    - intros q [Hq Hslice].
      unfold Slice in Hslice; cbn in Hslice.
      destruct Hslice as [_ Heq].
      unfold g, f; cbn.
      pose proof (mixed_radix_decode_encode__prefix_transition
        nx ny nz q Hnx Hny Hnz Hq) as Hrec.
      nia.
    - intros [x z] [Hx Hz].
      destruct Hx as [Hxl Hxh].
      destruct Hz as [Hzc Hzup].
      cbn in Hxl, Hxh, Hzc, Hzup.
      unfold f, g; cbn.
      assert (Hxlo_a : a <= xlo) by (unfold xlo; apply Z.le_max_l).
      assert (Hxlo_sc : s - c <= xlo) by (unfold xlo; apply Z.le_max_r).
      assert (Hxhi_b : xhi <= b) by (unfold xhi; apply Z.le_min_l).
      assert (Hxhi_sb : xhi <= s - b) by (unfold xhi; apply Z.le_min_r).
      assert (Hzhi : z <= zhi).
      {
        destruct (Z_le_gt_dec (zhi + 1) c) as [Hempty | Hnonempty].
        - unfold zup in Hzup; fold zhi in Hzup.
          rewrite Z.max_l in Hzup by lia. lia.
        - unfold zup in Hzup; fold zhi in Hzup.
          rewrite Z.max_r in Hzup by lia.
          apply Z.lt_succ_r. exact Hzup.
      }
      assert (Hzhi_d : zhi <= d) by (unfold zhi; apply Z.le_min_l).
      assert (Hixb : 0 <= x - a < nx).
      {
        split.
        - apply Z.sub_nonneg. eapply Z.le_trans; [exact Hxlo_a | exact Hxl].
        - replace nx with ((b + 1) - a) by (unfold nx; ring).
          apply Z.sub_lt_mono_r.
          eapply Z.lt_le_trans; [exact Hxh | lia].
      }
      assert (Hiyb : 0 <= s - x - b < ny) by (unfold ny; split; lia).
      assert (Hizb : 0 <= z - c < nz) by (unfold nz; split; lia).
      destruct (mixed_radix_encode_decode__prefix_transition
        nx ny nz (x - a) (s - x - b) (z - c)
        Hnx Hny Hnz Hixb Hiyb Hizb)
        as [_ [Hdx [_ Hdz]]].
      rewrite Hdx, Hdz. f_equal; lia.
  }
  change
    (@set_card Z (fun q => 0 <= q < nx * ny * nz /\ Slice q)
       (finite_Z_range' 0 (nx * ny * nz) Slice) =
     Z.max 0 (Z.min b (s - b) - Z.max a (s - c) + 1) *
       Z.max 0 (Z.min d (s - 1) - c + 1)).
  rewrite Hbij.
  rewrite set_card_Z_rectangle__prefix_transition by lia.
  unfold xlo, xhi, zup, zhi, nx, ny, nz.
  replace
    (Z.max 0 (Z.min b (s - b) - Z.max a (s - c) + 1))
    with (Z.min b (s - b) - Z.max a (s - c) + 1)
    by (symmetry; apply Z.max_r; lia).
  assert (Hmax :
    Z.max c (Z.min d (s - 1) + 1) - c =
    Z.max 0 (Z.min d (s - 1) - c + 1)).
  {
    destruct (Z_le_gt_dec (Z.min d (s - 1) + 1) c)
      as [Hzempty | Hznonempty].
    - rewrite Z.max_l by lia. rewrite Z.max_l by lia. lia.
    - rewrite Z.max_r by lia. rewrite Z.max_r by lia. lia.
  }
  rewrite Hmax. ring.
Qed.
Lemma triangle_prefix_step__prefix_transition :
  forall a b c d s total,
    1 <= a <= b -> b <= c -> c <= d ->
    a + b <= s <= b + c ->
    TrianglePrefix a b c d s total ->
    TrianglePrefix a b c d (s + 1)
      (total + TriangleContribution a b c d s).
Proof.
  intros a b c d s total Hab Hbc Hcd Hs Hprefix.
  destruct Hab as [Ha Hab].
  destruct Hs as [Hslow Hshigh].
  unfold TrianglePrefix in Hprefix |- *.
  cbn zeta in Hprefix |- *.
  subst total.
  unfold TriangleContribution.
  set (N := (b - a + 1) * (c - b + 1) * (d - c + 1)).
  set (Old := fun q : Z =>
    let x := a + (q / ((c - b + 1) * (d - c + 1))) mod (b - a + 1) in
    let y := b + (q / (d - c + 1)) mod (c - b + 1) in
    let z := c + q mod (d - c + 1) in
    x + y > z /\ x + y < s).
  set (Slice := fun q : Z =>
    let x := a + (q / ((c - b + 1) * (d - c + 1))) mod (b - a + 1) in
    let y := b + (q / (d - c + 1)) mod (c - b + 1) in
    let z := c + q mod (d - c + 1) in
    x + y > z /\ x + y = s).
  set (New := fun q : Z =>
    let x := a + (q / ((c - b + 1) * (d - c + 1))) mod (b - a + 1) in
    let y := b + (q / (d - c + 1)) mod (c - b + 1) in
    let z := c + q mod (d - c + 1) in
    x + y > z /\ x + y < s + 1).
  symmetry.
  change
    (@set_card Z (fun q => 0 <= q < N /\ New q)
       (finite_Z_range' 0 N New) =
     @set_card Z (fun q => 0 <= q < N /\ Old q)
       (finite_Z_range' 0 N Old) +
     Z.max 0 (Z.min b (s - b) - Z.max a (s - c) + 1) *
       Z.max 0 (Z.min d (s - 1) - c + 1)).
  transitivity
    (@set_card Z (fun q => 0 <= q < N /\ (Old q \/ Slice q))
       (finite_Z_range' 0 N (fun q => Old q \/ Slice q))).
  - apply set_card_ext__prefix_transition. intros q.
    unfold New, Old, Slice; cbn. intuition lia.
  - rewrite set_card_Z_bounded_disjoint_or__prefix_transition.
    + f_equal.
      unfold N, Slice.
      apply triangle_slice_card__prefix_transition; repeat split; assumption.
    + intros q Hq [Hold Hslice].
      unfold Old, Slice in *; cbn in *.
      intuition lia.
Qed.
Lemma triangle_prefix_complete__final_result :
  forall a b c d s total,
    1 <= a -> a <= b -> b <= c -> c <= d ->
    b + c < s ->
    TrianglePrefix a b c d s total ->
    Spec a b c d total.
Proof.
  intros a b c d s total Ha Hab Hbc Hcd Hs Hprefix.
  unfold TrianglePrefix in Hprefix.
  unfold Spec.
  cbv zeta in Hprefix |- *.
  rewrite Hprefix.
  assert (Hcard_ext :
    forall (P Q : Z -> Prop) (FP : Finite P) (FQ : Finite Q),
      (forall q, P q <-> Q q) ->
      @set_card Z P FP = @set_card Z Q FQ).
  {
    intros P Q FP FQ Hequiv.
    unfold set_card, SumLib.Sum.sum.
    assert (Hperm : Permutation (@enum Z P FP) (@enum Z Q FQ)).
    {
      apply NoDup_Permutation.
      - exact (@enum_nodup Z P FP).
      - exact (@enum_nodup Z Q FQ).
      - intro q.
        rewrite <- (@enum_ok Z P FP q), <- (@enum_ok Z Q FQ q).
        apply Hequiv.
    }
    induction Hperm.
    - reflexivity.
    - change (1 + fold_right (fun _ acc => 1 + acc) 0 l =
              1 + fold_right (fun _ acc => 1 + acc) 0 l').
      rewrite IHHperm. reflexivity.
    - reflexivity.
    - etransitivity; eassumption.
  }
  apply Hcard_ext.
  intro q.
  split.
  - intros (Hrange & Htriangle & Hlt).
    exact (conj Hrange Htriangle).
  - intros (Hrange & Htriangle).
    refine (conj Hrange (conj Htriangle _)).
    assert (Hnx : 0 < b - a + 1) by lia.
    assert (Hny : 0 < c - b + 1) by lia.
    pose proof (Z.mod_pos_bound
      (q / ((c - b + 1) * (d - c + 1)))
      (b - a + 1) Hnx) as Hx.
    pose proof (Z.mod_pos_bound
      (q / (d - c + 1))
      (c - b + 1) Hny) as Hy.
    lia.
Qed.
