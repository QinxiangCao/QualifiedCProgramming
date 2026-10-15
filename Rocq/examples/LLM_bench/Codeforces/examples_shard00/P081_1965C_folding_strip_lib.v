Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition ValidFoldedPlacement (s positions : list Z) (width : Z) : Prop :=
  Zlength positions = Zlength s /\ 1 <= width <= Zlength s /\
  Forall (fun p => 0 <= p < width) positions /\
  (forall i, 0 <= i < Zlength positions - 1 ->
    Z.abs (Znth (i+1) positions 0 - Znth i positions 0) = 1) /\
  (forall i j, 0 <= i < Zlength s -> 0 <= j < Zlength s ->
    Znth i positions 0 = Znth j positions 0 -> Znth i s 0 = Znth j s 0) /\
  (forall p, 0 <= p < width -> In p positions).

Definition Pre (s : list Z) : Prop :=
  1 <= Zlength s <= 200000 /\ Forall (fun c => c = 48 \/ c = 49) s.

Definition Spec (s : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      ValidFoldedPlacement s (fst candidate) (snd candidate))
    snd out.

Definition edge_lower (boundaries : list Z) (i : Z) : Z :=
  Z.min (Znth i boundaries 0) (Znth (i + 1) boundaries 0).

Definition ValidFoldedPlacementEdges
    (s boundaries : list Z) (width : Z) : Prop :=
  Zlength boundaries = Zlength s + 1 /\
  1 <= width <= Zlength s /\
  Forall (fun p => 0 <= p <= width) boundaries /\
  (forall i, 0 <= i < Zlength s ->
    Z.abs (Znth (i + 1) boundaries 0 - Znth i boundaries 0) = 1) /\
  (forall i j, 0 <= i < Zlength s -> 0 <= j < Zlength s ->
    edge_lower boundaries i = edge_lower boundaries j ->
    Znth i s 0 = Znth j s 0) /\
  (forall p, 0 <= p < width ->
    exists i, 0 <= i < Zlength s /\ edge_lower boundaries i = p).

Definition SpecEdges (s : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      ValidFoldedPlacementEdges s (fst candidate) (snd candidate))
    snd out.

Definition AlternatingWalkExtrema
    (s boundaries : list Z) (cur mn mx : Z) : Prop :=
  Zlength boundaries = Zlength s + 1 /\
  Znth 0 boundaries 0 = 0 /\
  Znth (Zlength s) boundaries 0 = cur /\
  (forall k, 0 <= k < Zlength s ->
    Z.abs (Znth (k + 1) boundaries 0 - Znth k boundaries 0) = 1) /\
  (forall k, 0 <= k < Zlength s ->
    (Znth k s 0 = 49 <->
     Z.even (edge_lower boundaries k) = true)) /\
  (forall k, 0 <= k < Zlength boundaries ->
    mn <= Znth k boundaries 0 <= mx) /\
  In mn boundaries /\ In mx boundaries.

Definition FoldPrefixState
    (s : list Z) (i cur mn mx : Z) : Prop :=
  0 <= i <= Zlength s /\
  exists boundaries,
    AlternatingWalkExtrema (sublist 0 i s) boundaries cur mn mx /\
    (forall candidate width,
      ValidFoldedPlacementEdges (sublist 0 i s) candidate width ->
      mx - mn <= width).

Definition AlternatingLabelPlacement
    (s boundaries : list Z) (width : Z) : Prop :=
  ValidFoldedPlacementEdges s boundaries width /\
  exists phase : bool,
    forall i, 0 <= i < Zlength s ->
      (Znth i s 0 = 49 <->
       Z.even (edge_lower boundaries i) = phase).

Definition SpecAlternatingEdges (s : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le
    (fun candidate : list Z * Z =>
      AlternatingLabelPlacement s (fst candidate) (snd candidate))
    snd out.

Definition FoldPrefixAlternatingState
    (s : list Z) (i cur mn mx : Z) : Prop :=
  0 <= i <= Zlength s /\
  exists boundaries,
    AlternatingWalkExtrema (sublist 0 i s) boundaries cur mn mx /\
    (forall candidate width,
      AlternatingLabelPlacement (sublist 0 i s) candidate width ->
      mx - mn <= width).

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Lemma Z_land_one_step_parity__alternating_transitions :
  forall x y,
    Z.land x 1 = Z.land y 1 ->
    Z.land (x + 1) 1 = Z.land (y + 1) 1 /\
    Z.land (x - 1) 1 = Z.land (y + 1) 1.
Proof.
  intros x y H.
  repeat rewrite (Z.land_ones _ 1) by lia.
  repeat rewrite (Z.land_ones _ 1) in H by lia.
  change (x mod 2 = y mod 2) in H.
  change ((x + 1) mod 2 = (y + 1) mod 2 /\
          (x - 1) mod 2 = (y + 1) mod 2).
  split.
  - rewrite (Z.add_mod x 1 2), (Z.add_mod y 1 2) by lia.
    rewrite H.
    reflexivity.
  - replace (x - 1) with ((x + 1) + (-1) * 2) by ring.
    rewrite Z.add_mod, Z.mul_mod by lia.
    cbn.
    rewrite Z.add_0_r, Zmod_mod.
    rewrite (Z.add_mod x 1 2), (Z.add_mod y 1 2) by lia.
    rewrite H.
    reflexivity.
Qed.
Lemma Z_land_one_even__alternating_transitions : forall x,
  Z.land x 1 = 0 <-> Z.even x = true.
Proof.
  intros x.
  repeat rewrite (Z.land_ones _ 1) by lia.
  change (x mod 2 = 0 <-> Z.even x = true).
  rewrite Z.even_spec.
  unfold Z.Even.
  split.
  - intros Hmod. exists (x / 2).
    pose proof (Z.div_mod x 2 ltac:(lia)). lia.
  - intros [z Hz]. subst x.
    rewrite Z.mul_mod by lia. reflexivity.
Qed.
Lemma abs_one_cases__alternating_transitions : forall d,
  Z.abs d = 1 -> d = 1 \/ d = -1.
Proof.
  intros d H. destruct (Z_le_gt_dec 0 d).
  - rewrite Z.abs_eq in H by lia. lia.
  - rewrite Z.abs_neq in H by lia. lia.
Qed.
Lemma alternating_unit_step_orientation__alternating_transitions :
  forall c a a' b b' phase,
  Z.abs (a' - a) = 1 ->
  Z.abs (b' - b) = 1 ->
  (c = 49 <-> Z.even (Z.min a a') = true) ->
  (c = 49 <-> Z.even (Z.min b b') = phase) ->
  Bool.eqb (Bool.eqb (Z.even b') phase) (Z.even a') =
    Bool.eqb (Bool.eqb (Z.even b) phase) (Z.even a) /\
  (if Bool.eqb (Bool.eqb (Z.even b) phase) (Z.even a)
   then b' - b = a' - a else b' - b = -(a' - a)).
Proof.
  intros c a a' b b' phase Ha Hb Hca Hcb.
  apply abs_one_cases__alternating_transitions in Ha.
  apply abs_one_cases__alternating_transitions in Hb.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  all: try replace a' with (a + 1) in * by lia.
  all: try replace a' with (a - 1) in * by lia.
  all: try replace b' with (b + 1) in * by lia.
  all: try replace b' with (b - 1) in * by lia.
  all: rewrite ?Z.min_l, ?Z.min_r in * by lia.
  all: rewrite ?Z.even_add, ?Z.even_sub in *.
  all: cbn in *.
  all: destruct (Z.eq_dec c 49) as [Hc|Hc];
    [ subst c | idtac ].
  all: destruct (Z.even a), (Z.even b), phase;
    cbn in *; try (split; reflexivity); try (split; ring);
    exfalso; firstorder congruence.
Qed.
Lemma alternating_paths_isometry_at_nat__alternating_transitions :
  forall s canonical candidate phase (n : nat),
  Zlength canonical = Zlength s + 1 ->
  Zlength candidate = Zlength s + 1 ->
  (forall k, 0 <= k < Zlength s ->
    Z.abs (Znth (k + 1) canonical 0 - Znth k canonical 0) = 1) ->
  (forall k, 0 <= k < Zlength s ->
    Z.abs (Znth (k + 1) candidate 0 - Znth k candidate 0) = 1) ->
  (forall k, 0 <= k < Zlength s ->
    (Znth k s 0 = 49 <->
     Z.even (edge_lower canonical k) = true)) ->
  (forall k, 0 <= k < Zlength s ->
    (Znth k s 0 = 49 <->
     Z.even (edge_lower candidate k) = phase)) ->
  Z.of_nat n <= Zlength s ->
  Bool.eqb (Bool.eqb (Z.even (Znth (Z.of_nat n) candidate 0)) phase)
      (Z.even (Znth (Z.of_nat n) canonical 0)) =
    Bool.eqb (Bool.eqb (Z.even (Znth 0 candidate 0)) phase)
      (Z.even (Znth 0 canonical 0)) /\
  (if Bool.eqb (Bool.eqb (Z.even (Znth 0 candidate 0)) phase)
        (Z.even (Znth 0 canonical 0))
   then Znth (Z.of_nat n) candidate 0 - Znth 0 candidate 0 =
        Znth (Z.of_nat n) canonical 0 - Znth 0 canonical 0
   else Znth (Z.of_nat n) candidate 0 - Znth 0 candidate 0 =
        -(Znth (Z.of_nat n) canonical 0 - Znth 0 canonical 0)).
Proof.
  intros s canonical candidate phase n.
  induction n as [|n IH]; intros Hclen Hblen Hcstep Hbstep Hclabel Hblabel Hn.
  - cbn. split; [reflexivity|].
    destruct (Bool.eqb (Bool.eqb (Z.even (Znth 0 candidate 0)) phase)
      (Z.even (Znth 0 canonical 0))); ring.
  - set (k := Z.of_nat n).
    replace (Z.of_nat (S n)) with (k + 1) by
      (unfold k; rewrite Nat2Z.inj_succ; lia).
    assert (Hk : 0 <= k < Zlength s) by
      (unfold k in *; pose proof (Nat2Z.is_nonneg n); lia).
    specialize (IH Hclen Hblen Hcstep Hbstep Hclabel Hblabel ltac:(lia)).
    destruct IH as [IHorient IHcoord].
    pose proof (alternating_unit_step_orientation__alternating_transitions
      (Znth k s 0)
      (Znth k canonical 0) (Znth (k + 1) canonical 0)
      (Znth k candidate 0) (Znth (k + 1) candidate 0) phase
      (Hcstep k Hk) (Hbstep k Hk)) as Hlocal.
    unfold edge_lower in Hclabel, Hblabel.
    specialize (Hlocal (Hclabel k Hk) (Hblabel k Hk)).
    destruct Hlocal as [Hnext Hdelta].
    unfold k in IHorient, IHcoord, Hnext, Hdelta.
    split.
    + etransitivity; [exact Hnext | exact IHorient].
    + destruct (Bool.eqb
        (Bool.eqb (Z.even (Znth 0 candidate 0)) phase)
        (Z.even (Znth 0 canonical 0))) eqn:Hinitial.
      * assert (Hcurrent : Bool.eqb
          (Bool.eqb (Z.even (Znth (Z.of_nat n) candidate 0)) phase)
          (Z.even (Znth (Z.of_nat n) canonical 0)) = true) by congruence.
        rewrite Hcurrent in Hdelta.
        unfold k. lia.
      * assert (Hcurrent : Bool.eqb
          (Bool.eqb (Z.even (Znth (Z.of_nat n) candidate 0)) phase)
          (Z.even (Znth (Z.of_nat n) canonical 0)) = false) by congruence.
        rewrite Hcurrent in Hdelta.
        unfold k. lia.
Qed.
Lemma In_Znth_index__final_result : forall {A : Type} (l : list A) (x d : A),
  In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l. induction l as [|a l IH]; intros x d Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + exists 0. split.
      * pose proof (Zlength_nonneg l). rewrite Zlength_cons. lia.
      * rewrite Znth0_cons. reflexivity.
    + destruct (IH x d Hin) as [i [Hi Hnth]].
      exists (i + 1). split.
      * rewrite Zlength_cons. lia.
      * rewrite Znth_cons by lia. replace (i + 1 - 1) with i by lia.
        exact Hnth.
Qed.
Lemma Forall_Znth__alternating_transitions {A : Type}
    (P : A -> Prop) (d : A) (l : list A) :
  Forall P l -> forall i, 0 <= i < Zlength l -> P (Znth i l d).
Proof.
  intros H. induction H as [|a l Ha Hl IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + rewrite Znth0_cons. exact Ha.
    + rewrite Znth_cons by lia. apply IH. lia.
Qed.
Lemma alternating_label_placement_rigidity__alternating_transitions :
  forall s canonical candidate cur mn mx width,
  AlternatingWalkExtrema s canonical cur mn mx ->
  AlternatingLabelPlacement s candidate width ->
  mx - mn <= width.
Proof.
  intros s canonical candidate cur mn mx width Haw Hal.
  unfold AlternatingWalkExtrema in Haw.
  destruct Haw as [Hclen [Hc0 [Hcur [Hcstep [Hclabel [Hcbounds [Hmn Hmx]]]]]]].
  unfold AlternatingLabelPlacement, ValidFoldedPlacementEdges in Hal.
  destruct Hal as [[Hblen [Hwidth [Hbforall [Hbstep [Hcollision Hcover]]]]]
    [phase Hblabel]].
  destruct (In_Znth_index__final_result canonical mn 0 Hmn)
    as [imn [Himn Hmnval]].
  destruct (In_Znth_index__final_result canonical mx 0 Hmx)
    as [imx [Himx Hmxval]].
  assert (Himn_s : imn <= Zlength s) by lia.
  assert (Himx_s : imx <= Zlength s) by lia.
  pose proof (alternating_paths_isometry_at_nat__alternating_transitions
    s canonical candidate phase (Z.to_nat imn) Hclen Hblen
    Hcstep Hbstep Hclabel Hblabel) as Hisomn.
  pose proof (alternating_paths_isometry_at_nat__alternating_transitions
    s canonical candidate phase (Z.to_nat imx) Hclen Hblen
    Hcstep Hbstep Hclabel Hblabel) as Hisomx.
  rewrite Z2Nat.id in Hisomn by lia.
  rewrite Z2Nat.id in Hisomx by lia.
  specialize (Hisomn Himn_s).
  specialize (Hisomx Himx_s).
  destruct Hisomn as [Horientmn Hcoordmn].
  destruct Hisomx as [Horientmx Hcoordmx].
  pose proof (Forall_Znth__alternating_transitions
    (fun p => 0 <= p <= width) 0 candidate Hbforall imn ltac:(lia)) as Hbmn.
  pose proof (Forall_Znth__alternating_transitions
    (fun p => 0 <= p <= width) 0 candidate Hbforall imx ltac:(lia)) as Hbmx.
  destruct (Bool.eqb (Bool.eqb (Z.even (Znth 0 candidate 0)) phase)
    (Z.even (Znth 0 canonical 0))).
  - rewrite Hmnval in Hcoordmn. rewrite Hmxval in Hcoordmx.
    cbn in Hbmn, Hbmx. lia.
  - rewrite Hmnval in Hcoordmn. rewrite Hmxval in Hcoordmx.
    cbn in Hbmn, Hbmx. lia.
Qed.
Lemma sublist_snoc__alternating_transitions :
  forall {A : Type} (d : A) (l : list A) i,
    0 <= i < Zlength l ->
    sublist 0 (i + 1) l = sublist 0 i l ++ Znth i l d :: nil.
Proof.
  intros A d l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single d i l) by lia.
  reflexivity.
Qed.
Lemma fold_prefix_alternating_step__alternating_transitions :
  forall s i cur mn mx next mn' mx',
  0 <= i < Zlength s ->
  FoldPrefixAlternatingState s i cur mn mx ->
  Z.abs (next - cur) = 1 ->
  (Znth i s 0 = 49 <-> Z.even (Z.min cur next) = true) ->
  mn' <= mn -> mx <= mx' -> mn' <= next <= mx' ->
  (mn' = mn \/ mn' = next) ->
  (mx' = mx \/ mx' = next) ->
  FoldPrefixAlternatingState s (i + 1) next mn' mx'.
Proof.
  intros s i cur mn mx next mn' mx' Hi Hstate Hstep Hlabel
    Hmnle Hmxle Hnext Hmnin Hmxin.
  unfold FoldPrefixAlternatingState in *.
  destruct Hstate as [Hiold [boundaries [Haw Hleast]]].
  split; [lia|].
  exists (boundaries ++ (next :: nil)).
  assert (Hnew : AlternatingWalkExtrema
    (sublist 0 (i + 1) s) (boundaries ++ (next :: nil)) next mn' mx').
  { unfold AlternatingWalkExtrema in *.
    destruct Haw as [Hlen [Hzero [Hcur [Hsteps [Hlabels [Hbounds [Hinmn Hinmx]]]]]]].
    assert (Hprelen : Zlength (sublist 0 i s) = i).
    { rewrite Zlength_sublist by lia. lia. }
    rewrite (sublist_snoc__alternating_transitions 0 s i Hi).
    repeat apply conj.
    + repeat rewrite Zlength_app. repeat rewrite Zlength_cons.
      rewrite Zlength_nil, Hlen, Hprelen. lia.
    + rewrite app_Znth1 by (rewrite Hlen, Hprelen; lia). exact Hzero.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil, Hprelen.
      rewrite app_Znth2 by (rewrite Hlen, Hprelen; lia).
      rewrite Hlen, Hprelen.
      replace (i + Z.succ 0 - (i + 1)) with 0 by lia.
      rewrite Znth0_cons. reflexivity.
    + intros k Hk.
      rewrite Zlength_app, Zlength_cons, Zlength_nil, Hprelen in Hk.
      destruct (Z_lt_ge_dec k i) as [Hki|Hki].
      * rewrite !app_Znth1 by (rewrite Hlen, Hprelen; lia).
        apply Hsteps. lia.
      * assert (k = i) by lia. subst k.
        rewrite (app_Znth1 0 boundaries (next :: nil) i)
          by (rewrite Hlen, Hprelen; lia).
        rewrite (app_Znth2 0 boundaries (next :: nil) (i + 1))
          by (rewrite Hlen, Hprelen; lia).
        rewrite Hlen, Hprelen.
        replace (i + 1 - (i + 1)) with 0 by lia. rewrite Znth0_cons.
        rewrite Hprelen in Hcur. rewrite Hcur. exact Hstep.
    + intros k2 Hk2.
      rewrite Zlength_app, Zlength_cons, Zlength_nil, Hprelen in Hk2.
      destruct (Z_lt_ge_dec k2 i) as [Hki2|Hki2].
      * rewrite app_Znth1 by (rewrite Hprelen; lia).
        unfold edge_lower.
        rewrite !app_Znth1 by (rewrite Hlen, Hprelen; lia).
        apply Hlabels. lia.
      * assert (k2 = i) by lia. subst k2.
        rewrite app_Znth2 by (rewrite Hprelen; lia).
        rewrite Hprelen. replace (i - i) with 0 by lia. rewrite Znth0_cons.
        unfold edge_lower.
        rewrite app_Znth1 by (rewrite Hlen, Hprelen; lia).
        rewrite app_Znth2 by (rewrite Hlen, Hprelen; lia).
        rewrite Hlen, Hprelen.
        replace (i + 1 - (i + 1)) with 0 by lia. rewrite Znth0_cons.
        rewrite Hprelen in Hcur. rewrite Hcur. exact Hlabel.
    + intros k3 Hk3.
      rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen, Hprelen in Hk3.
      destruct (Z_lt_ge_dec k3 (i + 1)) as [Hki3|Hki3].
      * rewrite app_Znth1 by (rewrite Hlen, Hprelen; lia).
        specialize (Hbounds k3 ltac:(rewrite Hlen, Hprelen; lia)). lia.
      * assert (k3 = i + 1) by lia. subst k3.
        rewrite app_Znth2 by (rewrite Hlen, Hprelen; lia).
        rewrite Hlen, Hprelen. replace (i + 1 - (i + 1)) with 0 by lia.
        rewrite Znth0_cons. exact Hnext.
    + destruct Hmnin as [-> | ->].
      * apply in_or_app. left. exact Hinmn.
      * apply in_or_app. right. simpl. auto.
    + destruct Hmxin as [-> | ->].
      * apply in_or_app. left. exact Hinmx.
      * apply in_or_app. right. simpl. auto.
  }
  split; [exact Hnew|].
  intros candidate width Hcandidate.
    eapply alternating_label_placement_rigidity__alternating_transitions.
    + exact Hnew.
    + exact Hcandidate.
Qed.
Lemma Zlength_map__final_result : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__final_result : forall {A B : Type} (f : A -> B)
  (l : list A) (i : Z) (da : A) (db : B),
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l. induction l as [|a l IH]; intros i da db Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia. apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.
Lemma unit_walk_head_distance__final_result : forall a l y,
  (forall k, 0 <= k < Zlength (a :: l) - 1 ->
    Z.abs (Znth (k + 1) (a :: l) 0 - Znth k (a :: l) 0) = 1) ->
  In y (a :: l) ->
  Z.abs (y - a) <= Zlength (a :: l) - 1.
Proof.
  intros a l. revert a.
  induction l as [|b tl IH]; intros a y Hadj Hin.
  - simpl in Hin. destruct Hin as [-> | []]. simpl. lia.
  - pose proof (Zlength_nonneg tl) as Hlen.
    assert (Hab := Hadj 0 ltac:(repeat rewrite Zlength_cons; simpl; lia)).
    rewrite Znth0_cons in Hab. rewrite Znth_cons in Hab by lia.
    replace (0 + 1 - 1) with 0 in Hab by lia. rewrite Znth0_cons in Hab.
    assert (Htail : forall k, 0 <= k < Zlength (b :: tl) - 1 ->
      Z.abs (Znth (k + 1) (b :: tl) 0 - Znth k (b :: tl) 0) = 1).
    { intros k Hk. specialize (Hadj (k + 1) ltac:(repeat rewrite Zlength_cons in *; lia)).
      rewrite (@Znth_cons Z 0 (k + 1 + 1) a (b :: tl)) in Hadj by lia.
      rewrite (@Znth_cons Z 0 (k + 1) a (b :: tl)) in Hadj by lia.
      replace (k + 1 + 1 - 1) with (k + 1) in Hadj by lia.
      replace (k + 1 - 1) with k in Hadj by lia. exact Hadj. }
    destruct Hin as [-> | Hin].
    + replace (y - y) with 0 by ring. rewrite Z.abs_0.
      repeat rewrite Zlength_cons. lia.
    + specialize (IH b y Htail Hin).
      assert (Htri : Z.abs (y - a) <= Z.abs (y - b) + Z.abs (b - a)).
      { replace (y - a) with ((y - b) + (b - a)) by ring.
        apply Z.abs_triangle. }
      repeat rewrite Zlength_cons in *. lia.
Qed.
Lemma unit_walk_pair_distance__final_result : forall l x y,
  (forall k, 0 <= k < Zlength l - 1 ->
    Z.abs (Znth (k + 1) l 0 - Znth k l 0) = 1) ->
  In x l -> In y l ->
  Z.abs (x - y) <= Zlength l - 1.
Proof.
  intros l. induction l as [|a tl IH]; intros x y Hadj Hx Hy.
  - contradiction.
  - destruct Hx as [-> | Hx].
    + replace (x - y) with (- (y - x)) by ring.
      rewrite Z.abs_opp. eapply unit_walk_head_distance__final_result.
      * exact Hadj.
      * exact Hy.
    + destruct Hy as [-> | Hy].
      * eapply unit_walk_head_distance__final_result.
        -- exact Hadj.
        -- right. exact Hx.
      * destruct tl as [|b tl']; [contradiction|].
        assert (Htail : forall k, 0 <= k < Zlength (b :: tl') - 1 ->
          Z.abs (Znth (k + 1) (b :: tl') 0 - Znth k (b :: tl') 0) = 1).
        { intros k Hk. specialize (Hadj (k + 1) ltac:(repeat rewrite Zlength_cons in *; lia)).
          rewrite (@Znth_cons Z 0 (k + 1 + 1) a (b :: tl')) in Hadj by lia.
          rewrite (@Znth_cons Z 0 (k + 1) a (b :: tl')) in Hadj by lia.
          replace (k + 1 + 1 - 1) with (k + 1) in Hadj by lia.
          replace (k + 1 - 1) with k in Hadj by lia. exact Hadj. }
        specialize (IH x y Htail Hx Hy).
        repeat rewrite Zlength_cons in *. lia.
Qed.
Lemma unit_walk_cross_up__final_result : forall a l q,
  (forall k, 0 <= k < Zlength (a :: l) - 1 ->
    Z.abs (Znth (k + 1) (a :: l) 0 - Znth k (a :: l) 0) = 1) ->
  a <= q ->
  (exists y, In y (a :: l) /\ q < y) ->
  exists k, 0 <= k < Zlength (a :: l) - 1 /\
    edge_lower (a :: l) k = q.
Proof.
  intros a l. revert a.
  induction l as [|b tl IH]; intros a q Hadj Ha [y [Hy Hqy]].
  - simpl in Hy. destruct Hy as [-> | []]. lia.
  - pose proof (Zlength_nonneg tl) as Hlen.
    assert (Hab := Hadj 0 ltac:(repeat rewrite Zlength_cons; simpl; lia)).
    rewrite Znth0_cons in Hab. rewrite Znth_cons in Hab by lia.
    replace (0 + 1 - 1) with 0 in Hab by lia. rewrite Znth0_cons in Hab.
    assert (Htail : forall k, 0 <= k < Zlength (b :: tl) - 1 ->
      Z.abs (Znth (k + 1) (b :: tl) 0 - Znth k (b :: tl) 0) = 1).
    { intros k Hk. specialize (Hadj (k + 1) ltac:(repeat rewrite Zlength_cons in *; lia)).
      rewrite (@Znth_cons Z 0 (k + 1 + 1) a (b :: tl)) in Hadj by lia.
      rewrite (@Znth_cons Z 0 (k + 1) a (b :: tl)) in Hadj by lia.
      replace (k + 1 + 1 - 1) with (k + 1) in Hadj by lia.
      replace (k + 1 - 1) with k in Hadj by lia. exact Hadj. }
    destruct (Z_le_gt_dec b q) as [Hb | Hb].
    + assert (Hy' : In y (b :: tl)).
      { simpl in Hy. destruct Hy as [-> | Hy]; [lia|exact Hy]. }
      destruct (IH b q Htail Hb (ex_intro _ y (conj Hy' Hqy)))
        as [k [Hk Hedge]].
      exists (k + 1). split.
      * repeat rewrite Zlength_cons in *. lia.
      * unfold edge_lower in *.
        rewrite (@Znth_cons Z 0 (k + 1) a (b :: tl)) by lia.
        rewrite (@Znth_cons Z 0 (k + 1 + 1) a (b :: tl)) by lia.
        replace (k + 1 + 1 - 1) with (k + 1) by lia.
        replace (k + 1 - 1) with k by lia. exact Hedge.
    + rewrite Z.abs_eq in Hab by lia.
      assert (a = q) by lia. subst a.
      exists 0. split.
      * repeat rewrite Zlength_cons. simpl. lia.
      * unfold edge_lower. rewrite Znth0_cons.
        rewrite Znth_cons by lia. replace (0 + 1 - 1) with 0 by lia.
        rewrite Znth0_cons. rewrite Z.min_l by lia. reflexivity.
Qed.
Lemma unit_walk_cross_down__final_result : forall a l q,
  (forall k, 0 <= k < Zlength (a :: l) - 1 ->
    Z.abs (Znth (k + 1) (a :: l) 0 - Znth k (a :: l) 0) = 1) ->
  q < a ->
  (exists y, In y (a :: l) /\ y <= q) ->
  exists k, 0 <= k < Zlength (a :: l) - 1 /\
    edge_lower (a :: l) k = q.
Proof.
  intros a l. revert a.
  induction l as [|b tl IH]; intros a q Hadj Ha [y [Hy Hyq]].
  - simpl in Hy. destruct Hy as [-> | []]. lia.
  - pose proof (Zlength_nonneg tl) as Hlen.
    assert (Hab := Hadj 0 ltac:(repeat rewrite Zlength_cons; simpl; lia)).
    rewrite Znth0_cons in Hab. rewrite Znth_cons in Hab by lia.
    replace (0 + 1 - 1) with 0 in Hab by lia. rewrite Znth0_cons in Hab.
    assert (Htail : forall k, 0 <= k < Zlength (b :: tl) - 1 ->
      Z.abs (Znth (k + 1) (b :: tl) 0 - Znth k (b :: tl) 0) = 1).
    { intros k Hk. specialize (Hadj (k + 1) ltac:(repeat rewrite Zlength_cons in *; lia)).
      rewrite (@Znth_cons Z 0 (k + 1 + 1) a (b :: tl)) in Hadj by lia.
      rewrite (@Znth_cons Z 0 (k + 1) a (b :: tl)) in Hadj by lia.
      replace (k + 1 + 1 - 1) with (k + 1) in Hadj by lia.
      replace (k + 1 - 1) with k in Hadj by lia. exact Hadj. }
    destruct (Z_le_gt_dec b q) as [Hb | Hb].
    + rewrite Z.abs_neq in Hab by lia.
      assert (b = q) by lia. subst b.
      exists 0. split.
      * repeat rewrite Zlength_cons. simpl. lia.
      * unfold edge_lower. rewrite Znth0_cons.
        rewrite Znth_cons by lia. replace (0 + 1 - 1) with 0 by lia.
        rewrite Znth0_cons. rewrite Z.min_r by lia. reflexivity.
    + assert (Hy' : In y (b :: tl)).
      { simpl in Hy. destruct Hy as [-> | Hy]; [lia|exact Hy]. }
      destruct (IH b q Htail ltac:(lia) (ex_intro _ y (conj Hy' Hyq)))
        as [k [Hk Hedge]].
      exists (k + 1). split.
      * repeat rewrite Zlength_cons in *. lia.
      * unfold edge_lower in *.
        rewrite (@Znth_cons Z 0 (k + 1) a (b :: tl)) by lia.
        rewrite (@Znth_cons Z 0 (k + 1 + 1) a (b :: tl)) by lia.
        replace (k + 1 + 1 - 1) with (k + 1) by lia.
        replace (k + 1 - 1) with k by lia. exact Hedge.
Qed.
Lemma fold_prefix_alternating_empty__initialization_and_final_result :
  forall s, FoldPrefixAlternatingState s 0 0 0 0.
Proof.
  intros s.
  unfold FoldPrefixAlternatingState.
  split.
  - pose proof (Zlength_nonneg s). lia.
  - exists (0 :: nil).
    rewrite Zsublist_nil by lia.
    split.
    + unfold AlternatingWalkExtrema.
      simpl.
      repeat split; try reflexivity; try tauto.
      all: intros; repeat rewrite Zlength_cons in *;
        repeat rewrite Zlength_nil in *; try lia.
      all: change (0 <= k < 1) in H;
        assert (k = 0) by lia; subst k; reflexivity.
    + intros candidate width Hvalid.
      unfold AlternatingLabelPlacement, ValidFoldedPlacementEdges in Hvalid.
      simpl in Hvalid.
      lia.
Qed.
Lemma even_sub_eq_phase__initialization_and_final_result : forall x m,
  (Z.even (x - m) = Z.even m <-> Z.even x = true).
Proof.
  intros x m. rewrite Z.even_sub.
  destruct (Z.even x) eqn:Hx; destruct (Z.even m) eqn:Hm;
    cbn; split; congruence.
Qed.
Lemma alternating_walk_normalized_candidate__initialization_and_final_result :
  forall s boundaries cur mn mx,
  1 <= Zlength s ->
  (forall k, 0 <= k < Zlength s -> Znth k s 0 = 48 \/ Znth k s 0 = 49) ->
  AlternatingWalkExtrema s boundaries cur mn mx ->
  exists shifted,
    AlternatingLabelPlacement s shifted (mx - mn).
Proof.
  intros s boundaries cur mn mx Hs Hbinary Haw.
  unfold AlternatingWalkExtrema in Haw.
  destruct Haw as [Hlen [_ [_ [Hadj [Hpar [Hbounds [Hmn Hmx]]]]]]].
  assert (Hadj' : forall k, 0 <= k < Zlength boundaries - 1 ->
    Z.abs (Znth (k + 1) boundaries 0 - Znth k boundaries 0) = 1).
  { intros k Hk. apply Hadj. lia. }
  assert (Hmn_le_mx : mn <= mx).
  { destruct (In_Znth_index__final_result boundaries mn 0 Hmn)
      as [k [Hk Hval]].
    specialize (Hbounds k Hk). rewrite Hval in Hbounds. lia. }
  assert (Hspan_upper : mx - mn <= Zlength s).
  { pose proof (unit_walk_pair_distance__final_result boundaries mn mx
      Hadj' Hmn Hmx) as Hdist.
    rewrite Hlen in Hdist. rewrite Z.abs_neq in Hdist by lia. lia. }
  assert (Hspan_lower : 1 <= mx - mn).
  { pose proof (Hadj 0 ltac:(lia)) as Hstep.
    replace (0 + 1) with 1 in Hstep by lia.
    pose proof (Hbounds 0 ltac:(lia)) as Hb0.
    pose proof (Hbounds 1 ltac:(lia)) as Hb1.
    assert (Znth 1 boundaries 0 - Znth 0 boundaries 0 <> 0).
    { intro Heq. rewrite Heq, Z.abs_0 in Hstep. lia. }
    lia. }
  set (shifted := map (fun x : Z => x - mn) boundaries).
  assert (Hedge_shift : forall k, 0 <= k < Zlength s ->
    edge_lower shifted k = edge_lower boundaries k - mn).
  { intros k Hk. unfold shifted, edge_lower.
    rewrite (Znth_map__final_result (fun x : Z => x - mn) boundaries k 0 0)
      by lia.
    rewrite (Znth_map__final_result (fun x : Z => x - mn) boundaries (k + 1) 0 0)
      by (rewrite Hlen; lia).
    destruct (Z_le_gt_dec (Znth k boundaries 0) (Znth (k + 1) boundaries 0)).
    - rewrite !Z.min_l by lia. lia.
    - rewrite !Z.min_r by lia. lia. }
  exists shifted.
  unfold AlternatingLabelPlacement.
  split.
  - unfold ValidFoldedPlacementEdges. repeat split.
    + unfold shifted. rewrite Zlength_map__final_result. exact Hlen.
    + exact Hspan_lower.
    + exact Hspan_upper.
    + apply Forall_forall. intros z Hz.
      unfold shifted in Hz. apply in_map_iff in Hz.
      destruct Hz as [x [<- Hxin]].
      destruct (In_Znth_index__final_result boundaries x 0 Hxin)
        as [k [Hk Hkx]].
      specialize (Hbounds k Hk). rewrite Hkx in Hbounds. lia.
    + intros k Hk. unfold shifted.
      rewrite (Znth_map__final_result (fun x : Z => x - mn) boundaries k 0 0)
        by lia.
      rewrite (Znth_map__final_result (fun x : Z => x - mn) boundaries (k + 1) 0 0)
        by (rewrite Hlen; lia).
      replace ((Znth (k + 1) boundaries 0 - mn) -
        (Znth k boundaries 0 - mn)) with
        (Znth (k + 1) boundaries 0 - Znth k boundaries 0) by ring.
      apply Hadj. exact Hk.
    + intros i j Hi Hj Heq.
      rewrite Hedge_shift in Heq by exact Hi.
      rewrite Hedge_shift in Heq by exact Hj.
      assert (Heven : Z.even (edge_lower boundaries i) =
        Z.even (edge_lower boundaries j)) by (f_equal; lia).
      pose proof (Hpar i Hi) as Hpari.
      pose proof (Hpar j Hj) as Hparj.
      destruct (Hbinary i Hi) as [Hi48 | Hi49];
      destruct (Hbinary j Hj) as [Hj48 | Hj49]; try congruence.
      * exfalso. assert (Hej : Z.even (edge_lower boundaries j) = true).
        { apply (proj1 Hparj). exact Hj49. }
        rewrite <- Heven in Hej. apply (proj2 Hpari) in Hej.
        rewrite Hi48 in Hej. lia.
      * exfalso. assert (Hei : Z.even (edge_lower boundaries i) = true).
        { apply (proj1 Hpari). exact Hi49. }
        rewrite Heven in Hei. apply (proj2 Hparj) in Hei.
        rewrite Hj48 in Hei. lia.
    + intros p Hp. assert (Hq : mn <= p + mn < mx) by lia.
      destruct boundaries as [|a l].
      * rewrite Zlength_nil in Hlen. lia.
      * assert (Hcross : exists k,
          0 <= k < Zlength (a :: l) - 1 /\
          edge_lower (a :: l) k = p + mn).
        { destruct (Z_le_gt_dec a (p + mn)) as [Ha | Ha].
          - apply (unit_walk_cross_up__final_result a l (p + mn)).
            + exact Hadj'.
            + exact Ha.
            + exists mx. split; [exact Hmx | lia].
          - apply (unit_walk_cross_down__final_result a l (p + mn)).
            + exact Hadj'.
            + lia.
            + exists mn. split; [exact Hmn | lia]. }
        destruct Hcross as [k [Hk Hedge]]. exists k. split.
        -- simpl in Hlen. lia.
        -- rewrite Hedge_shift by (simpl in Hlen; lia).
           rewrite Hedge. lia.
  - exists (Z.even mn). intros k Hk.
    rewrite Hedge_shift by exact Hk.
    rewrite even_sub_eq_phase__initialization_and_final_result.
    apply Hpar. exact Hk.
Qed.
Lemma fold_prefix_alternating_to_spec__initialization_and_final_result :
  forall s i cur mn mx,
  i = Zlength s ->
  1 <= Zlength s ->
  (forall k, 0 <= k < Zlength s -> Znth k s 0 = 48 \/ Znth k s 0 = 49) ->
  FoldPrefixAlternatingState s i cur mn mx ->
  SpecAlternatingEdges s (mx - mn).
Proof.
  intros s i cur mn mx Hi Hs Hbinary Hstate.
  unfold FoldPrefixAlternatingState in Hstate.
  destruct Hstate as [_ [boundaries [Hwalk Hleast]]].
  assert (Hsub : sublist 0 i s = s).
  { apply sublist_self. exact Hi. }
  rewrite Hsub in Hwalk, Hleast.
  destruct (alternating_walk_normalized_candidate__initialization_and_final_result
    s boundaries cur mn mx Hs Hbinary Hwalk) as [shifted Hcandidate].
  unfold SpecAlternatingEdges, min_value_of_subset, min_object_of_subset.
  exists (shifted, mx - mn). split.
  - split.
    + exact Hcandidate.
    + intros [candidate width] Hvalid. simpl.
      apply Hleast with (candidate := candidate). exact Hvalid.
  - reflexivity.
Qed.
