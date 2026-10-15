Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Signature: solve_case(k:Z,slogan:list Z)->list(Z*Z). An action (d,x) has
   d=-1/1 for a ladder move and d=0 for printing character x. Any shortest
   action sequence that prints every square correctly is accepted. *)
Definition ValidPlan (k : Z) (s : list Z) (plan : list (Z*Z)) : Prop :=
  exists pos : list Z,
    Zlength pos = Zlength plan + 1 /\ Znth 0 pos 0 = k /\
    (forall j, 0 <= j < Zlength plan ->
      let '(d,x) := Znth j plan (0,0) in
      ((d = -1 \/ d = 1) /\ Znth (j + 1) pos 0 = Znth j pos 0 + d /\ x = 0 \/
       d = 0 /\ Znth (j + 1) pos 0 = Znth j pos 0)) /\
    (forall j, 0 <= j < Zlength pos -> 1 <= Znth j pos 0 <= Zlength s) /\
    (forall i, 0 <= i < Zlength s -> exists j,
       0 <= j < Zlength plan /\ Znth j plan (0,0)=(0,Znth i s 0) /\
       Znth j pos 0 = i + 1).

Definition Pre (k : Z) (s : list Z) : Prop :=
  (* Every clause below is stated explicitly in the P010 solver Require, which
     therefore omits the Pre(...) call:
       1 <= k <= Zlength s /\
       1 <= Zlength s <= 100 /\
       Forall (fun c =>
         65 <= c <= 90 \/ 48 <= c <= 57 \/
         c = 46 \/ c = 33 \/ c = 44 \/ c = 63) s. *)
  True.
Definition Spec (k : Z) (s : list Z) (out : list (Z*Z)) : Prop :=
  min_object_of_subset Z.le (ValidPlan k s) (fun ys => Zlength ys) out.

Definition ActionBytes (action : Z * Z) (bytes : list Z) : Prop :=
  let '(d, x) := action in
  (d = -1 /\ x = 0 /\ bytes = [76; 69; 70; 84; 0]) \/
  (d = 1 /\ x = 0 /\ bytes = [82; 73; 71; 72; 84; 0]) \/
  (d = 0 /\ bytes = [80; 82; 73; 78; 84; 32; x; 0]).

Definition LeftAction : Z * Z := (-1, 0).
Definition RightAction : Z * Z := (1, 0).
Definition PrintAction (x : Z) : Z * Z := (0, x).

Definition LeftWalkPlan (k p : Z) : list (Z * Z) :=
  repeat LeftAction (Z.to_nat (k - p)).

Definition RightWalkPlan (k p : Z) : list (Z * Z) :=
  repeat RightAction (Z.to_nat (p - k)).

Definition ForwardSweepPlan (s : list Z) (next : Z) : list (Z * Z) :=
  flat_map (fun p =>
    PrintAction (Znth (p - 1) s 0) ::
    if Z_lt_dec p (Zlength s) then RightAction :: nil else nil)
    (Zrange 1 next).

Definition BackwardSweepPlan (s : list Z) (next : Z) : list (Z * Z) :=
  flat_map (fun p =>
    PrintAction (Znth (p - 1) s 0) ::
    if Z_lt_dec 1 p then LeftAction :: nil else nil)
    (rev (Zrange (next + 1) (Zlength s + 1))).

Definition LeftFirstPlan (k : Z) (s : list Z) : list (Z * Z) :=
  LeftWalkPlan k 1 ++ ForwardSweepPlan s (Zlength s + 1).

Definition RightFirstPlan (k : Z) (s : list Z) : list (Z * Z) :=
  RightWalkPlan k (Zlength s) ++ BackwardSweepPlan s 0.

Definition ActionSlotBridge
    (action : Z * Z) (before after : list Z) : Prop :=
  Zlength before = 8 /\
  exists bytes,
    ActionBytes action bytes /\
    after = bytes ++ sublist (Zlength bytes) 8 before.

Definition SolverOutputBridge
    (capacity : Z) (plan : list (Z * Z)) (ret : Z)
    (before after : list (list Z)) : Prop :=
  ret = Zlength plan /\
  Zlength before = capacity /\ Zlength after = capacity /\
  (forall i, 0 <= i < ret ->
    ActionSlotBridge (Znth i plan (0, 0))
      (Znth i before []) (Znth i after [])) /\
  (forall i, ret <= i < capacity -> Znth i after [] = Znth i before []).

(* The frozen definitions above deliberately state optimality over arbitrary
   action traces.  The following append-only development supplies the finite
   counting facts used by the two endpoint candidates. *)
Require Import Coq.micromega.Lia.

Definition poster_move_weight (a : Z * Z) : Z := Z.abs (fst a).
Definition poster_print_weight (a : Z * Z) : Z :=
  if Z.eq_dec (fst a) 0 then 1 else 0.

Lemma poster_abs_add__trace_count : forall x y : Z,
  Z.abs (x + y) <= Z.abs x + Z.abs y.
Proof.
  apply Z.abs_triangle.
Qed.

Lemma poster_weight_sum_nonnegative__trace_count : forall xs : list (Z * Z),
  0 <= ListLib.sum (map poster_move_weight xs).
Proof.
  induction xs as [|[d x] xs IH]; simpl; [lia|].
  change (0 <= Z.abs d + ListLib.sum (map poster_move_weight xs)).
  pose proof (Z.abs_nonneg d). lia.
Qed.

Lemma poster_print_sum_nonnegative__trace_count : forall xs : list (Z * Z),
  0 <= ListLib.sum (map poster_print_weight xs).
Proof.
  induction xs as [|[d x] xs IH]; simpl; [lia|].
  change (0 <= poster_print_weight (d, x) +
    ListLib.sum (map poster_print_weight xs)).
  destruct (Z.eq_dec d 0) as [Hd|Hd].
  - assert (Hweight : poster_print_weight (d, x) = 1).
    { subst d. reflexivity. }
    rewrite Hweight. lia.
  - assert (Hweight : poster_print_weight (d, x) = 0).
    { unfold poster_print_weight. simpl.
      destruct (Z.eq_dec d 0); [contradiction|reflexivity]. }
    rewrite Hweight. lia.
Qed.

Lemma poster_action_account__trace_count : forall xs : list (Z * Z),
  Forall (fun a => (fst a = -1) \/ (fst a = 0) \/ (fst a = 1)) xs ->
  Zlength xs =
    ListLib.sum (map poster_move_weight xs) +
    ListLib.sum (map poster_print_weight xs).
Proof.
  intros xs Hkind. induction Hkind as [|[d x] xs Hhead Htail IH].
  - reflexivity.
  - rewrite Zlength_cons.
    change (Zlength xs + 1 =
      (poster_move_weight (d, x) +
       ListLib.sum (map poster_move_weight xs)) +
      (poster_print_weight (d, x) +
       ListLib.sum (map poster_print_weight xs))).
    simpl in Hhead. destruct Hhead as [Hd|[Hd|Hd]]; subst d.
    + assert (Hm : poster_move_weight (-1, x) = 1) by reflexivity.
      assert (Hp : poster_print_weight (-1, x) = 0) by reflexivity.
      rewrite Hm, Hp. lia.
    + assert (Hm : poster_move_weight (0, x) = 0) by reflexivity.
      assert (Hp : poster_print_weight (0, x) = 1) by reflexivity.
      rewrite Hm, Hp. lia.
    + assert (Hm : poster_move_weight (1, x) = 1) by reflexivity.
      assert (Hp : poster_print_weight (1, x) = 0) by reflexivity.
      rewrite Hm, Hp. lia.
Qed.

Lemma poster_Zlength_Zrange__trace_count : forall lo hi : Z,
  lo <= hi -> Zlength (Zrange lo hi) = hi - lo.
Proof.
  intros lo hi Hle. unfold Zrange.
  rewrite Zlength_correct.
  assert (Haux : forall n low,
    length (Zrange_aux low n) = n).
  { induction n as [|n IH]; intros low; simpl; [reflexivity|].
    rewrite IH. reflexivity. }
  rewrite Haux. lia.
Qed.

Fixpoint poster_print_locations
    (plan : list (Z * Z)) (positions : list Z) : list Z :=
  match plan, positions with
  | (d, x) :: plan', p :: positions' =>
      if Z.eq_dec d 0
      then p :: poster_print_locations plan' positions'
      else poster_print_locations plan' positions'
  | _, _ => []
  end.

Lemma poster_print_locations_length__trace_count :
  forall plan positions,
    length positions = S (length plan) ->
    Z.of_nat (length (poster_print_locations plan positions)) =
      ListLib.sum (map poster_print_weight plan).
Proof.
  induction plan as [|[d x] plan IH]; intros positions Hlength.
  - destruct positions as [|p positions].
    + simpl in Hlength. discriminate.
    + destruct positions; simpl; reflexivity.
  - destruct positions as [|p positions].
    + simpl in Hlength. discriminate.
    + assert (Htail : length positions = S (length plan)) by
        (simpl in Hlength; lia).
      specialize (IH positions Htail).
      destruct (Z.eq_dec d 0) as [Hd|Hd].
      * subst d.
        change (Z.of_nat (S (length (poster_print_locations plan positions))) =
          poster_print_weight (0, x) +
          ListLib.sum (map poster_print_weight plan)).
        assert (Hp : poster_print_weight (0, x) = 1) by reflexivity.
        rewrite Hp. pose proof IH. lia.
      * assert (Hp : poster_print_weight (d, x) = 0).
        { unfold poster_print_weight. simpl.
          destruct (Z.eq_dec d 0); [contradiction|reflexivity]. }
        assert (Hlocations : poster_print_locations
          ((d, x) :: plan) (p :: positions) =
          poster_print_locations plan positions).
        { simpl. destruct (Z.eq_dec d 0); [contradiction|reflexivity]. }
        rewrite Hlocations.
        change (Z.of_nat (length (poster_print_locations plan positions)) =
          poster_print_weight (d, x) +
          ListLib.sum (map poster_print_weight plan)).
        rewrite Hp. pose proof IH. lia.
Qed.

Lemma poster_print_location_of_slot__trace_count :
  forall plan positions (j : nat),
    length positions = S (length plan) ->
    (j < length plan)%nat ->
    fst (nth j plan (0, 0)) = 0 ->
    In (nth j positions 0) (poster_print_locations plan positions).
Proof.
  induction plan as [|[d x] plan IH]; intros positions [|j] Hlength Hj Hprint.
  - simpl in Hj. lia.
  - simpl in Hj. lia.
  - destruct positions as [|p positions].
    + simpl in Hlength. discriminate.
    + simpl in Hprint. subst d. simpl. left. reflexivity.
  - destruct positions as [|p positions].
    + simpl in Hlength. discriminate.
    + assert (Htail : length positions = S (length plan)) by
        (simpl in Hlength; lia).
      assert (Hjtail : (j < length plan)%nat) by (simpl in Hj; lia).
      simpl in Hprint.
      specialize (IH positions j Htail Hjtail Hprint).
      simpl.
      destruct (Z.eq_dec d 0); simpl; try right; exact IH.
Qed.

Definition PosterTraceSteps
    (plan : list (Z * Z)) (positions : list Z) : Prop :=
  length positions = S (length plan) /\
  forall j : nat, (j < length plan)%nat ->
    Z.abs (nth (S j) positions 0 - nth j positions 0) =
      poster_move_weight (nth j plan (0, 0)).

Lemma poster_trace_distance_from_start__trace_count :
  forall plan positions,
    PosterTraceSteps plan positions ->
    forall q : nat, (q <= length plan)%nat ->
      Z.abs (nth q positions 0 - nth 0 positions 0) <=
        ListLib.sum (map poster_move_weight (firstn q plan)).
Proof.
  induction plan as [|[d x] plan IH]; intros positions Htrace q Hq.
  - destruct Htrace as [Hlength _].
    destruct positions as [|p positions].
    + simpl in Hlength. discriminate.
    + destruct positions; simpl in Hlength |- *; [|lia].
      apply Nat.le_0_r in Hq. subst q.
      rewrite Z.sub_diag. simpl. reflexivity.
  - destruct Htrace as [Hlength Hsteps].
    destruct positions as [|p0 positions].
    + simpl in Hlength. discriminate.
    + destruct positions as [|p1 positions].
      * simpl in Hlength. discriminate.
      * assert (Htail_length : length (p1 :: positions) =
          S (length plan)).
        { simpl in Hlength. injection Hlength as Hlength.
          simpl. rewrite Hlength. reflexivity. }
        assert (Htail_steps : forall j : nat, (j < length plan)%nat ->
          Z.abs (nth (S j) (p1 :: positions) 0 -
                 nth j (p1 :: positions) 0) =
          poster_move_weight (nth j plan (0, 0))).
        { intros j Hj.
          specialize (Hsteps (S j)).
          simpl in Hsteps. apply Hsteps. simpl. lia. }
        destruct q as [|q].
        { simpl. rewrite Z.sub_diag. simpl. lia. }
        assert (Hqtail : (q <= length plan)%nat) by (simpl in Hq; lia).
        specialize (IH (p1 :: positions)
          (conj Htail_length Htail_steps) q Hqtail).
        specialize (Hsteps 0%nat ltac:(simpl; lia)). simpl in Hsteps.
        change (Z.abs (nth q (p1 :: positions) 0 - p0) <=
          poster_move_weight (d, x) +
          ListLib.sum (map poster_move_weight (firstn q plan))).
        replace (nth q (p1 :: positions) 0 - p0) with
          ((nth q (p1 :: positions) 0 - p1) + (p1 - p0)) by lia.
        eapply Z.le_trans.
        { apply Z.abs_triangle. }
        change (Z.abs (nth q (p1 :: positions) 0 - p1) <=
          ListLib.sum (map poster_move_weight (firstn q plan))) in IH.
        rewrite Hsteps. lia.
Qed.

Lemma poster_Znth_of_nat__trace_count :
  forall {A : Type} (d : A) (xs : list A) (j : nat),
    Znth (Z.of_nat j) xs d = nth j xs d.
Proof.
  intros. unfold Znth. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma poster_trace_steps_skip__trace_count :
  forall plan positions (lo : nat),
    PosterTraceSteps plan positions ->
    (lo <= length plan)%nat ->
    PosterTraceSteps (skipn lo plan) (skipn lo positions).
Proof.
  intros plan positions lo [Hlength Hsteps] Hlo. split.
  - rewrite !length_skipn. lia.
  - intros j Hj. rewrite !nth_skipn.
    replace (lo + S j)%nat with (S (lo + j))%nat by lia.
    apply Hsteps. rewrite length_skipn in Hj. lia.
Qed.

Lemma poster_trace_distance_between__trace_count :
  forall plan positions (lo hi : nat),
    PosterTraceSteps plan positions ->
    (lo <= hi <= length plan)%nat ->
    Z.abs (nth hi positions 0 - nth lo positions 0) <=
      ListLib.sum
        (map poster_move_weight (firstn (hi - lo) (skipn lo plan))).
Proof.
  intros plan positions lo hi Htrace [Hlo Hhi].
  pose proof (poster_trace_steps_skip__trace_count
    plan positions lo Htrace ltac:(lia)) as Hskip.
  pose proof (poster_trace_distance_from_start__trace_count
    (skipn lo plan) (skipn lo positions) Hskip (hi - lo)
    ltac:(rewrite length_skipn; lia)) as Hdistance.
  rewrite !nth_skipn in Hdistance.
  replace (lo + (hi - lo))%nat with hi in Hdistance by lia.
  rewrite Nat.add_0_r in Hdistance.
  exact Hdistance.
Qed.

Lemma valid_plan_trace_steps__trace_count :
  forall k s plan,
    ValidPlan k s plan ->
    exists positions,
      PosterTraceSteps plan positions /\
      nth 0 positions 0 = k.
Proof.
  intros k s plan Hvalid.
  unfold ValidPlan in Hvalid.
  destruct Hvalid as [positions [Hlength [Hstart [Hsteps _]]]].
  exists positions. split.
  - split.
    + rewrite !Zlength_correct in Hlength.
      replace (Z.of_nat (length plan) + 1) with
        (Z.of_nat (length plan) + Z.of_nat 1) in Hlength by reflexivity.
      rewrite <- Nat2Z.inj_add in Hlength.
      simpl in Hlength.
      apply Nat2Z.inj in Hlength.
      rewrite Nat.add_1_r in Hlength. exact Hlength.
    + intros j Hj.
      assert (HjZ : 0 <= Z.of_nat j < Zlength plan).
      { rewrite Zlength_correct. lia. }
      specialize (Hsteps (Z.of_nat j) HjZ).
      replace (Z.of_nat j + 1) with (Z.of_nat (S j))
        in Hsteps by lia.
      rewrite !poster_Znth_of_nat__trace_count in Hsteps.
      destruct (nth j plan (0, 0)) as [d x].
      simpl in Hsteps |- *.
      destruct Hsteps as [[Hd [Hnext Hx]]|[Hd Hnext]].
      * assert (Hdiff : nth (S j) positions 0 - nth j positions 0 = d)
          by lia.
        unfold poster_move_weight. simpl. rewrite Hdiff. reflexivity.
      * assert (Hdiff : nth (S j) positions 0 - nth j positions 0 = d)
          by lia.
        unfold poster_move_weight. simpl. rewrite Hdiff. reflexivity.
  - change (Znth (Z.of_nat 0%nat) positions 0 = k) in Hstart.
    rewrite poster_Znth_of_nat__trace_count in Hstart.
    exact Hstart.
Qed.

Lemma valid_plan_action_kinds__trace_count :
  forall k s plan,
    ValidPlan k s plan ->
    Forall (fun a => (fst a = -1) \/ (fst a = 0) \/ (fst a = 1)) plan.
Proof.
  intros k s plan Hvalid.
  unfold ValidPlan in Hvalid.
  destruct Hvalid as [positions [Hlength [Hstart [Hsteps _]]]].
  apply (proj2 (Forall_Znth _ (0, 0) plan)).
  intros j Hj.
  specialize (Hsteps j Hj).
  destruct (Znth j plan (0, 0)) as [d x].
  simpl in Hsteps |- *.
  destruct Hsteps as [[Hd _]|[Hd _]]; tauto.
Qed.

Lemma valid_plan_print_lower_bound__trace_count :
  forall k s plan,
    ValidPlan k s plan ->
    Zlength s <= ListLib.sum (map poster_print_weight plan).
Proof.
  intros k s plan Hvalid.
  unfold ValidPlan in Hvalid.
  destruct Hvalid as [positions
    [Hlength [Hstart [Hsteps [Hbounds Hprints]]]]].
  assert (Hlength_nat : length positions = S (length plan)).
  { rewrite !Zlength_correct in Hlength.
    replace (Z.of_nat (length plan) + 1) with
      (Z.of_nat (length plan) + Z.of_nat 1) in Hlength by reflexivity.
    rewrite <- Nat2Z.inj_add in Hlength.
    simpl in Hlength. apply Nat2Z.inj in Hlength.
    rewrite Nat.add_1_r in Hlength. exact Hlength. }
  assert (Hincl : incl (Zrange 1 (Zlength s + 1))
    (poster_print_locations plan positions)).
  {
    intros q Hq.
    rewrite <- In_Zrange in Hq.
    set (i := q - 1).
    assert (Hi : 0 <= i < Zlength s) by (unfold i; lia).
    destruct (Hprints i Hi) as [j [Hj [Haction Hposition]]].
    set (j_nat := Z.to_nat j).
    assert (Hj_nat : (j_nat < length plan)%nat).
    { assert (Hplan : Z.to_nat (Zlength plan) = length plan).
      { rewrite Zlength_correct. rewrite Nat2Z.id. reflexivity. }
      unfold j_nat. rewrite <- Hplan.
      apply Z2Nat.inj_lt; lia. }
    assert (Haction_nat :
      fst (nth j_nat plan (0, 0)) = 0).
    {
      assert (Hjcast : j = Z.of_nat j_nat).
      { unfold j_nat. rewrite Z2Nat.id by lia. reflexivity. }
      rewrite Hjcast in Haction.
      rewrite poster_Znth_of_nat__trace_count in Haction.
      rewrite Haction. reflexivity.
    }
    assert (Hposition_nat : nth j_nat positions 0 = q).
    {
      assert (Hjcast : j = Z.of_nat j_nat).
      { unfold j_nat. rewrite Z2Nat.id by lia. reflexivity. }
      rewrite Hjcast in Hposition.
      rewrite poster_Znth_of_nat__trace_count in Hposition.
      assert (Hiq : i + 1 = q) by (unfold i; lia).
      rewrite Hiq in Hposition. exact Hposition.
    }
    rewrite <- Hposition_nat.
    eapply poster_print_location_of_slot__trace_count; eauto.
  }
  pose proof (NoDup_incl_length (NoDup_Zrange 1 (Zlength s + 1)) Hincl)
    as Hcard.
  apply Nat2Z.inj_le in Hcard.
  assert (Hrange :
    Z.of_nat (length (Zrange 1 (Zlength s + 1))) = Zlength s).
  { pose proof (Zlength_nonneg s).
    rewrite <- Zlength_correct.
    rewrite poster_Zlength_Zrange__trace_count by lia. lia. }
  pose proof (poster_print_locations_length__trace_count
    plan positions Hlength_nat) as Hprint_length.
  rewrite Hrange, Hprint_length in Hcard.
  exact Hcard.
Qed.

Lemma poster_trace_steps_from_valid_witness__trace_count :
  forall plan positions,
    Zlength positions = Zlength plan + 1 ->
    (forall j, 0 <= j < Zlength plan ->
      let '(d, x) := Znth j plan (0, 0) in
      ((d = -1 \/ d = 1) /\
       Znth (j + 1) positions 0 = Znth j positions 0 + d /\ x = 0 \/
       d = 0 /\ Znth (j + 1) positions 0 = Znth j positions 0)) ->
    PosterTraceSteps plan positions.
Proof.
  intros plan positions Hlength Hsteps. split.
  - rewrite !Zlength_correct in Hlength.
    replace (Z.of_nat (length plan) + 1) with
      (Z.of_nat (length plan) + Z.of_nat 1) in Hlength by reflexivity.
    rewrite <- Nat2Z.inj_add in Hlength.
    simpl in Hlength. apply Nat2Z.inj in Hlength.
    rewrite Nat.add_1_r in Hlength. exact Hlength.
  - intros j Hj.
    assert (HjZ : 0 <= Z.of_nat j < Zlength plan).
    { rewrite Zlength_correct. lia. }
    specialize (Hsteps (Z.of_nat j) HjZ).
    replace (Z.of_nat j + 1) with (Z.of_nat (S j))
      in Hsteps by lia.
    rewrite !poster_Znth_of_nat__trace_count in Hsteps.
    destruct (nth j plan (0, 0)) as [d x].
    simpl in Hsteps |- *.
    destruct Hsteps as [[Hd [Hnext Hx]]|[Hd Hnext]].
    + assert (Hdiff : nth (S j) positions 0 - nth j positions 0 = d)
        by lia.
      unfold poster_move_weight. simpl. rewrite Hdiff. reflexivity.
    + assert (Hdiff : nth (S j) positions 0 - nth j positions 0 = d)
        by lia.
      unfold poster_move_weight. simpl. rewrite Hdiff. reflexivity.
Qed.

Lemma poster_move_sum_split__trace_count :
  forall plan (lo hi : nat),
    (lo <= hi <= length plan)%nat ->
    ListLib.sum (map poster_move_weight plan) =
      ListLib.sum (map poster_move_weight (firstn lo plan)) +
      ListLib.sum
        (map poster_move_weight (firstn (hi - lo) (skipn lo plan)) ) +
      ListLib.sum (map poster_move_weight (skipn hi plan)).
Proof.
  intros plan lo hi [Hlo Hhi].
  assert (Hdecompose :
    plan = firstn lo plan ++
      firstn (hi - lo) (skipn lo plan) ++ skipn hi plan).
  {
    assert (Htail :
      skipn lo plan = firstn (hi - lo) (skipn lo plan) ++ skipn hi plan).
    {
      transitivity
        (firstn (hi - lo) (skipn lo plan) ++
         skipn (hi - lo) (skipn lo plan)).
      - symmetry. apply firstn_skipn.
      - rewrite skipn_skipn.
        replace (hi - lo + lo)%nat with hi by lia.
        reflexivity.
    }
    transitivity (firstn lo plan ++ skipn lo plan).
    - symmetry. apply firstn_skipn.
    - rewrite Htail at 1. rewrite app_assoc. reflexivity.
  }
  rewrite Hdecompose at 1.
  repeat rewrite map_app.
  repeat rewrite ListLib.sum_app.
  lia.
Qed.

Lemma valid_plan_move_lower_bound__trace_count :
  forall k s plan,
    1 <= k <= Zlength s ->
    1 <= Zlength s <= 100 ->
    ValidPlan k s plan ->
    (Zlength s - 1 + Z.min (k - 1) (Zlength s - k) <=
      ListLib.sum (map poster_move_weight plan)).
Proof.
  intros k s plan Hk Hn Hvalid.
  unfold ValidPlan in Hvalid.
  destruct Hvalid as [positions
    [Hlength [Hstart [Hsteps [Hbounds Hprints]]]]].
  pose proof (poster_trace_steps_from_valid_witness__trace_count
    plan positions Hlength Hsteps) as Htrace.
  assert (Hstart_nat : nth 0%nat positions 0 = k).
  { change (Znth (Z.of_nat 0%nat) positions 0 = k) in Hstart.
    rewrite poster_Znth_of_nat__trace_count in Hstart. exact Hstart. }
  destruct (Hprints 0 ltac:(lia)) as
    [left_z [Hleft_range [Hleft_action Hleft_pos]]].
  destruct (Hprints (Zlength s - 1) ltac:(lia)) as
    [right_z [Hright_range [Hright_action Hright_pos]]].
  set (left_nat := Z.to_nat left_z).
  set (right_nat := Z.to_nat right_z).
  assert (Hleft_nat : (left_nat < length plan)%nat).
  {
    assert (Hplan : Z.to_nat (Zlength plan) = length plan).
    { rewrite Zlength_correct. rewrite Nat2Z.id. reflexivity. }
    unfold left_nat. rewrite <- Hplan.
    apply Z2Nat.inj_lt; lia.
  }
  assert (Hright_nat : (right_nat < length plan)%nat).
  {
    assert (Hplan : Z.to_nat (Zlength plan) = length plan).
    { rewrite Zlength_correct. rewrite Nat2Z.id. reflexivity. }
    unfold right_nat. rewrite <- Hplan.
    apply Z2Nat.inj_lt; lia.
  }
  assert (Hleft_cast : left_z = Z.of_nat left_nat).
  { unfold left_nat. rewrite Z2Nat.id by lia. reflexivity. }
  assert (Hright_cast : right_z = Z.of_nat right_nat).
  { unfold right_nat. rewrite Z2Nat.id by lia. reflexivity. }
  assert (Hleft_position : nth left_nat positions 0 = 1).
  {
    rewrite Hleft_cast in Hleft_pos.
    rewrite poster_Znth_of_nat__trace_count in Hleft_pos.
    lia.
  }
  assert (Hright_position : nth right_nat positions 0 = Zlength s).
  {
    rewrite Hright_cast in Hright_pos.
    rewrite poster_Znth_of_nat__trace_count in Hright_pos.
    lia.
  }
  destruct (le_dec left_nat right_nat) as [Hlr|Hrl].
  - pose proof (poster_trace_distance_from_start__trace_count
      plan positions Htrace left_nat ltac:(lia)) as Hto_left.
    pose proof (poster_trace_distance_between__trace_count
      plan positions left_nat right_nat Htrace
      ltac:(split; lia)) as Hacross.
    rewrite Hleft_position, Hstart_nat in Hto_left.
    rewrite Hright_position, Hleft_position in Hacross.
    assert (Hto_left' :
      k - 1 <=
        ListLib.sum (map poster_move_weight (firstn left_nat plan))).
    { rewrite Z.abs_neq in Hto_left by lia. lia. }
    assert (Hacross' :
      Zlength s - 1 <=
        ListLib.sum
          (map poster_move_weight
            (firstn (right_nat - left_nat) (skipn left_nat plan)))).
    { rewrite Z.abs_eq in Hacross by lia. exact Hacross. }
    pose proof (poster_move_sum_split__trace_count
      plan left_nat right_nat ltac:(split; lia)) as Hsplit.
    pose proof (poster_weight_sum_nonnegative__trace_count
      (skipn right_nat plan)) as Htail_nonnegative.
    destruct (Z_le_dec (k - 1) (Zlength s - k)) as [Hmin|Hmin].
    + rewrite Z.min_l by lia. lia.
    + rewrite Z.min_r by lia. lia.
  - assert (Hrl' : (right_nat <= left_nat)%nat) by lia.
    pose proof (poster_trace_distance_from_start__trace_count
      plan positions Htrace right_nat ltac:(lia)) as Hto_right.
    pose proof (poster_trace_distance_between__trace_count
      plan positions right_nat left_nat Htrace
      ltac:(split; lia)) as Hacross.
    rewrite Hright_position, Hstart_nat in Hto_right.
    rewrite Hleft_position, Hright_position in Hacross.
    assert (Hto_right' :
      Zlength s - k <=
        ListLib.sum (map poster_move_weight (firstn right_nat plan))).
    { rewrite Z.abs_eq in Hto_right by lia. exact Hto_right. }
    assert (Hacross' :
      Zlength s - 1 <=
        ListLib.sum
          (map poster_move_weight
            (firstn (left_nat - right_nat) (skipn right_nat plan)))).
    { rewrite Z.abs_neq in Hacross by lia. lia. }
    pose proof (poster_move_sum_split__trace_count
      plan right_nat left_nat ltac:(split; lia)) as Hsplit.
    pose proof (poster_weight_sum_nonnegative__trace_count
      (skipn left_nat plan)) as Htail_nonnegative.
    destruct (Z_le_dec (k - 1) (Zlength s - k)) as [Hmin|Hmin].
    + rewrite Z.min_l by lia. lia.
    + rewrite Z.min_r by lia. lia.
Qed.

(* A route carries the concrete position trace and the (position, character)
   facts produced by its print actions.  It is the constructive counterpart of
   the arbitrary trace used in the lower-bound argument above. *)
Inductive PosterRoute (n : Z) :
    Z -> list (Z * Z) -> Z -> list Z -> list (Z * Z) -> Prop :=
| poster_route_nil : forall p,
    1 <= p <= n ->
    PosterRoute n p [] p [p] []
| poster_route_move : forall p d rest q positions prints,
    1 <= p <= n -> (d = -1 \/ d = 1) -> 1 <= p + d <= n ->
    PosterRoute n (p + d) rest q positions prints ->
    PosterRoute n p ((d, 0) :: rest) q (p :: positions) prints
| poster_route_print : forall p x rest q positions prints,
    1 <= p <= n ->
    PosterRoute n p rest q positions prints ->
    PosterRoute n p ((0, x) :: rest) q (p :: positions) ((p, x) :: prints).

Lemma poster_route_app__trace_count : forall n p plan1 q pos1 prints1
    plan2 r pos2 prints2,
  PosterRoute n p plan1 q pos1 prints1 ->
  PosterRoute n q plan2 r pos2 prints2 ->
  exists positions,
    PosterRoute n p (plan1 ++ plan2) r positions (prints1 ++ prints2).
Proof.
  intros n p plan1 q pos1 prints1 plan2 r pos2 prints2 Hroute1 Hroute2.
  revert plan2 r pos2 prints2 Hroute2.
  induction Hroute1; intros plan2 r pos2 prints2 Hroute2.
  - simpl. exists pos2. exact Hroute2.
  - simpl. destruct (IHHroute1 _ _ _ _ Hroute2) as [tail Htail].
    eexists. econstructor; eauto.
  - simpl. destruct (IHHroute1 _ _ _ _ Hroute2) as [tail Htail].
    eexists. econstructor; eauto.
Qed.

Lemma poster_route_length__trace_count : forall n p plan q positions prints,
  PosterRoute n p plan q positions prints ->
  Zlength positions = Zlength plan + 1.
Proof.
  intros n p plan q positions prints Hroute.
  induction Hroute.
  - reflexivity.
  - rewrite !Zlength_cons, IHHroute. lia.
  - rewrite !Zlength_cons, IHHroute. lia.
Qed.

Lemma poster_route_start__trace_count : forall n p plan q positions prints,
  PosterRoute n p plan q positions prints ->
  Znth 0 positions 0 = p.
Proof.
  intros n p plan q positions prints Hroute.
  destruct Hroute; reflexivity.
Qed.

Lemma poster_route_bounds__trace_count : forall n p plan q positions prints j,
  PosterRoute n p plan q positions prints ->
  0 <= j < Zlength positions ->
  1 <= Znth j positions 0 <= n.
Proof.
  intros n p plan q positions prints j Hroute.
  revert j. induction Hroute; intros j Hj.
  - rewrite Zlength_cons in Hj. change (0 <= j < 1) in Hj.
    assert (j = 0) by lia. subst j. exact H.
  - destruct (Z.eq_dec j 0) as [->|Hj0].
    + rewrite Znth0_cons. exact H.
    + rewrite Znth_cons by lia. apply (IHHroute (j - 1)).
      rewrite Zlength_cons in Hj. lia.
  - destruct (Z.eq_dec j 0) as [->|Hj0].
    + rewrite Znth0_cons. exact H.
    + rewrite Znth_cons by lia. apply (IHHroute (j - 1)).
      rewrite Zlength_cons in Hj. lia.
Qed.

Lemma poster_route_steps__trace_count : forall n p plan q positions prints j,
  PosterRoute n p plan q positions prints ->
  0 <= j < Zlength plan ->
  let '(d, x) := Znth j plan (0, 0) in
    ((d = -1 \/ d = 1) /\
     Znth (j + 1) positions 0 = Znth j positions 0 + d /\ x = 0 \/
     d = 0 /\ Znth (j + 1) positions 0 = Znth j positions 0).
Proof.
  intros n p plan q positions prints j Hroute.
  revert j. induction Hroute; intros j Hj.
  - rewrite Zlength_nil in Hj. lia.
  - destruct (Z.eq_dec j 0) as [->|Hj0].
    + assert (Hnext : Znth 0 positions 0 = p + d).
      { apply poster_route_start__trace_count with
          (n := n) (plan := rest) (q := q) (prints := prints).
        exact Hroute. }
      destruct positions as [|p' positions].
      { change (0 = p + d) in Hnext. lia. }
      rewrite Znth0_cons in Hnext.
      change ((d = -1 \/ d = 1) /\
        Znth 1 (p :: p' :: positions) 0 =
          Znth 0 (p :: p' :: positions) 0 + d /\ 0 = 0 \/
        d = 0 /\ Znth 1 (p :: p' :: positions) 0 =
          Znth 0 (p :: p' :: positions) 0).
      rewrite Znth0_cons. rewrite Znth_cons by lia. rewrite Znth0_cons.
      left. repeat split; lia.
    + rewrite !Znth_cons by lia.
      replace (j + 1 - 1) with (j - 1 + 1) by lia.
      apply (IHHroute (j - 1)).
      rewrite Zlength_cons in Hj. lia.
  - destruct (Z.eq_dec j 0) as [->|Hj0].
    + assert (Hnext : Znth 0 positions 0 = p).
      { apply poster_route_start__trace_count with
          (n := n) (plan := rest) (q := q) (prints := prints).
        exact Hroute. }
      destruct positions as [|p' positions].
      { change (0 = p) in Hnext. lia. }
      rewrite Znth0_cons in Hnext.
      change ((0 = -1 \/ 0 = 1) /\
        Znth 1 (p :: p' :: positions) 0 =
          Znth 0 (p :: p' :: positions) 0 + 0 /\ x = 0 \/
        0 = 0 /\ Znth 1 (p :: p' :: positions) 0 =
          Znth 0 (p :: p' :: positions) 0).
      rewrite Znth0_cons. rewrite Znth_cons by lia. rewrite Znth0_cons.
      right. split; lia.
    + rewrite !Znth_cons by lia.
      replace (j + 1 - 1) with (j - 1 + 1) by lia.
      apply (IHHroute (j - 1)).
      rewrite Zlength_cons in Hj. lia.
Qed.

Lemma poster_route_print_slot__trace_count : forall n p plan q positions prints a,
  PosterRoute n p plan q positions prints ->
  In a prints ->
  exists j, 0 <= j < Zlength plan /\
    Znth j plan (0, 0) = (0, snd a) /\ Znth j positions 0 = fst a.
Proof.
  intros n p plan q positions prints a Hroute.
  induction Hroute; intros Hin.
  - contradiction.
  - apply IHHroute in Hin as [j [Hj [Haction Hpos]]].
    exists (j + 1). split.
    + rewrite Zlength_cons. lia.
    + rewrite !Znth_cons by lia.
      replace (j + 1 - 1) with j by lia.
      exact (conj Haction Hpos).
  - simpl in Hin. destruct Hin as [Ha|Hin].
    + subst a. exists 0. split.
      * rewrite Zlength_cons. pose proof (Zlength_nonneg rest). lia.
      * rewrite !Znth0_cons. split; reflexivity.
    + apply IHHroute in Hin as [j [Hj [Haction Hpos]]].
      exists (j + 1). split.
      * rewrite Zlength_cons. lia.
      * rewrite !Znth_cons by lia.
        replace (j + 1 - 1) with j by lia.
        exact (conj Haction Hpos).
Qed.

Lemma poster_route_valid__trace_count : forall s n p plan q positions prints,
  n = Zlength s ->
  PosterRoute n p plan q positions prints ->
  (forall i, 0 <= i < Zlength s ->
    In (i + 1, Znth i s 0) prints) ->
  ValidPlan p s plan.
Proof.
  intros s n p plan q positions prints Hn Hroute Hprints.
  exists positions. split.
  - apply poster_route_length__trace_count with (n := n) (p := p)
      (q := q) (prints := prints). exact Hroute.
  - split.
    + apply poster_route_start__trace_count with (n := n) (plan := plan)
        (q := q) (prints := prints). exact Hroute.
    + split.
      * intros j Hj. eapply poster_route_steps__trace_count.
        -- exact Hroute.
        -- exact Hj.
      * split.
        -- intros j Hj. rewrite <- Hn.
           eapply poster_route_bounds__trace_count.
           ++ exact Hroute.
           ++ exact Hj.
        -- intros i Hi. eapply (poster_route_print_slot__trace_count
             n p plan q positions prints (i + 1, Znth i s 0)).
           ++ exact Hroute.
           ++ apply Hprints. exact Hi.
Qed.

Lemma poster_left_repeat_route__trace_count : forall n p m,
  1 <= p <= n -> 1 <= p - Z.of_nat m ->
  exists positions,
    PosterRoute n p (repeat LeftAction m) (p - Z.of_nat m) positions [].
Proof.
  intros n p m Hstart Hfinish.
  revert p Hstart Hfinish.
  induction m as [|m IH]; intros p Hstart Hfinish.
  - exists [p]. replace (p - Z.of_nat 0) with p by lia.
    apply poster_route_nil. exact Hstart.
  - assert (Hnext_start : 1 <= p - 1 <= n).
    { rewrite Nat2Z.inj_succ in Hfinish. lia. }
    assert (Htail_finish : 1 <= (p - 1) - Z.of_nat m).
    { rewrite Nat2Z.inj_succ in Hfinish. lia. }
    destruct (IH (p - 1) Hnext_start Htail_finish) as [positions Hroute].
    exists (p :: positions).
    replace (p - Z.of_nat (S m)) with ((p - 1) - Z.of_nat m)
      by (rewrite Nat2Z.inj_succ; lia).
    change (PosterRoute n p ((-1, 0) :: repeat LeftAction m)
      ((p - 1) - Z.of_nat m) (p :: positions) []).
    econstructor; eauto; lia.
Qed.

Definition poster_forward_piece (s : list Z) (n p : Z) : list (Z * Z) :=
  PrintAction (Znth (p - 1) s 0) ::
  if Z_lt_dec p n then RightAction :: nil else nil.

Lemma poster_forward_aux_route__trace_count : forall s n lo m,
  n = Zlength s -> 1 <= lo <= n -> lo + Z.of_nat m <= n + 1 ->
  exists q positions,
    PosterRoute n lo
      (flat_map (poster_forward_piece s n) (Zrange_aux lo m))
      q positions
      (map (fun p => (p, Znth (p - 1) s 0)) (Zrange_aux lo m)).
Proof.
  intros s n lo m Hn Hlo Hlength.
  revert lo Hlo Hlength.
  induction m as [|m IH]; intros lo Hlo Hlength.
  - exists lo, [lo]. simpl. apply poster_route_nil. exact Hlo.
  - simpl. destruct (Z_lt_dec lo n) as [Hlt|Hnlt].
    + assert (Htail_bounds : 1 <= lo + 1 <= n) by lia.
      assert (Htail_length : lo + 1 + Z.of_nat m <= n + 1).
      { rewrite Nat2Z.inj_succ in Hlength. lia. }
      destruct (IH (lo + 1) Htail_bounds Htail_length)
        as [q [positions Hroute]].
      exists q, (lo :: lo :: positions).
      change (PosterRoute n lo
        ((0, Znth (lo - 1) s 0) :: (1, 0) ::
          flat_map (poster_forward_piece s n) (Zrange_aux (lo + 1) m))
        q (lo :: lo :: positions)
        ((lo, Znth (lo - 1) s 0) ::
          map (fun p => (p, Znth (p - 1) s 0))
            (Zrange_aux (lo + 1) m))).
      econstructor; [lia|].
      econstructor; [lia|right; lia|lia|exact Hroute].
    + assert (Hlo_eq : lo = n) by lia.
      assert (Hm_zero : m = 0%nat).
      { rewrite Nat2Z.inj_succ in Hlength. lia. }
      subst m. subst lo.
      exists n, [n; n].
      change (PosterRoute n n [(0, Znth (n - 1) s 0)] n [n; n]
        [(n, Znth (n - 1) s 0)]).
      econstructor; [lia|]. apply poster_route_nil. lia.
Qed.

Lemma left_first_valid__trace_count : forall k s,
  1 <= k <= Zlength s ->
  1 <= Zlength s <= 100 ->
  ValidPlan k s (LeftFirstPlan k s).
Proof.
  intros k s Hk Hn.
  unfold LeftFirstPlan, LeftWalkPlan, ForwardSweepPlan, Zrange.
  replace (Z.to_nat (Zlength s + 1 - 1)) with (length s)
    by (rewrite Zlength_correct; lia).
  change (ValidPlan k s
    (repeat LeftAction (Z.to_nat (k - 1)) ++
     flat_map (poster_forward_piece s (Zlength s))
       (Zrange_aux 1 (length s)))).
  assert (Hleft_finish : 1 <= k - Z.of_nat (Z.to_nat (k - 1))).
  { rewrite Z2Nat.id by lia. lia. }
  destruct (poster_left_repeat_route__trace_count
    (Zlength s) k (Z.to_nat (k - 1)) Hk Hleft_finish)
    as [left_positions Hleft].
  assert (Hleft_endpoint : k - Z.of_nat (Z.to_nat (k - 1)) = 1).
  { rewrite Z2Nat.id by lia. lia. }
  rewrite Hleft_endpoint in Hleft.
  assert (Hforward_bounds : 1 <= 1 <= Zlength s) by lia.
  assert (Hforward_length : 1 + Z.of_nat (length s) <= Zlength s + 1).
  { rewrite Zlength_correct. lia. }
  destruct (poster_forward_aux_route__trace_count s (Zlength s) 1 (length s)
    eq_refl Hforward_bounds Hforward_length)
    as [q [forward_positions Hforward]].
  pose proof (poster_route_app__trace_count
    (Zlength s) k (repeat LeftAction (Z.to_nat (k - 1))) 1
    left_positions []
    (flat_map (poster_forward_piece s (Zlength s))
      (Zrange_aux 1 (length s))) q forward_positions
    (map (fun p => (p, Znth (p - 1) s 0)) (Zrange_aux 1 (length s)))
    Hleft Hforward) as Happ.
  destruct Happ as [positions Happ].
  eapply (poster_route_valid__trace_count s (Zlength s) k
    (repeat LeftAction (Z.to_nat (k - 1)) ++
     flat_map (poster_forward_piece s (Zlength s))
       (Zrange_aux 1 (length s))) q positions
    (map (fun p => (p, Znth (p - 1) s 0)) (Zrange_aux 1 (length s)))).
  - reflexivity.
  - exact Happ.
  - intros i Hi. apply in_map_iff.
    exists (i + 1). split.
    + replace (i + 1 - 1) with i by lia. reflexivity.
    + apply In_Zrange_aux. rewrite Zlength_correct in Hi. lia.
Qed.

Lemma poster_right_repeat_route__trace_count : forall n p m,
  1 <= p <= n -> p + Z.of_nat m <= n ->
  exists positions,
    PosterRoute n p (repeat RightAction m) (p + Z.of_nat m) positions [].
Proof.
  intros n p m Hstart Hfinish.
  revert p Hstart Hfinish.
  induction m as [|m IH]; intros p Hstart Hfinish.
  - exists [p]. replace (p + Z.of_nat 0) with p by lia.
    apply poster_route_nil. exact Hstart.
  - assert (Hnext_start : 1 <= p + 1 <= n).
    { rewrite Nat2Z.inj_succ in Hfinish. lia. }
    assert (Htail_finish : (p + 1) + Z.of_nat m <= n).
    { rewrite Nat2Z.inj_succ in Hfinish. lia. }
    destruct (IH (p + 1) Hnext_start Htail_finish) as [positions Hroute].
    exists (p :: positions).
    replace (p + Z.of_nat (S m)) with ((p + 1) + Z.of_nat m)
      by (rewrite Nat2Z.inj_succ; lia).
    change (PosterRoute n p ((1, 0) :: repeat RightAction m)
      ((p + 1) + Z.of_nat m) (p :: positions) []).
    econstructor; eauto; lia.
Qed.

Definition poster_backward_piece (s : list Z) (p : Z) : list (Z * Z) :=
  PrintAction (Znth (p - 1) s 0) ::
  if Z_lt_dec 1 p then LeftAction :: nil else nil.

Lemma poster_backward_piece_route__trace_count : forall s n p,
  1 <= p <= n ->
  exists positions,
    PosterRoute n p (poster_backward_piece s p)
      (if Z_lt_dec 1 p then p - 1 else p) positions
      [(p, Znth (p - 1) s 0)].
Proof.
  intros s n p Hbounds.
  unfold poster_backward_piece.
  destruct (Z_lt_dec 1 p) as [Hlt|Hnlt].
  - exists [p; p; p - 1].
    change (PosterRoute n p [(0, Znth (p - 1) s 0); (-1, 0)]
      (p - 1) [p; p; p - 1] [(p, Znth (p - 1) s 0)]).
    econstructor; [exact Hbounds|].
    econstructor; [lia|left; lia|lia|].
    apply poster_route_nil. lia.
  - exists [p; p].
    change (PosterRoute n p [(0, Znth (p - 1) s 0)] p
      [p; p] [(p, Znth (p - 1) s 0)]).
    econstructor; [exact Hbounds|].
    apply poster_route_nil. lia.
Qed.

Lemma poster_backward_aux_route__trace_count : forall s n lo m,
  1 <= lo -> lo + Z.of_nat m <= n ->
  exists positions,
    PosterRoute n (lo + Z.of_nat m)
      (flat_map (poster_backward_piece s)
        (rev (Zrange_aux lo (S m))))
      (if Z_lt_dec 1 lo then lo - 1 else lo) positions
      (map (fun p => (p, Znth (p - 1) s 0))
        (rev (Zrange_aux lo (S m)))).
Proof.
  intros s n lo m Hlo Hlength.
  revert lo Hlo Hlength.
  induction m as [|m IH]; intros lo Hlo Hlength.
  - replace (lo + Z.of_nat 0) with lo by lia.
    simpl. destruct (Z_lt_dec 1 lo) as [Hlt|Hnlt].
    + exists [lo; lo; lo - 1].
      change (PosterRoute n lo [(0, Znth (lo - 1) s 0); (-1, 0)]
        (lo - 1) [lo; lo; lo - 1] [(lo, Znth (lo - 1) s 0)]).
      econstructor; [lia|].
      econstructor; [lia|left; lia|lia|]. apply poster_route_nil. lia.
    + exists [lo; lo].
      change (PosterRoute n lo [(0, Znth (lo - 1) s 0)] lo
        [lo; lo] [(lo, Znth (lo - 1) s 0)]).
      econstructor; [lia|]. apply poster_route_nil. lia.
  - change (exists positions,
      PosterRoute n (lo + Z.of_nat (S m))
        (flat_map (poster_backward_piece s)
          (rev (Zrange_aux (lo + 1) (S m)) ++ [lo]))
        (if Z_lt_dec 1 lo then lo - 1 else lo) positions
        (map (fun p => (p, Znth (p - 1) s 0))
          (rev (Zrange_aux (lo + 1) (S m)) ++ [lo]))).
    rewrite flat_map_app, map_app.
    assert (Htail_low : 1 <= lo + 1) by lia.
    assert (Htail_length : lo + 1 + Z.of_nat m <= n).
    { rewrite Nat2Z.inj_succ in Hlength. lia. }
    destruct (IH (lo + 1) Htail_low Htail_length) as [tail_positions Htail].
    assert (Htail_end :
      (if Z_lt_dec 1 (lo + 1) then lo + 1 - 1 else lo + 1) = lo).
    { destruct (Z_lt_dec 1 (lo + 1)); lia. }
    rewrite Htail_end in Htail.
    assert (Hlast_bounds : 1 <= lo <= n).
    { rewrite Nat2Z.inj_succ in Hlength. lia. }
    destruct (poster_backward_piece_route__trace_count s n lo Hlast_bounds)
      as [last_positions Hlast].
    pose proof (poster_route_app__trace_count n
      (lo + 1 + Z.of_nat m)
      (flat_map (poster_backward_piece s)
        (rev (Zrange_aux (lo + 1) (S m)))) lo
      tail_positions
      (map (fun p => (p, Znth (p - 1) s 0))
        (rev (Zrange_aux (lo + 1) (S m))))
      (poster_backward_piece s lo)
      (if Z_lt_dec 1 lo then lo - 1 else lo)
      last_positions [(lo, Znth (lo - 1) s 0)] Htail Hlast) as Happ.
    destruct Happ as [positions Happ].
    exists positions.
    replace (lo + Z.of_nat (S m)) with (lo + 1 + Z.of_nat m)
      by (rewrite Nat2Z.inj_succ; lia).
    cbn [flat_map map].
    rewrite app_nil_r.
    exact Happ.
Qed.

Lemma right_first_valid__trace_count : forall k s,
  1 <= k <= Zlength s ->
  1 <= Zlength s <= 100 ->
  ValidPlan k s (RightFirstPlan k s).
Proof.
  intros k s Hk Hn.
  unfold RightFirstPlan, RightWalkPlan, BackwardSweepPlan, Zrange.
  replace (0 + 1) with 1 by lia.
  replace (Zlength s + 1 - 1) with (Zlength s) by lia.
  change (ValidPlan k s
    (repeat RightAction (Z.to_nat (Zlength s - k)) ++
     flat_map (poster_backward_piece s)
       (rev (Zrange_aux 1 (Z.to_nat (Zlength s)))))).
  replace (Z.to_nat (Zlength s)) with (length s)
    by (rewrite Zlength_correct; rewrite Nat2Z.id; reflexivity).
  assert (Hlen_pos : (0 < length s)%nat).
  { apply Nat2Z.inj_lt. rewrite <- Zlength_correct. lia. }
  assert (Hlen_succ : S (Nat.pred (length s)) = length s).
  { apply Nat.succ_pred_pos. exact Hlen_pos. }
  rewrite <- Hlen_succ.
  assert (Hright_finish : k + Z.of_nat (Z.to_nat (Zlength s - k)) <= Zlength s).
  { rewrite Z2Nat.id by lia. lia. }
  destruct (poster_right_repeat_route__trace_count
    (Zlength s) k (Z.to_nat (Zlength s - k)) Hk Hright_finish)
    as [right_positions Hright].
  assert (Hright_endpoint :
    k + Z.of_nat (Z.to_nat (Zlength s - k)) = Zlength s).
  { rewrite Z2Nat.id by lia. lia. }
  rewrite Hright_endpoint in Hright.
  assert (Hback_length :
    1 + Z.of_nat (Nat.pred (length s)) <= Zlength s).
  { pose proof (f_equal Z.of_nat Hlen_succ) as Hcast.
    rewrite Nat2Z.inj_succ in Hcast. rewrite Zlength_correct. lia. }
  destruct (poster_backward_aux_route__trace_count s (Zlength s) 1
    (Nat.pred (length s))
    ltac:(lia) Hback_length) as [back_positions Hback].
  assert (Hback_start :
    1 + Z.of_nat (Nat.pred (length s)) = Zlength s).
  { pose proof (f_equal Z.of_nat Hlen_succ) as Hcast.
    rewrite Nat2Z.inj_succ in Hcast. rewrite Zlength_correct. lia. }
  rewrite Hback_start in Hback.
  pose proof (poster_route_app__trace_count
    (Zlength s) k (repeat RightAction (Z.to_nat (Zlength s - k)))
    (Zlength s) right_positions []
    (flat_map (poster_backward_piece s)
      (rev (Zrange_aux 1 (S (Nat.pred (length s))))))
    (if Z_lt_dec 1 1 then 1 - 1 else 1) back_positions
    (map (fun p => (p, Znth (p - 1) s 0))
      (rev (Zrange_aux 1 (S (Nat.pred (length s)))))) Hright Hback) as Happ.
  destruct Happ as [positions Happ].
  eapply (poster_route_valid__trace_count s (Zlength s) k
    (repeat RightAction (Z.to_nat (Zlength s - k)) ++
     flat_map (poster_backward_piece s)
       (rev (Zrange_aux 1 (S (Nat.pred (length s))))))
    (if Z_lt_dec 1 1 then 1 - 1 else 1) positions
    (map (fun p => (p, Znth (p - 1) s 0))
      (rev (Zrange_aux 1 (S (Nat.pred (length s))))))).
  - reflexivity.
  - exact Happ.
  - intros i Hi. apply in_map_iff.
    exists (i + 1). split.
    + replace (i + 1 - 1) with i by lia. reflexivity.
    + apply (proj1 (in_rev
        (Zrange_aux 1 (S (Nat.pred (length s)))) (i + 1))).
      apply In_Zrange_aux.
      rewrite Zlength_correct in Hi. rewrite <- Hlen_succ in Hi. lia.
Qed.

Lemma poster_Zlength_repeat__trace_count : forall {A : Type} (x : A) m,
  Zlength (repeat x m) = Z.of_nat m.
Proof.
  intros A x m. induction m as [|m IH].
  - reflexivity.
  - simpl. rewrite Zlength_cons, IH. lia.
Qed.

Lemma poster_forward_aux_length__trace_count : forall s n lo m,
  1 <= lo <= n -> lo + Z.of_nat m = n + 1 ->
  Zlength (flat_map (poster_forward_piece s n) (Zrange_aux lo m)) =
    2 * Z.of_nat m - 1.
Proof.
  intros s n lo m Hlo Hspan.
  revert lo Hlo Hspan.
  induction m as [|m IH]; intros lo Hlo Hspan.
  - lia.
  - simpl. unfold poster_forward_piece.
    destruct (Z_lt_dec lo n) as [Hlt|Hnlt].
    + assert (Htail_lo : 1 <= lo + 1 <= n) by lia.
      assert (Htail_span : lo + 1 + Z.of_nat m = n + 1).
      { rewrite Nat2Z.inj_succ in Hspan. lia. }
      specialize (IH (lo + 1) Htail_lo Htail_span).
      unfold poster_forward_piece in IH.
      change (Zlength
        (PrintAction (Znth (lo - 1) s 0) :: RightAction ::
         flat_map (fun p =>
           PrintAction (Znth (p - 1) s 0) ::
           if Z_lt_dec p n then RightAction :: nil else nil)
           (Zrange_aux (lo + 1) m)) =
        2 * Z.of_nat (S m) - 1).
      rewrite !Zlength_cons, IH.
      rewrite Nat2Z.inj_succ. lia.
    + assert (Hlo_eq : lo = n) by lia.
      assert (Hm_zero : m = 0%nat).
      { rewrite Nat2Z.inj_succ in Hspan. lia. }
      subst lo. subst m. simpl.
      rewrite Zlength_cons, Zlength_nil. lia.
Qed.

Lemma poster_backward_piece_length__trace_count : forall s lo,
  Zlength (poster_backward_piece s lo) =
    if Z_lt_dec 1 lo then 2 else 1.
Proof.
  intros s lo. unfold poster_backward_piece.
  destruct (Z_lt_dec 1 lo) as [Hlt|Hnlt].
  - change (Zlength [(0, Znth (lo - 1) s 0); (-1, 0)] = 2).
    rewrite Zlength_correct. reflexivity.
  - change (Zlength [(0, Znth (lo - 1) s 0)] = 1).
    rewrite Zlength_correct. reflexivity.
Qed.

Lemma poster_backward_aux_length__trace_count : forall s lo m,
  1 <= lo ->
  Zlength (flat_map (poster_backward_piece s)
    (rev (Zrange_aux lo (S m)))) =
    2 * Z.of_nat (S m) - (if Z_lt_dec 1 lo then 0 else 1).
Proof.
  intros s lo m Hlo. revert lo Hlo.
  induction m as [|m IH]; intros lo Hlo.
  - cbn [Zrange_aux rev]. rewrite app_nil_l.
    cbn [flat_map]. rewrite app_nil_r.
    unfold poster_backward_piece.
    destruct (Z_lt_dec 1 lo) as [Hlt|Hnlt].
    + change (Zlength [(0, Znth (lo - 1) s 0); (-1, 0)] = 2).
      rewrite Zlength_correct. reflexivity.
    + change (Zlength [(0, Znth (lo - 1) s 0)] = 1).
      rewrite Zlength_correct. reflexivity.
  - change (Zlength (flat_map (poster_backward_piece s)
      (rev (Zrange_aux (lo + 1) (S m)) ++ [lo])) =
      2 * Z.of_nat (S (S m)) - (if Z_lt_dec 1 lo then 0 else 1)).
    rewrite flat_map_app.
    cbn [flat_map]. rewrite app_nil_r.
    change (Zlength (flat_map (poster_backward_piece s)
      (rev (Zrange_aux (lo + 1) (S m))) ++ poster_backward_piece s lo) =
      2 * Z.of_nat (S (S m)) - (if Z_lt_dec 1 lo then 0 else 1)).
    rewrite Zlength_app, poster_backward_piece_length__trace_count.
    assert (Htail := IH (lo + 1) ltac:(lia)).
    destruct (Z_lt_dec 1 (lo + 1)) as [Htail_lt|Htail_nlt]; [|lia].
    rewrite Htail.
    destruct (Z_lt_dec 1 lo) as [Hlt|Hnlt]; simpl.
    + lia.
    + lia.
Qed.

Lemma poster_forward_sweep_length__trace_count : forall s,
  1 <= Zlength s ->
  Zlength (ForwardSweepPlan s (Zlength s + 1)) = 2 * Zlength s - 1.
Proof.
  intros s Hlen.
  unfold ForwardSweepPlan, Zrange.
  replace (Z.to_nat (Zlength s + 1 - 1)) with (length s)
    by (rewrite Zlength_correct; lia).
  change (Zlength (flat_map (poster_forward_piece s (Zlength s))
    (Zrange_aux 1 (length s))) = 2 * Zlength s - 1).
  replace (2 * Zlength s - 1) with (2 * Z.of_nat (length s) - 1)
    by (rewrite Zlength_correct; lia).
  apply (poster_forward_aux_length__trace_count s (Zlength s) 1 (length s)).
  - lia.
  - rewrite Zlength_correct. lia.
Qed.

Lemma poster_backward_sweep_length__trace_count : forall s,
  1 <= Zlength s ->
  Zlength (BackwardSweepPlan s 0) = 2 * Zlength s - 1.
Proof.
  intros s Hlen.
  unfold BackwardSweepPlan, Zrange.
  replace (0 + 1) with 1 by lia.
  replace (Zlength s + 1 - 1) with (Zlength s) by lia.
  replace (Z.to_nat (Zlength s)) with (length s)
    by (rewrite Zlength_correct; rewrite Nat2Z.id; reflexivity).
  assert (Hlen_pos : (0 < length s)%nat).
  { apply Nat2Z.inj_lt. rewrite <- Zlength_correct. lia. }
  assert (Hlen_succ : S (Nat.pred (length s)) = length s).
  { apply Nat.succ_pred_pos. exact Hlen_pos. }
  rewrite <- Hlen_succ.
  pose proof (poster_backward_aux_length__trace_count s 1
    (Nat.pred (length s)) ltac:(lia)) as Hcount.
  destruct (Z_lt_dec 1 1) as [Hbad|Hgood]; [lia|].
  rewrite Hlen_succ in Hcount.
  rewrite <- Zlength_correct in Hcount.
  change (Zlength (flat_map (poster_backward_piece s)
    (rev (Zrange_aux 1 (S (Nat.pred (length s)))))) =
    2 * Zlength s - 1).
  rewrite Hlen_succ.
  exact Hcount.
Qed.

Lemma left_first_length__trace_count : forall k s,
  1 <= k <= Zlength s ->
  1 <= Zlength s <= 100 ->
  Zlength (LeftFirstPlan k s) = 2 * Zlength s - 1 + (k - 1).
Proof.
  intros k s Hk Hn.
  unfold LeftFirstPlan, LeftWalkPlan.
  rewrite Zlength_app, poster_Zlength_repeat__trace_count.
  rewrite poster_forward_sweep_length__trace_count by lia.
  rewrite Z2Nat.id by lia.
  ring.
Qed.

Lemma right_first_length__trace_count : forall k s,
  1 <= k <= Zlength s ->
  1 <= Zlength s <= 100 ->
  Zlength (RightFirstPlan k s) = 2 * Zlength s - 1 + (Zlength s - k).
Proof.
  intros k s Hk Hn.
  unfold RightFirstPlan, RightWalkPlan.
  rewrite Zlength_app, poster_Zlength_repeat__trace_count.
  rewrite poster_backward_sweep_length__trace_count by lia.
  rewrite Z2Nat.id by lia.
  ring.
Qed.

Lemma poster_valid_plan_total_lower_bound__trace_count : forall k s plan,
  1 <= k <= Zlength s ->
  1 <= Zlength s <= 100 ->
  ValidPlan k s plan ->
  2 * Zlength s - 1 + Z.min (k - 1) (Zlength s - k) <= Zlength plan.
Proof.
  intros k s plan Hk Hn Hvalid.
  pose proof (valid_plan_move_lower_bound__trace_count k s plan Hk Hn Hvalid)
    as Hmove.
  pose proof (valid_plan_print_lower_bound__trace_count k s plan Hvalid)
    as Hprint.
  pose proof (valid_plan_action_kinds__trace_count k s plan Hvalid)
    as Hkinds.
  pose proof (poster_action_account__trace_count plan Hkinds) as Haccount.
  lia.
Qed.

Lemma left_first_spec__trace_count : forall k s,
  1 <= k <= Zlength s ->
  1 <= Zlength s <= 100 ->
  k - 1 <= Zlength s - k ->
  Spec k s (LeftFirstPlan k s).
Proof.
  intros k s Hk Hn Hleft.
  unfold Spec, min_object_of_subset. split.
  - apply left_first_valid__trace_count; assumption.
  - intros plan Hvalid.
    pose proof (poster_valid_plan_total_lower_bound__trace_count
      k s plan Hk Hn Hvalid) as Hlower.
    pose proof (left_first_length__trace_count k s Hk Hn) as Hlength.
    rewrite Hlength.
    rewrite Z.min_l in Hlower by exact Hleft.
    exact Hlower.
Qed.

Lemma right_first_spec__trace_count : forall k s,
  1 <= k <= Zlength s ->
  1 <= Zlength s <= 100 ->
  Zlength s - k < k - 1 ->
  Spec k s (RightFirstPlan k s).
Proof.
  intros k s Hk Hn Hright.
  unfold Spec, min_object_of_subset. split.
  - apply right_first_valid__trace_count; assumption.
  - intros plan Hvalid.
    pose proof (poster_valid_plan_total_lower_bound__trace_count
      k s plan Hk Hn Hvalid) as Hlower.
    pose proof (right_first_length__trace_count k s Hk Hn) as Hlength.
    rewrite Hlength.
    rewrite Z.min_r in Hlower by lia.
    exact Hlower.
Qed.

#[export] Hint Resolve left_first_spec__trace_count right_first_spec__trace_count : core.

Lemma poster_Zlength_8_decompose__write_actions : forall (l : list Z),
  Zlength l = 8 ->
  exists a0 a1 a2 a3 a4 a5 a6 a7,
    l = [a0; a1; a2; a3; a4; a5; a6; a7].
Proof.
  intros l Hlength.
  rewrite Zlength_correct in Hlength.
  destruct l as [|a0 l]; [simpl in Hlength; lia|].
  destruct l as [|a1 l]; [simpl in Hlength; lia|].
  destruct l as [|a2 l]; [simpl in Hlength; lia|].
  destruct l as [|a3 l]; [simpl in Hlength; lia|].
  destruct l as [|a4 l]; [simpl in Hlength; lia|].
  destruct l as [|a5 l]; [simpl in Hlength; lia|].
  destruct l as [|a6 l]; [simpl in Hlength; lia|].
  destruct l as [|a7 l]; [simpl in Hlength; lia|].
  destruct l as [|a8 l].
  - repeat eexists; reflexivity.
  - simpl in Hlength. lia.
Qed.
Lemma Zlength_replace_Znth__left_walk :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l.
  induction l as [|a l IH]; intros n v; simpl; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n) as [|m].
  - simpl. repeat rewrite Zlength_cons. lia.
  - simpl. repeat rewrite Zlength_cons.
    specialize (IH (Z.of_nat m) v).
    replace (Z.to_nat (Z.of_nat m)) with m in IH by lia.
    rewrite IH. lia.
Qed.
Lemma Znth_app_left__left_walk :
  forall {A : Type} (d : A) (l1 l2 : list A) i,
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros A d l1 l2 i Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi. lia.
Qed.
Lemma Znth_app_last__left_walk :
  forall {A : Type} (d x : A) (l : list A),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros A d x l.
  unfold Znth.
  rewrite app_nth2.
  - replace (Z.to_nat (Zlength l) - length l)%nat with 0%nat.
    + simpl. reflexivity.
    + rewrite Zlength_correct, Nat2Z.id. lia.
  - rewrite Zlength_correct, Nat2Z.id. lia.
Qed.
Lemma left_walk_plan_step__left_walk : forall k p,
  1 < p -> p <= k ->
  LeftWalkPlan k (p - 1) = LeftWalkPlan k p ++ [LeftAction].
Proof.
  intros k p Hp Hpk.
  unfold LeftWalkPlan.
  assert (Hnat : Z.to_nat (k - (p - 1)) = (Z.to_nat (k - p) + 1)%nat).
  { apply Nat2Z.inj.
    rewrite Nat2Z.inj_add.
    rewrite !Z2Nat.id by lia. lia. }
  rewrite Hnat, repeat_app. simpl. reflexivity.
Qed.
Lemma solver_output_bridge_left_append__left_walk :
  forall capacity plan t before rows after,
    SolverOutputBridge capacity plan t before rows ->
    ActionSlotBridge LeftAction (Znth t rows []) after ->
    t + 1 < capacity ->
    SolverOutputBridge capacity (plan ++ [LeftAction]) (t + 1) before
      (replace_Znth t after rows).
Proof.
  intros capacity plan t before rows after Hbridge Hslot Hcap.
  unfold SolverOutputBridge in *.
  destruct Hbridge as [Ht [Hbefore [Hrows [Hactions Houtside]]]].
  assert (Ht_nonneg : 0 <= t) by (rewrite Ht; apply Zlength_nonneg).
  split.
  - rewrite Zlength_app, Zlength_cons, <- Ht. simpl. lia.
  - split.
    + exact Hbefore.
    + split.
      * rewrite Zlength_replace_Znth__left_walk. exact Hrows.
      * split.
        -- intros j Hj.
           destruct (Z.eq_dec j t) as [Hjt | Hjt].
           ++ subst j.
              rewrite Ht at 1.
              rewrite (Znth_app_last__left_walk (0, 0) LeftAction plan).
              rewrite (Znth_replace_Znth_Same [] rows t after)
                by (rewrite Hrows; lia).
              rewrite <- (Houtside t) by lia.
              exact Hslot.
           ++ assert (Hjold : 0 <= j < t) by lia.
              rewrite (Znth_app_left__left_walk (0, 0) plan [LeftAction] j)
                by (rewrite <- Ht; exact Hjold).
              rewrite (Znth_replace_Znth_Diff [] rows t j after)
                by (try rewrite Hrows; lia).
              apply Hactions. exact Hjold.
        -- intros j Hj.
           rewrite (Znth_replace_Znth_Diff [] rows t j after)
             by (try rewrite Hrows; lia).
           apply Houtside. lia.
Qed.
Lemma Zlength_replace_Znth__left_forward : forall {A : Type}
    (l : list A) n (v : A),
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
Lemma SolverOutputBridge_append__left_forward : forall
    (capacity : Z) (plan : list (Z * Z)) (ret : Z)
    (before rows : list (list Z)) (action : Z * Z) (after : list Z),
  0 <= ret < capacity ->
  SolverOutputBridge capacity plan ret before rows ->
  ActionSlotBridge action (Znth ret rows []) after ->
  SolverOutputBridge capacity (plan ++ action :: nil) (ret + 1)
    before (replace_Znth ret after rows).
Proof.
  intros capacity plan ret before rows action after Hret_bounds Hbridge Hslot.
  unfold SolverOutputBridge in Hbridge |- *.
  destruct Hbridge as [Hret [Hbefore [Hrows [Hdone Hstable]]]].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - split.
    + exact Hbefore.
    + split.
      * rewrite Zlength_replace_Znth__left_forward. exact Hrows.
      * split.
        -- intros idx Hidx.
           destruct (Z_lt_ge_dec idx ret) as [Hlt | Hge].
           ++ rewrite app_Znth1 by (rewrite <- Hret; lia).
              rewrite (Znth_replace_Znth_Diff [] rows ret idx after)
                by (try rewrite Hrows; lia).
              apply Hdone. lia.
           ++ assert (Hi_eq : idx = ret) by lia.
              subst idx.
              rewrite app_Znth2 by (rewrite <- Hret; lia).
              replace (ret - Zlength plan) with 0 by lia.
              simpl.
              rewrite Znth0_cons.
              rewrite (Znth_replace_Znth_Same [] rows ret after)
                by (rewrite Hrows; lia).
              rewrite <- (Hstable ret) by lia.
              exact Hslot.
        -- intros idx Hidx.
           rewrite (Znth_replace_Znth_Diff [] rows ret idx after)
             by (try rewrite Hrows; lia).
           apply Hstable. lia.
Qed.
Lemma forward_sweep_step__left_forward : forall s p,
  1 <= p ->
  p < Zlength s ->
  ForwardSweepPlan s (p + 1) =
    ForwardSweepPlan s p ++
      PrintAction (Znth (p - 1) s 0) :: RightAction :: nil.
Proof.
  intros s p Hp Hlt.
  unfold ForwardSweepPlan, Zrange.
  replace (p + 1 - 1) with p by ring.
  assert (Hnat : Z.to_nat p = (Z.to_nat (p - 1) + 1)%nat).
  { change (Z.to_nat p = (Z.to_nat (p - 1) + Z.to_nat 1)%nat).
      rewrite <- Z2Nat.inj_add by lia.
      f_equal. lia. }
  rewrite Hnat.
  rewrite Zrange_aux_app, flat_map_app.
  replace (1 + Z.of_nat (Z.to_nat (p - 1))) with p by
    (rewrite Z2Nat.id by lia; lia).
  simpl.
  destruct (Z_lt_dec p (Zlength s)) as [Hp_lt | Hp_not].
  - reflexivity.
  - lia.
Qed.
Lemma Zrange_one_succ__left_exit : forall k,
  1 <= k -> Zrange 1 (k + 1) = Zrange 1 k ++ (k :: nil).
Proof.
  intros k Hk. unfold Zrange.
  replace (Z.to_nat (k + 1 - 1)) with (Z.to_nat (k - 1) + 1)%nat by lia.
  rewrite Zrange_aux_app. simpl.
  replace (Z.of_nat (Z.to_nat (k - 1))) with (k - 1) by
    (rewrite Z2Nat.id by lia; reflexivity).
  change (Zrange_aux 1 (Z.to_nat (k - 1)) ++
    ((1 + (k - 1)) :: nil) =
    Zrange_aux 1 (Z.to_nat (k - 1)) ++ (k :: nil)).
  rewrite Z.add_1_l, Z.sub_1_r, Z.succ_pred. reflexivity.
Qed.
Lemma forward_sweep_terminal_step__left_exit : forall s n,
  1 <= n -> n = Zlength s ->
  ForwardSweepPlan s (n + 1) =
    ForwardSweepPlan s n ++ (PrintAction (Znth (n - 1) s 0) :: nil).
Proof.
  intros s n Hn Hlength.
  unfold ForwardSweepPlan.
  rewrite Zrange_one_succ__left_exit by lia.
  rewrite flat_map_app. simpl.
  destruct (Z_lt_dec n (Zlength s)); [lia|].
  reflexivity.
Qed.
Lemma right_walk_snoc__right_walk : forall k p,
  k <= p ->
  RightWalkPlan k (p + 1) = RightWalkPlan k p ++ [RightAction].
Proof.
  intros k p Hkp.
  unfold RightWalkPlan.
  replace (p + 1 - k) with ((p - k) + 1) by lia.
  rewrite Z2Nat.inj_add by lia.
  simpl.
  rewrite repeat_app.
  simpl.
  reflexivity.
Qed.
Lemma Zlength_replace_Znth__right_walk : forall {A : Type}
  (l : list A) n (v : A),
  Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v.
  revert n.
  induction l as [|a l IH]; simpl in *; intros n; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n) as [|n0].
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IH (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IH by lia.
    rewrite IH. lia.
Qed.
Lemma solver_output_bridge_append__right_walk :
  forall capacity plan ret before rows action after,
    SolverOutputBridge capacity plan ret before rows ->
    0 <= ret < capacity ->
    ActionSlotBridge action (Znth ret rows []) after ->
    SolverOutputBridge capacity (plan ++ [action]) (ret + 1)
      before (replace_Znth ret after rows).
Proof.
  intros capacity plan ret before rows action after Hbridge Hretcap Haction.
  unfold SolverOutputBridge in Hbridge |- *.
  destruct Hbridge as [Hret [Hbefore [Hrows [Hdone Hremain]]]].
  split.
  - rewrite Zlength_app_cons. lia.
  - split; [exact Hbefore|].
    split.
    + rewrite Zlength_replace_Znth__right_walk. exact Hrows.
    + split.
      * intros i Hi.
        destruct (Z.eq_dec i ret) as [Hi_eq|Hi_ne].
        -- subst i.
           rewrite Znth_replace_Znth_Same by (rewrite Hrows; lia).
           rewrite app_Znth2 by (rewrite Hret; lia).
           replace (ret - Zlength plan) with 0 by lia.
           simpl.
           assert (Hcurrent : Znth ret rows [] = Znth ret before []) by
             (apply Hremain; lia).
           change (ActionSlotBridge action (Znth ret before []) after).
           rewrite <- Hcurrent. exact Haction.
        -- rewrite Znth_replace_Znth_Diff by
             (rewrite ?Zlength_replace_Znth__right_walk, ?Hrows; lia).
           rewrite app_Znth1 by (rewrite <- Hret; lia).
           apply Hdone. lia.
      * intros i Hi.
        rewrite Znth_replace_Znth_Diff by
          (rewrite ?Zlength_replace_Znth__right_walk, ?Hrows; lia).
        apply Hremain. lia.
Qed.
Lemma backward_sweep_at_end__right_completion : forall s : list Z,
  BackwardSweepPlan s (Zlength s) = [].
Proof.
  intros s.
  unfold BackwardSweepPlan, Zrange.
  replace (Zlength s + 1 - (Zlength s + 1)) with 0 by lia.
  simpl.
  reflexivity.
Qed.
Lemma poster_Zlength_replace_Znth__right_sweep : forall {A : Type}
    (l : list A) n (v : A),
  Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros. revert n. induction l; simpl in *; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma poster_Znth_replace_Znth_Same__right_sweep : forall {A}
    (d : A) (l : list A) (i : Z) (v : A),
  0 <= i < Zlength l ->
  Znth i (replace_Znth i v l) d = v.
Proof.
  intros. unfold Znth, replace_Znth.
  set (m := Z.to_nat i).
  rewrite Zlength_correct in H.
  assert (0 <= m < length l)%nat by lia.
  clearbody m. clear H i.
  generalize dependent m.
  induction l; simpl in *; intros.
  - lia.
  - destruct m.
    + reflexivity.
    + simpl. rewrite IHl; auto. lia.
Qed.
Lemma poster_Znth_replace_Znth_Diff__right_sweep : forall {A}
    (d : A) (l : list A) (i j : Z) (v : A),
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  i <> j ->
  Znth j (replace_Znth i v l) d = Znth j l d.
Proof.
  intros. unfold Znth, replace_Znth.
  set (m := Z.to_nat i).
  set (n := Z.to_nat j).
  rewrite Zlength_correct in H, H0.
  assert (0 <= m < length l)%nat by lia.
  assert (0 <= n < length l)%nat by lia.
  assert (m <> n) by lia.
  clearbody m. clearbody n.
  clear H H0 H1 i j.
  generalize dependent m.
  generalize dependent n.
  induction l; simpl in *; intros.
  - lia.
  - destruct m, n; simpl in *; try auto; try lia.
    rewrite IHl; try lia; auto.
Qed.
Lemma poster_app_Znth1__right_sweep : forall {A} (d : A)
    (l l' : list A) (i : Z),
  0 <= i < Zlength l ->
  Znth i (l ++ l') d = Znth i l d.
Proof.
  intros. unfold Znth.
  assert (Z.to_nat i < length l)%nat by
    (rewrite Zlength_correct in H; lia).
  set (j := Z.to_nat i) in *; clearbody j; clear i H.
  apply app_nth1; auto.
Qed.
Lemma poster_app_Znth2__right_sweep : forall {A} (d : A)
    (l l' : list A) (i : Z),
  i >= Zlength l ->
  Znth i (l ++ l') d = Znth (i - Zlength l) l' d.
Proof.
  intros. unfold Znth.
  assert (Z.to_nat i >= length l)%nat by
    (rewrite Zlength_correct in H; lia).
  replace (Z.to_nat (i - Zlength l)) with
    (Z.to_nat i - length l)%nat by (rewrite Zlength_correct in *; lia).
  apply app_nth2; auto.
Qed.
Lemma poster_solver_output_bridge_snoc__right_sweep :
  forall capacity plan ret before after action newrow,
    SolverOutputBridge capacity plan ret before after ->
    ret < capacity ->
    0 <= ret ->
    ActionSlotBridge action (Znth ret after []) newrow ->
    SolverOutputBridge capacity (plan ++ action :: nil) (ret + 1) before
      (replace_Znth ret newrow after).
Proof.
  intros capacity plan ret before after action newrow Hbridge Hcap Hnonneg Hslot.
  unfold SolverOutputBridge in *.
  destruct Hbridge as [Hret [Hbefore [Hafter [Hslots Htail]]]].
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - rewrite Zlength_app_cons. lia.
  - exact Hbefore.
  - rewrite poster_Zlength_replace_Znth__right_sweep. exact Hafter.
  - intros idx Hidx.
    destruct (Z.eq_dec idx ret) as [Hidx_eq | Hidx_ne].
    + subst idx.
      rewrite (poster_app_Znth2__right_sweep (0, 0) plan
        (action :: nil) ret) by lia.
      assert (Hzero : ret - Zlength plan = 0) by lia.
      rewrite Hzero, Znth0_cons.
      rewrite poster_Znth_replace_Znth_Same__right_sweep
        by (rewrite Hafter; lia).
      assert (Hsame : Znth ret after [] = Znth ret before []) by
        (apply Htail; lia).
      rewrite Hsame in Hslot.
      exact Hslot.
    + rewrite (poster_app_Znth1__right_sweep (0, 0) plan
        (action :: nil) idx) by lia.
      rewrite poster_Znth_replace_Znth_Diff__right_sweep by lia.
      apply Hslots. lia.
  - intros idx Hidx.
    assert (Hret_bound : 0 <= ret < Zlength after) by
      (rewrite Hafter; lia).
    assert (Hidx_bound : 0 <= idx < Zlength after) by
      (rewrite Hafter; lia).
    assert (Hidx_ne : ret <> idx) by lia.
    rewrite (poster_Znth_replace_Znth_Diff__right_sweep [] after ret idx newrow
      Hret_bound Hidx_bound Hidx_ne).
    apply Htail. lia.
Qed.
Lemma poster_backward_sweep_step__right_sweep : forall s p,
  1 < p ->
  p <= Zlength s ->
  BackwardSweepPlan s (p - 1) =
    (BackwardSweepPlan s p ++ PrintAction (Znth (p - 1) s 0) :: nil) ++
      LeftAction :: nil.
Proof.
  intros s p Hp Hbound.
  unfold BackwardSweepPlan.
  assert (Hrange :
    Zrange p (Zlength s + 1) =
      p :: Zrange (p + 1) (Zlength s + 1)).
  { unfold Zrange.
    replace (Z.to_nat (Zlength s + 1 - p))
      with (S (Z.to_nat (Zlength s + 1 - (p + 1)))) by lia.
    reflexivity. }
  assert (Hpiece :
    PrintAction (Znth (p - 1) s 0) ::
      (if Z_lt_dec 1 p then LeftAction :: nil else nil) =
    PrintAction (Znth (p - 1) s 0) :: LeftAction :: nil).
  { destruct (Z_lt_dec 1 p); [reflexivity | lia]. }
  replace (p - 1 + 1) with p by lia.
  rewrite Hrange. simpl. rewrite flat_map_app.
  simpl.
  rewrite app_nil_r.
  rewrite Hpiece.
  rewrite <- app_assoc.
  reflexivity.
Qed.
Lemma poster_backward_sweep_step_prefixed__right_sweep : forall prefix s p,
  1 < p ->
  p <= Zlength s ->
  prefix ++ BackwardSweepPlan s (p - 1) =
    ((prefix ++ BackwardSweepPlan s p) ++
      PrintAction (Znth (p - 1) s 0) :: nil) ++ LeftAction :: nil.
Proof.
  intros prefix s p Hp Hbound.
  rewrite (poster_backward_sweep_step__right_sweep s p Hp Hbound).
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.
Lemma poster_backward_sweep_exit__right_sweep : forall s,
  1 <= Zlength s ->
  BackwardSweepPlan s 0 =
    BackwardSweepPlan s 1 ++ PrintAction (Znth 0 s 0) :: nil.
Proof.
  intros s Hlength.
  unfold BackwardSweepPlan.
  assert (Hrange :
    Zrange 1 (Zlength s + 1) =
      1 :: Zrange 2 (Zlength s + 1)).
  { unfold Zrange.
    replace (Z.to_nat (Zlength s + 1 - 1))
      with (S (Z.to_nat (Zlength s + 1 - 2))) by lia.
    reflexivity. }
  replace (0 + 1) with 1 by lia.
  rewrite Hrange. simpl. rewrite flat_map_app. simpl.
  reflexivity.
Qed.
Lemma poster_backward_sweep_exit_prefixed__right_sweep : forall prefix s,
  1 <= Zlength s ->
  prefix ++ BackwardSweepPlan s 0 =
    (prefix ++ BackwardSweepPlan s 1) ++ PrintAction (Znth 0 s 0) :: nil.
Proof.
  intros prefix s Hlength.
  rewrite (poster_backward_sweep_exit__right_sweep s Hlength).
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.
