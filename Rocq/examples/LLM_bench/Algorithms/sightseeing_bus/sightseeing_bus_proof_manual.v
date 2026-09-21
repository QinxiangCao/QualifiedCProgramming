Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.sightseeing_bus Require Import sightseeing_bus_goal.
Require Import AUXLib.MonotonicList.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.sightseeing_bus.sightseeing_bus_lib.
Local Open Scope sac.
Local Opaque IntArray.undef_full IntArray.undef_seg IntArray.full IntArray.seg.

Ltac bus_make_inputs n m dist times origins destinations :=
  assert (InputFacts : SightseeingInputsBounded n m dist times origins destinations) by
  (unfold SightseeingInputsBounded;
   do 6 (split; [lia|]); split;
   [intros edge He;
    pose proof (proj1 (Forall_Znth (Z.le 0) 0 dist) ltac:(eassumption) edge ltac:(lia));
    pose proof (proj1 (Forall_Znth (Z.ge 100) 0 dist) ltac:(eassumption) edge ltac:(lia)); lia
   |intros passenger Hp;
    pose proof (proj1 (Forall_Znth (Z.le 0) 0 times) ltac:(eassumption) passenger ltac:(lia));
    pose proof (proj1 (Forall_Znth (Z.ge 100000) 0 times) ltac:(eassumption) passenger ltac:(lia));
    pose proof (proj1 (Forall_Znth (Z.le 1) 0 origins) ltac:(eassumption) passenger ltac:(lia));
    pose proof (proj1 (Forall_Znth (Z.ge n) 0 destinations) ltac:(eassumption) passenger ltac:(lia));
    pose proof (bus_Forall2_Znth Z.lt origins destinations passenger ltac:(eassumption) ltac:(lia));
    repeat split; lia]).

Ltac bus_shapes :=
  try match goal with
  | H : BoosterProgress ?n ?m ?b ?r ?ini ?ts ?os ?ds ?d ?l ?c ?a |- _ =>
    let S := fresh "shape" in
    assert (S : Zlength d = n-1 /\ Zlength l = n /\ Zlength c = n /\ Zlength a = n) by
      (let HC := fresh in pose proof H as HC;
       unfold BoosterProgress, LatestDepartures, DestinationCounts,
         FeasibleBoostedDistances, BusArrivalSchedule in HC; tauto)
  end;
  try match goal with
  | H : CanonicalBusState ?n ?m ?ts ?os ?ds ?d ?l ?c ?a |- _ =>
    let S := fresh "shape" in
    assert (S : Zlength l = n /\ Zlength c = n /\ Zlength a = n) by
      (let HC := fresh in pose proof H as HC;
       unfold CanonicalBusState, StationSummaryState, LatestDepartures,
         DestinationCounts, BusArrivalSchedule in HC; tauto)
  end;
  try match goal with
  | H : StationSummaryState ?n ?m ?ts ?os ?ds ?l ?c |- _ =>
    let S := fresh "shape" in
    assert (S : Zlength l = n /\ Zlength c = n) by
      (let HC := fresh in pose proof H as HC;
       unfold StationSummaryState, LatestDepartures, DestinationCounts in HC; tauto)
  end.

Ltac bus_points :=
  repeat match goal with
  | H : Forall ?P ?l |- context [Znth ?idx ?l 0] =>
    let B := fresh "point" in
    pose proof (proj1 (Forall_Znth P 0 l) H idx ltac:(rewrite ?Zlength_replace_Znth, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia)) as B; clear H
  end;
  repeat multimatch goal with
  | H : forall i : Z, _ -> _ |- context [Znth ?idx _ 0] =>
    let B := fresh "point" in pose proof (H idx ltac:(lia)) as B; clear H
  end.

Ltac bus_zero :=
  repeat match goal with
  | H : WorkspacesZeroPrefix ?l ?c ?p |- _ =>
    rewrite (WorkspacesZeroPrefix_unfold l c p ltac:(lia) ltac:(rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia) ltac:(rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia)) in H
  end;
  try match goal with
  | |- WorkspacesZeroPrefix ?l ?c ?p =>
    apply (proj2 (WorkspacesZeroPrefix_unfold l c p ltac:(lia) ltac:(rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia) ltac:(rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia)))
  end.

Ltac bus_forall :=
  match goal with |- Forall ?P ?xs =>
    apply (proj2 (Forall_Znth P 0 xs));
    let idx := fresh "idx" in let Hi := fresh "idx_range" in intros idx Hi;
    try rewrite Zlength_replace_Znth in Hi;
    first [solve [bus_points; lia] |
      match goal with |- context [Znth idx (replace_Znth ?p ?v ?l) 0] =>
        destruct (Z.eq_dec idx p) as [Heq | Hne];
        [subst idx; rewrite Znth_replace_Znth_Same by lia |
         rewrite Znth_replace_Znth_Diff by lia]; bus_points; lia
      end]
  end.

Ltac bus_cancel :=
  elim_emp; sepcon_right_assoc;
  repeat match goal with
  | |- ?P ** _ |-- _ => progress (cancel P)
  | |- ?P |-- ?P => apply derivable1_refl
  end; try cancel.



Lemma proof_of_solve_safety_wit_6_split_goal_1 : solve_safety_wit_6_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof InputFacts as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist_bounds Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds i ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_6_split_goal_2 : solve_safety_wit_6_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof InputFacts as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist_bounds Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds i ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_6 : solve_safety_wit_6.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_8_split_goal_1 : solve_safety_wit_8_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof InputFacts as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist_bounds Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds i ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_8_split_goal_2 : solve_safety_wit_8_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof InputFacts as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist_bounds Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds i ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_8 : solve_safety_wit_8.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_8_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_8_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_10_split_goal_1 : solve_safety_wit_10_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) by (intros; repeat split; bus_points; lia).
  pose proof
    (Legacy_PreH24 (Znth i destinations 0 - 1) ltac:(lia)) as Hcount_bounds.
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_10_split_goal_2 : solve_safety_wit_10_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) by (intros; repeat split; bus_points; lia).
  pose proof
    (Legacy_PreH24 (Znth i destinations 0 - 1) ltac:(lia)) as Hcount_bounds.
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_10 : solve_safety_wit_10.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_12_split_goal_1 : solve_safety_wit_12_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) by (intros; repeat split; bus_points; lia).
  pose proof
    (Legacy_PreH24 (Znth i destinations 0 - 1) ltac:(lia)) as Hcount_bounds.
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_12_split_goal_2 : solve_safety_wit_12_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH24 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= i)))) by (intros; repeat split; bus_points; lia).
  pose proof
    (Legacy_PreH24 (Znth i destinations 0 - 1) ltac:(lia)) as Hcount_bounds.
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_12 : solve_safety_wit_12.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_12_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_22_split_goal_1 : solve_safety_wit_22_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) by (intros; repeat split; bus_points; lia).
  pose proof InputFacts as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [_ [_ [_ [_ [_ [_ [Hdist _]]]]]]].
  specialize (Hdist i ltac:(lia)).
  specialize (Legacy_PreH13 i ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_22_split_goal_2 : solve_safety_wit_22_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)))) by (intros; repeat split; bus_points; lia).
  pose proof InputFacts as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [_ [_ [_ [_ [_ [_ [Hdist _]]]]]]].
  specialize (Hdist i ltac:(lia)).
  specialize (Legacy_PreH13 i ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_22 : solve_safety_wit_22.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_22_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_23_split_goal_1 : solve_safety_wit_23_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof InputFacts as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [_ [_ [_ [_ [_ [_ [Hdist _]]]]]]].
  specialize (Hdist i ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_23_split_goal_2 : solve_safety_wit_23_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof InputFacts as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [_ [_ [_ [_ [_ [_ [Hdist _]]]]]]].
  specialize (Hdist i ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_23 : solve_safety_wit_23.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_23_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_39_split_goal_1 : solve_safety_wit_39_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  specialize (Legacy_PreH22 j ltac:(lia)).
  unfold SightseeingInputsBounded in InputFacts.
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_39_split_goal_2 : solve_safety_wit_39_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH22 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals) (0)))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  specialize (Legacy_PreH22 j ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_39 : solve_safety_wit_39.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_39_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_39_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_46_split_goal_1 : solve_safety_wit_46_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) by (intros; repeat split; bus_points; lia).
  specialize (Legacy_PreH18 pos ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_46_split_goal_2 : solve_safety_wit_46_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH18 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist) (0))) /\ ((Znth (edge) (current_dist) (0)) <= 100)))) by (intros; repeat split; bus_points; lia).
  specialize (Legacy_PreH18 pos ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_46 : solve_safety_wit_46.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_46_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_46_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_50_split_goal_1 : solve_safety_wit_50_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  specialize (Legacy_PreH19 i ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_50_split_goal_2 : solve_safety_wit_50_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH19 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest) (0))) /\ ((Znth (station) (latest) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals) (0)))) /\ ((Znth (station) (new_arrivals) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  specialize (Legacy_PreH19 i ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_50 : solve_safety_wit_50.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_50_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_50_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_63_split_goal_1 : solve_safety_wit_63_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  all: assert (Legacy_PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) by (intros; repeat split; bus_points; lia).
  specialize (Legacy_PreH23 (Znth i destinations 0 - 1) ltac:(lia)).
  specialize (Legacy_PreH24 i ltac:(lia)).
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [Hm _]].
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_63_split_goal_2 : solve_safety_wit_63_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof PreH35 as Hstate.
  unfold OptimizedBusState in Hstate.
  destruct Hstate as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hoptimum]]]].
  assert (Hdist_nonnegative :
    forall edge, 0 <= edge < n_pre - 1 ->
      0 <= Znth edge final_dist 0).
  {
    try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
    destruct Hfeasible as [_ [Hdist_bounds _]].
    intros edge Hedge.
    specialize (Hdist_bounds edge Hedge).
    lia.
  }
  pose proof
    (arrival_dominates_passenger_time__travel_and_return
       n_pre m_pre dist times origins destinations
       final_dist latest arrivals i
       InputFacts Hlatest (or_intror Hdist_nonnegative) Hschedule
       ltac:(lia)) as Harrival_dominates.
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_63 : solve_safety_wit_63.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_63_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_63_split_goal_2.
Qed.

Lemma proof_of_solve_safety_wit_64_split_goal_1 : solve_safety_wit_64_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  specialize (Legacy_PreH23 (Znth i destinations 0 - 1) ltac:(lia)).
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [Hm _]].
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_64_split_goal_2 : solve_safety_wit_64_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals) (0))) /\ ((Znth (station) (arrivals) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  specialize (Legacy_PreH23 (Znth i destinations 0 - 1) ltac:(lia)).
  dump_pre_spatial.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_safety_wit_64 : solve_safety_wit_64.
Proof.
  unfold solve_safety_wit_64; left; intros.
  apply _derivable1_andp_intros.
  - eapply proof_of_solve_safety_wit_64_split_goal_1; eassumption.
  - eapply proof_of_solve_safety_wit_64_split_goal_2; eassumption.
Qed.

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  unfold solve_entail_wit_1; right; intros.
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&("late")) n_pre 1000 ltac:(lia)).
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&("off")) n_pre 1000 ltac:(lia)).
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&("arr")) n_pre 1000 ltac:(lia)).
  sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&("arr")) 0 n_pre).
  rewrite ?Z.mul_0_l, ?Z.add_0_r, ?Z.sub_0_r.
  split_pure_spatial.
  - bus_cancel.
  - split_pures; dump_pre_spatial; try reflexivity.
    unfold WorkspacesZeroPrefix; cbn; split; constructor.
Qed.

Lemma proof_of_solve_entail_wit_2_split_goal_1 : solve_entail_wit_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  bus_zero.
  intros station Hstation.
  specialize (PreH6 station).
  destruct (Z_lt_ge_dec station i) as [Hbefore | Hat].
  - specialize (PreH6 ltac:(lia)).
    destruct PreH6 as [Hlatest Hcounts].
    split.
    + rewrite app_Znth1 by (rewrite PreH4; lia).
      exact Hlatest.
    + rewrite app_Znth1 by (rewrite PreH5; lia).
      exact Hcounts.
  - assert (station = i) by lia.
    subst station.
    split.
    + rewrite app_Znth2 by (rewrite PreH4; lia).
      rewrite PreH4.
      replace (i - i) with 0 by lia.
      reflexivity.
    + rewrite app_Znth2 by (rewrite PreH5; lia).
      rewrite PreH5.
      replace (i - i) with 0 by lia.
      reflexivity.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_2_split_goal_2 : solve_entail_wit_2_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_2_split_goal_3 : solve_entail_wit_2_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof PreH6 as ZeroFacts.
  rewrite (WorkspacesZeroPrefix_unfold latest_prefix counts_prefix i ltac:(lia)
    ltac:(lia) ltac:(lia)) in ZeroFacts.
  assert (Hagg : PassengerAggregationPrefix n_pre m_pre times origins destinations
    0 latest_prefix counts_prefix).
  { unfold PassengerAggregationPrefix. split.
    - intros station Hstation.
      pose proof (ZeroFacts station ltac:(lia)) as [HZ _]. rewrite HZ.
      unfold LatestAtStationPrefix. apply MaxMin.max_default_default.
      intros passenger HP. lia.
    - intros station Hstation.
      pose proof (ZeroFacts station ltac:(lia)) as [_ HZ]. rewrite HZ.
      unfold Sum.sum. cbn. reflexivity. }
  Exists counts_prefix latest_prefix.
  split_pure_spatial.
  - assert (Hi : i = n_pre) by lia.
    rewrite Hi in *.
    rewrite (IntArray.undef_seg_empty (&("late")) n_pre).
    sep_apply_l_atomic
      (IntArray.seg_to_full (&("late")) 0 n_pre latest_prefix).
    replace ((&("late")) + 0 * sizeof(INT)) with (&("late")) by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (IntArray.full (&("late")) n_pre latest_prefix).
    rewrite (IntArray.undef_seg_empty (&("off")) n_pre).
    sep_apply_l_atomic
      (IntArray.seg_to_full (&("off")) 0 n_pre counts_prefix).
    replace ((&("off")) + 0 * sizeof(INT)) with (&("off")) by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (IntArray.full (&("off")) n_pre counts_prefix).
    bus_cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: bus_forall.
Qed.

Lemma proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bus_make_inputs n_pre m_pre dist times origins destinations.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [_ [_ [_ [_ [_ [_ Hpassenger]]]]]]].
  specialize (Hpassenger i ltac:(lia)).
  split_pure_spatial.
  - bus_cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia | int_auto].
Qed.

Lemma proof_of_solve_entail_wit_5_1_split_goal_1 : solve_entail_wit_5_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof
    (passenger_aggregation_prefix_step__passenger_aggregation
       n_pre m_pre times origins destinations i latest_2 counts_2
       ltac:(lia) PreH32 PreH33 ltac:(lia) ltac:(lia) PreH38) as Hstep.
  rewrite
    (MaxMin.max_r Z.le
       (Znth (Znth i origins 0 - 1) latest_2 0)
       (Znth i times 0) ltac:(lia)) in Hstep.
  exact Hstep.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_5_1_split_goal_2 : solve_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: bus_forall.
Qed.

Lemma proof_of_solve_entail_wit_5_1_split_goal_3 : solve_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: bus_forall.
Qed.

Lemma proof_of_solve_entail_wit_5_1_split_goal_4 : solve_entail_wit_5_1_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: bus_forall.
Qed.

Lemma proof_of_solve_entail_wit_5_1_split_goal_5 : solve_entail_wit_5_1_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: bus_forall.
Qed.

Lemma proof_of_solve_entail_wit_5_1_split_goal_6 : solve_entail_wit_5_1_split_goal_6.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  rewrite Zlength_replace_Znth.
  exact PreH33.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_5_1_split_goal_7 : solve_entail_wit_5_1_split_goal_7.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  rewrite Zlength_replace_Znth.
  exact PreH32.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_5_1 : solve_entail_wit_5_1.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_5_1_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_5_1_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_5_1_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_5_1_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_5_1_split_goal_7.
Qed.

Lemma proof_of_solve_entail_wit_5_2_split_goal_1 : solve_entail_wit_5_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof
    (passenger_aggregation_prefix_step__passenger_aggregation
       n_pre m_pre times origins destinations i latest_2 counts_2
       ltac:(lia) PreH32 PreH33 ltac:(lia) ltac:(lia) PreH38) as Hstep.
  rewrite
    (MaxMin.max_l Z.le
       (Znth (Znth i origins 0 - 1) latest_2 0)
       (Znth i times 0) ltac:(lia)) in Hstep.
  rewrite replace_Znth_Znth in Hstep.
  exact Hstep.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_5_2_split_goal_2 : solve_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: bus_forall.
Qed.

Lemma proof_of_solve_entail_wit_5_2_split_goal_3 : solve_entail_wit_5_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: bus_forall.
Qed.

Lemma proof_of_solve_entail_wit_5_2_split_goal_4 : solve_entail_wit_5_2_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  rewrite Zlength_replace_Znth.
  exact PreH33.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_5_2 : solve_entail_wit_5_2.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_5_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_5_2_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_5_2_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_1 : solve_entail_wit_6_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold ArrivalSimulationPrefix.
  split.
  - intros station Hstation.
    lia.
  - left.
    lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_2 : solve_entail_wit_6_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: bus_forall.
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_3 : solve_entail_wit_6_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  eapply (passenger_aggregation_complete__comparison_completion
    n_pre m_pre times origins destinations i latest_2 counts_2).
  - lia.
  - exact PreH21.
  - exact PreH22.
  - exact PreH27.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_6_split_goal_4 : solve_entail_wit_6_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_solve_entail_wit_6_split_goal_1.
 - Goal_apply proof_of_solve_entail_wit_6_split_goal_2.
 - Goal_apply proof_of_solve_entail_wit_6_split_goal_3.
 - Goal_apply proof_of_solve_entail_wit_6_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_7_1_split_goal_1 : solve_entail_wit_7_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  eapply arrival_simulation_prefix_snoc__arrival_simulation.
  - exact PreH8.
  - lia.
  - exact PreH31.
  - left.
    split; lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_1_split_goal_2 : solve_entail_wit_7_1_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  rewrite Zlength_app, PreH8.
  cbn.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_1_split_goal_3 : solve_entail_wit_7_1_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) by (intros; repeat split; bus_points; lia).
  pose proof (Legacy_PreH13 i ltac:(lia)) as Hlatest.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as
    [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
      [Hdestinations_length [Hdist Hpassengers]]]]]]].
  specialize (Hdist i ltac:(lia)).
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_1_split_goal_4 : solve_entail_wit_7_1_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) by (intros; repeat split; bus_points; lia).
  pose proof (Legacy_PreH13 i ltac:(lia)) as Hlatest.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as
    [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
      [Hdestinations_length [Hdist Hpassengers]]]]]]].
  specialize (Hdist i ltac:(lia)).
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_1 : solve_entail_wit_7_1.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_7_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_7_1_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_7_1_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_7_2_split_goal_1 : solve_entail_wit_7_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  eapply arrival_simulation_prefix_snoc__arrival_simulation.
  - exact PreH8.
  - lia.
  - exact PreH31.
  - right.
    split; lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_2_split_goal_2 : solve_entail_wit_7_2_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  rewrite Zlength_app, PreH8.
  cbn.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_2_split_goal_3 : solve_entail_wit_7_2_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) by (intros; repeat split; bus_points; lia).
  pose proof InputFacts as Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as
    [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
      [Hdestinations_length [Hdist Hpassengers]]]]]]].
  assert (Hlatest : forall station, 0 <= station < n_pre ->
      0 <= Znth station latest_2 0 <= 100000).
  {
    intros station Hstation.
    pose proof (Legacy_PreH13 station Hstation).
    lia.
  }
  pose proof
    (arrival_simulation_prefix_pending_bound__arrival_simulation
       n_pre dist latest_2 arrivals_prefix_2 i cur
       Hn Hdist Hlatest ltac:(lia) PreH31) as Hcur.
  specialize (Hdist i ltac:(lia)).
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_2_split_goal_4 : solve_entail_wit_7_2_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as
    [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
      [Hdestinations_length [Hdist Hpassengers]]]]]]].
  specialize (Hdist i ltac:(lia)).
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_2 : solve_entail_wit_7_2.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_7_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_7_2_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_7_2_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_7_3_split_goal_1 : solve_entail_wit_7_3_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  assert (Hi : i = n_pre - 1) by lia.
  assert (Hdist_zero : Znth i dist 0 = 0).
  {
    unfold SightseeingInputsBounded in InputFacts.
    destruct InputFacts as
      [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
        [Hdestinations_length [Hdist Hpassengers]]]]]]].
    apply Znth_at_or_past_length_default__arrival_simulation; lia.
  }
  eapply arrival_simulation_prefix_snoc__arrival_simulation.
  - exact PreH8.
  - lia.
  - exact PreH31.
  - left.
    split; lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_3_split_goal_2 : solve_entail_wit_7_3_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  rewrite Zlength_app, PreH8.
  cbn.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_3_split_goal_3 : solve_entail_wit_7_3_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH13 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)))) by (intros; repeat split; bus_points; lia).
  pose proof (Legacy_PreH13 i ltac:(lia)) as Hlatest.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_3 : solve_entail_wit_7_3.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_7_3_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_7_3_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_7_3_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_7_4_split_goal_1 : solve_entail_wit_7_4_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  assert (Hi : i = n_pre - 1) by lia.
  assert (Hdist_zero : Znth i dist 0 = 0).
  {
    unfold SightseeingInputsBounded in InputFacts.
    destruct InputFacts as
      [Hn [Hm [Hdist_length [Htimes_length [Horigins_length
        [Hdestinations_length [Hdist Hpassengers]]]]]]].
    apply Znth_at_or_past_length_default__arrival_simulation; lia.
  }
  eapply arrival_simulation_prefix_snoc__arrival_simulation.
  - exact PreH8.
  - lia.
  - exact PreH31.
  - right.
    split; lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_4_split_goal_2 : solve_entail_wit_7_4_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  rewrite Zlength_app, PreH8.
  cbn.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_7_4 : solve_entail_wit_7_4.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_7_4_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_7_4_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  bus_make_inputs n_pre m_pre dist times origins destinations.
  bus_shapes.
  assert (HD : forall edge, 0 <= edge < n_pre - 1 -> 0 <= Znth edge dist 0 <= 100) by (intros; bus_points; lia).
  assert (HL : forall station, 0 <= station < n_pre -> 0 <= Znth station latest_2 0 <= 100000) by (intros; bus_points; lia).
  destruct (arrival_simulation_complete__comparison_completion
    n_pre dist latest_2 arrivals_prefix cur ltac:(lia) HD HL ltac:(lia)
    ltac:(replace n_pre with i by lia; exact PreH29)) as [HS HA].
  assert (HC : CanonicalBusState n_pre m_pre times origins destinations dist latest_2 counts_2 arrivals_prefix) by (split; [exact PreH24|exact HS]).
  assert (HB : BoosterProgress n_pre m_pre k_pre k_pre dist times origins destinations dist latest_2 counts_2 arrivals_prefix).
  { eapply booster_progress_initial_active__booster_and_scan_initialization; eauto. }
  Exists arrivals_prefix counts_2 latest_2 dist.
  split_pure_spatial.
  - assert (Hi : i = n_pre) by lia. rewrite Hi.
    rewrite (IntArray.undef_seg_empty (&("arr")) n_pre).
    sep_apply_l_atomic (IntArray.seg_to_full (&("arr")) 0 n_pre arrivals_prefix).
    rewrite ?Z.mul_0_l, ?Z.add_0_r, ?Z.sub_0_r.
    sep_apply_l_atomic (store_int_undef_store_int (&("i")) n_pre).
    sep_apply_l_atomic (store_int_undef_store_int (&("cur")) cur).
    bus_cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    all: bus_forall.
Qed.

Lemma proof_of_solve_entail_wit_9_split_goal_1 : solve_entail_wit_9_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold EdgeChoicePrefix.
  split.
  - apply MaxMin.max_default_default.
    intros [edge benefit] Heligible.
    unfold EligibleEdgeBenefit in Heligible.
    cbn in Heligible.
    lia.
  - left.
    lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Proof.
aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_10_split_goal_1 : solve_entail_wit_10_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply marginal_benefit_scan_empty__booster_and_scan_initialization.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_10 : solve_entail_wit_10.
Proof.
aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_10_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_11_split_goal_1 : solve_entail_wit_11_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  eapply marginal_benefit_scan_snoc__edge_benefit_scan;
    [lia | exact PreH46 | lia].

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_11_split_goal_2 : solve_entail_wit_11_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold BoosterProgress in PreH44.
  destruct PreH44 as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]].
  unfold SightseeingInputsBounded in InputFacts.
  eapply
    (marginal_benefit_scan_extended_upper__booster_and_scan_initialization
      n_pre m_pre destinations counts_2 latest_2 arrivals_2 i j cnt);
    [lia | lia | lia | lia | exact Hcounts | exact PreH46].

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_11_split_goal_3 : solve_entail_wit_11_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  specialize (Legacy_PreH23 j ltac:(lia)).
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_11 : solve_entail_wit_11.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_11_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_11_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_11_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_12_1_split_goal_1 : solve_entail_wit_12_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  eapply marginal_scan_to_edge_benefit__edge_benefit_scan
    with (next := j) (benefit := cnt).
  - lia.
  - lia.
  - exact PreH45.
  - left. split; lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_12_1 : solve_entail_wit_12_1.
Proof.
aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_12_1_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_12_2_split_goal_1 : solve_entail_wit_12_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  eapply marginal_scan_to_edge_benefit__edge_benefit_scan
    with (next := j) (benefit := cnt).
  - lia.
  - lia.
  - exact PreH46.
  - right.
    split; [lia |].
    split; [exact PreH1 | reflexivity].

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_12_2_split_goal_2 : solve_entail_wit_12_2_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof InputFacts as Hinput_bounds.
  unfold SightseeingInputsBounded in Hinput_bounds.
  destruct Hinput_bounds as [Hn [Hm Hinput_rest]].
  pose proof PreH44 as Hprogress_fields.
  unfold BoosterProgress in Hprogress_fields.
  destruct Hprogress_fields as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]].
  pose proof
    (destination_count_interval_bound__edge_benefit_scan
      n_pre m_pre destinations counts (i + 1) (j + 1)
      ltac:(lia) ltac:(repeat split; lia) Hcounts) as Hinterval_bound.
  rewrite MarginalBenefitScan_unfold in PreH46.
  destruct PreH46 as [Hcnt Hstrict].
  rewrite ZRange.sum_Z_range_extend_right in Hinterval_bound by lia.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_12_2_split_goal_3 : solve_entail_wit_12_2_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts) (0)))) /\ ((Znth (station) (counts) (0)) <= m_pre)) /\ (0 <= (Znth (station) (arrivals_2) (0)))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  pose proof (Legacy_PreH23 j ltac:(lia)) as Hstation_bounds.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_12_2 : solve_entail_wit_12_2.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_12_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_12_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_12_2_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_1 : solve_entail_wit_13_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof
    (edge_choice_prefix_step__edge_choice
      n_pre current_dist_2 counts_2 latest_2 arrivals_2
      i best pos cnt PreH32 PreH5 PreH6 PreH15 PreH33)
    as [Hbetter Hnot_better].
  apply Hbetter.
  exact PreH1.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_2 : solve_entail_wit_13_1_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_3 : solve_entail_wit_13_1_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_4 : solve_entail_wit_13_1_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_5 : solve_entail_wit_13_1_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_6 : solve_entail_wit_13_1_split_goal_6.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_7 : solve_entail_wit_13_1_split_goal_7.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_8 : solve_entail_wit_13_1_split_goal_8.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress _ _ _ _ _ _ _ _ current_dist_2 _ _ _ |- _ =>
    destruct H as [_ [_ [HF _]]]; apply FeasibleBoostedDistances_unfold in HF;
    destruct HF as [_ [HCurrentDist _]]; specialize (HCurrentDist idx ltac:(lia)) end.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [_ [_ [_ [_ [_ [HD _]]]]]]].
  specialize (HD idx ltac:(lia)). lia.
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_9 : solve_entail_wit_13_1_split_goal_9.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress _ _ _ _ _ _ _ _ current_dist_2 _ _ _ |- _ =>
    destruct H as [_ [_ [HF _]]]; apply FeasibleBoostedDistances_unfold in HF;
    destruct HF as [_ [HCurrentDist _]]; specialize (HCurrentDist idx ltac:(lia)) end.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [_ [_ [_ [_ [_ [HD _]]]]]]].
  specialize (HD idx ltac:(lia)). lia.
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_10 : solve_entail_wit_13_1_split_goal_10.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold BoosterProgress, BusArrivalSchedule in *.
  tauto.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_11 : solve_entail_wit_13_1_split_goal_11.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold BoosterProgress, DestinationCounts in *.
  tauto.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_12 : solve_entail_wit_13_1_split_goal_12.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold BoosterProgress, LatestDepartures in *.
  tauto.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_1_split_goal_13 : solve_entail_wit_13_1_split_goal_13.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold BoosterProgress in *. try rewrite FeasibleBoostedDistances_unfold in *.
  tauto.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_1 : solve_entail_wit_13_1.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_7.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_8.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_9.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_10.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_11.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_12.
  - Goal_apply proof_of_solve_entail_wit_13_1_split_goal_13.
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_1 : solve_entail_wit_13_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof
    (edge_choice_prefix_step__edge_choice
      n_pre current_dist_2 counts_2 latest_2 arrivals_2
      i best pos cnt PreH32 PreH5 PreH6 PreH15 PreH33)
    as [Hbetter Hnot_better].
  apply Hnot_better.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_2 : solve_entail_wit_13_2_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_3 : solve_entail_wit_13_2_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_4 : solve_entail_wit_13_2_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_5 : solve_entail_wit_13_2_split_goal_5.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_6 : solve_entail_wit_13_2_split_goal_6.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_7 : solve_entail_wit_13_2_split_goal_7.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress ?n ?m ?bg ?r ?di ?ts ?os ?ds ?fd ?la ?co ?ar |- _ =>
    pose proof (booster_progress_station_bounds__edge_benefit_and_choice
      n m bg r di ts os ds fd la co ar InputFacts H idx ltac:(lia)) as HB end.
  lia.
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_8 : solve_entail_wit_13_2_split_goal_8.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress _ _ _ _ _ _ _ _ current_dist_2 _ _ _ |- _ =>
    destruct H as [_ [_ [HF _]]]; apply FeasibleBoostedDistances_unfold in HF;
    destruct HF as [_ [HCurrentDist _]]; specialize (HCurrentDist idx ltac:(lia)) end.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [_ [_ [_ [_ [_ [HD _]]]]]]].
  specialize (HD idx ltac:(lia)). lia.
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_9 : solve_entail_wit_13_2_split_goal_9.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  match goal with H : BoosterProgress _ _ _ _ _ _ _ _ current_dist_2 _ _ _ |- _ =>
    destruct H as [_ [_ [HF _]]]; apply FeasibleBoostedDistances_unfold in HF;
    destruct HF as [_ [HCurrentDist _]]; specialize (HCurrentDist idx ltac:(lia)) end.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [_ [_ [_ [_ [_ [HD _]]]]]]].
  specialize (HD idx ltac:(lia)). lia.
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_10 : solve_entail_wit_13_2_split_goal_10.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold BoosterProgress, BusArrivalSchedule in *.
  tauto.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_11 : solve_entail_wit_13_2_split_goal_11.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold BoosterProgress, DestinationCounts in *.
  tauto.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_12 : solve_entail_wit_13_2_split_goal_12.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold BoosterProgress, LatestDepartures in *.
  tauto.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_2_split_goal_13 : solve_entail_wit_13_2_split_goal_13.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold BoosterProgress in *. try rewrite FeasibleBoostedDistances_unfold in *.
  tauto.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_2 : solve_entail_wit_13_2.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_4.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_5.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_6.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_7.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_8.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_9.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_10.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_11.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_12.
  - Goal_apply proof_of_solve_entail_wit_13_2_split_goal_13.
Qed.

Lemma proof_of_solve_entail_wit_13_3_split_goal_1 : solve_entail_wit_13_3_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH17 : forall (edge: Z) , (((0 <= edge) /\ (edge < (n_pre - 1 ))) -> ((0 <= (Znth (edge) (current_dist_2) (0))) /\ ((Znth (edge) (current_dist_2) (0)) <= 100)))) by (intros; repeat split; bus_points; lia).
  eapply edge_choice_prefix_skip__edge_choice.
  - exact PreH1.
  - lia.
  - lia.
  - intros edge Hedge.
    pose proof (Legacy_PreH17 edge Hedge) as Hedge_bounds.
    lia.
  - exact PreH40.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_13_3 : solve_entail_wit_13_3.
Proof.
aggressive_pre_process.
  Goal_apply proof_of_solve_entail_wit_13_3_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_14 : solve_entail_wit_14.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH18 : forall (edge_2: Z) , (((0 <= edge_2) /\ (edge_2 < (n_pre - 1 ))) -> ((0 <= (Znth (edge_2) (current_dist) (0))) /\ ((Znth (edge_2) (current_dist) (0)) <= 100)))) by (intros; repeat split; bus_points; lia).
  assert (Hi : i = n_pre - 1) by lia.
  subst i.
  assert (Hbest : 0 < best) by lia.
  assert (Hchoice :
    BestBoostChoice n_pre current_dist counts_2 latest_2 arrivals best pos).
  {
    unfold BestBoostChoice.
    exact PreH41.
  }
  pose proof (best_boost_choice_positive_edge__saturation
    n_pre current_dist counts_2 latest_2 arrivals best pos
    Hbest Hchoice) as [Hpos_range Hpos_positive].
  assert (Hnew_dist_length :
    Zlength (replace_Znth pos (Znth pos current_dist 0 - 1) current_dist) =
    n_pre - 1).
  {
    rewrite Zlength_replace_Znth.
    exact PreH28.
  }
  assert (Hnew_dist_bounds : forall edge,
    0 <= edge < n_pre - 1 ->
    0 <= Znth edge
      (replace_Znth pos (Znth pos current_dist 0 - 1) current_dist) 0 <=
      100).
  {
    intros edge Hedge.
    destruct (Z.eq_dec edge pos) as [Heq | Hne].
    - subst edge.
      rewrite Znth_replace_Znth_Same by lia.
      specialize (Legacy_PreH18 pos ltac:(lia)).
      lia.
    - rewrite Znth_replace_Znth_Diff by lia.
      apply Legacy_PreH18.
      exact Hedge.
  }
  assert (Hrepair :
    ArrivalRepairProgress n_pre current_dist arrivals
      (replace_Znth pos (Znth pos current_dist 0 - 1) current_dist)
      arrivals latest_2 pos (pos + 1)).
  {
    eapply arrival_repair_progress_init__arrival_repair;
      eauto.
  }
  Exists counts_2 latest_2 arrivals arrivals
    (replace_Znth pos (Znth pos current_dist 0 - 1) current_dist)
    current_dist.
  split_pure_spatial.
  - bus_cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_15 : solve_entail_wit_15.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH20 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((((((0 <= (Znth (station) (latest_2) (0))) /\ ((Znth (station) (latest_2) (0)) <= 100000)) /\ (0 <= (Znth (station) (counts_2) (0)))) /\ ((Znth (station) (counts_2) (0)) <= m_pre)) /\ (0 <= (Znth (station) (new_arrivals_2) (0)))) /\ ((Znth (station) (new_arrivals_2) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  assert (Hi_range : 0 <= i < n_pre) by lia.
  assert (Hnew_arrivals_length :
    Zlength
      (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2) =
    n_pre).
  {
    rewrite Zlength_replace_Znth.
    exact PreH30.
  }
  assert (Hnew_arrivals_bounds : forall station,
    0 <= station < n_pre ->
    (((0 <= Znth station latest_2 0 <= 100000 /\
       0 <= Znth station counts_2 0) /\
      Znth station counts_2 0 <= m_pre) /\
     0 <= Znth station
       (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2) 0) /\
    Znth station
      (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2) 0 <=
    200000).
  {
    intros station Hstation.
    specialize (Legacy_PreH20 station Hstation).
    destruct (Z.eq_dec station i) as [Heq | Hne].
    - subst station.
      rewrite Znth_replace_Znth_Same by lia.
      rewrite Znth_replace_Znth_Same in PreH1 by lia.
      destruct Legacy_PreH20 as
        [[[[Hlatest_bounds Hcount_lower] Hcount_upper]
          Harrival_lower] Harrival_upper].
      repeat split; try assumption; lia.
    - rewrite Znth_replace_Znth_Diff by lia.
      exact Legacy_PreH20.
  }
  assert (Hrepair :
    ArrivalRepairProgress n_pre old_dist_2 old_arrivals_2 new_dist_2
      (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2)
      latest_2 pos (i + 1)).
  {
    eapply arrival_repair_progress_step__arrival_repair;
      eauto; lia.
  }
  Exists counts_2 latest_2
    (replace_Znth i (Znth i new_arrivals_2 0 - 1) new_arrivals_2)
    old_arrivals_2 new_dist_2 old_dist_2.
  split_pure_spatial.
  - bus_cancel.
  - split_pures.
    all: dump_pre_spatial.
    all: try assumption.
    all: try lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_16_1_split_goal_1 : solve_entail_wit_16_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  assert (Hi : i = n_pre) by lia.
  subst i.
  assert (Houtcome :
    ArrivalRepairOutcome n_pre old_dist old_arrivals
      new_dist new_arrivals latest_2 pos).
  {
    eapply arrival_repair_progress_outcome__arrival_repair
      with (new_arrivals := new_arrivals) (stop := n_pre);
      eauto; try lia.
  }
  assert (Hcertificate : SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best).
  { eapply selected_exchange_certificate_from_repair__normalization; eauto. }
  pose proof PreH40 as Hprogress_fields.
  unfold BoosterProgress in Hprogress_fields.
  destruct Hprogress_fields as
    [Hlatest [Hcounts [Hfeasible [Hschedule
      [old_total [Hold_total Hold_minimum]]]]]].
  assert (Hnew_feasible :
    FeasibleBoostedDistances
      n_pre (k_pre - (k - 1)) dist new_dist).
  {
    eapply feasible_boosted_distances_step__exchange_certificate_transition;
      eauto.
  }
  assert (Hnew_schedule :
    BusArrivalSchedule n_pre new_dist latest_2 new_arrivals).
  {
    eapply arrival_repair_outcome_schedule__saturation; eauto.
  }
  assert (Hnew_total :
    PassengerTravelTotal
      m_pre times destinations new_arrivals (old_total - best)).
  {
    eapply passenger_travel_total_after_repair__saturation; eauto.
  }
  assert (Hnew_minimum :
    SightseeingMinimumTotal
      n_pre m_pre (k_pre - (k - 1))
      dist times origins destinations (old_total - best)).
  {
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset.
    exists (old_total - best).
    split.
    - split.
      + unfold SightseeingCandidateTotal.
        exists new_dist, latest_2, new_arrivals.
        exact (conj Hlatest
          (conj Hnew_feasible (conj Hnew_schedule Hnew_total))).
      + intros candidate_total Hcandidate.
        eapply selected_exchange_adjacent_lower_bound__exchange;
          try eassumption.
        replace (k_pre - k + 1) with (k_pre - (k - 1)) by lia.
        exact Hcandidate.
    - reflexivity.
  }
  pose proof Hnew_feasible as Hnew_feasible_fields.
  rewrite FeasibleBoostedDistances_unfold in Hnew_feasible_fields.
  try rewrite FeasibleBoostedDistances_unfold in Hnew_feasible_fields.
  destruct Hnew_feasible_fields as
    [Hnew_dist_length [Hnew_dist_bounds Hnew_budget]].
  assert (Hnew_total_nonnegative : 0 <= old_total - best).
  {
    eapply passenger_travel_total_nonnegative__exchange_certificate_transition
      with (n := n_pre) (initial_dist := dist)
           (origins := origins) (final_dist := new_dist)
           (latest := latest_2) (arrivals := new_arrivals);
      eauto.
    intros edge Hedge.
    exact (proj1 (Hnew_dist_bounds edge Hedge)).
  }
  unfold BoosterProgress.
  split; [exact Hlatest |].
  split; [exact Hcounts |].
  split; [exact Hnew_feasible |].
  split; [exact Hnew_schedule |].
  exists (old_total - best).
  split; [exact Hnew_total |].
  exact Hnew_minimum.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_16_1 : solve_entail_wit_16_1.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_solve_entail_wit_16_1_split_goal_1.
Qed.

Lemma proof_of_solve_entail_wit_16_2_split_goal_1 : solve_entail_wit_16_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  assert (Hnew_arrivals_length :
    Zlength
      (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals) =
    n_pre).
  {
    rewrite Zlength_replace_Znth.
    exact PreH30.
  }
  assert (Houtcome :
    ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist
      (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals)
      latest_2 pos).
  {
    eapply arrival_repair_progress_outcome__arrival_repair
      with (new_arrivals := new_arrivals) (stop := i).
    - exact PreH30.
    - lia.
    - lia.
    - exact PreH43.
    - right.
      repeat split; try assumption; reflexivity.
  }
  assert (Hcertificate : SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best).
  { eapply selected_exchange_certificate_from_repair__normalization; eauto. }
  pose proof PreH41 as Hprogress_fields.
  unfold BoosterProgress in Hprogress_fields.
  destruct Hprogress_fields as
    [Hlatest [Hcounts [Hfeasible [Hschedule
      [old_total [Hold_total Hold_minimum]]]]]].
  assert (Hnew_feasible :
    FeasibleBoostedDistances
      n_pre (k_pre - (k - 1)) dist new_dist).
  {
    eapply feasible_boosted_distances_step__exchange_certificate_transition;
      eauto.
  }
  assert (Hnew_schedule :
    BusArrivalSchedule n_pre new_dist latest_2 (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals)).
  {
    eapply arrival_repair_outcome_schedule__saturation; eauto.
  }
  assert (Hnew_total :
    PassengerTravelTotal
      m_pre times destinations (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals) (old_total - best)).
  {
    eapply passenger_travel_total_after_repair__saturation; eauto.
  }
  assert (Hnew_minimum :
    SightseeingMinimumTotal
      n_pre m_pre (k_pre - (k - 1))
      dist times origins destinations (old_total - best)).
  {
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset.
    exists (old_total - best).
    split.
    - split.
      + unfold SightseeingCandidateTotal.
        exists new_dist, latest_2, (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals).
        exact (conj Hlatest
          (conj Hnew_feasible (conj Hnew_schedule Hnew_total))).
      + intros candidate_total Hcandidate.
        eapply selected_exchange_adjacent_lower_bound__exchange;
          try eassumption.
        replace (k_pre - k + 1) with (k_pre - (k - 1)) by lia.
        exact Hcandidate.
    - reflexivity.
  }
  pose proof Hnew_feasible as Hnew_feasible_fields.
  rewrite FeasibleBoostedDistances_unfold in Hnew_feasible_fields.
  try rewrite FeasibleBoostedDistances_unfold in Hnew_feasible_fields.
  destruct Hnew_feasible_fields as
    [Hnew_dist_length [Hnew_dist_bounds Hnew_budget]].
  assert (Hnew_total_nonnegative : 0 <= old_total - best).
  {
    eapply passenger_travel_total_nonnegative__exchange_certificate_transition
      with (n := n_pre) (initial_dist := dist)
           (origins := origins) (final_dist := new_dist)
           (latest := latest_2) (arrivals := (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals));
      eauto.
    intros edge Hedge.
    exact (proj1 (Hnew_dist_bounds edge Hedge)).
  }
  unfold BoosterProgress.
  split; [exact Hlatest |].
  split; [exact Hcounts |].
  split; [exact Hnew_feasible |].
  split; [exact Hnew_schedule |].
  exists (old_total - best).
  split; [exact Hnew_total |].
  exact Hnew_minimum.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_16_2_split_goal_2 : solve_entail_wit_16_2_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  assert (Hnew_arrivals_length :
    Zlength
      (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals) =
    n_pre).
  {
    rewrite Zlength_replace_Znth.
    exact PreH30.
  }
  assert (Houtcome :
    ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist
      (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals)
      latest_2 pos).
  {
    eapply arrival_repair_progress_outcome__arrival_repair
      with (new_arrivals := new_arrivals) (stop := i).
    - exact PreH30.
    - lia.
    - lia.
    - exact PreH43.
    - right.
      repeat split; try assumption; reflexivity.
  }
  assert (Hcertificate : SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best).
  { eapply selected_exchange_certificate_from_repair__normalization; eauto. }
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  assert (HB : 0 <= Znth idx (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals) 0 <= 200000) by
    (eapply arrival_repair_outcome_bounds__exchange_certificate_transition; eauto; lia).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_16_2_split_goal_3 : solve_entail_wit_16_2_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  assert (Hnew_arrivals_length :
    Zlength
      (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals) =
    n_pre).
  {
    rewrite Zlength_replace_Znth.
    exact PreH30.
  }
  assert (Houtcome :
    ArrivalRepairOutcome n_pre old_dist old_arrivals new_dist
      (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals)
      latest_2 pos).
  {
    eapply arrival_repair_progress_outcome__arrival_repair
      with (new_arrivals := new_arrivals) (stop := i).
    - exact PreH30.
    - lia.
    - lia.
    - exact PreH43.
    - right.
      repeat split; try assumption; reflexivity.
  }
  assert (Hcertificate : SelectedExchangeCertificate n_pre m_pre k_pre k dist times origins destinations old_dist latest_2 counts_2 old_arrivals best).
  { eapply selected_exchange_certificate_from_repair__normalization; eauto. }
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  assert (HB : 0 <= Znth idx (replace_Znth i (Znth i new_arrivals 0 - 1) new_arrivals) 0 <= 200000) by
    (eapply arrival_repair_outcome_bounds__exchange_certificate_transition; eauto; lia).
  lia.
Qed.

Lemma proof_of_solve_entail_wit_16_2_split_goal_4 : solve_entail_wit_16_2_split_goal_4.
Proof.
 LLM_pre_process ltac:(lia || int_auto). rewrite Zlength_replace_Znth. assumption.
Qed.

Lemma proof_of_solve_entail_wit_16_2 : solve_entail_wit_16_2.
Proof.
 aggressive_pre_process.
 - Goal_apply proof_of_solve_entail_wit_16_2_split_goal_1.
 - Goal_apply proof_of_solve_entail_wit_16_2_split_goal_2.
 - Goal_apply proof_of_solve_entail_wit_16_2_split_goal_3.
 - Goal_apply proof_of_solve_entail_wit_16_2_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_17_1_split_goal_1 : solve_entail_wit_17_1_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_17_1_split_goal_2 : solve_entail_wit_17_1_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [_ [_ [_ [_ [_ [_ HP]]]]]]].
  specialize (HP idx ltac:(lia)). lia.
Qed.

Lemma proof_of_solve_entail_wit_17_1_split_goal_3 : solve_entail_wit_17_1_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  unfold BoosterProgress in PreH32.
  unfold OptimizedBusState.
  replace (k_pre - k) with k_pre in PreH32 by lia.
  exact PreH32.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_17_1 : solve_entail_wit_17_1.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_17_1_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_17_1_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_17_1_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_17_2_split_goal_1 : solve_entail_wit_17_2_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_17_2_split_goal_2 : solve_entail_wit_17_2_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [_ [_ [_ [_ [_ [_ HP]]]]]]].
  specialize (HP idx ltac:(lia)). lia.
Qed.

Lemma proof_of_solve_entail_wit_17_2_split_goal_3 : solve_entail_wit_17_2_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  assert (Hbest_choice :
    BestBoostChoice n_pre current_dist counts_2 latest_2 arrivals_2
      best pos).
  {
    unfold BestBoostChoice.
    replace (n_pre - 1) with i by lia.
    exact PreH40.
  }
  assert (Hbest_zero : best = 0).
  {
    unfold EdgeChoicePrefix in PreH40.
    destruct PreH40 as [Hmaximum [Hdefault | Heligible]].
    - tauto.
    - unfold EligibleEdgeBenefit in Heligible.
      cbn in Heligible.
      lia.
  }
  exact (booster_progress_zero_best_optimized__termination_and_travel_total
    n_pre m_pre k_pre k dist times origins destinations
    current_dist latest_2 counts_2 arrivals_2 best pos
    ltac:(lia) PreH4 InputFacts PreH39 Hbest_choice Hbest_zero).

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_17_2 : solve_entail_wit_17_2.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_17_2_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_17_2_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_17_2_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_17_3_split_goal_1 : solve_entail_wit_17_3_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_17_3_split_goal_2 : solve_entail_wit_17_3_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  apply (proj2 (Forall_Znth _ 0 _)). intros idx Hi.
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [_ [_ [_ [_ [_ [_ HP]]]]]]].
  specialize (HP idx ltac:(lia)). lia.
Qed.

Lemma proof_of_solve_entail_wit_17_3_split_goal_3 : solve_entail_wit_17_3_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  assert (Hbest_choice :
    BestBoostChoice n_pre current_dist counts_2 latest_2 arrivals_2
      best pos).
  {
    unfold BestBoostChoice.
    replace (n_pre - 1) with i by lia.
    exact PreH41.
  }
  exact (booster_progress_zero_best_optimized__termination_and_travel_total
    n_pre m_pre k_pre k dist times origins destinations
    current_dist latest_2 counts_2 arrivals_2 best pos
    ltac:(lia) PreH5 InputFacts PreH40 Hbest_choice PreH1).

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_17_3 : solve_entail_wit_17_3.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_17_3_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_17_3_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_17_3_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_18_split_goal_1 : solve_entail_wit_18_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) by (intros; repeat split; bus_points; lia).
  pose proof (Legacy_PreH24 i ltac:(lia)) as Hpassenger_bounds.
  destruct Hpassenger_bounds as [[Htime Hdestination_lower] Hdestination_upper].
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_18_split_goal_2 : solve_entail_wit_18_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) by (intros; repeat split; bus_points; lia).
  pose proof (Legacy_PreH24 i ltac:(lia)) as Hpassenger_bounds.
  destruct Hpassenger_bounds as [[Htime Hdestination_lower] Hdestination_upper].
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_18 : solve_entail_wit_18.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_18_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_18_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_19_split_goal_1 : solve_entail_wit_19_split_goal_1.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof (travel_sum_prefix_step__travel_and_return
    m_pre times destinations arrivals_2 i ans
    PreH15 PreH11 PreH40) as Hstep.
  unfold TravelSumPrefix in Hstep.
  unfold TravelSumPrefix.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_19_split_goal_2 : solve_entail_wit_19_split_goal_2.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  all: assert (Legacy_PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) by (intros; repeat split; bus_points; lia).
  pose proof (Legacy_PreH23 (Znth i destinations 0 - 1) ltac:(lia))
    as Harrival_bounds.
  pose proof (Legacy_PreH24 i ltac:(lia)) as Hpassenger_bounds.
  destruct Hpassenger_bounds as [[Htime Hdestination_lower] Hdestination_upper].
  unfold SightseeingInputsBounded in InputFacts.
  destruct InputFacts as [_ [Hm _]].
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_19_split_goal_3 : solve_entail_wit_19_split_goal_3.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  all: assert (Legacy_PreH23 : forall (station: Z) , (((0 <= station) /\ (station < n_pre)) -> ((0 <= (Znth (station) (arrivals_2) (0))) /\ ((Znth (station) (arrivals_2) (0)) <= 200000)))) by (intros; repeat split; bus_points; lia).
  all: assert (Legacy_PreH24 : forall (passenger: Z) , (((0 <= passenger) /\ (passenger < m_pre)) -> ((((0 <= (Znth (passenger) (times) (0))) /\ ((Znth (passenger) (times) (0)) <= 100000)) /\ (1 <= (Znth (passenger) (destinations) (0)))) /\ ((Znth (passenger) (destinations) (0)) <= n_pre)))) by (intros; repeat split; bus_points; lia).
  pose proof (Legacy_PreH23 (Znth i destinations 0 - 1) ltac:(lia))
    as Harrival_bounds.
  pose proof (Legacy_PreH24 i ltac:(lia)) as Hpassenger_bounds.
  destruct Hpassenger_bounds as [[Htime Hdestination_lower] Hdestination_upper].
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_19_split_goal_4 : solve_entail_wit_19_split_goal_4.
Proof.
LLM_pre_process ltac:(lia || int_auto).
  all: try (bus_make_inputs n_pre m_pre dist times origins destinations).
  all: bus_shapes.
  pose proof PreH35 as Hoptimized.
  unfold OptimizedBusState in Hoptimized.
  destruct Hoptimized as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hoptimum]]]].
  pose proof Hfeasible as Hfeasible_fields.
  rewrite FeasibleBoostedDistances_unfold in Hfeasible_fields.
  try rewrite FeasibleBoostedDistances_unfold in Hfeasible_fields.
  destruct Hfeasible_fields as [_ [Hdist_bounds _]].
  assert (Hdist_nonnegative : forall edge, 0 <= edge < n_pre - 1 ->
    0 <= Znth edge final_dist_2 0).
  {
    intros edge Hedge.
    specialize (Hdist_bounds edge Hedge).
    lia.
  }
  pose proof (arrival_dominates_passenger_time__travel_and_return
    n_pre m_pre dist times origins destinations
    final_dist_2 latest_2 arrivals_2 i
    InputFacts Hlatest (or_intror Hdist_nonnegative) Hschedule ltac:(lia))
    as Harrival_dominates.
  lia.

  all: try solve [bus_forall].
  all: try solve [intros; bus_points; lia].
  all: try solve [rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; cbn; lia].
Qed.

Lemma proof_of_solve_entail_wit_19 : solve_entail_wit_19.
Proof.
aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_19_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_19_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_19_split_goal_3.
  - Goal_apply proof_of_solve_entail_wit_19_split_goal_4.
Qed.

Lemma proof_of_solve_entail_wit_20 : solve_entail_wit_20.
Proof.
  unfold solve_entail_wit_20; right; intros.
  assert (Hi : i = m_pre) by lia. subst i.
  assert (HT : PassengerTravelTotal m_pre times destinations arrivals ans).
  { apply (proj1 (travel_sum_prefix_complete__travel_and_return m_pre times destinations arrivals ans ltac:(lia))). eassumption. }
  assert (Hminimum : SightseeingMinimumTotal n_pre m_pre k_pre dist times origins destinations ans).
  { destruct PreH25 as [_ [_ [_ [_ [opt [HO HM]]]]]].
    unfold PassengerTravelTotal in HT, HO; replace ans with opt by lia; exact HM. }
  sep_apply_l_atomic (IntArray.full_to_undef_full (&("late")) n_pre latest).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("late")) n_pre).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("late")) 0 n_pre 1000 ltac:(lia)).
  sep_apply_l_atomic (IntArray.full_to_undef_full (&("off")) n_pre counts).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("off")) n_pre).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("off")) 0 n_pre 1000 ltac:(lia)).
  sep_apply_l_atomic (IntArray.full_to_undef_full (&("arr")) n_pre arrivals).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("arr")) n_pre).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("arr")) 0 n_pre 1000 ltac:(lia)).
  rewrite ?Z.mul_0_l, ?Z.add_0_r, ?Z.sub_0_r.
  remember 1000 as scratch_capacity eqn:Hscratch_capacity.
  apply _derivable1_andp_intros.
  - dump_pre_spatial; exact Hminimum.
  - cancel (IntArray.undef_full (&("late")) scratch_capacity).
    cancel (IntArray.undef_full (&("off")) scratch_capacity).
    all: apply derivable1_refl.
Qed.
