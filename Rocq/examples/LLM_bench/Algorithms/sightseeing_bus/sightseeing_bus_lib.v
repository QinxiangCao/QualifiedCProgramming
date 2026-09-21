From Coq Require Import ZArith List Lia.
From AUXLib Require Import ListLib MonotonicList.
From SumLib Require Import Sum ZRange.
From MaxMinLib Require Import MaxMin Interface.

Import ListNotations.
Local Open Scope Z_scope.

Lemma bus_Forall2_indexed {A B : Type} (R : A -> B -> Prop)
    (f : Z -> A) (g : Z -> B) lo hi :
  Forall2 R (map f (Zrange lo hi)) (map g (Zrange lo hi)) <->
  forall p, lo <= p < hi -> R (f p) (g p).
Proof.
  assert (Hmap : forall xs, Forall2 R (map f xs) (map g xs) <->
    Forall (fun p => R (f p) (g p)) xs).
  { induction xs as [|x xs IH]; cbn.
    - split; intros; constructor.
    - split; intro H; inversion H; subst; constructor; try assumption;
      apply IH; assumption. }
  rewrite Hmap, Forall_forall. split; intros H p Hp; apply H;
    [apply In_Zrange | apply In_Zrange]; assumption.
Qed.

Lemma bus_Forall_prefix (P : Z -> Prop) l k :
  0 <= k <= Zlength l ->
  (Forall P (sublist 0 k l) <->
   forall i, 0 <= i < k -> P (Znth i l 0)).
Proof.
  intros Hk. rewrite (Forall_Znth P 0 (sublist 0 k l)), Zlength_sublist0 by lia.
  split; intros H i Hi.
  - specialize (H i Hi). rewrite Znth_sublist0 in H by lia. exact H.
  - rewrite Znth_sublist0 by lia. apply H. exact Hi.
Qed.

Lemma bus_Forall2_Znth (R : Z -> Z -> Prop) xs ys i :
  Forall2 R xs ys -> 0 <= i < Zlength xs -> R (Znth i xs 0) (Znth i ys 0).
Proof.
  intros H Hi. apply (proj1 (Forall2_nth_iff Z Z R xs ys 0 0)) in H.
  destruct H as [Hlen Hpoint]. unfold Znth. apply Hpoint.
  rewrite Zlength_correct in Hi. lia.
Qed.

(** Compatibility premise retained for the existing arithmetic helpers.
    The C contracts and invariants spell its conditions out with Forall/Forall2. *)
Definition SightseeingInputsBounded
    (n m : Z) (dist times origins destinations : list Z) : Prop :=
  2 <= n <= 1000 /\
  1 <= m <= 10000 /\
  Zlength dist = n - 1 /\
  Zlength times = m /\
  Zlength origins = m /\
  Zlength destinations = m /\
  (forall edge, 0 <= edge < n - 1 ->
     0 <= Znth edge dist 0 <= 100) /\
  (forall passenger, 0 <= passenger < m ->
     0 <= Znth passenger times 0 <= 100000 /\
     1 <= Znth passenger origins 0 < Znth passenger destinations 0 /\
     Znth passenger destinations 0 <= n).

(* The latest passenger-arrival time at a station is expressed through the
   project MaxMin library.  The default 0 covers stations with no passengers. *)
Definition LatestAtStation
    (m : Z) (times origins : list Z) (station latest : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun passenger =>
       0 <= passenger < m /\
       Znth passenger origins 0 = station + 1)
    (fun passenger => Znth passenger times 0)
    0 latest.

Definition LatestDepartures
    (n m : Z) (times origins latest : list Z) : Prop :=
  Zlength latest = n /\
  forall station, 0 <= station < n ->
    LatestAtStation m times origins station (Znth station latest 0).

Definition DestinationCounts
    (n m : Z) (destinations counts : list Z) : Prop :=
  Zlength counts = n /\
  forall station, 0 <= station < n ->
    Znth station counts 0 =
      sum (fun passenger =>
             0 <= passenger < m /\
             Znth passenger destinations 0 = station + 1)
          (fun _ => 1).

Definition FeasibleBoostedDistances
    (n budget : Z) (initial_dist final_dist : list Z) : Prop :=
  Zlength final_dist = n - 1 /\
  Forall2 (fun final initial => 0 <= final <= initial)
    (map (fun edge => Znth edge final_dist 0) (Zrange 0 (n - 1)))
    (map (fun edge => Znth edge initial_dist 0) (Zrange 0 (n - 1))) /\
  sum (fun edge => 0 <= edge < n - 1)
      (fun edge =>
         Znth edge initial_dist 0 - Znth edge final_dist 0) <= budget.

Lemma FeasibleBoostedDistances_unfold n budget initial_dist final_dist :
  FeasibleBoostedDistances n budget initial_dist final_dist <->
  Zlength final_dist = n - 1 /\
  (forall edge, 0 <= edge < n - 1 ->
    0 <= Znth edge final_dist 0 <= Znth edge initial_dist 0) /\
  sum (fun edge => 0 <= edge < n - 1)
    (fun edge => Znth edge initial_dist 0 - Znth edge final_dist 0) <= budget.
Proof. unfold FeasibleBoostedDistances. rewrite bus_Forall2_indexed. reflexivity. Qed.

(* A departure is the larger of the bus-arrival time and the latest passenger
   arrival time.  This maximum is deliberately represented by MaxMinLib. *)
Definition StationDeparture
    (arrivals latest : list Z) (station departure : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun candidate => candidate = Znth station latest 0)
    (fun candidate => candidate)
    (Znth station arrivals 0) departure.

Definition BusArrivalSchedule
    (n : Z) (dist latest arrivals : list Z) : Prop :=
  Zlength arrivals = n /\
  Znth 0 arrivals 0 = 0 /\
  forall station, 0 <= station < n - 1 ->
    exists departure,
      StationDeparture arrivals latest station departure /\
      Znth (station + 1) arrivals 0 =
        departure + Znth station dist 0.

Definition PassengerTravelTotal
    (m : Z) (times destinations arrivals : list Z) (total : Z) : Prop :=
  total =
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) arrivals 0 -
           Znth passenger times 0).

Definition SightseeingCandidateTotal
    (n m budget : Z)
    (initial_dist times origins destinations : list Z)
    (total : Z) : Prop :=
  exists final_dist latest arrivals,
    LatestDepartures n m times origins latest /\
    FeasibleBoostedDistances n budget initial_dist final_dist /\
    BusArrivalSchedule n final_dist latest arrivals /\
    PassengerTravelTotal m times destinations arrivals total.

Definition SightseeingMinimumTotal
    (n m budget : Z)
    (initial_dist times origins destinations : list Z)
    (answer : Z) : Prop :=
  min_value_of_subset Z.le
    (SightseeingCandidateTotal
       n m budget initial_dist times origins destinations)
    (fun total => total) answer.

Definition SightseeingOptimalState
    (n m budget : Z)
    (initial_dist times origins destinations : list Z)
    (final_dist latest arrivals : list Z)
    (answer : Z) : Prop :=
  LatestDepartures n m times origins latest /\
  FeasibleBoostedDistances n budget initial_dist final_dist /\
  BusArrivalSchedule n final_dist latest arrivals /\
  PassengerTravelTotal m times destinations arrivals answer /\
  SightseeingMinimumTotal
    n m budget initial_dist times origins destinations answer.

(* ------------------------------------------------------------------------- *)
(* Internal annotation states.  These declarations describe stable program
   points; array ownership, loop-index bounds, and [@pre] bridges stay in C. *)

Definition StationSummaryState
    (n m : Z) (times origins destinations latest counts : list Z) : Prop :=
  LatestDepartures n m times origins latest /\
  DestinationCounts n m destinations counts.

Definition CanonicalBusState
    (n m : Z)
    (times origins destinations dist latest counts arrivals : list Z) : Prop :=
  StationSummaryState n m times origins destinations latest counts /\
  BusArrivalSchedule n dist latest arrivals.

Definition WorkspacesZeroPrefix
    (latest counts : list Z) (processed : Z) : Prop :=
  Forall (fun x => x = 0) (sublist 0 processed latest) /\
  Forall (fun x => x = 0) (sublist 0 processed counts).

Lemma WorkspacesZeroPrefix_unfold latest counts processed :
  0 <= processed -> processed <= Zlength latest -> processed <= Zlength counts ->
  (WorkspacesZeroPrefix latest counts processed <->
   forall station, 0 <= station < processed ->
     Znth station latest 0 = 0 /\ Znth station counts 0 = 0).
Proof.
  intros H0 Hl Hc. unfold WorkspacesZeroPrefix.
  rewrite !bus_Forall_prefix by lia. firstorder.
Qed.


Definition LatestAtStationPrefix
    (m : Z) (times origins : list Z)
    (processed station latest : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun passenger =>
       0 <= passenger < processed /\
       passenger < m /\
       Znth passenger origins 0 = station + 1)
    (fun passenger => Znth passenger times 0)
    0 latest.

Definition PassengerAggregationPrefix
    (n m : Z) (times origins destinations : list Z)
    (processed : Z) (latest counts : list Z) : Prop :=
  (forall station, 0 <= station < n ->
     LatestAtStationPrefix
       m times origins processed station (Znth station latest 0)) /\
  (forall station, 0 <= station < n ->
     Znth station counts 0 =
       sum (fun passenger =>
              0 <= passenger < processed /\
              passenger < m /\
              Znth passenger destinations 0 = station + 1)
           (fun _ => 1)).

Definition ArrivalSimulationPrefix
    (n : Z) (dist latest arrivals : list Z)
    (processed next_arrival : Z) : Prop :=
  (forall station, 0 <= station < processed ->
     (station = 0 /\ Znth station arrivals 0 = 0) \/
     (0 < station /\
      exists departure,
        StationDeparture arrivals latest (station - 1) departure /\
        Znth station arrivals 0 =
          departure + Znth (station - 1) dist 0)) /\
  ((processed = 0 /\ next_arrival = 0) \/
   (0 < processed /\
    exists departure,
      StationDeparture arrivals latest (processed - 1) departure /\
      next_arrival =
        departure + Znth (processed - 1) dist 0)).

Definition MarginalBenefitScan
    (counts latest arrivals : list Z)
    (edge next_station benefit : Z) : Prop :=
  benefit =
    sum (fun station => edge + 1 <= station < next_station)
        (fun station => Znth station counts 0) /\
  Forall2 Z.lt
    (map (fun station => Znth station latest 0) (Zrange (edge + 1) next_station))
    (map (fun station => Znth station arrivals 0) (Zrange (edge + 1) next_station)).

Lemma MarginalBenefitScan_unfold counts latest arrivals edge next_station benefit :
  MarginalBenefitScan counts latest arrivals edge next_station benefit <->
  benefit = sum (fun station => edge + 1 <= station < next_station)
    (fun station => Znth station counts 0) /\
  forall station, edge + 1 <= station < next_station ->
    Znth station latest 0 < Znth station arrivals 0.
Proof. unfold MarginalBenefitScan. rewrite bus_Forall2_indexed. reflexivity. Qed.


Definition EdgeMarginalBenefit
    (n : Z) (counts latest arrivals : list Z)
    (edge benefit : Z) : Prop :=
  exists stop,
    edge + 2 <= stop <= n /\
    Forall2 Z.lt
      (map (fun station => Znth station latest 0) (Zrange (edge + 1) (stop - 1)))
      (map (fun station => Znth station arrivals 0) (Zrange (edge + 1) (stop - 1))) /\
    (stop = n \/
     Znth (stop - 1) arrivals 0 <= Znth (stop - 1) latest 0) /\
    benefit =
      sum (fun station => edge + 1 <= station < stop)
          (fun station => Znth station counts 0).

Lemma EdgeMarginalBenefit_unfold n counts latest arrivals edge benefit :
  EdgeMarginalBenefit n counts latest arrivals edge benefit <->
  exists stop, edge + 2 <= stop <= n /\
    (forall station, edge + 1 <= station < stop - 1 ->
      Znth station latest 0 < Znth station arrivals 0) /\
    (stop = n \/ Znth (stop - 1) arrivals 0 <= Znth (stop - 1) latest 0) /\
    benefit = sum (fun station => edge + 1 <= station < stop)
      (fun station => Znth station counts 0).
Proof. unfold EdgeMarginalBenefit. setoid_rewrite bus_Forall2_indexed. reflexivity. Qed.

Definition EligibleEdgeBenefit
    (n : Z) (dist counts latest arrivals : list Z)
    (scanned : Z) (choice : Z * Z) : Prop :=
  let '(edge, benefit) := choice in
  0 <= edge < scanned /\
  edge < n - 1 /\
  0 < Znth edge dist 0 /\
  EdgeMarginalBenefit n counts latest arrivals edge benefit.

Definition EdgeChoicePrefix
    (n : Z) (dist counts latest arrivals : list Z)
    (scanned best position : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (EligibleEdgeBenefit n dist counts latest arrivals scanned)
    (fun choice => snd choice) 0 best /\
  ((best = 0 /\ position = -1) \/
   EligibleEdgeBenefit
     n dist counts latest arrivals scanned (position, best)).

Definition BestBoostChoice
    (n : Z) (dist counts latest arrivals : list Z)
    (best position : Z) : Prop :=
  EdgeChoicePrefix
    n dist counts latest arrivals (n - 1) best position.

Definition ArrivalRepairProgress
    (n : Z)
    (old_dist old_arrivals new_dist new_arrivals latest : list Z)
    (edge next_station : Z) : Prop :=
  (forall candidate_edge, 0 <= candidate_edge < n - 1 ->
     Znth candidate_edge new_dist 0 =
       if Z.eq_dec candidate_edge edge
       then Znth candidate_edge old_dist 0 - 1
       else Znth candidate_edge old_dist 0) /\
  Forall2 eq
    (map (fun station => Znth station new_arrivals 0) (Zrange 0 (edge + 1)))
    (map (fun station => Znth station old_arrivals 0) (Zrange 0 (edge + 1))) /\
  Forall2 (fun current previous =>
      current = fst previous - 1 /\ snd previous <= current)
    (map (fun station => Znth station new_arrivals 0) (Zrange (edge + 1) next_station))
    (map (fun station => (Znth station old_arrivals 0, Znth station latest 0))
      (Zrange (edge + 1) next_station)) /\
  Forall2 eq
    (map (fun station => Znth station new_arrivals 0) (Zrange next_station n))
    (map (fun station => Znth station old_arrivals 0) (Zrange next_station n)).

Definition ArrivalRepairOutcome
    (n : Z)
    (old_dist old_arrivals new_dist new_arrivals latest : list Z)
    (edge : Z) : Prop :=
  exists stop,
    edge + 1 <= stop <= n /\
    (forall candidate_edge, 0 <= candidate_edge < n - 1 ->
       Znth candidate_edge new_dist 0 =
         if Z.eq_dec candidate_edge edge
         then Znth candidate_edge old_dist 0 - 1
         else Znth candidate_edge old_dist 0) /\
    Forall2 eq
      (map (fun station => Znth station new_arrivals 0) (Zrange 0 (edge + 1)))
      (map (fun station => Znth station old_arrivals 0) (Zrange 0 (edge + 1))) /\
    Forall2 (fun current previous =>
        current = fst previous - 1 /\ snd previous <= current)
      (map (fun station => Znth station new_arrivals 0) (Zrange (edge + 1) stop))
      (map (fun station => (Znth station old_arrivals 0, Znth station latest 0))
        (Zrange (edge + 1) stop)) /\
    ((stop = n /\
      Forall2 (fun current previous => current = previous - 1)
        (map (fun station => Znth station new_arrivals 0) (Zrange (edge + 1) n))
        (map (fun station => Znth station old_arrivals 0) (Zrange (edge + 1) n))) \/
     (stop < n /\
      Znth stop new_arrivals 0 = Znth stop old_arrivals 0 - 1 /\
      Znth stop new_arrivals 0 < Znth stop latest 0 /\
      Forall2 eq
        (map (fun station => Znth station new_arrivals 0) (Zrange (stop + 1) n))
        (map (fun station => Znth station old_arrivals 0) (Zrange (stop + 1) n)))).

Lemma ArrivalRepairProgress_unfold n old_dist old_arrivals new_dist new_arrivals latest edge next_station :
  ArrivalRepairProgress n old_dist old_arrivals new_dist new_arrivals latest edge next_station <->
  (forall candidate_edge, 0 <= candidate_edge < n - 1 ->
     Znth candidate_edge new_dist 0 =
       if Z.eq_dec candidate_edge edge
       then Znth candidate_edge old_dist 0 - 1
       else Znth candidate_edge old_dist 0) /\
  (forall station, 0 <= station <= edge ->
     Znth station new_arrivals 0 = Znth station old_arrivals 0) /\
  (forall station, edge < station < next_station ->
     Znth station new_arrivals 0 = Znth station old_arrivals 0 - 1 /\
     Znth station latest 0 <= Znth station new_arrivals 0) /\
  (forall station, next_station <= station < n ->
     Znth station new_arrivals 0 = Znth station old_arrivals 0).
Proof.
  unfold ArrivalRepairProgress. setoid_rewrite bus_Forall2_indexed.
  cbn. firstorder lia.
Qed.

Lemma ArrivalRepairOutcome_unfold n old_dist old_arrivals new_dist new_arrivals latest edge :
  ArrivalRepairOutcome n old_dist old_arrivals new_dist new_arrivals latest edge <->
  exists stop,
    edge + 1 <= stop <= n /\
    (forall candidate_edge, 0 <= candidate_edge < n - 1 ->
       Znth candidate_edge new_dist 0 =
         if Z.eq_dec candidate_edge edge
         then Znth candidate_edge old_dist 0 - 1
         else Znth candidate_edge old_dist 0) /\
    (forall station, 0 <= station <= edge ->
       Znth station new_arrivals 0 = Znth station old_arrivals 0) /\
    (forall station, edge < station < stop ->
       Znth station new_arrivals 0 = Znth station old_arrivals 0 - 1 /\
       Znth station latest 0 <= Znth station new_arrivals 0) /\
    ((stop = n /\
      forall station, edge < station < n ->
        Znth station new_arrivals 0 = Znth station old_arrivals 0 - 1) \/
     (stop < n /\
      Znth stop new_arrivals 0 = Znth stop old_arrivals 0 - 1 /\
      Znth stop new_arrivals 0 < Znth stop latest 0 /\
      forall station, stop < station < n ->
        Znth station new_arrivals 0 = Znth station old_arrivals 0)).
Proof.
  unfold ArrivalRepairOutcome. setoid_rewrite bus_Forall2_indexed.
  cbn. firstorder lia.
Qed.

Definition BoosterProgress
    (n m budget remaining : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) : Prop :=
  LatestDepartures n m times origins latest /\
  DestinationCounts n m destinations counts /\
  FeasibleBoostedDistances
    n (budget - remaining) initial_dist dist /\
  BusArrivalSchedule n dist latest arrivals /\
  exists current_total,
    PassengerTravelTotal
      m times destinations arrivals current_total /\
    SightseeingMinimumTotal
      n m (budget - remaining)
      initial_dist times origins destinations current_total.

Definition OptimizedBusState
    (n m budget : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) : Prop :=
  LatestDepartures n m times origins latest /\
  DestinationCounts n m destinations counts /\
  FeasibleBoostedDistances n budget initial_dist dist /\
  BusArrivalSchedule n dist latest arrivals /\
  exists optimum,
    PassengerTravelTotal m times destinations arrivals optimum /\
    SightseeingMinimumTotal
      n m budget initial_dist times origins destinations optimum.

Definition TravelSumPrefix
    (m : Z) (times destinations arrivals : list Z)
    (processed total : Z) : Prop :=
  total =
    sum (fun passenger => 0 <= passenger < processed /\ passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) arrivals 0 -
           Znth passenger times 0).

(* ------------------------------------------------------------------------- *)
(* Chain-schedule primal/dual certificate.  This is a mathematical proof
   interface, not a mirror of the C control flow. *)

Definition ChainWeightedArrivalTotal
    (n : Z) (counts arrivals : list Z) (weighted : Z) : Prop :=
  weighted =
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station arrivals 0).

Definition ChainDualCertificate
    (n budget : Z) (initial_dist latest counts : list Z)
    (alpha beta delta : list Z) (gamma lower : Z) : Prop :=
  Zlength alpha = n - 1 /\
  Zlength beta = n - 1 /\
  Zlength delta = n - 1 /\
  0 <= gamma /\
  (forall edge, 0 <= edge < n - 1 ->
     0 <= Znth edge alpha 0 /\
     0 <= Znth edge beta 0 /\
     0 <= Znth edge delta 0 /\
     Znth edge alpha 0 + Znth edge beta 0 <=
       gamma + Znth edge delta 0) /\
  (forall station, 1 <= station < n - 1 ->
     Znth (station - 1) alpha 0 + Znth (station - 1) beta 0 -
       Znth station alpha 0 <= Znth station counts 0) /\
  (Znth (n - 2) alpha 0 + Znth (n - 2) beta 0 <=
     Znth (n - 1) counts 0) /\
  lower =
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 *
             (Znth edge alpha 0 + Znth edge beta 0) +
           Znth edge latest 0 * Znth edge beta 0 -
           Znth edge initial_dist 0 * Znth edge delta 0) -
    budget * gamma.

Lemma station_departure_ge_inputs__chain_dual :
  forall arrivals latest station departure,
    StationDeparture arrivals latest station departure ->
    Znth station arrivals 0 <= departure /\
    Znth station latest 0 <= departure.
Proof.
  intros arrivals latest station departure Hdeparture.
  unfold StationDeparture,
    MaxMin.max_value_of_subset_with_default in Hdeparture.
  destruct Hdeparture as [[Hmaximum Hdefault] | [Hall Hdefault]].
  - destruct Hmaximum as [candidate [[Hmember Hgreatest] Hvalue]].
    change (candidate = Znth station latest 0) in Hmember.
    subst candidate.
    cbn in Hvalue.
    subst departure.
    split; [exact Hdefault | lia].
  - cbn in Hdefault.
    subst departure.
    split; [lia |].
    specialize (Hall (Znth station latest 0) eq_refl).
    cbn in Hall.
    exact Hall.
Qed.

Lemma bus_schedule_edge_lower_bounds__chain_dual :
  forall n dist latest arrivals edge,
    BusArrivalSchedule n dist latest arrivals ->
    0 <= edge < n - 1 ->
    Znth edge arrivals 0 + Znth edge dist 0 <=
      Znth (edge + 1) arrivals 0 /\
    Znth edge latest 0 + Znth edge dist 0 <=
      Znth (edge + 1) arrivals 0.
Proof.
  intros n dist latest arrivals edge Hschedule Hedge.
  destruct Hschedule as [_ [_ Hstep]].
  specialize (Hstep edge Hedge).
  destruct Hstep as [departure [Hdeparture Harrival]].
  pose proof (station_departure_ge_inputs__chain_dual
    arrivals latest edge departure Hdeparture) as [Ha Hl].
  lia.
Qed.

Lemma chain_dual_weak_bound :
  forall n budget initial_dist final_dist latest counts arrivals
         alpha beta delta gamma lower weighted,
    2 <= n ->
    FeasibleBoostedDistances n budget initial_dist final_dist ->
    BusArrivalSchedule n final_dist latest arrivals ->
    (forall station, 0 <= station < n ->
       0 <= Znth station arrivals 0) ->
    ChainDualCertificate
      n budget initial_dist latest counts
      alpha beta delta gamma lower ->
    ChainWeightedArrivalTotal n counts arrivals weighted ->
    lower <= weighted.
Proof.
  intros n budget initial_dist final_dist latest counts arrivals
    alpha beta delta gamma lower weighted Hn Hfeasible Hschedule
    Harrivals Hdual Hweighted.
  rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  destruct Hfeasible as [Hfinal_len [Hfinal_bounds Hbudget]].
  unfold ChainDualCertificate in Hdual.
  destruct Hdual as
    [Halpha_len [Hbeta_len [Hdelta_len [Hgamma
      [Hedge [Hstation [Hlast Hlower]]]]]]].
  unfold ChainWeightedArrivalTotal in Hweighted.
  subst weighted lower.
  assert (Hweighted_balance :
    sum (fun station => 1 <= station < n)
        (fun station =>
           (Znth (station - 1) alpha 0 +
            Znth (station - 1) beta 0 -
            (if Z_lt_dec station (n - 1)
             then Znth station alpha 0 else 0)) *
           Znth station arrivals 0) <=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station arrivals 0)).
  {
    apply sum_Z_range_le.
    intros station Hstation_range.
    pose proof (Harrivals station ltac:(lia)) as Harrival_nonnegative.
    destruct (Z_lt_dec station (n - 1)) as [Hbefore_last | Hlast_station].
    - specialize (Hstation station ltac:(lia)).
      nia.
    - assert (station = n - 1) by lia.
      subst station.
      destruct (Z_lt_dec (n - 1) (n - 1)); [lia |].
      replace (n - 1 - 1) with (n - 2) by lia.
      replace
        (Znth (n - 2) alpha 0 + Znth (n - 2) beta 0 - 0)
        with (Znth (n - 2) alpha 0 + Znth (n - 2) beta 0) by lia.
      apply Z.mul_le_mono_nonneg_r; assumption.
  }
  assert (Hbalance_rewrite :
    sum (fun station => 1 <= station < n)
        (fun station =>
           (Znth (station - 1) alpha 0 +
            Znth (station - 1) beta 0 -
            (if Z_lt_dec station (n - 1)
             then Znth station alpha 0 else 0)) *
           Znth station arrivals 0) =
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           (Znth edge alpha 0 + Znth edge beta 0) *
           Znth (edge + 1) arrivals 0) -
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge alpha 0 * Znth edge arrivals 0)).
  {
    assert (Hshift_q :
      sum (fun station => 1 <= station < n)
          (fun station =>
             (Znth (station - 1) alpha 0 +
              Znth (station - 1) beta 0) *
             Znth station arrivals 0) =
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             (Znth edge alpha 0 + Znth edge beta 0) *
             Znth (edge + 1) arrivals 0)).
    {
      pose proof (sum_Z_range_shift 0 (n - 1) 1
        (fun station =>
           (Znth (station - 1) alpha 0 +
            Znth (station - 1) beta 0) *
           Znth station arrivals 0)) as Hshift.
      replace (n - 1 + 1) with n in Hshift by lia.
      rewrite (sum_Z_range_ext 0 (n - 1)
        (fun edge =>
           (Znth (edge + 1 - 1) alpha 0 +
            Znth (edge + 1 - 1) beta 0) *
           Znth (edge + 1) arrivals 0)
        (fun edge =>
           (Znth edge alpha 0 + Znth edge beta 0) *
           Znth (edge + 1) arrivals 0)) in Hshift.
      2: {
        intros edge Hedge_range.
        replace (edge + 1 - 1) with edge by lia.
        reflexivity.
      }
      exact Hshift.
    }
    assert (Hguard_alpha :
      sum (fun station => 1 <= station < n)
          (fun station =>
             (if Z_lt_dec station (n - 1)
              then Znth station alpha 0 else 0) *
             Znth station arrivals 0) =
      sum (fun station => 1 <= station < n - 1)
          (fun station =>
             Znth station alpha 0 * Znth station arrivals 0)).
    {
      rewrite (sum_Z_range_split 1 (n - 1) n
        (fun station =>
           (if Z_lt_dec station (n - 1)
            then Znth station alpha 0 else 0) *
           Znth station arrivals 0)) by lia.
      rewrite (sum_Z_range_cons (n - 1) n) by lia.
      rewrite (sum_Z_range_empty (n - 1 + 1) n) by lia.
      destruct (Z_lt_dec (n - 1) (n - 1)); [lia |].
      rewrite (sum_Z_range_ext 1 (n - 1)
        (fun station =>
           (if Z_lt_dec station (n - 1)
            then Znth station alpha 0 else 0) *
           Znth station arrivals 0)
        (fun station =>
           Znth station alpha 0 * Znth station arrivals 0)).
      2: {
        intros station Hstation_range.
        destruct (Z_lt_dec station (n - 1)); [reflexivity | lia].
      }
      lia.
    }
    assert (Halpha_zero :
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge => Znth edge alpha 0 * Znth edge arrivals 0) =
      sum (fun station => 1 <= station < n - 1)
          (fun station => Znth station alpha 0 * Znth station arrivals 0)).
    {
      rewrite (sum_Z_range_split 0 1 (n - 1)
        (fun edge => Znth edge alpha 0 * Znth edge arrivals 0)) by lia.
      rewrite sum_Z_range_cons by lia.
      rewrite sum_Z_range_empty by lia.
      destruct Hschedule as [_ [Harrival_zero _]].
      rewrite Harrival_zero.
      lia.
    }
    rewrite (sum_Z_range_ext 1 n
      (fun station =>
         (Znth (station - 1) alpha 0 +
          Znth (station - 1) beta 0 -
          (if Z_lt_dec station (n - 1)
           then Znth station alpha 0 else 0)) *
         Znth station arrivals 0)
      (fun station =>
         (Znth (station - 1) alpha 0 +
          Znth (station - 1) beta 0) *
           Znth station arrivals 0 -
         (if Z_lt_dec station (n - 1)
          then Znth station alpha 0 else 0) *
           Znth station arrivals 0)).
    2: { intros station Hstation_range; ring. }
    rewrite sum_Z_range_sub, Hshift_q, Hguard_alpha.
    rewrite <- Halpha_zero.
    reflexivity.
  }
  assert (Hschedule_bound :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge beta 0 * Znth edge latest 0 +
           (Znth edge alpha 0 + Znth edge beta 0) *
             Znth edge final_dist 0) <=
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           (Znth edge alpha 0 + Znth edge beta 0) *
             Znth (edge + 1) arrivals 0 -
           Znth edge alpha 0 * Znth edge arrivals 0)).
  {
    apply sum_Z_range_le.
    intros edge Hedge_range.
    specialize (Hedge edge Hedge_range).
    destruct Hedge as [Halpha [Hbeta [Hdelta Hshadow]]].
    pose proof (bus_schedule_edge_lower_bounds__chain_dual
      n final_dist latest arrivals edge Hschedule Hedge_range)
      as [Hmove Hwait].
    nia.
  }
  rewrite sum_Z_range_sub in Hschedule_bound.
  rewrite <- Hbalance_rewrite in Hschedule_bound.
  assert (Hreduction_bound :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           (Znth edge alpha 0 + Znth edge beta 0) *
             (Znth edge initial_dist 0 - Znth edge final_dist 0)) <=
    budget * gamma +
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 * Znth edge delta 0)).
  {
    eapply Z.le_trans.
    - apply sum_Z_range_le.
      intros edge Hedge_range.
      specialize (Hedge edge Hedge_range).
      specialize (Hfinal_bounds edge Hedge_range).
      destruct Hedge as [Halpha [Hbeta [Hdelta Hshadow]]].
      apply Z.mul_le_mono_nonneg_r; [lia | exact Hshadow].
    - rewrite (sum_Z_range_ext 0 (n - 1)
        (fun edge =>
           (gamma + Znth edge delta 0) *
             (Znth edge initial_dist 0 - Znth edge final_dist 0))
        (fun edge =>
           gamma * (Znth edge initial_dist 0 - Znth edge final_dist 0) +
           Znth edge delta 0 *
             (Znth edge initial_dist 0 - Znth edge final_dist 0))).
      2: { intros edge Hedge_range; ring. }
      rewrite sum_Z_range_add.
      rewrite sum_Z_range_factor_l.
      assert (Hdelta_reduction :
        sum (fun edge => 0 <= edge < n - 1)
            (fun edge =>
               Znth edge delta 0 *
                 (Znth edge initial_dist 0 - Znth edge final_dist 0)) <=
        sum (fun edge => 0 <= edge < n - 1)
            (fun edge =>
               Znth edge initial_dist 0 * Znth edge delta 0)).
      {
        apply sum_Z_range_le.
        intros edge Hedge_range.
        specialize (Hedge edge Hedge_range).
        specialize (Hfinal_bounds edge Hedge_range).
        destruct Hedge as [Halpha [Hbeta [Hdelta Hshadow]]].
        replace
          (Znth edge initial_dist 0 * Znth edge delta 0)
          with (Znth edge delta 0 * Znth edge initial_dist 0) by ring.
        apply Z.mul_le_mono_nonneg_l; [exact Hdelta | lia].
      }
      nia.
  }
  rewrite sum_Z_range_add in Hschedule_bound.
  assert (Hobjective_algebra :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 *
             (Znth edge alpha 0 + Znth edge beta 0) +
           Znth edge latest 0 * Znth edge beta 0 -
           Znth edge initial_dist 0 * Znth edge delta 0) -
      budget * gamma <=
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge beta 0 * Znth edge latest 0 +
           (Znth edge alpha 0 + Znth edge beta 0) *
             Znth edge final_dist 0)).
  {
    assert (Hdecompose :
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 *
               (Znth edge alpha 0 + Znth edge beta 0) +
             Znth edge latest 0 * Znth edge beta 0 -
             Znth edge initial_dist 0 * Znth edge delta 0) -
        budget * gamma =
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge beta 0 * Znth edge latest 0 +
             (Znth edge alpha 0 + Znth edge beta 0) *
               Znth edge final_dist 0) +
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             (Znth edge alpha 0 + Znth edge beta 0) *
               (Znth edge initial_dist 0 - Znth edge final_dist 0)) -
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 * Znth edge delta 0) -
      budget * gamma).
    {
      rewrite (sum_Z_range_ext 0 (n - 1)
        (fun edge =>
           Znth edge initial_dist 0 *
             (Znth edge alpha 0 + Znth edge beta 0) +
           Znth edge latest 0 * Znth edge beta 0 -
           Znth edge initial_dist 0 * Znth edge delta 0)
        (fun edge =>
           (Znth edge beta 0 * Znth edge latest 0 +
            (Znth edge alpha 0 + Znth edge beta 0) *
              Znth edge final_dist 0) +
           (Znth edge alpha 0 + Znth edge beta 0) *
             (Znth edge initial_dist 0 - Znth edge final_dist 0) -
           Znth edge initial_dist 0 * Znth edge delta 0)).
      2: { intros edge Hedge_range; ring. }
      rewrite sum_Z_range_sub, !sum_Z_range_add.
      ring.
    }
    rewrite Hdecompose.
    nia.
  }
  eapply Z.le_trans; [exact Hobjective_algebra |].
  rewrite sum_Z_range_add.
  eapply Z.le_trans; [exact Hschedule_bound |].
  exact Hweighted_balance.
Qed.

Lemma fold_Zsum_add__chain_dual :
  forall (xs : list Z) (f g : Z -> Z),
    fold_right (fun x acc => (f x + g x) + acc) 0 xs =
    fold_right (fun x acc => f x + acc) 0 xs +
    fold_right (fun x acc => g x + acc) 0 xs.
Proof.
  induction xs as [|x xs IH]; intros f g; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma fold_Zsum_nested_swap__chain_dual :
  forall (xs ys : list Z) (f : Z -> Z -> Z),
    fold_right
      (fun x acc => fold_right (fun y acc => f x y + acc) 0 ys + acc)
      0 xs =
    fold_right
      (fun y acc => fold_right (fun x acc => f x y + acc) 0 xs + acc)
      0 ys.
Proof.
  induction xs as [|x xs IH]; intros ys f; simpl.
  - induction ys as [|y ys IHys]; simpl; auto.
  - rewrite IH.
    rewrite <- fold_Zsum_add__chain_dual.
    reflexivity.
Qed.

Lemma sum_Z_range_nested_swap__chain_dual :
  forall x_low x_high y_low y_high f,
    sum (fun x => x_low <= x < x_high)
        (fun x => sum (fun y => y_low <= y < y_high)
                      (fun y => f x y)) =
    sum (fun y => y_low <= y < y_high)
        (fun y => sum (fun x => x_low <= x < x_high)
                      (fun x => f x y)).
Proof.
  intros x_low x_high y_low y_high f.
  rewrite !sum_range_unfold.
  apply fold_Zsum_nested_swap__chain_dual.
Qed.

Lemma sum_Z_range_filter_indicator__chain_dual :
  forall low high (P : Z -> Prop) f,
    sum (fun x => low <= x < high /\ P x) f =
    sum (fun x => low <= x < high)
        (fun x => if prop_dec (P x) then f x else 0).
Proof.
  intros low high P f.
  unfold sum.
  simpl.
  induction (Zrange low high) as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (prop_dec (P x)); simpl; rewrite IH; ring.
Qed.

Lemma destination_indicator_weight__chain_dual :
  forall n station_value destination,
    1 <= destination - 1 < n ->
    sum (fun station => 1 <= station < n)
        (fun station =>
           (if prop_dec (destination = station + 1) then 1 else 0) *
           Znth station station_value 0) =
    Znth (destination - 1) station_value 0.
Proof.
  intros n station_value destination Hdestination.
  rewrite (sum_Z_range_split 1 (destination - 1) n) by lia.
  assert (Hleft :
    sum (fun station => 1 <= station < destination - 1)
        (fun station =>
           (if prop_dec (destination = station + 1) then 1 else 0) *
           Znth station station_value 0) = 0).
  {
    apply sum_Z_range_eq_zero.
    intros station Hstation.
    destruct (prop_dec (destination = station + 1)); [lia | reflexivity].
  }
  rewrite Hleft.
  rewrite (sum_Z_range_cons (destination - 1) n) by lia.
  assert (Hright :
    sum (fun station => destination - 1 + 1 <= station < n)
        (fun station =>
           (if prop_dec (destination = station + 1) then 1 else 0) *
           Znth station station_value 0) = 0).
  {
    apply sum_Z_range_eq_zero.
    intros station Hstation.
    destruct (prop_dec (destination = station + 1)); [lia | reflexivity].
  }
  rewrite Hright.
  destruct (prop_dec (destination = destination - 1 + 1)); [ring | lia].
Qed.

Lemma destination_counts_weighted_arrivals__chain_dual :
  forall n m initial_dist times origins destinations counts arrivals,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    DestinationCounts n m destinations counts ->
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station arrivals 0) =
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) arrivals 0).
Proof.
  intros n m initial_dist times origins destinations counts arrivals
    Hinputs Hcounts.
  unfold DestinationCounts in Hcounts.
  destruct Hcounts as [Hcounts_len Hcount].
  rewrite (sum_Z_range_ext 1 n
    (fun station => Znth station counts 0 * Znth station arrivals 0)
    (fun station =>
       sum (fun passenger => 0 <= passenger < m)
           (fun passenger =>
              (if prop_dec
                 (Znth passenger destinations 0 = station + 1)
               then 1 else 0) * Znth station arrivals 0))).
  2: {
    intros station Hstation.
    rewrite Hcount by lia.
    rewrite sum_Z_range_filter_indicator__chain_dual.
    rewrite sum_Z_range_factor_r.
    reflexivity.
  }
  rewrite sum_Z_range_nested_swap__chain_dual.
  apply sum_Z_range_ext.
  intros passenger Hpassenger.
  pose proof Hinputs as Hbounds.
  unfold SightseeingInputsBounded in Hbounds.
  destruct Hbounds as [_ [_ [_ [_ [_ [_ [_ Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds passenger Hpassenger).
  destruct Hpassenger_bounds as
    [Htime [[Horigin Horigin_destination] Hdestination]].
  apply destination_indicator_weight__chain_dual.
  lia.
Qed.

Lemma latest_at_station_unique__chain_dual :
  forall m times origins station x y,
    LatestAtStation m times origins station x ->
    LatestAtStation m times origins station y ->
    x = y.
Proof.
  intros m times origins station x y Hx Hy.
  unfold LatestAtStation in Hx, Hy.
  eapply (@MaxMin.max_default_unique
    Z Z.le Zle_TotalOrder Z
    (fun passenger => Znth passenger times 0)
    (fun passenger =>
       0 <= passenger < m /\
       Znth passenger origins 0 = station + 1)
    0); eauto.
Qed.

Lemma latest_departures_pointwise_unique__chain_dual :
  forall n m times origins latest1 latest2 station,
    LatestDepartures n m times origins latest1 ->
    LatestDepartures n m times origins latest2 ->
    0 <= station < n ->
    Znth station latest1 0 = Znth station latest2 0.
Proof.
  intros n m times origins latest1 latest2 station
    Hlatest1 Hlatest2 Hstation.
  destruct Hlatest1 as [_ Hlatest1].
  destruct Hlatest2 as [_ Hlatest2].
  eapply latest_at_station_unique__chain_dual;
    [apply Hlatest1 | apply Hlatest2]; exact Hstation.
Qed.

Lemma bus_schedule_latest_ext__chain_dual :
  forall n dist latest1 latest2 arrivals,
    (forall station, 0 <= station < n ->
       Znth station latest1 0 = Znth station latest2 0) ->
    BusArrivalSchedule n dist latest1 arrivals ->
    BusArrivalSchedule n dist latest2 arrivals.
Proof.
  intros n dist latest1 latest2 arrivals Hlatest Hschedule.
  destruct Hschedule as [Hlength [Hzero Hstep]].
  split; [exact Hlength |].
  split; [exact Hzero |].
  intros station Hstation.
  specialize (Hstep station Hstation).
  destruct Hstep as [departure [Hdeparture Harrival]].
  exists departure.
  split; [| exact Harrival].
  pose proof (Hlatest station ltac:(lia)) as Heq.
  unfold StationDeparture in Hdeparture.
  unfold StationDeparture.
  replace (Znth station latest2 0) with (Znth station latest1 0)
    by exact Heq.
  exact Hdeparture.
Qed.

Lemma bus_schedule_arrivals_nonnegative__chain_dual :
  forall n dist latest arrivals,
    2 <= n ->
    BusArrivalSchedule n dist latest arrivals ->
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge dist 0) ->
    forall station, 0 <= station < n ->
      0 <= Znth station arrivals 0.
Proof.
  intros n dist latest arrivals Hn Hschedule Hdist.
  intros station Hstation.
  destruct Hschedule as [Hlength [Hzero Hstep]].
  assert (Hnat : forall k : nat,
    Z.of_nat k < n -> 0 <= Znth (Z.of_nat k) arrivals 0).
  {
    induction k as [|k IH].
    - cbn. rewrite Hzero. lia.
    - intros Hk.
      rewrite Nat2Z.inj_succ in Hk.
      specialize (IH ltac:(lia)).
      specialize (Hstep (Z.of_nat k) ltac:(lia)).
      destruct Hstep as [departure [Hdeparture Harrival]].
      pose proof (station_departure_ge_inputs__chain_dual
        arrivals latest (Z.of_nat k) departure Hdeparture) as [Ha Hl].
      specialize (Hdist (Z.of_nat k) ltac:(lia)).
      assert (Hnext :
        0 <= Znth (Z.of_nat k + 1) arrivals 0).
      { rewrite Harrival. lia. }
      replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
      exact Hnext.
  }
  replace station with (Z.of_nat (Z.to_nat station)) by lia.
  apply Hnat.
  lia.
Qed.

Definition SightseeingDualLowerBound
    (n m budget : Z)
    (initial_dist times origins destinations latest counts : list Z)
    (alpha beta delta : list Z) (gamma lower_total : Z) : Prop :=
  ChainDualCertificate
    n budget initial_dist latest counts alpha beta delta gamma
    (lower_total +
     sum (fun passenger => 0 <= passenger < m)
         (fun passenger => Znth passenger times 0)).

Lemma sightseeing_dual_lower_bound_sound :
  forall n m budget initial_dist times origins destinations latest counts
         alpha beta delta gamma lower_total candidate_total,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    DestinationCounts n m destinations counts ->
    SightseeingDualLowerBound
      n m budget initial_dist times origins destinations latest counts
      alpha beta delta gamma lower_total ->
    SightseeingCandidateTotal
      n m budget initial_dist times origins destinations candidate_total ->
    lower_total <= candidate_total.
Proof.
  intros n m budget initial_dist times origins destinations latest counts
    alpha beta delta gamma lower_total candidate_total
    Hinputs Hlatest Hcounts Hdual Hcandidate.
  destruct Hcandidate as
    [candidate_dist [candidate_latest [candidate_arrivals
      [Hcandidate_latest [Hcandidate_feasible
        [Hcandidate_schedule Hcandidate_total]]]]]].
  assert (Hlatest_pointwise : forall station, 0 <= station < n ->
      Znth station candidate_latest 0 = Znth station latest 0).
  {
    intros station Hstation.
    symmetry.
    eapply latest_departures_pointwise_unique__chain_dual; eauto.
  }
  assert (Hschedule_current_latest :
      BusArrivalSchedule n candidate_dist latest candidate_arrivals).
  {
    eapply bus_schedule_latest_ext__chain_dual.
    - intros station Hstation.
      apply Hlatest_pointwise; exact Hstation.
    - exact Hcandidate_schedule.
  }
  assert (Hcandidate_dist_nonnegative :
      forall edge, 0 <= edge < n - 1 ->
        0 <= Znth edge candidate_dist 0).
  {
    pose proof Hcandidate_feasible as Hfeasible_fields.
    rewrite FeasibleBoostedDistances_unfold in Hfeasible_fields.
    destruct Hfeasible_fields as [_ [Hbounds _]].
    intros edge Hedge.
    specialize (Hbounds edge Hedge).
    lia.
  }
  assert (Hcandidate_arrivals_nonnegative :
      forall station, 0 <= station < n ->
        0 <= Znth station candidate_arrivals 0).
  {
    eapply bus_schedule_arrivals_nonnegative__chain_dual;
      [| exact Hschedule_current_latest | exact Hcandidate_dist_nonnegative].
    unfold SightseeingInputsBounded in Hinputs; lia.
  }
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts candidate_arrivals
    Hinputs Hcounts) as Hweighted_identity.
  set (weighted :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station candidate_arrivals 0)).
  assert (Hweighted :
      ChainWeightedArrivalTotal n counts candidate_arrivals weighted).
  { unfold ChainWeightedArrivalTotal, weighted. reflexivity. }
  unfold SightseeingDualLowerBound in Hdual.
  pose proof (chain_dual_weak_bound
    n budget initial_dist candidate_dist latest counts candidate_arrivals
    alpha beta delta gamma
    (lower_total +
      sum (fun passenger => 0 <= passenger < m)
          (fun passenger => Znth passenger times 0))
    weighted
    ltac:(unfold SightseeingInputsBounded in Hinputs; lia)
    Hcandidate_feasible Hschedule_current_latest
    Hcandidate_arrivals_nonnegative Hdual Hweighted) as Hbound.
  unfold PassengerTravelTotal in Hcandidate_total.
  rewrite sum_Z_range_sub in Hcandidate_total.
  subst candidate_total weighted.
  rewrite Hweighted_identity in Hbound.
  nia.
Qed.

Lemma sightseeing_dual_rebudget_one__chain_dual :
  forall n m budget initial_dist times origins destinations latest counts
         alpha beta delta gamma lower_total,
    SightseeingDualLowerBound
      n m budget initial_dist times origins destinations latest counts
      alpha beta delta gamma lower_total ->
    SightseeingDualLowerBound
      n m (budget + 1) initial_dist times origins destinations latest counts
      alpha beta delta gamma (lower_total - gamma).
Proof.
  intros n m budget initial_dist times origins destinations latest counts
    alpha beta delta gamma lower_total Hdual.
  unfold SightseeingDualLowerBound in Hdual |-.
  unfold ChainDualCertificate in Hdual |-.
  destruct Hdual as
    [Halpha [Hbeta [Hdelta [Hgamma
      [Hedge [Hstation [Hlast Hvalue]]]]]]].
  split; [exact Halpha |].
  split; [exact Hbeta |].
  split; [exact Hdelta |].
  split; [exact Hgamma |].
  split; [exact Hedge |].
  split; [exact Hstation |].
  split; [exact Hlast |].
  replace
    (lower_total - gamma +
      sum (fun passenger => 0 <= passenger < m)
          (fun passenger => Znth passenger times 0))
    with
    ((lower_total +
      sum (fun passenger => 0 <= passenger < m)
          (fun passenger => Znth passenger times 0)) - gamma) by ring.
  replace
    (sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 *
             (Znth edge alpha 0 + Znth edge beta 0) +
           Znth edge latest 0 * Znth edge beta 0 -
           Znth edge initial_dist 0 * Znth edge delta 0) -
      (budget + 1) * gamma)
    with
    ((sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 *
             (Znth edge alpha 0 + Znth edge beta 0) +
           Znth edge latest 0 * Znth edge beta 0 -
           Znth edge initial_dist 0 * Znth edge delta 0) -
      budget * gamma) - gamma) by ring.
  exact (f_equal (fun z : Z => z - gamma) Hvalue).
Qed.

Lemma sightseeing_dual_attained_is_minimum__chain_dual :
  forall n m budget initial_dist times origins destinations
         final_dist latest counts arrivals answer
         alpha beta delta gamma,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    DestinationCounts n m destinations counts ->
    FeasibleBoostedDistances n budget initial_dist final_dist ->
    BusArrivalSchedule n final_dist latest arrivals ->
    PassengerTravelTotal m times destinations arrivals answer ->
    SightseeingDualLowerBound
      n m budget initial_dist times origins destinations latest counts
      alpha beta delta gamma answer ->
    SightseeingMinimumTotal
      n m budget initial_dist times origins destinations answer.
Proof.
  intros n m budget initial_dist times origins destinations
    final_dist latest counts arrivals answer alpha beta delta gamma
    Hinputs Hlatest Hcounts Hfeasible Hschedule Htotal Hdual.
  unfold SightseeingMinimumTotal,
    MaxMin.min_value_of_subset, MaxMin.min_object_of_subset.
  exists answer.
  split; [| reflexivity].
  split.
  - unfold SightseeingCandidateTotal.
    exists final_dist, latest, arrivals.
    exact (conj Hlatest (conj Hfeasible (conj Hschedule Htotal))).
  - intros candidate Hcandidate.
    cbn.
    eapply sightseeing_dual_lower_bound_sound
      with (candidate_total := candidate); eauto.
Qed.

Definition GreedyDualReady
    (n m budget remaining : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) : Prop :=
  forall current_total best position,
    PassengerTravelTotal m times destinations arrivals current_total ->
    0 < best ->
    BestBoostChoice n dist counts latest arrivals best position ->
    exists alpha beta delta,
      SightseeingDualLowerBound
        n m (budget - remaining)
        initial_dist times origins destinations latest counts
        alpha beta delta best current_total.

Definition SelectedDualCertificate
    (n m budget remaining : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) (best : Z) : Prop :=
  exists current_total alpha beta delta,
    PassengerTravelTotal m times destinations arrivals current_total /\
    SightseeingDualLowerBound
      n m (budget - remaining)
      initial_dist times origins destinations latest counts
      alpha beta delta best current_total.

Lemma greedy_dual_ready_select__chain_dual :
  forall n m budget remaining initial_dist times origins destinations
         dist latest counts arrivals best position,
    GreedyDualReady n m budget remaining
      initial_dist times origins destinations
      dist latest counts arrivals ->
    (exists current_total,
       PassengerTravelTotal m times destinations arrivals current_total) ->
    0 < best ->
    BestBoostChoice n dist counts latest arrivals best position ->
    SelectedDualCertificate n m budget remaining
      initial_dist times origins destinations
      dist latest counts arrivals best.
Proof.
  intros n m budget remaining initial_dist times origins destinations
    dist latest counts arrivals best position Hready Htotal Hbest Hchoice.
  destruct Htotal as [current_total Htotal].
  specialize (Hready current_total best position Htotal Hbest Hchoice).
  destruct Hready as [alpha [beta [delta Hdual]]].
  exists current_total, alpha, beta, delta.
  tauto.
Qed.

(* ------------------------------------------------------------------------- *)
(* Proof-carrying ghost execution history.  This trace is internal: public
   functional correctness remains the raw MinMax optimum. *)

Inductive GreedyShadowTrace
    (n m budget : Z)
    (initial_dist times origins destinations latest counts : list Z)
    : Z -> list Z -> list Z -> Prop :=
| GreedyShadowTrace_base :
    forall initial_arrivals initial_total,
      BusArrivalSchedule n initial_dist latest initial_arrivals ->
      PassengerTravelTotal
        m times destinations initial_arrivals initial_total ->
      GreedyShadowTrace
        n m budget initial_dist times origins destinations latest counts
        0 initial_dist initial_arrivals
| GreedyShadowTrace_step :
    forall spent old_dist old_arrivals new_dist new_arrivals
           old_total best position alpha beta delta,
      GreedyShadowTrace
        n m budget initial_dist times origins destinations latest counts
        spent old_dist old_arrivals ->
      0 < best ->
      BestBoostChoice
        n old_dist counts latest old_arrivals best position ->
      PassengerTravelTotal
        m times destinations old_arrivals old_total ->
      SightseeingDualLowerBound
        n m spent initial_dist times origins destinations latest counts
        alpha beta delta best old_total ->
      ArrivalRepairOutcome
        n old_dist old_arrivals new_dist new_arrivals latest position ->
      GreedyShadowTrace
        n m budget initial_dist times origins destinations latest counts
        (spent + 1) new_dist new_arrivals.

Definition GreedyShadowSelection
    (n m budget spent : Z)
    (initial_dist times origins destinations latest counts : list Z)
    (dist arrivals : list Z) (best position : Z) : Prop :=
  exists alpha beta delta current_total,
    GreedyShadowTrace
      n m budget initial_dist times origins destinations latest counts
      spent dist arrivals /\
    0 < best /\
    BestBoostChoice n dist counts latest arrivals best position /\
    PassengerTravelTotal m times destinations arrivals current_total /\
    SightseeingDualLowerBound
      n m spent initial_dist times origins destinations latest counts
      alpha beta delta best current_total.

Lemma greedy_shadow_trace_base__chain_dual :
  forall n m budget initial_dist times origins destinations latest counts
         arrivals total,
    BusArrivalSchedule n initial_dist latest arrivals ->
    PassengerTravelTotal m times destinations arrivals total ->
    GreedyShadowTrace
      n m budget initial_dist times origins destinations latest counts
      0 initial_dist arrivals.
Proof.
  intros.
  econstructor; eauto.
Qed.

Lemma greedy_shadow_trace_append__chain_dual :
  forall n m budget initial_dist times origins destinations latest counts
         spent old_dist old_arrivals new_dist new_arrivals
         old_total best position alpha beta delta,
    GreedyShadowTrace
      n m budget initial_dist times origins destinations latest counts
      spent old_dist old_arrivals ->
    0 < best ->
    BestBoostChoice
      n old_dist counts latest old_arrivals best position ->
    PassengerTravelTotal m times destinations old_arrivals old_total ->
    SightseeingDualLowerBound
      n m spent initial_dist times origins destinations latest counts
      alpha beta delta best old_total ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    GreedyShadowTrace
      n m budget initial_dist times origins destinations latest counts
      (spent + 1) new_dist new_arrivals.
Proof.
  intros.
  econstructor; eauto.
Qed.

Lemma greedy_shadow_selection_selected_certificate__chain_dual :
  forall n m budget remaining spent
         initial_dist times origins destinations latest counts
         dist arrivals best position,
    spent = budget - remaining ->
    GreedyShadowSelection
      n m budget spent initial_dist times origins destinations latest counts
      dist arrivals best position ->
    SelectedDualCertificate
      n m budget remaining initial_dist times origins destinations
      dist latest counts arrivals best.
Proof.
  intros n m budget remaining spent initial_dist times origins destinations
    latest counts dist arrivals best position Hspent Hselection.
  destruct Hselection as
    [alpha [beta [delta [current_total
      [Htrace [Hbest [Hchoice [Htotal Hdual]]]]]]]].
  subst spent.
  exists current_total, alpha, beta, delta.
  split; assumption.
Qed.

Lemma greedy_shadow_trace_step_minimum__chain_dual :
  forall n m budget initial_dist times origins destinations latest counts
         spent old_dist old_arrivals new_dist new_arrivals
         old_total new_total best position alpha beta delta,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    DestinationCounts n m destinations counts ->
    GreedyShadowTrace
      n m budget initial_dist times origins destinations latest counts
      spent old_dist old_arrivals ->
    0 < best ->
    BestBoostChoice
      n old_dist counts latest old_arrivals best position ->
    PassengerTravelTotal m times destinations old_arrivals old_total ->
    SightseeingDualLowerBound
      n m spent initial_dist times origins destinations latest counts
      alpha beta delta best old_total ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    FeasibleBoostedDistances
      n (spent + 1) initial_dist new_dist ->
    BusArrivalSchedule n new_dist latest new_arrivals ->
    PassengerTravelTotal m times destinations new_arrivals new_total ->
    new_total = old_total - best ->
    SightseeingMinimumTotal
      n m (spent + 1) initial_dist times origins destinations new_total.
Proof.
  intros n m budget initial_dist times origins destinations latest counts
    spent old_dist old_arrivals new_dist new_arrivals old_total new_total
    best position alpha beta delta Hinputs Hlatest Hcounts Htrace Hbest
    Hchoice Hold_total Hdual Hrepair Hfeasible Hschedule Hnew_total Hdecr.
  pose proof (sightseeing_dual_rebudget_one__chain_dual
    n m spent initial_dist times origins destinations latest counts
    alpha beta delta best old_total Hdual) as Hdual_next.
  subst new_total.
  eapply sightseeing_dual_attained_is_minimum__chain_dual; eauto.
Qed.

Definition TracedBoosterProgress
    (n m budget remaining : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) : Prop :=
  BoosterProgress
    n m budget remaining initial_dist times origins destinations
    dist latest counts arrivals /\
  GreedyShadowTrace
    n m budget initial_dist times origins destinations latest counts
    (budget - remaining) dist arrivals.

(* ------------------------------------------------------------------------- *)
(* Direct combinatorial adjacent-budget exchange certificate. *)

Definition UndoOneDistance
    (n : Z) (candidate restored : list Z) (edge : Z) : Prop :=
  Zlength candidate = n - 1 /\
  Zlength restored = n - 1 /\
  0 <= edge < n - 1 /\
  forall e, 0 <= e < n - 1 ->
    Znth e restored 0 =
      if Z.eq_dec e edge
      then Znth e candidate 0 + 1
      else Znth e candidate 0.

Definition AdjacentCandidateUndoEvidence
    (n m old_budget : Z)
    (initial_dist times origins destinations : list Z)
    (candidate_total best : Z) : Prop :=
  exists candidate_dist candidate_latest candidate_arrivals,
    LatestDepartures n m times origins candidate_latest /\
    FeasibleBoostedDistances
      n (old_budget + 1) initial_dist candidate_dist /\
    BusArrivalSchedule n candidate_dist candidate_latest candidate_arrivals /\
    PassengerTravelTotal
      m times destinations candidate_arrivals candidate_total /\
    (FeasibleBoostedDistances
       n old_budget initial_dist candidate_dist \/
     exists edge restored_dist restored_latest restored_arrivals
            restored_total loss,
       UndoOneDistance n candidate_dist restored_dist edge /\
       LatestDepartures n m times origins restored_latest /\
       FeasibleBoostedDistances
         n old_budget initial_dist restored_dist /\
       BusArrivalSchedule
         n restored_dist restored_latest restored_arrivals /\
       PassengerTravelTotal
         m times destinations restored_arrivals restored_total /\
       restored_total <= candidate_total + loss /\
       loss <= best).

(* A clean adjacent-budget lower-bound certificate used by annotations.  The
   public candidate and MinMax minimum definitions remain unchanged. *)
Definition SelectedExchangeCertificate
    (n m budget remaining : Z)
    (initial_dist times origins destinations : list Z)
    (dist latest counts arrivals : list Z) (best : Z) : Prop :=
  0 <= best /\
  exists current_total,
    PassengerTravelTotal m times destinations arrivals current_total /\
    forall candidate_total,
      SightseeingCandidateTotal
        n m (budget - remaining + 1)
        initial_dist times origins destinations candidate_total ->
      current_total - best <= candidate_total.

Lemma adjacent_undo_evidence_lower_bound__exchange :
  forall n m old_budget initial_dist times origins destinations
         old_total candidate_total best,
    SightseeingMinimumTotal
      n m old_budget initial_dist times origins destinations old_total ->
    0 <= best ->
    AdjacentCandidateUndoEvidence
      n m old_budget initial_dist times origins destinations
      candidate_total best ->
    old_total - best <= candidate_total.
Proof.
  intros n m old_budget initial_dist times origins destinations
    old_total candidate_total best Hminimum Hbest_nonnegative Hevidence.
  unfold SightseeingMinimumTotal,
    MaxMin.min_value_of_subset, MaxMin.min_object_of_subset in Hminimum.
  destruct Hminimum as [minimum_witness [[Hminimum_member Hleast] Hvalue]].
  cbn in Hvalue.
  subst minimum_witness.
  destruct Hevidence as
    [candidate_dist [candidate_latest [candidate_arrivals
      [Hcandidate_latest [Hcandidate_feasible
        [Hcandidate_schedule [Hcandidate_total Hundo]]]]]]].
  destruct Hundo as [Hold_feasible | Hundo].
  - assert (Hold_candidate :
      SightseeingCandidateTotal
        n m old_budget initial_dist times origins destinations
        candidate_total).
    {
      exists candidate_dist, candidate_latest, candidate_arrivals.
      exact (conj Hcandidate_latest
        (conj Hold_feasible
          (conj Hcandidate_schedule Hcandidate_total))).
    }
    specialize (Hleast candidate_total Hold_candidate).
    cbn in Hleast.
    lia.
  - destruct Hundo as
      [edge [restored_dist [restored_latest [restored_arrivals
        [restored_total [loss
          [Hundo [Hrestored_latest [Hrestored_feasible
            [Hrestored_schedule [Hrestored_total [Hloss Hbest]]]]]]]]]]]].
    assert (Hrestored_candidate :
      SightseeingCandidateTotal
        n m old_budget initial_dist times origins destinations
        restored_total).
    {
      exists restored_dist, restored_latest, restored_arrivals.
      exact (conj Hrestored_latest
        (conj Hrestored_feasible
          (conj Hrestored_schedule Hrestored_total))).
    }
    specialize (Hleast restored_total Hrestored_candidate).
    cbn in Hleast.
    lia.
Qed.

Lemma selected_exchange_adjacent_lower_bound__exchange :
  forall n m budget remaining initial_dist times origins destinations
         dist latest counts arrivals best current_total candidate_total,
    SelectedExchangeCertificate
      n m budget remaining initial_dist times origins destinations
      dist latest counts arrivals best ->
    PassengerTravelTotal m times destinations arrivals current_total ->
    SightseeingMinimumTotal
      n m (budget - remaining)
      initial_dist times origins destinations current_total ->
    SightseeingCandidateTotal
      n m (budget - remaining + 1)
      initial_dist times origins destinations candidate_total ->
    current_total - best <= candidate_total.
Proof.
  intros n m budget remaining initial_dist times origins destinations
    dist latest counts arrivals best current_total candidate_total
    Hcertificate Htotal Hminimum Hcandidate.
  destruct Hcertificate as
    [Hbest_nonnegative [stored_total [Hstored_total Hlower]]].
  assert (stored_total = current_total).
  {
    unfold PassengerTravelTotal in Hstored_total, Htotal.
    lia.
  }
  subst stored_total.
  apply Hlower.
  exact Hcandidate.
Qed.

(* ------------------------------------------------------------------------- *)
(* Max-plus cut representation of the chain schedule.  Prefix sums are kept
   relational and every maximum continues to use [MaxMinLib]. *)

Definition ChainIntervalDistance
    (dist : list Z) (lo hi : Z) : Z :=
  sum (fun edge => lo <= edge < hi)
      (fun edge => Znth edge dist 0).

Definition ChainArrivalClosedForm
    (dist latest : list Z) (station arrival : Z) : Prop :=
  (station = 0 /\ arrival = 0) \/
  (0 < station /\
   max_value_of_subset_with_default Z.le
     (fun cut => 0 <= cut < station)
     (fun cut =>
        Znth cut latest 0 +
        ChainIntervalDistance dist cut station)
     (ChainIntervalDistance dist 0 station)
     arrival).

Lemma chain_interval_empty__cut_exchange :
  forall dist lo hi,
    hi <= lo ->
    ChainIntervalDistance dist lo hi = 0.
Proof.
  intros dist lo hi Hhi.
  unfold ChainIntervalDistance.
  apply sum_Z_range_empty.
  lia.
Qed.

Lemma chain_interval_snoc__cut_exchange :
  forall dist lo hi,
    lo <= hi ->
    ChainIntervalDistance dist lo (hi + 1) =
    ChainIntervalDistance dist lo hi + Znth hi dist 0.
Proof.
  intros dist lo hi Hrange.
  unfold ChainIntervalDistance.
  rewrite (sum_Z_range_split lo hi (hi + 1)) by lia.
  rewrite (sum_Z_range_cons hi (hi + 1)) by lia.
  rewrite (sum_Z_range_empty (hi + 1) (hi + 1)
    (fun edge => Znth edge dist 0)) by lia.
  lia.
Qed.

Lemma chain_closed_form_bounds__cut_exchange :
  forall dist latest station arrival,
    0 <= station ->
    ChainArrivalClosedForm dist latest station arrival ->
    ChainIntervalDistance dist 0 station <= arrival /\
    (forall cut, 0 <= cut < station ->
       Znth cut latest 0 +
       ChainIntervalDistance dist cut station <= arrival).
Proof.
  intros dist latest station arrival Hstation Hclosed.
  unfold ChainArrivalClosedForm in Hclosed.
  destruct Hclosed as [[Hzero Harrival] | [Hpositive Hmaximum]].
  - subst station arrival.
    split.
    + rewrite chain_interval_empty__cut_exchange by lia.
      lia.
    + intros cut Hcut. lia.
  - unfold MaxMin.max_value_of_subset_with_default in Hmaximum.
    destruct Hmaximum as [[Hmaximum Hdefault] | [Hall Hdefault]].
    + split; [exact Hdefault |].
      intros cut Hcut.
      destruct Hmaximum as
        [chosen [[Hchosen Hgreatest] Hchosen_value]].
      subst arrival.
      apply Hgreatest.
      exact Hcut.
    + subst arrival.
      split; [lia |].
      intros cut Hcut.
      apply Hall.
      exact Hcut.
Qed.

Lemma chain_closed_form_source__cut_exchange :
  forall dist latest station arrival,
    0 <= station ->
    ChainArrivalClosedForm dist latest station arrival ->
    arrival = ChainIntervalDistance dist 0 station \/
    exists cut,
      0 <= cut < station /\
      arrival =
        Znth cut latest 0 +
        ChainIntervalDistance dist cut station.
Proof.
  intros dist latest station arrival Hstation Hclosed.
  unfold ChainArrivalClosedForm in Hclosed.
  destruct Hclosed as [[Hzero Harrival] | [Hpositive Hmaximum]].
  - subst station arrival.
    left.
    rewrite chain_interval_empty__cut_exchange by lia.
    reflexivity.
  - unfold MaxMin.max_value_of_subset_with_default in Hmaximum.
    destruct Hmaximum as [[Hmaximum Hdefault] | [Hall Hdefault]].
    + right.
      destruct Hmaximum as
        [cut [[Hcut Hgreatest] Hvalue]].
      exists cut.
      split; [exact Hcut | symmetry; exact Hvalue].
    + left. symmetry. exact Hdefault.
Qed.

Lemma chain_closed_form_step__cut_exchange :
  forall dist latest arrivals station departure,
    0 <= station ->
    ChainArrivalClosedForm
      dist latest station (Znth station arrivals 0) ->
    StationDeparture arrivals latest station departure ->
    ChainArrivalClosedForm
      dist latest (station + 1)
      (departure + Znth station dist 0).
Proof.
  intros dist latest arrivals station departure
    Hstation Hclosed Hdeparture.
  pose proof (chain_closed_form_bounds__cut_exchange
    dist latest station (Znth station arrivals 0)
    Hstation Hclosed) as [Hdefault_bound Hcut_bound].
  pose proof (chain_closed_form_source__cut_exchange
    dist latest station (Znth station arrivals 0)
    Hstation Hclosed) as Hsource.
  unfold StationDeparture,
    MaxMin.max_value_of_subset_with_default in Hdeparture.
  destruct Hdeparture as
    [[Hlatest_max Harrival_le] | [Hlatest_le Harrival_eq]].
  - destruct Hlatest_max as
      [candidate [[Hcandidate Hgreatest] Hdeparture_value]].
    change (candidate = Znth station latest 0) in Hcandidate.
    subst candidate.
    cbn in Hdeparture_value.
    subst departure.
    unfold ChainArrivalClosedForm.
    right.
    split; [lia |].
    unfold MaxMin.max_value_of_subset_with_default.
    left.
    split.
    + unfold MaxMin.max_value_of_subset.
      exists station.
      split.
      * unfold MaxMin.max_object_of_subset.
        split.
        -- change (0 <= station < station + 1). lia.
        --
        intros cut Hcut.
        change (0 <= cut < station + 1) in Hcut.
        destruct (Z.eq_dec cut station) as [Heq | Hneq].
        ++ subst cut.
           specialize (Hgreatest (Znth station latest 0) eq_refl).
           cbn in Hgreatest.
           lia.
        ++ assert (Hcut_old : 0 <= cut < station) by lia.
           specialize (Hcut_bound cut Hcut_old).
           rewrite (chain_interval_snoc__cut_exchange
             dist cut station) by lia.
           rewrite (chain_interval_snoc__cut_exchange
             dist station station) by lia.
           rewrite (chain_interval_empty__cut_exchange
             dist station station) by lia.
           lia.
      * rewrite (chain_interval_snoc__cut_exchange
          dist station station) by lia.
        rewrite (chain_interval_empty__cut_exchange
          dist station station) by lia.
        lia.
    + rewrite (chain_interval_snoc__cut_exchange
        dist 0 station) by lia.
      lia.
  - cbn in Harrival_eq.
    subst departure.
    destruct Hsource as [Hsource_default | Hsource_cut].
    + unfold ChainArrivalClosedForm.
      right.
      split; [lia |].
      unfold MaxMin.max_value_of_subset_with_default.
      right.
      split.
      * intros cut Hcut.
        change (0 <= cut < station + 1) in Hcut.
        destruct (Z.eq_dec cut station) as [Heq | Hneq].
        -- subst cut.
           rewrite (chain_interval_snoc__cut_exchange
             dist station station) by lia.
           rewrite (chain_interval_empty__cut_exchange
             dist station station) by lia.
           specialize (Hlatest_le (Znth station latest 0) eq_refl).
           cbn in Hlatest_le.
           rewrite (chain_interval_snoc__cut_exchange
             dist 0 station) by lia.
           lia.
        -- assert (Hcut_old : 0 <= cut < station) by lia.
           specialize (Hcut_bound cut Hcut_old).
           rewrite (chain_interval_snoc__cut_exchange
             dist cut station) by lia.
           rewrite (chain_interval_snoc__cut_exchange
             dist 0 station) by lia.
           lia.
      * rewrite (chain_interval_snoc__cut_exchange
          dist 0 station) by lia.
        lia.
    + destruct Hsource_cut as [chosen [Hchosen Hsource_value]].
      unfold ChainArrivalClosedForm.
      right.
      split; [lia |].
      unfold MaxMin.max_value_of_subset_with_default.
      left.
      split.
      * unfold MaxMin.max_value_of_subset.
        exists chosen.
        split.
        -- unfold MaxMin.max_object_of_subset.
           split.
           ++ change (0 <= chosen < station + 1). lia.
           ++
           intros cut Hcut.
           change (0 <= cut < station + 1) in Hcut.
           destruct (Z.eq_dec cut station) as [Heq | Hneq].
           ** subst cut.
              rewrite (chain_interval_snoc__cut_exchange
                dist station station) by lia.
              rewrite (chain_interval_empty__cut_exchange
                dist station station) by lia.
              specialize (Hlatest_le (Znth station latest 0) eq_refl).
              cbn in Hlatest_le.
              rewrite (chain_interval_snoc__cut_exchange
                dist chosen station) by lia.
              lia.
           ** assert (Hcut_old : 0 <= cut < station) by lia.
              specialize (Hcut_bound cut Hcut_old).
              rewrite (chain_interval_snoc__cut_exchange
                dist cut station) by lia.
              rewrite (chain_interval_snoc__cut_exchange
                dist chosen station) by lia.
              lia.
        -- rewrite (chain_interval_snoc__cut_exchange
             dist chosen station) by lia.
           lia.
      * rewrite (chain_interval_snoc__cut_exchange
          dist 0 station) by lia.
        lia.
Qed.

Lemma bus_schedule_closed_form__cut_exchange :
  forall n dist latest arrivals,
    BusArrivalSchedule n dist latest arrivals ->
    forall station, 0 <= station < n ->
      ChainArrivalClosedForm
        dist latest station (Znth station arrivals 0).
Proof.
  intros n dist latest arrivals Hschedule station Hstation.
  destruct Hschedule as [Hlength [Hzero Hstep]].
  assert (Hnat : forall k : nat,
    Z.of_nat k < n ->
    ChainArrivalClosedForm
      dist latest (Z.of_nat k)
      (Znth (Z.of_nat k) arrivals 0)).
  {
    induction k as [|k IH].
    - intros Hzero_range.
      unfold ChainArrivalClosedForm.
      left. cbn. tauto.
    - intros Hsuccessor_range.
      rewrite Nat2Z.inj_succ in Hsuccessor_range.
      specialize (IH ltac:(lia)).
      specialize (Hstep (Z.of_nat k) ltac:(lia)).
      destruct Hstep as [departure [Hdeparture Harrival]].
      pose proof (chain_closed_form_step__cut_exchange
        dist latest arrivals (Z.of_nat k) departure
        ltac:(lia) IH Hdeparture) as Hnext.
      replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
      rewrite Harrival.
      exact Hnext.
  }
  replace station with (Z.of_nat (Z.to_nat station)) by lia.
  apply Hnat.
  lia.
Qed.

Lemma max_default_Z_bounds_source__cut_exchange :
  forall (A : Type) (P : A -> Prop) (f : A -> Z) default maximum,
    max_value_of_subset_with_default Z.le P f default maximum ->
    default <= maximum /\
    (forall x, P x -> f x <= maximum) /\
    (maximum = default \/ exists x, P x /\ maximum = f x).
Proof.
  intros A P f default maximum Hmaximum.
  unfold MaxMin.max_value_of_subset_with_default in Hmaximum.
  destruct Hmaximum as [[Hmaximum Hdefault] | [Hall Hdefault]].
  - destruct Hmaximum as [chosen [[Hchosen Hgreatest] Hvalue]].
    split; [exact Hdefault |].
    split.
    + intros x Hx.
      subst maximum.
      apply Hgreatest. exact Hx.
    + right. exists chosen. split; [exact Hchosen |].
      symmetry. exact Hvalue.
  - subst maximum.
    split; [lia |].
    split; [exact Hall | tauto].
Qed.

Lemma max_default_Z_min_max_pair__cut_exchange :
  forall (A : Type) (P : A -> Prop)
         (f g : A -> Z) default_f default_g
         maximum_f maximum_g maximum_min maximum_max,
    max_value_of_subset_with_default
      Z.le P f default_f maximum_f ->
    max_value_of_subset_with_default
      Z.le P g default_g maximum_g ->
    max_value_of_subset_with_default
      Z.le P (fun x => Z.min (f x) (g x))
      (Z.min default_f default_g) maximum_min ->
    max_value_of_subset_with_default
      Z.le P (fun x => Z.max (f x) (g x))
      (Z.max default_f default_g) maximum_max ->
    maximum_min + maximum_max <= maximum_f + maximum_g.
Proof.
  intros A P f g default_f default_g maximum_f maximum_g
    maximum_min maximum_max Hf Hg Hmin Hmax.
  pose proof (max_default_Z_bounds_source__cut_exchange
    A P f default_f maximum_f Hf)
    as [Hf_default [Hf_bound Hf_source]].
  pose proof (max_default_Z_bounds_source__cut_exchange
    A P g default_g maximum_g Hg)
    as [Hg_default [Hg_bound Hg_source]].
  pose proof (max_default_Z_bounds_source__cut_exchange
    A P (fun x => Z.min (f x) (g x))
    (Z.min default_f default_g) maximum_min Hmin)
    as [Hmin_default [Hmin_bound Hmin_source]].
  pose proof (max_default_Z_bounds_source__cut_exchange
    A P (fun x => Z.max (f x) (g x))
    (Z.max default_f default_g) maximum_max Hmax)
    as [Hmax_default [Hmax_bound Hmax_source]].
  assert (Hminimum_f : maximum_min <= maximum_f).
  {
    destruct Hmin_source as [Hsource | [x [Hx Hsource]]].
    - subst maximum_min. lia.
    - subst maximum_min.
      specialize (Hf_bound x Hx).
      eapply Z.le_trans.
      + apply Z.le_min_l.
      + exact Hf_bound.
  }
  assert (Hminimum_g : maximum_min <= maximum_g).
  {
    destruct Hmin_source as [Hsource | [x [Hx Hsource]]].
    - subst maximum_min. lia.
    - subst maximum_min.
      specialize (Hg_bound x Hx).
      eapply Z.le_trans.
      + apply Z.le_min_r.
      + exact Hg_bound.
  }
  assert (Hmaximum_upper :
      maximum_max <= Z.max maximum_f maximum_g).
  {
    destruct Hmax_source as [Hsource | [x [Hx Hsource]]].
    - subst maximum_max.
      apply Z.max_lub; lia.
    - subst maximum_max.
      specialize (Hf_bound x Hx).
      specialize (Hg_bound x Hx).
      apply Z.max_lub; lia.
  }
  destruct (Z_le_gt_dec maximum_f maximum_g).
  - rewrite Z.max_r in Hmaximum_upper by lia.
    lia.
  - rewrite Z.max_l in Hmaximum_upper by lia.
    lia.
Qed.

Definition ChainCutEnvelope
    (latest : list Z) (station : Z)
    (prefix : Z -> Z) (envelope : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun cut => 0 <= cut < station)
    (fun cut => Znth cut latest 0 - prefix cut)
    (- prefix 0) envelope.

Definition ChainProfileArrival
    (latest : list Z) (station : Z)
    (prefix : Z -> Z) (arrival : Z) : Prop :=
  (station = 0 /\ arrival = 0) \/
  (0 < station /\
   exists envelope,
     ChainCutEnvelope latest station prefix envelope /\
     arrival = prefix station + envelope).

Lemma chain_interval_split__cut_exchange :
  forall dist cut station,
    0 <= cut <= station ->
    ChainIntervalDistance dist 0 station =
    ChainIntervalDistance dist 0 cut +
    ChainIntervalDistance dist cut station.
Proof.
  intros dist cut station Hcut.
  unfold ChainIntervalDistance.
  apply sum_Z_range_split.
  lia.
Qed.

Lemma max_default_Z_shift__cut_exchange :
  forall (A : Type) (P : A -> Prop) (f : A -> Z)
         default maximum shift,
    max_value_of_subset_with_default Z.le P f default maximum ->
    max_value_of_subset_with_default Z.le P
      (fun x => f x + shift) (default + shift) (maximum + shift).
Proof.
  intros A P f default maximum shift Hmaximum.
  unfold MaxMin.max_value_of_subset_with_default in Hmaximum |-.
  destruct Hmaximum as [[Hmaximum Hdefault] | [Hall Hdefault]].
  - left.
    split; [| lia].
    destruct Hmaximum as [chosen [[Hchosen Hgreatest] Hvalue]].
    exists chosen.
    split.
    + split; [exact Hchosen |].
      intros x Hx.
      specialize (Hgreatest x Hx).
      lia.
    + lia.
  - right.
    split.
    + intros x Hx.
      specialize (Hall x Hx).
      lia.
    + lia.
Qed.

Lemma chain_closed_form_profile__cut_exchange :
  forall dist latest station arrival,
    0 <= station ->
    ChainArrivalClosedForm dist latest station arrival ->
    ChainProfileArrival latest station
      (fun s => ChainIntervalDistance dist 0 s) arrival.
Proof.
  intros dist latest station arrival Hstation Hclosed.
  unfold ChainArrivalClosedForm in Hclosed.
  destruct Hclosed as [[Hzero Harrival] | [Hpositive Hmaximum]].
  - unfold ChainProfileArrival.
    left. tauto.
  - unfold ChainProfileArrival.
    right.
    split; [exact Hpositive |].
    exists (arrival - ChainIntervalDistance dist 0 station).
    split; [| lia].
    unfold ChainCutEnvelope.
    pose proof (max_default_Z_shift__cut_exchange
      Z (fun cut => 0 <= cut < station)
      (fun cut =>
         Znth cut latest 0 +
         ChainIntervalDistance dist cut station)
      (ChainIntervalDistance dist 0 station) arrival
      (- ChainIntervalDistance dist 0 station) Hmaximum) as Hshift.
    replace
      (ChainIntervalDistance dist 0 station +
       - ChainIntervalDistance dist 0 station) with 0 in Hshift by ring.
    replace
      (arrival + - ChainIntervalDistance dist 0 station)
      with (arrival - ChainIntervalDistance dist 0 station)
      in Hshift by ring.
    eapply (@MaxMin.max_default_eq_forward
      Z Z.le Zle_TotalOrder Z).
    + exact Hshift.
    + intros cut Hcut.
      change (0 <= cut < station) in Hcut.
      exists cut.
      split; [exact Hcut |].
      rewrite (chain_interval_split__cut_exchange
        dist cut station) by lia.
      lia.
    + intros cut Hcut.
      change (0 <= cut < station) in Hcut.
      exists cut.
      split; [exact Hcut |].
      rewrite (chain_interval_split__cut_exchange
        dist cut station) by lia.
      lia.
Qed.

Lemma Z_sub_max_min__cut_exchange :
  forall a b c,
    a - Z.max b c = Z.min (a - b) (a - c).
Proof.
  intros a b c.
  destruct (Z_le_gt_dec b c).
  - rewrite Z.max_r by lia.
    rewrite Z.min_r by lia.
    reflexivity.
  - rewrite Z.max_l by lia.
    rewrite Z.min_l by lia.
    reflexivity.
Qed.

Lemma Z_sub_min_max__cut_exchange :
  forall a b c,
    a - Z.min b c = Z.max (a - b) (a - c).
Proof.
  intros a b c.
  destruct (Z_le_gt_dec b c).
  - rewrite Z.min_l by lia.
    rewrite Z.max_l by lia.
    reflexivity.
  - rewrite Z.min_r by lia.
    rewrite Z.max_r by lia.
    reflexivity.
Qed.

Lemma chain_profile_arrival_pair__cut_exchange :
  forall latest station (prefix1 prefix2 : Z -> Z)
         arrival1 arrival2 arrival_min arrival_max,
    0 < station ->
    ChainProfileArrival latest station prefix1 arrival1 ->
    ChainProfileArrival latest station prefix2 arrival2 ->
    ChainProfileArrival latest station
      (fun s => Z.min (prefix1 s) (prefix2 s)) arrival_min ->
    ChainProfileArrival latest station
      (fun s => Z.max (prefix1 s) (prefix2 s)) arrival_max ->
    arrival_min + arrival_max <= arrival1 + arrival2.
Proof.
  intros latest station prefix1 prefix2
    arrival1 arrival2 arrival_min arrival_max Hstation
    Harrival1 Harrival2 Harrival_min Harrival_max.
  unfold ChainProfileArrival in
    Harrival1, Harrival2, Harrival_min, Harrival_max.
  destruct Harrival1 as [[Hzero _] |
    [_ [envelope1 [Henvelope1 Hvalue1]]]]; [lia |].
  destruct Harrival2 as [[Hzero _] |
    [_ [envelope2 [Henvelope2 Hvalue2]]]]; [lia |].
  destruct Harrival_min as [[Hzero _] |
    [_ [envelope_min [Henvelope_min Hvalue_min]]]]; [lia |].
  destruct Harrival_max as [[Hzero _] |
    [_ [envelope_max [Henvelope_max Hvalue_max]]]]; [lia |].
  unfold ChainCutEnvelope in
    Henvelope1, Henvelope2, Henvelope_min, Henvelope_max.
  assert (Hscore_min :
    max_value_of_subset_with_default Z.le
      (fun cut => 0 <= cut < station)
      (fun cut =>
         Z.min
           (Znth cut latest 0 - prefix1 cut)
           (Znth cut latest 0 - prefix2 cut))
      (Z.min (- prefix1 0) (- prefix2 0)) envelope_max).
  {
    replace (- Z.max (prefix1 0) (prefix2 0))
      with (Z.min (- prefix1 0) (- prefix2 0))
      in Henvelope_max.
    2: {
      pose proof (Z_sub_max_min__cut_exchange
        0 (prefix1 0) (prefix2 0)).
      lia.
    }
    eapply (@MaxMin.max_default_eq_forward
      Z Z.le Zle_TotalOrder Z).
    - exact Henvelope_max.
    - intros cut Hcut.
      exists cut. split; [exact Hcut |].
      rewrite Z_sub_max_min__cut_exchange.
      lia.
    - intros cut Hcut.
      exists cut. split; [exact Hcut |].
      rewrite Z_sub_max_min__cut_exchange.
      lia.
  }
  assert (Hscore_max :
    max_value_of_subset_with_default Z.le
      (fun cut => 0 <= cut < station)
      (fun cut =>
         Z.max
           (Znth cut latest 0 - prefix1 cut)
           (Znth cut latest 0 - prefix2 cut))
      (Z.max (- prefix1 0) (- prefix2 0)) envelope_min).
  {
    replace (- Z.min (prefix1 0) (prefix2 0))
      with (Z.max (- prefix1 0) (- prefix2 0))
      in Henvelope_min.
    2: {
      pose proof (Z_sub_min_max__cut_exchange
        0 (prefix1 0) (prefix2 0)).
      lia.
    }
    eapply (@MaxMin.max_default_eq_forward
      Z Z.le Zle_TotalOrder Z).
    - exact Henvelope_min.
    - intros cut Hcut.
      exists cut. split; [exact Hcut |].
      rewrite Z_sub_min_max__cut_exchange.
      lia.
    - intros cut Hcut.
      exists cut. split; [exact Hcut |].
      rewrite Z_sub_min_max__cut_exchange.
      lia.
  }
  pose proof (max_default_Z_min_max_pair__cut_exchange
    Z (fun cut => 0 <= cut < station)
    (fun cut => Znth cut latest 0 - prefix1 cut)
    (fun cut => Znth cut latest 0 - prefix2 cut)
    (- prefix1 0) (- prefix2 0)
    envelope1 envelope2 envelope_max envelope_min
    Henvelope1 Henvelope2 Hscore_min Hscore_max) as Henvelopes.
  subst arrival1 arrival2 arrival_min arrival_max.
  assert (Hprefix :
    Z.min (prefix1 station) (prefix2 station) +
    Z.max (prefix1 station) (prefix2 station) =
    prefix1 station + prefix2 station).
  {
    destruct (Z_le_gt_dec (prefix1 station) (prefix2 station)).
    - rewrite Z.min_l, Z.max_r by lia. ring.
    - rewrite Z.min_r, Z.max_l by lia. ring.
  }
  lia.
Qed.

Lemma max_default_Z_ext__cut_exchange :
  forall (A : Type) (P : A -> Prop) (f1 f2 : A -> Z)
         default1 default2 maximum,
    default1 = default2 ->
    (forall x, P x -> f1 x = f2 x) ->
    max_value_of_subset_with_default
      Z.le P f1 default1 maximum ->
    max_value_of_subset_with_default
      Z.le P f2 default2 maximum.
Proof.
  intros A P f1 f2 default1 default2 maximum
    Hdefault Hfunction Hmaximum.
  subst default2.
  unfold MaxMin.max_value_of_subset_with_default in Hmaximum |-.
  destruct Hmaximum as [[Hmaximum Hdefault_bound] |
    [Hall Hdefault_value]].
  - left.
    split; [| exact Hdefault_bound].
    destruct Hmaximum as [chosen [[Hchosen Hgreatest] Hvalue]].
    exists chosen.
    split.
    + split; [exact Hchosen |].
      intros x Hx.
      rewrite <- (Hfunction x Hx), <- (Hfunction chosen Hchosen).
      apply Hgreatest. exact Hx.
    + rewrite <- (Hfunction chosen Hchosen).
      exact Hvalue.
  - right.
    split; [| exact Hdefault_value].
    intros x Hx.
    rewrite <- (Hfunction x Hx).
    apply Hall. exact Hx.
Qed.

Lemma chain_profile_arrival_prefix_ext__cut_exchange :
  forall latest station (prefix1 prefix2 : Z -> Z) arrival,
    0 <= station ->
    (forall s, 0 <= s <= station -> prefix1 s = prefix2 s) ->
    ChainProfileArrival latest station prefix1 arrival ->
    ChainProfileArrival latest station prefix2 arrival.
Proof.
  intros latest station prefix1 prefix2 arrival
    Hstation Hprefix Harrival.
  unfold ChainProfileArrival in Harrival |-.
  destruct Harrival as [[Hzero Hvalue] |
    [Hpositive [envelope [Henvelope Hvalue]]]].
  - left. tauto.
  - right.
    split; [exact Hpositive |].
    exists envelope.
    split.
    + unfold ChainCutEnvelope in Henvelope |-.
      eapply (@max_default_Z_ext__cut_exchange
        Z (fun cut => 0 <= cut < station)
        (fun cut => Znth cut latest 0 - prefix1 cut)
        (fun cut => Znth cut latest 0 - prefix2 cut)
        (- prefix1 0) (- prefix2 0) envelope).
      * assert (Hzero_range : 0 <= 0 <= station) by lia.
        pose proof (Hprefix 0 Hzero_range) as Hzero.
        lia.
      * intros cut Hcut.
        change (0 <= cut < station) in Hcut.
        assert (Hcut_range : 0 <= cut <= station) by lia.
        pose proof (Hprefix cut Hcut_range) as Hcut_eq.
        lia.
      * exact Henvelope.
    + rewrite <- (Hprefix station) by lia.
      exact Hvalue.
Qed.

Definition ChainPrefixMeetJoin
    (n : Z) (dist1 dist2 dist_meet dist_join : list Z) : Prop :=
  forall station, 0 <= station <= n - 1 ->
    ChainIntervalDistance dist_meet 0 station =
      Z.min
        (ChainIntervalDistance dist1 0 station)
        (ChainIntervalDistance dist2 0 station) /\
    ChainIntervalDistance dist_join 0 station =
      Z.max
        (ChainIntervalDistance dist1 0 station)
        (ChainIntervalDistance dist2 0 station).

Lemma destination_counts_nonnegative__cut_exchange :
  forall n m destinations counts,
    DestinationCounts n m destinations counts ->
    forall station, 0 <= station < n ->
      0 <= Znth station counts 0.
Proof.
  intros n m destinations counts Hcounts station Hstation.
  unfold DestinationCounts in Hcounts.
  destruct Hcounts as [Hlength Hcount].
  rewrite Hcount by exact Hstation.
  apply sum_nonneg.
  intros passenger Hpassenger.
  lia.
Qed.

Lemma chain_weighted_arrival_lattice__cut_exchange :
  forall n counts latest
         dist1 dist2 dist_meet dist_join
         arrivals1 arrivals2 arrivals_meet arrivals_join
         weighted1 weighted2 weighted_meet weighted_join,
    2 <= n ->
    (forall station, 0 <= station < n ->
       0 <= Znth station counts 0) ->
    BusArrivalSchedule n dist1 latest arrivals1 ->
    BusArrivalSchedule n dist2 latest arrivals2 ->
    BusArrivalSchedule n dist_meet latest arrivals_meet ->
    BusArrivalSchedule n dist_join latest arrivals_join ->
    ChainPrefixMeetJoin n dist1 dist2 dist_meet dist_join ->
    ChainWeightedArrivalTotal n counts arrivals1 weighted1 ->
    ChainWeightedArrivalTotal n counts arrivals2 weighted2 ->
    ChainWeightedArrivalTotal n counts arrivals_meet weighted_meet ->
    ChainWeightedArrivalTotal n counts arrivals_join weighted_join ->
    weighted_meet + weighted_join <= weighted1 + weighted2.
Proof.
  intros n counts latest dist1 dist2 dist_meet dist_join
    arrivals1 arrivals2 arrivals_meet arrivals_join
    weighted1 weighted2 weighted_meet weighted_join
    Hn Hcounts Hschedule1 Hschedule2 Hschedule_meet Hschedule_join
    Hmeetjoin Hweighted1 Hweighted2 Hweighted_meet Hweighted_join.
  unfold ChainWeightedArrivalTotal in
    Hweighted1, Hweighted2, Hweighted_meet, Hweighted_join.
  subst weighted1 weighted2 weighted_meet weighted_join.
  rewrite <- !sum_Z_range_add.
  apply sum_Z_range_le.
  intros station Hstation.
  assert (Hstation_full : 0 <= station < n) by lia.
  pose proof (bus_schedule_closed_form__cut_exchange
    n dist1 latest arrivals1 Hschedule1 station Hstation_full) as Hclosed1.
  pose proof (bus_schedule_closed_form__cut_exchange
    n dist2 latest arrivals2 Hschedule2 station Hstation_full) as Hclosed2.
  pose proof (bus_schedule_closed_form__cut_exchange
    n dist_meet latest arrivals_meet Hschedule_meet
    station Hstation_full) as Hclosed_meet.
  pose proof (bus_schedule_closed_form__cut_exchange
    n dist_join latest arrivals_join Hschedule_join
    station Hstation_full) as Hclosed_join.
  pose proof (chain_closed_form_profile__cut_exchange
    dist1 latest station (Znth station arrivals1 0)
    ltac:(lia) Hclosed1) as Hprofile1.
  pose proof (chain_closed_form_profile__cut_exchange
    dist2 latest station (Znth station arrivals2 0)
    ltac:(lia) Hclosed2) as Hprofile2.
  pose proof (chain_closed_form_profile__cut_exchange
    dist_meet latest station (Znth station arrivals_meet 0)
    ltac:(lia) Hclosed_meet) as Hprofile_meet.
  pose proof (chain_closed_form_profile__cut_exchange
    dist_join latest station (Znth station arrivals_join 0)
    ltac:(lia) Hclosed_join) as Hprofile_join.
  assert (Hprofile_meet' :
    ChainProfileArrival latest station
      (fun s => Z.min
        (ChainIntervalDistance dist1 0 s)
        (ChainIntervalDistance dist2 0 s))
      (Znth station arrivals_meet 0)).
  {
    eapply chain_profile_arrival_prefix_ext__cut_exchange.
    - lia.
    - intros s Hs.
      apply (proj1 (Hmeetjoin s ltac:(lia))).
    - exact Hprofile_meet.
  }
  assert (Hprofile_join' :
    ChainProfileArrival latest station
      (fun s => Z.max
        (ChainIntervalDistance dist1 0 s)
        (ChainIntervalDistance dist2 0 s))
      (Znth station arrivals_join 0)).
  {
    eapply chain_profile_arrival_prefix_ext__cut_exchange.
    - lia.
    - intros s Hs.
      apply (proj2 (Hmeetjoin s ltac:(lia))).
    - exact Hprofile_join.
  }
  pose proof (chain_profile_arrival_pair__cut_exchange
    latest station
    (fun s => ChainIntervalDistance dist1 0 s)
    (fun s => ChainIntervalDistance dist2 0 s)
    (Znth station arrivals1 0)
    (Znth station arrivals2 0)
    (Znth station arrivals_meet 0)
    (Znth station arrivals_join 0)
    ltac:(lia) Hprofile1 Hprofile2 Hprofile_meet' Hprofile_join')
    as Harrival_pair.
  specialize (Hcounts station Hstation_full).
  nia.
Qed.

Lemma finite_Z_function_list__cut_exchange :
  forall length (f : Z -> Z),
    0 <= length ->
    exists values,
      Zlength values = length /\
      forall i, 0 <= i < length -> Znth i values 0 = f i.
Proof.
  intros length f Hlength.
  remember (Z.to_nat length) as fuel eqn:Hfuel.
  replace length with (Z.of_nat fuel) by lia.
  clear length Hlength Hfuel.
  induction fuel as [|fuel IH].
  - exists [].
    split; [reflexivity |].
    intros i Hi. lia.
  - destruct IH as [values [Hvalues_length Hvalues]].
    exists (values ++ [f (Z.of_nat fuel)]).
    split.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    + intros i Hi.
      destruct (Z_lt_ge_dec i (Z.of_nat fuel)).
      * rewrite app_Znth1 by (rewrite Hvalues_length; lia).
        apply Hvalues. lia.
      * assert (i = Z.of_nat fuel) by lia.
        subst i.
        rewrite app_Znth2 by (rewrite Hvalues_length; lia).
        rewrite Hvalues_length.
        replace (Z.of_nat fuel - Z.of_nat fuel) with 0 by lia.
        reflexivity.
Qed.

Lemma sum_Z_range_differences__cut_exchange :
  forall (prefix : Z -> Z) hi,
    0 <= hi ->
    sum (fun edge => 0 <= edge < hi)
        (fun edge => prefix (edge + 1) - prefix edge) =
    prefix hi - prefix 0.
Proof.
  intros prefix hi Hhi.
  remember (Z.to_nat hi) as fuel eqn:Hfuel.
  replace hi with (Z.of_nat fuel) by lia.
  clear hi Hhi Hfuel.
  induction fuel as [|fuel IH].
  - rewrite sum_Z_range_empty by lia.
    cbn. ring.
  - rewrite Nat2Z.inj_succ.
    rewrite (sum_Z_range_split 0 (Z.of_nat fuel)
      (Z.of_nat fuel + 1)) by lia.
    rewrite (sum_Z_range_cons (Z.of_nat fuel)
      (Z.of_nat fuel + 1)) by lia.
    rewrite (sum_Z_range_empty (Z.of_nat fuel + 1)
      (Z.of_nat fuel + 1)
      (fun edge => prefix (edge + 1) - prefix edge)) by lia.
    rewrite IH.
    ring.
Qed.

Lemma chain_distance_from_prefix__cut_exchange :
  forall n (prefix : Z -> Z),
    1 <= n ->
    prefix 0 = 0 ->
    exists dist,
      Zlength dist = n - 1 /\
      (forall edge, 0 <= edge < n - 1 ->
         Znth edge dist 0 = prefix (edge + 1) - prefix edge) /\
      (forall station, 0 <= station <= n - 1 ->
         ChainIntervalDistance dist 0 station = prefix station).
Proof.
  intros n prefix Hn Hprefix_zero.
  destruct (finite_Z_function_list__cut_exchange
    (n - 1) (fun edge => prefix (edge + 1) - prefix edge)
    ltac:(lia)) as [dist [Hlength Hvalues]].
  exists dist.
  split; [exact Hlength |].
  split; [exact Hvalues |].
  intros station Hstation.
  unfold ChainIntervalDistance.
  rewrite (sum_Z_range_ext 0 station
    (fun edge => Znth edge dist 0)
    (fun edge => prefix (edge + 1) - prefix edge)).
  2: {
    intros edge Hedge.
    apply Hvalues. lia.
  }
  rewrite sum_Z_range_differences__cut_exchange by lia.
  lia.
Qed.

Lemma Z_min_increment_bounds__cut_exchange :
  forall a0 a1 b0 b1 lower upper,
    lower <= a1 - a0 <= upper ->
    lower <= b1 - b0 <= upper ->
    lower <= Z.min a1 b1 - Z.min a0 b0 <= upper.
Proof.
  intros a0 a1 b0 b1 lower upper Ha Hb.
  destruct (Z_le_gt_dec a0 b0);
  destruct (Z_le_gt_dec a1 b1);
  rewrite ?Z.min_l, ?Z.min_r by lia;
  lia.
Qed.

Lemma Z_max_increment_bounds__cut_exchange :
  forall a0 a1 b0 b1 lower upper,
    lower <= a1 - a0 <= upper ->
    lower <= b1 - b0 <= upper ->
    lower <= Z.max a1 b1 - Z.max a0 b0 <= upper.
Proof.
  intros a0 a1 b0 b1 lower upper Ha Hb.
  destruct (Z_le_gt_dec a0 b0);
  destruct (Z_le_gt_dec a1 b1);
  rewrite ?Z.max_l, ?Z.max_r by lia;
  lia.
Qed.

Lemma chain_prefix_increment__cut_exchange :
  forall dist edge,
    0 <= edge ->
    ChainIntervalDistance dist 0 (edge + 1) -
    ChainIntervalDistance dist 0 edge =
    Znth edge dist 0.
Proof.
  intros dist edge Hedge.
  rewrite chain_interval_snoc__cut_exchange by lia.
  ring.
Qed.

Lemma chain_reduction_prefix__cut_exchange :
  forall n initial_dist final_dist,
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge final_dist 0) =
    ChainIntervalDistance initial_dist 0 (n - 1) -
    ChainIntervalDistance final_dist 0 (n - 1).
Proof.
  intros n initial_dist final_dist.
  unfold ChainIntervalDistance.
  rewrite sum_Z_range_sub.
  reflexivity.
Qed.

Lemma chain_feasible_prefix_lattice__cut_exchange :
  forall n budget1 budget2 initial_dist dist1 dist2,
    2 <= n ->
    FeasibleBoostedDistances n budget1 initial_dist dist1 ->
    FeasibleBoostedDistances n budget2 initial_dist dist2 ->
    exists dist_meet dist_join,
      FeasibleBoostedDistances
        n (Z.max budget1 budget2) initial_dist dist_meet /\
      FeasibleBoostedDistances
        n (Z.min budget1 budget2) initial_dist dist_join /\
      ChainPrefixMeetJoin n dist1 dist2 dist_meet dist_join.
Proof.
  intros n budget1 budget2 initial_dist dist1 dist2
    Hn Hfeasible1 Hfeasible2.
  rewrite FeasibleBoostedDistances_unfold in Hfeasible1, Hfeasible2.
  destruct Hfeasible1 as [Hlength1 [Hbounds1 Hbudget1]].
  destruct Hfeasible2 as [Hlength2 [Hbounds2 Hbudget2]].
  set (prefix1 := fun station =>
    ChainIntervalDistance dist1 0 station).
  set (prefix2 := fun station =>
    ChainIntervalDistance dist2 0 station).
  set (prefix_meet := fun station =>
    Z.min (prefix1 station) (prefix2 station)).
  set (prefix_join := fun station =>
    Z.max (prefix1 station) (prefix2 station)).
  assert (Hprefix1_zero : prefix1 0 = 0).
  {
    unfold prefix1.
    apply chain_interval_empty__cut_exchange. lia.
  }
  assert (Hprefix2_zero : prefix2 0 = 0).
  {
    unfold prefix2.
    apply chain_interval_empty__cut_exchange. lia.
  }
  assert (Hmeet_zero : prefix_meet 0 = 0).
  {
    unfold prefix_meet.
    rewrite Hprefix1_zero, Hprefix2_zero.
    reflexivity.
  }
  assert (Hjoin_zero : prefix_join 0 = 0).
  {
    unfold prefix_join.
    rewrite Hprefix1_zero, Hprefix2_zero.
    reflexivity.
  }
  destruct (chain_distance_from_prefix__cut_exchange
    n prefix_meet ltac:(lia) Hmeet_zero) as
    [dist_meet [Hmeet_length [Hmeet_value Hmeet_prefix]]].
  destruct (chain_distance_from_prefix__cut_exchange
    n prefix_join ltac:(lia) Hjoin_zero) as
    [dist_join [Hjoin_length [Hjoin_value Hjoin_prefix]]].
  exists dist_meet, dist_join.
  assert (Hinitial_nonnegative : forall edge,
    0 <= edge < n - 1 -> 0 <= Znth edge initial_dist 0).
  {
    intros edge Hedge.
    specialize (Hbounds1 edge Hedge).
    lia.
  }
  assert (Hmeet_bounds : forall edge,
    0 <= edge < n - 1 ->
    0 <= Znth edge dist_meet 0 <= Znth edge initial_dist 0).
  {
    intros edge Hedge.
    rewrite Hmeet_value by exact Hedge.
    unfold prefix_meet.
    apply Z_min_increment_bounds__cut_exchange.
    - unfold prefix1.
      rewrite chain_prefix_increment__cut_exchange by lia.
      specialize (Hbounds1 edge Hedge). exact Hbounds1.
    - unfold prefix2.
      rewrite chain_prefix_increment__cut_exchange by lia.
      specialize (Hbounds2 edge Hedge). exact Hbounds2.
  }
  assert (Hjoin_bounds : forall edge,
    0 <= edge < n - 1 ->
    0 <= Znth edge dist_join 0 <= Znth edge initial_dist 0).
  {
    intros edge Hedge.
    rewrite Hjoin_value by exact Hedge.
    unfold prefix_join.
    apply Z_max_increment_bounds__cut_exchange.
    - unfold prefix1.
      rewrite chain_prefix_increment__cut_exchange by lia.
      specialize (Hbounds1 edge Hedge). exact Hbounds1.
    - unfold prefix2.
      rewrite chain_prefix_increment__cut_exchange by lia.
      specialize (Hbounds2 edge Hedge). exact Hbounds2.
  }
  assert (Hmeet_budget :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge dist_meet 0) <=
    Z.max budget1 budget2).
  {
    rewrite chain_reduction_prefix__cut_exchange.
    rewrite Hmeet_prefix by lia.
    unfold prefix_meet, prefix1, prefix2.
    rewrite chain_reduction_prefix__cut_exchange in Hbudget1, Hbudget2.
    destruct (Z_le_gt_dec
      (ChainIntervalDistance dist1 0 (n - 1))
      (ChainIntervalDistance dist2 0 (n - 1)));
    destruct (Z_le_gt_dec budget1 budget2);
    rewrite ?Z.min_l, ?Z.min_r, ?Z.max_l, ?Z.max_r by lia;
    lia.
  }
  assert (Hjoin_budget :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge dist_join 0) <=
    Z.min budget1 budget2).
  {
    rewrite chain_reduction_prefix__cut_exchange.
    rewrite Hjoin_prefix by lia.
    unfold prefix_join, prefix1, prefix2.
    rewrite chain_reduction_prefix__cut_exchange in Hbudget1, Hbudget2.
    destruct (Z_le_gt_dec
      (ChainIntervalDistance dist1 0 (n - 1))
      (ChainIntervalDistance dist2 0 (n - 1)));
    destruct (Z_le_gt_dec budget1 budget2);
    rewrite ?Z.min_l, ?Z.min_r, ?Z.max_l, ?Z.max_r by lia;
    lia.
  }
  split.
  - apply FeasibleBoostedDistances_unfold. split; [exact Hmeet_length |].
    split; [exact Hmeet_bounds | exact Hmeet_budget].
  - split.
    + apply FeasibleBoostedDistances_unfold. split; [exact Hjoin_length |].
      split; [exact Hjoin_bounds | exact Hjoin_budget].
    + unfold ChainPrefixMeetJoin.
      intros station Hstation.
      rewrite Hmeet_prefix by exact Hstation.
      rewrite Hjoin_prefix by exact Hstation.
      unfold prefix_meet, prefix_join, prefix1, prefix2.
      tauto.
Qed.

Lemma station_departure_exists__cut_exchange :
  forall arrivals latest station,
    exists departure,
      StationDeparture arrivals latest station departure.
Proof.
  intros arrivals latest station.
  destruct (Z_le_gt_dec
    (Znth station arrivals 0) (Znth station latest 0)).
  - exists (Znth station latest 0).
    unfold StationDeparture,
      MaxMin.max_value_of_subset_with_default.
    left.
    split; [| exact l].
    unfold MaxMin.max_value_of_subset.
    exists (Znth station latest 0).
    split.
    + unfold MaxMin.max_object_of_subset.
      split; [reflexivity |].
      intros candidate Hcandidate.
      change (candidate = Znth station latest 0) in Hcandidate.
      subst candidate. lia.
    + reflexivity.
  - exists (Znth station arrivals 0).
    unfold StationDeparture,
      MaxMin.max_value_of_subset_with_default.
    right.
    split; [| reflexivity].
    intros candidate Hcandidate.
    change (candidate = Znth station latest 0) in Hcandidate.
    subst candidate. lia.
Qed.

Lemma station_departure_arrivals_ext__cut_exchange :
  forall arrivals1 arrivals2 latest station departure,
    Znth station arrivals1 0 = Znth station arrivals2 0 ->
    StationDeparture arrivals1 latest station departure ->
    StationDeparture arrivals2 latest station departure.
Proof.
  intros arrivals1 arrivals2 latest station departure
    Harrival Hdeparture.
  unfold StationDeparture in Hdeparture.
  unfold StationDeparture.
  replace (Znth station arrivals2 0)
    with (Znth station arrivals1 0) by exact Harrival.
  exact Hdeparture.
Qed.

Lemma bus_schedule_exists__cut_exchange :
  forall n dist latest,
    1 <= n ->
    exists arrivals,
      BusArrivalSchedule n dist latest arrivals.
Proof.
  intros n dist latest Hn.
  assert (Hfuel : forall fuel : nat,
    exists arrivals,
      Zlength arrivals = Z.of_nat (S fuel) /\
      Znth 0 arrivals 0 = 0 /\
      forall station,
        0 <= station < Z.of_nat fuel ->
        exists departure,
          StationDeparture arrivals latest station departure /\
          Znth (station + 1) arrivals 0 =
            departure + Znth station dist 0).
  {
    induction fuel as [|fuel IH].
    - exists [0].
      split; [reflexivity |].
      split; [reflexivity |].
      intros station Hstation. lia.
    - destruct IH as [arrivals
        [Hlength [Hzero Hsteps]]].
      destruct (station_departure_exists__cut_exchange
        arrivals latest (Z.of_nat fuel)) as [departure Hdeparture].
      set (next := departure + Znth (Z.of_nat fuel) dist 0).
      exists (arrivals ++ [next]).
      split.
      + rewrite Zlength_app, Zlength_cons, Zlength_nil,
          Nat2Z.inj_succ.
        lia.
      + split.
        * rewrite app_Znth1 by (rewrite Hlength; lia).
          exact Hzero.
        * intros station Hstation.
          rewrite Nat2Z.inj_succ in Hstation.
          destruct (Z_lt_ge_dec station (Z.of_nat fuel)).
          -- specialize (Hsteps station ltac:(lia)).
             destruct Hsteps as [old_departure
               [Hold_departure Hold_next]].
             exists old_departure.
             split.
             ++ eapply station_departure_arrivals_ext__cut_exchange.
                2: exact Hold_departure.
                symmetry.
                rewrite app_Znth1 by (rewrite Hlength; lia).
                reflexivity.
             ++ rewrite app_Znth1 by (rewrite Hlength; lia).
                exact Hold_next.
          -- assert (station = Z.of_nat fuel) by lia.
             subst station.
             exists departure.
             split.
             ++ eapply station_departure_arrivals_ext__cut_exchange.
                2: exact Hdeparture.
                symmetry.
                rewrite app_Znth1 by (rewrite Hlength; lia).
                reflexivity.
             ++ unfold next.
                rewrite app_Znth2 by (rewrite Hlength; lia).
                rewrite Hlength.
                replace
                  (Z.of_nat fuel + 1 - Z.of_nat (S fuel))
                  with 0 by (rewrite Nat2Z.inj_succ; lia).
                reflexivity.
  }
  remember (Z.to_nat (n - 1)) as fuel eqn:Hfuel_eq.
  assert (Hn_eq : n = Z.of_nat (S fuel)).
  { rewrite Nat2Z.inj_succ. lia. }
  destruct (Hfuel fuel) as [arrivals [Hlength [Hzero Hsteps]]].
  exists arrivals.
  unfold BusArrivalSchedule.
  rewrite Hn_eq.
  split; [exact Hlength |].
  split; [exact Hzero |].
  intros station Hstation.
  rewrite Nat2Z.inj_succ in Hstation.
  apply Hsteps. lia.
Qed.

Lemma chain_passenger_total_lattice__cut_exchange :
  forall n m budget1 budget2
         initial_dist times origins destinations latest counts
         dist1 dist2 arrivals1 arrivals2 total1 total2,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    DestinationCounts n m destinations counts ->
    FeasibleBoostedDistances n budget1 initial_dist dist1 ->
    FeasibleBoostedDistances n budget2 initial_dist dist2 ->
    BusArrivalSchedule n dist1 latest arrivals1 ->
    BusArrivalSchedule n dist2 latest arrivals2 ->
    PassengerTravelTotal m times destinations arrivals1 total1 ->
    PassengerTravelTotal m times destinations arrivals2 total2 ->
    exists dist_meet arrivals_meet total_meet
           dist_join arrivals_join total_join,
      FeasibleBoostedDistances
        n (Z.max budget1 budget2) initial_dist dist_meet /\
      BusArrivalSchedule n dist_meet latest arrivals_meet /\
      PassengerTravelTotal
        m times destinations arrivals_meet total_meet /\
      FeasibleBoostedDistances
        n (Z.min budget1 budget2) initial_dist dist_join /\
      BusArrivalSchedule n dist_join latest arrivals_join /\
      PassengerTravelTotal
        m times destinations arrivals_join total_join /\
      ChainPrefixMeetJoin n dist1 dist2 dist_meet dist_join /\
      total_meet + total_join <= total1 + total2.
Proof.
  intros n m budget1 budget2 initial_dist times origins destinations
    latest counts dist1 dist2 arrivals1 arrivals2 total1 total2
    Hinputs Hcounts Hfeasible1 Hfeasible2 Hschedule1 Hschedule2
    Htotal1 Htotal2.
  assert (Hn : 2 <= n).
  { unfold SightseeingInputsBounded in Hinputs. lia. }
  destruct (chain_feasible_prefix_lattice__cut_exchange
    n budget1 budget2 initial_dist dist1 dist2 Hn
    Hfeasible1 Hfeasible2) as
    [dist_meet [dist_join
      [Hfeasible_meet [Hfeasible_join Hmeetjoin]]]].
  destruct (bus_schedule_exists__cut_exchange
    n dist_meet latest ltac:(lia)) as [arrivals_meet Hschedule_meet].
  destruct (bus_schedule_exists__cut_exchange
    n dist_join latest ltac:(lia)) as [arrivals_join Hschedule_join].
  set (total_meet :=
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) arrivals_meet 0 -
           Znth passenger times 0)).
  set (total_join :=
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) arrivals_join 0 -
           Znth passenger times 0)).
  assert (Htotal_meet :
    PassengerTravelTotal
      m times destinations arrivals_meet total_meet).
  { unfold PassengerTravelTotal, total_meet. reflexivity. }
  assert (Htotal_join :
    PassengerTravelTotal
      m times destinations arrivals_join total_join).
  { unfold PassengerTravelTotal, total_join. reflexivity. }
  set (weighted1 :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station arrivals1 0)).
  set (weighted2 :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station arrivals2 0)).
  set (weighted_meet :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station arrivals_meet 0)).
  set (weighted_join :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station arrivals_join 0)).
  assert (Hweighted1 :
    ChainWeightedArrivalTotal n counts arrivals1 weighted1).
  { unfold ChainWeightedArrivalTotal, weighted1. reflexivity. }
  assert (Hweighted2 :
    ChainWeightedArrivalTotal n counts arrivals2 weighted2).
  { unfold ChainWeightedArrivalTotal, weighted2. reflexivity. }
  assert (Hweighted_meet :
    ChainWeightedArrivalTotal n counts arrivals_meet weighted_meet).
  { unfold ChainWeightedArrivalTotal, weighted_meet. reflexivity. }
  assert (Hweighted_join :
    ChainWeightedArrivalTotal n counts arrivals_join weighted_join).
  { unfold ChainWeightedArrivalTotal, weighted_join. reflexivity. }
  pose proof (chain_weighted_arrival_lattice__cut_exchange
    n counts latest dist1 dist2 dist_meet dist_join
    arrivals1 arrivals2 arrivals_meet arrivals_join
    weighted1 weighted2 weighted_meet weighted_join Hn
    (destination_counts_nonnegative__cut_exchange
      n m destinations counts Hcounts)
    Hschedule1 Hschedule2 Hschedule_meet Hschedule_join Hmeetjoin
    Hweighted1 Hweighted2 Hweighted_meet Hweighted_join) as Hweighted_pair.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts arrivals1
    Hinputs Hcounts) as Hidentity1.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts arrivals2
    Hinputs Hcounts) as Hidentity2.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts arrivals_meet
    Hinputs Hcounts) as Hidentity_meet.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts arrivals_join
    Hinputs Hcounts) as Hidentity_join.
  exists dist_meet, arrivals_meet, total_meet,
    dist_join, arrivals_join, total_join.
  split; [exact Hfeasible_meet |].
  split; [exact Hschedule_meet |].
  split; [exact Htotal_meet |].
  split; [exact Hfeasible_join |].
  split; [exact Hschedule_join |].
  split; [exact Htotal_join |].
  split; [exact Hmeetjoin |].
  unfold PassengerTravelTotal in
    Htotal1, Htotal2, Htotal_meet, Htotal_join.
  rewrite sum_Z_range_sub in
    Htotal1, Htotal2, Htotal_meet, Htotal_join.
  subst total1 total2 total_meet total_join.
  unfold weighted1, weighted2, weighted_meet, weighted_join
    in Hweighted_pair.
  rewrite Hidentity1, Hidentity2, Hidentity_meet, Hidentity_join
    in Hweighted_pair.
  nia.
Qed.

Lemma chain_profile_arrival_translate__cut_exchange :
  forall latest station (prefix : Z -> Z) arrival shift,
    ChainProfileArrival latest station prefix arrival ->
    ChainProfileArrival latest station
      (fun s => prefix s + shift) arrival.
Proof.
  intros latest station prefix arrival shift Harrival.
  unfold ChainProfileArrival in Harrival |-.
  destruct Harrival as [[Hzero Hvalue] |
    [Hpositive [envelope [Henvelope Hvalue]]]].
  - left. tauto.
  - right.
    split; [exact Hpositive |].
    exists (envelope - shift).
    split.
    + unfold ChainCutEnvelope in Henvelope |-.
      pose proof (max_default_Z_shift__cut_exchange
        Z (fun cut => 0 <= cut < station)
        (fun cut => Znth cut latest 0 - prefix cut)
        (- prefix 0) envelope (- shift) Henvelope) as Hshift.
      eapply (@max_default_Z_ext__cut_exchange
        Z (fun cut => 0 <= cut < station)
        (fun cut =>
           (Znth cut latest 0 - prefix cut) + - shift)
        (fun cut =>
           Znth cut latest 0 - (prefix cut + shift))
        ((- prefix 0) + - shift)
        (- (prefix 0 + shift))
        (envelope - shift)).
      * ring.
      * intros cut Hcut. ring.
      * replace (envelope + - shift) with (envelope - shift)
          in Hshift by ring.
        exact Hshift.
    + ring_simplify.
      exact Hvalue.
Qed.

Definition ChainUnitCutPath
    (n : Z) (current_dist next_dist : list Z) : Prop :=
  (forall station, 0 <= station <= n - 1 ->
     ChainIntervalDistance next_dist 0 station =
       ChainIntervalDistance current_dist 0 station \/
     ChainIntervalDistance next_dist 0 station =
       ChainIntervalDistance current_dist 0 station - 1) /\
  ChainIntervalDistance next_dist 0 (n - 1) =
    ChainIntervalDistance current_dist 0 (n - 1) - 1.

Lemma chain_unit_cut_path_prefix_bounds__cut_exchange :
  forall n current_dist next_dist,
    ChainUnitCutPath n current_dist next_dist ->
    forall station, 0 <= station <= n - 1 ->
      ChainIntervalDistance current_dist 0 station - 1 <=
        ChainIntervalDistance next_dist 0 station <=
      ChainIntervalDistance current_dist 0 station.
Proof.
  intros n current_dist next_dist Hpath station Hstation.
  unfold ChainUnitCutPath in Hpath.
  destruct Hpath as [Hpointwise Hend].
  specialize (Hpointwise station Hstation).
  destruct Hpointwise; lia.
Qed.

Definition ChainPrefixClamp
    (n : Z)
    (current_dist candidate_dist old_dist next_dist : list Z) : Prop :=
  forall station, 0 <= station <= n - 1 ->
    ChainIntervalDistance old_dist 0 station =
      Z.min
        (ChainIntervalDistance current_dist 0 station)
        (ChainIntervalDistance candidate_dist 0 station + 1) /\
    ChainIntervalDistance next_dist 0 station + 1 =
      Z.max
        (ChainIntervalDistance current_dist 0 station)
        (ChainIntervalDistance candidate_dist 0 station + 1).

Lemma chain_weighted_arrival_clamp__cut_exchange :
  forall n counts latest
         current_dist candidate_dist old_dist next_dist
         current_arrivals candidate_arrivals old_arrivals next_arrivals
         current_weight candidate_weight old_weight next_weight,
    2 <= n ->
    (forall station, 0 <= station < n ->
       0 <= Znth station counts 0) ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    BusArrivalSchedule n candidate_dist latest candidate_arrivals ->
    BusArrivalSchedule n old_dist latest old_arrivals ->
    BusArrivalSchedule n next_dist latest next_arrivals ->
    ChainPrefixClamp
      n current_dist candidate_dist old_dist next_dist ->
    ChainWeightedArrivalTotal
      n counts current_arrivals current_weight ->
    ChainWeightedArrivalTotal
      n counts candidate_arrivals candidate_weight ->
    ChainWeightedArrivalTotal n counts old_arrivals old_weight ->
    ChainWeightedArrivalTotal n counts next_arrivals next_weight ->
    old_weight + next_weight <= current_weight + candidate_weight.
Proof.
  intros n counts latest current_dist candidate_dist old_dist next_dist
    current_arrivals candidate_arrivals old_arrivals next_arrivals
    current_weight candidate_weight old_weight next_weight
    Hn Hcounts Hcurrent_schedule Hcandidate_schedule
    Hold_schedule Hnext_schedule Hclamp
    Hcurrent_weight Hcandidate_weight Hold_weight Hnext_weight.
  unfold ChainWeightedArrivalTotal in
    Hcurrent_weight, Hcandidate_weight, Hold_weight, Hnext_weight.
  subst current_weight candidate_weight old_weight next_weight.
  rewrite <- !sum_Z_range_add.
  apply sum_Z_range_le.
  intros station Hstation.
  assert (Hstation_full : 0 <= station < n) by lia.
  pose proof (bus_schedule_closed_form__cut_exchange
    n current_dist latest current_arrivals Hcurrent_schedule
    station Hstation_full) as Hcurrent_closed.
  pose proof (bus_schedule_closed_form__cut_exchange
    n candidate_dist latest candidate_arrivals Hcandidate_schedule
    station Hstation_full) as Hcandidate_closed.
  pose proof (bus_schedule_closed_form__cut_exchange
    n old_dist latest old_arrivals Hold_schedule
    station Hstation_full) as Hold_closed.
  pose proof (bus_schedule_closed_form__cut_exchange
    n next_dist latest next_arrivals Hnext_schedule
    station Hstation_full) as Hnext_closed.
  pose proof (chain_closed_form_profile__cut_exchange
    current_dist latest station (Znth station current_arrivals 0)
    ltac:(lia) Hcurrent_closed) as Hcurrent_profile.
  pose proof (chain_closed_form_profile__cut_exchange
    candidate_dist latest station (Znth station candidate_arrivals 0)
    ltac:(lia) Hcandidate_closed) as Hcandidate_profile.
  pose proof (chain_closed_form_profile__cut_exchange
    old_dist latest station (Znth station old_arrivals 0)
    ltac:(lia) Hold_closed) as Hold_profile.
  pose proof (chain_closed_form_profile__cut_exchange
    next_dist latest station (Znth station next_arrivals 0)
    ltac:(lia) Hnext_closed) as Hnext_profile.
  pose proof (chain_profile_arrival_translate__cut_exchange
    latest station
    (fun s => ChainIntervalDistance candidate_dist 0 s)
    (Znth station candidate_arrivals 0) 1 Hcandidate_profile)
    as Hcandidate_plus.
  pose proof (chain_profile_arrival_translate__cut_exchange
    latest station
    (fun s => ChainIntervalDistance next_dist 0 s)
    (Znth station next_arrivals 0) 1 Hnext_profile)
    as Hnext_plus.
  assert (Hold_profile' :
    ChainProfileArrival latest station
      (fun s => Z.min
        (ChainIntervalDistance current_dist 0 s)
        (ChainIntervalDistance candidate_dist 0 s + 1))
      (Znth station old_arrivals 0)).
  {
    eapply chain_profile_arrival_prefix_ext__cut_exchange.
    - lia.
    - intros s Hs.
      apply (proj1 (Hclamp s ltac:(lia))).
    - exact Hold_profile.
  }
  assert (Hnext_profile' :
    ChainProfileArrival latest station
      (fun s => Z.max
        (ChainIntervalDistance current_dist 0 s)
        (ChainIntervalDistance candidate_dist 0 s + 1))
      (Znth station next_arrivals 0)).
  {
    eapply chain_profile_arrival_prefix_ext__cut_exchange.
    - lia.
    - intros s Hs.
      apply (proj2 (Hclamp s ltac:(lia))).
    - exact Hnext_plus.
  }
  pose proof (chain_profile_arrival_pair__cut_exchange
    latest station
    (fun s => ChainIntervalDistance current_dist 0 s)
    (fun s => ChainIntervalDistance candidate_dist 0 s + 1)
    (Znth station current_arrivals 0)
    (Znth station candidate_arrivals 0)
    (Znth station old_arrivals 0)
    (Znth station next_arrivals 0)
    ltac:(lia) Hcurrent_profile Hcandidate_plus
    Hold_profile' Hnext_profile') as Harrival_pair.
  specialize (Hcounts station Hstation_full).
  nia.
Qed.

Lemma chain_clamp_distances_exists__cut_exchange :
  forall n budget initial_dist current_dist candidate_dist,
    2 <= n ->
    FeasibleBoostedDistances
      n budget initial_dist current_dist ->
    FeasibleBoostedDistances
      n (budget + 1) initial_dist candidate_dist ->
    (forall station, 0 <= station <= n - 1 ->
       ChainIntervalDistance candidate_dist 0 station <=
       ChainIntervalDistance current_dist 0 station) ->
    ChainIntervalDistance current_dist 0 (n - 1) =
      ChainIntervalDistance candidate_dist 0 (n - 1) + 1 ->
    exists old_dist next_dist,
      FeasibleBoostedDistances n budget initial_dist old_dist /\
      FeasibleBoostedDistances
        n (budget + 1) initial_dist next_dist /\
      ChainPrefixClamp
        n current_dist candidate_dist old_dist next_dist /\
      ChainUnitCutPath n current_dist next_dist.
Proof.
  intros n budget initial_dist current_dist candidate_dist
    Hn Hcurrent_feasible Hcandidate_feasible Hbelow Hendpoint.
  rewrite FeasibleBoostedDistances_unfold in
    Hcurrent_feasible, Hcandidate_feasible.
  destruct Hcurrent_feasible as
    [Hcurrent_length [Hcurrent_bounds Hcurrent_budget]].
  try rewrite FeasibleBoostedDistances_unfold in Hcandidate_feasible.
  destruct Hcandidate_feasible as
    [Hcandidate_length [Hcandidate_bounds Hcandidate_budget]].
  set (current_prefix := fun station =>
    ChainIntervalDistance current_dist 0 station).
  set (candidate_plus := fun station =>
    ChainIntervalDistance candidate_dist 0 station + 1).
  set (old_prefix := fun station =>
    Z.min (current_prefix station) (candidate_plus station)).
  set (next_prefix := fun station =>
    Z.max (current_prefix station) (candidate_plus station) - 1).
  assert (Hcurrent_zero : current_prefix 0 = 0).
  {
    unfold current_prefix.
    apply chain_interval_empty__cut_exchange. lia.
  }
  assert (Hcandidate_plus_zero : candidate_plus 0 = 1).
  {
    unfold candidate_plus.
    rewrite chain_interval_empty__cut_exchange by lia.
    lia.
  }
  assert (Hold_zero : old_prefix 0 = 0).
  {
    unfold old_prefix.
    rewrite Hcurrent_zero, Hcandidate_plus_zero.
    reflexivity.
  }
  assert (Hnext_zero : next_prefix 0 = 0).
  {
    unfold next_prefix.
    rewrite Hcurrent_zero, Hcandidate_plus_zero.
    reflexivity.
  }
  destruct (chain_distance_from_prefix__cut_exchange
    n old_prefix ltac:(lia) Hold_zero) as
    [old_dist [Hold_length [Hold_value Hold_prefix]]].
  destruct (chain_distance_from_prefix__cut_exchange
    n next_prefix ltac:(lia) Hnext_zero) as
    [next_dist [Hnext_length [Hnext_value Hnext_prefix]]].
  exists old_dist, next_dist.
  assert (Hold_bounds : forall edge,
    0 <= edge < n - 1 ->
    0 <= Znth edge old_dist 0 <= Znth edge initial_dist 0).
  {
    intros edge Hedge.
    rewrite Hold_value by exact Hedge.
    unfold old_prefix.
    apply Z_min_increment_bounds__cut_exchange.
    - unfold current_prefix.
      rewrite chain_prefix_increment__cut_exchange by lia.
      apply Hcurrent_bounds. exact Hedge.
    - unfold candidate_plus.
      replace
        (ChainIntervalDistance candidate_dist 0 (edge + 1) + 1 -
         (ChainIntervalDistance candidate_dist 0 edge + 1))
        with
        (ChainIntervalDistance candidate_dist 0 (edge + 1) -
         ChainIntervalDistance candidate_dist 0 edge) by ring.
      rewrite chain_prefix_increment__cut_exchange by lia.
      apply Hcandidate_bounds. exact Hedge.
  }
  assert (Hnext_bounds : forall edge,
    0 <= edge < n - 1 ->
    0 <= Znth edge next_dist 0 <= Znth edge initial_dist 0).
  {
    intros edge Hedge.
    rewrite Hnext_value by exact Hedge.
    unfold next_prefix.
    replace
      (Z.max (current_prefix (edge + 1)) (candidate_plus (edge + 1)) - 1 -
       (Z.max (current_prefix edge) (candidate_plus edge) - 1))
      with
      (Z.max (current_prefix (edge + 1)) (candidate_plus (edge + 1)) -
       Z.max (current_prefix edge) (candidate_plus edge)) by ring.
    apply Z_max_increment_bounds__cut_exchange.
    - unfold current_prefix.
      rewrite chain_prefix_increment__cut_exchange by lia.
      apply Hcurrent_bounds. exact Hedge.
    - unfold candidate_plus.
      replace
        (ChainIntervalDistance candidate_dist 0 (edge + 1) + 1 -
         (ChainIntervalDistance candidate_dist 0 edge + 1))
        with
        (ChainIntervalDistance candidate_dist 0 (edge + 1) -
         ChainIntervalDistance candidate_dist 0 edge) by ring.
      rewrite chain_prefix_increment__cut_exchange by lia.
      apply Hcandidate_bounds. exact Hedge.
  }
  assert (Hold_endpoint : old_prefix (n - 1) = current_prefix (n - 1)).
  {
    unfold old_prefix, current_prefix, candidate_plus.
    rewrite Hendpoint.
    rewrite Z.min_id.
    reflexivity.
  }
  assert (Hnext_endpoint :
    next_prefix (n - 1) = current_prefix (n - 1) - 1).
  {
    unfold next_prefix, current_prefix, candidate_plus.
    rewrite Hendpoint.
    rewrite Z.max_id.
    reflexivity.
  }
  assert (Hold_budget :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge old_dist 0) <= budget).
  {
    rewrite chain_reduction_prefix__cut_exchange.
    rewrite Hold_prefix by lia.
    rewrite Hold_endpoint.
    unfold current_prefix.
    rewrite chain_reduction_prefix__cut_exchange in Hcurrent_budget.
    exact Hcurrent_budget.
  }
  assert (Hnext_budget :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge next_dist 0) <=
    budget + 1).
  {
    rewrite chain_reduction_prefix__cut_exchange.
    rewrite Hnext_prefix by lia.
    rewrite Hnext_endpoint.
    unfold current_prefix.
    rewrite chain_reduction_prefix__cut_exchange in Hcurrent_budget.
    lia.
  }
  split.
  - apply FeasibleBoostedDistances_unfold. split; [exact Hold_length |].
    split; [exact Hold_bounds | exact Hold_budget].
  - split.
    + apply FeasibleBoostedDistances_unfold. split; [exact Hnext_length |].
      split; [exact Hnext_bounds | exact Hnext_budget].
    + split.
      * unfold ChainPrefixClamp.
        intros station Hstation.
        rewrite Hold_prefix by exact Hstation.
        rewrite Hnext_prefix by exact Hstation.
        unfold old_prefix, next_prefix, current_prefix, candidate_plus.
        split; [reflexivity | ring].
      * unfold ChainUnitCutPath.
        split.
        -- intros station Hstation.
           rewrite Hnext_prefix by exact Hstation.
           unfold next_prefix, current_prefix, candidate_plus.
           specialize (Hbelow station Hstation).
           destruct (Z_le_gt_dec
             (ChainIntervalDistance candidate_dist 0 station + 1)
             (ChainIntervalDistance current_dist 0 station)).
           ++ rewrite Z.max_l by lia. right. reflexivity.
           ++ rewrite Z.max_r by lia. left. lia.
        -- rewrite Hnext_prefix by lia.
           exact Hnext_endpoint.
Qed.

Lemma chain_candidate_clamp__cut_exchange :
  forall n m budget initial_dist times origins destinations latest counts
         current_dist current_arrivals current_total
         candidate_dist candidate_arrivals candidate_total,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    DestinationCounts n m destinations counts ->
    FeasibleBoostedDistances
      n budget initial_dist current_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    PassengerTravelTotal
      m times destinations current_arrivals current_total ->
    SightseeingMinimumTotal
      n m budget initial_dist times origins destinations current_total ->
    FeasibleBoostedDistances
      n (budget + 1) initial_dist candidate_dist ->
    BusArrivalSchedule n candidate_dist latest candidate_arrivals ->
    PassengerTravelTotal
      m times destinations candidate_arrivals candidate_total ->
    (forall station, 0 <= station <= n - 1 ->
       ChainIntervalDistance candidate_dist 0 station <=
       ChainIntervalDistance current_dist 0 station) ->
    ChainIntervalDistance current_dist 0 (n - 1) =
      ChainIntervalDistance candidate_dist 0 (n - 1) + 1 ->
    exists next_dist next_arrivals next_total,
      FeasibleBoostedDistances
        n (budget + 1) initial_dist next_dist /\
      BusArrivalSchedule n next_dist latest next_arrivals /\
      PassengerTravelTotal
        m times destinations next_arrivals next_total /\
      ChainUnitCutPath n current_dist next_dist /\
      next_total <= candidate_total.
Proof.
  intros n m budget initial_dist times origins destinations latest counts
    current_dist current_arrivals current_total
    candidate_dist candidate_arrivals candidate_total
    Hinputs Hlatest Hcounts Hcurrent_feasible Hcurrent_schedule
    Hcurrent_total Hminimum Hcandidate_feasible Hcandidate_schedule
    Hcandidate_total Hbelow Hendpoint.
  assert (Hn : 2 <= n).
  { unfold SightseeingInputsBounded in Hinputs. lia. }
  destruct (chain_clamp_distances_exists__cut_exchange
    n budget initial_dist current_dist candidate_dist Hn
    Hcurrent_feasible Hcandidate_feasible Hbelow Hendpoint) as
    [old_dist [next_dist
      [Hold_feasible [Hnext_feasible [Hclamp Hpath]]]]].
  destruct (bus_schedule_exists__cut_exchange
    n old_dist latest ltac:(lia)) as [old_arrivals Hold_schedule].
  destruct (bus_schedule_exists__cut_exchange
    n next_dist latest ltac:(lia)) as [next_arrivals Hnext_schedule].
  set (old_total :=
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) old_arrivals 0 -
           Znth passenger times 0)).
  set (next_total :=
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) next_arrivals 0 -
           Znth passenger times 0)).
  assert (Hold_total :
    PassengerTravelTotal m times destinations old_arrivals old_total).
  { unfold PassengerTravelTotal, old_total. reflexivity. }
  assert (Hnext_total :
    PassengerTravelTotal m times destinations next_arrivals next_total).
  { unfold PassengerTravelTotal, next_total. reflexivity. }
  assert (Hold_candidate :
    SightseeingCandidateTotal
      n m budget initial_dist times origins destinations old_total).
  {
    exists old_dist, latest, old_arrivals.
    exact (conj Hlatest
      (conj Hold_feasible (conj Hold_schedule Hold_total))).
  }
  assert (Hminimum_bound : current_total <= old_total).
  {
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset in Hminimum.
    destruct Hminimum as [witness [[Hwitness Hleast] Hvalue]].
    cbn in Hvalue.
    subst witness.
    specialize (Hleast old_total Hold_candidate).
    cbn in Hleast.
    exact Hleast.
  }
  set (current_weight :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station current_arrivals 0)).
  set (candidate_weight :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station candidate_arrivals 0)).
  set (old_weight :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station old_arrivals 0)).
  set (next_weight :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station next_arrivals 0)).
  assert (Hcurrent_weight :
    ChainWeightedArrivalTotal
      n counts current_arrivals current_weight).
  { unfold ChainWeightedArrivalTotal, current_weight. reflexivity. }
  assert (Hcandidate_weight :
    ChainWeightedArrivalTotal
      n counts candidate_arrivals candidate_weight).
  { unfold ChainWeightedArrivalTotal, candidate_weight. reflexivity. }
  assert (Hold_weight :
    ChainWeightedArrivalTotal n counts old_arrivals old_weight).
  { unfold ChainWeightedArrivalTotal, old_weight. reflexivity. }
  assert (Hnext_weight :
    ChainWeightedArrivalTotal n counts next_arrivals next_weight).
  { unfold ChainWeightedArrivalTotal, next_weight. reflexivity. }
  pose proof (chain_weighted_arrival_clamp__cut_exchange
    n counts latest current_dist candidate_dist old_dist next_dist
    current_arrivals candidate_arrivals old_arrivals next_arrivals
    current_weight candidate_weight old_weight next_weight Hn
    (destination_counts_nonnegative__cut_exchange
      n m destinations counts Hcounts)
    Hcurrent_schedule Hcandidate_schedule Hold_schedule Hnext_schedule
    Hclamp Hcurrent_weight Hcandidate_weight Hold_weight Hnext_weight)
    as Hweighted_pair.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts current_arrivals
    Hinputs Hcounts) as Hidentity_current.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts candidate_arrivals
    Hinputs Hcounts) as Hidentity_candidate.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts old_arrivals
    Hinputs Hcounts) as Hidentity_old.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts next_arrivals
    Hinputs Hcounts) as Hidentity_next.
  assert (Htotal_pair :
    old_total + next_total <= current_total + candidate_total).
  {
    unfold PassengerTravelTotal in
      Hcurrent_total, Hcandidate_total, Hold_total, Hnext_total.
    rewrite sum_Z_range_sub in
      Hcurrent_total, Hcandidate_total, Hold_total, Hnext_total.
    unfold current_weight, candidate_weight, old_weight, next_weight
      in Hweighted_pair.
    rewrite Hidentity_current, Hidentity_candidate,
      Hidentity_old, Hidentity_next in Hweighted_pair.
    lia.
  }
  exists next_dist, next_arrivals, next_total.
  split; [exact Hnext_feasible |].
  split; [exact Hnext_schedule |].
  split; [exact Hnext_total |].
  split; [exact Hpath |].
  lia.
Qed.

Lemma chain_candidate_uncross_to_unit__cut_exchange :
  forall n m budget initial_dist times origins destinations latest counts
         current_dist current_arrivals current_total
         candidate_dist candidate_arrivals candidate_total,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    DestinationCounts n m destinations counts ->
    FeasibleBoostedDistances
      n budget initial_dist current_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    PassengerTravelTotal
      m times destinations current_arrivals current_total ->
    SightseeingMinimumTotal
      n m budget initial_dist times origins destinations current_total ->
    FeasibleBoostedDistances
      n (budget + 1) initial_dist candidate_dist ->
    BusArrivalSchedule n candidate_dist latest candidate_arrivals ->
    PassengerTravelTotal
      m times destinations candidate_arrivals candidate_total ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge current_dist 0) = budget ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge candidate_dist 0) =
      budget + 1 ->
    exists next_dist next_arrivals next_total,
      FeasibleBoostedDistances
        n (budget + 1) initial_dist next_dist /\
      BusArrivalSchedule n next_dist latest next_arrivals /\
      PassengerTravelTotal
        m times destinations next_arrivals next_total /\
      ChainUnitCutPath n current_dist next_dist /\
      next_total <= candidate_total.
Proof.
  intros n m budget initial_dist times origins destinations latest counts
    current_dist current_arrivals current_total
    candidate_dist candidate_arrivals candidate_total
    Hinputs Hlatest Hcounts Hcurrent_feasible Hcurrent_schedule
    Hcurrent_total Hminimum Hcandidate_feasible Hcandidate_schedule
    Hcandidate_total Hcurrent_used Hcandidate_used.
  assert (Hn : 2 <= n).
  { unfold SightseeingInputsBounded in Hinputs. lia. }
  destruct (chain_passenger_total_lattice__cut_exchange
    n m budget (budget + 1)
    initial_dist times origins destinations latest counts
    current_dist candidate_dist current_arrivals candidate_arrivals
    current_total candidate_total Hinputs Hcounts
    Hcurrent_feasible Hcandidate_feasible
    Hcurrent_schedule Hcandidate_schedule
    Hcurrent_total Hcandidate_total) as
    [meet_dist [meet_arrivals [meet_total
      [join_dist [join_arrivals [join_total
        [Hmeet_feasible [Hmeet_schedule [Hmeet_total
          [Hjoin_feasible [Hjoin_schedule [Hjoin_total
            [Hmeetjoin Htotal_pair]]]]]]]]]]]]].
  replace (Z.max budget (budget + 1)) with (budget + 1)
    in Hmeet_feasible by (rewrite Z.max_r; lia).
  replace (Z.min budget (budget + 1)) with budget
    in Hjoin_feasible by (rewrite Z.min_l; lia).
  assert (Hjoin_candidate :
    SightseeingCandidateTotal
      n m budget initial_dist times origins destinations join_total).
  {
    exists join_dist, latest, join_arrivals.
    exact (conj Hlatest
      (conj Hjoin_feasible (conj Hjoin_schedule Hjoin_total))).
  }
  assert (Hjoin_lower : current_total <= join_total).
  {
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset in Hminimum.
    destruct Hminimum as [witness [[Hwitness Hleast] Hvalue]].
    cbn in Hvalue.
    subst witness.
    specialize (Hleast join_total Hjoin_candidate).
    cbn in Hleast. exact Hleast.
  }
  assert (Hmeet_upper : meet_total <= candidate_total) by lia.
  assert (Hmeet_below : forall station, 0 <= station <= n - 1 ->
    ChainIntervalDistance meet_dist 0 station <=
    ChainIntervalDistance current_dist 0 station).
  {
    intros station Hstation.
    pose proof (proj1 (Hmeetjoin station Hstation)) as Hmeet_prefix.
    rewrite Hmeet_prefix.
    apply Z.le_min_l.
  }
  assert (Hcurrent_endpoint :
    ChainIntervalDistance initial_dist 0 (n - 1) -
    ChainIntervalDistance current_dist 0 (n - 1) = budget).
  {
    rewrite <- chain_reduction_prefix__cut_exchange.
    exact Hcurrent_used.
  }
  assert (Hcandidate_endpoint :
    ChainIntervalDistance initial_dist 0 (n - 1) -
    ChainIntervalDistance candidate_dist 0 (n - 1) = budget + 1).
  {
    rewrite <- chain_reduction_prefix__cut_exchange.
    exact Hcandidate_used.
  }
  assert (Hmeet_endpoint :
    ChainIntervalDistance current_dist 0 (n - 1) =
    ChainIntervalDistance meet_dist 0 (n - 1) + 1).
  {
    assert (Hlast_range : 0 <= n - 1 <= n - 1) by lia.
    pose proof (proj1 (Hmeetjoin (n - 1) Hlast_range))
      as Hmeet_prefix.
    rewrite Hmeet_prefix.
    destruct (Z_le_gt_dec
      (ChainIntervalDistance current_dist 0 (n - 1))
      (ChainIntervalDistance candidate_dist 0 (n - 1))).
    - rewrite Z.min_l by lia. lia.
    - rewrite Z.min_r by lia. lia.
  }
  destruct (chain_candidate_clamp__cut_exchange
    n m budget initial_dist times origins destinations latest counts
    current_dist current_arrivals current_total
    meet_dist meet_arrivals meet_total
    Hinputs Hlatest Hcounts Hcurrent_feasible Hcurrent_schedule
    Hcurrent_total Hminimum Hmeet_feasible Hmeet_schedule Hmeet_total
    Hmeet_below Hmeet_endpoint) as
    [next_dist [next_arrivals [next_total
      [Hnext_feasible [Hnext_schedule [Hnext_total [Hpath Hnext_upper]]]]]]].
  exists next_dist, next_arrivals, next_total.
  split; [exact Hnext_feasible |].
  split; [exact Hnext_schedule |].
  split; [exact Hnext_total |].
  split; [exact Hpath |].
  lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Positive marginal and budget-saturation bridges. *)

Lemma best_boost_choice_positive_edge__saturation :
  forall n dist counts latest arrivals best position,
    0 < best ->
    BestBoostChoice n dist counts latest arrivals best position ->
    0 <= position < n - 1 /\ 0 < Znth position dist 0.
Proof.
  intros n dist counts latest arrivals best position Hbest Hchoice.
  unfold BestBoostChoice, EdgeChoicePrefix in Hchoice.
  destruct Hchoice as [Hmaximum Hposition].
  destruct Hposition as [[Hbest_zero Hposition] | Heligible].
  - lia.
  - unfold EligibleEdgeBenefit in Heligible.
    cbn in Heligible.
    tauto.
Qed.

Lemma station_departure_by_cases__saturation :
  forall arrivals latest station,
    (Znth station arrivals 0 <= Znth station latest 0 ->
       StationDeparture arrivals latest station (Znth station latest 0)) /\
    (Znth station latest 0 <= Znth station arrivals 0 ->
       StationDeparture arrivals latest station (Znth station arrivals 0)).
Proof.
  intros arrivals latest station.
  unfold StationDeparture.
  split; intro Horder.
  - unfold MaxMin.max_value_of_subset_with_default.
    left; split; [| exact Horder].
    unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
    exists (Znth station latest 0).
    split.
    + split; [reflexivity |].
      intros candidate Hcandidate.
      change (candidate = Znth station latest 0) in Hcandidate.
      subst candidate.
      reflexivity.
    + reflexivity.
  - unfold MaxMin.max_value_of_subset_with_default.
    right; split; [| reflexivity].
    intros candidate Hcandidate.
    change (candidate = Znth station latest 0) in Hcandidate.
    subst candidate.
    exact Horder.
Qed.

Lemma station_departure_unique__saturation :
  forall arrivals latest station departure1 departure2,
    StationDeparture arrivals latest station departure1 ->
    StationDeparture arrivals latest station departure2 ->
    departure1 = departure2.
Proof.
  intros arrivals latest station departure1 departure2
    Hdeparture1 Hdeparture2.
  unfold StationDeparture in Hdeparture1, Hdeparture2.
  eapply (@MaxMin.max_default_unique
    Z Z.le Zle_TotalOrder Z
    (fun candidate => candidate)
    (fun candidate => candidate = Znth station latest 0)
    (Znth station arrivals 0)); eauto.
Qed.

Lemma arrival_repair_outcome_schedule__saturation :
  forall n old_dist old_arrivals new_dist new_arrivals latest counts best position,
    Zlength new_dist = n - 1 ->
    Zlength new_arrivals = n ->
    0 < best ->
    BestBoostChoice n old_dist counts latest old_arrivals best position ->
    BusArrivalSchedule n old_dist latest old_arrivals ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    BusArrivalSchedule n new_dist latest new_arrivals.
Proof.
  intros n old_dist old_arrivals new_dist new_arrivals latest counts
    best position Hnew_dist_len Hnew_arrivals_len Hbest Hchoice
    Hschedule Houtcome.
  pose proof (best_boost_choice_positive_edge__saturation
    n old_dist counts latest old_arrivals best position Hbest Hchoice)
    as [Hposition_range Hposition_positive].
  destruct Hschedule as [Hold_arrivals_len [Hold_zero Hold_step]].
  rewrite ArrivalRepairOutcome_unfold in Houtcome.
  destruct Houtcome as
    [stop [Hstop [Hdistance [Hbefore [Hchanged Hfinish]]]]].
  unfold BusArrivalSchedule.
  split; [exact Hnew_arrivals_len |].
  split.
  - rewrite Hbefore by lia.
    exact Hold_zero.
  - intros station Hstation.
    specialize (Hold_step station Hstation).
    destruct Hold_step as [old_departure [Hold_departure Hold_next]].
    specialize (Hdistance station Hstation).
    destruct (Z.lt_trichotomy station position) as
      [Hstation_before | [Hstation_eq | Hstation_after]].
    + assert (Hcurrent_eq :
        Znth station new_arrivals 0 = Znth station old_arrivals 0)
        by (apply Hbefore; lia).
      assert (Hnext_eq :
        Znth (station + 1) new_arrivals 0 =
        Znth (station + 1) old_arrivals 0)
        by (apply Hbefore; lia).
      assert (Hdist_eq :
        Znth station new_dist 0 = Znth station old_dist 0).
      {
        destruct (Z.eq_dec station position); [lia | exact Hdistance].
      }
      exists old_departure.
      split.
      * unfold StationDeparture in *.
        rewrite Hcurrent_eq.
        exact Hold_departure.
      * lia.
    + subst station.
      assert (Hcurrent_eq :
        Znth position new_arrivals 0 = Znth position old_arrivals 0)
        by (apply Hbefore; lia).
      assert (Hnext_eq :
        Znth (position + 1) new_arrivals 0 =
        Znth (position + 1) old_arrivals 0 - 1).
      {
        destruct (Z_lt_ge_dec (position + 1) stop) as [Hlt | Hge].
        - exact (proj1 (Hchanged (position + 1) ltac:(lia))).
        - assert (Hstop_eq : stop = position + 1) by lia.
          subst stop.
          destruct Hfinish as [[Hstop_n Hall_changed] |
            [Hstop_lt [Hstop_changed [Hguard Hafter]]]].
          + apply Hall_changed; lia.
          + exact Hstop_changed.
      }
      assert (Hdist_eq :
        Znth position new_dist 0 = Znth position old_dist 0 - 1).
      {
        destruct (Z.eq_dec position position) as [_ | Hcontra];
          [exact Hdistance | contradiction].
      }
      exists old_departure.
      split.
      * unfold StationDeparture in *.
        rewrite Hcurrent_eq.
        exact Hold_departure.
      * lia.
    + destruct (Z_lt_ge_dec station stop) as
        [Hstation_changed | Hstation_ge].
      * pose proof (Hchanged station ltac:(lia))
          as [Hcurrent_eq Hcurrent_latest].
        assert (Hold_current_latest :
          Znth station latest 0 <= Znth station old_arrivals 0) by lia.
        pose proof (proj2
          (station_departure_by_cases__saturation
            old_arrivals latest station) Hold_current_latest)
          as Hold_canonical.
        pose proof (station_departure_unique__saturation
          old_arrivals latest station old_departure
          (Znth station old_arrivals 0)
          Hold_departure Hold_canonical) as Hold_departure_eq.
        assert (Hnew_departure :
          StationDeparture new_arrivals latest station
            (Znth station new_arrivals 0)).
        {
          apply (proj2
            (station_departure_by_cases__saturation
              new_arrivals latest station)).
          exact Hcurrent_latest.
        }
        assert (Hnext_eq :
          Znth (station + 1) new_arrivals 0 =
          Znth (station + 1) old_arrivals 0 - 1).
        {
          destruct (Z_lt_ge_dec (station + 1) stop) as [Hnext_lt | Hnext_ge].
          - exact (proj1 (Hchanged (station + 1) ltac:(lia))).
          - assert (Hnext_eq_stop : station + 1 = stop) by lia.
            subst stop.
            destruct Hfinish as [[Hstop_n Hall_changed] |
              [Hstop_lt [Hstop_changed [Hguard Hafter]]]].
            + apply Hall_changed; lia.
            + exact Hstop_changed.
        }
        assert (Hdist_eq :
          Znth station new_dist 0 = Znth station old_dist 0).
        {
          destruct (Z.eq_dec station position); [lia | exact Hdistance].
        }
        exists (Znth station new_arrivals 0).
        split; [exact Hnew_departure |].
        lia.
      * destruct Hfinish as [[Hstop_n Hall_changed] |
          [Hstop_lt [Hstop_changed [Hguard Hafter]]]].
        -- lia.
        -- destruct (Z.eq_dec station stop) as
             [Hstation_eq_stop | Hstation_gt].
           ++ subst station.
              assert (Hold_current_latest :
                Znth stop old_arrivals 0 <= Znth stop latest 0) by lia.
              pose proof (proj1
                (station_departure_by_cases__saturation
                  old_arrivals latest stop) Hold_current_latest)
                as Hold_canonical.
              pose proof (station_departure_unique__saturation
                old_arrivals latest stop old_departure
                (Znth stop latest 0)
                Hold_departure Hold_canonical) as Hold_departure_eq.
              assert (Hnew_departure :
                StationDeparture new_arrivals latest stop
                  (Znth stop latest 0)).
              {
                apply (proj1
                  (station_departure_by_cases__saturation
                    new_arrivals latest stop)).
                lia.
              }
              assert (Hnext_eq :
                Znth (stop + 1) new_arrivals 0 =
                Znth (stop + 1) old_arrivals 0)
                by (apply Hafter; lia).
              assert (Hdist_eq :
                Znth stop new_dist 0 = Znth stop old_dist 0).
              {
                destruct (Z.eq_dec stop position); [lia | exact Hdistance].
              }
              exists (Znth stop latest 0).
              split; [exact Hnew_departure |].
              lia.
           ++ assert (Hstation_gt_stop : stop < station) by lia.
              assert (Hcurrent_eq :
                Znth station new_arrivals 0 =
                Znth station old_arrivals 0)
                by (apply Hafter; lia).
              assert (Hnext_eq :
                Znth (station + 1) new_arrivals 0 =
                Znth (station + 1) old_arrivals 0)
                by (apply Hafter; lia).
              assert (Hdist_eq :
                Znth station new_dist 0 = Znth station old_dist 0).
              {
                destruct (Z.eq_dec station position); [lia | exact Hdistance].
              }
              exists old_departure.
              split.
              ** unfold StationDeparture in *.
                 rewrite Hcurrent_eq.
                 exact Hold_departure.
              ** lia.
Qed.

Lemma sum_Z_range_single_indicator__saturation :
  forall low high position,
    low <= position < high ->
    sum (fun edge => low <= edge < high)
        (fun edge => if Z.eq_dec edge position then 1 else 0) = 1.
Proof.
  intros low high position Hposition.
  rewrite (sum_Z_range_split low position high) by lia.
  assert (Hleft :
    sum (fun edge => low <= edge < position)
        (fun edge => if Z.eq_dec edge position then 1 else 0) = 0).
  {
    apply sum_Z_range_eq_zero.
    intros edge Hedge.
    destruct (Z.eq_dec edge position); [lia | reflexivity].
  }
  rewrite Hleft.
  rewrite sum_Z_range_cons by lia.
  assert (Hright :
    sum (fun edge => position + 1 <= edge < high)
        (fun edge => if Z.eq_dec edge position then 1 else 0) = 0).
  {
    apply sum_Z_range_eq_zero.
    intros edge Hedge.
    destruct (Z.eq_dec edge position); [lia | reflexivity].
  }
  rewrite Hright.
  destruct (Z.eq_dec position position); [lia | contradiction].
Qed.

Lemma arrival_repair_used_step__saturation :
  forall n initial_dist old_dist old_arrivals
         new_dist new_arrivals latest counts best position,
    0 < best ->
    BestBoostChoice n old_dist counts latest old_arrivals best position ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge => Znth edge initial_dist 0 - Znth edge new_dist 0) =
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge => Znth edge initial_dist 0 - Znth edge old_dist 0) + 1.
Proof.
  intros n initial_dist old_dist old_arrivals new_dist new_arrivals
    latest counts best position Hbest Hchoice Houtcome.
  pose proof (best_boost_choice_positive_edge__saturation
    n old_dist counts latest old_arrivals best position Hbest Hchoice)
    as [Hposition_range Hposition_positive].
  rewrite ArrivalRepairOutcome_unfold in Houtcome.
  destruct Houtcome as
    [stop [Hstop [Hdistance [Hbefore [Hchanged Hfinish]]]]].
  rewrite (sum_Z_range_ext 0 (n - 1)
    (fun edge => Znth edge initial_dist 0 - Znth edge new_dist 0)
    (fun edge =>
       (Znth edge initial_dist 0 - Znth edge old_dist 0) +
       (if Z.eq_dec edge position then 1 else 0))).
  2: {
    intros edge Hedge.
    specialize (Hdistance edge Hedge).
    destruct (Z.eq_dec edge position) as [Heq | Hne].
    - subst edge.
      destruct (Z.eq_dec position position) as [_ | Hcontra];
        [lia | contradiction].
    - destruct (Z.eq_dec edge position) as [Hcontra | _];
        [contradiction | lia].
  }
  rewrite sum_Z_range_add.
  rewrite sum_Z_range_single_indicator__saturation by lia.
  reflexivity.
Qed.

Lemma arrival_repair_effect_interval__saturation :
  forall n old_dist old_arrivals new_dist new_arrivals latest counts
         best position,
    0 < best ->
    BestBoostChoice n old_dist counts latest old_arrivals best position ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    exists high,
      position + 1 <= high <= n /\
      best = sum (fun station => position + 1 <= station < high)
                 (fun station => Znth station counts 0) /\
      (forall station, 0 <= station < n ->
         position < station < high ->
         Znth station new_arrivals 0 =
           Znth station old_arrivals 0 - 1) /\
      (forall station, 0 <= station < n ->
         ~ (position < station < high) ->
         Znth station new_arrivals 0 =
           Znth station old_arrivals 0).
Proof.
  intros n old_dist old_arrivals new_dist new_arrivals latest counts
    best position Hbest Hchoice Houtcome.
  unfold BestBoostChoice, EdgeChoicePrefix in Hchoice.
  destruct Hchoice as [Hmaximum Hposition].
  destruct Hposition as [[Hbest_zero Hposition_default] | Heligible];
    [lia |].
  unfold EligibleEdgeBenefit in Heligible.
  cbn in Heligible.
  destruct Heligible as
    [Hposition_scanned
      [Hposition_bound [Hposition_dist Hedge_benefit]]].
  rewrite EdgeMarginalBenefit_unfold in Hedge_benefit.
  destruct Hedge_benefit as
    [benefit_stop [Hbenefit_stop [Hbenefit_strict
      [Hbenefit_finish Hbenefit_value]]]].
  rewrite ArrivalRepairOutcome_unfold in Houtcome.
  destruct Houtcome as
    [repair_stop [Hrepair_stop [Hdistance
      [Hbefore [Hchanged Hrepair_finish]]]]].
  assert (Hstop_relation :
    (benefit_stop = n /\
       (repair_stop = n \/ repair_stop = n - 1)) \/
    (benefit_stop < n /\ repair_stop = benefit_stop - 1)).
  {
    destruct (Z.eq_dec benefit_stop n) as [Hbenefit_n | Hbenefit_not_n].
    - left.
      split; [exact Hbenefit_n |].
      subst benefit_stop.
      assert (Hrepair_lower : n - 1 <= repair_stop).
      {
        destruct (Z_lt_ge_dec repair_stop (n - 1)) as [Hlt | Hge];
          [| lia].
        assert (Hstrict_old :
          Znth repair_stop latest 0 <
          Znth repair_stop old_arrivals 0).
        { apply Hbenefit_strict; lia. }
        destruct Hrepair_finish as [[Hrepair_n Hall_changed] |
          [Hrepair_lt [Hrepair_changed [Hguard Hafter]]]];
          lia.
      }
      lia.
    - right.
      assert (Hbenefit_lt : benefit_stop < n) by lia.
      split; [exact Hbenefit_lt |].
      destruct (Z.lt_trichotomy repair_stop (benefit_stop - 1)) as
        [Hrepair_early | [Hrepair_eq | Hrepair_late]].
      + assert (Hstrict_old :
          Znth repair_stop latest 0 <
          Znth repair_stop old_arrivals 0).
        { apply Hbenefit_strict; lia. }
        destruct Hrepair_finish as [[Hrepair_n Hall_changed] |
          [Hrepair_lt [Hrepair_changed [Hguard Hafter]]]];
          lia.
      + exact Hrepair_eq.
      + destruct Hbenefit_finish as [Hbenefit_n | Hbenefit_blocked];
          [contradiction |].
        pose proof (Hchanged (benefit_stop - 1) ltac:(lia))
          as [Hchanged_value Hchanged_latest].
        lia.
  }
  exists benefit_stop.
  split; [lia |].
  split; [exact Hbenefit_value |].
  split.
  - intros station Hstation Haffected.
    destruct Hstop_relation as
      [[Hbenefit_n [Hrepair_n | Hrepair_last]] |
       [Hbenefit_lt Hrepair_eq]].
    + subst benefit_stop repair_stop.
      exact (proj1 (Hchanged station ltac:(lia))).
    + subst benefit_stop repair_stop.
      destruct (Z.eq_dec station (n - 1)) as [-> | Hneq].
      * destruct Hrepair_finish as [[Hcontra Hall_changed] |
          [Hrepair_lt [Hrepair_changed [Hguard Hafter]]]];
          [lia | exact Hrepair_changed].
      * exact (proj1 (Hchanged station ltac:(lia))).
    + subst repair_stop.
      destruct (Z.eq_dec station (benefit_stop - 1)) as [-> | Hneq].
      * destruct Hrepair_finish as [[Hcontra Hall_changed] |
          [Hrepair_lt [Hrepair_changed [Hguard Hafter]]]];
          [lia | exact Hrepair_changed].
      * exact (proj1 (Hchanged station ltac:(lia))).
  - intros station Hstation Hnot_affected.
    destruct (Z_le_gt_dec station position) as
      [Hbefore_position | Hafter_position].
    + apply Hbefore; lia.
    + assert (Hstation_high : benefit_stop <= station) by lia.
      destruct Hstop_relation as
        [[Hbenefit_n [Hrepair_n | Hrepair_last]] |
         [Hbenefit_lt Hrepair_eq]].
      * lia.
      * lia.
      * subst repair_stop.
        destruct Hrepair_finish as [[Hcontra Hall_changed] |
          [Hrepair_lt [Hrepair_changed [Hguard Hafter]]]];
          [lia |].
        apply Hafter; lia.
Qed.

Lemma destination_indicator_interval_value__saturation :
  forall low high destination,
    low <= high ->
    sum (fun station => low <= station < high)
        (fun station =>
           if prop_dec (destination = station + 1) then 1 else 0) =
    (if prop_dec (low <= destination - 1 < high) then 1 else 0).
Proof.
  intros low high destination Hrange.
  destruct (prop_dec (low <= destination - 1 < high)) as
    [Hinside | Houtside].
  - rewrite (sum_Z_range_split low (destination - 1) high) by lia.
    assert (Hleft :
      sum (fun station => low <= station < destination - 1)
          (fun station =>
             if prop_dec (destination = station + 1) then 1 else 0) = 0).
    {
      apply sum_Z_range_eq_zero.
      intros station Hstation.
      destruct (prop_dec (destination = station + 1)); [lia | reflexivity].
    }
    rewrite Hleft.
    rewrite sum_Z_range_cons by lia.
    assert (Hright :
      sum (fun station => destination - 1 + 1 <= station < high)
          (fun station =>
             if prop_dec (destination = station + 1) then 1 else 0) = 0).
    {
      apply sum_Z_range_eq_zero.
      intros station Hstation.
      destruct (prop_dec (destination = station + 1)); [lia | reflexivity].
    }
    rewrite Hright.
    destruct (prop_dec (destination = destination - 1 + 1));
      [reflexivity | lia].
  - rewrite sum_Z_range_eq_zero.
    + reflexivity.
    + intros station Hstation.
      destruct (prop_dec (destination = station + 1));
        [exfalso; apply Houtside; lia | reflexivity].
Qed.

Lemma destination_counts_interval_as_passengers__saturation :
  forall n m destinations counts low high,
    0 <= low -> low <= high -> high <= n ->
    DestinationCounts n m destinations counts ->
    sum (fun station => low <= station < high)
        (fun station => Znth station counts 0) =
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           if prop_dec
             (low <= Znth passenger destinations 0 - 1 < high)
           then 1 else 0).
Proof.
  intros n m destinations counts low high Hlow Hlowhigh Hhigh Hcounts.
  unfold DestinationCounts in Hcounts.
  destruct Hcounts as [Hcounts_len Hcounts].
  rewrite (sum_Z_range_ext low high
    (fun station => Znth station counts 0)
    (fun station =>
       sum (fun passenger => 0 <= passenger < m)
           (fun passenger =>
              if prop_dec
                (Znth passenger destinations 0 = station + 1)
              then 1 else 0))).
  2: {
    intros station Hstation.
    rewrite Hcounts by lia.
    rewrite sum_Z_range_filter_indicator__chain_dual.
    apply sum_Z_range_ext.
    intros passenger Hpassenger.
    destruct (prop_dec
      (Znth passenger destinations 0 = station + 1)); reflexivity.
  }
  rewrite sum_Z_range_nested_swap__chain_dual.
  apply sum_Z_range_ext.
  intros passenger Hpassenger.
  apply destination_indicator_interval_value__saturation.
  lia.
Qed.

Lemma passenger_travel_total_after_repair__saturation :
  forall n m initial_dist times origins destinations old_dist old_arrivals
         new_dist new_arrivals latest counts best position old_total,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    DestinationCounts n m destinations counts ->
    0 < best ->
    BestBoostChoice n old_dist counts latest old_arrivals best position ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    PassengerTravelTotal m times destinations old_arrivals old_total ->
    PassengerTravelTotal
      m times destinations new_arrivals (old_total - best).
Proof.
  intros n m initial_dist times origins destinations old_dist old_arrivals
    new_dist new_arrivals latest counts best position old_total
    Hinputs Hcounts Hbest Hchoice Houtcome Hold_total.
  pose proof (arrival_repair_effect_interval__saturation
    n old_dist old_arrivals new_dist new_arrivals latest counts
    best position Hbest Hchoice Houtcome)
    as [high [Hhigh [Hbest_value [Hchanged Hunchanged]]]].
  pose proof (best_boost_choice_positive_edge__saturation
    n old_dist counts latest old_arrivals best position Hbest Hchoice)
    as [Hposition_range Hposition_positive].
  pose proof Hinputs as Hinput_bounds.
  unfold SightseeingInputsBounded in Hinput_bounds.
  destruct Hinput_bounds as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist_bounds Hpassenger_bounds]]]]]]].
  unfold PassengerTravelTotal in Hold_total |-.
  transitivity
    (sum (fun passenger => 0 <= passenger < m)
       (fun passenger =>
          (Znth (Znth passenger destinations 0 - 1) old_arrivals 0 -
           Znth passenger times 0) -
          (if prop_dec
             (position + 1 <= Znth passenger destinations 0 - 1 < high)
           then 1 else 0))).
  - rewrite sum_sub.
    rewrite <- Hold_total.
    rewrite <- (destination_counts_interval_as_passengers__saturation
      n m destinations counts (position + 1) high)
      by (try lia; exact Hcounts).
    rewrite <- Hbest_value.
    reflexivity.
  - symmetry.
    apply sum_ext.
    intros passenger Hpassenger.
    specialize (Hpassenger_bounds passenger Hpassenger).
    destruct Hpassenger_bounds as
      [Htime [[Horigin_lower Horigin_destination] Hdestination_upper]].
    destruct (prop_dec
      (position + 1 <= Znth passenger destinations 0 - 1 < high))
      as [Haffected | Hnot_affected].
    + rewrite Hchanged by lia.
      lia.
    + rewrite Hunchanged by lia.
      lia.
Qed.

Lemma booster_progress_budget_saturated__saturation :
  forall n m budget remaining initial_dist times origins destinations
         old_dist latest counts old_arrivals
         new_dist new_arrivals best position,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    BoosterProgress n m budget remaining
      initial_dist times origins destinations
      old_dist latest counts old_arrivals ->
    0 < best ->
    BestBoostChoice n old_dist counts latest old_arrivals best position ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    Zlength new_dist = n - 1 ->
    Zlength new_arrivals = n ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge old_dist 0) =
      budget - remaining.
Proof.
  intros n m budget remaining initial_dist times origins destinations
    old_dist latest counts old_arrivals new_dist new_arrivals best position
    Hinputs Hprogress Hbest Hchoice Houtcome
    Hnew_dist_length Hnew_arrivals_length.
  pose proof Hprogress as Hfields.
  unfold BoosterProgress in Hfields.
  destruct Hfields as
    [Hlatest [Hcounts [Hfeasible [Hschedule
      [old_total [Hold_total Hminimum]]]]]].
  rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  destruct Hfeasible as
    [Hold_dist_length [Hold_bounds Hold_budget]].
  set (used :=
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge old_dist 0)).
  assert (Hused_le : used <= budget - remaining).
  { unfold used. exact Hold_budget. }
  destruct (Z.eq_dec used (budget - remaining)) as [Heq | Hneq].
  - exact Heq.
  - assert (Hused_lt : used < budget - remaining) by lia.
    pose proof (best_boost_choice_positive_edge__saturation
      n old_dist counts latest old_arrivals best position Hbest Hchoice)
      as [Hposition_range Hposition_positive].
    rewrite ArrivalRepairOutcome_unfold in Houtcome.
    destruct Houtcome as
      [stop [Hstop [Hdistance [Hbefore [Hchanged Hfinish]]]]].
    assert (Hnew_bounds : forall edge, 0 <= edge < n - 1 ->
      0 <= Znth edge new_dist 0 <= Znth edge initial_dist 0).
    {
      intros edge Hedge.
      specialize (Hold_bounds edge Hedge).
      specialize (Hdistance edge Hedge).
      destruct (Z.eq_dec edge position) as [Heq_edge | Hne_edge].
      - subst edge.
        destruct (Z.eq_dec position position) as [_ | Hcontra];
          [lia | contradiction].
      - destruct (Z.eq_dec edge position) as [Hcontra | _];
          [contradiction | lia].
    }
    assert (Hused_step :
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 - Znth edge new_dist 0) = used + 1).
    {
      unfold used.
      apply arrival_repair_used_step__saturation
        with (old_arrivals := old_arrivals)
             (new_arrivals := new_arrivals)
             (latest := latest) (counts := counts)
             (best := best) (position := position);
        try assumption.
      rewrite ArrivalRepairOutcome_unfold.
      exists stop. tauto.
    }
    assert (Hnew_feasible :
      FeasibleBoostedDistances
        n (budget - remaining) initial_dist new_dist).
    {
      rewrite FeasibleBoostedDistances_unfold.
      split; [exact Hnew_dist_length |].
      split; [exact Hnew_bounds |].
      rewrite Hused_step.
      lia.
    }
    assert (Houtcome_rebuilt :
      ArrivalRepairOutcome
        n old_dist old_arrivals new_dist new_arrivals latest position).
    {
      rewrite ArrivalRepairOutcome_unfold.
      exists stop. tauto.
    }
    pose proof (arrival_repair_outcome_schedule__saturation
      n old_dist old_arrivals new_dist new_arrivals latest counts
      best position Hnew_dist_length Hnew_arrivals_length Hbest Hchoice
      Hschedule Houtcome_rebuilt) as Hnew_schedule.
    pose proof (passenger_travel_total_after_repair__saturation
      n m initial_dist times origins destinations old_dist old_arrivals
      new_dist new_arrivals latest counts best position old_total
      Hinputs Hcounts Hbest Hchoice Houtcome_rebuilt Hold_total)
      as Hnew_total.
    assert (Hnew_candidate :
      SightseeingCandidateTotal
        n m (budget - remaining)
        initial_dist times origins destinations (old_total - best)).
    {
      exists new_dist, latest, new_arrivals.
      exact (conj Hlatest
        (conj Hnew_feasible (conj Hnew_schedule Hnew_total))).
    }
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset in Hminimum.
    destruct Hminimum as [witness [[Hwitness Hleast] Hvalue]].
    cbn in Hvalue.
    subst witness.
    specialize (Hleast (old_total - best) Hnew_candidate).
    cbn in Hleast.
    lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Boolean record-cut effect exposed by a [ChainUnitCutPath]. *)

Lemma max_default_Z_unit_band__record_cut :
  forall (A : Type) (P : A -> Prop) (f1 f2 : A -> Z)
         default1 default2 maximum1 maximum2,
    max_value_of_subset_with_default
      Z.le P f1 default1 maximum1 ->
    max_value_of_subset_with_default
      Z.le P f2 default2 maximum2 ->
    default1 <= default2 <= default1 + 1 ->
    (forall x, P x -> f1 x <= f2 x <= f1 x + 1) ->
    maximum1 <= maximum2 <= maximum1 + 1.
Proof.
  intros A P f1 f2 default1 default2 maximum1 maximum2
    Hmaximum1 Hmaximum2 Hdefault Hpointwise.
  pose proof (max_default_Z_bounds_source__cut_exchange
    A P f1 default1 maximum1 Hmaximum1)
    as [Hdefault1 [Hbound1 Hsource1]].
  pose proof (max_default_Z_bounds_source__cut_exchange
    A P f2 default2 maximum2 Hmaximum2)
    as [Hdefault2 [Hbound2 Hsource2]].
  split.
  - destruct Hsource1 as [Hsource | [x [Hx Hsource]]].
    + subst maximum1. lia.
    + subst maximum1.
      specialize (Hpointwise x Hx).
      specialize (Hbound2 x Hx).
      lia.
  - destruct Hsource2 as [Hsource | [x [Hx Hsource]]].
    + subst maximum2. lia.
    + subst maximum2.
      specialize (Hpointwise x Hx).
      specialize (Hbound1 x Hx).
      lia.
Qed.

Definition ChainCutBit
    (current_dist next_dist : list Z) (station bit : Z) : Prop :=
  bit =
    ChainIntervalDistance current_dist 0 station -
    ChainIntervalDistance next_dist 0 station /\
  (bit = 0 \/ bit = 1).

Definition ChainCutHit
    (current_arrivals next_arrivals : list Z)
    (station bit hit : Z) : Prop :=
  hit =
    Znth station next_arrivals 0 -
    Znth station current_arrivals 0 + bit /\
  (hit = 0 \/ hit = 1).

Lemma chain_unit_cut_effect_bits__record_cut :
  forall n current_dist next_dist latest current_arrivals next_arrivals,
    1 <= n ->
    ChainUnitCutPath n current_dist next_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    BusArrivalSchedule n next_dist latest next_arrivals ->
    forall station, 0 <= station < n ->
      exists bit hit,
        ChainCutBit current_dist next_dist station bit /\
        ChainCutHit current_arrivals next_arrivals station bit hit.
Proof.
  intros n current_dist next_dist latest current_arrivals next_arrivals
    Hn Hpath Hcurrent_schedule Hnext_schedule station Hstation.
  destruct (Z.eq_dec station 0) as [Hzero | Hpositive].
  - subst station.
    exists 0, 0.
    split.
    + unfold ChainCutBit.
      rewrite !chain_interval_empty__cut_exchange by lia.
      tauto.
    + unfold ChainCutHit.
      destruct Hcurrent_schedule as [_ [Hcurrent_zero _]].
      destruct Hnext_schedule as [_ [Hnext_zero _]].
      rewrite Hcurrent_zero, Hnext_zero.
      tauto.
  - assert (Hstation_positive : 0 < station) by lia.
    pose proof (bus_schedule_closed_form__cut_exchange
      n current_dist latest current_arrivals Hcurrent_schedule
      station Hstation) as Hcurrent_closed.
    pose proof (bus_schedule_closed_form__cut_exchange
      n next_dist latest next_arrivals Hnext_schedule
      station Hstation) as Hnext_closed.
    pose proof (chain_closed_form_profile__cut_exchange
      current_dist latest station (Znth station current_arrivals 0)
      ltac:(lia) Hcurrent_closed) as Hcurrent_profile.
    pose proof (chain_closed_form_profile__cut_exchange
      next_dist latest station (Znth station next_arrivals 0)
      ltac:(lia) Hnext_closed) as Hnext_profile.
    unfold ChainProfileArrival in Hcurrent_profile, Hnext_profile.
    destruct Hcurrent_profile as [[Hcontra _] |
      [_ [current_envelope [Hcurrent_envelope Hcurrent_value]]]];
      [lia |].
    destruct Hnext_profile as [[Hcontra _] |
      [_ [next_envelope [Hnext_envelope Hnext_value]]]];
      [lia |].
    assert (Hprefix_band : forall s, 0 <= s <= station ->
      ChainIntervalDistance current_dist 0 s - 1 <=
        ChainIntervalDistance next_dist 0 s <=
      ChainIntervalDistance current_dist 0 s).
    {
      intros s Hs.
      apply chain_unit_cut_path_prefix_bounds__cut_exchange
        with (n := n); try assumption.
      lia.
    }
    assert (Henvelope_band :
      current_envelope <= next_envelope <= current_envelope + 1).
    {
      unfold ChainCutEnvelope in
        Hcurrent_envelope, Hnext_envelope.
      eapply (@max_default_Z_unit_band__record_cut
        Z (fun cut => 0 <= cut < station)
        (fun cut =>
           Znth cut latest 0 -
           ChainIntervalDistance current_dist 0 cut)
        (fun cut =>
           Znth cut latest 0 -
           ChainIntervalDistance next_dist 0 cut)
        (- ChainIntervalDistance current_dist 0 0)
        (- ChainIntervalDistance next_dist 0 0)
        current_envelope next_envelope).
      - exact Hcurrent_envelope.
      - exact Hnext_envelope.
      - assert (Hzero_range : 0 <= 0 <= station) by lia.
        pose proof (Hprefix_band 0 Hzero_range) as Hzero_band.
        lia.
      - intros cut Hcut.
        change (0 <= cut < station) in Hcut.
        assert (Hcut_range : 0 <= cut <= station) by lia.
        pose proof (Hprefix_band cut Hcut_range) as Hcut_band.
        lia.
    }
    assert (Hstation_range : 0 <= station <= station) by lia.
    pose proof (Hprefix_band station Hstation_range) as Hstation_band.
    set (bit :=
      ChainIntervalDistance current_dist 0 station -
      ChainIntervalDistance next_dist 0 station).
    set (hit := next_envelope - current_envelope).
    exists bit, hit.
    split.
    + unfold ChainCutBit, bit.
      split; [reflexivity |]. lia.
    + unfold ChainCutHit, hit, bit.
      split.
      * lia.
      * lia.
Qed.

Definition ChainCutHitStep
    (current_arrivals latest : list Z)
    (station bit hit next_hit : Z) : Prop :=
  (Znth station current_arrivals 0 < Znth station latest 0 /\
   next_hit = bit) \/
  (Znth station latest 0 < Znth station current_arrivals 0 /\
   next_hit = hit) \/
  (Znth station current_arrivals 0 = Znth station latest 0 /\
   ((hit = 1 \/ bit = 1) /\ next_hit = 1 \/
    hit = 0 /\ bit = 0 /\ next_hit = 0)).

Lemma chain_unit_cut_hit_step__record_cut :
  forall n current_dist next_dist latest current_arrivals next_arrivals
         station bit hit next_bit next_hit,
    1 <= n ->
    0 <= station < n - 1 ->
    ChainUnitCutPath n current_dist next_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    BusArrivalSchedule n next_dist latest next_arrivals ->
    ChainCutBit current_dist next_dist station bit ->
    ChainCutHit current_arrivals next_arrivals station bit hit ->
    ChainCutBit current_dist next_dist (station + 1) next_bit ->
    ChainCutHit current_arrivals next_arrivals
      (station + 1) next_bit next_hit ->
    ChainCutHitStep current_arrivals latest station bit hit next_hit.
Proof.
  intros n current_dist next_dist latest current_arrivals next_arrivals
    station bit hit next_bit next_hit Hn Hstation Hpath
    Hcurrent_schedule Hnext_schedule Hbit Hhit Hnext_bit Hnext_hit.
  unfold ChainCutBit in Hbit, Hnext_bit.
  unfold ChainCutHit in Hhit, Hnext_hit.
  destruct Hbit as [Hbit_value Hbit_bool].
  destruct Hhit as [Hhit_value Hhit_bool].
  destruct Hnext_bit as [Hnext_bit_value Hnext_bit_bool].
  destruct Hnext_hit as [Hnext_hit_value Hnext_hit_bool].
  destruct Hcurrent_schedule as [_ [_ Hcurrent_step]].
  destruct Hnext_schedule as [_ [_ Hnext_step]].
  specialize (Hcurrent_step station Hstation).
  specialize (Hnext_step station Hstation).
  destruct Hcurrent_step as
    [current_departure [Hcurrent_departure Hcurrent_next]].
  destruct Hnext_step as
    [next_departure [Hnext_departure Hnext_next]].
  pose proof (station_departure_ge_inputs__chain_dual
    current_arrivals latest station current_departure Hcurrent_departure)
    as [Hcurrent_arrival_le Hcurrent_latest_le].
  pose proof (station_departure_ge_inputs__chain_dual
    next_arrivals latest station next_departure Hnext_departure)
    as [Hnext_arrival_le Hnext_latest_le].
  assert (Hcurrent_departure_cases :
    current_departure = Znth station current_arrivals 0 \/
    current_departure = Znth station latest 0).
  {
    unfold StationDeparture,
      MaxMin.max_value_of_subset_with_default in Hcurrent_departure.
    destruct Hcurrent_departure as
      [[Hmaximum Hdefault] | [Hall Heq]].
    - destruct Hmaximum as [candidate [[Hcandidate Hgreatest] Hvalue]].
      change (candidate = Znth station latest 0) in Hcandidate.
      subst candidate. cbn in Hvalue. right. symmetry. exact Hvalue.
    - left. symmetry. exact Heq.
  }
  assert (Hnext_departure_cases :
    next_departure = Znth station next_arrivals 0 \/
    next_departure = Znth station latest 0).
  {
    unfold StationDeparture,
      MaxMin.max_value_of_subset_with_default in Hnext_departure.
    destruct Hnext_departure as
      [[Hmaximum Hdefault] | [Hall Heq]].
    - destruct Hmaximum as [candidate [[Hcandidate Hgreatest] Hvalue]].
      change (candidate = Znth station latest 0) in Hcandidate.
      subst candidate. cbn in Hvalue. right. symmetry. exact Hvalue.
    - left. symmetry. exact Heq.
  }
  pose proof (chain_prefix_increment__cut_exchange
    current_dist station ltac:(lia)) as Hcurrent_increment.
  pose proof (chain_prefix_increment__cut_exchange
    next_dist station ltac:(lia)) as Hnext_increment.
  destruct (Z.lt_trichotomy
    (Znth station current_arrivals 0)
    (Znth station latest 0)) as
    [Hwait | [Hequal | Hbusy]].
  - left. split; [exact Hwait |].
    destruct Hcurrent_departure_cases as [Hcontra | Hcurrent_departure_eq];
      [lia |].
    assert (Hnext_departure_eq :
      next_departure = Znth station latest 0).
    {
      destruct Hnext_departure_cases as [Hnext_arrival | Hnext_latest];
        [| exact Hnext_latest].
      subst next_departure.
      destruct Hhit_bool as [-> | ->];
      destruct Hbit_bool as [-> | ->]; lia.
    }
    lia.
  - right. right. split; [exact Hequal |].
    destruct Hhit_bool as [Hhit_zero | Hhit_one];
    destruct Hbit_bool as [Hbit_zero | Hbit_one]; subst hit bit.
    + right. repeat split; auto.
      destruct Hcurrent_departure_cases;
      destruct Hnext_departure_cases; lia.
    + left. split; [tauto |].
      destruct Hcurrent_departure_cases;
      destruct Hnext_departure_cases; lia.
    + left. split; [tauto |].
      destruct Hcurrent_departure_cases;
      destruct Hnext_departure_cases; lia.
    + left. split; [tauto |].
      destruct Hcurrent_departure_cases;
      destruct Hnext_departure_cases; lia.
  - right. left. split; [exact Hbusy |].
    assert (Hcurrent_departure_eq :
      current_departure = Znth station current_arrivals 0).
    {
      destruct Hcurrent_departure_cases; [assumption | lia].
    }
    assert (Hnext_departure_eq :
      next_departure = Znth station next_arrivals 0).
    {
      destruct Hnext_departure_cases as [Hnext_arrival | Hnext_latest];
        [exact Hnext_arrival |].
      destruct Hhit_bool as [-> | ->];
      destruct Hbit_bool as [-> | ->]; lia.
    }
    lia.
Qed.

Definition ChainCutBitValue
    (current_dist next_dist : list Z) (station : Z) : Z :=
  ChainIntervalDistance current_dist 0 station -
  ChainIntervalDistance next_dist 0 station.

Definition ChainCutHitValue
    (current_dist next_dist current_arrivals next_arrivals : list Z)
    (station : Z) : Z :=
  Znth station next_arrivals 0 -
  Znth station current_arrivals 0 +
  ChainCutBitValue current_dist next_dist station.

Definition ChainRecordCutEffect
    (n : Z) (counts current_dist next_dist current_arrivals next_arrivals : list Z)
    (effect : Z) : Prop :=
  effect =
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 *
           (ChainCutHitValue
              current_dist next_dist current_arrivals next_arrivals station -
            ChainCutBitValue current_dist next_dist station)).

Lemma chain_unit_cut_values_boolean__record_cut :
  forall n current_dist next_dist latest current_arrivals next_arrivals,
    1 <= n ->
    ChainUnitCutPath n current_dist next_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    BusArrivalSchedule n next_dist latest next_arrivals ->
    forall station, 0 <= station < n ->
      (ChainCutBitValue current_dist next_dist station = 0 \/
       ChainCutBitValue current_dist next_dist station = 1) /\
      (ChainCutHitValue
         current_dist next_dist current_arrivals next_arrivals station = 0 \/
       ChainCutHitValue
         current_dist next_dist current_arrivals next_arrivals station = 1).
Proof.
  intros n current_dist next_dist latest current_arrivals next_arrivals
    Hn Hpath Hcurrent_schedule Hnext_schedule station Hstation.
  destruct (chain_unit_cut_effect_bits__record_cut
    n current_dist next_dist latest current_arrivals next_arrivals
    Hn Hpath Hcurrent_schedule Hnext_schedule station Hstation)
    as [bit [hit [Hbit Hhit]]].
  unfold ChainCutBit in Hbit.
  unfold ChainCutHit in Hhit.
  unfold ChainCutBitValue, ChainCutHitValue.
  destruct Hbit as [Hbit_value Hbit_bool].
  destruct Hhit as [Hhit_value Hhit_bool].
  subst bit hit.
  tauto.
Qed.

Lemma chain_unit_cut_values_step__record_cut :
  forall n current_dist next_dist latest current_arrivals next_arrivals station,
    1 <= n ->
    0 <= station < n - 1 ->
    ChainUnitCutPath n current_dist next_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    BusArrivalSchedule n next_dist latest next_arrivals ->
    ChainCutHitStep current_arrivals latest station
      (ChainCutBitValue current_dist next_dist station)
      (ChainCutHitValue
        current_dist next_dist current_arrivals next_arrivals station)
      (ChainCutHitValue
        current_dist next_dist current_arrivals next_arrivals (station + 1)).
Proof.
  intros n current_dist next_dist latest current_arrivals next_arrivals
    station Hn Hstation Hpath Hcurrent_schedule Hnext_schedule.
  pose proof (chain_unit_cut_values_boolean__record_cut
    n current_dist next_dist latest current_arrivals next_arrivals
    Hn Hpath Hcurrent_schedule Hnext_schedule station ltac:(lia))
    as [Hbit Hhit].
  pose proof (chain_unit_cut_values_boolean__record_cut
    n current_dist next_dist latest current_arrivals next_arrivals
    Hn Hpath Hcurrent_schedule Hnext_schedule (station + 1) ltac:(lia))
    as [Hnext_bit Hnext_hit].
  eapply chain_unit_cut_hit_step__record_cut
    with (next_bit := ChainCutBitValue current_dist next_dist (station + 1));
    try eassumption.
  - unfold ChainCutBit, ChainCutBitValue. tauto.
  - unfold ChainCutHit, ChainCutHitValue. tauto.
  - unfold ChainCutBit, ChainCutBitValue. tauto.
  - unfold ChainCutHit, ChainCutHitValue. tauto.
Qed.

Lemma chain_record_cut_effect_total__record_cut :
  forall n m initial_dist times origins destinations counts
         current_dist next_dist current_arrivals next_arrivals
         current_total next_total,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    DestinationCounts n m destinations counts ->
    PassengerTravelTotal
      m times destinations current_arrivals current_total ->
    PassengerTravelTotal
      m times destinations next_arrivals next_total ->
    ChainRecordCutEffect
      n counts current_dist next_dist current_arrivals next_arrivals
      (next_total - current_total).
Proof.
  intros n m initial_dist times origins destinations counts
    current_dist next_dist current_arrivals next_arrivals
    current_total next_total Hinputs Hcounts Hcurrent_total Hnext_total.
  unfold ChainRecordCutEffect.
  rewrite (sum_Z_range_ext 1 n
    (fun station =>
       Znth station counts 0 *
       (ChainCutHitValue
          current_dist next_dist current_arrivals next_arrivals station -
        ChainCutBitValue current_dist next_dist station))
    (fun station =>
       Znth station counts 0 *
       (Znth station next_arrivals 0 -
        Znth station current_arrivals 0))).
  2: {
    intros station Hstation.
    unfold ChainCutHitValue, ChainCutBitValue.
    ring.
  }
  rewrite (sum_Z_range_ext 1 n
    (fun station =>
       Znth station counts 0 *
       (Znth station next_arrivals 0 -
        Znth station current_arrivals 0))
    (fun station =>
       Znth station counts 0 * Znth station next_arrivals 0 -
       Znth station counts 0 * Znth station current_arrivals 0)).
  2: { intros station Hstation. ring. }
  rewrite sum_Z_range_sub.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts next_arrivals
    Hinputs Hcounts) as Hnext_identity.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts current_arrivals
    Hinputs Hcounts) as Hcurrent_identity.
  rewrite Hnext_identity, Hcurrent_identity.
  unfold PassengerTravelTotal in Hcurrent_total, Hnext_total.
  rewrite sum_Z_range_sub in Hcurrent_total, Hnext_total.
  lia.
Qed.

Definition RecordResetStart
    (bit hit : Z -> Z) (start : Z) : Prop :=
  1 <= start /\
  bit (start - 1) = 0 /\
  bit start = 1 /\
  hit start = 0.

Lemma record_zero_run_hit_zero__normalization :
  forall last bit hit lo hi,
    0 <= lo /\ lo <= hi /\ hi <= last ->
    hit lo = 0 ->
    (forall station, lo <= station < hi -> bit station = 0) ->
    (forall station, 0 <= station < last ->
       bit station = 0 -> hit station = 0 -> hit (station + 1) = 0) ->
    hit hi = 0.
Proof.
  intros last bit hit lo hi Hrange Hhit Hbits Hcarry.
  remember (Z.to_nat (hi - lo)) as fuel eqn:Hfuel.
  assert (Hhi : hi = lo + Z.of_nat fuel) by lia.
  subst hi.
  clear Hfuel.
  induction fuel as [|fuel IH].
  - cbn. replace (lo + 0) with lo by lia. exact Hhit.
  - rewrite Nat2Z.inj_succ.
    unfold Z.succ.
    replace (lo + (Z.of_nat fuel + 1))
      with ((lo + Z.of_nat fuel) + 1) by ring.
    apply Hcarry.
    + lia.
    + apply Hbits. lia.
    + apply IH; try lia.
      intros station Hstation.
      apply Hbits. lia.
Qed.

Lemma record_first_one_after__normalization :
  forall last bit lo,
    0 <= lo < last ->
    bit last = 1 ->
    (forall station, lo < station <= last ->
       bit station = 0 \/ bit station = 1) ->
    exists start,
      lo < start <= last /\
      bit start = 1 /\
      forall station, lo < station < start -> bit station = 0.
Proof.
  intros last bit lo Hlo Hlast Hbit_bool.
  set (width := last - lo - 1).
  assert (Hwidth : 0 <= width) by (unfold width; lia).
  assert (Hexists : exists offset,
    0 <= offset <= width /\ bit (lo + 1 + offset) = 1).
  {
    exists width.
    split; [lia |].
    unfold width.
    replace (lo + 1 + (last - lo - 1)) with last by ring.
    exact Hlast.
  }
  destruct (min_n_in_range
    (fun offset => bit (lo + 1 + offset) = 1)
    width Hwidth Hexists) as
    [offset [Hoffset_value [Hoffset_range Hoffset_min]]].
  exists (lo + 1 + offset).
  split; [lia |].
  split; [exact Hoffset_value |].
  intros station Hstation.
  destruct (Z.eq_dec (bit station) 0) as [Hzero | Hnot_zero];
    [exact Hzero |].
  exfalso.
  assert (Hstation_offset :
    0 <= station - (lo + 1) <= width) by (unfold width; lia).
  specialize (Hoffset_min (station - (lo + 1)) Hstation_offset).
  assert (Hstation_rewrite :
    lo + 1 + (station - (lo + 1)) = station) by ring.
  rewrite Hstation_rewrite in Hoffset_min.
  destruct (Hbit_bool station ltac:(lia)) as [Hbit_zero | Hbit_one].
  - contradiction.
  - specialize (Hoffset_min Hbit_one). lia.
Qed.

Lemma record_first_reset_start__normalization :
  forall last bit hit,
    1 <= last ->
    bit 0 = 0 ->
    bit last = 1 ->
    hit 0 = 0 ->
    (forall station, 0 <= station <= last ->
       bit station = 0 \/ bit station = 1) ->
    (forall station, 0 <= station < last ->
       bit station = 0 -> hit station = 0 -> hit (station + 1) = 0) ->
    exists start,
      1 <= start <= last /\ RecordResetStart bit hit start.
Proof.
  intros last bit hit Hlast Hbit_zero Hbit_last Hhit_zero
    Hbit_bool Hcarry.
  destruct (record_first_one_after__normalization
    last bit 0 ltac:(lia) Hbit_last
    ltac:(intros station Hstation; apply Hbit_bool; lia)) as
    [start [Hstart [Hstart_one Hbefore_zero]]].
  assert (Hhit_start : hit start = 0).
  {
    eapply record_zero_run_hit_zero__normalization
      with (lo := 0) (last := last); try eassumption.
    - lia.
    - intros station Hstation.
      destruct (Z.eq_dec station 0) as [-> | Hnonzero].
      + exact Hbit_zero.
      + apply Hbefore_zero. lia.
  }
  exists start.
  split; [lia |].
  unfold RecordResetStart.
  split; [lia |].
  split.
  - destruct (Z.eq_dec (start - 1) 0) as [Heq | Hneq].
    + rewrite Heq. exact Hbit_zero.
    + apply Hbefore_zero. lia.
  - split; [exact Hstart_one | exact Hhit_start].
Qed.

Lemma record_last_reset_start__normalization :
  forall last bit hit,
    1 <= last ->
    (exists start, 1 <= start <= last /\ RecordResetStart bit hit start) ->
    exists start,
      1 <= start <= last /\
      RecordResetStart bit hit start /\
      forall later, start < later <= last ->
        RecordResetStart bit hit later -> False.
Proof.
  intros last bit hit Hlast Hexists.
  destruct (max_n_in_range
    (fun start => RecordResetStart bit hit start)
    last ltac:(lia)) as [start [Hstart [Hrange Hmax]]].
  - destruct Hexists as [witness [Hwitness Hreset]].
    exists witness. split; [lia | exact Hreset].
  - exists start.
    split.
    + unfold RecordResetStart in Hstart. lia.
    + split; [exact Hstart |].
      intros later Hlater Hlater_reset.
      specialize (Hmax later ltac:(lia) Hlater_reset).
      lia.
Qed.

Lemma record_after_last_reset_zero_is_hit__normalization :
  forall last bit hit start,
    1 <= last ->
    (forall station, 0 <= station <= last ->
       bit station = 0 \/ bit station = 1) ->
    (forall station, 0 <= station <= last ->
       hit station = 0 \/ hit station = 1) ->
    (forall station, 0 <= station < last ->
       bit station = 0 -> hit station = 0 -> hit (station + 1) = 0) ->
    bit last = 1 ->
    1 <= start ->
    start < last ->
    (forall later, start < later <= last ->
       RecordResetStart bit hit later -> False) ->
    forall station, start <= station <= last ->
      bit station = 0 -> hit station = 1.
Proof.
  intros last bit hit start Hlast Hbit_bool Hhit_bool Hcarry Hbit_last
    Hstart_nonnegative Hstart_lt Hmax station Hstation Hbit_station.
  assert (Hstation_full : 0 <= station <= last) by lia.
  destruct (Hbit_bool station Hstation_full) as [Hbit_zero | Hbit_one];
    [| congruence].
  destruct (Z.eq_dec (hit station) 1) as [Hhit_one | Hhit_not_one];
    [exact Hhit_one |].
  assert (Hhit_zero : hit station = 0).
  { destruct (Hhit_bool station Hstation_full); [assumption | congruence]. }
  assert (Hstation_lt : station < last).
  {
    destruct (Z.eq_dec station last); [subst; congruence | lia].
  }
  destruct (record_first_one_after__normalization
    last bit station ltac:(lia) Hbit_last
    ltac:(intros j Hj; apply Hbit_bool; lia)) as
    [later [Hlater [Hlater_one Hbetween_zero]]].
  assert (Hhit_later : hit later = 0).
  {
    eapply record_zero_run_hit_zero__normalization
      with (lo := station) (last := last); try eassumption.
    - lia.
    - intros j Hj.
      destruct (Z.eq_dec j station) as [-> | Hneq].
      + exact Hbit_zero.
      + apply Hbetween_zero. lia.
  }
  exfalso.
  apply (Hmax later ltac:(lia)).
  unfold RecordResetStart.
  split; [lia |].
  split.
  - destruct (Z.eq_dec (later - 1) station) as [Heq | Hneq].
    + rewrite Heq. exact Hbit_zero.
    + apply Hbetween_zero. lia.
  - split; [exact Hlater_one | exact Hhit_later].
Qed.

Lemma record_terminal_path_suffix_bound__normalization :
  forall last weight bit hit,
    1 <= last ->
    bit 0 = 0 ->
    bit last = 1 ->
    hit 0 = 0 ->
    (forall station, 0 <= station <= last ->
       bit station = 0 \/ bit station = 1) ->
    (forall station, 0 <= station <= last ->
       hit station = 0 \/ hit station = 1) ->
    (forall station, 0 <= station <= last -> 0 <= weight station) ->
    (forall station, 0 <= station < last ->
       bit station = 0 -> hit station = 0 -> hit (station + 1) = 0) ->
    (forall start, 1 <= start <= last ->
       RecordResetStart bit hit start ->
       0 <= sum (fun station => 1 <= station < start)
              (fun station => weight station * (hit station - bit station))) ->
    exists start,
      1 <= start <= last /\
      RecordResetStart bit hit start /\
      (forall later, start < later <= last ->
         RecordResetStart bit hit later -> False) /\
      sum (fun station => start <= station < last + 1)
          (fun station => weight station * (hit station - 1)) <=
      sum (fun station => 1 <= station < last + 1)
          (fun station => weight station * (hit station - bit station)).
Proof.
  intros last weight bit hit Hlast Hbit_zero Hbit_last Hhit_zero
    Hbit_bool Hhit_bool Hweight Hcarry Hprefix_nonnegative.
  destruct (record_first_reset_start__normalization
    last bit hit Hlast Hbit_zero Hbit_last Hhit_zero Hbit_bool Hcarry)
    as [first [Hfirst_range Hfirst_reset]].
  destruct (record_last_reset_start__normalization
    last bit hit Hlast ltac:(exists first; tauto)) as
    [start [Hstart_range [Hstart_reset Hlast_reset]]].
  exists start.
  split; [exact Hstart_range |].
  split; [exact Hstart_reset |].
  split; [exact Hlast_reset |].
  pose proof (Hprefix_nonnegative start Hstart_range Hstart_reset)
    as Hprefix_cost.
  assert (Htail_pointwise : forall station,
    start <= station < last + 1 ->
    weight station * (hit station - 1) <=
    weight station * (hit station - bit station)).
  {
    intros station Hstation.
    destruct (Hbit_bool station ltac:(lia)) as [Hbit_station | Hbit_station].
    - assert (Hhit_station : hit station = 1).
      {
        destruct (Z.eq_dec start last) as [Hstart_last | Hstart_before].
        - subst start.
          assert (station = last) by lia.
          subst station. congruence.
        - eapply (record_after_last_reset_zero_is_hit__normalization
            last bit hit start Hlast Hbit_bool Hhit_bool Hcarry
            Hbit_last ltac:(lia) ltac:(lia) Hlast_reset station).
          + lia.
          + exact Hbit_station.
      }
      rewrite Hbit_station, Hhit_station.
      specialize (Hweight station ltac:(lia)).
      nia.
    - rewrite Hbit_station.
      lia.
  }
  pose proof (sum_Z_range_le start (last + 1)
    (fun station => weight station * (hit station - 1))
    (fun station => weight station * (hit station - bit station))
    Htail_pointwise) as Htail_cost.
  rewrite (sum_Z_range_split 1 start (last + 1)
    (fun station => weight station * (hit station - bit station)))
    by lia.
  lia.
Qed.

Lemma record_reset_prefix_nonnegative__normalization :
  forall n m budget initial_dist times origins destinations latest counts
         current_dist next_dist current_arrivals next_arrivals current_total
         start,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    DestinationCounts n m destinations counts ->
    FeasibleBoostedDistances n budget initial_dist current_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    PassengerTravelTotal
      m times destinations current_arrivals current_total ->
    SightseeingMinimumTotal
      n m budget initial_dist times origins destinations current_total ->
    FeasibleBoostedDistances n (budget + 1) initial_dist next_dist ->
    BusArrivalSchedule n next_dist latest next_arrivals ->
    ChainUnitCutPath n current_dist next_dist ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge current_dist 0) = budget ->
    1 <= start <= n - 1 ->
    RecordResetStart
      (ChainCutBitValue current_dist next_dist)
      (ChainCutHitValue
        current_dist next_dist current_arrivals next_arrivals)
      start ->
    0 <= sum (fun station => 1 <= station < start)
        (fun station =>
           Znth station counts 0 *
           (ChainCutHitValue
              current_dist next_dist current_arrivals next_arrivals station -
            ChainCutBitValue current_dist next_dist station)).
Proof.
  intros n m budget initial_dist times origins destinations latest counts
    current_dist next_dist current_arrivals next_arrivals current_total
    start Hinputs Hlatest Hcounts Hcurrent_feasible Hcurrent_schedule
    Hcurrent_total Hminimum Hnext_feasible Hnext_schedule Hpath
    Hcurrent_used Hstart Hreset.
  unfold RecordResetStart in Hreset.
  destruct Hreset as
    [Hstart_positive [Hbit_before [Hbit_start Hhit_start]]].
  set (current_prefix := fun station =>
    ChainIntervalDistance current_dist 0 station).
  set (next_prefix := fun station =>
    ChainIntervalDistance next_dist 0 station).
  set (truncated_prefix := fun station =>
    if Z_lt_dec station start
    then next_prefix station else current_prefix station).
  assert (Htruncated_zero : truncated_prefix 0 = 0).
  {
    unfold truncated_prefix, next_prefix.
    destruct (Z_lt_dec 0 start); [|lia].
    apply chain_interval_empty__cut_exchange. lia.
  }
  destruct (chain_distance_from_prefix__cut_exchange
    n truncated_prefix ltac:(unfold SightseeingInputsBounded in Hinputs; lia)
    Htruncated_zero) as
    [truncated_dist
      [Htruncated_dist_length [Htruncated_dist_value Htruncated_prefix]]].
  set (truncated_arrival_value := fun station =>
    if Z_lt_dec station start
    then Znth station next_arrivals 0
    else Znth station current_arrivals 0).
  destruct (finite_Z_function_list__cut_exchange
    n truncated_arrival_value
    ltac:(unfold SightseeingInputsBounded in Hinputs; lia)) as
    [truncated_arrivals
      [Htruncated_arrivals_length Htruncated_arrivals_value]].
  pose proof Hcurrent_feasible as Hcurrent_fields.
  rewrite FeasibleBoostedDistances_unfold in Hcurrent_fields.
  destruct Hcurrent_fields as
    [Hcurrent_dist_length [Hcurrent_bounds Hcurrent_budget]].
  pose proof Hnext_feasible as Hnext_fields.
  rewrite FeasibleBoostedDistances_unfold in Hnext_fields.
  destruct Hnext_fields as [Hnext_dist_length [Hnext_bounds Hnext_budget]].
  assert (Htruncated_bounds : forall edge, 0 <= edge < n - 1 ->
    0 <= Znth edge truncated_dist 0 <= Znth edge initial_dist 0).
  {
    intros edge Hedge.
    rewrite Htruncated_dist_value by exact Hedge.
    unfold truncated_prefix.
    destruct (Z_lt_dec edge start) as [Hedge_before | Hedge_after];
    destruct (Z_lt_dec (edge + 1) start) as
      [Hnext_before | Hnext_after].
    - unfold next_prefix.
      rewrite chain_prefix_increment__cut_exchange by lia.
      apply Hnext_bounds. exact Hedge.
    - assert (Hedge_eq : edge = start - 1) by lia.
      subst edge.
      unfold ChainCutBitValue in Hbit_before.
      unfold next_prefix, current_prefix.
      pose proof (chain_prefix_increment__cut_exchange
        current_dist (start - 1) ltac:(lia)) as Hcurrent_increment.
      pose proof (Hcurrent_bounds (start - 1) ltac:(lia))
        as Hcurrent_edge_bounds.
      lia.
    - lia.
    - unfold current_prefix.
      rewrite chain_prefix_increment__cut_exchange by lia.
      apply Hcurrent_bounds. exact Hedge.
  }
  assert (Htruncated_endpoint :
    ChainIntervalDistance truncated_dist 0 (n - 1) =
    ChainIntervalDistance current_dist 0 (n - 1)).
  {
    rewrite Htruncated_prefix by lia.
    unfold truncated_prefix, current_prefix.
    destruct (Z_lt_dec (n - 1) start); [lia | reflexivity].
  }
  assert (Htruncated_feasible :
    FeasibleBoostedDistances n budget initial_dist truncated_dist).
  {
    rewrite FeasibleBoostedDistances_unfold.
    split; [exact Htruncated_dist_length |].
    split; [exact Htruncated_bounds |].
    rewrite chain_reduction_prefix__cut_exchange.
    rewrite Htruncated_endpoint.
    rewrite <- chain_reduction_prefix__cut_exchange.
    rewrite Hcurrent_used.
    lia.
  }
  assert (Htruncated_schedule :
    BusArrivalSchedule n truncated_dist latest truncated_arrivals).
  {
    unfold BusArrivalSchedule.
    split; [exact Htruncated_arrivals_length |].
    split.
    - rewrite Htruncated_arrivals_value by
        (unfold SightseeingInputsBounded in Hinputs; lia).
      unfold truncated_arrival_value.
      destruct (Z_lt_dec 0 start); [|lia].
      destruct Hnext_schedule as [_ [Hnext_zero _]].
      exact Hnext_zero.
    - intros edge Hedge.
      destruct (Z.lt_trichotomy (edge + 1) start) as
        [Hbefore | [Hboundary | Hafter]].
      + pose proof Hnext_schedule as Hnext_at_edge.
        destruct Hnext_at_edge as [_ [_ Hstep]].
        specialize (Hstep edge Hedge).
        destruct Hstep as [departure [Hdeparture Harrival]].
        exists departure.
        split.
        * eapply station_departure_arrivals_ext__cut_exchange.
          2: exact Hdeparture.
          rewrite Htruncated_arrivals_value by lia.
          unfold truncated_arrival_value.
          destruct (Z_lt_dec edge start); [reflexivity | lia].
        * rewrite Htruncated_arrivals_value by lia.
          rewrite Htruncated_dist_value by exact Hedge.
          unfold truncated_arrival_value, truncated_prefix.
          destruct (Z_lt_dec edge start); [|lia].
          destruct (Z_lt_dec (edge + 1) start); [|lia].
          unfold next_prefix.
          rewrite chain_prefix_increment__cut_exchange by lia.
          exact Harrival.
      + assert (Hedge_eq : edge = start - 1) by lia.
        subst edge.
        pose proof Hnext_schedule as Hnext_at_edge.
        destruct Hnext_at_edge as [_ [_ Hnext_step]].
        specialize (Hnext_step (start - 1) ltac:(lia)).
        destruct Hnext_step as
          [next_departure [Hnext_departure Hnext_arrival]].
        pose proof Hcurrent_schedule as Hcurrent_at_edge.
        destruct Hcurrent_at_edge as [_ [_ Hcurrent_step]].
        specialize (Hcurrent_step (start - 1) ltac:(lia)).
        destruct Hcurrent_step as
          [current_departure [Hcurrent_departure Hcurrent_arrival]].
        exists next_departure.
        split.
        * eapply station_departure_arrivals_ext__cut_exchange.
          2: exact Hnext_departure.
          rewrite Htruncated_arrivals_value by lia.
          unfold truncated_arrival_value.
          destruct (Z_lt_dec (start - 1) start);
            [reflexivity | lia].
        * rewrite Htruncated_arrivals_value by lia.
          rewrite Htruncated_dist_value by lia.
          unfold truncated_arrival_value, truncated_prefix.
          replace (start - 1 + 1) with start by lia.
          destruct (Z_lt_dec start start); [lia |].
          destruct (Z_lt_dec (start - 1) start); [|lia].
          unfold current_prefix, next_prefix.
          pose proof (chain_prefix_increment__cut_exchange
            current_dist (start - 1) ltac:(lia)) as Hcurrent_increment.
          pose proof (chain_prefix_increment__cut_exchange
            next_dist (start - 1) ltac:(lia)) as Hnext_increment.
          replace (start - 1 + 1) with start in
            Hcurrent_increment, Hnext_increment,
            Hcurrent_arrival, Hnext_arrival by lia.
          rewrite <- Hnext_increment in Hnext_arrival.
          unfold ChainCutBitValue in Hbit_before, Hbit_start.
          unfold ChainCutHitValue in Hhit_start.
          unfold ChainCutBitValue in Hhit_start.
          lia.
      + pose proof Hcurrent_schedule as Hcurrent_at_edge.
        destruct Hcurrent_at_edge as [_ [_ Hstep]].
        specialize (Hstep edge Hedge).
        destruct Hstep as [departure [Hdeparture Harrival]].
        exists departure.
        split.
        * eapply station_departure_arrivals_ext__cut_exchange.
          2: exact Hdeparture.
          rewrite Htruncated_arrivals_value by lia.
          unfold truncated_arrival_value.
          destruct (Z_lt_dec edge start); [lia | reflexivity].
        * rewrite Htruncated_arrivals_value by lia.
          rewrite Htruncated_dist_value by exact Hedge.
          unfold truncated_arrival_value, truncated_prefix.
          destruct (Z_lt_dec edge start); [lia |].
          destruct (Z_lt_dec (edge + 1) start); [lia |].
          unfold current_prefix.
          rewrite chain_prefix_increment__cut_exchange by lia.
          exact Harrival.
  }
  set (truncated_total :=
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) truncated_arrivals 0 -
           Znth passenger times 0)).
  assert (Htruncated_total :
    PassengerTravelTotal
      m times destinations truncated_arrivals truncated_total).
  { unfold PassengerTravelTotal, truncated_total. reflexivity. }
  assert (Htruncated_candidate :
    SightseeingCandidateTotal
      n m budget initial_dist times origins destinations truncated_total).
  {
    exists truncated_dist, latest, truncated_arrivals.
    exact (conj Hlatest
      (conj Htruncated_feasible
        (conj Htruncated_schedule Htruncated_total))).
  }
  assert (Hminimum_bound : current_total <= truncated_total).
  {
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset in Hminimum.
    destruct Hminimum as [witness [[Hwitness Hleast] Hvalue]].
    cbn in Hvalue. subst witness.
    specialize (Hleast truncated_total Htruncated_candidate).
    cbn in Hleast. exact Hleast.
  }
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts truncated_arrivals
    Hinputs Hcounts) as Htruncated_identity.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts current_arrivals
    Hinputs Hcounts) as Hcurrent_identity.
  assert (Hdifference :
    truncated_total - current_total =
    sum (fun station => 1 <= station < start)
        (fun station =>
           Znth station counts 0 *
           (ChainCutHitValue
              current_dist next_dist current_arrivals next_arrivals station -
            ChainCutBitValue current_dist next_dist station))).
  {
    unfold truncated_total.
    rewrite sum_Z_range_sub.
    unfold PassengerTravelTotal in Hcurrent_total.
    rewrite sum_Z_range_sub in Hcurrent_total.
    rewrite Hcurrent_total.
    ring_simplify.
    rewrite <- Htruncated_identity, <- Hcurrent_identity.
    rewrite <- sum_Z_range_sub.
    rewrite (sum_Z_range_split 1 start n
      (fun station =>
         Znth station counts 0 * Znth station truncated_arrivals 0 -
         Znth station counts 0 * Znth station current_arrivals 0)) by lia.
    assert (Hafter_zero :
      sum (fun station => start <= station < n)
          (fun station =>
             Znth station counts 0 * Znth station truncated_arrivals 0 -
             Znth station counts 0 * Znth station current_arrivals 0) = 0).
    {
      apply sum_Z_range_eq_zero.
      intros station Hstation.
      rewrite Htruncated_arrivals_value by lia.
      unfold truncated_arrival_value.
      destruct (Z_lt_dec station start); [lia | ring].
    }
    rewrite Hafter_zero.
    rewrite (sum_Z_range_ext 1 start
      (fun station =>
         Znth station counts 0 * Znth station truncated_arrivals 0 -
         Znth station counts 0 * Znth station current_arrivals 0)
      (fun station =>
         Znth station counts 0 *
         (ChainCutHitValue
            current_dist next_dist current_arrivals next_arrivals station -
          ChainCutBitValue current_dist next_dist station))).
    2: {
      intros station Hstation.
      rewrite Htruncated_arrivals_value by lia.
      unfold truncated_arrival_value, ChainCutHitValue.
      destruct (Z_lt_dec station start); [|lia].
      ring.
    }
    lia.
  }
  lia.
Qed.

Lemma record_after_last_reset_suffix_step__normalization :
  forall last bit hit start current_arrivals latest station,
    1 <= start ->
    start <= station < last ->
    (forall j, 0 <= j <= last -> bit j = 0 \/ bit j = 1) ->
    (forall j, 0 <= j <= last -> hit j = 0 \/ hit j = 1) ->
    (forall j, start <= j <= last -> bit j = 0 -> hit j = 1) ->
    (forall later, start < later <= last ->
       RecordResetStart bit hit later -> False) ->
    ChainCutHitStep current_arrivals latest station
      (bit station) (hit station) (hit (station + 1)) ->
    (Znth station current_arrivals 0 < Znth station latest 0 /\
       hit (station + 1) = 1) \/
    (Znth station latest 0 < Znth station current_arrivals 0 /\
       hit (station + 1) = hit station) \/
    (Znth station current_arrivals 0 = Znth station latest 0 /\
       hit (station + 1) = 1).
Proof.
  intros last bit hit start current_arrivals latest station
    Hstart Hstation Hbit_bool Hhit_bool Hzero_hit Hmax Hstep.
  unfold ChainCutHitStep in Hstep.
  destruct Hstep as
    [[Hwait Hnext] | [[Hbusy Hnext] | [Hequal Hor]]].
  - left. split; [exact Hwait |].
    rewrite Hnext.
    destruct (Hbit_bool station ltac:(lia)) as [Hbit_zero | Hbit_one].
    + assert (Hhit_next_zero : hit (station + 1) = 0) by lia.
      destruct (Hbit_bool (station + 1) ltac:(lia)) as
        [Hnext_bit_zero | Hnext_bit_one].
      * pose proof (Hzero_hit (station + 1) ltac:(lia) Hnext_bit_zero).
        congruence.
      * exfalso.
        apply (Hmax (station + 1) ltac:(lia)).
        unfold RecordResetStart.
        split; [lia |].
        split.
        -- replace (station + 1 - 1) with station by lia.
           exact Hbit_zero.
        -- split; [exact Hnext_bit_one | exact Hhit_next_zero].
    + exact Hbit_one.
  - right. left. tauto.
  - right. right. split; [exact Hequal |].
    destruct Hor as [[[Hhit_one | Hbit_one] Hnext] |
      [Hhit_zero [Hbit_zero Hnext]]].
    + exact Hnext.
    + exact Hnext.
    + pose proof (Hzero_hit station ltac:(lia) Hbit_zero).
      congruence.
Qed.

Lemma record_suffix_hit_one_persists__normalization :
  forall last bit hit start current_arrivals latest station,
    1 <= start ->
    start <= station < last ->
    (forall j, 0 <= j <= last -> bit j = 0 \/ bit j = 1) ->
    (forall j, 0 <= j <= last -> hit j = 0 \/ hit j = 1) ->
    (forall j, start <= j <= last -> bit j = 0 -> hit j = 1) ->
    (forall later, start < later <= last ->
       RecordResetStart bit hit later -> False) ->
    ChainCutHitStep current_arrivals latest station
      (bit station) (hit station) (hit (station + 1)) ->
    hit station = 1 ->
    hit (station + 1) = 1.
Proof.
  intros last bit hit start current_arrivals latest station
    Hstart Hstation Hbit_bool Hhit_bool Hzero_hit Hmax Hstep Hhit_one.
  pose proof (record_after_last_reset_suffix_step__normalization
    last bit hit start current_arrivals latest station
    Hstart Hstation Hbit_bool Hhit_bool Hzero_hit Hmax Hstep) as Hcases.
  destruct Hcases as [[Hwait Hnext] | [[Hbusy Hnext] | [Hequal Hnext]]];
    lia.
Qed.

Lemma record_hit_step_zero_carry__normalization :
  forall current_arrivals latest station bit hit next_hit,
    ChainCutHitStep current_arrivals latest station bit hit next_hit ->
    bit = 0 -> hit = 0 -> next_hit = 0.
Proof.
  intros current_arrivals latest station bit hit next_hit
    Hstep Hbit Hhit.
  unfold ChainCutHitStep in Hstep.
  destruct Hstep as
    [[Hwait Hnext] | [[Hbusy Hnext] | [Hequal Hor]]].
  - lia.
  - lia.
  - destruct Hor as [[[Hhit_one | Hbit_one] Hnext] |
      [Hhit_zero [Hbit_zero Hnext]]]; lia.
Qed.

Lemma record_suffix_zero_transition_busy__normalization :
  forall last bit hit start current_arrivals latest station,
    1 <= start ->
    start <= station < last ->
    (forall j, 0 <= j <= last -> bit j = 0 \/ bit j = 1) ->
    (forall j, 0 <= j <= last -> hit j = 0 \/ hit j = 1) ->
    (forall j, start <= j <= last -> bit j = 0 -> hit j = 1) ->
    (forall later, start < later <= last ->
       RecordResetStart bit hit later -> False) ->
    ChainCutHitStep current_arrivals latest station
      (bit station) (hit station) (hit (station + 1)) ->
    hit station = 0 ->
    hit (station + 1) = 0 ->
    Znth station latest 0 < Znth station current_arrivals 0.
Proof.
  intros last bit hit start current_arrivals latest station
    Hstart Hstation Hbit_bool Hhit_bool Hzero_hit Hmax Hstep
    Hhit_zero Hnext_zero.
  pose proof (record_after_last_reset_suffix_step__normalization
    last bit hit start current_arrivals latest station
    Hstart Hstation Hbit_bool Hhit_bool Hzero_hit Hmax Hstep) as Hcases.
  destruct Hcases as [[Hwait Hnext] | [[Hbusy Hnext] | [Hequal Hnext]]];
    [lia | exact Hbusy | lia].
Qed.

Lemma record_suffix_zero_to_one_barrier__normalization :
  forall last bit hit start current_arrivals latest station,
    1 <= start ->
    start <= station < last ->
    (forall j, 0 <= j <= last -> bit j = 0 \/ bit j = 1) ->
    (forall j, 0 <= j <= last -> hit j = 0 \/ hit j = 1) ->
    (forall j, start <= j <= last -> bit j = 0 -> hit j = 1) ->
    (forall later, start < later <= last ->
       RecordResetStart bit hit later -> False) ->
    ChainCutHitStep current_arrivals latest station
      (bit station) (hit station) (hit (station + 1)) ->
    hit station = 0 ->
    hit (station + 1) = 1 ->
    Znth station current_arrivals 0 <= Znth station latest 0.
Proof.
  intros last bit hit start current_arrivals latest station
    Hstart Hstation Hbit_bool Hhit_bool Hzero_hit Hmax Hstep
    Hhit_zero Hnext_one.
  pose proof (record_after_last_reset_suffix_step__normalization
    last bit hit start current_arrivals latest station
    Hstart Hstation Hbit_bool Hhit_bool Hzero_hit Hmax Hstep) as Hcases.
  destruct Hcases as [[Hwait Hnext] | [[Hbusy Hnext] | [Hequal Hnext]]];
    [lia | lia | lia].
Qed.

Lemma record_one_run__normalization :
  forall last hit lo hi,
    0 <= lo /\ lo <= hi /\ hi <= last ->
    hit lo = 1 ->
    (forall station, lo <= station < hi ->
       hit station = 1 -> hit (station + 1) = 1) ->
    hit hi = 1.
Proof.
  intros last hit lo hi Hrange Hhit Hstep.
  remember (Z.to_nat (hi - lo)) as fuel eqn:Hfuel.
  assert (Hhi : hi = lo + Z.of_nat fuel) by lia.
  subst hi. clear Hfuel.
  induction fuel as [|fuel IH].
  - cbn. replace (lo + 0) with lo by lia. exact Hhit.
  - rewrite Nat2Z.inj_succ. unfold Z.succ.
    replace (lo + (Z.of_nat fuel + 1))
      with ((lo + Z.of_nat fuel) + 1) by ring.
    apply Hstep.
    + lia.
    + apply IH; try lia.
      intros station Hstation.
      apply Hstep. lia.
Qed.

Lemma record_last_reset_edge_benefit__normalization :
  forall n counts current_dist next_dist latest current_arrivals next_arrivals
         start,
    2 <= n ->
    ChainUnitCutPath n current_dist next_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    BusArrivalSchedule n next_dist latest next_arrivals ->
    1 <= start <= n - 1 ->
    RecordResetStart
      (ChainCutBitValue current_dist next_dist)
      (ChainCutHitValue
        current_dist next_dist current_arrivals next_arrivals)
      start ->
    (forall later, start < later <= n - 1 ->
       RecordResetStart
         (ChainCutBitValue current_dist next_dist)
         (ChainCutHitValue
           current_dist next_dist current_arrivals next_arrivals)
         later -> False) ->
    exists benefit,
      EdgeMarginalBenefit
        n counts latest current_arrivals (start - 1) benefit /\
      sum (fun station => start <= station < n)
          (fun station =>
             Znth station counts 0 *
             (ChainCutHitValue
                current_dist next_dist current_arrivals next_arrivals station - 1)) =
        - benefit.
Proof.
  intros n counts current_dist next_dist latest current_arrivals next_arrivals
    start Hn Hpath Hcurrent_schedule Hnext_schedule Hstart Hreset Hmax.
  set (bit := ChainCutBitValue current_dist next_dist).
  set (hit := ChainCutHitValue
    current_dist next_dist current_arrivals next_arrivals).
  assert (Hbit_bool : forall station, 0 <= station <= n - 1 ->
    bit station = 0 \/ bit station = 1).
  {
    intros station Hstation.
    unfold bit.
    apply (proj1 (chain_unit_cut_values_boolean__record_cut
      n current_dist next_dist latest current_arrivals next_arrivals
      ltac:(lia) Hpath Hcurrent_schedule Hnext_schedule station ltac:(lia))).
  }
  assert (Hhit_bool : forall station, 0 <= station <= n - 1 ->
    hit station = 0 \/ hit station = 1).
  {
    intros station Hstation.
    unfold hit.
    apply (proj2 (chain_unit_cut_values_boolean__record_cut
      n current_dist next_dist latest current_arrivals next_arrivals
      ltac:(lia) Hpath Hcurrent_schedule Hnext_schedule station ltac:(lia))).
  }
  assert (Hsteps : forall station, 0 <= station < n - 1 ->
    ChainCutHitStep current_arrivals latest station
      (bit station) (hit station) (hit (station + 1))).
  {
    intros station Hstation.
    unfold bit, hit.
    eapply chain_unit_cut_values_step__record_cut
      with (n := n) (current_dist := current_dist)
           (next_dist := next_dist) (next_arrivals := next_arrivals).
    - lia.
    - exact Hstation.
    - exact Hpath.
    - exact Hcurrent_schedule.
    - exact Hnext_schedule.
  }
  assert (Hbit_last : bit (n - 1) = 1).
  {
    unfold bit, ChainCutBitValue.
    unfold ChainUnitCutPath in Hpath.
    destruct Hpath as [Hpointwise Hendpoint].
    lia.
  }
  assert (Hzero_hit : forall station, start <= station <= n - 1 ->
    bit station = 0 -> hit station = 1).
  {
    intros station Hstation Hbit_station.
    destruct (Z.eq_dec start (n - 1)) as [Hstart_last | Hstart_before].
    - assert (station = n - 1) by lia.
      subst station. congruence.
    - eapply (record_after_last_reset_zero_is_hit__normalization
        (n - 1) bit hit start ltac:(lia) Hbit_bool Hhit_bool
        ltac:(intros j Hj Hbj Hhj;
          eapply record_hit_step_zero_carry__normalization;
          [apply Hsteps; lia | exact Hbj | exact Hhj])
        Hbit_last ltac:(lia) ltac:(lia) Hmax station Hstation
        Hbit_station).
  }
  assert (Hpersistent : forall station, start <= station < n - 1 ->
    hit station = 1 -> hit (station + 1) = 1).
  {
    intros station Hstation Hhit_station.
    eapply (record_suffix_hit_one_persists__normalization
      (n - 1) bit hit start current_arrivals latest station
      ltac:(lia) Hstation Hbit_bool Hhit_bool Hzero_hit Hmax
      (Hsteps station ltac:(lia)) Hhit_station).
  }
  unfold RecordResetStart in Hreset.
  destruct Hreset as
    [Hstart_positive [Hbit_before [Hbit_start Hhit_start]]].
  change (bit (start - 1) = 0) in Hbit_before.
  change (bit start = 1) in Hbit_start.
  change (hit start = 0) in Hhit_start.
  destruct (prop_dec (exists station,
    start < station <= n - 1 /\ hit station = 1)) as
    [Hhas_one | Hno_one].
  - set (width := n - 1 - start - 1).
    assert (Hwidth : 0 <= width) by
      (destruct Hhas_one as [witness [Hwitness Hhit_witness]];
       unfold width; lia).
    assert (Hexists_offset : exists offset,
      0 <= offset <= width /\ hit (start + 1 + offset) = 1).
    {
      destruct Hhas_one as [witness [Hwitness Hhit_witness]].
      exists (witness - (start + 1)).
      split; [unfold width; lia |].
      replace (start + 1 + (witness - (start + 1)))
        with witness by ring.
      exact Hhit_witness.
    }
    destruct (min_n_in_range
      (fun offset => hit (start + 1 + offset) = 1)
      width Hwidth Hexists_offset) as
      [offset [Hoffset_hit [Hoffset_range Hoffset_min]]].
    set (high := start + 1 + offset).
    assert (Hhigh : start < high <= n - 1) by
      (unfold high, width in *; lia).
    assert (Hbefore_zero : forall station, start <= station < high ->
      hit station = 0).
    {
      intros station Hstation.
      destruct (Hhit_bool station ltac:(lia)) as [Hzero | Hone];
        [exact Hzero |].
      destruct (Z.eq_dec station start) as [-> | Hneq];
        [congruence |].
      assert (Hstation_offset :
        0 <= station - (start + 1) <= width) by
        (unfold width; lia).
      specialize (Hoffset_min (station - (start + 1)) Hstation_offset).
      replace (start + 1 + (station - (start + 1)))
        with station in Hoffset_min by ring.
      specialize (Hoffset_min Hone).
      unfold high in Hstation.
      lia.
    }
    assert (Hafter_one : forall station, high <= station <= n - 1 ->
      hit station = 1).
    {
      intros station Hstation.
      eapply record_one_run__normalization
        with (last := n - 1) (lo := high).
      - lia.
      - unfold high. exact Hoffset_hit.
      - intros j Hj.
        apply Hpersistent. lia.
    }
    set (benefit := sum (fun station => start <= station < high)
      (fun station => Znth station counts 0)).
    exists benefit.
    split.
    + rewrite EdgeMarginalBenefit_unfold.
      exists high.
      split; [lia |].
      split.
      * intros station Hstation.
        eapply record_suffix_zero_transition_busy__normalization
          with (last := n - 1) (bit := bit) (hit := hit)
               (start := start); try eassumption.
        -- lia.
        -- apply Hsteps. lia.
        -- apply Hbefore_zero. lia.
        -- apply Hbefore_zero. lia.
      * split.
        -- right.
           eapply record_suffix_zero_to_one_barrier__normalization
             with (last := n - 1) (bit := bit) (hit := hit)
                  (start := start); try eassumption.
           ++ lia.
           ++ apply Hsteps. lia.
           ++ apply Hbefore_zero. lia.
           ++ replace (high - 1 + 1) with high by lia.
              unfold high. exact Hoffset_hit.
        -- replace (start - 1 + 1) with start by lia.
           unfold benefit. reflexivity.
    + rewrite (sum_Z_range_split start high n
        (fun station =>
           Znth station counts 0 * (hit station - 1))) by lia.
      rewrite (sum_Z_range_ext start high
        (fun station => Znth station counts 0 * (hit station - 1))
        (fun station => - Znth station counts 0)).
      2: { intros station Hstation. rewrite Hbefore_zero by lia. ring. }
      rewrite (sum_Z_range_ext high n
        (fun station => Znth station counts 0 * (hit station - 1))
        (fun _ => 0)).
      2: { intros station Hstation. rewrite Hafter_one by lia. ring. }
      assert (Hzero_sum :
        sum (fun station => high <= station < n) (fun _ => 0) = 0).
      {
        apply sum_Z_range_eq_zero.
        intros station Hstation. reflexivity.
      }
      rewrite Hzero_sum.
      unfold benefit.
      rewrite <- sum_opp.
      ring.
  - assert (Hall_zero : forall station, start <= station <= n - 1 ->
      hit station = 0).
    {
      intros station Hstation.
      destruct (Hhit_bool station ltac:(lia)) as [Hzero | Hone];
        [exact Hzero |].
      destruct (Z.eq_dec station start) as [-> | Hneq];
        [congruence |].
      exfalso. apply Hno_one.
      exists station. split; [lia | exact Hone].
    }
    set (benefit := sum (fun station => start <= station < n)
      (fun station => Znth station counts 0)).
    exists benefit.
    split.
    + rewrite EdgeMarginalBenefit_unfold.
      exists n.
      split; [lia |].
      split.
      * intros station Hstation.
        eapply record_suffix_zero_transition_busy__normalization
          with (last := n - 1) (bit := bit) (hit := hit)
               (start := start); try eassumption.
        -- lia.
        -- apply Hsteps. lia.
        -- apply Hall_zero. lia.
        -- apply Hall_zero. lia.
      * split; [left; reflexivity |].
        replace (start - 1 + 1) with start by lia.
        unfold benefit. reflexivity.
    + rewrite (sum_Z_range_ext start n
        (fun station =>
           Znth station counts 0 * (hit station - 1))
        (fun station => - Znth station counts 0)).
      2: { intros station Hstation. rewrite Hall_zero by lia. ring. }
      unfold benefit.
      rewrite <- sum_opp.
      ring.
Qed.

Lemma best_boost_choice_bounds_edge__normalization :
  forall n dist counts latest arrivals best position edge benefit,
    BestBoostChoice n dist counts latest arrivals best position ->
    0 <= edge < n - 1 ->
    0 < Znth edge dist 0 ->
    EdgeMarginalBenefit n counts latest arrivals edge benefit ->
    benefit <= best.
Proof.
  intros n dist counts latest arrivals best position edge benefit
    Hchoice Hedge Hpositive Hbenefit.
  unfold BestBoostChoice, EdgeChoicePrefix in Hchoice.
  destruct Hchoice as [Hmaximum Hposition].
  pose proof (max_default_Z_bounds_source__cut_exchange
    (Z * Z)
    (EligibleEdgeBenefit n dist counts latest arrivals (n - 1))
    (fun choice : Z * Z => snd choice) 0 best Hmaximum)
    as [Hdefault [Hbound Hsource]].
  specialize (Hbound (edge, benefit)).
  cbn in Hbound.
  apply Hbound.
  unfold EligibleEdgeBenefit.
  cbn.
  repeat split; try assumption; lia.
Qed.

Lemma chain_unit_cut_path_lower_bound__normalization :
  forall n m budget initial_dist times origins destinations latest counts
         current_dist next_dist current_arrivals next_arrivals
         current_total next_total best position,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    DestinationCounts n m destinations counts ->
    FeasibleBoostedDistances n budget initial_dist current_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    PassengerTravelTotal
      m times destinations current_arrivals current_total ->
    SightseeingMinimumTotal
      n m budget initial_dist times origins destinations current_total ->
    FeasibleBoostedDistances n (budget + 1) initial_dist next_dist ->
    BusArrivalSchedule n next_dist latest next_arrivals ->
    PassengerTravelTotal m times destinations next_arrivals next_total ->
    ChainUnitCutPath n current_dist next_dist ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge current_dist 0) = budget ->
    BestBoostChoice
      n current_dist counts latest current_arrivals best position ->
    current_total - best <= next_total.
Proof.
  intros n m budget initial_dist times origins destinations latest counts
    current_dist next_dist current_arrivals next_arrivals
    current_total next_total best position
    Hinputs Hlatest Hcounts Hcurrent_feasible Hcurrent_schedule
    Hcurrent_total Hminimum Hnext_feasible Hnext_schedule Hnext_total
    Hpath Hcurrent_used Hchoice.
  assert (Hn : 2 <= n).
  { unfold SightseeingInputsBounded in Hinputs. lia. }
  set (bit := ChainCutBitValue current_dist next_dist).
  set (hit := ChainCutHitValue
    current_dist next_dist current_arrivals next_arrivals).
  assert (Hbit_bool : forall station, 0 <= station <= n - 1 ->
    bit station = 0 \/ bit station = 1).
  {
    intros station Hstation.
    unfold bit.
    apply (proj1 (chain_unit_cut_values_boolean__record_cut
      n current_dist next_dist latest current_arrivals next_arrivals
      ltac:(lia) Hpath Hcurrent_schedule Hnext_schedule station ltac:(lia))).
  }
  assert (Hhit_bool : forall station, 0 <= station <= n - 1 ->
    hit station = 0 \/ hit station = 1).
  {
    intros station Hstation.
    unfold hit.
    apply (proj2 (chain_unit_cut_values_boolean__record_cut
      n current_dist next_dist latest current_arrivals next_arrivals
      ltac:(lia) Hpath Hcurrent_schedule Hnext_schedule station ltac:(lia))).
  }
  assert (Hsteps : forall station, 0 <= station < n - 1 ->
    ChainCutHitStep current_arrivals latest station
      (bit station) (hit station) (hit (station + 1))).
  {
    intros station Hstation.
    unfold bit, hit.
    eapply chain_unit_cut_values_step__record_cut;
      try eassumption; lia.
  }
  assert (Hcarry : forall station, 0 <= station < n - 1 ->
    bit station = 0 -> hit station = 0 -> hit (station + 1) = 0).
  {
    intros station Hstation Hbit_station Hhit_station.
    eapply record_hit_step_zero_carry__normalization.
    - apply Hsteps. exact Hstation.
    - exact Hbit_station.
    - exact Hhit_station.
  }
  assert (Hbit_zero : bit 0 = 0).
  {
    unfold bit, ChainCutBitValue.
    rewrite !chain_interval_empty__cut_exchange by lia.
    lia.
  }
  assert (Hbit_last : bit (n - 1) = 1).
  {
    unfold bit, ChainCutBitValue, ChainUnitCutPath in *.
    destruct Hpath as [Hpointwise Hendpoint].
    lia.
  }
  assert (Hhit_zero : hit 0 = 0).
  {
    unfold hit, ChainCutHitValue, ChainCutBitValue.
    rewrite !chain_interval_empty__cut_exchange by lia.
    destruct Hcurrent_schedule as [_ [Hcurrent_zero _]].
    destruct Hnext_schedule as [_ [Hnext_zero _]].
    lia.
  }
  assert (Hweight : forall station, 0 <= station <= n - 1 ->
    0 <= Znth station counts 0).
  {
    intros station Hstation.
    eapply destination_counts_nonnegative__cut_exchange;
      [exact Hcounts | lia].
  }
  destruct (record_terminal_path_suffix_bound__normalization
    (n - 1) (fun station => Znth station counts 0) bit hit
    ltac:(lia) Hbit_zero Hbit_last Hhit_zero Hbit_bool Hhit_bool
    Hweight Hcarry) as
    [start [Hstart [Hreset [Hlast_reset Hsuffix_bound]]]].
  - intros reset_start Hreset_range Hreset_start.
    unfold bit, hit in Hreset_start |-.
    eapply record_reset_prefix_nonnegative__normalization;
      try eassumption.
  - destruct (record_last_reset_edge_benefit__normalization
      n counts current_dist next_dist latest current_arrivals next_arrivals
      start Hn Hpath Hcurrent_schedule Hnext_schedule Hstart Hreset
      Hlast_reset) as [benefit [Hbenefit Hsuffix_effect]].
    assert (Hedge_range : 0 <= start - 1 < n - 1) by lia.
    pose proof Hnext_feasible as Hnext_bounds_fields.
    rewrite FeasibleBoostedDistances_unfold in Hnext_bounds_fields.
    destruct Hnext_bounds_fields as [_ [Hnext_bounds Hnext_budget]].
    assert (Hedge_positive : 0 < Znth (start - 1) current_dist 0).
    {
      unfold RecordResetStart in Hreset.
      destruct Hreset as
        [Hstart_positive [Hbit_before [Hbit_start Hhit_start]]].
      unfold bit, ChainCutBitValue in Hbit_before, Hbit_start.
      pose proof (chain_prefix_increment__cut_exchange
        current_dist (start - 1) ltac:(lia)) as Hcurrent_increment.
      pose proof (chain_prefix_increment__cut_exchange
        next_dist (start - 1) ltac:(lia)) as Hnext_increment.
      replace (start - 1 + 1) with start in
        Hcurrent_increment, Hnext_increment by lia.
      pose proof (Hnext_bounds (start - 1) Hedge_range).
      lia.
    }
    pose proof (best_boost_choice_bounds_edge__normalization
      n current_dist counts latest current_arrivals best position
      (start - 1) benefit Hchoice Hedge_range Hedge_positive Hbenefit)
      as Hbenefit_best.
    pose proof (chain_record_cut_effect_total__record_cut
      n m initial_dist times origins destinations counts
      current_dist next_dist current_arrivals next_arrivals
      current_total next_total Hinputs Hcounts Hcurrent_total Hnext_total)
      as Heffect.
    unfold ChainRecordCutEffect in Heffect.
    change (next_total - current_total =
      sum (fun station => 1 <= station < n)
          (fun station =>
             Znth station counts 0 * (hit station - bit station)))
      in Heffect.
    change (
      sum (fun station => start <= station < n)
          (fun station => Znth station counts 0 * (hit station - 1)) =
      - benefit) in Hsuffix_effect.
    replace (n - 1 + 1) with n in Hsuffix_bound by lia.
    lia.
Qed.

Lemma selected_exchange_certificate_from_repair__normalization :
  forall n m budget remaining initial_dist times origins destinations
         old_dist latest counts old_arrivals
         new_dist new_arrivals best position,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    BoosterProgress n m budget remaining
      initial_dist times origins destinations
      old_dist latest counts old_arrivals ->
    0 < best ->
    BestBoostChoice n old_dist counts latest old_arrivals best position ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    Zlength new_dist = n - 1 ->
    Zlength new_arrivals = n ->
    SelectedExchangeCertificate
      n m budget remaining initial_dist times origins destinations
      old_dist latest counts old_arrivals best.
Proof.
  intros n m budget remaining initial_dist times origins destinations
    old_dist latest counts old_arrivals new_dist new_arrivals best position
    Hinputs Hprogress Hbest Hchoice Houtcome
    Hnew_dist_length Hnew_arrivals_length.
  pose proof Hprogress as Hfields.
  unfold BoosterProgress in Hfields.
  destruct Hfields as
    [Hlatest [Hcounts [Hfeasible [Hschedule
      [current_total [Hcurrent_total Hminimum]]]]]].
  pose proof (booster_progress_budget_saturated__saturation
    n m budget remaining initial_dist times origins destinations
    old_dist latest counts old_arrivals new_dist new_arrivals best position
    Hinputs Hprogress Hbest Hchoice Houtcome
    Hnew_dist_length Hnew_arrivals_length) as Hcurrent_used.
  unfold SelectedExchangeCertificate.
  split; [lia |].
  exists current_total.
  split; [exact Hcurrent_total |].
  intros candidate_total Hcandidate.
  unfold SightseeingCandidateTotal in Hcandidate.
  destruct Hcandidate as
    [candidate_dist [candidate_latest [candidate_arrivals
      [Hcandidate_latest [Hcandidate_feasible
        [Hcandidate_schedule Hcandidate_total]]]]]].
  assert (Hlatest_pointwise : forall station, 0 <= station < n ->
    Znth station candidate_latest 0 = Znth station latest 0).
  {
    intros station Hstation.
    symmetry.
    eapply latest_departures_pointwise_unique__chain_dual; eauto.
  }
  assert (Hcandidate_schedule_current :
    BusArrivalSchedule n candidate_dist latest candidate_arrivals).
  {
    eapply bus_schedule_latest_ext__chain_dual.
    - intros station Hstation.
      apply Hlatest_pointwise. exact Hstation.
    - exact Hcandidate_schedule.
  }
  pose proof Hcandidate_feasible as Hcandidate_fields.
  rewrite FeasibleBoostedDistances_unfold in Hcandidate_fields.
  destruct Hcandidate_fields as
    [Hcandidate_length [Hcandidate_bounds Hcandidate_used_le]].
  set (candidate_used :=
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge candidate_dist 0)).
  destruct (Z_le_gt_dec candidate_used (budget - remaining)) as
    [Hold_budget | Hnext_exact].
  - assert (Hcandidate_old_feasible :
      FeasibleBoostedDistances
        n (budget - remaining) initial_dist candidate_dist).
    {
      rewrite FeasibleBoostedDistances_unfold.
      split; [exact Hcandidate_length |].
      split; [exact Hcandidate_bounds |].
      unfold candidate_used in Hold_budget.
      exact Hold_budget.
    }
    assert (Hcandidate_old :
      SightseeingCandidateTotal
        n m (budget - remaining)
        initial_dist times origins destinations candidate_total).
    {
      exists candidate_dist, candidate_latest, candidate_arrivals.
      exact (conj Hcandidate_latest
        (conj Hcandidate_old_feasible
          (conj Hcandidate_schedule Hcandidate_total))).
    }
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset in Hminimum.
    destruct Hminimum as [witness [[Hwitness Hleast] Hvalue]].
    cbn in Hvalue. subst witness.
    specialize (Hleast candidate_total Hcandidate_old).
    cbn in Hleast. lia.
  - assert (Hcandidate_used :
      candidate_used = budget - remaining + 1) by
      (unfold candidate_used in *; lia).
    destruct (chain_candidate_uncross_to_unit__cut_exchange
      n m (budget - remaining)
      initial_dist times origins destinations latest counts
      old_dist old_arrivals current_total
      candidate_dist candidate_arrivals candidate_total
      Hinputs Hlatest Hcounts Hfeasible Hschedule Hcurrent_total Hminimum
      Hcandidate_feasible Hcandidate_schedule_current Hcandidate_total
      Hcurrent_used Hcandidate_used) as
      [unit_dist [unit_arrivals [unit_total
        [Hunit_feasible [Hunit_schedule [Hunit_total
          [Hunit_path Hunit_upper]]]]]]].
    pose proof (chain_unit_cut_path_lower_bound__normalization
      n m (budget - remaining)
      initial_dist times origins destinations latest counts
      old_dist unit_dist old_arrivals unit_arrivals
      current_total unit_total best position
      Hinputs Hlatest Hcounts Hfeasible Hschedule Hcurrent_total Hminimum
      Hunit_feasible Hunit_schedule Hunit_total Hunit_path
      Hcurrent_used Hchoice) as Hunit_lower.
    lia.
Qed.

Lemma best_boost_choice_positive_edge__exchange_certificate_transition :
  forall n dist counts latest arrivals best position,
    0 < best ->
    BestBoostChoice n dist counts latest arrivals best position ->
    0 <= position < n - 1 /\ 0 < Znth position dist 0.
Proof.
  intros n dist counts latest arrivals best position Hbest Hchoice.
  unfold BestBoostChoice, EdgeChoicePrefix in Hchoice.
  destruct Hchoice as [Hmaximum Hposition].
  destruct Hposition as [[Hbest_zero Hposition] | Heligible].
  - lia.
  - unfold EligibleEdgeBenefit in Heligible.
    cbn in Heligible.
    tauto.
Qed.
Lemma sum_Z_range_filter_indicator__exchange_certificate_transition :
  forall low high (P : Z -> Prop) f,
    sum (fun x => low <= x < high /\ P x) f =
    sum (fun x => low <= x < high)
        (fun x => if prop_dec (P x) then f x else 0).
Proof.
  intros low high P f.
  unfold sum.
  simpl.
  induction (Zrange low high) as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (prop_dec (P x)); simpl; rewrite IH; ring.
Qed.
Lemma latest_at_station_bounds__exchange_certificate_transition :
  forall n m initial_dist times origins destinations latest station,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    0 <= station < n ->
    0 <= Znth station latest 0 <= 100000.
Proof.
  intros n m initial_dist times origins destinations latest station
    Hinputs Hlatest Hstation.
  unfold LatestDepartures in Hlatest.
  destruct Hlatest as [_ Hlatest].
  specialize (Hlatest station Hstation).
  unfold LatestAtStation, MaxMin.max_value_of_subset_with_default in Hlatest.
  destruct Hlatest as [[Hmaximum Hdefault] | [Hall Hdefault]].
  - destruct Hmaximum as [passenger [Hobject Hvalue]].
    destruct Hobject as [Hmember Hgreatest].
    destruct Hmember as [Hpassenger Horigin].
    unfold SightseeingInputsBounded in Hinputs.
    destruct Hinputs as [_ [_ [_ [_ [_ [_ [_ Hpassenger_bounds]]]]]]].
    specialize (Hpassenger_bounds passenger Hpassenger).
    cbn in Hvalue.
    lia.
  - cbn in Hdefault.
    lia.
Qed.
Lemma destination_count_bounds__exchange_certificate_transition :
  forall n m destinations counts station,
    0 <= m ->
    DestinationCounts n m destinations counts ->
    0 <= station < n ->
    0 <= Znth station counts 0 <= m.
Proof.
  intros n m destinations counts station Hm Hcounts Hstation.
  unfold DestinationCounts in Hcounts.
  destruct Hcounts as [_ Hcounts].
  specialize (Hcounts station Hstation).
  rewrite Hcounts.
  rewrite sum_Z_range_filter_indicator__exchange_certificate_transition.
  split.
  - eapply Z.le_trans with (m := (m - 0) * 0); [lia |].
    apply sum_Z_range_lower_bound; [lia |].
    intros passenger Hpassenger.
    destruct (prop_dec (Znth passenger destinations 0 = station + 1));
      cbn; lia.
  - eapply Z.le_trans with (m := (m - 0) * 1).
    + apply sum_Z_range_upper_bound; [lia |].
      intros passenger Hpassenger.
      destruct (prop_dec (Znth passenger destinations 0 = station + 1));
        cbn; lia.
    + lia.
Qed.
Lemma station_departure_bounds__exchange_certificate_transition :
  forall arrivals latest station departure upper,
    StationDeparture arrivals latest station departure ->
    0 <= Znth station arrivals 0 <= upper ->
    0 <= Znth station latest 0 <= upper ->
    0 <= departure <= upper.
Proof.
  intros arrivals latest station departure upper Hdeparture
    Harrival Hlatest.
  unfold StationDeparture, MaxMin.max_value_of_subset_with_default in Hdeparture.
  destruct Hdeparture as [[Hmaximum Hdefault] | [Hall Hdefault]].
  - destruct Hmaximum as [candidate [Hobject Hvalue]].
    destruct Hobject as [Hmember Hgreatest].
    change (candidate = Znth station latest 0) in Hmember.
    cbn in Hvalue.
    lia.
  - cbn in Hdefault.
    subst departure.
    exact Harrival.
Qed.
Lemma bus_arrival_step_nondec__exchange_certificate_transition :
  forall n dist latest arrivals station,
    BusArrivalSchedule n dist latest arrivals ->
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge dist 0) ->
    0 <= station < n - 1 ->
    Znth station arrivals 0 <= Znth (station + 1) arrivals 0.
Proof.
  intros n dist latest arrivals station Hschedule Hdist Hstation.
  destruct Hschedule as [_ [_ Hnext]].
  specialize (Hnext station Hstation).
  destruct Hnext as [departure [Hdeparture Harrival]].
  unfold StationDeparture,
    MaxMin.max_value_of_subset_with_default in Hdeparture.
  assert (Hdeparture_default : Znth station arrivals 0 <= departure).
  {
    destruct Hdeparture as [[_ Hdefault] | [_ Heq]].
    - exact Hdefault.
    - lia.
  }
  specialize (Hdist station Hstation).
  lia.
Qed.
Lemma bus_arrivals_nondecreasing__exchange_certificate_transition :
  forall n dist latest arrivals lo hi,
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge dist 0) ->
    BusArrivalSchedule n dist latest arrivals ->
    0 <= lo -> lo <= hi -> hi < n ->
    Znth lo arrivals 0 <= Znth hi arrivals 0.
Proof.
  intros n dist latest arrivals lo hi Hdist Hschedule Hlo Hlohi Hhi.
  assert (Hnat : forall d : nat,
    lo + Z.of_nat d < n ->
    Znth lo arrivals 0 <= Znth (lo + Z.of_nat d) arrivals 0).
  {
    induction d as [|d IH].
    - intros _.
      replace (lo + Z.of_nat 0) with lo by lia.
      apply Z.le_refl.
    - intros Hd.
      replace (lo + Z.of_nat (S d))
        with ((lo + Z.of_nat d) + 1) by lia.
      eapply Z.le_trans.
      + apply IH; lia.
      + eapply bus_arrival_step_nondec__exchange_certificate_transition;
          eauto; lia.
  }
  specialize (Hnat (Z.to_nat (hi - lo))).
  replace (lo + Z.of_nat (Z.to_nat (hi - lo))) with hi in Hnat by lia.
  apply Hnat; exact Hhi.
Qed.
Lemma booster_progress_arrival_bounds__exchange_certificate_transition :
  forall n m budget remaining initial_dist times origins destinations
         final_dist latest counts arrivals,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    BoosterProgress n m budget remaining
      initial_dist times origins destinations
      final_dist latest counts arrivals ->
    forall station, 0 <= station < n ->
      0 <= Znth station arrivals 0 <= 200000.
Proof.
  intros n m budget remaining initial_dist times origins destinations
    final_dist latest counts arrivals Hinputs Hprogress station Hstation.
  pose proof Hinputs as Hinput_bounds.
  unfold SightseeingInputsBounded in Hinput_bounds.
  destruct Hinput_bounds as
    [Hn [Hm [Hinitial_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hinitial_bounds Hpassenger_bounds]]]]]]].
  unfold BoosterProgress in Hprogress.
  destruct Hprogress as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]].
  try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  destruct Hfeasible as [Hfinal_len [Hfinal_bounds Hbudget]].
  destruct Hschedule as [Harrival_len [Harrival_zero Harrival_step]].
  assert (Hstrong : forall j, 0 <= j < n ->
      0 <= Znth j arrivals 0 <= 100000 + 100 * j).
  {
    intros j Hj.
    assert (Hrepr : j = Z.of_nat (Z.to_nat j)).
    { rewrite Z2Nat.id; lia. }
    rewrite Hrepr in *.
    remember (Z.to_nat j) as j_nat.
    clear j Hrepr Heqj_nat.
    induction j_nat as [|j_nat IH].
    - cbn.
      rewrite Harrival_zero.
      lia.
    - rewrite Nat2Z.inj_succ in *.
      assert (Hprevious_range : 0 <= Z.of_nat j_nat < n) by lia.
      specialize (IH ltac:(lia)).
      specialize (Harrival_step (Z.of_nat j_nat) ltac:(lia)).
      destruct Harrival_step as [departure [Hdeparture Harrival]].
      pose proof (latest_at_station_bounds__exchange_certificate_transition
        n m initial_dist times origins destinations latest
        (Z.of_nat j_nat) Hinputs Hlatest Hprevious_range) as Hlatest_bound.
      specialize (Hfinal_bounds (Z.of_nat j_nat) ltac:(lia)).
      specialize (Hinitial_bounds (Z.of_nat j_nat) ltac:(lia)).
      pose proof (station_departure_bounds__exchange_certificate_transition
        arrivals latest (Z.of_nat j_nat) departure
        (100000 + 100 * Z.of_nat j_nat)
        Hdeparture IH ltac:(lia)) as Hdeparture_bound.
      replace (Z.succ (Z.of_nat j_nat)) with
        (Z.of_nat j_nat + 1) by lia.
      rewrite Harrival.
      lia.
  }
  specialize (Hstrong station Hstation).
  lia.
Qed.
Lemma arrival_repair_outcome_distance_bounds__exchange_certificate_transition :
  forall n m budget remaining initial_dist times origins destinations
         old_dist old_arrivals new_dist new_arrivals latest counts best position,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    BoosterProgress n m budget remaining
      initial_dist times origins destinations
      old_dist latest counts old_arrivals ->
    0 < best ->
    BestBoostChoice n old_dist counts latest old_arrivals best position ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    forall edge, 0 <= edge < n - 1 ->
      0 <= Znth edge new_dist 0 <= 100.
Proof.
  intros n m budget remaining initial_dist times origins destinations
    old_dist old_arrivals new_dist new_arrivals latest counts best position
    Hinputs Hprogress Hbest Hchoice Houtcome edge Hedge.
  pose proof Hinputs as Hinput_bounds.
  unfold SightseeingInputsBounded in Hinput_bounds.
  destruct Hinput_bounds as
    [_ [_ [_ [_ [_ [_ [Hinitial_bounds _]]]]]]].
  pose proof Hprogress as Hprogress_bounds.
  unfold BoosterProgress in Hprogress_bounds.
  destruct Hprogress_bounds as
    [_ [_ [Hfeasible [_ _]]]].
  rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  destruct Hfeasible as [_ [Hold_bounds _]].
  pose proof (best_boost_choice_positive_edge__exchange_certificate_transition
    n old_dist counts latest old_arrivals best position Hbest Hchoice)
    as [Hposition_range Hposition_positive].
  rewrite ArrivalRepairOutcome_unfold in Houtcome.
  destruct Houtcome as
    [stop [Hstop [Hdistance [Hbefore [Hchanged Hfinish]]]]].
  specialize (Hdistance edge Hedge).
  specialize (Hold_bounds edge Hedge).
  specialize (Hinitial_bounds edge Hedge).
  destruct (Z.eq_dec edge position) as [Heq | Hne].
  - subst edge.
    destruct (Z.eq_dec position position) as [_ | Hcontra];
      [lia | contradiction].
  - destruct (Z.eq_dec edge position) as [Hcontra | _];
      [contradiction | lia].
Qed.
Lemma arrival_repair_outcome_bounds__exchange_certificate_transition :
  forall n m budget remaining initial_dist times origins destinations
         old_dist old_arrivals new_dist new_arrivals latest counts best position,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    BoosterProgress n m budget remaining
      initial_dist times origins destinations
      old_dist latest counts old_arrivals ->
    0 < best ->
    BestBoostChoice n old_dist counts latest old_arrivals best position ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    forall station, 0 <= station < n ->
      0 <= Znth station new_arrivals 0 <= 200000.
Proof.
  intros n m budget remaining initial_dist times origins destinations
    old_dist old_arrivals new_dist new_arrivals latest counts best position
    Hinputs Hprogress Hbest Hchoice Houtcome station Hstation.
  pose proof (booster_progress_arrival_bounds__exchange_certificate_transition
    n m budget remaining initial_dist times origins destinations
    old_dist latest counts old_arrivals Hinputs Hprogress) as Hold_bounds.
  pose proof (best_boost_choice_positive_edge__exchange_certificate_transition
    n old_dist counts latest old_arrivals best position Hbest Hchoice)
    as [Hposition_range Hposition_positive].
  pose proof Hprogress as Hprogress_fields.
  unfold BoosterProgress in Hprogress_fields.
  destruct Hprogress_fields as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]].
  try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  destruct Hfeasible as [Hdist_len [Hdist_bounds Hbudget]].
  assert (Hafter_position : forall j, position < j < n ->
      0 < Znth j old_arrivals 0).
  {
    intros j Hj.
    pose proof Hschedule as Hschedule_at_position.
    destruct Hschedule_at_position as [_ [_ Hstep]].
    specialize (Hstep position ltac:(lia)).
    destruct Hstep as [departure [Hdeparture Harrival]].
    assert (Hdeparture_nonnegative : 0 <= departure).
    {
      pose proof (Hold_bounds position ltac:(lia)) as Hposition_arrival.
      unfold StationDeparture,
        MaxMin.max_value_of_subset_with_default in Hdeparture.
      destruct Hdeparture as [[_ Hdefault] | [_ Heq]]; lia.
    }
    assert (Hnext_positive :
      0 < Znth (position + 1) old_arrivals 0) by lia.
    destruct (Z.eq_dec j (position + 1)) as [-> | Hneq].
    - exact Hnext_positive.
    - pose proof (bus_arrivals_nondecreasing__exchange_certificate_transition
        n old_dist latest old_arrivals (position + 1) j
        (fun edge Hedge => proj1 (Hdist_bounds edge Hedge)) Hschedule
        ltac:(lia) ltac:(lia) ltac:(lia)) as Hnondec.
      lia.
  }
  rewrite ArrivalRepairOutcome_unfold in Houtcome.
  destruct Houtcome as
    [stop [Hstop [Hdistance [Hbefore [Hchanged Hfinish]]]]].
  pose proof (Hold_bounds station Hstation) as Hold_station.
  destruct (Z_le_gt_dec station position) as [Hle | Hgt].
  - rewrite Hbefore by lia.
    exact Hold_station.
  - destruct (Z_lt_ge_dec station stop) as [Hlt | Hge].
    + specialize (Hchanged station ltac:(lia)).
      destruct Hchanged as [Heq Hlatest_new].
      pose proof (Hafter_position station ltac:(lia)).
      lia.
    + destruct Hfinish as [[Hstop_n Hall_changed] |
                           [Hstop_lt [Hstop_eq [Hguard Hafter]]]].
      * assert (station < stop) by lia.
        contradiction.
      * destruct (Z.eq_dec station stop) as [-> | Hneq].
        -- pose proof (Hafter_position stop ltac:(lia)).
           lia.
        -- rewrite Hafter by lia.
           exact Hold_station.
Qed.
Lemma sum_Z_range_single_indicator__exchange_certificate_transition :
  forall low high position,
    low <= position < high ->
    sum (fun edge => low <= edge < high)
        (fun edge => if Z.eq_dec edge position then 1 else 0) = 1.
Proof.
  intros low high position Hposition.
  rewrite (sum_Z_range_split low position high) by lia.
  assert (Hleft :
    sum (fun edge => low <= edge < position)
        (fun edge => if Z.eq_dec edge position then 1 else 0) = 0).
  {
    apply sum_Z_range_eq_zero.
    intros edge Hedge.
    destruct (Z.eq_dec edge position); [lia | reflexivity].
  }
  rewrite Hleft.
  rewrite sum_Z_range_cons by lia.
  assert (Hright :
    sum (fun edge => position + 1 <= edge < high)
        (fun edge => if Z.eq_dec edge position then 1 else 0) = 0).
  {
    apply sum_Z_range_eq_zero.
    intros edge Hedge.
    destruct (Z.eq_dec edge position); [lia | reflexivity].
  }
  rewrite Hright.
  destruct (Z.eq_dec position position); [lia | contradiction].
Qed.
Lemma feasible_boosted_distances_step__exchange_certificate_transition :
  forall n budget remaining initial_dist old_dist old_arrivals
         new_dist new_arrivals latest counts best position,
    Zlength new_dist = n - 1 ->
    0 < best ->
    BestBoostChoice n old_dist counts latest old_arrivals best position ->
    FeasibleBoostedDistances
      n (budget - remaining) initial_dist old_dist ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist new_arrivals latest position ->
    FeasibleBoostedDistances
      n (budget - (remaining - 1)) initial_dist new_dist.
Proof.
  intros n budget remaining initial_dist old_dist old_arrivals
    new_dist new_arrivals latest counts best position Hnew_dist_len
    Hbest Hchoice Hfeasible Houtcome.
  pose proof (best_boost_choice_positive_edge__exchange_certificate_transition
    n old_dist counts latest old_arrivals best position Hbest Hchoice)
    as [Hposition_range Hposition_positive].
  pose proof Houtcome as Houtcome_fields.
  rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  apply FeasibleBoostedDistances_unfold.
  try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  destruct Hfeasible as [Hold_dist_len [Hold_bounds Hold_budget]].
  rewrite ArrivalRepairOutcome_unfold in Houtcome_fields.
  destruct Houtcome_fields as
    [stop [Hstop [Hdistance [Hbefore [Hchanged Hfinish]]]]].
  split; [exact Hnew_dist_len |].
  split.
  - intros edge Hedge.
    specialize (Hold_bounds edge Hedge).
    specialize (Hdistance edge Hedge).
    destruct (Z.eq_dec edge position) as [Heq | Hne].
    + subst edge.
      destruct (Z.eq_dec position position) as [_ | Hcontra];
        [lia | contradiction].
    + destruct (Z.eq_dec edge position) as [Hcontra | _];
        [contradiction | lia].
  - assert (Hsum_step :
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge => Znth edge initial_dist 0 - Znth edge new_dist 0) =
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge => Znth edge initial_dist 0 - Znth edge old_dist 0) + 1).
    {
      rewrite (sum_Z_range_ext 0 (n - 1)
        (fun edge => Znth edge initial_dist 0 - Znth edge new_dist 0)
        (fun edge =>
           (Znth edge initial_dist 0 - Znth edge old_dist 0) +
           (if Z.eq_dec edge position then 1 else 0))).
      2: {
        intros edge Hedge.
        specialize (Hdistance edge Hedge).
        destruct (Z.eq_dec edge position) as [Heq | Hne].
        - subst edge.
          destruct (Z.eq_dec position position) as [_ | Hcontra];
            [lia | contradiction].
        - destruct (Z.eq_dec edge position) as [Hcontra | _];
            [contradiction | lia].
      }
      rewrite sum_Z_range_add.
      rewrite sum_Z_range_single_indicator__exchange_certificate_transition by lia.
      reflexivity.
    }
    rewrite Hsum_step.
    lia.
Qed.
Lemma max_default_member_le__exchange_certificate_transition :
  forall {A : Type} (P : A -> Prop) (f : A -> Z)
         (default maximum : Z) (a : A),
    max_value_of_subset_with_default Z.le P f default maximum ->
    P a ->
    f a <= maximum.
Proof.
  intros A P f default maximum a Hmaximum Ha.
  destruct Hmaximum as [[Hmaximum _] | [Hall Heq]].
  - destruct Hmaximum as [maximum_object [[_ Hsound] Hvalue]].
    subst maximum.
    apply Hsound, Ha.
  - subst maximum.
    apply Hall, Ha.
Qed.
Lemma arrival_dominates_passenger_time__exchange_certificate_transition :
  forall n m initial_dist times origins destinations
         final_dist latest arrivals passenger,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge final_dist 0) ->
    BusArrivalSchedule n final_dist latest arrivals ->
    0 <= passenger < m ->
    Znth passenger times 0 <=
      Znth (Znth passenger destinations 0 - 1) arrivals 0.
Proof.
  intros n m initial_dist times origins destinations
    final_dist latest arrivals passenger
    Hinputs Hlatest Hdist Hschedule Hpassenger.
  pose proof Hinputs as Hbounds.
  destruct Hbounds as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hinitial_dist Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds passenger Hpassenger).
  destruct Hpassenger_bounds as
    [Htime [[Horigin_lower Horigin_destination] Hdestination_upper]].
  destruct Hlatest as [_ Hlatest].
  specialize (Hlatest (Znth passenger origins 0 - 1) ltac:(lia)).
  unfold LatestAtStation in Hlatest.
  pose proof
    (max_default_member_le__exchange_certificate_transition
       (fun candidate =>
          0 <= candidate < m /\
          Znth candidate origins 0 =
            (Znth passenger origins 0 - 1) + 1)
       (fun candidate => Znth candidate times 0)
       0 (Znth (Znth passenger origins 0 - 1) latest 0)
       passenger Hlatest ltac:(split; [exact Hpassenger | lia]))
    as Htime_latest.
  cbn in Htime_latest.
  pose proof Hschedule as Hschedule_step.
  destruct Hschedule_step as [_ [_ Hnext]].
  specialize (Hnext (Znth passenger origins 0 - 1) ltac:(lia)).
  destruct Hnext as [departure [Hdeparture Harrival]].
  unfold StationDeparture,
    MaxMin.max_value_of_subset_with_default in Hdeparture.
  assert (Hlatest_departure :
    Znth (Znth passenger origins 0 - 1) latest 0 <= departure).
  {
    destruct Hdeparture as [[Hmaximum _] | [Hall Heq]].
    - destruct Hmaximum as [candidate [[Hcandidate Hsound] Hvalue]].
      specialize (Hsound
        (Znth (Znth passenger origins 0 - 1) latest 0) eq_refl).
      simpl in Hsound, Hvalue.
      lia.
    - specialize (Hall
        (Znth (Znth passenger origins 0 - 1) latest 0) eq_refl).
      lia.
  }
  pose proof (Hdist (Znth passenger origins 0 - 1) ltac:(lia))
    as Horigin_dist.
  assert (Horigin_arrival :
    Znth passenger times 0 <=
      Znth (Znth passenger origins 0) arrivals 0).
  {
    replace (Znth passenger origins 0)
      with ((Znth passenger origins 0 - 1) + 1) by lia.
    rewrite Harrival.
    lia.
  }
  eapply Z.le_trans; [exact Horigin_arrival |].
  eapply bus_arrivals_nondecreasing__exchange_certificate_transition
    with (n := n) (dist := final_dist) (latest := latest).
  - exact Hdist.
  - exact Hschedule.
  - lia.
  - lia.
  - lia.
Qed.
Lemma passenger_travel_total_nonnegative__exchange_certificate_transition :
  forall n m initial_dist times origins destinations
         final_dist latest arrivals total,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge final_dist 0) ->
    BusArrivalSchedule n final_dist latest arrivals ->
    PassengerTravelTotal m times destinations arrivals total ->
    0 <= total.
Proof.
  intros n m initial_dist times origins destinations
    final_dist latest arrivals total Hinputs Hlatest Hdist Hschedule Htotal.
  unfold PassengerTravelTotal in Htotal.
  rewrite Htotal.
  apply sum_nonneg.
  intros passenger Hpassenger.
  pose proof
    (arrival_dominates_passenger_time__exchange_certificate_transition
       n m initial_dist times origins destinations
       final_dist latest arrivals passenger
       Hinputs Hlatest Hdist Hschedule Hpassenger) as Hdominates.
  lia.
Qed.
Lemma sum_redundant_upper_bound__comparison_completion :
  forall m (P : Z -> Prop),
    Sum.sum (fun x => 0 <= x < m /\ x < m /\ P x) (fun _ => 1) =
    Sum.sum (fun x => 0 <= x < m /\ P x) (fun _ => 1).
Proof.
  intros m P.
  unfold Sum.sum.
  change (
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter
         (fun x => if Sum.prop_dec (x < m /\ P x) then true else false)
         (Zrange 0 m)) =
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun x => if Sum.prop_dec (P x) then true else false)
         (Zrange 0 m))).
  f_equal.
  apply filter_ext_in.
  intros x Hx.
  pose proof (proj2 (In_Zrange 0 m x) Hx) as Hrange.
  destruct (Sum.prop_dec (x < m /\ P x)) as [Hleft | Hleft];
    destruct (Sum.prop_dec (P x)) as [Hright | Hright];
    try reflexivity.
  - exfalso.
    apply Hright.
    tauto.
  - exfalso.
    apply Hleft.
    tauto.
Qed.
Lemma passenger_aggregation_complete__comparison_completion :
  forall n m times origins destinations processed latest counts,
    processed = m ->
    Zlength latest = n ->
    Zlength counts = n ->
    PassengerAggregationPrefix
      n m times origins destinations processed latest counts ->
    StationSummaryState n m times origins destinations latest counts.
Proof.
  intros n m times origins destinations processed latest counts
    Hprocessed Hlatest_len Hcounts_len Hprefix.
  subst processed.
  unfold PassengerAggregationPrefix in Hprefix.
  destruct Hprefix as [Hlatest Hcounts].
  unfold StationSummaryState, LatestDepartures, DestinationCounts.
  split.
  - split; [exact Hlatest_len |].
    intros station Hstation.
    specialize (Hlatest station Hstation).
    unfold LatestAtStationPrefix in Hlatest.
    unfold LatestAtStation.
    eapply MaxMin.max_default_eq_forward; try typeclasses eauto.
    + exact Hlatest.
    + intros passenger Hpassenger.
      exists passenger.
      split.
      * cbn in Hpassenger |-.
        tauto.
      * lia.
    + intros passenger Hpassenger.
      exists passenger.
      split.
      * cbn in Hpassenger |-.
        tauto.
      * lia.
  - split; [exact Hcounts_len |].
    intros station Hstation.
    specialize (Hcounts station Hstation).
    rewrite Hcounts.
    apply sum_redundant_upper_bound__comparison_completion.
Qed.
Lemma sum_Z_range_filter__passenger_aggregation :
  forall low high (P : Z -> Prop) (f : Z -> Z),
    sum (fun x => low <= x < high /\ P x) f =
    sum (fun x => low <= x < high)
        (fun x => if prop_dec (P x) then f x else 0).
Proof.
  intros low high P f.
  rewrite sum_range_unfold.
  unfold sum.
  simpl.
  generalize (Zrange low high) as xs.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (prop_dec (P x)); simpl; rewrite IH; reflexivity.
Qed.
Lemma sum_prefix_filter_extend_right__passenger_aggregation :
  forall processed m (P : Z -> Prop),
    0 <= processed ->
    processed < m ->
    sum (fun x => 0 <= x < processed + 1 /\ x < m /\ P x)
        (fun _ => 1) =
    sum (fun x => 0 <= x < processed /\ x < m /\ P x)
        (fun _ => 1) +
    (if prop_dec (P processed) then 1 else 0).
Proof.
  intros processed m P Hprocessed Hm.
  rewrite !sum_Z_range_filter__passenger_aggregation.
  rewrite (sum_Z_range_extend_right 0 processed) by lia.
  destruct (prop_dec (P processed)) as [HP | HnotP];
    destruct (prop_dec (processed < m /\ P processed)) as [Hboth | Hnotboth];
    simpl; try reflexivity; tauto.
Qed.
Lemma latest_at_station_prefix_step__passenger_aggregation :
  forall m times origins processed station latest,
    0 <= processed < m ->
    LatestAtStationPrefix m times origins processed station latest ->
    LatestAtStationPrefix m times origins (processed + 1) station
      (if Z.eq_dec (Znth processed origins 0) (station + 1)
       then le_max Z.le latest (Znth processed times 0)
       else latest).
Proof.
  intros m times origins processed station latest Hprocessed Hlatest.
  unfold LatestAtStationPrefix in *.
  destruct (Z.eq_dec (Znth processed origins 0) (station + 1))
    as [Horigin | Horigin].
  - eapply max_default_union_1_right
      with (a := processed)
           (P := fun passenger =>
             0 <= passenger < processed /\
             passenger < m /\
             Znth passenger origins 0 = station + 1).
    + exact Hlatest.
    + reflexivity.
    + intro passenger.
      split.
      * intros (Hrange & Hm & Hstation).
        destruct (Z.eq_dec passenger processed) as [Heq | Hneq].
        -- right. lia.
        -- left. repeat split; try lia; assumption.
      * intros [(Hrange & Hm & Hstation) | Heq].
        -- repeat split; try lia; assumption.
        -- subst passenger. repeat split; try lia; assumption.
  - eapply (@max_default_eq_forward Z Z.le Zle_TotalOrder Z
      (fun passenger => Znth passenger times 0)
      (fun passenger => Znth passenger times 0)
      (fun passenger =>
         0 <= passenger < processed /\
         passenger < m /\
         Znth passenger origins 0 = station + 1)
      (fun passenger =>
         0 <= passenger < processed + 1 /\
         passenger < m /\
         Znth passenger origins 0 = station + 1)
      0 latest).
    + exact Hlatest.
    + intros passenger (Hrange & Hm & Hstation).
      exists passenger. split.
      * repeat split; try lia; assumption.
      * lia.
    + intros passenger (Hrange & Hm & Hstation).
      exists passenger. split.
      * repeat split; try lia.
        destruct (Z.eq_dec passenger processed) as [Heq | Hneq].
        -- subst passenger. contradiction.
        -- lia.
      * lia.
Qed.
Lemma passenger_aggregation_prefix_step__passenger_aggregation :
  forall n m times origins destinations processed latest counts,
    0 <= processed < m ->
    Zlength latest = n ->
    Zlength counts = n ->
    0 <= Znth processed origins 0 - 1 < n ->
    0 <= Znth processed destinations 0 - 1 < n ->
    PassengerAggregationPrefix
      n m times origins destinations processed latest counts ->
    PassengerAggregationPrefix
      n m times origins destinations (processed + 1)
      (replace_Znth
         (Znth processed origins 0 - 1)
         (le_max Z.le
            (Znth (Znth processed origins 0 - 1) latest 0)
            (Znth processed times 0))
         latest)
      (replace_Znth
         (Znth processed destinations 0 - 1)
         (Znth (Znth processed destinations 0 - 1) counts 0 + 1)
         counts).
Proof.
  intros n m times origins destinations processed latest counts
    Hprocessed Hlatest_len Hcounts_len Horigin_range Hdestination_range
    Hprefix.
  unfold PassengerAggregationPrefix in *.
  destruct Hprefix as [Hlatest Hcounts].
  split.
  - intros station Hstation.
    pose proof
      (latest_at_station_prefix_step__passenger_aggregation
         m times origins processed station (Znth station latest 0)
         Hprocessed (Hlatest station Hstation)) as Hstep.
    destruct (Z.eq_dec station (Znth processed origins 0 - 1))
      as [Heq | Hneq].
    + subst station.
      rewrite Znth_replace_Znth_Same by lia.
      destruct (Z.eq_dec (Znth processed origins 0)
                         (Znth processed origins 0 - 1 + 1));
        [exact Hstep | lia].
    + rewrite Znth_replace_Znth_Diff by lia.
      destruct (Z.eq_dec (Znth processed origins 0) (station + 1));
        [lia | exact Hstep].
  - intros station Hstation.
    specialize (Hcounts station Hstation).
    pose proof
      (sum_prefix_filter_extend_right__passenger_aggregation
         processed m
         (fun passenger =>
            Znth passenger destinations 0 = station + 1)
         ltac:(lia) ltac:(lia)) as Hsum.
    destruct (Z.eq_dec station (Znth processed destinations 0 - 1))
      as [Heq | Hneq].
    + subst station.
      rewrite Znth_replace_Znth_Same by lia.
      destruct (prop_dec
        (Znth processed destinations 0 =
         Znth processed destinations 0 - 1 + 1));
        lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      destruct (prop_dec
        (Znth processed destinations 0 = station + 1));
        lia.
Qed.
Lemma station_departure_by_cases__arrival_simulation :
  forall arrivals latest station,
    (Znth station arrivals 0 <= Znth station latest 0 ->
       StationDeparture arrivals latest station (Znth station latest 0)) /\
    (Znth station latest 0 <= Znth station arrivals 0 ->
       StationDeparture arrivals latest station (Znth station arrivals 0)).
Proof.
  intros arrivals latest station.
  unfold StationDeparture.
  split; intro Horder.
  - unfold max_value_of_subset_with_default.
    left; split; [| exact Horder].
    unfold max_value_of_subset, max_object_of_subset.
    exists (Znth station latest 0).
    split.
    + split; [reflexivity |].
      intros candidate Hcandidate.
      change (candidate = Znth station latest 0) in Hcandidate.
      subst candidate.
      reflexivity.
    + reflexivity.
  - unfold max_value_of_subset_with_default.
    right; split; [| reflexivity].
    intros candidate Hcandidate.
    change (candidate = Znth station latest 0) in Hcandidate.
    subst candidate.
    exact Horder.
Qed.
Lemma arrival_simulation_prefix_snoc__arrival_simulation :
  forall n dist latest arrivals processed next_arrival new_next,
    Zlength arrivals = processed ->
    0 <= processed ->
    ArrivalSimulationPrefix
      n dist latest arrivals processed next_arrival ->
    ((next_arrival <= Znth processed latest 0 /\
      new_next = Znth processed latest 0 + Znth processed dist 0) \/
     (Znth processed latest 0 <= next_arrival /\
      new_next = next_arrival + Znth processed dist 0)) ->
    ArrivalSimulationPrefix
      n dist latest (arrivals ++ [next_arrival]) (processed + 1) new_next.
Proof.
  intros n dist latest arrivals processed next_arrival new_next
    Hlength Hprocessed Hprefix Hnext.
  destruct Hprefix as [Hstations Hpending].
  assert (Happ_old : forall index,
      0 <= index < processed ->
      Znth index (arrivals ++ [next_arrival]) 0 = Znth index arrivals 0).
  {
    intros index Hindex.
    apply app_Znth1.
    rewrite Hlength.
    exact Hindex.
  }
  assert (Happ_last :
      Znth processed (arrivals ++ [next_arrival]) 0 = next_arrival).
  {
    rewrite app_Znth2 by (rewrite Hlength; lia).
    rewrite Hlength.
    replace (processed - processed) with 0 by lia.
    reflexivity.
  }
  assert (Hdeparture :
      exists departure,
        StationDeparture
          (arrivals ++ [next_arrival]) latest processed departure /\
        new_next = departure + Znth processed dist 0).
  {
    destruct Hnext as [[Hbefore Hnew] | [Hafter Hnew]].
    - exists (Znth processed latest 0).
      split; [| exact Hnew].
      destruct
        (station_departure_by_cases__arrival_simulation
           (arrivals ++ [next_arrival]) latest processed)
        as [Hlatest _].
      apply Hlatest.
      rewrite Happ_last.
      exact Hbefore.
    - exists next_arrival.
      split; [| exact Hnew].
      destruct
        (station_departure_by_cases__arrival_simulation
           (arrivals ++ [next_arrival]) latest processed)
        as [_ Harrival].
      rewrite Happ_last in Harrival.
      apply Harrival.
      exact Hafter.
  }
  unfold ArrivalSimulationPrefix.
  split.
  - intros station Hstation.
    destruct (Z.eq_dec station processed) as [Heq | Hneq].
    + subst station.
      destruct (Z.eq_dec processed 0) as [Hzero | Hpositive].
      * rewrite Hzero in *.
        left.
        split; [reflexivity |].
        destruct Hpending as [[_ Hnext_zero] | [Hcontra _]]; [| lia].
        rewrite Happ_last.
        exact Hnext_zero.
      * right.
        split; [lia |].
        destruct Hpending as [[Hcontra _] | [_ [departure [Hdepart Heqnext]]]];
          [lia |].
        exists departure.
        split.
        -- unfold StationDeparture in *.
           rewrite Happ_old by lia.
           exact Hdepart.
        -- rewrite Happ_last.
           exact Heqnext.
    + assert (Hstation_old : 0 <= station < processed) by lia.
      specialize (Hstations station Hstation_old).
      destruct Hstations as [[Hstation_zero Harrival_zero] |
          [Hstation_positive [departure [Hdepart Heqarrival]]]].
      * left.
        split; [exact Hstation_zero |].
        rewrite Happ_old by exact Hstation_old.
        exact Harrival_zero.
      * right.
        split; [exact Hstation_positive |].
        exists departure.
        split.
        -- unfold StationDeparture in *.
           rewrite Happ_old by lia.
           exact Hdepart.
        -- rewrite Happ_old by exact Hstation_old.
           exact Heqarrival.
  - right.
    split; [lia |].
    replace (processed + 1 - 1) with processed by lia.
    exact Hdeparture.
Qed.
Lemma station_departure_bounds__comparison_completion :
  forall arrivals latest station departure upper,
    StationDeparture arrivals latest station departure ->
    0 <= Znth station arrivals 0 <= upper ->
    0 <= Znth station latest 0 <= upper ->
    0 <= departure <= upper.
Proof.
  intros arrivals latest station departure upper Hdeparture
    Harrival Hlatest.
  unfold StationDeparture, MaxMin.max_value_of_subset_with_default in Hdeparture.
  destruct Hdeparture as [[Hmaximum Hdefault] | [Hall Hdefault]].
  - destruct Hmaximum as [candidate [Hobject Hvalue]].
    destruct Hobject as [Hmember Hgreatest].
    change (candidate = Znth station latest 0) in Hmember.
    cbn in Hvalue.
    lia.
  - cbn in Hdefault.
    subst departure.
    exact Harrival.
Qed.
Lemma arrival_simulation_complete__comparison_completion :
  forall n dist latest arrivals cur,
    2 <= n <= 1000 ->
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge dist 0 <= 100) ->
    (forall station, 0 <= station < n ->
       0 <= Znth station latest 0 <= 100000) ->
    Zlength arrivals = n ->
    ArrivalSimulationPrefix n dist latest arrivals n cur ->
    BusArrivalSchedule n dist latest arrivals /\
    forall station, 0 <= station < n ->
      0 <= Znth station arrivals 0 <= 200000.
Proof.
  intros n dist latest arrivals cur Hn Hdist Hlatest Harrivals_len Hprefix.
  unfold ArrivalSimulationPrefix in Hprefix.
  destruct Hprefix as [Hstations Hnext].
  assert (Hschedule : BusArrivalSchedule n dist latest arrivals).
  {
    unfold BusArrivalSchedule.
    split; [exact Harrivals_len |].
    split.
    - specialize (Hstations 0 ltac:(lia)).
      destruct Hstations as [[_ Harrival0] | [Hpositive _]]; lia.
    - intros station Hstation.
      specialize (Hstations (station + 1) ltac:(lia)).
      destruct Hstations as
        [[Hzero _] | [Hpositive [departure [Hdeparture Harrival]]]].
      + lia.
      + exists departure.
        replace (station + 1 - 1) with station in Hdeparture, Harrival by lia.
        tauto.
  }
  split; [exact Hschedule |].
  assert (Hstrong : forall station, 0 <= station < n ->
    0 <= Znth station arrivals 0 <= 100000 + 100 * station).
  {
    intros station Hstation.
    assert (Hrepr : station = Z.of_nat (Z.to_nat station)).
    { rewrite Z2Nat.id; lia. }
    rewrite Hrepr in *.
    remember (Z.to_nat station) as station_nat.
    clear station Hrepr Heqstation_nat.
    induction station_nat as [|station_nat IH].
    - cbn.
      specialize (Hstations 0 ltac:(lia)).
      destruct Hstations as [[_ Harrival0] | [Hpositive _]]; lia.
    - rewrite Nat2Z.inj_succ in *.
      specialize (Hstations (Z.of_nat station_nat + 1) ltac:(lia)).
      destruct Hstations as
        [[Hzero _] | [Hpositive [departure [Hdeparture Harrival]]]].
      + lia.
      + replace (Z.of_nat station_nat + 1 - 1) with (Z.of_nat station_nat)
          in Hdeparture, Harrival by lia.
        assert (Hprevious_range : 0 <= Z.of_nat station_nat < n) by lia.
        specialize (IH ltac:(lia)).
        specialize (Hlatest (Z.of_nat station_nat) Hprevious_range).
        specialize (Hdist (Z.of_nat station_nat) ltac:(lia)).
        pose proof
          (station_departure_bounds__comparison_completion
             arrivals latest (Z.of_nat station_nat) departure
             (100000 + 100 * Z.of_nat station_nat)
             Hdeparture ltac:(lia) ltac:(lia)) as Hdeparture_bounds.
        replace (Z.succ (Z.of_nat station_nat)) with
          (Z.of_nat station_nat + 1) by lia.
        rewrite Harrival.
        lia.
  }
  intros station Hstation.
  pose proof (Hstrong station Hstation).
  lia.
Qed.
Lemma arrival_simulation_prefix_pending_bound__arrival_simulation :
  forall n dist latest arrivals processed next_arrival,
    2 <= n <= 1000 ->
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge dist 0 <= 100) ->
    (forall station, 0 <= station < n ->
       0 <= Znth station latest 0 <= 100000) ->
    0 <= processed < n ->
    ArrivalSimulationPrefix
      n dist latest arrivals processed next_arrival ->
    0 <= next_arrival <= 100000 + 100 * processed.
Proof.
  intros n dist latest arrivals processed next_arrival
    Hn Hdist Hlatest Hprocessed Hprefix.
  unfold ArrivalSimulationPrefix in Hprefix.
  destruct Hprefix as [Hstations Hpending].
  assert (Hstrong : forall station, 0 <= station < processed ->
    0 <= Znth station arrivals 0 <= 100000 + 100 * station).
  {
    intros station Hstation.
    assert (Hrepr : station = Z.of_nat (Z.to_nat station)).
    { rewrite Z2Nat.id; lia. }
    rewrite Hrepr in *.
    remember (Z.to_nat station) as station_nat.
    clear station Hrepr Heqstation_nat.
    induction station_nat as [|station_nat IH].
    - cbn.
      specialize (Hstations 0 ltac:(lia)).
      destruct Hstations as [[_ Harrival0] | [Hpositive _]]; lia.
    - rewrite Nat2Z.inj_succ in *.
      specialize (Hstations (Z.of_nat station_nat + 1) ltac:(lia)).
      destruct Hstations as
        [[Hzero _] | [Hpositive [departure [Hdeparture Harrival]]]].
      + lia.
      + replace (Z.of_nat station_nat + 1 - 1) with (Z.of_nat station_nat)
          in Hdeparture, Harrival by lia.
        assert (Hprevious_range : 0 <= Z.of_nat station_nat < n) by lia.
        specialize (IH ltac:(lia)).
        specialize (Hlatest (Z.of_nat station_nat) Hprevious_range).
        specialize (Hdist (Z.of_nat station_nat) ltac:(lia)).
        pose proof
          (station_departure_bounds__comparison_completion
             arrivals latest (Z.of_nat station_nat) departure
             (100000 + 100 * Z.of_nat station_nat)
             Hdeparture ltac:(lia) ltac:(lia)) as Hdeparture_bounds.
        replace (Z.succ (Z.of_nat station_nat)) with
          (Z.of_nat station_nat + 1) by lia.
        rewrite Harrival.
        lia.
  }
  destruct Hpending as
    [[Hprocessed_zero Hnext_zero] |
     [Hprocessed_positive [departure [Hdeparture Hnext]]]].
  - lia.
  - assert (Hprevious_range : 0 <= processed - 1 < n) by lia.
    specialize (Hstrong (processed - 1) ltac:(lia)).
    specialize (Hlatest (processed - 1) Hprevious_range).
    specialize (Hdist (processed - 1) ltac:(lia)).
    pose proof
      (station_departure_bounds__comparison_completion
         arrivals latest (processed - 1) departure
         (100000 + 100 * (processed - 1))
         Hdeparture ltac:(lia) ltac:(lia)) as Hdeparture_bounds.
    rewrite Hnext.
    lia.
Qed.
Lemma Znth_at_or_past_length_default__arrival_simulation :
  forall (A : Type) (l : list A) (index : Z) (default : A),
    0 <= index ->
    Zlength l <= index ->
    Znth index l default = default.
Proof.
  intros A l index default Hindex Hlength.
  unfold Znth.
  rewrite nth_overflow; [reflexivity |].
  apply Nat2Z.inj_le.
  rewrite Z2Nat.id by exact Hindex.
  rewrite <- Zlength_correct.
  exact Hlength.
Qed.
Lemma bus_arrivals_nondecreasing__booster_and_scan_initialization :
  forall n dist latest arrivals lo hi,
    BusArrivalSchedule n dist latest arrivals ->
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge dist 0) ->
    0 <= lo -> lo <= hi -> hi < n ->
    Znth lo arrivals 0 <= Znth hi arrivals 0.
Proof.
  intros n dist latest arrivals lo hi Hschedule Hdist Hlo Hlohi Hhi.
  assert (Hstep : forall station, 0 <= station < n - 1 ->
      Znth station arrivals 0 <= Znth (station + 1) arrivals 0).
  {
    intros station Hstation.
    destruct Hschedule as [_ [_ Hnext]].
    specialize (Hnext station Hstation).
    destruct Hnext as [departure [Hdeparture Harrival_next]].
    pose proof (station_departure_ge_inputs__chain_dual
      arrivals latest station departure Hdeparture) as [Harrival_bound _].
    specialize (Hdist station Hstation).
    lia.
  }
  assert (Hnat : forall d : nat,
    lo + Z.of_nat d < n ->
    Znth lo arrivals 0 <= Znth (lo + Z.of_nat d) arrivals 0).
  {
    induction d as [|d IH].
    - intros _.
      replace (lo + Z.of_nat 0) with lo by lia.
      apply Z.le_refl.
    - intros Hd.
      replace (lo + Z.of_nat (S d))
        with ((lo + Z.of_nat d) + 1) by lia.
      eapply Z.le_trans.
      + apply IH; lia.
      + apply Hstep; lia.
  }
  specialize (Hnat (Z.to_nat (hi - lo))).
  replace (lo + Z.of_nat (Z.to_nat (hi - lo))) with hi in Hnat by lia.
  apply Hnat; exact Hhi.
Qed.
Lemma arrival_dominates_passenger_time__booster_and_scan_initialization :
  forall n m initial_dist times origins destinations latest arrivals passenger,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    BusArrivalSchedule n initial_dist latest arrivals ->
    0 <= passenger < m ->
    Znth passenger times 0 <=
      Znth (Znth passenger destinations 0 - 1) arrivals 0.
Proof.
  intros n m initial_dist times origins destinations latest arrivals passenger
    Hinputs Hlatest Hschedule Hpassenger.
  pose proof Hinputs as Hbounds.
  unfold SightseeingInputsBounded in Hbounds.
  destruct Hbounds as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hdist Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds passenger Hpassenger).
  destruct Hpassenger_bounds as
    [Htime [[Horigin_lower Horigin_destination] Hdestination_upper]].
  destruct Hlatest as [_ Hlatest].
  specialize (Hlatest (Znth passenger origins 0 - 1) ltac:(lia)).
  unfold LatestAtStation,
    MaxMin.max_value_of_subset_with_default in Hlatest.
  assert (Htime_latest :
    Znth passenger times 0 <=
      Znth (Znth passenger origins 0 - 1) latest 0).
  {
    destruct Hlatest as [[Hmaximum _] | [Hall Heq]].
    - destruct Hmaximum as [candidate [[Hcandidate Hgreatest] Hvalue]].
      specialize (Hgreatest passenger
        ltac:(split; [exact Hpassenger | lia])).
      cbn in Hgreatest.
      lia.
    - specialize (Hall passenger ltac:(split; [exact Hpassenger | lia])).
      lia.
  }
  pose proof Hschedule as Hschedule_full.
  destruct Hschedule as [_ [_ Hnext]].
  specialize (Hnext (Znth passenger origins 0 - 1) ltac:(lia)).
  destruct Hnext as [departure [Hdeparture Harrival]].
  pose proof (station_departure_ge_inputs__chain_dual
    arrivals latest (Znth passenger origins 0 - 1) departure Hdeparture)
    as [_ Hlatest_departure].
  pose proof Hdist as Hdist_full.
  specialize (Hdist (Znth passenger origins 0 - 1) ltac:(lia)).
  assert (Horigin_arrival :
    Znth passenger times 0 <=
      Znth (Znth passenger origins 0) arrivals 0).
  {
    replace (Znth passenger origins 0)
      with ((Znth passenger origins 0 - 1) + 1) by lia.
    rewrite Harrival.
    lia.
  }
  eapply Z.le_trans; [exact Horigin_arrival |].
  eapply bus_arrivals_nondecreasing__booster_and_scan_initialization.
  - exact Hschedule_full.
  - intros edge Hedge.
    specialize (Hdist_full edge Hedge).
    lia.
  - lia.
  - lia.
  - lia.
Qed.
Lemma marginal_benefit_scan_snoc__edge_benefit_scan :
  forall counts latest arrivals edge next benefit,
    edge + 1 <= next ->
    MarginalBenefitScan counts latest arrivals edge next benefit ->
    Znth next latest 0 < Znth next arrivals 0 ->
    MarginalBenefitScan counts latest arrivals edge (next + 1)
      (benefit + Znth next counts 0).
Proof.
  intros counts latest arrivals edge next benefit Hrange Hscan Hstrict.
  rewrite MarginalBenefitScan_unfold in *.
  destruct Hscan as [Hsum Hprefix].
  split.
  - rewrite sum_Z_range_extend_right by lia.
    lia.
  - intros station Hstation.
    destruct (Z.eq_dec station next) as [-> | Hne].
    + exact Hstrict.
    + apply Hprefix.
      lia.
Qed.
Lemma zlist_eq_by_Znth__booster_entry :
  forall (l1 l2 : list Z),
    Zlength l1 = Zlength l2 ->
    (forall i, 0 <= i < Zlength l1 ->
       Znth i l1 0 = Znth i l2 0) ->
    l1 = l2.
Proof.
  intros l1 l2 Hlen Hpoint.
  apply (list_eq_nth Z l1 l2 0).
  - rewrite !Zlength_correct in Hlen.
    lia.
  - intros i Hi.
    specialize (Hpoint (Z.of_nat i)).
    unfold Znth in Hpoint.
    rewrite Nat2Z.id in Hpoint.
    apply Hpoint.
    rewrite Zlength_correct.
    lia.
Qed.
Lemma feasible_zero_budget_identity__booster_entry :
  forall n initial_dist final_dist,
    Zlength initial_dist = n - 1 ->
    FeasibleBoostedDistances n 0 initial_dist final_dist ->
    final_dist = initial_dist.
Proof.
  intros n initial_dist final_dist Hinitial Hfeasible.
  rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  destruct Hfeasible as [Hfinal [Hbounds Hbudget]].
  assert (Hnonneg : forall edge,
    0 <= edge < n - 1 ->
    0 <= Znth edge initial_dist 0 - Znth edge final_dist 0).
  {
    intros edge Hedge.
    specialize (Hbounds edge Hedge).
    lia.
  }
  assert (Hsum_nonneg :
    0 <= sum (fun edge => 0 <= edge < n - 1)
      (fun edge =>
         Znth edge initial_dist 0 - Znth edge final_dist 0)).
  {
    apply sum_nonneg.
    exact Hnonneg.
  }
  assert (Hsum_zero :
    sum (fun edge => 0 <= edge < n - 1)
      (fun edge =>
         Znth edge initial_dist 0 - Znth edge final_dist 0) = 0) by lia.
  pose proof (sum_nonneg_eq_zero_elim
    (fun edge => 0 <= edge < n - 1)
    (fun edge => Znth edge initial_dist 0 - Znth edge final_dist 0)
    Hnonneg Hsum_zero) as Hzero.
  apply zlist_eq_by_Znth__booster_entry.
  - lia.
  - intros edge Hedge.
    assert (Hrange : 0 <= edge < n - 1).
    {
      rewrite <- Hfinal.
      exact Hedge.
    }
    specialize (Hzero edge Hrange).
    lia.
Qed.
Lemma initial_dist_feasible_zero__booster_entry :
  forall n m initial_dist times origins destinations,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    FeasibleBoostedDistances n 0 initial_dist initial_dist.
Proof.
  intros n m initial_dist times origins destinations Hinputs.
  unfold SightseeingInputsBounded in Hinputs.
  destruct Hinputs as [_ [_ [Hlen [_ [_ [_ [Hbounds _]]]]]]].
  rewrite FeasibleBoostedDistances_unfold.
  split; [exact Hlen |].
  split.
  - intros edge Hedge.
    specialize (Hbounds edge Hedge).
    lia.
  - rewrite (sum_ext
      (fun edge => 0 <= edge < n - 1)
      (fun edge => Znth edge initial_dist 0 - Znth edge initial_dist 0)
      (fun _ => 0)).
    + rewrite sum_zero.
      lia.
    + intros edge Hedge.
      lia.
Qed.
Lemma latest_departures_unique__booster_entry :
  forall n m times origins latest1 latest2,
    LatestDepartures n m times origins latest1 ->
    LatestDepartures n m times origins latest2 ->
    latest1 = latest2.
Proof.
  intros n m times origins latest1 latest2 Hlatest1 Hlatest2.
  unfold LatestDepartures in Hlatest1, Hlatest2.
  destruct Hlatest1 as [Hlen1 Hpoint1].
  destruct Hlatest2 as [Hlen2 Hpoint2].
  apply zlist_eq_by_Znth__booster_entry.
  - lia.
  - intros station Hstation.
    specialize (Hpoint1 station ltac:(lia)).
    specialize (Hpoint2 station ltac:(lia)).
    unfold LatestAtStation in Hpoint1, Hpoint2.
    eapply (@MaxMin.max_default_unique
      Z Z.le Zle_TotalOrder Z
      (fun passenger => Znth passenger times 0)
      (fun passenger =>
         0 <= passenger < m /\
         Znth passenger origins 0 = station + 1)
      0); eauto.
Qed.
Lemma bus_arrival_schedule_unique__booster_entry :
  forall n dist latest arrivals1 arrivals2,
    BusArrivalSchedule n dist latest arrivals1 ->
    BusArrivalSchedule n dist latest arrivals2 ->
    arrivals1 = arrivals2.
Proof.
  intros n dist latest arrivals1 arrivals2 Hschedule1 Hschedule2.
  unfold BusArrivalSchedule in Hschedule1, Hschedule2.
  destruct Hschedule1 as [Hlen1 [Hzero1 Hstep1]].
  destruct Hschedule2 as [Hlen2 [Hzero2 Hstep2]].
  apply (list_eq_nth Z arrivals1 arrivals2 0).
  - rewrite !Zlength_correct in Hlen1, Hlen2.
    lia.
  - intros index Hindex.
    revert Hindex.
    induction index as [|index IH]; intros Hindex.
    + unfold Znth in Hzero1, Hzero2.
      simpl in Hzero1, Hzero2.
      lia.
    + assert (Hprevious : (index < length arrivals1)%nat) by lia.
      specialize (IH Hprevious).
      assert (Hstation : 0 <= Z.of_nat index < n - 1).
      {
        rewrite Zlength_correct in Hlen1.
        lia.
      }
      specialize (Hstep1 (Z.of_nat index) Hstation).
      specialize (Hstep2 (Z.of_nat index) Hstation).
      destruct Hstep1 as [departure1 [Hdeparture1 Harrival1]].
      destruct Hstep2 as [departure2 [Hdeparture2 Harrival2]].
      assert (Hprevious_Znth :
        Znth (Z.of_nat index) arrivals1 0 =
        Znth (Z.of_nat index) arrivals2 0).
      {
        unfold Znth.
        rewrite !Nat2Z.id.
        exact IH.
      }
      unfold StationDeparture in Hdeparture1, Hdeparture2.
      rewrite <- Hprevious_Znth in Hdeparture2.
      assert (Hdeparture_eq : departure1 = departure2).
      {
        eapply (@MaxMin.max_default_unique
          Z Z.le Zle_TotalOrder Z
          (fun candidate => candidate)
          (fun candidate => candidate = Znth (Z.of_nat index) latest 0)
          (Znth (Z.of_nat index) arrivals1 0)); eauto.
      }
      replace (Z.of_nat index + 1) with (Z.of_nat (S index))
        in Harrival1, Harrival2 by lia.
      unfold Znth in Harrival1, Harrival2.
      rewrite !Nat2Z.id in Harrival1, Harrival2.
      rewrite Harrival1, Harrival2, Hdeparture_eq.
      reflexivity.
Qed.
Lemma canonical_zero_budget_optimal__booster_entry :
  forall n m initial_dist times origins destinations latest arrivals total,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    BusArrivalSchedule n initial_dist latest arrivals ->
    PassengerTravelTotal m times destinations arrivals total ->
    SightseeingMinimumTotal
      n m 0 initial_dist times origins destinations total.
Proof.
  intros n m initial_dist times origins destinations latest arrivals total
    Hinputs Hlatest Hschedule Htotal.
  assert (Hfeasible :
    FeasibleBoostedDistances n 0 initial_dist initial_dist).
  {
    eapply initial_dist_feasible_zero__booster_entry.
    exact Hinputs.
  }
  unfold SightseeingMinimumTotal,
    MaxMin.min_value_of_subset, MaxMin.min_object_of_subset.
  exists total.
  split.
  - split.
    + unfold SightseeingCandidateTotal.
      exists initial_dist, latest, arrivals.
      split; [exact Hlatest |].
      split; [exact Hfeasible |].
      split; [exact Hschedule | exact Htotal].
    + intros candidate Hcandidate.
      unfold SightseeingCandidateTotal in Hcandidate.
      destruct Hcandidate as
        [candidate_dist [candidate_latest [candidate_arrivals
          [Hcandidate_latest [Hcandidate_feasible
            [Hcandidate_schedule Hcandidate_total]]]]]].
      assert (Hinitial_len : Zlength initial_dist = n - 1).
      {
        unfold SightseeingInputsBounded in Hinputs.
        tauto.
      }
      pose proof (feasible_zero_budget_identity__booster_entry
        n initial_dist candidate_dist Hinitial_len Hcandidate_feasible)
        as Hcandidate_dist_eq.
      subst candidate_dist.
      pose proof (latest_departures_unique__booster_entry
        n m times origins candidate_latest latest
        Hcandidate_latest Hlatest) as Hcandidate_latest_eq.
      subst candidate_latest.
      pose proof (bus_arrival_schedule_unique__booster_entry
        n initial_dist latest candidate_arrivals arrivals
        Hcandidate_schedule Hschedule) as Hcandidate_arrivals_eq.
      subst candidate_arrivals.
      unfold PassengerTravelTotal in Hcandidate_total, Htotal.
      lia.
  - reflexivity.
Qed.
Lemma booster_progress_initial_active__booster_and_scan_initialization :
  forall n m budget initial_dist times origins destinations
         latest counts arrivals,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    CanonicalBusState
      n m times origins destinations initial_dist latest counts arrivals ->
    (forall station, 0 <= station < n ->
       0 <= Znth station arrivals 0 <= 200000) ->
    BoosterProgress
      n m budget budget initial_dist times origins destinations
      initial_dist latest counts arrivals.
Proof.
  intros n m budget initial_dist times origins destinations
    latest counts arrivals Hinputs Hcanonical Harrival_bounds.
  unfold CanonicalBusState, StationSummaryState in Hcanonical.
  destruct Hcanonical as [[Hlatest Hcounts] Hschedule].
  unfold BoosterProgress.
  split; [exact Hlatest |].
  split; [exact Hcounts |].
  split.
  - replace (budget - budget) with 0 by lia.
    eapply initial_dist_feasible_zero__booster_entry.
    exact Hinputs.
  - split; [exact Hschedule |].
    exists
      (sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) arrivals 0 -
           Znth passenger times 0)).
    split.
    + unfold PassengerTravelTotal.
      reflexivity.
    + replace (budget - budget) with 0 by lia.
      eapply canonical_zero_budget_optimal__booster_entry;
        [exact Hinputs | exact Hlatest | exact Hschedule |].
      unfold PassengerTravelTotal. reflexivity.
Qed.
Lemma destination_count_interval_bound__booster_and_scan_initialization :
  forall n m destinations counts low high,
    0 <= m ->
    0 <= low -> low <= high -> high <= n ->
    DestinationCounts n m destinations counts ->
    sum (fun station => low <= station < high)
        (fun station => Znth station counts 0) <= m.
Proof.
  intros n m destinations counts low high
    Hm Hlow Hlowhigh Hhigh Hcounts.
  rewrite (destination_counts_interval_as_passengers__saturation
    n m destinations counts low high
    Hlow Hlowhigh Hhigh Hcounts).
  eapply Z.le_trans with
    (m := sum (fun passenger => 0 <= passenger < m) (fun _ => 1)).
  - apply sum_Z_range_le.
    intros passenger Hpassenger.
    destruct (prop_dec
      (low <= Znth passenger destinations 0 - 1 < high)); lia.
  - rewrite sum_Z_range_const by lia.
    lia.
Qed.
Lemma canonical_station_bounds__booster_and_scan_initialization :
  forall n m initial_dist times origins destinations latest counts arrivals
         station,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    CanonicalBusState
      n m times origins destinations initial_dist latest counts arrivals ->
    (forall candidate_station, 0 <= candidate_station < n ->
       0 <= Znth candidate_station arrivals 0 <= 200000) ->
    0 <= station < n ->
    0 <= Znth station latest 0 <= 100000 /\
    0 <= Znth station counts 0 <= m /\
    0 <= Znth station arrivals 0 <= 200000.
Proof.
  intros n m initial_dist times origins destinations latest counts arrivals
    station Hinputs Hcanonical Harrival Hstation.
  unfold CanonicalBusState, StationSummaryState in Hcanonical.
  destruct Hcanonical as [[Hlatest Hcounts] Hschedule].
  unfold LatestDepartures in Hlatest.
  destruct Hlatest as [Hlatest_length Hlatest].
  unfold DestinationCounts in Hcounts.
  destruct Hcounts as [Hcounts_length Hcounts].
  specialize (Hlatest station Hstation).
  specialize (Hcounts station Hstation).
  specialize (Harrival station Hstation).
  assert (Hlatest_bounds : 0 <= Znth station latest 0 <= 100000).
  {
    unfold LatestAtStation in Hlatest.
    pose proof (max_default_Z_bounds_source__cut_exchange
      Z
      (fun passenger =>
         0 <= passenger < m /\
         Znth passenger origins 0 = station + 1)
      (fun passenger => Znth passenger times 0)
      0 (Znth station latest 0) Hlatest)
      as [Hnonnegative [_ Hsource]].
    split; [exact Hnonnegative |].
    destruct Hsource as [Hzero | [passenger [Hpassenger Hvalue]]].
    - lia.
    - pose proof Hinputs as Hinput_bounds.
      unfold SightseeingInputsBounded in Hinput_bounds.
      destruct Hinput_bounds as
        [_ [_ [_ [_ [_ [_ [_ Hpassenger_bounds]]]]]]].
      specialize (Hpassenger_bounds passenger (proj1 Hpassenger)).
      lia.
  }
  assert (Hcount_bounds : 0 <= Znth station counts 0 <= m).
  {
    pose proof Hinputs as Hinput_numeric.
    unfold SightseeingInputsBounded in Hinput_numeric.
    rewrite Hcounts.
    rewrite sum_Z_range_filter_indicator__chain_dual.
    split.
    - apply sum_nonneg.
      intros passenger Hpassenger.
      destruct (prop_dec
        (Znth passenger destinations 0 = station + 1)); lia.
    - eapply Z.le_trans with
        (m := sum (fun passenger => 0 <= passenger < m) (fun _ => 1)).
      + apply sum_Z_range_le.
        intros passenger Hpassenger.
        destruct (prop_dec
          (Znth passenger destinations 0 = station + 1)); lia.
      + rewrite sum_Z_range_const by lia.
        lia.
  }
  tauto.
Qed.
Lemma marginal_benefit_scan_empty__booster_and_scan_initialization :
  forall counts latest arrivals edge,
    MarginalBenefitScan counts latest arrivals edge (edge + 1) 0.
Proof.
  intros counts latest arrivals edge.
  rewrite MarginalBenefitScan_unfold.
  split.
  - rewrite sum_Z_range_empty by lia.
    reflexivity.
  - intros station Hstation.
    lia.
Qed.
Lemma marginal_benefit_scan_extended_upper__booster_and_scan_initialization :
  forall n m destinations counts latest arrivals edge next benefit,
    0 <= m ->
    0 <= edge ->
    edge + 1 <= next ->
    next < n ->
    DestinationCounts n m destinations counts ->
    MarginalBenefitScan counts latest arrivals edge next benefit ->
    benefit + Znth next counts 0 <= m.
Proof.
  intros n m destinations counts latest arrivals edge next benefit
    Hm Hedge Hnext Hnext_n Hcounts Hscan.
  pose proof
    (destination_count_interval_bound__booster_and_scan_initialization
      n m destinations counts (edge + 1) (next + 1)
      Hm ltac:(lia) ltac:(lia) ltac:(lia) Hcounts) as Hinterval.
  rewrite MarginalBenefitScan_unfold in Hscan.
  destruct Hscan as [Hbenefit Hstrict].
  rewrite sum_Z_range_extend_right in Hinterval by lia.
  lia.
Qed.
Lemma sum_Z_range_filter_indicator__edge_benefit_and_choice :
  forall low high (P : Z -> Prop) f,
    sum (fun x => low <= x < high /\ P x) f =
    sum (fun x => low <= x < high)
        (fun x => if prop_dec (P x) then f x else 0).
Proof.
  intros low high P f.
  unfold sum.
  simpl.
  induction (Zrange low high) as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (prop_dec (P x)); simpl; rewrite IH; ring.
Qed.
Lemma latest_at_station_bounds__edge_benefit_and_choice :
  forall n m initial_dist times origins destinations latest station,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    0 <= station < n ->
    0 <= Znth station latest 0 <= 100000.
Proof.
  intros n m initial_dist times origins destinations latest station
    Hinputs Hlatest Hstation.
  unfold LatestDepartures in Hlatest.
  destruct Hlatest as [_ Hlatest].
  specialize (Hlatest station Hstation).
  unfold LatestAtStation, MaxMin.max_value_of_subset_with_default in Hlatest.
  destruct Hlatest as [[Hmaximum Hdefault] | [Hall Hdefault]].
  - destruct Hmaximum as [passenger [Hobject Hvalue]].
    destruct Hobject as [Hmember Hgreatest].
    destruct Hmember as [Hpassenger Horigin].
    unfold SightseeingInputsBounded in Hinputs.
    destruct Hinputs as [_ [_ [_ [_ [_ [_ [_ Hpassenger_bounds]]]]]]].
    specialize (Hpassenger_bounds passenger Hpassenger).
    cbn in Hvalue.
    lia.
  - cbn in Hdefault.
    lia.
Qed.
Lemma destination_count_bounds__edge_benefit_and_choice :
  forall n m destinations counts station,
    0 <= m ->
    DestinationCounts n m destinations counts ->
    0 <= station < n ->
    0 <= Znth station counts 0 <= m.
Proof.
  intros n m destinations counts station Hm Hcounts Hstation.
  unfold DestinationCounts in Hcounts.
  destruct Hcounts as [_ Hcounts].
  specialize (Hcounts station Hstation).
  rewrite Hcounts.
  rewrite sum_Z_range_filter_indicator__edge_benefit_and_choice.
  split.
  - eapply Z.le_trans with (m := (m - 0) * 0); [lia |].
    apply sum_Z_range_lower_bound; [lia |].
    intros passenger Hpassenger.
    destruct (prop_dec (Znth passenger destinations 0 = station + 1));
      cbn; lia.
  - eapply Z.le_trans with (m := (m - 0) * 1).
    + apply sum_Z_range_upper_bound; [lia |].
      intros passenger Hpassenger.
      destruct (prop_dec (Znth passenger destinations 0 = station + 1));
        cbn; lia.
    + lia.
Qed.
Lemma booster_progress_arrival_bounds__edge_benefit_and_choice :
  forall n m budget remaining initial_dist times origins destinations
         final_dist latest counts arrivals,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    BoosterProgress n m budget remaining
      initial_dist times origins destinations
      final_dist latest counts arrivals ->
    forall station, 0 <= station < n ->
      0 <= Znth station arrivals 0 <= 200000.
Proof.
  intros n m budget remaining initial_dist times origins destinations
    final_dist latest counts arrivals Hinputs Hprogress station Hstation.
  pose proof Hinputs as Hinput_bounds.
  unfold SightseeingInputsBounded in Hinput_bounds.
  destruct Hinput_bounds as
    [Hn [Hm [Hinitial_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hinitial_bounds Hpassenger_bounds]]]]]]].
  unfold BoosterProgress in Hprogress.
  destruct Hprogress as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]].
  try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
  destruct Hfeasible as [Hfinal_len [Hfinal_bounds Hbudget]].
  destruct Hschedule as [Harrival_len [Harrival_zero Harrival_step]].
  assert (Hstrong : forall j, 0 <= j < n ->
      0 <= Znth j arrivals 0 <= 100000 + 100 * j).
  {
    intros j Hj.
    assert (Hrepr : j = Z.of_nat (Z.to_nat j)).
    { rewrite Z2Nat.id; lia. }
    rewrite Hrepr in *.
    remember (Z.to_nat j) as j_nat.
    clear j Hrepr Heqj_nat.
    induction j_nat as [|j_nat IH].
    - cbn.
      rewrite Harrival_zero.
      lia.
    - rewrite Nat2Z.inj_succ in *.
      assert (Hprevious_range : 0 <= Z.of_nat j_nat < n) by lia.
      specialize (IH ltac:(lia)).
      specialize (Harrival_step (Z.of_nat j_nat) ltac:(lia)).
      destruct Harrival_step as [departure [Hdeparture Harrival]].
      pose proof (latest_at_station_bounds__edge_benefit_and_choice
        n m initial_dist times origins destinations latest
        (Z.of_nat j_nat) Hinputs Hlatest Hprevious_range) as Hlatest_bound.
      specialize (Hfinal_bounds (Z.of_nat j_nat) ltac:(lia)).
      specialize (Hinitial_bounds (Z.of_nat j_nat) ltac:(lia)).
      pose proof (station_departure_bounds__comparison_completion
        arrivals latest (Z.of_nat j_nat) departure
        (100000 + 100 * Z.of_nat j_nat)
        Hdeparture IH ltac:(lia)) as Hdeparture_bound.
      replace (Z.succ (Z.of_nat j_nat)) with
        (Z.of_nat j_nat + 1) by lia.
      rewrite Harrival.
      lia.
  }
  specialize (Hstrong station Hstation).
  lia.
Qed.
Lemma booster_progress_station_bounds__edge_benefit_and_choice :
  forall n m budget remaining initial_dist times origins destinations
         final_dist latest counts arrivals,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    BoosterProgress n m budget remaining
      initial_dist times origins destinations
      final_dist latest counts arrivals ->
    forall station, 0 <= station < n ->
      0 <= Znth station latest 0 <= 100000 /\
      0 <= Znth station counts 0 <= m /\
      0 <= Znth station arrivals 0 <= 200000.
Proof.
  intros n m budget remaining initial_dist times origins destinations
    final_dist latest counts arrivals Hinputs Hprogress station Hstation.
  pose proof Hprogress as Hfields.
  unfold BoosterProgress in Hfields.
  destruct Hfields as
    [Hlatest [Hcounts [Hfeasible [Hschedule Hminimum]]]].
  pose proof Hinputs as Hinput_bounds.
  unfold SightseeingInputsBounded in Hinput_bounds.
  destruct Hinput_bounds as [Hn [Hm Hrest]].
  split.
  - eapply latest_at_station_bounds__edge_benefit_and_choice; eauto.
  - split.
    + eapply destination_count_bounds__edge_benefit_and_choice.
      * lia.
      * exact Hcounts.
      * exact Hstation.
    + eapply booster_progress_arrival_bounds__edge_benefit_and_choice; eauto.
Qed.
Lemma marginal_scan_to_edge_benefit__edge_benefit_scan :
  forall n counts latest arrivals edge next benefit result,
    edge < n - 1 ->
    edge + 1 <= next <= n ->
    MarginalBenefitScan counts latest arrivals edge next benefit ->
    ((next = n /\ result = benefit) \/
     (next < n /\
      Znth next arrivals 0 <= Znth next latest 0 /\
      result = benefit + Znth next counts 0)) ->
    EdgeMarginalBenefit n counts latest arrivals edge result.
Proof.
  intros n counts latest arrivals edge next benefit result Hedge Hrange Hscan Hstop.
  apply EdgeMarginalBenefit_unfold.
  destruct Hstop as [[-> ->] | [Hnext [Hbreak ->]]].
  - exists n.
    rewrite MarginalBenefitScan_unfold in Hscan.
    destruct Hscan as [Hsum Hstrict].
    split.
    + lia.
    + split.
      * intros station Hstation.
        apply Hstrict.
        lia.
      * split.
        -- left; reflexivity.
        -- exact Hsum.
  - exists (next + 1).
    rewrite MarginalBenefitScan_unfold in Hscan.
    destruct Hscan as [Hsum Hstrict].
    split.
    + lia.
    + split.
      * intros station Hstation.
        apply Hstrict.
        lia.
      * split.
        -- right.
           replace (next + 1 - 1) with next by lia.
           exact Hbreak.
        -- rewrite sum_Z_range_extend_right by lia.
           lia.
Qed.
Lemma edge_marginal_benefit_unique__edge_choice :
  forall n counts latest arrivals edge benefit1 benefit2,
    EdgeMarginalBenefit n counts latest arrivals edge benefit1 ->
    EdgeMarginalBenefit n counts latest arrivals edge benefit2 ->
    benefit1 = benefit2.
Proof.
  intros n counts latest arrivals edge benefit1 benefit2 Hbenefit1 Hbenefit2.
  rewrite EdgeMarginalBenefit_unfold in *.
  destruct Hbenefit1 as
      [stop1 [[Hstop1_lo Hstop1_hi]
        [Hbefore1 [Hstop1 Hvalue1]]]].
  destruct Hbenefit2 as
      [stop2 [[Hstop2_lo Hstop2_hi]
        [Hbefore2 [Hstop2 Hvalue2]]]].
  assert (Hstops : stop1 = stop2).
  {
    destruct (Z.lt_trichotomy stop1 stop2) as
        [Hlt | [Heq | Hgt]]; [| exact Heq |].
    - destruct Hstop1 as [Hstop1_n | Hblocked1].
      + lia.
      + specialize (Hbefore2 (stop1 - 1) ltac:(lia)).
        lia.
    - destruct Hstop2 as [Hstop2_n | Hblocked2].
      + lia.
      + specialize (Hbefore1 (stop2 - 1) ltac:(lia)).
        lia.
  }
  subst stop2.
  congruence.
Qed.
Lemma eligible_edge_benefit_prefix_step__edge_choice :
  forall n dist counts latest arrivals i cnt,
    0 <= i ->
    i < n - 1 ->
    0 < Znth i dist 0 ->
    EdgeMarginalBenefit n counts latest arrivals i cnt ->
    forall choice,
      EligibleEdgeBenefit n dist counts latest arrivals (i + 1) choice <->
      EligibleEdgeBenefit n dist counts latest arrivals i choice \/
      (i, cnt) = choice.
Proof.
  intros n dist counts latest arrivals i cnt Hi Hi_bound Hdist Hbenefit
         [edge benefit].
  unfold EligibleEdgeBenefit; cbn.
  split.
  - intros [[Hedge_nonneg Hedge_next]
            [Hedge_bound [Hedge_dist Hedge_benefit]]].
    destruct (Z_lt_ge_dec edge i) as [Hedge_old | Hedge_current].
    + left. repeat split; assumption.
    + right.
      assert (Hedge_eq : edge = i) by lia.
      subst edge.
      assert (Hbenefit_eq : cnt = benefit).
      { eapply edge_marginal_benefit_unique__edge_choice; eauto. }
      subst benefit.
      reflexivity.
  - intros [Hold | Hcurrent].
    + destruct Hold as
          [[Hedge_nonneg Hedge_old]
            [Hedge_bound [Hedge_dist Hedge_benefit]]].
      repeat split; try assumption; lia.
    + injection Hcurrent as Hedge_eq Hbenefit_eq.
      subst edge benefit.
      repeat split; try assumption; lia.
Qed.
Lemma edge_choice_prefix_step__edge_choice :
  forall n dist counts latest arrivals i best position cnt,
    EdgeChoicePrefix n dist counts latest arrivals i best position ->
    0 <= i ->
    i < n - 1 ->
    0 < Znth i dist 0 ->
    EdgeMarginalBenefit n counts latest arrivals i cnt ->
    (best < cnt ->
       EdgeChoicePrefix
         n dist counts latest arrivals (i + 1) cnt i) /\
    (cnt <= best ->
       EdgeChoicePrefix
         n dist counts latest arrivals (i + 1) best position).
Proof.
  intros n dist counts latest arrivals i best position cnt
         [Hmaximum Hposition] Hi Hi_bound Hdist Hbenefit.
  assert (Hmaximum_next :
    max_value_of_subset_with_default Z.le
      (EligibleEdgeBenefit n dist counts latest arrivals (i + 1))
      (fun choice => snd choice) 0 (le_max Z.le best cnt)).
  {
    eapply (max_default_union_1_right Z.le best cnt (i, cnt)).
    - exact Hmaximum.
    - reflexivity.
    - intro choice.
      apply eligible_edge_benefit_prefix_step__edge_choice; assumption.
  }
  assert (Hcurrent :
    EligibleEdgeBenefit
      n dist counts latest arrivals (i + 1) (i, cnt)).
  {
    apply (proj2
      (eligible_edge_benefit_prefix_step__edge_choice
        n dist counts latest arrivals i cnt
        Hi Hi_bound Hdist Hbenefit (i, cnt))).
    right; reflexivity.
  }
  split.
  - intro Hbetter.
    unfold EdgeChoicePrefix.
    split.
    + rewrite (max_r Z.le best cnt ltac:(lia)) in Hmaximum_next.
      exact Hmaximum_next.
    + right; exact Hcurrent.
  - intro Hnot_better.
    unfold EdgeChoicePrefix.
    split.
    + rewrite (max_l Z.le best cnt ltac:(lia)) in Hmaximum_next.
      exact Hmaximum_next.
    + destruct Hposition as [Hdefault | Hold].
      * left; exact Hdefault.
      * right.
        apply (proj2
          (eligible_edge_benefit_prefix_step__edge_choice
            n dist counts latest arrivals i cnt
            Hi Hi_bound Hdist Hbenefit (position, best))).
        left; exact Hold.
Qed.
Lemma edge_choice_prefix_skip__edge_choice :
  forall n dist counts latest arrivals i best position,
    Znth i dist 0 <= 0 ->
    0 <= i ->
    i < n - 1 ->
    (forall edge, 0 <= edge < n - 1 -> 0 <= Znth edge dist 0) ->
    EdgeChoicePrefix n dist counts latest arrivals i best position ->
    EdgeChoicePrefix
      n dist counts latest arrivals (i + 1) best position.
Proof.
  intros n dist counts latest arrivals i best position
         Hnonpos Hi Hi_bound Hdist_nonneg [Hmaximum Hposition].
  assert (Heligible : forall choice,
    EligibleEdgeBenefit n dist counts latest arrivals (i + 1) choice <->
    EligibleEdgeBenefit n dist counts latest arrivals i choice).
  {
    intros [edge benefit].
    unfold EligibleEdgeBenefit; cbn.
    split.
    - intros [[Hedge_nonneg Hedge_next]
              [Hedge_bound [Hedge_dist Hedge_benefit]]].
      assert (Hedge_neq : edge <> i).
      {
        intro Hedge_eq; subst edge.
        specialize (Hdist_nonneg i ltac:(lia)).
        lia.
      }
      repeat split; try assumption; lia.
    - intros [[Hedge_nonneg Hedge_old]
              [Hedge_bound [Hedge_dist Hedge_benefit]]].
      repeat split; try assumption; lia.
  }
  unfold EdgeChoicePrefix.
  split.
  - eapply (max_default_eq_forward Z.le).
    + exact Hmaximum.
    + intros choice Hchoice.
      exists choice; split.
      * apply (proj2 (Heligible choice)); exact Hchoice.
      * lia.
    + intros choice Hchoice.
      exists choice; split.
      * apply (proj1 (Heligible choice)); exact Hchoice.
      * lia.
  - destruct Hposition as [Hdefault | Hold].
    + left; exact Hdefault.
    + right.
      apply (proj2 (Heligible (position, best))).
      exact Hold.
Qed.
Lemma fold_Zsum_add__edge_benefit_scan :
  forall (xs : list Z) (f g : Z -> Z),
    fold_right (fun x acc => (f x + g x) + acc) 0 xs =
    fold_right (fun x acc => f x + acc) 0 xs +
    fold_right (fun x acc => g x + acc) 0 xs.
Proof.
  induction xs as [|x xs IH]; intros f g; simpl.
  - ring.
  - rewrite IH. ring.
Qed.
Lemma fold_Zsum_nested_swap__edge_benefit_scan :
  forall (xs ys : list Z) (f : Z -> Z -> Z),
    fold_right
      (fun x acc => fold_right (fun y acc => f x y + acc) 0 ys + acc)
      0 xs =
    fold_right
      (fun y acc => fold_right (fun x acc => f x y + acc) 0 xs + acc)
      0 ys.
Proof.
  induction xs as [|x xs IH]; intros ys f; simpl.
  - induction ys as [|y ys IHys]; simpl; auto.
  - rewrite IH.
    rewrite <- fold_Zsum_add__edge_benefit_scan.
    reflexivity.
Qed.
Lemma sum_Z_range_nested_swap__edge_benefit_scan :
  forall x_low x_high y_low y_high f,
    sum (fun x => x_low <= x < x_high)
        (fun x => sum (fun y => y_low <= y < y_high)
                      (fun y => f x y)) =
    sum (fun y => y_low <= y < y_high)
        (fun y => sum (fun x => x_low <= x < x_high)
                      (fun x => f x y)).
Proof.
  intros x_low x_high y_low y_high f.
  rewrite !sum_range_unfold.
  apply fold_Zsum_nested_swap__edge_benefit_scan.
Qed.
Lemma sum_Z_range_filter_indicator__edge_benefit_scan :
  forall low high (P : Z -> Prop) f,
    sum (fun x => low <= x < high /\ P x) f =
    sum (fun x => low <= x < high)
        (fun x => if prop_dec (P x) then f x else 0).
Proof.
  intros low high P f.
  unfold sum.
  simpl.
  induction (Zrange low high) as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (prop_dec (P x)); simpl; rewrite IH; ring.
Qed.
Lemma destination_indicator_interval_bound__edge_benefit_scan :
  forall low high destination,
    sum (fun station => low <= station < high)
        (fun station =>
           if prop_dec (destination = station + 1) then 1 else 0) <= 1.
Proof.
  intros low high destination.
  destruct (Z_lt_ge_dec (destination - 1) low) as [Hbelow | Hnotbelow].
  - rewrite sum_Z_range_eq_zero.
    + lia.
    + intros station Hstation.
      destruct (prop_dec (destination = station + 1)); [lia | reflexivity].
  - destruct (Z_lt_ge_dec (destination - 1) high) as [Hinside | Habove].
    + rewrite (sum_Z_range_split low (destination - 1) high) by lia.
      assert (Hleft :
        sum (fun station => low <= station < destination - 1)
            (fun station =>
               if prop_dec (destination = station + 1) then 1 else 0) = 0).
      {
        apply sum_Z_range_eq_zero.
        intros station Hstation.
        destruct (prop_dec (destination = station + 1)); [lia | reflexivity].
      }
      assert (Htail :
        sum (fun station => destination - 1 + 1 <= station < high)
            (fun station =>
               if prop_dec (destination = station + 1) then 1 else 0) = 0).
      {
        apply sum_Z_range_eq_zero.
        intros station Hstation.
        destruct (prop_dec (destination = station + 1)); [lia | reflexivity].
      }
      rewrite Hleft.
      rewrite sum_Z_range_cons by lia.
      rewrite Htail.
      destruct (prop_dec (destination = destination - 1 + 1)); lia.
    + rewrite sum_Z_range_eq_zero.
      * lia.
      * intros station Hstation.
        destruct (prop_dec (destination = station + 1)); [lia | reflexivity].
Qed.
Lemma destination_count_interval_bound__edge_benefit_scan :
  forall n m destinations counts low high,
    0 <= m ->
    0 <= low /\ low <= high /\ high <= n ->
    DestinationCounts n m destinations counts ->
    sum (fun station => low <= station < high)
        (fun station => Znth station counts 0) <= m.
Proof.
  intros n m destinations counts low high Hm Hrange Hcounts.
  destruct Hcounts as [_ Hcount].
  rewrite (sum_Z_range_ext low high
    (fun station => Znth station counts 0)
    (fun station =>
       sum (fun passenger => 0 <= passenger < m)
           (fun passenger =>
              if prop_dec (Znth passenger destinations 0 = station + 1)
              then 1 else 0))).
  2: {
    intros station Hstation.
    rewrite Hcount by lia.
    apply sum_Z_range_filter_indicator__edge_benefit_scan.
  }
  rewrite sum_Z_range_nested_swap__edge_benefit_scan.
  eapply Z.le_trans.
  - apply sum_Z_range_le.
    intros passenger Hpassenger.
    apply destination_indicator_interval_bound__edge_benefit_scan.
  - rewrite sum_Z_range_const by lia.
    lia.
Qed.
Lemma arrival_repair_progress_init__arrival_repair :
  forall n old_dist old_arrivals latest edge,
    Zlength old_dist = n - 1 ->
    0 <= edge < n - 1 ->
    0 < Znth edge old_dist 0 ->
    ArrivalRepairProgress
      n old_dist old_arrivals
      (replace_Znth edge (Znth edge old_dist 0 - 1) old_dist)
      old_arrivals latest edge (edge + 1).
Proof.
  intros n old_dist old_arrivals latest edge Hdist Hedge _.
  rewrite ArrivalRepairProgress_unfold.
  split.
  - intros candidate Hcandidate.
    destruct (Z.eq_dec candidate edge) as [-> | Hne].
    + destruct (Z.eq_dec edge edge) as [_ | Hcontra]; [| contradiction].
      rewrite Znth_replace_Znth_Same by lia.
      reflexivity.
    + destruct (Z.eq_dec candidate edge) as [Hcontra | _]; [contradiction |].
      rewrite Znth_replace_Znth_Diff by lia.
      reflexivity.
  - split.
    + intros station _.
      reflexivity.
    + split.
      * intros station Hstation.
        lia.
      * intros station _.
        reflexivity.
Qed.
Lemma arrival_repair_progress_step__arrival_repair :
  forall n old_dist old_arrivals new_dist new_arrivals latest edge station,
    Zlength new_arrivals = n ->
    0 <= station < n ->
    0 <= edge ->
    edge < station ->
    ArrivalRepairProgress
      n old_dist old_arrivals new_dist new_arrivals latest edge station ->
    Znth station
      (replace_Znth station (Znth station new_arrivals 0 - 1) new_arrivals) 0 >=
      Znth station latest 0 ->
    ArrivalRepairProgress
      n old_dist old_arrivals new_dist
      (replace_Znth station (Znth station new_arrivals 0 - 1) new_arrivals)
      latest edge (station + 1).
Proof.
  intros n old_dist old_arrivals new_dist new_arrivals latest edge station
    Harrivals Hstation Hedge_nonnegative Hedge Hprogress Hguard.
  rewrite ArrivalRepairProgress_unfold in *.
  destruct Hprogress as [Hdist [Hbefore [Hchanged Hafter]]].
  split; [exact Hdist |].
  split.
  - intros j Hj.
    rewrite Znth_replace_Znth_Diff by lia.
    apply Hbefore; lia.
  - split.
    + intros j Hj.
      destruct (Z.eq_dec j station) as [-> | Hne].
      * split.
        -- rewrite Znth_replace_Znth_Same by lia.
           specialize (Hafter station ltac:(lia)).
           lia.
        -- lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        apply Hchanged; lia.
    + intros j Hj.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Hafter; lia.
Qed.
Lemma arrival_repair_progress_outcome__arrival_repair :
  forall n old_dist old_arrivals new_dist new_arrivals updated_arrivals latest
         edge stop,
    Zlength new_arrivals = n ->
    0 <= edge < n - 1 ->
    edge + 1 <= stop <= n ->
    ArrivalRepairProgress
      n old_dist old_arrivals new_dist new_arrivals latest edge stop ->
    ((stop = n /\ updated_arrivals = new_arrivals) \/
     (stop < n /\
      updated_arrivals =
        replace_Znth stop (Znth stop new_arrivals 0 - 1) new_arrivals /\
      Znth stop updated_arrivals 0 < Znth stop latest 0)) ->
    ArrivalRepairOutcome
      n old_dist old_arrivals new_dist updated_arrivals latest edge.
Proof.
  intros n old_dist old_arrivals new_dist new_arrivals updated_arrivals latest
    edge stop Harrivals Hedge Hstop Hprogress Hfinish.
  rewrite ArrivalRepairProgress_unfold in Hprogress.
  destruct Hprogress as [Hdist [Hbefore [Hchanged Hafter]]].
  rewrite ArrivalRepairOutcome_unfold.
  exists stop.
  split; [exact Hstop |].
  destruct Hfinish as [[Hdone ->] | [Hearly [-> Hguard]]].
  - split; [exact Hdist |].
    split; [exact Hbefore |].
    split; [exact Hchanged |].
    left.
    split; [exact Hdone |].
    intros station Hstation.
    apply Hchanged; lia.
  - split; [exact Hdist |].
    split.
    + intros station Hstation.
      rewrite Znth_replace_Znth_Diff by lia.
      apply Hbefore; lia.
    + split.
      * intros station Hstation.
        rewrite Znth_replace_Znth_Diff by lia.
        apply Hchanged; lia.
      * right.
        repeat split; try assumption.
        -- rewrite Znth_replace_Znth_Same by lia.
           specialize (Hafter stop ltac:(lia)).
           lia.
        -- intros station Hstation.
           rewrite Znth_replace_Znth_Diff by lia.
           apply Hafter; lia.
Qed.
Lemma sum_range_with_redundant_upper__travel_and_return :
  forall (high bound : Z) (f : Z -> Z),
    high <= bound ->
    Sum.sum (fun x => 0 <= x < high /\ x < bound) f =
    Sum.sum (fun x => 0 <= x < high) f.
Proof.
  intros high bound f Hbound.
  unfold Sum.sum.
  simpl.
  assert (Hfilter :
    filter (fun x => if prop_dec (x < bound) then true else false)
           (Zrange 0 high) = Zrange 0 high).
  {
    remember (Zrange 0 high) as xs eqn:Hrange.
    assert (Hxs : forall x, In x xs -> x < bound).
    {
      intros x Hx.
      rewrite Hrange in Hx.
      apply <- In_Zrange in Hx.
      lia.
    }
    clear Hrange.
    induction xs as [|x xs IH]; simpl.
    - reflexivity.
    - destruct (prop_dec (x < bound)) as [Hxlt | Hnot].
      + f_equal.
        apply IH.
        intros y Hy.
        apply Hxs.
        right; exact Hy.
      + exfalso.
        apply Hnot, Hxs.
        left; reflexivity.
  }
  rewrite Hfilter.
  reflexivity.
Qed.
Lemma travel_sum_prefix_step__travel_and_return :
  forall (m : Z) (times destinations arrivals : list Z)
         (processed total : Z),
    0 <= processed ->
    processed < m ->
    TravelSumPrefix m times destinations arrivals processed total ->
    TravelSumPrefix m times destinations arrivals (processed + 1)
      (total +
       (Znth (Znth processed destinations 0 - 1) arrivals 0 -
        Znth processed times 0)).
Proof.
  intros m times destinations arrivals processed total
    Hprocessed Hlt Hprefix.
  unfold TravelSumPrefix in *.
  rewrite (sum_range_with_redundant_upper__travel_and_return
             processed m) in Hprefix by lia.
  rewrite (sum_range_with_redundant_upper__travel_and_return
             (processed + 1) m) by lia.
  rewrite sum_Z_range_extend_right by lia.
  lia.
Qed.
Lemma travel_sum_prefix_complete__travel_and_return :
  forall (m : Z) (times destinations arrivals : list Z) (total : Z),
    0 <= m ->
    (TravelSumPrefix m times destinations arrivals m total <->
     PassengerTravelTotal m times destinations arrivals total).
Proof.
  intros m times destinations arrivals total Hm.
  unfold TravelSumPrefix, PassengerTravelTotal.
  rewrite (sum_range_with_redundant_upper__travel_and_return m m) by lia.
  tauto.
Qed.
Lemma max_default_member_le__travel_and_return :
  forall {A : Type} (P : A -> Prop) (f : A -> Z)
         (default maximum : Z) (a : A),
    max_value_of_subset_with_default Z.le P f default maximum ->
    P a ->
    f a <= maximum.
Proof.
  intros A P f default maximum a Hmaximum Ha.
  destruct Hmaximum as [[Hmaximum _] | [Hall Heq]].
  - destruct Hmaximum as [maximum_object [[_ Hsound] Hvalue]].
    subst maximum.
    apply Hsound, Ha.
  - subst maximum.
    apply Hall, Ha.
Qed.
Lemma bus_arrival_step_nondec__travel_and_return :
  forall (n m : Z) (initial_dist times origins destinations : list Z)
         (final_dist latest arrivals : list Z) (station : Z),
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    BusArrivalSchedule n final_dist latest arrivals ->
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge final_dist 0) ->
    0 <= station < n - 1 ->
    Znth station arrivals 0 <= Znth (station + 1) arrivals 0.
Proof.
  intros n m initial_dist times origins destinations
    final_dist latest arrivals station _ Hschedule Hdist Hstation.
  destruct Hschedule as [_ [_ Hnext]].
  specialize (Hnext station Hstation).
  destruct Hnext as [departure [Hdeparture Harrival]].
  unfold StationDeparture,
    max_value_of_subset_with_default in Hdeparture.
  assert (Hdeparture_default : Znth station arrivals 0 <= departure).
  {
    destruct Hdeparture as [[_ Hdefault] | [_ Heq]].
    - exact Hdefault.
    - lia.
  }
  specialize (Hdist station Hstation).
  lia.
Qed.
Lemma bus_arrivals_nondecreasing__travel_and_return :
  forall (n m : Z) (initial_dist times origins destinations : list Z)
         (final_dist latest arrivals : list Z) (lo hi : Z),
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    FeasibleBoostedDistances n 0 initial_dist final_dist \/
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge final_dist 0) ->
    BusArrivalSchedule n final_dist latest arrivals ->
    0 <= lo -> lo <= hi -> hi < n ->
    Znth lo arrivals 0 <= Znth hi arrivals 0.
Proof.
  intros n m initial_dist times origins destinations
    final_dist latest arrivals lo hi Hinputs Hdist_or Hschedule
    Hlo Hlohi Hhi.
  assert (Hdist : forall edge, 0 <= edge < n - 1 ->
      0 <= Znth edge final_dist 0).
  {
    destruct Hdist_or as [Hfeasible | Hdist]; [|exact Hdist].
    try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
    destruct Hfeasible as [_ [Hdist _]].
    intros edge Hedge.
    specialize (Hdist edge Hedge).
    lia.
  }
  assert (Hnat : forall d : nat,
    lo + Z.of_nat d < n ->
    Znth lo arrivals 0 <= Znth (lo + Z.of_nat d) arrivals 0).
  {
    induction d as [|d IH].
    - intros _.
      replace (lo + Z.of_nat 0) with lo by lia.
      apply Z.le_refl.
    - intros Hd.
      replace (lo + Z.of_nat (S d))
        with ((lo + Z.of_nat d) + 1) by lia.
      eapply Z.le_trans.
      + apply IH; lia.
      + eapply bus_arrival_step_nondec__travel_and_return;
          eauto; lia.
  }
  specialize (Hnat (Z.to_nat (hi - lo))).
  replace (lo + Z.of_nat (Z.to_nat (hi - lo))) with hi in Hnat by lia.
  apply Hnat; exact Hhi.
Qed.
Lemma arrival_dominates_passenger_time__travel_and_return :
  forall (n m : Z) (initial_dist times origins destinations : list Z)
         (final_dist latest arrivals : list Z) (passenger : Z),
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    FeasibleBoostedDistances n 0 initial_dist final_dist \/
    (forall edge, 0 <= edge < n - 1 ->
       0 <= Znth edge final_dist 0) ->
    BusArrivalSchedule n final_dist latest arrivals ->
    0 <= passenger < m ->
    Znth passenger times 0 <=
      Znth (Znth passenger destinations 0 - 1) arrivals 0.
Proof.
  intros n m initial_dist times origins destinations
    final_dist latest arrivals passenger
    Hinputs Hlatest Hdist_or Hschedule Hpassenger.
  pose proof Hinputs as Hbounds.
  destruct Hbounds as
    [Hn [Hm [Hdist_len [Htimes_len [Horigins_len
      [Hdestinations_len [Hinitial_dist Hpassenger_bounds]]]]]]].
  specialize (Hpassenger_bounds passenger Hpassenger).
  destruct Hpassenger_bounds as
    [Htime [[Horigin_lower Horigin_destination] Hdestination_upper]].
  destruct Hlatest as [_ Hlatest].
  specialize (Hlatest (Znth passenger origins 0 - 1) ltac:(lia)).
  unfold LatestAtStation in Hlatest.
  pose proof
    (max_default_member_le__travel_and_return
       (fun candidate =>
          0 <= candidate < m /\
          Znth candidate origins 0 =
            (Znth passenger origins 0 - 1) + 1)
       (fun candidate => Znth candidate times 0)
       0 (Znth (Znth passenger origins 0 - 1) latest 0)
       passenger Hlatest ltac:(split; [exact Hpassenger | lia]))
    as Htime_latest.
  cbn in Htime_latest.
  pose proof Hschedule as Hschedule_step.
  destruct Hschedule_step as [_ [_ Hnext]].
  specialize (Hnext (Znth passenger origins 0 - 1) ltac:(lia)).
  destruct Hnext as [departure [Hdeparture Harrival]].
  unfold StationDeparture,
    max_value_of_subset_with_default in Hdeparture.
  assert (Hlatest_departure :
    Znth (Znth passenger origins 0 - 1) latest 0 <= departure).
  {
    destruct Hdeparture as [[Hmaximum _] | [Hall Heq]].
    - destruct Hmaximum as [candidate [[Hcandidate Hsound] Hvalue]].
      specialize (Hsound
        (Znth (Znth passenger origins 0 - 1) latest 0) eq_refl).
      simpl in Hsound, Hvalue.
      lia.
    - specialize (Hall
        (Znth (Znth passenger origins 0 - 1) latest 0) eq_refl).
      lia.
  }
  assert (Hdist : forall edge, 0 <= edge < n - 1 ->
      0 <= Znth edge final_dist 0).
  {
    destruct Hdist_or as [Hfeasible | Hdist]; [|exact Hdist].
    try rewrite FeasibleBoostedDistances_unfold in Hfeasible.
    destruct Hfeasible as [_ [Hdist _]].
    intros edge Hedge.
    specialize (Hdist edge Hedge).
    lia.
  }
  specialize (Hdist (Znth passenger origins 0 - 1) ltac:(lia)).
  assert (Horigin_arrival :
    Znth passenger times 0 <=
      Znth (Znth passenger origins 0) arrivals 0).
  {
    replace (Znth passenger origins 0)
      with ((Znth passenger origins 0 - 1) + 1) by lia.
    rewrite Harrival.
    lia.
  }
  eapply Z.le_trans; [exact Horigin_arrival |].
  eapply bus_arrivals_nondecreasing__travel_and_return;
    eauto; lia.
Qed.
Lemma chain_gap_clamp_distances_exists__termination_and_travel_total :
  forall n current_used candidate_used initial_dist current_dist candidate_dist,
    2 <= n ->
    FeasibleBoostedDistances
      n current_used initial_dist current_dist ->
    FeasibleBoostedDistances
      n candidate_used initial_dist candidate_dist ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge current_dist 0) =
      current_used ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge candidate_dist 0) =
      candidate_used ->
    current_used < candidate_used ->
    (forall station, 0 <= station <= n - 1 ->
       ChainIntervalDistance candidate_dist 0 station <=
       ChainIntervalDistance current_dist 0 station) ->
    exists old_dist next_dist,
      FeasibleBoostedDistances
        n (candidate_used - 1) initial_dist old_dist /\
      FeasibleBoostedDistances
        n (current_used + 1) initial_dist next_dist /\
      ChainPrefixClamp
        n current_dist candidate_dist old_dist next_dist /\
      ChainUnitCutPath n current_dist next_dist.
Proof.
  intros n current_used candidate_used initial_dist current_dist
    candidate_dist Hn Hcurrent_feasible Hcandidate_feasible
    Hcurrent_used Hcandidate_used Hused_lt Hbelow.
  rewrite FeasibleBoostedDistances_unfold in
    Hcurrent_feasible, Hcandidate_feasible.
  destruct Hcurrent_feasible as
    [Hcurrent_length [Hcurrent_bounds Hcurrent_budget]].
  try rewrite FeasibleBoostedDistances_unfold in Hcandidate_feasible.
  destruct Hcandidate_feasible as
    [Hcandidate_length [Hcandidate_bounds Hcandidate_budget]].
  set (current_prefix := fun station =>
    ChainIntervalDistance current_dist 0 station).
  set (candidate_plus := fun station =>
    ChainIntervalDistance candidate_dist 0 station + 1).
  set (old_prefix := fun station =>
    Z.min (current_prefix station) (candidate_plus station)).
  set (next_prefix := fun station =>
    Z.max (current_prefix station) (candidate_plus station) - 1).
  assert (Hcurrent_zero : current_prefix 0 = 0).
  {
    unfold current_prefix.
    apply chain_interval_empty__cut_exchange. lia.
  }
  assert (Hcandidate_plus_zero : candidate_plus 0 = 1).
  {
    unfold candidate_plus.
    rewrite chain_interval_empty__cut_exchange by lia.
    lia.
  }
  assert (Hold_zero : old_prefix 0 = 0).
  {
    unfold old_prefix.
    rewrite Hcurrent_zero, Hcandidate_plus_zero.
    reflexivity.
  }
  assert (Hnext_zero : next_prefix 0 = 0).
  {
    unfold next_prefix.
    rewrite Hcurrent_zero, Hcandidate_plus_zero.
    reflexivity.
  }
  destruct (chain_distance_from_prefix__cut_exchange
    n old_prefix ltac:(lia) Hold_zero) as
    [old_dist [Hold_length [Hold_value Hold_prefix]]].
  destruct (chain_distance_from_prefix__cut_exchange
    n next_prefix ltac:(lia) Hnext_zero) as
    [next_dist [Hnext_length [Hnext_value Hnext_prefix]]].
  exists old_dist, next_dist.
  assert (Hold_bounds : forall edge,
    0 <= edge < n - 1 ->
    0 <= Znth edge old_dist 0 <= Znth edge initial_dist 0).
  {
    intros edge Hedge.
    rewrite Hold_value by exact Hedge.
    unfold old_prefix.
    apply Z_min_increment_bounds__cut_exchange.
    - unfold current_prefix.
      rewrite chain_prefix_increment__cut_exchange by lia.
      apply Hcurrent_bounds. exact Hedge.
    - unfold candidate_plus.
      replace
        (ChainIntervalDistance candidate_dist 0 (edge + 1) + 1 -
         (ChainIntervalDistance candidate_dist 0 edge + 1))
        with
        (ChainIntervalDistance candidate_dist 0 (edge + 1) -
         ChainIntervalDistance candidate_dist 0 edge) by ring.
      rewrite chain_prefix_increment__cut_exchange by lia.
      apply Hcandidate_bounds. exact Hedge.
  }
  assert (Hnext_bounds : forall edge,
    0 <= edge < n - 1 ->
    0 <= Znth edge next_dist 0 <= Znth edge initial_dist 0).
  {
    intros edge Hedge.
    rewrite Hnext_value by exact Hedge.
    unfold next_prefix.
    replace
      (Z.max (current_prefix (edge + 1)) (candidate_plus (edge + 1)) - 1 -
       (Z.max (current_prefix edge) (candidate_plus edge) - 1))
      with
      (Z.max (current_prefix (edge + 1)) (candidate_plus (edge + 1)) -
       Z.max (current_prefix edge) (candidate_plus edge)) by ring.
    apply Z_max_increment_bounds__cut_exchange.
    - unfold current_prefix.
      rewrite chain_prefix_increment__cut_exchange by lia.
      apply Hcurrent_bounds. exact Hedge.
    - unfold candidate_plus.
      replace
        (ChainIntervalDistance candidate_dist 0 (edge + 1) + 1 -
         (ChainIntervalDistance candidate_dist 0 edge + 1))
        with
        (ChainIntervalDistance candidate_dist 0 (edge + 1) -
         ChainIntervalDistance candidate_dist 0 edge) by ring.
      rewrite chain_prefix_increment__cut_exchange by lia.
      apply Hcandidate_bounds. exact Hedge.
  }
  assert (Hendpoint_order :
    candidate_plus (n - 1) <= current_prefix (n - 1)).
  {
    unfold candidate_plus, current_prefix.
    rewrite chain_reduction_prefix__cut_exchange in
      Hcurrent_used, Hcandidate_used.
    lia.
  }
  assert (Hold_endpoint :
    old_prefix (n - 1) = candidate_plus (n - 1)).
  {
    unfold old_prefix.
    rewrite Z.min_r by exact Hendpoint_order.
    reflexivity.
  }
  assert (Hnext_endpoint :
    next_prefix (n - 1) = current_prefix (n - 1) - 1).
  {
    unfold next_prefix.
    rewrite Z.max_l by exact Hendpoint_order.
    reflexivity.
  }
  assert (Hold_budget :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge old_dist 0) <=
      candidate_used - 1).
  {
    rewrite chain_reduction_prefix__cut_exchange.
    rewrite Hold_prefix by lia.
    rewrite Hold_endpoint.
    unfold candidate_plus.
    rewrite chain_reduction_prefix__cut_exchange in Hcandidate_used.
    lia.
  }
  assert (Hnext_budget :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge next_dist 0) <=
      current_used + 1).
  {
    rewrite chain_reduction_prefix__cut_exchange.
    rewrite Hnext_prefix by lia.
    rewrite Hnext_endpoint.
    unfold current_prefix.
    rewrite chain_reduction_prefix__cut_exchange in Hcurrent_used.
    lia.
  }
  split.
  - apply FeasibleBoostedDistances_unfold. split; [exact Hold_length |].
    split; [exact Hold_bounds | exact Hold_budget].
  - split.
    + apply FeasibleBoostedDistances_unfold. split; [exact Hnext_length |].
      split; [exact Hnext_bounds | exact Hnext_budget].
    + split.
      * unfold ChainPrefixClamp.
        intros station Hstation.
        rewrite Hold_prefix by exact Hstation.
        rewrite Hnext_prefix by exact Hstation.
        unfold old_prefix, next_prefix, current_prefix, candidate_plus.
        split; [reflexivity | ring].
      * unfold ChainUnitCutPath.
        split.
        -- intros station Hstation.
           rewrite Hnext_prefix by exact Hstation.
           unfold next_prefix, current_prefix, candidate_plus.
           specialize (Hbelow station Hstation).
           destruct (Z_le_gt_dec
             (ChainIntervalDistance candidate_dist 0 station + 1)
             (ChainIntervalDistance current_dist 0 station)).
           ++ rewrite Z.max_l by lia. right. reflexivity.
           ++ rewrite Z.max_r by lia. left. lia.
        -- rewrite Hnext_prefix by lia.
           exact Hnext_endpoint.
Qed.
Lemma chain_gap_clamp_total_pair__termination_and_travel_total :
  forall n m current_used candidate_used
         initial_dist times origins destinations latest counts
         current_dist candidate_dist current_arrivals candidate_arrivals
         current_total candidate_total,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    DestinationCounts n m destinations counts ->
    FeasibleBoostedDistances
      n current_used initial_dist current_dist ->
    FeasibleBoostedDistances
      n candidate_used initial_dist candidate_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    BusArrivalSchedule n candidate_dist latest candidate_arrivals ->
    PassengerTravelTotal
      m times destinations current_arrivals current_total ->
    PassengerTravelTotal
      m times destinations candidate_arrivals candidate_total ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge current_dist 0) =
      current_used ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge candidate_dist 0) =
      candidate_used ->
    current_used < candidate_used ->
    (forall station, 0 <= station <= n - 1 ->
       ChainIntervalDistance candidate_dist 0 station <=
       ChainIntervalDistance current_dist 0 station) ->
    exists old_dist old_arrivals old_total
           next_dist next_arrivals next_total,
      FeasibleBoostedDistances
        n (candidate_used - 1) initial_dist old_dist /\
      BusArrivalSchedule n old_dist latest old_arrivals /\
      PassengerTravelTotal m times destinations old_arrivals old_total /\
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 - Znth edge old_dist 0) =
        candidate_used - 1 /\
      FeasibleBoostedDistances
        n (current_used + 1) initial_dist next_dist /\
      BusArrivalSchedule n next_dist latest next_arrivals /\
      PassengerTravelTotal m times destinations next_arrivals next_total /\
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 - Znth edge next_dist 0) =
        current_used + 1 /\
      ChainUnitCutPath n current_dist next_dist /\
      old_total + next_total <= current_total + candidate_total.
Proof.
  intros n m current_used candidate_used initial_dist times origins
    destinations latest counts current_dist candidate_dist
    current_arrivals candidate_arrivals current_total candidate_total
    Hinputs Hcounts Hcurrent_feasible Hcandidate_feasible
    Hcurrent_schedule Hcandidate_schedule Hcurrent_total Hcandidate_total
    Hcurrent_used Hcandidate_used Hused_lt Hbelow.
  assert (Hn : 2 <= n).
  { unfold SightseeingInputsBounded in Hinputs. lia. }
  destruct (chain_gap_clamp_distances_exists__termination_and_travel_total
    n current_used candidate_used initial_dist current_dist candidate_dist
    Hn Hcurrent_feasible Hcandidate_feasible Hcurrent_used Hcandidate_used
    Hused_lt Hbelow) as
    [old_dist [next_dist
      [Hold_feasible [Hnext_feasible [Hclamp Hpath]]]]].
  destruct (bus_schedule_exists__cut_exchange
    n old_dist latest ltac:(lia)) as [old_arrivals Hold_schedule].
  destruct (bus_schedule_exists__cut_exchange
    n next_dist latest ltac:(lia)) as [next_arrivals Hnext_schedule].
  set (old_total :=
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) old_arrivals 0 -
           Znth passenger times 0)).
  set (next_total :=
    sum (fun passenger => 0 <= passenger < m)
        (fun passenger =>
           Znth (Znth passenger destinations 0 - 1) next_arrivals 0 -
           Znth passenger times 0)).
  assert (Hold_total :
    PassengerTravelTotal m times destinations old_arrivals old_total).
  { unfold PassengerTravelTotal, old_total. reflexivity. }
  assert (Hnext_total :
    PassengerTravelTotal m times destinations next_arrivals next_total).
  { unfold PassengerTravelTotal, next_total. reflexivity. }
  set (current_weight :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station current_arrivals 0)).
  set (candidate_weight :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station candidate_arrivals 0)).
  set (old_weight :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station old_arrivals 0)).
  set (next_weight :=
    sum (fun station => 1 <= station < n)
        (fun station =>
           Znth station counts 0 * Znth station next_arrivals 0)).
  assert (Hcurrent_weight :
    ChainWeightedArrivalTotal n counts current_arrivals current_weight).
  { unfold ChainWeightedArrivalTotal, current_weight. reflexivity. }
  assert (Hcandidate_weight :
    ChainWeightedArrivalTotal n counts candidate_arrivals candidate_weight).
  { unfold ChainWeightedArrivalTotal, candidate_weight. reflexivity. }
  assert (Hold_weight :
    ChainWeightedArrivalTotal n counts old_arrivals old_weight).
  { unfold ChainWeightedArrivalTotal, old_weight. reflexivity. }
  assert (Hnext_weight :
    ChainWeightedArrivalTotal n counts next_arrivals next_weight).
  { unfold ChainWeightedArrivalTotal, next_weight. reflexivity. }
  pose proof (chain_weighted_arrival_clamp__cut_exchange
    n counts latest current_dist candidate_dist old_dist next_dist
    current_arrivals candidate_arrivals old_arrivals next_arrivals
    current_weight candidate_weight old_weight next_weight Hn
    (destination_counts_nonnegative__cut_exchange
      n m destinations counts Hcounts)
    Hcurrent_schedule Hcandidate_schedule Hold_schedule Hnext_schedule
    Hclamp Hcurrent_weight Hcandidate_weight Hold_weight Hnext_weight)
    as Hweighted_pair.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts current_arrivals
    Hinputs Hcounts) as Hidentity_current.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts candidate_arrivals
    Hinputs Hcounts) as Hidentity_candidate.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts old_arrivals
    Hinputs Hcounts) as Hidentity_old.
  pose proof (destination_counts_weighted_arrivals__chain_dual
    n m initial_dist times origins destinations counts next_arrivals
    Hinputs Hcounts) as Hidentity_next.
  assert (Htotal_pair :
    old_total + next_total <= current_total + candidate_total).
  {
    unfold PassengerTravelTotal in
      Hcurrent_total, Hcandidate_total, Hold_total, Hnext_total.
    rewrite sum_Z_range_sub in
      Hcurrent_total, Hcandidate_total, Hold_total, Hnext_total.
    unfold current_weight, candidate_weight, old_weight, next_weight
      in Hweighted_pair.
    rewrite Hidentity_current, Hidentity_candidate,
      Hidentity_old, Hidentity_next in Hweighted_pair.
    lia.
  }
  assert (Hold_used :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge old_dist 0) =
      candidate_used - 1).
  {
    rewrite chain_reduction_prefix__cut_exchange.
    pose proof (proj1 (Hclamp (n - 1) ltac:(lia))) as Hold_endpoint.
    rewrite Hold_endpoint.
    assert (Hendpoint_order :
      ChainIntervalDistance candidate_dist 0 (n - 1) + 1 <=
      ChainIntervalDistance current_dist 0 (n - 1)).
    {
      rewrite chain_reduction_prefix__cut_exchange in
        Hcurrent_used, Hcandidate_used.
      lia.
    }
    rewrite Z.min_r by exact Hendpoint_order.
    rewrite chain_reduction_prefix__cut_exchange in Hcandidate_used.
    lia.
  }
  assert (Hnext_used :
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge next_dist 0) =
      current_used + 1).
  {
    rewrite chain_reduction_prefix__cut_exchange.
    unfold ChainUnitCutPath in Hpath.
    destruct Hpath as [Hpath_pointwise Hpath_endpoint].
    rewrite Hpath_endpoint.
    rewrite chain_reduction_prefix__cut_exchange in Hcurrent_used.
    lia.
  }
  exists old_dist, old_arrivals, old_total,
    next_dist, next_arrivals, next_total.
  split; [exact Hold_feasible |].
  split; [exact Hold_schedule |].
  split; [exact Hold_total |].
  split; [exact Hold_used |].
  split; [exact Hnext_feasible |].
  split; [exact Hnext_schedule |].
  split; [exact Hnext_total |].
  split; [exact Hnext_used |].
  split; [exact Hpath |].
  exact Htotal_pair.
Qed.
Lemma zero_best_candidate_lower_by_gap__termination_and_travel_total :
  forall n m used initial_dist times origins destinations latest counts
         current_dist current_arrivals current_total best position gap,
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    LatestDepartures n m times origins latest ->
    DestinationCounts n m destinations counts ->
    FeasibleBoostedDistances n used initial_dist current_dist ->
    BusArrivalSchedule n current_dist latest current_arrivals ->
    PassengerTravelTotal
      m times destinations current_arrivals current_total ->
    SightseeingMinimumTotal
      n m used initial_dist times origins destinations current_total ->
    BestBoostChoice
      n current_dist counts latest current_arrivals best position ->
    best = 0 ->
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge current_dist 0) = used ->
    forall candidate_dist candidate_arrivals candidate_total,
      FeasibleBoostedDistances
        n (used + Z.of_nat gap) initial_dist candidate_dist ->
      BusArrivalSchedule n candidate_dist latest candidate_arrivals ->
      PassengerTravelTotal
        m times destinations candidate_arrivals candidate_total ->
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 - Znth edge candidate_dist 0) =
        used + Z.of_nat gap ->
      current_total <= candidate_total.
Proof.
  intros n m used initial_dist times origins destinations latest counts
    current_dist current_arrivals current_total best position gap
    Hinputs Hlatest Hcounts Hcurrent_feasible Hcurrent_schedule
    Hcurrent_total Hminimum Hchoice Hbest Hcurrent_used.
  assert (Hn : 2 <= n).
  { unfold SightseeingInputsBounded in Hinputs. lia. }
  induction gap as [|gap IH];
    intros candidate_dist candidate_arrivals candidate_total
      Hcandidate_feasible Hcandidate_schedule Hcandidate_total
      Hcandidate_used.
  - replace (used + Z.of_nat 0) with used in
      Hcandidate_feasible, Hcandidate_used by lia.
    assert (Hcandidate :
      SightseeingCandidateTotal
        n m used initial_dist times origins destinations candidate_total).
    {
      exists candidate_dist, latest, candidate_arrivals.
      exact (conj Hlatest
        (conj Hcandidate_feasible
          (conj Hcandidate_schedule Hcandidate_total))).
    }
    pose proof Hminimum as Hminimum_fields.
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset in Hminimum_fields.
    destruct Hminimum_fields as
      [minimum_witness [[Hminimum_member Hleast] Hvalue]].
    cbn in Hvalue.
    subst minimum_witness.
    specialize (Hleast candidate_total Hcandidate).
    cbn in Hleast.
    exact Hleast.
  - set (candidate_used := used + Z.of_nat (S gap)).
    assert (Hused_lt : used < candidate_used).
    { unfold candidate_used. rewrite Nat2Z.inj_succ. lia. }
    destruct (chain_passenger_total_lattice__cut_exchange
      n m used candidate_used
      initial_dist times origins destinations latest counts
      current_dist candidate_dist current_arrivals candidate_arrivals
      current_total candidate_total
      Hinputs Hcounts Hcurrent_feasible Hcandidate_feasible
      Hcurrent_schedule Hcandidate_schedule
      Hcurrent_total Hcandidate_total) as
      [meet_dist [meet_arrivals [meet_total
        [join_dist [join_arrivals [join_total
          [Hmeet_feasible [Hmeet_schedule [Hmeet_total
            [Hjoin_feasible [Hjoin_schedule [Hjoin_total
              [Hmeetjoin Hlattice_pair]]]]]]]]]]]]].
    replace (Z.max used candidate_used) with candidate_used
      in Hmeet_feasible by (rewrite Z.max_r; lia).
    replace (Z.min used candidate_used) with used
      in Hjoin_feasible by (rewrite Z.min_l; lia).
    assert (Hendpoint_order :
      ChainIntervalDistance candidate_dist 0 (n - 1) <=
      ChainIntervalDistance current_dist 0 (n - 1)).
    {
      change
        (sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 - Znth edge candidate_dist 0) =
         candidate_used) in Hcandidate_used.
      rewrite chain_reduction_prefix__cut_exchange in
        Hcurrent_used, Hcandidate_used.
      lia.
    }
    assert (Hmeet_used :
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 - Znth edge meet_dist 0) =
        candidate_used).
    {
      rewrite chain_reduction_prefix__cut_exchange.
      pose proof (proj1 (Hmeetjoin (n - 1) ltac:(lia)))
        as Hmeet_endpoint.
      rewrite Hmeet_endpoint.
      rewrite Z.min_r by exact Hendpoint_order.
      change
        (sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 - Znth edge candidate_dist 0) =
         candidate_used) in Hcandidate_used.
      rewrite chain_reduction_prefix__cut_exchange in Hcandidate_used.
      exact Hcandidate_used.
    }
    assert (Hjoin_used :
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 - Znth edge join_dist 0) = used).
    {
      rewrite chain_reduction_prefix__cut_exchange.
      pose proof (proj2 (Hmeetjoin (n - 1) ltac:(lia)))
        as Hjoin_endpoint.
      rewrite Hjoin_endpoint.
      rewrite Z.max_l by exact Hendpoint_order.
      rewrite chain_reduction_prefix__cut_exchange in Hcurrent_used.
      exact Hcurrent_used.
    }
    assert (Hmeet_below : forall station, 0 <= station <= n - 1 ->
      ChainIntervalDistance meet_dist 0 station <=
      ChainIntervalDistance current_dist 0 station).
    {
      intros station Hstation.
      pose proof (proj1 (Hmeetjoin station Hstation)) as Hmeet_prefix.
      rewrite Hmeet_prefix.
      apply Z.le_min_l.
    }
    assert (Hjoin_candidate :
      SightseeingCandidateTotal
        n m used initial_dist times origins destinations join_total).
    {
      exists join_dist, latest, join_arrivals.
      exact (conj Hlatest
        (conj Hjoin_feasible (conj Hjoin_schedule Hjoin_total))).
    }
    assert (Hjoin_lower : current_total <= join_total).
    {
      pose proof Hminimum as Hminimum_fields.
      unfold SightseeingMinimumTotal,
        MaxMin.min_value_of_subset,
        MaxMin.min_object_of_subset in Hminimum_fields.
      destruct Hminimum_fields as
        [minimum_witness [[Hminimum_member Hleast] Hvalue]].
      cbn in Hvalue.
      subst minimum_witness.
      specialize (Hleast join_total Hjoin_candidate).
      cbn in Hleast.
      exact Hleast.
    }
    destruct (chain_gap_clamp_total_pair__termination_and_travel_total
      n m used candidate_used
      initial_dist times origins destinations latest counts
      current_dist meet_dist current_arrivals meet_arrivals
      current_total meet_total
      Hinputs Hcounts Hcurrent_feasible Hmeet_feasible
      Hcurrent_schedule Hmeet_schedule Hcurrent_total Hmeet_total
      Hcurrent_used Hmeet_used Hused_lt Hmeet_below) as
      [old_dist [old_arrivals [old_total
        [next_dist [next_arrivals [next_total
          [Hold_feasible [Hold_schedule [Hold_total [Hold_used
            [Hnext_feasible [Hnext_schedule [Hnext_total [Hnext_used
              [Hpath Hclamp_pair]]]]]]]]]]]]]]].
    assert (Hold_feasible_gap :
      FeasibleBoostedDistances
        n (used + Z.of_nat gap) initial_dist old_dist).
    {
      replace (used + Z.of_nat gap) with (candidate_used - 1).
      - exact Hold_feasible.
      - unfold candidate_used. rewrite Nat2Z.inj_succ. lia.
    }
    assert (Hold_used_gap :
      sum (fun edge => 0 <= edge < n - 1)
          (fun edge =>
             Znth edge initial_dist 0 - Znth edge old_dist 0) =
        used + Z.of_nat gap).
    {
      replace (used + Z.of_nat gap) with (candidate_used - 1).
      - exact Hold_used.
      - unfold candidate_used. rewrite Nat2Z.inj_succ. lia.
    }
    pose proof (IH old_dist old_arrivals old_total
      Hold_feasible_gap Hold_schedule Hold_total Hold_used_gap)
      as Hold_lower.
    pose proof (chain_unit_cut_path_lower_bound__normalization
      n m used initial_dist times origins destinations latest counts
      current_dist next_dist current_arrivals next_arrivals
      current_total next_total best position
      Hinputs Hlatest Hcounts Hcurrent_feasible Hcurrent_schedule
      Hcurrent_total Hminimum Hnext_feasible Hnext_schedule Hnext_total
      Hpath Hcurrent_used Hchoice) as Hnext_lower.
    lia.
Qed.
Lemma booster_progress_zero_best_optimized__termination_and_travel_total :
  forall n m budget remaining initial_dist times origins destinations
         current_dist latest counts arrivals best position,
    0 <= remaining ->
    remaining <= budget ->
    SightseeingInputsBounded
      n m initial_dist times origins destinations ->
    BoosterProgress n m budget remaining
      initial_dist times origins destinations
      current_dist latest counts arrivals ->
    BestBoostChoice
      n current_dist counts latest arrivals best position ->
    best = 0 ->
    OptimizedBusState n m budget
      initial_dist times origins destinations
      current_dist latest counts arrivals.
Proof.
  intros n m budget remaining initial_dist times origins destinations
    current_dist latest counts arrivals best position
    Hremaining Hremaining_budget Hinputs Hprogress Hchoice Hbest.
  unfold BoosterProgress in Hprogress.
  destruct Hprogress as
    [Hlatest [Hcounts [Hfeasible [Hschedule
      [current_total [Hcurrent_total Hminimum]]]]]].
  set (used :=
    sum (fun edge => 0 <= edge < n - 1)
        (fun edge =>
           Znth edge initial_dist 0 - Znth edge current_dist 0)).
  pose proof Hfeasible as Hfeasible_fields.
  rewrite FeasibleBoostedDistances_unfold in Hfeasible_fields.
  destruct Hfeasible_fields as
    [Hcurrent_length [Hcurrent_bounds Hused_base]].
  assert (Hused_nonnegative : 0 <= used).
  {
    unfold used.
    apply sum_nonneg.
    intros edge Hedge.
    specialize (Hcurrent_bounds edge Hedge).
    lia.
  }
  assert (Hused_le_base : used <= budget - remaining).
  { unfold used. exact Hused_base. }
  assert (Hfeasible_used :
    FeasibleBoostedDistances n used initial_dist current_dist).
  {
    rewrite FeasibleBoostedDistances_unfold.
    split; [exact Hcurrent_length |].
    split; [exact Hcurrent_bounds |].
    unfold used.
    lia.
  }
  assert (Hminimum_used :
    SightseeingMinimumTotal
      n m used initial_dist times origins destinations current_total).
  {
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset.
    exists current_total.
    split; [| reflexivity].
    split.
    - unfold SightseeingCandidateTotal.
      exists current_dist, latest, arrivals.
      exact (conj Hlatest
        (conj Hfeasible_used (conj Hschedule Hcurrent_total))).
    - intros candidate_total Hcandidate.
      cbn.
      unfold SightseeingCandidateTotal in Hcandidate.
      destruct Hcandidate as
        [candidate_dist [candidate_latest [candidate_arrivals
          [Hcandidate_latest [Hcandidate_feasible
            [Hcandidate_schedule Hcandidate_total]]]]]].
      pose proof Hcandidate_feasible as Hcandidate_fields.
      rewrite FeasibleBoostedDistances_unfold in Hcandidate_fields.
      destruct Hcandidate_fields as
        [Hcandidate_length [Hcandidate_bounds Hcandidate_used]].
      assert (Hcandidate_feasible_base :
        FeasibleBoostedDistances
          n (budget - remaining) initial_dist candidate_dist).
      {
        rewrite FeasibleBoostedDistances_unfold.
        split; [exact Hcandidate_length |].
        split; [exact Hcandidate_bounds |].
        lia.
      }
      assert (Hcandidate_base :
        SightseeingCandidateTotal
          n m (budget - remaining)
          initial_dist times origins destinations candidate_total).
      {
        exists candidate_dist, candidate_latest, candidate_arrivals.
        exact (conj Hcandidate_latest
          (conj Hcandidate_feasible_base
            (conj Hcandidate_schedule Hcandidate_total))).
      }
      pose proof Hminimum as Hminimum_fields.
      unfold SightseeingMinimumTotal,
        MaxMin.min_value_of_subset,
        MaxMin.min_object_of_subset in Hminimum_fields.
      destruct Hminimum_fields as
        [minimum_witness [[Hminimum_member Hleast] Hvalue]].
      cbn in Hvalue.
      subst minimum_witness.
      specialize (Hleast candidate_total Hcandidate_base).
      cbn in Hleast.
      exact Hleast.
  }
  assert (Hfeasible_full :
    FeasibleBoostedDistances n budget initial_dist current_dist).
  {
    rewrite FeasibleBoostedDistances_unfold.
    split; [exact Hcurrent_length |].
    split; [exact Hcurrent_bounds |].
    unfold used in Hused_le_base.
    lia.
  }
  assert (Hminimum_full :
    SightseeingMinimumTotal
      n m budget initial_dist times origins destinations current_total).
  {
    unfold SightseeingMinimumTotal,
      MaxMin.min_value_of_subset,
      MaxMin.min_object_of_subset.
    exists current_total.
    split; [| reflexivity].
    split.
    - unfold SightseeingCandidateTotal.
      exists current_dist, latest, arrivals.
      exact (conj Hlatest
        (conj Hfeasible_full (conj Hschedule Hcurrent_total))).
    - intros candidate_total Hcandidate.
      cbn.
      unfold SightseeingCandidateTotal in Hcandidate.
      destruct Hcandidate as
        [candidate_dist [candidate_latest [candidate_arrivals
          [Hcandidate_latest [Hcandidate_feasible
            [Hcandidate_schedule Hcandidate_total]]]]]].
      assert (Hlatest_pointwise : forall station, 0 <= station < n ->
        Znth station candidate_latest 0 = Znth station latest 0).
      {
        intros station Hstation.
        symmetry.
        eapply latest_departures_pointwise_unique__chain_dual; eauto.
      }
      assert (Hcandidate_schedule_current :
        BusArrivalSchedule n candidate_dist latest candidate_arrivals).
      {
        eapply bus_schedule_latest_ext__chain_dual.
        - intros station Hstation.
          apply Hlatest_pointwise. exact Hstation.
        - exact Hcandidate_schedule.
      }
      pose proof Hcandidate_feasible as Hcandidate_fields.
      rewrite FeasibleBoostedDistances_unfold in Hcandidate_fields.
      destruct Hcandidate_fields as
        [Hcandidate_length [Hcandidate_bounds Hcandidate_budget]].
      set (candidate_used :=
        sum (fun edge => 0 <= edge < n - 1)
            (fun edge =>
               Znth edge initial_dist 0 - Znth edge candidate_dist 0)).
      assert (Hcandidate_used_nonnegative : 0 <= candidate_used).
      {
        unfold candidate_used.
        apply sum_nonneg.
        intros edge Hedge.
        specialize (Hcandidate_bounds edge Hedge).
        lia.
      }
      assert (Hcandidate_used_budget : candidate_used <= budget).
      { unfold candidate_used. exact Hcandidate_budget. }
      destruct (Z_le_gt_dec candidate_used used) as
        [Hcandidate_old | Hcandidate_new].
      + assert (Hcandidate_feasible_used :
          FeasibleBoostedDistances n used initial_dist candidate_dist).
        {
          rewrite FeasibleBoostedDistances_unfold.
          split; [exact Hcandidate_length |].
          split; [exact Hcandidate_bounds |].
          unfold candidate_used in Hcandidate_old.
          exact Hcandidate_old.
        }
        assert (Hcandidate_used_state :
          SightseeingCandidateTotal
            n m used initial_dist times origins destinations candidate_total).
        {
          exists candidate_dist, candidate_latest, candidate_arrivals.
          exact (conj Hcandidate_latest
            (conj Hcandidate_feasible_used
              (conj Hcandidate_schedule Hcandidate_total))).
        }
        pose proof Hminimum_used as Hminimum_fields.
        unfold SightseeingMinimumTotal,
          MaxMin.min_value_of_subset,
          MaxMin.min_object_of_subset in Hminimum_fields.
        destruct Hminimum_fields as
          [minimum_witness [[Hminimum_member Hleast] Hvalue]].
        cbn in Hvalue.
        subst minimum_witness.
        specialize (Hleast candidate_total Hcandidate_used_state).
        cbn in Hleast.
        exact Hleast.
      + set (gap := Z.to_nat (candidate_used - used)).
        assert (Hgap : candidate_used = used + Z.of_nat gap).
        {
          unfold gap.
          rewrite Z2Nat.id by lia.
          lia.
        }
        assert (Hcandidate_feasible_exact :
          FeasibleBoostedDistances
            n candidate_used initial_dist candidate_dist).
        {
          rewrite FeasibleBoostedDistances_unfold.
          split; [exact Hcandidate_length |].
          split; [exact Hcandidate_bounds |].
          unfold candidate_used.
          lia.
        }
        assert (Hcandidate_feasible_gap :
          FeasibleBoostedDistances
            n (used + Z.of_nat gap) initial_dist candidate_dist).
        { rewrite <- Hgap. exact Hcandidate_feasible_exact. }
        assert (Hcandidate_used_gap :
          sum (fun edge => 0 <= edge < n - 1)
              (fun edge =>
                 Znth edge initial_dist 0 - Znth edge candidate_dist 0) =
            used + Z.of_nat gap).
        { rewrite <- Hgap. unfold candidate_used. reflexivity. }
        eapply (zero_best_candidate_lower_by_gap__termination_and_travel_total
          n m used initial_dist times origins destinations latest counts
          current_dist arrivals current_total best position gap
          Hinputs Hlatest Hcounts Hfeasible_used Hschedule Hcurrent_total
          Hminimum_used Hchoice Hbest ltac:(unfold used; reflexivity)
          candidate_dist candidate_arrivals candidate_total);
          eauto.
  }
  unfold OptimizedBusState.
  exact (conj Hlatest
    (conj Hcounts
      (conj Hfeasible_full
        (conj Hschedule
          (ex_intro _ current_total
            (conj Hcurrent_total
              Hminimum_full)))))).
Qed.
