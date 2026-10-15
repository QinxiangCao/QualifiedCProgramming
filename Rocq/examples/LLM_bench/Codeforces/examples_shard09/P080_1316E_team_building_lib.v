Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition TeamChoice (aud : list Z) (skill : list (list Z)) (k : Z) (score : Z) : Prop :=
  exists players audience : list Z,
   Zlength players = Zlength (Znth 0 skill []) /\ Zlength audience = k /\
   NoDup (players ++ audience) /\ (Forall (fun i => 0 <= i < (Zlength aud)) (players ++ audience)) /\
   score = (fold_right Z.add 0) (map (fun q => Znth (fst q) (Znth (snd q) skill []) 0)
      (combine (Zrange 0 (Zlength players)) players)) +
     (fold_right Z.add 0) (map (fun i => Znth i aud 0) audience).
Definition Pre (k : Z) (aud : list Z) (skill : list (list Z)) : Prop :=
  (* Stated explicitly in the P080 solver Require, so dropped here:
       2 <= Zlength aud <= 100000 /\
       Forall (fun x => 1 <= x <= 1000000000) aud /\
       1 <= k /\
       1 <= p <= 7 /\
       Forall (Forall (fun x => 1 <= x <= 1000000000)) skill *)
  Zlength skill = Zlength aud /\
  exists p,
  p + k <= Zlength aud /\
  Zlength skill = Zlength aud /\
  Forall (fun row => Zlength row = p) skill.

Definition Spec (k : Z) (aud : list Z) (skill : list (list Z)) (out : Z) : Prop :=
  (max_value_of_subset Z.le (TeamChoice aud skill k) (fun x => x)) out.

(* Mathematical interface for the bounded unsigned popcount helper. *)
Definition BitCount (v count : Z) : Prop :=
  count = fold_right Z.add 0
    (map (fun bit => if Z.testbit v bit then 1 else 0) (Zrange 0 32)).

(* The heap sort moves audience values and their original-person indexes as
   inseparable pairs. *)
Definition PeoplePermutation
    (audience order audience' order' : list Z) : Prop :=
  Permutation (combine audience order) (combine audience' order').

Definition PeopleHeapParentsFrom
    (audience : list Z) (lo hi : Z) : Prop :=
  forall child,
    1 <= child <= hi ->
    lo <= (child - 1) / 2 ->
    Znth child audience 0 <= Znth ((child - 1) / 2) audience 0.

Definition PeopleHeapOrderedExceptAt
    (audience : list Z) (lo hi bad : Z) : Prop :=
  forall child,
    1 <= child <= hi ->
    lo <= (child - 1) / 2 ->
    (child - 1) / 2 <> bad ->
    Znth child audience 0 <= Znth ((child - 1) / 2) audience 0.

Definition BitCountProgress
    (original remaining count : Z) : Prop :=
  exists consumed,
    0 <= consumed <= 32 /\
    remaining = Z.shiftr original consumed /\
    count = fold_right Z.add 0
      (map (fun bit => if Z.testbit original bit then 1 else 0)
           (Zrange 0 consumed)).

Definition PeopleSiftProgress
    (audience0 order0 audience order : list Z)
    (root0 root hi n : Z) : Prop :=
  PeoplePermutation audience0 order0 audience order /\
  sublist (hi + 1) n audience = sublist (hi + 1) n audience0 /\
  sublist (hi + 1) n order = sublist (hi + 1) n order0 /\
  PeopleHeapOrderedExceptAt audience root0 hi root /\
  (root = root0 \/
   ((2 * root + 1 <= hi ->
       Znth (2 * root + 1) audience 0 <=
       Znth ((root - 1) / 2) audience 0) /\
    (2 * root + 2 <= hi ->
       Znth (2 * root + 2) audience 0 <=
       Znth ((root - 1) / 2) audience 0))).

Definition PeopleSelectedLargerChild
    (audience : list Z) (root hi child : Z) : Prop :=
  (child = 2 * root + 1 \/ child = 2 * root + 2) /\
  child <= hi /\
  (2 * root + 1 <= hi ->
     Znth (2 * root + 1) audience 0 <= Znth child audience 0) /\
  (2 * root + 2 <= hi ->
     Znth (2 * root + 2) audience 0 <= Znth child audience 0).

Definition PeopleHeapBuildState
    (audience0 order0 audience order : list Z) (root n : Z) : Prop :=
  PeoplePermutation audience0 order0 audience order /\
  PeopleHeapParentsFrom audience (root + 1) (n - 1).

Definition PeopleHeapSortState
    (audience0 order0 audience order : list Z) (hi : Z) : Prop :=
  PeoplePermutation audience0 order0 audience order /\
  PeopleHeapParentsFrom audience 0 hi /\
  ListLib.increasing (sublist (hi + 1) (Zlength audience) audience) /\
  (forall left right,
     0 <= left <= hi ->
     hi < right < Zlength audience ->
     Znth left audience 0 <= Znth right audience 0).

Definition SortedPeopleState
    (audience0 order0 audience order : list Z) : Prop :=
  Zlength audience = Zlength audience0 /\
  Zlength order = Zlength order0 /\
  PeoplePermutation audience0 order0 audience order /\
  ListLib.increasing audience /\
  (forall q,
     0 <= q < Zlength order ->
     0 <= Znth q order 0 < Zlength audience0 /\
     Znth q audience 0 = Znth (Znth q order 0) audience0 0).

Definition TeamNegInf : Z := -(2 ^ 60).

Definition AllTeamNegInf (values : list Z) : Prop :=
  Forall (fun value => value = TeamNegInf) values.

Definition ProcessedPerson
    (sorted_order : list Z) (processed person : Z) : Prop :=
  exists step,
    0 <= step < processed /\
    person = Znth (Zlength sorted_order - 1 - step) sorted_order 0.

Definition AssignmentsMatchMask
    (positions mask : Z) (assignments : list (Z * Z)) : Prop :=
  NoDup (map fst assignments) /\
  (forall role,
     0 <= role < positions ->
     (Z.testbit mask role = true <->
      exists person, In (role, person) assignments)).

Definition TeamPrefixChoice
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed mask score : Z)
    : Prop :=
  0 <= mask < 2 ^ positions /\
  exists assignments audience_people,
    AssignmentsMatchMask positions mask assignments /\
    NoDup (map snd assignments ++ audience_people) /\
    Forall (ProcessedPerson sorted_order processed)
      (map snd assignments ++ audience_people) /\
    Zlength audience_people =
      Z.min audience_limit (processed - Zlength assignments) /\
    score =
      fold_right Z.add 0
        (map
          (fun assignment =>
             Znth (fst assignment)
               (Znth (snd assignment) skill []) 0)
          assignments) +
      fold_right Z.add 0
        (map (fun person => Znth person audience 0) audience_people).

Definition TeamDPCell
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed mask value : Z)
    : Prop :=
  max_value_of_subset Z.le
    (TeamPrefixChoice audience skill sorted_order
      positions audience_limit processed mask)
    (fun score => score) value \/
  (value = TeamNegInf /\
   forall score,
     ~ TeamPrefixChoice audience skill sorted_order
         positions audience_limit processed mask score).

Definition TeamDPTable
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed : Z)
    (values : list Z) : Prop :=
  forall mask,
    0 <= mask < 2 ^ positions ->
    TeamDPCell audience skill sorted_order positions audience_limit
      processed mask (Znth mask values TeamNegInf).

Definition TeamTransitionCandidate
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values : list Z)
    (source_limit target score : Z) : Prop :=
  exists source source_score,
    0 <= source < source_limit /\
    source_score = Znth source old_values TeamNegInf /\
    source_score <> TeamNegInf /\
    ((target = source /\ score = source_score) \/
     (exists used,
        BitCount source used /\
        processed - used < audience_limit /\
        target = source /\
        score = source_score +
          Znth (Zlength sorted_audience - 1 - processed)
            sorted_audience 0) \/
     (exists role,
        0 <= role < positions /\
        Z.testbit source role = false /\
        target = Z.lor source (2 ^ role) /\
        score = source_score +
          Znth role
            (Znth
              (Znth (Zlength sorted_order - 1 - processed)
                sorted_order 0)
              skill []) 0)).

Definition TeamNextRowProgress
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values next_values : list Z)
    (source_limit : Z) : Prop :=
  forall target,
    0 <= target < 2 ^ positions ->
    (max_value_of_subset Z.le
       (TeamTransitionCandidate sorted_audience sorted_order skill
         positions audience_limit processed old_values source_limit target)
       (fun score => score) (Znth target next_values TeamNegInf) \/
     (Znth target next_values TeamNegInf = TeamNegInf /\
      forall score,
        ~ TeamTransitionCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source_limit
            target score)).

Definition TeamCurrentSourceCandidate
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values : list Z)
    (source roles_scanned target score : Z) : Prop :=
  let source_score := Znth source old_values TeamNegInf in
  source_score <> TeamNegInf /\
  ((target = source /\ score = source_score) \/
   (exists used,
      BitCount source used /\
      processed - used < audience_limit /\
      target = source /\
      score = source_score +
        Znth (Zlength sorted_audience - 1 - processed)
          sorted_audience 0) \/
   (exists role,
      0 <= role < roles_scanned /\
      Z.testbit source role = false /\
      target = Z.lor source (2 ^ role) /\
      score = source_score +
        Znth role
          (Znth
            (Znth (Zlength sorted_order - 1 - processed)
              sorted_order 0)
            skill []) 0)).

Definition TeamRoleUpdateProgress
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values next_values : list Z)
    (source roles_scanned : Z) : Prop :=
  forall target,
    0 <= target < 2 ^ positions ->
    (max_value_of_subset Z.le
       (fun score =>
          TeamTransitionCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source target score \/
          TeamCurrentSourceCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source roles_scanned
            target score)
       (fun score => score) (Znth target next_values TeamNegInf) \/
     (Znth target next_values TeamNegInf = TeamNegInf /\
      forall score,
        ~ (TeamTransitionCandidate sorted_audience sorted_order skill
             positions audience_limit processed old_values source target score \/
           TeamCurrentSourceCandidate sorted_audience sorted_order skill
             positions audience_limit processed old_values source roles_scanned
             target score))).

Definition TeamCopyPrefix
    (source destination : list Z) (copied : Z) : Prop :=
  forall mask,
    0 <= mask < copied ->
    Znth mask destination TeamNegInf = Znth mask source TeamNegInf.

(* Revision-2 bounded DP semantics.  The revision is additive because the
   earlier declarations are part of the frozen formal surface. *)
Definition BoundedAssignmentsMatchMask
    (positions mask : Z) (assignments : list (Z * Z)) : Prop :=
  AssignmentsMatchMask positions mask assignments /\
  Forall (fun assignment => 0 <= fst assignment < positions) assignments.

Definition BoundedTeamPrefixChoice
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed mask score : Z)
    : Prop :=
  0 <= mask < 2 ^ positions /\
  exists assignments audience_people,
    BoundedAssignmentsMatchMask positions mask assignments /\
    NoDup (map snd assignments ++ audience_people) /\
    Forall (ProcessedPerson sorted_order processed)
      (map snd assignments ++ audience_people) /\
    Zlength audience_people =
      Z.min audience_limit (processed - Zlength assignments) /\
    score =
      fold_right Z.add 0
        (map
          (fun assignment =>
             Znth (fst assignment)
               (Znth (snd assignment) skill []) 0)
          assignments) +
      fold_right Z.add 0
        (map (fun person => Znth person audience 0) audience_people).

Definition BoundedTeamDPCell
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed mask value : Z)
    : Prop :=
  max_value_of_subset Z.le
    (BoundedTeamPrefixChoice audience skill sorted_order
      positions audience_limit processed mask)
    (fun score => score) value \/
  (value = TeamNegInf /\
   forall score,
     ~ BoundedTeamPrefixChoice audience skill sorted_order
         positions audience_limit processed mask score).

Definition BoundedTeamDPTable
    (audience : list Z) (skill : list (list Z))
    (sorted_order : list Z) (positions audience_limit processed : Z)
    (values : list Z) : Prop :=
  forall mask,
    0 <= mask < 2 ^ positions ->
    BoundedTeamDPCell audience skill sorted_order positions audience_limit
      processed mask (Znth mask values TeamNegInf).

Definition BoundedTeamNextRowProgress
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values next_values : list Z)
    (source_limit : Z) : Prop :=
  forall target,
    0 <= target < 2 ^ positions ->
    (max_value_of_subset Z.le
       (TeamTransitionCandidate sorted_audience sorted_order skill
         positions audience_limit processed old_values source_limit target)
       (fun score => score) (Znth target next_values TeamNegInf) \/
     (Znth target next_values TeamNegInf = TeamNegInf /\
      forall score,
        ~ TeamTransitionCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source_limit
            target score)).

Definition BoundedTeamRoleUpdateProgress
    (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values next_values : list Z)
    (source roles_scanned : Z) : Prop :=
  forall target,
    0 <= target < 2 ^ positions ->
    (max_value_of_subset Z.le
       (fun score =>
          TeamTransitionCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source target score \/
          TeamCurrentSourceCandidate sorted_audience sorted_order skill
            positions audience_limit processed old_values source roles_scanned
            target score)
       (fun score => score) (Znth target next_values TeamNegInf) \/
     (Znth target next_values TeamNegInf = TeamNegInf /\
      forall score,
        ~ (TeamTransitionCandidate sorted_audience sorted_order skill
             positions audience_limit processed old_values source target score \/
           TeamCurrentSourceCandidate sorted_audience sorted_order skill
             positions audience_limit processed old_values source roles_scanned
             target score))).

Definition BoundedTeamCopyPrefix
    (source destination : list Z) (copied : Z) : Prop :=
  forall mask,
    0 <= mask < copied ->
    Znth mask destination TeamNegInf = Znth mask source TeamNegInf.
Require Import Coq.micromega.Lia.

Lemma map_snd_combine__solver_row_close :
  forall (xs ys : list Z),
    Zlength xs = Zlength ys ->
    map snd (combine xs ys) = ys.
Proof.
  induction xs as [|x xs IH]; intros ys Hlen.
  - destruct ys as [|y ys].
    + reflexivity.
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.

Lemma processed_audience_dominates_new__solver_row_close :
  forall audience order_values sorted_audience sorted_order processed old_person,
    SortedPeopleState audience order_values sorted_audience sorted_order ->
    Zlength sorted_audience = Zlength sorted_order ->
    0 <= processed < Zlength sorted_order ->
    ProcessedPerson sorted_order processed old_person ->
    Znth (Znth (Zlength sorted_order - 1 - processed) sorted_order 0)
      audience 0 <= Znth old_person audience 0.
Proof.
  intros audience order_values sorted_audience sorted_order processed old_person
    Hsorted Hsame_length Hprocessed [step [[Hstep0 Hstep] Hold_person]].
  destruct Hsorted as [Hlen_audience [Hlen_order [Hperm [Hinc Hmap]]]].
  assert (Hnew_rank : 0 <= Zlength sorted_order - 1 - processed <
      Zlength sorted_order) by lia.
  assert (Hold_rank : 0 <= Zlength sorted_order - 1 - step <
      Zlength sorted_order) by lia.
  pose proof (Hmap (Zlength sorted_order - 1 - processed) Hnew_rank)
    as [_ Hmap_new].
  pose proof (Hmap (Zlength sorted_order - 1 - step) Hold_rank)
    as [_ Hmap_old].
  pose proof (proj2 (mono_nondec_iff_increasing sorted_audience) Hinc)
    as Hmono.
  unfold mono_nondec in Hmono.
  pose proof (Hmono (Zlength sorted_order - 1 - processed)
    (Zlength sorted_order - 1 - step) ltac:(lia) ltac:(lia)
    ltac:(rewrite Hsame_length; lia)) as Hle.
  rewrite Hmap_new, Hmap_old, <- Hold_person in Hle. exact Hle.
Qed.

Lemma bounded_dp_choice_upper__solver_row_close :
  forall audience skill order positions audience_limit processed values mask score,
    0 <= mask < 2 ^ positions ->
    BoundedTeamDPTable audience skill order positions audience_limit processed values ->
    BoundedTeamPrefixChoice audience skill order positions audience_limit processed
      mask score ->
    score <= Znth mask values TeamNegInf.
Proof.
  intros audience skill order positions audience_limit processed values mask score
    Hmask Htable Hchoice.
  specialize (Htable mask Hmask).
  unfold BoundedTeamDPCell in Htable.
  destruct Htable as [Hmax | [Heq Hempty]].
  - unfold max_value_of_subset, max_object_of_subset in Hmax.
    destruct Hmax as [best [[Hbest Hupper] Hvalue]].
    rewrite <- Hvalue. apply Hupper. exact Hchoice.
  - exfalso. apply (Hempty score). exact Hchoice.
Qed.

Lemma fold_right_add_app__solver_row_close :
  forall left right,
    fold_right Z.add 0 (left ++ right) =
    fold_right Z.add 0 left + fold_right Z.add 0 right.
Proof.
  intros left right. induction left as [|x xs IH]; simpl; lia.
Qed.

Lemma fold_bit_count_filter__solver_row_close :
  forall (f : Z -> bool) values,
    fold_right Z.add 0
      (map (fun bit => if f bit then 1 else 0) values) =
    Zlength (filter f values).
Proof.
  intros f values. induction values as [|x xs IH].
  - reflexivity.
  - cbn [map fold_right]. destruct (f x) eqn:Hfx.
    + cbn [filter]. rewrite Hfx, Zlength_cons, IH.
      unfold Z.succ. apply Z.add_comm.
    + cbn [filter]. rewrite Hfx. exact IH.
Qed.

Lemma bounded_mask_high_bit_false__solver_row_close :
  forall mask positions bit,
    0 <= mask < 2 ^ positions ->
    0 <= positions -> positions <= bit ->
    Z.testbit mask bit = false.
Proof.
  intros mask positions bit Hmask Hpositions Hbit.
  destruct (Z.eq_dec mask 0) as [-> | Hnonzero].
  - apply Z.bits_0.
  - apply Z.bits_above_log2; [lia |].
    assert (Z.log2 mask < positions).
    { apply (proj1 (Z.log2_lt_pow2 mask positions ltac:(lia))); lia. }
    lia.
Qed.

Lemma bitcount_assignments_length__solver_row_close :
  forall positions mask assignments used,
    0 <= positions <= 7 ->
    0 <= mask < 2 ^ positions ->
    BoundedAssignmentsMatchMask positions mask assignments ->
    BitCount mask used ->
    used = Zlength assignments.
Proof.
  intros positions mask assignments used Hpositions Hmask Hbounded Hcount.
  destruct Hbounded as [[Hroles Hmatch] Hrole_bounds].
  unfold BitCount in Hcount.
  rewrite fold_bit_count_filter__solver_row_close in Hcount.
  assert (Hperm : Permutation (map fst assignments)
      (filter (fun bit => Z.testbit mask bit) (Zrange 0 32))).
  {
    apply NoDup_Permutation.
    - exact Hroles.
    - apply NoDup_filter. apply NoDup_Zrange.
    - intros role. rewrite filter_In, <- In_Zrange.
      split.
      + intros Hin.
        assert (Hpair : exists person, In (role, person) assignments).
        { apply in_map_iff in Hin as [[role' person] [Heq Hin]].
          simpl in Heq. subst role'. exists person. exact Hin. }
        assert (Hrole : 0 <= role < positions).
        { rewrite Forall_forall in Hrole_bounds.
          destruct Hpair as [person Hin_pair].
          specialize (Hrole_bounds (role, person) Hin_pair). exact Hrole_bounds. }
        split; [lia |].
        apply (proj2 (Hmatch role Hrole)). exact Hpair.
      + intros [[Hrole0 Hrole32] Hbit].
        assert (Hrole : role < positions).
        { destruct (Z_lt_ge_dec role positions); [assumption |].
          rewrite (bounded_mask_high_bit_false__solver_row_close mask positions role)
            in Hbit by lia. discriminate. }
        destruct (proj1 (Hmatch role ltac:(lia)) Hbit) as [person Hin].
        apply in_map_iff. exists (role, person). split; [reflexivity | exact Hin].
  }
  apply Permutation_length in Hperm.
  rewrite length_map in Hperm.
  rewrite Hcount, !Zlength_correct. f_equal. symmetry. exact Hperm.
Qed.

Lemma identity_order_nodup__solver_row_close :
  forall order n,
    Zlength order = n ->
    (forall q, 0 <= q < n -> Znth q order 0 = q) ->
    NoDup order.
Proof.
  intros order n Hlen Hidentity.
  apply (proj2 (NoDup_nth order 0)).
  intros x y Hx Hy Heq.
  assert (HxZ : 0 <= Z.of_nat x < n).
  { rewrite <- Hlen, Zlength_correct. lia. }
  assert (HyZ : 0 <= Z.of_nat y < n).
  { rewrite <- Hlen, Zlength_correct. lia. }
  pose proof (Hidentity (Z.of_nat x) HxZ) as Hidentity_x.
  pose proof (Hidentity (Z.of_nat y) HyZ) as Hidentity_y.
  unfold Znth in Hidentity_x, Hidentity_y.
  rewrite !Nat2Z.id in Hidentity_x, Hidentity_y.
  lia.
Qed.

Lemma sorted_order_nodup__solver_row_close :
  forall aud order_values sorted_audience sorted_order n,
    Zlength aud = n ->
    Zlength order_values = n ->
    Zlength sorted_audience = n ->
    Zlength sorted_order = n ->
    (forall q, 0 <= q < n -> Znth q order_values 0 = q) ->
    PeoplePermutation aud order_values sorted_audience sorted_order ->
    NoDup sorted_order.
Proof.
  intros aud order_values sorted_audience sorted_order n Haud Horder Hsorted_aud
    Hsorted_order Hidentity Hperm.
  assert (Horder_nodup : NoDup order_values).
  { eapply identity_order_nodup__solver_row_close; eauto. }
  unfold PeoplePermutation in Hperm.
  pose proof (Permutation_map snd Hperm) as Horders.
  rewrite (map_snd_combine__solver_row_close aud order_values) in Horders by lia.
  rewrite (map_snd_combine__solver_row_close sorted_audience sorted_order)
    in Horders by lia.
  eapply Permutation_NoDup; eauto.
Qed.

Lemma nodup_Znth_injective__solver_row_close :
  forall (values : list Z) i j,
    NoDup values ->
    0 <= i < Zlength values ->
    0 <= j < Zlength values ->
    Znth i values 0 = Znth j values 0 ->
    i = j.
Proof.
  intros values i j Hnodup Hi Hj Heq.
  apply Z2Nat.inj; try lia.
  apply (proj1 (NoDup_nth values 0) Hnodup).
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
  - unfold Znth in Heq. exact Heq.
Qed.

Lemma processed_person_lift__solver_row_close :
  forall order processed person,
    ProcessedPerson order processed person ->
    ProcessedPerson order (processed + 1) person.
Proof.
  intros order processed person [step [Hstep Hperson]].
  exists step. split; [lia | exact Hperson].
Qed.

Lemma processed_person_not_new__solver_row_close :
  forall order processed person,
    NoDup order ->
    0 <= processed < Zlength order ->
    ProcessedPerson order processed person ->
    person <> Znth (Zlength order - 1 - processed) order 0.
Proof.
  intros order processed person Hnodup Hprocessed
    [step [[Hstep0 Hstep] Hperson]] Heq.
  rewrite Hperson in Heq.
  eapply nodup_Znth_injective__solver_row_close in Heq; try eassumption; lia.
Qed.

Lemma bounded_dp_finite_choice__solver_row_close :
  forall aud skill order positions audience_limit processed values mask,
    0 <= mask < 2 ^ positions ->
    BoundedTeamDPTable aud skill order positions audience_limit processed values ->
    Znth mask values TeamNegInf <> TeamNegInf ->
    BoundedTeamPrefixChoice aud skill order positions audience_limit processed
      mask (Znth mask values TeamNegInf).
Proof.
  intros aud skill order positions audience_limit processed values mask Hmask
    Htable Hfinite.
  specialize (Htable mask Hmask).
  unfold BoundedTeamDPCell in Htable.
  destruct Htable as [Hmax | [Heq _]]; [|contradiction].
  unfold max_value_of_subset, max_object_of_subset in Hmax.
  destruct Hmax as [score [[Hchoice _] Hscore]].
  rewrite <- Hscore. exact Hchoice.
Qed.

Lemma max_value_cofinal__solver_row_close :
  forall (P Q : Z -> Prop) value,
    (forall p, P p -> exists q, Q q /\ p <= q) ->
    (forall q, Q q -> exists p, P p /\ q <= p) ->
    max_value_of_subset Z.le P (fun x => x) value ->
    max_value_of_subset Z.le Q (fun x => x) value.
Proof.
  intros P Q value HPQ HQP Hmax.
  unfold max_value_of_subset, max_object_of_subset in *.
  destruct Hmax as [best [[Hbest Hupper] Hvalue]].
  destruct (HPQ best Hbest) as [q [Hq Hbest_q]].
  destruct (HQP q Hq) as [p [Hp Hq_p]].
  pose proof (Hupper p Hp) as Hp_best.
  assert (best = q) by lia.
  subst q. exists best. split; [split | exact Hvalue].
  - exact Hq.
  - intros q' Hq'. destruct (HQP q' Hq') as [p' [Hp' Hqprime_pprime]].
    specialize (Hupper p' Hp'). lia.
Qed.

Lemma Zlength_Zrange_zero__solver_row_close :
  forall high, 0 <= high -> Zlength (Zrange 0 high) = high.
Proof.
  intros high Hhigh. unfold Zrange.
  rewrite Zlength_correct.
  assert (Haux : forall count low, length (Zrange_aux low count) = count).
  { induction count as [|count IH]; intros low; simpl; [reflexivity |].
    rewrite IH. reflexivity. }
  rewrite Haux, Z2Nat.id by lia. lia.
Qed.

Lemma processed_person_in_people__solver_row_close :
  forall order processed person,
    0 <= processed ->
    (ProcessedPerson order processed person <->
     In person
       (map (fun step => Znth (Zlength order - 1 - step) order 0)
         (Zrange 0 processed))).
Proof.
  intros order processed person Hprocessed.
  unfold ProcessedPerson.
  rewrite in_map_iff. split.
  - intros [step [Hstep Hperson]]. exists step. split.
    + symmetry. exact Hperson.
    + apply In_Zrange. lia.
  - intros [step [Hperson Hstep]]. exists step. split.
    + apply In_Zrange in Hstep. lia.
    + symmetry. exact Hperson.
Qed.

Lemma processed_people_nodup__solver_row_close :
  forall order processed,
    NoDup order ->
    0 <= processed <= Zlength order ->
    NoDup
      (map (fun step => Znth (Zlength order - 1 - step) order 0)
        (Zrange 0 processed)).
Proof.
  intros order processed Horder Hprocessed.
  apply Injective_map_NoDup_in.
  - intros left right Hleft Hright Heq.
    apply In_Zrange in Hleft. apply In_Zrange in Hright.
    eapply nodup_Znth_injective__solver_row_close in Heq; try eassumption; lia.
  - apply NoDup_Zrange.
Qed.

Lemma processed_selection_card__solver_row_close :
  forall order processed selected,
    0 <= processed ->
    NoDup selected ->
    Forall (ProcessedPerson order processed) selected ->
    Zlength selected <= processed.
Proof.
  intros order processed selected Hprocessed Hnodup Hall.
  assert (Hincl : incl selected
      (map (fun step => Znth (Zlength order - 1 - step) order 0)
        (Zrange 0 processed))).
  { intros person Hin. rewrite Forall_forall in Hall.
    apply processed_person_in_people__solver_row_close; [lia |].
    apply Hall. exact Hin. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite length_map in Hlen.
  rewrite <- !Zlength_correct in Hlen.
  rewrite Zlength_Zrange_zero__solver_row_close in Hlen by lia.
  exact Hlen.
Qed.

Lemma processed_missing_person__solver_row_close :
  forall order processed selected,
    NoDup order ->
    0 <= processed <= Zlength order ->
    NoDup selected ->
    Zlength selected < processed ->
    exists person,
      ProcessedPerson order processed person /\ ~ In person selected.
Proof.
  intros order processed selected Horder Hprocessed Hselected Hlen.
  set (people :=
    map (fun step => Znth (Zlength order - 1 - step) order 0)
      (Zrange 0 processed)).
  assert (Hpeople_nodup : NoDup people).
  { subst people. apply processed_people_nodup__solver_row_close; assumption. }
  assert (Hpeople_len : Zlength people = processed).
  { subst people.
    rewrite Zlength_correct, length_map, <- Zlength_correct.
    rewrite Zlength_Zrange_zero__solver_row_close by lia. reflexivity. }
  destruct (classic (exists person, In person people /\ ~ In person selected))
    as [[person [Hin Hnot]] | Hnone].
  - exists person. split; [|exact Hnot].
    apply processed_person_in_people__solver_row_close; [lia | exact Hin].
  - exfalso.
    assert (Hincl : incl people selected).
    { intros person Hin. apply NNPP. intro Hnot.
      apply Hnone. exists person. tauto. }
    pose proof (NoDup_incl_length Hpeople_nodup Hincl) as Hnat.
    apply Nat2Z.inj_le in Hnat.
    rewrite <- !Zlength_correct in Hnat. lia.
Qed.

Lemma processed_person_succ_cases__solver_row_close :
  forall order processed person,
    0 <= processed ->
    ProcessedPerson order (processed + 1) person ->
    person = Znth (Zlength order - 1 - processed) order 0 \/
    ProcessedPerson order processed person.
Proof.
  intros order processed person Hprocessed [step [[Hstep0 Hstep] Hperson]].
  destruct (Z.eq_dec step processed) as [-> | Hneq].
  - left. exact Hperson.
  - right. exists step. split; [lia | exact Hperson].
Qed.

Lemma testbit_pow2__solver_row_close :
  forall role bit,
    0 <= role -> 0 <= bit ->
    Z.testbit (2 ^ role) bit = Z.eqb bit role.
Proof.
  intros role bit Hrole Hbit.
  rewrite <- Z.shiftl_1_l.
  destruct (Z.lt_trichotomy bit role) as [Hlt | [-> | Hgt]].
  - rewrite Z.shiftl_spec_low by lia. symmetry. apply Z.eqb_neq. lia.
  - rewrite Z.shiftl_spec by lia. replace (role - role) with 0 by lia.
    simpl. symmetry. apply Z.eqb_refl.
  - rewrite Z.shiftl_spec by lia.
    replace (bit =? role) with false by (symmetry; apply Z.eqb_neq; lia).
    apply Z.bits_above_log2; [lia |]. cbn. lia.
Qed.

Lemma small_mask_remove_bit__solver_row_close :
  forall positions target role,
    0 <= positions <= 7 ->
    0 <= target < 2 ^ positions ->
    0 <= role < positions ->
    Z.testbit target role = true ->
    let source := Z.ldiff target (2 ^ role) in
    0 <= source < 2 ^ positions /\
    Z.testbit source role = false /\
    Z.lor source (2 ^ role) = target /\
    forall other,
      0 <= other < positions -> other <> role ->
      Z.testbit source other = Z.testbit target other.
Proof.
  intros positions target role Hpositions Htarget Hrole Hbit.
  cbn.
  assert (Hsource0 : 0 <= Z.ldiff target (2 ^ role)).
  { assert (Hpow : 0 < 2 ^ role) by (apply Z.pow_pos_nonneg; lia).
    destruct target as [|target_pos|target_neg]; [reflexivity | | lia].
    destruct (2 ^ role) as [|bit_pos|bit_neg] eqn:Hbit_value; try lia.
    cbn [Z.ldiff]. destruct (Pos.ldiff target_pos bit_pos); simpl; lia. }
  assert (Hsource_le : Z.ldiff target (2 ^ role) <= target).
  { assert (Hpow : 0 < 2 ^ role) by (apply Z.pow_pos_nonneg; lia).
    destruct target as [|target_pos|target_neg]; [reflexivity | | lia].
    destruct (2 ^ role) as [|bit_pos|bit_neg] eqn:Hbit_value; try lia.
    pose proof (N.ldiff_le_l (N.pos target_pos) (N.pos bit_pos)) as Hle.
    apply N2Z.inj_le in Hle. exact Hle. }
  repeat split; try lia.
  - rewrite Z.ldiff_spec, testbit_pow2__solver_row_close by lia.
    rewrite Z.eqb_refl. simpl. destruct (Z.testbit target role); reflexivity.
  - apply Z.bits_inj'. intros bit Hbit0.
    rewrite Z.lor_spec, Z.ldiff_spec, !testbit_pow2__solver_row_close by lia.
    destruct (Z.eq_dec bit role) as [-> | Hneq].
    + rewrite Z.eqb_refl, Hbit. reflexivity.
    + replace (bit =? role) with false
        by (symmetry; apply Z.eqb_neq; exact Hneq).
      destruct (Z.testbit target bit); reflexivity.
  - intros other Hother Hneq.
    rewrite Z.ldiff_spec, testbit_pow2__solver_row_close by lia.
    replace (other =? role) with false
      by (symmetry; apply Z.eqb_neq; exact Hneq).
    destruct (Z.testbit target other); reflexivity.
Qed.

Lemma mask_set_bit_bounds__solver_row_close :
  forall mask role positions,
    0 <= mask < Z.shiftl 1 positions ->
    0 <= role < positions ->
    0 <= Z.lor mask (Z.shiftl 1 role) < Z.shiftl 1 positions.
Proof.
  intros mask role positions Hmask Hrole.
  rewrite !Z.shiftl_1_l in *.
  assert (Hbit : 0 <= 2 ^ role < 2 ^ positions).
  { split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
  split; [apply Z.lor_nonneg; lia |].
  assert (Hmask_bits : Z.land mask (2 ^ positions - 1) = mask).
  { change (Z.land mask (Z.pred (2 ^ positions)) = mask).
    rewrite <- Z.ones_equiv, Z.land_ones by lia.
    rewrite Z.mod_small; lia. }
  assert (Hbit_bits : Z.land (2 ^ role) (2 ^ positions - 1) = 2 ^ role).
  { change (Z.land (2 ^ role) (Z.pred (2 ^ positions)) = 2 ^ role).
    rewrite <- Z.ones_equiv, Z.land_ones by lia.
    rewrite Z.mod_small; lia. }
  assert (Hall_bits :
      Z.land (Z.lor mask (2 ^ role)) (2 ^ positions - 1) =
      Z.lor mask (2 ^ role)).
  { rewrite Z.land_lor_distr_l, Hmask_bits, Hbit_bits. reflexivity. }
  change (Z.land (Z.lor mask (2 ^ role)) (Z.pred (2 ^ positions)) =
      Z.lor mask (2 ^ role)) in Hall_bits.
  rewrite <- Z.ones_equiv in Hall_bits.
  rewrite Z.land_ones in Hall_bits by lia.
  pose proof (Z.mod_pos_bound (Z.lor mask (2 ^ role))
    (2 ^ positions) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
Qed.

Lemma small_mask_add_bit__solver_row_close :
  forall positions source role,
    0 <= positions <= 7 ->
    0 <= source < 2 ^ positions ->
    0 <= role < positions ->
    Z.testbit source role = false ->
    let target := Z.lor source (2 ^ role) in
    0 <= target < 2 ^ positions /\
    Z.testbit target role = true /\
    forall other,
      0 <= other < positions -> other <> role ->
      Z.testbit target other = Z.testbit source other.
Proof.
  intros positions source role Hpositions Hsource Hrole Hbit.
  cbn.
  assert (Htarget : 0 <= Z.lor source (2 ^ role) < 2 ^ positions).
  { pose proof (mask_set_bit_bounds__solver_row_close source role positions
      ltac:(rewrite Z.shiftl_1_l; exact Hsource) Hrole) as Hset.
    rewrite !Z.shiftl_1_l in Hset. exact Hset. }
  split; [exact Htarget |]. split.
  - rewrite Z.lor_spec, testbit_pow2__solver_row_close by lia.
    rewrite Z.eqb_refl, Hbit. reflexivity.
  - intros other Hother Hneq.
    rewrite Z.lor_spec, testbit_pow2__solver_row_close by lia.
    replace (other =? role) with false
      by (symmetry; apply Z.eqb_neq; exact Hneq).
    destruct (Z.testbit source other); reflexivity.
Qed.

Lemma bounded_match_cons__solver_row_close :
  forall positions source assignments role person,
    0 <= positions <= 7 ->
    0 <= source < 2 ^ positions ->
    BoundedAssignmentsMatchMask positions source assignments ->
    0 <= role < positions ->
    Z.testbit source role = false ->
    BoundedAssignmentsMatchMask positions (Z.lor source (2 ^ role))
      ((role, person) :: assignments).
Proof.
  intros positions source assignments role person Hpositions Hsource
    [[Hnodup Hmatch] Hbounds] Hrole Hbit.
  pose proof (small_mask_add_bit__solver_row_close positions source role
    Hpositions Hsource Hrole Hbit) as [Htarget [Htarget_role Htarget_other]].
  split; [split |].
  - simpl. constructor.
    + intro Hin. apply in_map_iff in Hin as [[other other_person] [Heq Hin]].
      simpl in Heq. subst other.
      assert (Z.testbit source role = true).
      { apply (proj2 (Hmatch role Hrole)). exists other_person. exact Hin. }
      congruence.
    + exact Hnodup.
  - intros other Hother. destruct (Z.eq_dec other role) as [-> | Hneq].
    + rewrite Htarget_role. split.
      * intros _. exists person. left. reflexivity.
      * intros _. reflexivity.
    + rewrite Htarget_other by assumption.
      rewrite Hmatch by assumption.
      split.
      * intros [other_person Hin]. exists other_person. right. exact Hin.
      * intros [other_person [Heq | Hin]].
        -- inversion Heq; subst. exfalso. apply Hneq. reflexivity.
        -- exists other_person. exact Hin.
  - constructor; [exact Hrole | exact Hbounds].
Qed.

Lemma bounded_match_remove__solver_row_close :
  forall positions target before after role person,
    0 <= positions <= 7 ->
    0 <= target < 2 ^ positions ->
    BoundedAssignmentsMatchMask positions target
      (before ++ (role, person) :: after) ->
    exists source,
      0 <= source < 2 ^ positions /\
      Z.testbit source role = false /\
      Z.lor source (2 ^ role) = target /\
      BoundedAssignmentsMatchMask positions source (before ++ after).
Proof.
  intros positions target before after role person Hpositions Htarget
    [[Hnodup Hmatch] Hbounds].
  assert (Hrole : 0 <= role < positions).
  { rewrite Forall_forall in Hbounds. apply (Hbounds (role, person)).
    apply in_or_app. right. left. reflexivity. }
  assert (Htarget_bit : Z.testbit target role = true).
  { apply (proj2 (Hmatch role Hrole)). exists person.
    apply in_or_app. right. left. reflexivity. }
  pose proof (small_mask_remove_bit__solver_row_close positions target role
    Hpositions Htarget Hrole Htarget_bit) as
    [Hsource [Hsource_bit [Hsource_target Hsource_other]]].
  exists (Z.ldiff target (2 ^ role)).
  split; [exact Hsource |]. split; [exact Hsource_bit |].
  split; [exact Hsource_target |]. split; [split |].
  - rewrite !map_app in Hnodup |- *. simpl in Hnodup.
    eapply NoDup_remove_1. exact Hnodup.
  - intros other Hother. destruct (Z.eq_dec other role) as [-> | Hneq].
    + rewrite Hsource_bit. split; [discriminate |].
      intros [other_person Hin].
      assert (Hin_role_remaining : In role (map fst (before ++ after))).
      { apply in_map_iff. exists (role, other_person). split; [reflexivity | exact Hin]. }
      rewrite !map_app in Hnodup. simpl in Hnodup.
      apply NoDup_remove_2 in Hnodup. exfalso. apply Hnodup.
      rewrite map_app in Hin_role_remaining. exact Hin_role_remaining.
    + rewrite Hsource_other by assumption.
      rewrite Hmatch by assumption.
      split.
      * intros [other_person Hin]. exists other_person.
        apply in_app_or in Hin as [Hin | [Heq | Hin]].
        -- apply in_or_app. left. exact Hin.
        -- inversion Heq; subst. exfalso. apply Hneq. reflexivity.
        -- apply in_or_app. right. exact Hin.
      * intros [other_person Hin]. exists other_person.
        apply in_app_or in Hin as [Hin | Hin]; apply in_or_app.
        -- left. exact Hin.
        -- right. apply in_cons. exact Hin.
  - rewrite Forall_forall in Hbounds |- *.
    intros assignment Hin. apply Hbounds.
    apply in_app_or in Hin as [Hin | Hin]; apply in_or_app.
    + left. exact Hin.
    + right. apply in_cons. exact Hin.
Qed.

Lemma transition_to_bounded_choice__solver_row_close :
  forall audience sorted_audience skill order positions audience_limit processed
    old_values target score,
    0 <= positions <= 7 ->
    1 <= audience_limit ->
    0 <= processed < Zlength order ->
    NoDup order ->
    Znth (Zlength sorted_audience - 1 - processed) sorted_audience 0 =
      Znth (Znth (Zlength order - 1 - processed) order 0) audience 0 ->
    1 <= Znth (Zlength sorted_audience - 1 - processed) sorted_audience 0 ->
    BoundedTeamDPTable audience skill order positions audience_limit processed
      old_values ->
    TeamTransitionCandidate sorted_audience order skill positions audience_limit
      processed old_values (2 ^ positions) target score ->
    exists choice_score,
      BoundedTeamPrefixChoice audience skill order positions audience_limit
        (processed + 1) target choice_score /\
      score <= choice_score.
Proof.
  intros audience sorted_audience skill order positions audience_limit processed
    old_values target score Hpositions Haudience_limit Hprocessed Horder
    Hnew_audience Hnew_positive Htable Hcandidate.
  unfold TeamTransitionCandidate in Hcandidate.
  destruct Hcandidate as [source [source_score [Hsource [Hsource_value
    [Hsource_live Hcase]]]]].
  assert (Hold_choice : BoundedTeamPrefixChoice audience skill order positions
      audience_limit processed source source_score).
  { rewrite Hsource_value in Hsource_live |- *.
    eapply bounded_dp_finite_choice__solver_row_close.
    - exact Hsource.
    - exact Htable.
    - exact Hsource_live. }
  unfold BoundedTeamPrefixChoice in Hold_choice.
  destruct Hold_choice as [Hsource_mask [assignments [audience_people
    [Hmatch [Hselected [Hprocessed_all [Haudience_len Hscore_old]]]]]]].
  set (new_person := Znth (Zlength order - 1 - processed) order 0).
  assert (Hnew_notin : ~ In new_person (map snd assignments ++ audience_people)).
  { intro Hin. rewrite Forall_forall in Hprocessed_all.
    pose proof (Hprocessed_all new_person Hin) as Hold_new.
    pose proof (processed_person_not_new__solver_row_close order processed
      new_person Horder Hprocessed Hold_new) as Hneq.
    unfold new_person in Hneq. contradiction. }
  assert (Hlift : Forall (ProcessedPerson order (processed + 1))
      (map snd assignments ++ audience_people)).
  { eapply Forall_impl; [|exact Hprocessed_all].
    intros person Hperson. apply processed_person_lift__solver_row_close.
    exact Hperson. }
  destruct Hcase as [[Htarget Hscore] | [Haudience_case | Hrole_case]].
  - subst target score.
    destruct (Z_lt_ge_dec (processed - Zlength assignments) audience_limit)
      as [Hunsaturated | Hsaturated].
    + exists (source_score +
        Znth (Zlength sorted_audience - 1 - processed) sorted_audience 0).
      split; [|lia]. split; [exact Hsource_mask |].
      exists assignments, (new_person :: audience_people).
      split; [exact Hmatch |]. split.
      * assert (Hperm : Permutation
          (new_person :: (map snd assignments ++ audience_people))
          (map snd assignments ++ new_person :: audience_people)).
        { apply Permutation_middle. }
        eapply Permutation_NoDup; [exact Hperm |].
        constructor; assumption.
      * split.
        -- assert (Hperm : Permutation
          (new_person :: (map snd assignments ++ audience_people))
          (map snd assignments ++ new_person :: audience_people)).
           { apply Permutation_middle. }
           eapply Permutation_Forall; [exact Hperm |].
           constructor; [|exact Hlift].
           exists processed. split; [lia | reflexivity].
        -- split.
           ++ rewrite Zlength_cons, Haudience_len.
              rewrite Z.min_r by lia. rewrite Z.min_r by lia. lia.
           ++ simpl. unfold new_person.
              rewrite Hscore_old, Hnew_audience. simpl. lia.
    + exists source_score. split; [|lia]. split; [exact Hsource_mask |].
      exists assignments, audience_people.
      split; [exact Hmatch |]. split; [exact Hselected |].
      split; [exact Hlift |]. split.
      * rewrite Haudience_len. rewrite Z.min_l by lia.
        rewrite Z.min_l by lia. reflexivity.
      * exact Hscore_old.
  - destruct Haudience_case as [used [Hcount [Heligible [Htarget Hscore]]]].
    subst target score.
    assert (Hused : used = Zlength assignments).
    { eapply bitcount_assignments_length__solver_row_close; eauto. }
    exists (source_score +
      Znth (Zlength sorted_audience - 1 - processed) sorted_audience 0).
    split; [|lia]. split; [exact Hsource_mask |].
    exists assignments, (new_person :: audience_people).
    split; [exact Hmatch |]. split.
    + assert (Hperm : Permutation
        (new_person :: (map snd assignments ++ audience_people))
        (map snd assignments ++ new_person :: audience_people)).
      { apply Permutation_middle. }
      eapply Permutation_NoDup; [exact Hperm |]. constructor; assumption.
    + split.
      * assert (Hperm : Permutation
        (new_person :: (map snd assignments ++ audience_people))
        (map snd assignments ++ new_person :: audience_people)).
        { apply Permutation_middle. }
        eapply Permutation_Forall; [exact Hperm |].
        constructor; [|exact Hlift].
        exists processed. split; [lia | reflexivity].
      * split.
        -- rewrite Zlength_cons, Haudience_len.
           rewrite Z.min_r by lia. rewrite Z.min_r by lia. lia.
        -- simpl. unfold new_person.
           rewrite Hscore_old, Hnew_audience. simpl. lia.
  - destruct Hrole_case as [role [Hrole [Hbit [Htarget Hscore]]]].
    subst target score.
    exists (source_score +
      Znth role (Znth new_person skill []) 0).
    split; [|unfold new_person; lia].
    pose proof (small_mask_add_bit__solver_row_close positions source role
      Hpositions Hsource Hrole Hbit) as [Htarget_mask _].
    split; [exact Htarget_mask |].
    exists ((role, new_person) :: assignments), audience_people.
    split.
    + eapply bounded_match_cons__solver_row_close; eauto.
    + split.
      * simpl. constructor; assumption.
      * split.
        -- simpl. constructor.
           ++ exists processed. split; [lia | reflexivity].
           ++ exact Hlift.
        -- split.
           ++ simpl. rewrite Zlength_cons.
              unfold Z.succ.
              replace (processed + 1 - (Zlength assignments + 1))
                with (processed - Zlength assignments) by lia.
              exact Haudience_len.
           ++ simpl. rewrite Hscore_old. lia.
Qed.

Lemma fold_right_add_nonnegative__solver_row_close :
  forall values,
    Forall (fun value => 0 <= value) values ->
    0 <= fold_right Z.add 0 values.
Proof.
  intros values Hall. induction Hall; simpl; lia.
Qed.

Lemma bounded_choice_score_nonnegative__solver_row_close :
  forall audience skill order positions audience_limit processed mask score,
    (forall person,
      ProcessedPerson order processed person ->
      0 <= Znth person audience 0) ->
    (forall role person,
      0 <= role < positions ->
      ProcessedPerson order processed person ->
      0 <= Znth role (Znth person skill []) 0) ->
    BoundedTeamPrefixChoice audience skill order positions audience_limit
      processed mask score ->
    0 <= score.
Proof.
  intros audience skill order positions audience_limit processed mask score
    Haudience Hskill Hchoice.
  unfold BoundedTeamPrefixChoice in Hchoice.
  destruct Hchoice as [_ [assignments [audience_people
    [Hmatch [_ [Hprocessed [_ Hscore]]]]]]].
  destruct Hmatch as [_ Hrole_bounds].
  rewrite Hscore. apply Z.add_nonneg_nonneg.
  - apply fold_right_add_nonnegative__solver_row_close.
    rewrite Forall_forall. intros contribution Hin.
    apply in_map_iff in Hin as [[role person] [Heq Hin]]. simpl in Heq.
    subst contribution. apply Hskill.
    + rewrite Forall_forall in Hrole_bounds.
      specialize (Hrole_bounds (role, person) Hin). exact Hrole_bounds.
    + rewrite Forall_forall in Hprocessed.
      apply Hprocessed. apply in_or_app. left.
      apply in_map_iff. exists (role, person). split; [reflexivity | exact Hin].
  - apply fold_right_add_nonnegative__solver_row_close.
    rewrite Forall_forall. intros contribution Hin.
    apply in_map_iff in Hin as [person [Heq Hin]]. subst contribution.
    apply Haudience. rewrite Forall_forall in Hprocessed.
    apply Hprocessed. apply in_or_app. right. exact Hin.
Qed.

Lemma fold_map_middle__solver_row_close :
  forall {A : Type} (f : A -> Z) before x after,
    fold_right Z.add 0 (map f (before ++ x :: after)) =
    f x + fold_right Z.add 0 (map f (before ++ after)).
Proof.
  intros A f before x after.
  rewrite !map_app, !fold_right_add_app__solver_row_close.
  simpl. lia.
Qed.

Lemma processed_selection_without_new__solver_row_close :
  forall order processed before after,
    0 <= processed ->
    let new_person :=
      Znth (Zlength order - 1 - processed) order 0 in
    NoDup (before ++ new_person :: after) ->
    Forall (ProcessedPerson order (processed + 1))
      (before ++ new_person :: after) ->
    Forall (ProcessedPerson order processed) (before ++ after).
Proof.
  intros order processed before after Hprocessed new_person Hnodup Hall.
  apply Forall_forall. intros person Hin.
  assert (Hin_next : In person (before ++ new_person :: after)).
  {
    apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [Hin | Hin].
    - left. exact Hin.
    - right. simpl. right. exact Hin.
  }
  apply Forall_forall with (x := person) in Hall; [|exact Hin_next].
  destruct (processed_person_succ_cases__solver_row_close
    order processed person Hprocessed Hall) as [Heq | Hold]; [|exact Hold].
  exfalso. subst person.
  apply NoDup_remove_2 with (a := new_person) in Hnodup.
  exact (Hnodup Hin).
Qed.

Lemma team_neg_inf_negative__solver_row_close : TeamNegInf < 0.
Proof.
  unfold TeamNegInf.
  pose proof (Z.pow_pos_nonneg 2 60 ltac:(lia)).
  lia.
Qed.

Lemma bounded_choice_to_transition__solver_row_close :
  forall audience sorted_audience skill order positions audience_limit processed
    old_values target choice_score,
    0 <= positions <= 7 ->
    1 <= audience_limit ->
    0 <= processed < Zlength order ->
    NoDup order ->
    Znth (Zlength sorted_audience - 1 - processed) sorted_audience 0 =
      Znth (Znth (Zlength order - 1 - processed) order 0) audience 0 ->
    (forall old_person,
      ProcessedPerson order processed old_person ->
      Znth (Znth (Zlength order - 1 - processed) order 0) audience 0 <=
        Znth old_person audience 0) ->
    (forall person,
      ProcessedPerson order processed person ->
      0 <= Znth person audience 0) ->
    (forall role person,
      0 <= role < positions ->
      ProcessedPerson order processed person ->
      0 <= Znth role (Znth person skill []) 0) ->
    BoundedTeamDPTable audience skill order positions audience_limit processed
      old_values ->
    BoundedTeamPrefixChoice audience skill order positions audience_limit
      (processed + 1) target choice_score ->
    exists transition_score,
      TeamTransitionCandidate sorted_audience order skill positions
        audience_limit processed old_values (2 ^ positions) target
        transition_score /\
      choice_score <= transition_score.
Proof.
  intros audience sorted_audience skill order positions audience_limit processed
    old_values target choice_score Hpositions Haudience_limit Hprocessed
    Horder Hnew_audience Hdominates Haudience_nonnegative Hskill_nonnegative
    Htable Hchoice.
  unfold BoundedTeamPrefixChoice in Hchoice.
  destruct Hchoice as [Htarget [assignments [audience_people
    [Hmatch [Hselected [Hprocessed_all [Haudience_len Hchoice_score]]]]]]].
  set (new_person :=
    Znth (Zlength order - 1 - processed) order 0).
  set (role_score := fun assignment : Z * Z =>
    Znth (fst assignment) (Znth (snd assignment) skill []) 0).
  set (audience_score := fun person : Z => Znth person audience 0).
  change (choice_score =
    fold_right Z.add 0 (map role_score assignments) +
    fold_right Z.add 0 (map audience_score audience_people))
    in Hchoice_score.
  destruct (classic (In new_person (map snd assignments))) as
    [Hin_role | Hnot_role].
  - apply in_map_iff in Hin_role.
    destruct Hin_role as [[role person] [Hperson Hin_assignment]].
    simpl in Hperson. subst person.
    apply in_split in Hin_assignment.
    destruct Hin_assignment as [before [after Hassignments]].
    subst assignments.
    destruct (bounded_match_remove__solver_row_close positions target before
      after role new_person Hpositions Htarget Hmatch) as
      [source [Hsource [Hsource_bit [Hsource_target Hsource_match]]]].
    assert (Hselected_shape :
      map snd (before ++ (role, new_person) :: after) ++ audience_people =
      map snd before ++ new_person :: (map snd after ++ audience_people)).
    { rewrite map_app. simpl. rewrite <- app_assoc. reflexivity. }
    rewrite Hselected_shape in Hselected, Hprocessed_all.
    assert (Hold_selected :
      NoDup (map snd (before ++ after) ++ audience_people)).
    {
      rewrite map_app, <- app_assoc.
      apply NoDup_remove_1 with (a := new_person).
      exact Hselected.
    }
    assert (Hold_processed :
      Forall (ProcessedPerson order processed)
        (map snd (before ++ after) ++ audience_people)).
    {
      rewrite map_app, <- app_assoc.
      eapply processed_selection_without_new__solver_row_close;
        [lia | exact Hselected | exact Hprocessed_all].
    }
    assert (Hold_choice :
      BoundedTeamPrefixChoice audience skill order positions audience_limit
        processed source
        (fold_right Z.add 0 (map role_score (before ++ after)) +
         fold_right Z.add 0 (map audience_score audience_people))).
    {
      split; [exact Hsource |].
      exists (before ++ after), audience_people.
      split; [exact Hsource_match |]. split; [exact Hold_selected |].
      split; [exact Hold_processed |]. split.
      - rewrite !Zlength_correct in Haudience_len |- *.
        rewrite length_app in Haudience_len |- *.
        simpl in Haudience_len. lia.
      - reflexivity.
    }
    assert (Hold_nonnegative :
      0 <= fold_right Z.add 0 (map role_score (before ++ after)) +
        fold_right Z.add 0 (map audience_score audience_people)).
    {
      eapply bounded_choice_score_nonnegative__solver_row_close;
        [exact Haudience_nonnegative | exact Hskill_nonnegative |].
      exact Hold_choice.
    }
    pose proof (bounded_dp_choice_upper__solver_row_close audience skill order
      positions audience_limit processed old_values source
      (fold_right Z.add 0 (map role_score (before ++ after)) +
       fold_right Z.add 0 (map audience_score audience_people))
      Hsource Htable Hold_choice) as Hupper.
    assert (Hlive : Znth source old_values TeamNegInf <> TeamNegInf).
    {
      intro Heq. rewrite Heq in Hupper.
      pose proof team_neg_inf_negative__solver_row_close. lia.
    }
    assert (Hrole : 0 <= role < positions).
    {
      destruct Hmatch as [_ Hbounds].
      apply Forall_forall with (x := (role, new_person)) in Hbounds.
      - exact Hbounds.
      - apply in_or_app. right. simpl. auto.
    }
    exists (Znth source old_values TeamNegInf +
      Znth role (Znth new_person skill []) 0).
    split.
    + exists source, (Znth source old_values TeamNegInf).
      split; [exact Hsource |].
      split; [reflexivity |].
      split; [exact Hlive |].
      right. right. exists role.
      split; [exact Hrole |].
      split; [exact Hsource_bit |].
      split; [symmetry; exact Hsource_target |].
      reflexivity.
    + rewrite (fold_map_middle__solver_row_close role_score before
        (role, new_person) after) in Hchoice_score.
      unfold role_score, audience_score in *.
      simpl in Hchoice_score. lia.
  - destruct (classic (In new_person audience_people)) as
      [Hin_audience | Hnot_audience].
    + apply in_split in Hin_audience.
      destruct Hin_audience as [before [after Haudience_people]].
      subst audience_people.
      assert (Hselected_shape :
        map snd assignments ++ before ++ new_person :: after =
        (map snd assignments ++ before) ++ new_person :: after).
      { rewrite app_assoc. reflexivity. }
      rewrite Hselected_shape in Hselected, Hprocessed_all.
      assert (Hold_selected :
        NoDup (map snd assignments ++ before ++ after)).
      {
        rewrite app_assoc.
        apply NoDup_remove_1 with (a := new_person).
        exact Hselected.
      }
      assert (Hold_processed :
        Forall (ProcessedPerson order processed)
          (map snd assignments ++ before ++ after)).
      {
        rewrite app_assoc.
        eapply processed_selection_without_new__solver_row_close;
          [lia | exact Hselected | exact Hprocessed_all].
      }
      destruct (Z_lt_ge_dec
        (processed - Zlength assignments) audience_limit) as
        [Hunsaturated | Hsaturated].
      * assert (Hold_choice :
          BoundedTeamPrefixChoice audience skill order positions audience_limit
            processed target
            (fold_right Z.add 0 (map role_score assignments) +
             fold_right Z.add 0 (map audience_score (before ++ after)))).
        {
          split; [exact Htarget |]. exists assignments, (before ++ after).
          split; [exact Hmatch |]. split; [exact Hold_selected |].
          split; [exact Hold_processed |]. split.
          - rewrite Z.min_r by lia.
            rewrite Z.min_r in Haudience_len by lia.
            rewrite !Zlength_correct in Haudience_len |- *.
            rewrite length_app in Haudience_len |- *.
            simpl in Haudience_len. lia.
          - reflexivity.
        }
        assert (Hold_nonnegative :
          0 <= fold_right Z.add 0 (map role_score assignments) +
            fold_right Z.add 0 (map audience_score (before ++ after))).
        {
          eapply bounded_choice_score_nonnegative__solver_row_close;
            [exact Haudience_nonnegative | exact Hskill_nonnegative |].
          exact Hold_choice.
        }
        pose proof (bounded_dp_choice_upper__solver_row_close audience skill
          order positions audience_limit processed old_values target
          (fold_right Z.add 0 (map role_score assignments) +
           fold_right Z.add 0 (map audience_score (before ++ after)))
          Htarget Htable Hold_choice) as Hupper.
        assert (Hlive : Znth target old_values TeamNegInf <> TeamNegInf).
        {
          intro Heq. rewrite Heq in Hupper.
          pose proof team_neg_inf_negative__solver_row_close. lia.
        }
        set (used := fold_right Z.add 0
          (map (fun bit => if Z.testbit target bit then 1 else 0)
            (Zrange 0 32))).
        assert (Hused_count : BitCount target used).
        { unfold BitCount, used. reflexivity. }
        assert (Hused_assignments : used = Zlength assignments).
        {
          eapply bitcount_assignments_length__solver_row_close;
            [exact Hpositions | exact Htarget | exact Hmatch | exact Hused_count].
        }
        exists (Znth target old_values TeamNegInf +
          Znth (Zlength sorted_audience - 1 - processed)
            sorted_audience 0).
        split.
        -- exists target, (Znth target old_values TeamNegInf).
           split; [exact Htarget |].
           split; [reflexivity |].
           split; [exact Hlive |].
           right. left. exists used.
           split; [exact Hused_count |].
           split; [lia |].
           split; reflexivity.
        -- unfold role_score, audience_score in *.
           rewrite fold_map_middle__solver_row_close in Hchoice_score.
           unfold new_person in Hchoice_score.
           rewrite <- Hnew_audience in Hchoice_score. lia.
      * assert (Hremaining_len :
          Zlength (map snd assignments ++ before ++ after) < processed).
        {
          rewrite Z.min_l in Haudience_len by lia.
          assert (Hmap_len : Zlength (map snd assignments) =
            Zlength assignments).
          { rewrite !Zlength_correct, length_map. reflexivity. }
          rewrite !Zlength_app, Hmap_len.
          rewrite !Zlength_app, Zlength_cons in Haudience_len. lia.
        }
        destruct (processed_missing_person__solver_row_close order processed
          (map snd assignments ++ before ++ after) Horder ltac:(lia)
          Hold_selected Hremaining_len) as
          [replacement [Hreplacement Hreplacement_notin]].
        assert (Hreplacement_selected :
          NoDup (map snd assignments ++ replacement :: (before ++ after))).
        {
          assert (Hperm : Permutation
            (replacement :: (map snd assignments ++ before ++ after))
            (map snd assignments ++ replacement :: (before ++ after))).
          { apply Permutation_middle. }
          eapply Permutation_NoDup; [exact Hperm |].
          constructor; [exact Hreplacement_notin | exact Hold_selected].
        }
        assert (Hreplacement_processed :
          Forall (ProcessedPerson order processed)
            (map snd assignments ++ replacement :: (before ++ after))).
        {
          apply Forall_forall. intros person Hin.
          apply in_app_or in Hin. destruct Hin as [Hin | Hin].
          - apply Forall_forall with (x := person) in Hold_processed.
            + exact Hold_processed.
            + apply in_or_app. left. exact Hin.
          - simpl in Hin. destruct Hin as [-> | Hin].
            + exact Hreplacement.
            + apply Forall_forall with (x := person) in Hold_processed.
              * exact Hold_processed.
              * apply in_or_app. right. exact Hin.
        }
        assert (Hold_choice :
          BoundedTeamPrefixChoice audience skill order positions audience_limit
            processed target
            (fold_right Z.add 0 (map role_score assignments) +
             fold_right Z.add 0
               (map audience_score (replacement :: before ++ after)))).
        {
          split; [exact Htarget |].
          exists assignments, (replacement :: before ++ after).
          split; [exact Hmatch |]. split; [exact Hreplacement_selected |].
          split; [exact Hreplacement_processed |]. split.
          - rewrite Z.min_l by lia.
            rewrite Z.min_l in Haudience_len by lia.
            rewrite Zlength_cons, Zlength_app.
            rewrite Zlength_app, Zlength_cons in Haudience_len. lia.
          - reflexivity.
        }
        assert (Hold_nonnegative :
          0 <= fold_right Z.add 0 (map role_score assignments) +
            fold_right Z.add 0
              (map audience_score (replacement :: before ++ after))).
        {
          eapply bounded_choice_score_nonnegative__solver_row_close;
            [exact Haudience_nonnegative | exact Hskill_nonnegative |].
          exact Hold_choice.
        }
        pose proof (bounded_dp_choice_upper__solver_row_close audience skill
          order positions audience_limit processed old_values target
          (fold_right Z.add 0 (map role_score assignments) +
           fold_right Z.add 0
             (map audience_score (replacement :: before ++ after)))
          Htarget Htable Hold_choice) as Hupper.
        assert (Hlive : Znth target old_values TeamNegInf <> TeamNegInf).
        {
          intro Heq. rewrite Heq in Hupper.
          pose proof team_neg_inf_negative__solver_row_close. lia.
        }
        pose proof (Hdominates replacement Hreplacement) as Hreplace_score.
        exists (Znth target old_values TeamNegInf).
        split.
        -- exists target, (Znth target old_values TeamNegInf).
           split; [exact Htarget |].
           split; [reflexivity |].
           split; [exact Hlive |].
           left. split; reflexivity.
        -- unfold role_score, audience_score in *.
           rewrite fold_map_middle__solver_row_close in Hchoice_score.
           unfold new_person in Hchoice_score.
           simpl in *. lia.
    + assert (Hold_processed :
        Forall (ProcessedPerson order processed)
          (map snd assignments ++ audience_people)).
      {
        apply Forall_forall. intros person Hin.
        apply Forall_forall with (x := person) in Hprocessed_all;
          [|exact Hin].
        destruct (processed_person_succ_cases__solver_row_close
          order processed person ltac:(lia) Hprocessed_all) as [Heq | Hold].
        - exfalso. subst person.
          apply in_app_or in Hin. destruct Hin as [Hin | Hin].
          + exact (Hnot_role Hin).
          + exact (Hnot_audience Hin).
        - exact Hold.
      }
      assert (Hsaturated :
        audience_limit <= processed - Zlength assignments).
      {
        destruct (Z_lt_ge_dec
          (processed - Zlength assignments) audience_limit) as
          [Hunsaturated | Hsaturated].
        - pose proof (processed_selection_card__solver_row_close order processed
            (map snd assignments ++ audience_people) ltac:(lia) Hselected
            Hold_processed) as Hcard.
          rewrite Z.min_r in Haudience_len by lia.
          assert (Hmap_len : Zlength (map snd assignments) =
            Zlength assignments).
          { rewrite !Zlength_correct, length_map. reflexivity. }
          rewrite Zlength_app, Hmap_len in Hcard. lia.
        - lia.
      }
      assert (Hold_choice :
        BoundedTeamPrefixChoice audience skill order positions audience_limit
          processed target choice_score).
      {
        split; [exact Htarget |]. exists assignments, audience_people.
        split; [exact Hmatch |]. split; [exact Hselected |].
        split; [exact Hold_processed |]. split.
        - rewrite Haudience_len. rewrite Z.min_l by lia.
          rewrite Z.min_l by lia. reflexivity.
        - exact Hchoice_score.
      }
      assert (Hchoice_nonnegative : 0 <= choice_score).
      {
        eapply bounded_choice_score_nonnegative__solver_row_close;
          [exact Haudience_nonnegative | exact Hskill_nonnegative |].
        exact Hold_choice.
      }
      pose proof (bounded_dp_choice_upper__solver_row_close audience skill order
        positions audience_limit processed old_values target choice_score
        Htarget Htable Hold_choice) as Hupper.
      assert (Hlive : Znth target old_values TeamNegInf <> TeamNegInf).
      {
        intro Heq. rewrite Heq in Hupper.
        pose proof team_neg_inf_negative__solver_row_close. lia.
      }
      exists (Znth target old_values TeamNegInf).
      split.
      * exists target, (Znth target old_values TeamNegInf).
        split; [exact Htarget |].
        split; [reflexivity |].
        split; [exact Hlive |].
        left. split; reflexivity.
      * exact Hupper.
Qed.

Lemma bounded_team_row_close_core__solver_row_close :
  forall audience sorted_audience skill order positions audience_limit processed
    old_values next_values,
    0 <= positions <= 7 ->
    1 <= audience_limit ->
    0 <= processed < Zlength order ->
    NoDup order ->
    Znth (Zlength sorted_audience - 1 - processed) sorted_audience 0 =
      Znth (Znth (Zlength order - 1 - processed) order 0) audience 0 ->
    1 <= Znth (Zlength sorted_audience - 1 - processed)
      sorted_audience 0 ->
    (forall old_person,
      ProcessedPerson order processed old_person ->
      Znth (Znth (Zlength order - 1 - processed) order 0) audience 0 <=
        Znth old_person audience 0) ->
    (forall person,
      ProcessedPerson order processed person ->
      0 <= Znth person audience 0) ->
    (forall role person,
      0 <= role < positions ->
      ProcessedPerson order processed person ->
      0 <= Znth role (Znth person skill []) 0) ->
    BoundedTeamDPTable audience skill order positions audience_limit processed
      old_values ->
    BoundedTeamNextRowProgress sorted_audience order skill positions
      audience_limit processed old_values next_values (2 ^ positions) ->
    BoundedTeamDPTable audience skill order positions audience_limit
      (processed + 1) next_values.
Proof.
  intros audience sorted_audience skill order positions audience_limit processed
    old_values next_values Hpositions Haudience_limit Hprocessed Horder
    Hnew_audience Hnew_positive Hdominates Haudience_nonnegative
    Hskill_nonnegative Htable Hprogress.
  unfold BoundedTeamDPTable. intros target Htarget.
  specialize (Hprogress target Htarget).
  unfold BoundedTeamDPCell.
  destruct Hprogress as [Hmaximum | [Hnegative Hnone]].
  - left. eapply max_value_cofinal__solver_row_close.
    + intros transition_score Htransition.
      eapply transition_to_bounded_choice__solver_row_close; eauto.
    + intros choice_score Hchoice.
      eapply bounded_choice_to_transition__solver_row_close; eauto.
    + exact Hmaximum.
  - right. split; [exact Hnegative |].
    intros choice_score Hchoice.
    destruct (bounded_choice_to_transition__solver_row_close audience
      sorted_audience skill order positions audience_limit processed old_values
      target choice_score Hpositions Haudience_limit Hprocessed Horder
      Hnew_audience Hdominates Haudience_nonnegative Hskill_nonnegative Htable
      Hchoice) as [transition_score [Htransition _]].
    exact (Hnone transition_score Htransition).
Qed.

Theorem bounded_team_next_row_closes__solver_row_close :
  forall n audience skill order_values sorted_audience sorted_order
    positions audience_limit processed old_values next_values,
    2 <= n ->
    1 <= positions <= 7 ->
    1 <= audience_limit ->
    n = Zlength audience ->
    positions = Zlength (Znth 0 skill []) ->
    Zlength order_values = n ->
    Zlength sorted_audience = n ->
    Zlength sorted_order = n ->
    Pre audience_limit audience skill ->
    Forall (Forall (fun x => 1 <= x <= 1000000000)) skill ->
    SortedPeopleState audience order_values sorted_audience sorted_order ->
    (forall q, 0 <= q < n -> 1 <= Znth q sorted_audience 0) ->
    (forall q, 0 <= q < n -> Znth q order_values 0 = q) ->
    0 <= processed < n ->
    BoundedTeamDPTable audience skill sorted_order positions audience_limit
      processed old_values ->
    BoundedTeamNextRowProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values (2 ^ positions) ->
    BoundedTeamDPTable audience skill sorted_order positions audience_limit
      (processed + 1) next_values.
Proof.
  intros n audience skill order_values sorted_audience sorted_order positions
    audience_limit processed old_values next_values Hn Hpositions
    Haudience_limit Hn_audience Hpositions_row0 Horder_values_len
    Hsorted_audience_len Hsorted_order_len Hpre Hskill_values Hsorted
    Hsorted_audience_positive Hidentity Hprocessed Htable Hprogress.
  assert (Hsorted_saved := Hsorted).
  destruct Hsorted as
    [Hsorted_aud_len [Hsorted_ord_len [Hpermutation [Hincreasing Hmap]]]].
  assert (Horder_nodup : NoDup sorted_order).
  {
    eapply sorted_order_nodup__solver_row_close with (n := n).
    - symmetry. exact Hn_audience.
    - exact Horder_values_len.
    - exact Hsorted_audience_len.
    - exact Hsorted_order_len.
    - exact Hidentity.
    - exact Hpermutation.
  }
  assert (Hrank :
    0 <= Zlength sorted_order - 1 - processed < Zlength sorted_order) by lia.
  pose proof (Hmap (Zlength sorted_order - 1 - processed) Hrank) as
    [Hnew_person_bounds Hnew_audience].
  assert (Hnew_positive :
    1 <= Znth (Zlength sorted_audience - 1 - processed)
      sorted_audience 0).
  {
    apply Hsorted_audience_positive. lia.
  }
  assert (Hsame_sorted_length :
    Zlength sorted_audience = Zlength sorted_order) by lia.
  assert (Hdominates : forall old_person,
    ProcessedPerson sorted_order processed old_person ->
    Znth (Znth (Zlength sorted_order - 1 - processed) sorted_order 0)
      audience 0 <= Znth old_person audience 0).
  {
    intros old_person Hold_person.
    eapply processed_audience_dominates_new__solver_row_close.
    - exact Hsorted_saved.
    - exact Hsame_sorted_length.
    - lia.
    - exact Hold_person.
  }
  assert (Haudience_nonnegative : forall person,
    ProcessedPerson sorted_order processed person ->
    0 <= Znth person audience 0).
  {
    intros person [step [[Hstep0 Hstep] Hperson]].
    assert (Hstep_rank :
      0 <= Zlength sorted_order - 1 - step < Zlength sorted_order) by lia.
    pose proof (Hmap (Zlength sorted_order - 1 - step) Hstep_rank) as
      [_ Hperson_audience].
    pose proof (Hsorted_audience_positive
      (Zlength sorted_order - 1 - step) ltac:(lia)) as Hpositive.
    rewrite <- Hperson in Hperson_audience.
    rewrite Hperson_audience in Hpositive. lia.
  }
  destruct Hpre as
    [Hskill_len [declared_positions [Hcapacity [_ Hrows]]]].
  assert (Hdeclared_positions_eq : declared_positions = positions).
  {
    pose proof ((proj1
      (Forall_Znth (fun row => Zlength row = declared_positions) [] skill))
      Hrows 0 ltac:(lia)) as Hrow0_len.
    rewrite Hrow0_len in Hpositions_row0. lia.
  }
  assert (Hskill_nonnegative : forall role person,
    0 <= role < positions ->
    ProcessedPerson sorted_order processed person ->
    0 <= Znth role (Znth person skill []) 0).
  {
    intros role person Hrole [step [[Hstep0 Hstep] Hperson]].
    assert (Hstep_rank :
      0 <= Zlength sorted_order - 1 - step < Zlength sorted_order) by lia.
    pose proof (Hmap (Zlength sorted_order - 1 - step) Hstep_rank) as
      [Hperson_bounds _].
    rewrite <- Hperson in Hperson_bounds.
    pose proof ((proj1
      (Forall_Znth
        (Forall (fun value => 1 <= value <= 1000000000)) [] skill))
      Hskill_values person ltac:(lia)) as Hrow_values.
    pose proof ((proj1
      (Forall_Znth (fun row => Zlength row = declared_positions) [] skill))
      Hrows person ltac:(lia)) as Hrow_len.
    assert (Hrole_row : 0 <= role < Zlength (Znth person skill [])).
    { rewrite Hrow_len, Hdeclared_positions_eq. exact Hrole. }
    pose proof ((proj1
      (Forall_Znth (fun value => 1 <= value <= 1000000000) 0
        (Znth person skill []))) Hrow_values role Hrole_row) as Hvalue.
    eapply Z.le_trans; [exact Z.le_0_1 | exact (proj1 Hvalue)].
  }
  eapply bounded_team_row_close_core__solver_row_close.
  - lia.
  - exact Haudience_limit.
  - lia.
  - exact Horder_nodup.
  - rewrite Hsame_sorted_length. exact Hnew_audience.
  - exact Hnew_positive.
  - exact Hdominates.
  - exact Haudience_nonnegative.
  - exact Hskill_nonnegative.
  - exact Htable.
  - exact Hprogress.
Qed.

Require Import Coq.micromega.Psatz.
Require Import Coq.setoid_ring.Ring.
Lemma Zrange_zero_succ__popcount : forall k,
  0 <= k ->
  Zrange 0 (k + 1) = Zrange 0 k ++ [k].
Proof.
  intros k Hk.
  unfold Zrange.
  replace (Z.to_nat (k + 1 - 0))
    with (Z.to_nat (k - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app. simpl.
  replace (k - 0) with k by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma Zrange_zero_split__popcount : forall mid high,
  0 <= mid <= high ->
  Zrange 0 high = Zrange 0 mid ++ Zrange mid high.
Proof.
  intros mid high Hbounds.
  unfold Zrange.
  replace (Z.to_nat (high - 0))
    with (Z.to_nat (mid - 0) + Z.to_nat (high - mid))%nat by lia.
  rewrite Zrange_aux_app.
  replace (0 + Z.of_nat (Z.to_nat (mid - 0))) with mid by lia.
  reflexivity.
Qed.
Lemma fold_add_app__popcount : forall left right,
  fold_right Z.add 0 (left ++ right) =
  fold_right Z.add 0 left + fold_right Z.add 0 right.
Proof.
  induction left as [|x left IH]; intros right; simpl.
  - lia.
  - rewrite IH. lia.
Qed.
Lemma fold_add_map_zero__popcount : forall values : list Z,
  fold_right Z.add 0 (map (fun _ => 0) values) = 0.
Proof.
  induction values as [|x values IH]; simpl; auto.
Qed.
Lemma land_shiftr_one_bit__popcount : forall original consumed,
  0 <= consumed ->
  Z.land (Z.shiftr original consumed) 1 =
  Z.b2z (Z.testbit original consumed).
Proof.
  intros original consumed Hconsumed.
  replace 1 with (Z.ones 1) by reflexivity.
  rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  symmetry.
  apply Z.testbit_spec'; lia.
Qed.
Lemma bitcount_progress_step__popcount : forall original remaining count,
  0 <= original < 128 ->
  remaining <> 0 ->
  BitCountProgress original remaining count ->
  BitCountProgress original (Z.shiftr remaining 1)
    (count + Z.land remaining 1).
Proof.
  intros original remaining count Horiginal Hremaining Hprogress.
  unfold BitCountProgress in Hprogress |- *.
  destruct Hprogress as (consumed & Hconsumed & Hremain & Hcount).
  assert (Hlt : consumed < 32).
  {
    destruct Hconsumed as [Hnonneg Hle].
    assert (Hne : consumed <> 32).
    {
      intro Heq. subst consumed.
      rewrite Z.shiftr_div_pow2 in Hremain by lia.
      change (remaining = original / 4294967296) in Hremain.
      rewrite Z.div_small in Hremain by lia.
      contradiction.
    }
    lia.
  }
  exists (consumed + 1).
  split; [lia|].
  split.
  - rewrite Hremain, Z.shiftr_shiftr by lia. f_equal.
  - rewrite Hcount, Zrange_zero_succ__popcount by lia.
    rewrite map_app, fold_add_app__popcount. simpl.
    rewrite Hremain.
    rewrite land_shiftr_one_bit__popcount by lia.
    destruct (Z.testbit original consumed); simpl; lia.
Qed.
Lemma bitcount_progress_finish__popcount : forall original remaining count,
  0 <= original < 128 ->
  remaining = 0 ->
  BitCountProgress original remaining count ->
  BitCount original count.
Proof.
  intros original remaining count Horiginal Hremaining Hprogress.
  unfold BitCountProgress in Hprogress.
  destruct Hprogress as (consumed & Hconsumed & Hremain & Hcount).
  unfold BitCount.
  rewrite Hcount.
  rewrite (Zrange_zero_split__popcount consumed 32) by lia.
  rewrite map_app, fold_add_app__popcount.
  assert (Hshift0 : Z.shiftr original consumed = 0) by lia.
  assert (Hzeros :
    map (fun bit => if Z.testbit original bit then 1 else 0)
      (Zrange consumed 32) =
    map (fun _ => 0) (Zrange consumed 32)).
  {
    apply map_ext_in.
    intros bit Hbit.
    apply In_Zrange in Hbit.
    pose proof (Z.shiftr_spec original consumed (bit - consumed)
      ltac:(lia)) as Htest.
    rewrite Hshift0, Z.testbit_0_l in Htest.
    replace (bit - consumed + consumed) with bit in Htest by lia.
    rewrite <- Htest. reflexivity.
  }
  rewrite Hzeros.
  rewrite fold_add_map_zero__popcount, Z.add_0_r.
  reflexivity.
Qed.
Lemma Zlength_Zrange_aux__popcount : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low. induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__popcount : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__popcount. lia.
Qed.
Lemma fold_bit_indicator_bound__popcount : forall original values,
  fold_right Z.add 0
      (map (fun bit => if Z.testbit original bit then 1 else 0) values)
    <= Zlength values.
Proof.
  intros original values. induction values as [|bit values IH].
  - rewrite Zlength_nil. simpl. lia.
  - simpl map. simpl fold_right.
    rewrite Zlength_cons.
    unfold Z.succ.
    destruct (Z.testbit original bit).
    + change (1 + fold_right Z.add 0
        (map (fun bit => if Z.testbit original bit then 1 else 0) values)
        <= Zlength values + 1).
      lia.
    + change (0 + fold_right Z.add 0
        (map (fun bit => if Z.testbit original bit then 1 else 0) values)
        <= Zlength values + 1).
      lia.
Qed.
Lemma bitcount_progress_step_bound__popcount : forall original remaining count,
  0 <= original < 128 ->
  remaining <> 0 ->
  BitCountProgress original remaining count ->
  count + Z.land remaining 1 <= 7.
Proof.
  intros original remaining count Horiginal Hremaining Hprogress.
  unfold BitCountProgress in Hprogress.
  destruct Hprogress as (consumed & Hconsumed & Hremain & Hcount).
  assert (Hconsumed_lt : consumed < 7).
  {
    destruct (Z_lt_ge_dec consumed 7) as [Hlt | Hge]; [exact Hlt |].
    assert (Hpow : 128 <= 2 ^ consumed).
    {
      replace 128 with (2 ^ 7) by reflexivity.
      apply Z.pow_le_mono_r; lia.
    }
    rewrite Z.shiftr_div_pow2 in Hremain by lia.
    rewrite Z.div_small in Hremain by lia.
    contradiction.
  }
  pose proof (fold_bit_indicator_bound__popcount original
    (Zrange 0 consumed)) as Hcount_bound.
  rewrite Zlength_Zrange__popcount in Hcount_bound by lia.
  rewrite <- Hcount in Hcount_bound.
  pose proof (land_shiftr_one_bit__popcount remaining 0 ltac:(lia)) as Hbit.
  rewrite Z.shiftr_0_r in Hbit.
  rewrite Hbit.
  destruct (Z.testbit remaining 0); simpl; lia.
Qed.
Lemma Zlength_replace_Znth__sift_transition_exit :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. revert n.
  induction l as [|x xs IH]; intros n; simpl; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n) as [|k].
  - simpl. repeat rewrite Zlength_cons. lia.
  - simpl. repeat rewrite Zlength_cons.
    specialize (IH (Z.of_nat k)).
    replace (Z.to_nat (Z.of_nat k)) with k in IH by lia.
    rewrite IH. lia.
Qed.
Lemma double_replace_suffix__sift_transition_exit :
  forall {A : Type} (l : list A) (vi vj : A) i j lo hi,
    0 <= i < lo ->
    0 <= j < lo ->
    0 <= lo <= hi ->
    hi <= Zlength l ->
    sublist lo hi (replace_Znth j vj (replace_Znth i vi l)) =
    sublist lo hi l.
Proof.
  intros A l vi vj i j lo hi Hi Hj Hlohi Hhi.
  destruct Hlohi as [Hlo Hlohi].
  apply (proj2 (list_eq_ext _ _ vi)). split.
  - rewrite !Zlength_sublist'.
    assert (Hlen :
      length (replace_Znth j vj (replace_Znth i vi l)) = length l).
    {
      apply Nat2Z.inj.
      repeat rewrite <- Zlength_correct.
      rewrite (Zlength_replace_Znth__sift_transition_exit (replace_Znth i vi l) j vj).
      rewrite (Zlength_replace_Znth__sift_transition_exit l i vi).
      reflexivity.
    }
    rewrite Hlen.
    reflexivity.
  - intros k Hk.
    rewrite Zlength_sublist in Hk.
    2: { split; [lia |].
         repeat rewrite Zlength_replace_Znth__sift_transition_exit. lia. }
    rewrite !Znth_sublist by
      (repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    reflexivity.
Qed.
Lemma replace_Znth_swap_form__sift_transition_exit :
  forall {A : Type} (l1 l2 l3 : list A) (xi xj : A),
    replace_Znth (Zlength l1 + 1 + Zlength l2) xi
      (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
    l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros A l1 l2 l3 xi xj.
  pose proof (Zlength_nonneg l2).
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xi :: l2 ++ xj :: l3) by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  change (replace_Znth 0 xj (xi :: l2 ++ xj :: l3))
    with (xj :: l2 ++ xj :: l3).
  rewrite replace_Znth_app_r with
    (l1 := l1) (l2 := xj :: l2 ++ xj :: l3) by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := A)
    (n1 + 1 + Zlength l2) l1 xi) by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1)
    with (1 + Zlength l2) by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := xj :: l3) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  reflexivity.
Qed.
Lemma list_split_nth__sift_transition_exit :
  forall (A : Type) (n : nat) (l : list A) (d : A),
    (n < length l)%nat ->
    l = firstn n l ++ nth n l d :: skipn (S n) l.
Proof.
  intros A n l d Hn.
  apply firstn_skipSn. exact Hn.
Qed.
Lemma permutation_swap_Znth_lt__sift_transition_exit :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < j ->
    j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hij Hj.
  remember (Znth i l d) as xi.
  remember (Znth j l d) as xj.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth__sift_transition_exit _ (Z.to_nat i) l d) at 1.
    2: { rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi. reflexivity.
  }
  assert (Hj_lr : (nj < length lr)%nat).
  {
    subst nj lr ni. rewrite length_skipn.
    rewrite Zlength_correct in Hj. lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth__sift_transition_exit _ nj lr d) at 1 by exact Hj_lr.
    replace xj with (nth nj lr d).
    2: {
      subst nj lr ni. rewrite Heqxj. unfold Znth.
      rewrite nth_skipn.
      assert ((Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat =
              Z.to_nat j).
      {
        apply Nat2Z.inj. rewrite Nat2Z.inj_add, Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia. lia.
      }
      rewrite Nat.add_comm, H. reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi :: l2 ++ xj :: l3).
  { rewrite Hsplit_j in Hsplit_i. exact Hsplit_i. }
  replace l with (l1 ++ xi :: l2 ++ xj :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2: {
    subst l1 ni. rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj. rewrite Nat.min_l by lia. lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2: {
    subst l1 l2 lr ni nj. rewrite !Zlength_correct.
    rewrite !length_firstn, length_skipn.
    rewrite Zlength_correct in Hj. lia.
  }
  rewrite replace_Znth_swap_form__sift_transition_exit.
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head. apply perm_swap.
    + apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma replace_nth_comm__sift_transition_exit :
  forall {A : Type} ni nj (l : list A) a b,
    ni <> nj ->
    replace_nth nj (replace_nth ni l a) b =
    replace_nth ni (replace_nth nj l b) a.
Proof.
  intros A ni. induction ni as [|ni IH]; intros nj l a b Hneq;
    destruct l as [|x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl; [contradiction Hneq; reflexivity | reflexivity].
  - destruct nj; reflexivity.
  - destruct nj; simpl; [reflexivity |].
    f_equal. apply IH. intros Heq. apply Hneq. now f_equal.
Qed.
Lemma permutation_swap_Znth__sift_transition_exit :
  forall {A : Type} (l : list A) i j (d : A),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    Permutation l
      (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hij].
  - apply permutation_swap_Znth_lt__sift_transition_exit; lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Hji].
    + assert (Hcomm : forall a b,
        replace_Znth j b (replace_Znth i a l) =
        replace_Znth i a (replace_Znth j b l)).
      {
        intros a b. unfold replace_Znth.
        apply replace_nth_comm__sift_transition_exit. intro Heq.
        apply Z2Nat.inj in Heq; lia.
      }
      rewrite Hcomm.
      apply permutation_swap_Znth_lt__sift_transition_exit; lia.
    + assert (i = j) by lia. subst j.
      rewrite replace_Znth_Znth, replace_Znth_Znth.
      apply Permutation_refl.
Qed.
Lemma combine_replace_Znth_both__sift_transition_exit :
  forall {A B : Type} (xs : list A) (ys : list B) i x y,
    Zlength xs = Zlength ys ->
    0 <= i < Zlength xs ->
    combine (replace_Znth i x xs) (replace_Znth i y ys) =
    replace_Znth i (x, y) (combine xs ys).
Proof.
  intros A B xs. induction xs as [|a xs IH]; intros ys i x y Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|b ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct (Z.eq_dec i 0) as [-> | Hne].
      * reflexivity.
      * simpl. rewrite !replace_Znth_cons by lia. simpl. f_equal.
        apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Zlength_combine_eq__sift_transition_exit :
  forall {A B : Type} (xs : list A) (ys : list B),
    Zlength xs = Zlength ys ->
    Zlength (combine xs ys) = Zlength xs.
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys Hlen.
  - reflexivity.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. rewrite !Zlength_cons. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma Znth_combine__sift_transition_exit :
  forall {A B : Type} (xs : list A) (ys : list B) i da db,
    Zlength xs = Zlength ys ->
    0 <= i < Zlength xs ->
    Znth i (combine xs ys) (da, db) = (Znth i xs da, Znth i ys db).
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys i da db Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct (Z.eq_dec i 0) as [-> | Hne].
      * reflexivity.
      * simpl. rewrite !Znth_cons by lia. apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma people_parallel_permutation_swap__sift_transition_exit :
  forall audience0 order0 audience order root child,
    PeoplePermutation audience0 order0 audience order ->
    Zlength audience = Zlength order ->
    0 <= root < Zlength audience ->
    0 <= child < Zlength audience ->
    PeoplePermutation audience0 order0
      (replace_Znth child (Znth root audience 0)
        (replace_Znth root (Znth child audience 0) audience))
      (replace_Znth child (Znth root order 0)
        (replace_Znth root (Znth child order 0) order)).
Proof.
  intros audience0 order0 audience order root child Hperm Hlen Hroot Hchild.
  unfold PeoplePermutation in *.
  eapply Permutation_trans; [exact Hperm |].
  rewrite combine_replace_Znth_both__sift_transition_exit
    by (repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
  rewrite combine_replace_Znth_both__sift_transition_exit by lia.
  rewrite <- (@Znth_combine__sift_transition_exit Z Z audience order
    root 0 0 Hlen Hroot).
  rewrite <- (@Znth_combine__sift_transition_exit Z Z audience order
    child 0 0 Hlen Hchild).
  apply permutation_swap_Znth__sift_transition_exit;
    rewrite Zlength_combine_eq__sift_transition_exit by lia; lia.
Qed.
Lemma heap_parent_bounds__sift_transition_exit :
  forall child,
    0 < child ->
    0 <= (child - 1) / 2 < child.
Proof.
  intros child Hchild. split.
  - apply Z_div_nonneg_nonneg; lia.
  - assert ((child - 1) / 2 <= child - 1) by
      (apply Z.div_le_upper_bound; lia).
    lia.
Qed.
Lemma heap_children_characterization__sift_transition_exit :
  forall root child,
    0 <= root ->
    0 < child ->
    (child - 1) / 2 = root ->
    child = 2 * root + 1 \/ child = 2 * root + 2.
Proof.
  intros root child Hroot Hchild Hparent.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hrem.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hquot.
  rewrite Hparent in Hquot.
  assert (Z.modulo (child - 1) 2 = 0 \/ Z.modulo (child - 1) 2 = 1)
    as [Hr | Hr] by lia; lia.
Qed.
Lemma people_selected_child_parent__sift_transition_exit :
  forall audience root hi child,
    0 <= root ->
    PeopleSelectedLargerChild audience root hi child ->
    (child - 1) / 2 = root.
Proof.
  intros audience root hi child Hroot [[Hleft | Hright] _]; subst child.
  - replace (2 * root + 1 - 1) with (root * 2) by ring.
    rewrite Z.div_mul by lia. reflexivity.
  - replace (2 * root + 2 - 1) with (root * 2 + 1) by ring.
    pose proof (Z.mod_pos_bound (root * 2 + 1) 2 ltac:(lia)) as Hrem.
    pose proof (Z.div_mod (root * 2 + 1) 2 ltac:(lia)) as Hquot.
    assert (Z.modulo (root * 2 + 1) 2 = 1) by lia. lia.
Qed.
Lemma people_heap_except_after_selected_swap__sift_transition_exit :
  forall audience root0 root hi child,
    0 <= root0 <= root ->
    root <= hi ->
    hi < Zlength audience ->
    PeopleSelectedLargerChild audience root hi child ->
    Znth root audience 0 < Znth child audience 0 ->
    PeopleHeapOrderedExceptAt audience root0 hi root ->
    (1 <= root ->
      root0 <= (root - 1) / 2 ->
      Znth child audience 0 <= Znth ((root - 1) / 2) audience 0) ->
    PeopleHeapOrderedExceptAt
      (replace_Znth child (Znth root audience 0)
        (replace_Znth root (Znth child audience 0) audience))
      root0 hi child.
Proof.
  intros audience root0 root hi child Hroots Hroot_hi Hhi Hselected
    Hrise Hheap Henter.
  destruct Hselected as [Hchild_shape [Hchild_hi [Hleft Hright]]].
  assert (Hroot_range : 0 <= root < Zlength audience) by lia.
  assert (Hchild_parent : (child - 1) / 2 = root).
  {
    apply people_selected_child_parent__sift_transition_exit with
      (audience := audience) (hi := hi).
    - lia.
    - repeat split; assumption.
  }
  assert (Hroot_child : root < child).
  { destruct Hchild_shape as [-> | ->]; lia. }
  assert (Hchild_range : 0 <= child < Zlength audience) by lia.
  set (swapped :=
    replace_Znth child (Znth root audience 0)
      (replace_Znth root (Znth child audience 0) audience)).
  assert (Hswap_root : Znth root swapped 0 = Znth child audience 0).
  {
    unfold swapped.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    rewrite Znth_replace_Znth_Same by exact Hroot_range.
    reflexivity.
  }
  assert (Hswap_child : Znth child swapped 0 = Znth root audience 0).
  {
    unfold swapped.
    rewrite Znth_replace_Znth_Same by
      (rewrite Zlength_replace_Znth__sift_transition_exit; exact Hchild_range).
    reflexivity.
  }
  assert (Hswap_other : forall k,
    0 <= k < Zlength audience ->
    k <> root -> k <> child ->
    Znth k swapped 0 = Znth k audience 0).
  {
    intros k Hk Hkr Hkc. unfold swapped.
    rewrite Znth_replace_Znth_Diff by
      (repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    rewrite Znth_replace_Znth_Diff by lia. reflexivity.
  }
  unfold PeopleHeapOrderedExceptAt in Hheap |- *.
  intros k Hk Hparent Hparent_not_child.
  pose proof (heap_parent_bounds__sift_transition_exit k ltac:(lia)) as Hp_bounds.
  assert (Hk_range : 0 <= k < Zlength audience) by lia.
  assert (Hp_range : 0 <= (k - 1) / 2 < Zlength audience) by lia.
  destruct (Z.eq_dec ((k - 1) / 2) root)
    as [Hparent_root | Hparent_not_root].
  - destruct (Z.eq_dec k child) as [Hk_child | Hk_not_child].
    + subst k. rewrite Hswap_child, Hchild_parent, Hswap_root. lia.
    + assert (Hk_not_root : k <> root) by lia.
      rewrite Hparent_root, Hswap_root.
      rewrite Hswap_other by assumption.
      destruct (heap_children_characterization__sift_transition_exit
        root k ltac:(lia) ltac:(lia) Hparent_root) as [-> | ->].
      * apply Hleft. lia.
      * apply Hright. lia.
  - destruct (Z.eq_dec k root) as [Hk_root | Hk_not_root].
    + subst k.
      rewrite Hswap_root.
      rewrite Hswap_other by (try assumption; lia).
      apply Henter; [lia | exact Hparent].
    + assert (Hk_not_child : k <> child).
      { intro Heq. subst k. apply Hparent_not_root. exact Hchild_parent. }
      rewrite Hswap_other by assumption.
      rewrite Hswap_other by (try assumption; lia).
      apply Hheap; assumption.
Qed.
Lemma people_selected_swap_descendant_edge__sift_transition_exit :
  forall audience root0 root hi child descendant,
    0 <= root0 <= root ->
    root <= hi ->
    hi < Zlength audience ->
    PeopleSelectedLargerChild audience root hi child ->
    PeopleHeapOrderedExceptAt audience root0 hi root ->
    (descendant = 2 * child + 1 \/ descendant = 2 * child + 2) ->
    descendant <= hi ->
    Znth descendant
      (replace_Znth child (Znth root audience 0)
        (replace_Znth root (Znth child audience 0) audience)) 0 <=
    Znth ((child - 1) / 2)
      (replace_Znth child (Znth root audience 0)
        (replace_Znth root (Znth child audience 0) audience)) 0.
Proof.
  intros audience root0 root hi child descendant Hroots Hroot_hi Hhi
    Hselected Hheap Hdesc_shape Hdesc_hi.
  assert (Hchild_parent : (child - 1) / 2 = root).
  { eapply people_selected_child_parent__sift_transition_exit; eauto; lia. }
  assert (Hroot_child : root < child).
  {
    unfold PeopleSelectedLargerChild in Hselected.
    destruct Hselected as [[-> | ->] _]; lia.
  }
  assert (Hdesc_parent : (descendant - 1) / 2 = child).
  {
    destruct Hdesc_shape as [-> | ->].
    - replace (2 * child + 1 - 1) with (child * 2) by ring.
      rewrite Z.div_mul by lia. reflexivity.
    - replace (2 * child + 2 - 1) with (child * 2 + 1) by ring.
      pose proof (Z.mod_pos_bound (child * 2 + 1) 2 ltac:(lia)) as Hrem.
      pose proof (Z.div_mod (child * 2 + 1) 2 ltac:(lia)) as Hdiv.
      assert (Z.modulo (child * 2 + 1) 2 = 1) by lia. lia.
  }
  assert (Hroot_range : 0 <= root < Zlength audience) by lia.
  assert (Hchild_range : 0 <= child < Zlength audience) by lia.
  assert (Hdesc_range : 0 <= descendant < Zlength audience) by
    (destruct Hdesc_shape as [-> | ->]; lia).
  pose proof (Hheap descendant ltac:(lia) ltac:(lia) ltac:(lia)) as Hedge.
  rewrite Hdesc_parent in Hedge.
  rewrite Hchild_parent.
  rewrite Znth_replace_Znth_Diff by
    (repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
  rewrite Znth_replace_Znth_Diff by lia.
  rewrite Znth_replace_Znth_Diff by
    (repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
  rewrite Znth_replace_Znth_Same by exact Hroot_range.
  exact Hedge.
Qed.
Lemma people_heap_child_of_parent__sift_transition_exit :
  forall child parent,
    1 <= child ->
    (child - 1) / 2 = parent ->
    child = 2 * parent + 1 \/ child = 2 * parent + 2.
Proof.
  intros child parent Hchild Hparent.
  pose proof (Z.mod_pos_bound (child - 1) 2 ltac:(lia)) as Hmod.
  pose proof (Z.div_mod (child - 1) 2 ltac:(lia)) as Hdecomp.
  rewrite Hparent in Hdecomp.
  assert ((child - 1) mod 2 = 0 \/ (child - 1) mod 2 = 1) by lia.
  destruct H as [H | H]; [left | right]; lia.
Qed.
Lemma people_heap_parents_after_selected_stop__sift_transition_exit :
  forall audience lo hi root selected,
    PeopleSelectedLargerChild audience root hi selected ->
    Znth selected audience 0 <= Znth root audience 0 ->
    PeopleHeapOrderedExceptAt audience lo hi root ->
    PeopleHeapParentsFrom audience lo hi.
Proof.
  intros audience lo hi root selected Hselected Hstop Hordered.
  unfold PeopleHeapParentsFrom.
  intros current Hcurrent Hlo.
  destruct (Z.eq_dec ((current - 1) / 2) root) as [Hparent | Hparent].
  - rewrite Hparent.
    destruct Hselected as [_ [Hselected_hi [Hleft_max Hright_max]]].
    pose proof (people_heap_child_of_parent__sift_transition_exit current root
      ltac:(lia) Hparent) as [Hleft | Hright].
    + subst current.
      eapply Z.le_trans; [apply Hleft_max; lia | exact Hstop].
    + subst current.
      eapply Z.le_trans; [apply Hright_max; lia | exact Hstop].
  - unfold PeopleHeapOrderedExceptAt in Hordered.
    eapply Hordered; eauto.
Qed.
Lemma people_heap_parents_after_leaf_stop__sift_transition_exit :
  forall audience lo hi root,
    2 * root + 1 > hi ->
    PeopleHeapOrderedExceptAt audience lo hi root ->
    PeopleHeapParentsFrom audience lo hi.
Proof.
  intros audience lo hi root Hleaf Hordered.
  unfold PeopleHeapParentsFrom.
  intros current Hcurrent Hlo.
  destruct (Z.eq_dec ((current - 1) / 2) root) as [Hparent | Hparent].
  - pose proof (people_heap_child_of_parent__sift_transition_exit current root
      ltac:(lia) Hparent) as [Hleft | Hright]; lia.
  - unfold PeopleHeapOrderedExceptAt in Hordered.
    eapply Hordered; eauto.
Qed.
Lemma people_sift_swap_preserves_progress__sift_transition_exit :
  forall audience0 order0 audience order root0 root hi n child,
    Zlength audience = n ->
    Zlength order = n ->
    0 <= root0 <= root ->
    root <= hi ->
    hi < n ->
    0 <= child <= hi ->
    Znth root audience 0 < Znth child audience 0 ->
    PeopleSiftProgress audience0 order0 audience order root0 root hi n ->
    PeopleSelectedLargerChild audience root hi child ->
    PeopleSiftProgress audience0 order0
      (replace_Znth child (Znth root audience 0)
        (replace_Znth root (Znth child audience 0) audience))
      (replace_Znth child (Znth root order 0)
        (replace_Znth root (Znth child order 0) order))
      root0 child hi n.
Proof.
  intros audience0 order0 audience order root0 root hi n child
    Ha_len Ho_len Hroots Hroot_hi Hhi Hchild Hrise Hprogress Hselected.
  destruct Hprogress as
    [Hperm [Ha_suffix [Ho_suffix [Hheap Hentry]]]].
  unfold PeopleSiftProgress. repeat split.
  - eapply people_parallel_permutation_swap__sift_transition_exit; eauto; lia.
  - rewrite double_replace_suffix__sift_transition_exit by lia.
    exact Ha_suffix.
  - rewrite double_replace_suffix__sift_transition_exit by lia.
    exact Ho_suffix.
  - eapply people_heap_except_after_selected_swap__sift_transition_exit;
      eauto; try lia.
    intros Hroot_pos Hparent_lo.
    destruct Hentry as [Heq | [Hleft Hright]].
    + subst root.
      pose proof (heap_parent_bounds__sift_transition_exit root0 ltac:(lia)).
      lia.
    + unfold PeopleSelectedLargerChild in Hselected.
      destruct Hselected as [[-> | ->] _].
      * apply Hleft. lia.
      * apply Hright. lia.
  - right. split; intros Hdesc.
    + eapply people_selected_swap_descendant_edge__sift_transition_exit;
        eauto; try lia.
    + eapply people_selected_swap_descendant_edge__sift_transition_exit;
        eauto; try lia.
Qed.
Lemma people_sift_exit_restores_heap__sift_transition_exit :
  forall audience0 order0 audience order root0 root hi n,
    PeopleSiftProgress audience0 order0 audience order root0 root hi n ->
    (2 * root + 1 > hi \/
     exists selected,
       PeopleSelectedLargerChild audience root hi selected /\
       Znth selected audience 0 <= Znth root audience 0) ->
    PeopleHeapParentsFrom audience root0 hi.
Proof.
  intros audience0 order0 audience order root0 root hi n Hprogress Hstop.
  destruct Hprogress as [_ [_ [_ [Hheap _]]]].
  destruct Hstop as [Hleaf | [selected [Hselected Hdominance]]].
  - eapply people_heap_parents_after_leaf_stop__sift_transition_exit; eauto.
  - eapply people_heap_parents_after_selected_stop__sift_transition_exit; eauto.
Qed.
Lemma people_heap_build_step__sort_build :
  forall audience0 order0 audience order audience' order' root n,
    PeopleHeapBuildState audience0 order0 audience order root n ->
    PeoplePermutation audience order audience' order' ->
    PeopleHeapParentsFrom audience' root (n - 1) ->
    PeopleHeapBuildState audience0 order0 audience' order' (root - 1) n.
Proof.
  intros audience0 order0 audience order audience' order' root n
    [Hperm01 Hparents] Hperm12 Hparents'.
  unfold PeopleHeapBuildState.
  split.
  - unfold PeoplePermutation in *.
    eapply Permutation_trans; eauto.
  - replace (root - 1 + 1) with root by lia.
    exact Hparents'.
Qed.
Lemma people_map_fst_combine__sort_extract_final :
  forall (audience order : list Z),
    Zlength audience = Zlength order ->
    map fst (combine audience order) = audience.
Proof.
  intros audience. induction audience as [|a audience IH];
    intros order Hlen.
  - destruct order; reflexivity.
  - destruct order as [|o order].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma people_audience_permutation__sort_extract_final :
  forall audience order audience' order',
    Zlength audience = Zlength order ->
    Zlength audience' = Zlength order' ->
    PeoplePermutation audience order audience' order' ->
    Permutation audience audience'.
Proof.
  intros audience order audience' order' Hlen Hlen' Hparallel.
  unfold PeoplePermutation in Hparallel.
  pose proof (Permutation_map fst Hparallel) as Hperm.
  rewrite !people_map_fst_combine__sort_extract_final in Hperm by assumption.
  exact Hperm.
Qed.
Lemma people_prefix_permutation_from_suffix__sort_extract_final :
  forall (before after : list Z) n cut,
    Zlength before = n ->
    Zlength after = n ->
    0 <= cut <= n ->
    Permutation before after ->
    sublist cut n after = sublist cut n before ->
    Permutation (sublist 0 cut before) (sublist 0 cut after).
Proof.
  intros before after n cut Hbefore Hafter Hcut Hperm Hsuffix.
  assert (Hbefore_split :
    before = sublist 0 cut before ++ sublist cut n before).
  { transitivity (sublist 0 n before).
    - symmetry. apply sublist_self. symmetry. exact Hbefore.
    - apply sublist_split; lia. }
  assert (Hafter_split :
    after = sublist 0 cut after ++ sublist cut n after).
  { transitivity (sublist 0 n after).
    - symmetry. apply sublist_self. symmetry. exact Hafter.
    - apply sublist_split; lia. }
  rewrite Hbefore_split, Hafter_split in Hperm.
  rewrite Hsuffix in Hperm.
  apply Permutation_app_inv_r in Hperm.
  exact Hperm.
Qed.
Lemma people_cross_preserved_after_sift__sort_extract_final :
  forall audience_now audience_after n hi,
    Zlength audience_now = n ->
    Zlength audience_after = n ->
    1 <= hi <= n ->
    Permutation audience_now audience_after ->
    sublist hi n audience_after = sublist hi n audience_now ->
    (forall left right,
      0 <= left < hi -> hi <= right < n ->
      Znth left audience_now 0 <= Znth right audience_now 0) ->
    forall left right,
      0 <= left < hi -> hi <= right < n ->
      Znth left audience_after 0 <= Znth right audience_after 0.
Proof.
  intros audience_now audience_after n hi Hnow Hafter Hhi
    Hperm Hsuffix Hcross left right Hleft Hright.
  pose proof (people_prefix_permutation_from_suffix__sort_extract_final
    audience_now audience_after n hi Hnow Hafter ltac:(lia)
    Hperm Hsuffix) as Hprefixperm.
  assert (Hright_eq : Znth right audience_after 0 =
    Znth right audience_now 0).
  { pose proof (f_equal (fun l => Znth (right - hi) l 0) Hsuffix) as H.
    cbn in H.
    rewrite !Znth_sublist in H by lia.
    replace (right - hi + hi) with right in H by lia. exact H. }
  assert (Hbefore_forall :
    Forall (fun x => x <= Znth right audience_now 0)
      (sublist 0 hi audience_now)).
  { apply (proj2 (Forall_Znth _ 0 _)). intros k Hk.
    rewrite Zlength_sublist0 in Hk by lia.
    rewrite Znth_sublist0 by lia.
    apply Hcross; lia. }
  assert (Hafter_forall :
    Forall (fun x => x <= Znth right audience_now 0)
      (sublist 0 hi audience_after)).
  { eapply Permutation_Forall; eauto. }
  apply (proj1 (Forall_Znth _ 0 _)) with (i := left) in Hafter_forall.
  2: { rewrite Zlength_sublist0 by lia. lia. }
  rewrite Znth_sublist0 in Hafter_forall by lia.
  rewrite Hright_eq. exact Hafter_forall.
Qed.
Lemma people_heap_extract_step__sort_extract_final :
  forall audience0 order0 audience_now order_now
    audience_after order_after n hi,
    Zlength audience_now = n ->
    Zlength order_now = n ->
    Zlength audience_after = n ->
    Zlength order_after = n ->
    1 <= hi <= n ->
    PeoplePermutation audience0 order0 audience_now order_now ->
    PeoplePermutation audience_now order_now audience_after order_after ->
    PeopleHeapParentsFrom audience_after 0 (hi - 1) ->
    sublist hi n audience_after = sublist hi n audience_now ->
    ListLib.increasing (sublist hi n audience_now) ->
    (forall left right,
      0 <= left < hi -> hi <= right < n ->
      Znth left audience_now 0 <= Znth right audience_now 0) ->
    PeopleHeapSortState audience0 order0 audience_after order_after (hi - 1).
Proof.
  intros audience0 order0 audience_now order_now audience_after order_after
    n hi Haudnow Hordnow Haudafter Hordafter Hhi Hperm0 Hperm1 Hheap
    Hsuffix Hinc Hcross.
  unfold PeopleHeapSortState.
  repeat split.
  - unfold PeoplePermutation in *. eapply Permutation_trans; eauto.
  - exact Hheap.
  - replace (hi - 1 + 1) with hi by lia.
    rewrite Haudafter. rewrite Hsuffix. exact Hinc.
  - intros left right Hleft Hright.
    assert (Haudperm : Permutation audience_now audience_after).
    { eapply people_audience_permutation__sort_extract_final.
      - rewrite Haudnow, Hordnow. reflexivity.
      - rewrite Haudafter, Hordafter. reflexivity.
      - exact Hperm1. }
    apply (people_cross_preserved_after_sift__sort_extract_final
      audience_now audience_after n hi Haudnow Haudafter ltac:(lia)
      Haudperm Hsuffix Hcross left right ltac:(lia)).
    lia.
Qed.
Lemma people_heap_sort_final__sort_extract_final :
  forall audience0 order0 audience order n,
    Zlength audience = n ->
    1 <= n ->
    PeopleHeapSortState audience0 order0 audience order 0 ->
    ListLib.increasing audience /\
    PeoplePermutation audience0 order0 audience order.
Proof.
  intros audience0 order0 audience order n Hlen Hn Hstate.
  destruct Hstate as [Hperm [_ [Hinc Hcross]]].
  split; [|exact Hperm].
  apply (proj2 (increasing_iff_chain _)).
  apply (proj2 (mono_chain_iff_index Z.le _)).
  intros i j Hi Hij Hj.
  destruct (Z.eq_dec i 0) as [-> | Hi0].
  - apply Hcross; lia.
  - assert (Hchain : mono_chain Z.le (sublist 1 n audience)).
    { rewrite <- Hlen. apply (proj1 (increasing_iff_chain _)). exact Hinc. }
    apply (proj1 (mono_chain_iff_index Z.le _))
      with (i := i - 1) (j := j - 1) in Hchain; try lia.
    + rewrite !Znth_sublist in Hchain by lia.
      replace (i - 1 + 1) with i in Hchain by lia.
      replace (j - 1 + 1) with j in Hchain by lia.
      exact Hchain.
    + rewrite Zlength_sublist by lia. lia.
Qed.
Lemma people_heap_root_upper__sort_extract_final :
  forall audience hi child,
    0 <= child <= hi ->
    PeopleHeapParentsFrom audience 0 hi ->
    Znth child audience 0 <= Znth 0 audience 0.
Proof.
  intros audience hi child Hchild Hheap.
  assert (Haux : forall fuel current,
    fuel = Z.to_nat current ->
    0 <= current <= hi ->
    Znth current audience 0 <= Znth 0 audience 0).
  {
    intros fuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros current Hfuel Hcurrent.
    destruct (Z.eq_dec current 0) as [-> | Hcurrent_ne].
    - apply Z.le_refl.
    - pose proof (heap_parent_bounds__sift_transition_exit current ltac:(lia))
        as Hparent.
      eapply Z.le_trans.
      + apply Hheap; lia.
      + apply (IH (Z.to_nat ((current - 1) / 2))).
        * apply Nat2Z.inj_lt.
          rewrite Z2Nat.id by lia.
          rewrite Hfuel, Z2Nat.id by lia.
          lia.
        * reflexivity.
        * lia.
  }
  eapply Haux; [reflexivity | exact Hchild].
Qed.
Lemma people_heap_extract_cross__sort_extract_final :
  forall audience0 order0 audience order hi n,
    Zlength audience = n ->
    1 <= hi < n ->
    PeopleHeapSortState audience0 order0 audience order hi ->
    forall left right,
      0 <= left < hi -> hi <= right < n ->
      Znth left
        (replace_Znth hi (Znth 0 audience 0)
          (replace_Znth 0 (Znth hi audience 0) audience)) 0 <=
      Znth right
        (replace_Znth hi (Znth 0 audience 0)
          (replace_Znth 0 (Znth hi audience 0) audience)) 0.
Proof.
  intros audience0 order0 audience order hi n Haudience Hhi Hstate.
  destruct Hstate as [_ [Hheap [_ Hcross]]].
  intros left right Hleft Hright.
  destruct (Z.eq_dec left 0) as [-> | Hleft_ne];
    destruct (Z.eq_dec right hi) as [-> | Hright_ne].
  - rewrite Znth_replace_Znth_Diff by
      (try repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Znth_replace_Znth_Same by
      (rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    apply people_heap_root_upper__sort_extract_final with (hi := hi).
    + lia.
    + exact Hheap.
  - rewrite Znth_replace_Znth_Diff by
      (try repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Znth_replace_Znth_Diff by
      (try repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    apply Hcross; lia.
  - rewrite Znth_replace_Znth_Diff by
      (try repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    rewrite Znth_replace_Znth_Same by
      (rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    apply people_heap_root_upper__sort_extract_final with (hi := hi).
    + lia.
    + exact Hheap.
  - rewrite !Znth_replace_Znth_Diff by
      (try repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    apply Hcross; lia.
Qed.
Lemma people_heap_extract_except__sort_extract_final :
  forall audience0 order0 audience order hi n,
    Zlength audience = n ->
    1 <= hi < n ->
    PeopleHeapSortState audience0 order0 audience order hi ->
    PeopleHeapOrderedExceptAt
      (replace_Znth hi (Znth 0 audience 0)
        (replace_Znth 0 (Znth hi audience 0) audience))
      0 (hi - 1) 0.
Proof.
  intros audience0 order0 audience order hi n Haudience Hhi Hstate.
  destruct Hstate as [_ [Hheap _]].
  unfold PeopleHeapOrderedExceptAt, PeopleHeapParentsFrom in *.
  intros child Hchild Hparent Hparent_ne.
  pose proof (heap_parent_bounds__sift_transition_exit child ltac:(lia))
    as Hparent_bounds.
  assert (Hedge := Hheap child ltac:(lia) ltac:(lia)).
  repeat rewrite Znth_replace_Znth_Diff by
    (try repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
  exact Hedge.
Qed.
Lemma people_heap_extract_suffix__sort_extract_final :
  forall audience0 order0 audience order hi n,
    Zlength audience = n ->
    1 <= hi < n ->
    PeopleHeapSortState audience0 order0 audience order hi ->
    ListLib.increasing
      (sublist hi n
        (replace_Znth hi (Znth 0 audience 0)
          (replace_Znth 0 (Znth hi audience 0) audience))).
Proof.
  intros audience0 order0 audience order hi n Haudience Hhi Hstate.
  destruct Hstate as [_ [_ [Hincreasing Hcross]]].
  apply (proj2 (increasing_iff_chain _)).
  apply (proj2 (mono_chain_iff_index Z.le _)).
  intros i j Hi Hij Hj.
  assert (Hswapped_len :
    Zlength
      (replace_Znth hi (Znth 0 audience 0)
        (replace_Znth 0 (Znth hi audience 0) audience)) = n).
  { repeat rewrite Zlength_replace_Znth__sift_transition_exit.
    exact Haudience. }
  rewrite Zlength_sublist in Hj by lia.
  rewrite !Znth_sublist by lia.
  destruct (Z.eq_dec i 0) as [-> | Hi_ne].
  - rewrite Znth_replace_Znth_Same by
      (rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    rewrite Znth_replace_Znth_Diff by
      (try repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    rewrite Znth_replace_Znth_Diff by lia.
    apply Hcross; lia.
  - rewrite !Znth_replace_Znth_Diff by
      (try repeat rewrite Zlength_replace_Znth__sift_transition_exit; lia).
    assert (Hchain : mono_chain Z.le (sublist (hi + 1) n audience)).
    { rewrite <- Haudience.
      apply (proj1 (increasing_iff_chain _)). exact Hincreasing. }
    apply (proj1 (mono_chain_iff_index Z.le _))
      with (i := i - 1) (j := j - 1) in Hchain; try lia.
    + rewrite !Znth_sublist in Hchain by lia.
      replace (i - 1 + (hi + 1)) with (i + hi) in Hchain by lia.
      replace (j - 1 + (hi + 1)) with (j + hi) in Hchain by lia.
      exact Hchain.
    + rewrite Zlength_sublist by lia. lia.
Qed.
Lemma all_team_neg_inf_replace_extend__solver_setup :
  forall values m,
    0 <= m < Zlength values ->
    AllTeamNegInf (sublist 0 m values) ->
    AllTeamNegInf
      (sublist 0 (m + 1) (replace_Znth m TeamNegInf values)).
Proof.
  intros values m Hm Hall.
  rewrite (sublist_split 0 (m + 1) m (replace_Znth m TeamNegInf values)) by
      (rewrite ?ListLib.Zlength_replace_Znth; lia).
  assert (Hprefix :
    sublist 0 m (replace_Znth m TeamNegInf values) = sublist 0 m values).
  {
    apply (proj2 (list_eq_ext _ _ TeamNegInf)). split.
    - rewrite !Zlength_sublist by
        (rewrite ?ListLib.Zlength_replace_Znth; lia). reflexivity.
    - intros k Hk.
      rewrite Zlength_sublist in Hk by
          (rewrite ?ListLib.Zlength_replace_Znth; lia).
      rewrite !Znth_sublist by
        (rewrite ?ListLib.Zlength_replace_Znth; lia).
      rewrite Znth_replace_Znth_Diff by lia. reflexivity.
  }
  rewrite Hprefix.
  rewrite (sublist_single TeamNegInf m (replace_Znth m TeamNegInf values)) by
      (rewrite ListLib.Zlength_replace_Znth; lia).
  rewrite (Znth_replace_Znth_Same TeamNegInf values m TeamNegInf) by lia.
  unfold AllTeamNegInf in *. apply Forall_app. split; [exact Hall |].
  constructor; [reflexivity | constructor].
Qed.
Lemma all_team_neg_inf_Znth__solver_setup :
  forall values prefix i,
    0 <= i < prefix ->
    prefix <= Zlength values ->
    AllTeamNegInf (sublist 0 prefix values) ->
    Znth i values TeamNegInf = TeamNegInf.
Proof.
  intros values prefix i Hi Hprefix Hall.
  unfold AllTeamNegInf in Hall.
  pose proof
    (proj1 (Forall_nth (fun value : Z => value = TeamNegInf)
      (sublist 0 prefix values)) Hall (Z.to_nat i) TeamNegInf) as Hvalue.
  specialize (Hvalue ltac:(
    assert (HltZ : i < Zlength (sublist 0 prefix values)) by
      (rewrite Zlength_sublist by lia; lia);
    rewrite Zlength_correct in HltZ;
    apply Z2Nat.inj_lt in HltZ; try lia; exact HltZ)).
  change (Znth i (sublist 0 prefix values) TeamNegInf = TeamNegInf) in Hvalue.
  rewrite Znth_sublist in Hvalue by lia.
  replace (i + 0) with i in Hvalue by lia. exact Hvalue.
Qed.
Lemma bounded_team_prefix_choice_zero__solver_setup :
  forall audience skill sorted_order positions audience_limit mask score,
    0 <= positions ->
    BoundedTeamPrefixChoice audience skill sorted_order
      positions audience_limit 0 mask score ->
    mask = 0 /\ score = 0.
Proof.
  intros audience skill sorted_order positions audience_limit mask score
    Hpositions Hchoice.
  unfold BoundedTeamPrefixChoice in Hchoice.
  destruct Hchoice as
    [Hmask [assignments [audience_people
      [[Hmatch Hassignment_bounds]
       [Hnodup [Hprocessed [Hlength Hscore]]]]]]].
  assert (Hassignments : assignments = []).
  {
    destruct assignments as [|[role person] rest]; [reflexivity |].
    simpl in Hprocessed. inversion Hprocessed as [|x xs Hperson Hrest].
    unfold ProcessedPerson in Hperson.
    destruct Hperson as [step [Hstep _]]. lia.
  }
  subst assignments.
  assert (Haudience : audience_people = []).
  {
    destruct audience_people as [|person rest]; [reflexivity |].
    simpl in Hprocessed. inversion Hprocessed as [|x xs Hperson Hrest].
    unfold ProcessedPerson in Hperson.
    destruct Hperson as [step [Hstep _]]. lia.
  }
  subst audience_people. split.
  - unfold AssignmentsMatchMask in Hmatch. destruct Hmatch as [_ Hbits].
    apply Z.bits_inj_0. intro bit.
    destruct (Z_lt_ge_dec bit 0) as [Hnegative | Hnonnegative].
    + apply Z.testbit_neg_r. exact Hnegative.
    + destruct (Z_lt_ge_dec bit positions) as [Hlow | Hhigh].
      * specialize (Hbits bit ltac:(lia)). simpl in Hbits.
        destruct (Z.testbit mask bit) eqn:Hbit; [|reflexivity].
        exfalso. destruct (proj1 Hbits eq_refl) as [person Hfalse].
        exact Hfalse.
      * destruct (Z.eq_dec mask 0) as [-> | Hmask_nonzero].
        -- apply Z.bits_0.
        -- apply Z.bits_above_log2; [lia |].
           assert (Z.log2 mask < positions) as Hlog.
           { apply (proj1 (Z.log2_lt_pow2 mask positions ltac:(lia))); lia. }
           lia.
  - simpl in Hscore. lia.
Qed.
Lemma bounded_team_dp_base_zero__solver_setup :
  forall audience skill sorted_order positions audience_limit values prefix,
    0 <= positions ->
    0 <= audience_limit ->
    2 ^ positions <= prefix ->
    prefix <= Zlength values ->
    AllTeamNegInf (sublist 0 prefix values) ->
    BoundedTeamDPTable audience skill sorted_order positions audience_limit 0
      (replace_Znth 0 0 values).
Proof.
  intros audience skill sorted_order positions audience_limit values prefix
    Hpositions Haudience_limit Hpower Hprefix Hall mask Hmask.
  unfold BoundedTeamDPCell.
  destruct (Z.eq_dec mask 0) as [-> | Hmask_nonzero].
  - rewrite (Znth_replace_Znth_Same TeamNegInf values 0 0) by
      (pose proof (Z.pow_pos_nonneg 2 positions ltac:(lia) Hpositions); lia).
    left. unfold max_value_of_subset, max_object_of_subset.
    exists 0. split.
    + split.
      * unfold BoundedTeamPrefixChoice.
        split; [exact Hmask |]. exists [], []. split.
        -- split.
           ++ unfold AssignmentsMatchMask. split; [constructor |].
              intros role Hrole. split; intro Hfalse.
              ** rewrite Z.bits_0 in Hfalse. discriminate.
              ** destruct Hfalse as [person Hfalse]. inversion Hfalse.
           ++ constructor.
        -- split; [constructor |]. split; [constructor |]. split.
           ++ simpl. rewrite Z.min_r by lia. reflexivity.
           ++ reflexivity.
      * intros candidate Hcandidate.
        destruct (bounded_team_prefix_choice_zero__solver_setup
          audience skill sorted_order positions audience_limit 0 candidate
          Hpositions Hcandidate) as [_ ->]. lia.
    + reflexivity.
  - right. split.
    + rewrite Znth_replace_Znth_Diff by lia.
      exact (all_team_neg_inf_Znth__solver_setup values prefix mask
        ltac:(lia) Hprefix Hall).
    + intros score Hchoice.
      destruct (bounded_team_prefix_choice_zero__solver_setup
        audience skill sorted_order positions audience_limit mask score
        Hpositions Hchoice) as [Hmask_zero _]. contradiction.
Qed.
Lemma Zlength_combine_eq__solver_setup :
  forall {A B : Type} (xs : list A) (ys : list B),
    Zlength xs = Zlength ys ->
    Zlength (combine xs ys) = Zlength xs.
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys Hlen.
  - reflexivity.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. rewrite !Zlength_cons. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma Znth_combine__solver_setup :
  forall {A B : Type} (xs : list A) (ys : list B) i da db,
    Zlength xs = Zlength ys ->
    0 <= i < Zlength xs ->
    Znth i (combine xs ys) (da, db) = (Znth i xs da, Znth i ys db).
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys i da db Hlen Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + destruct (Z.eq_dec i 0) as [-> | Hne].
      * reflexivity.
      * simpl. rewrite !Znth_cons by lia. apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- rewrite Zlength_cons in Hi. lia.
Qed.
Lemma In_Znth_index__solver_setup : forall {A : Type} (xs : list A) x d,
  In x xs -> exists i, 0 <= i < Zlength xs /\ Znth i xs d = x.
Proof.
  intros A xs. induction xs as [|a xs IH]; intros x d Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [-> | Hin].
    + exists 0. split.
      * rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
      * reflexivity.
    + destruct (IH x d Hin) as [i [Hi Hnth]].
      exists (i + 1). split.
      * rewrite Zlength_cons. lia.
      * rewrite Znth_cons by lia. replace (i + 1 - 1) with i by lia.
        exact Hnth.
Qed.
Lemma people_permutation_lookup__solver_setup :
  forall audience order audience' order' n q,
    Zlength audience = n ->
    Zlength order = n ->
    Zlength audience' = n ->
    Zlength order' = n ->
    (forall i, 0 <= i < n -> Znth i order 0 = i) ->
    PeoplePermutation audience order audience' order' ->
    0 <= q < n ->
    0 <= Znth q order' 0 < n /\
    Znth q audience' 0 = Znth (Znth q order' 0) audience 0.
Proof.
  intros audience order audience' order' n q Ha Ho Ha' Ho' Hidentity
    Hperm Hq.
  assert (Hpair :
    In (Znth q audience' 0, Znth q order' 0) (combine audience' order')).
  {
    rewrite <- (Znth_combine__solver_setup audience' order' q 0 0) by lia.
    apply Znth_In_Zlength with (default := (0, 0)) (i := q).
    rewrite Zlength_combine_eq__solver_setup by lia. lia.
  }
  unfold PeoplePermutation in Hperm.
  assert (Hpair0 :
    In (Znth q audience' 0, Znth q order' 0) (combine audience order)).
  { eapply Permutation_in; [exact (Permutation_sym Hperm) | exact Hpair]. }
  destruct (In_Znth_index__solver_setup
    (combine audience order) (Znth q audience' 0, Znth q order' 0) (0, 0)
    Hpair0) as [i [Hi Hnth]].
  rewrite Zlength_combine_eq__solver_setup in Hi by lia.
  rewrite Znth_combine__solver_setup in Hnth by lia.
  pose proof (f_equal fst Hnth) as Haudience.
  pose proof (f_equal snd Hnth) as Horder.
  simpl in Haudience, Horder. rewrite Hidentity in Horder by lia.
  rewrite <- Horder. split; [lia | symmetry; exact Haudience].
Qed.
Lemma sorted_people_state_intro__solver_setup :
  forall audience order audience' order' n,
    Zlength audience = n ->
    Zlength order = n ->
    Zlength audience' = n ->
    Zlength order' = n ->
    (forall i, 0 <= i < n -> Znth i order 0 = i) ->
    PeoplePermutation audience order audience' order' ->
    ListLib.increasing audience' ->
    SortedPeopleState audience order audience' order'.
Proof.
  intros audience order audience' order' n Ha Ho Ha' Ho' Hidentity
    Hperm Hincreasing.
  unfold SortedPeopleState. split; [lia |]. split; [lia |].
  split; [exact Hperm |]. split; [exact Hincreasing |]. intros q Hq.
  rewrite Ha.
  apply (people_permutation_lookup__solver_setup
    audience order audience' order' n q Ha Ho Ha' Ho' Hidentity Hperm).
  lia.
Qed.
Lemma Zlength_concat_uniform__solver_setup :
  forall (rows : list (list Z)) (width : Z),
    Forall (fun row => Zlength row = width) rows ->
    Zlength (concat rows) = Zlength rows * width.
Proof.
  intros rows width Hrows.
  induction Hrows as [|row rows Hrow Hrows IH]; simpl.
  - reflexivity.
  - rewrite Zlength_app, Zlength_cons, Hrow, IH. lia.
Qed.
Lemma people_order_bounds__solver_setup :
  forall audience order audience' order' n,
    Zlength audience = n ->
    Zlength order = n ->
    Zlength audience' = n ->
    Zlength order' = n ->
    (forall i, 0 <= i < n -> Znth i order 0 = i) ->
    PeoplePermutation audience order audience' order' ->
    forall q, 0 <= q < Zlength audience' ->
      0 <= Znth q order' 0 < Zlength audience'.
Proof.
  intros audience order audience' order' n Ha Ho Ha' Ho' Hidentity Hperm q Hq.
  destruct (people_permutation_lookup__solver_setup audience order audience'
    order' n q Ha Ho Ha' Ho' Hidentity Hperm ltac:(lia)) as [Hbounds _].
  lia.
Qed.
Lemma people_audience_bounds__solver_setup :
  forall audience order audience' order' n,
    Zlength audience = n ->
    Zlength order = n ->
    Zlength audience' = n ->
    Zlength order' = n ->
    (forall i, 0 <= i < n -> Znth i order 0 = i) ->
    PeoplePermutation audience order audience' order' ->
    (forall i, 0 <= i < n -> 1 <= Znth i audience 0 <= 1000000000) ->
    forall q, 0 <= q < Zlength audience' ->
      1 <= Znth q audience' 0 <= 1000000000.
Proof.
  intros audience order audience' order' n Ha Ho Ha' Ho' Hidentity Hperm
    Haudience q Hq.
  destruct (people_permutation_lookup__solver_setup audience order audience'
    order' n q Ha Ho Ha' Ho' Hidentity Hperm ltac:(lia))
    as [Hbounds Hvalue].
  rewrite Hvalue. apply Haudience. exact Hbounds.
Qed.
Lemma skill_concat_length_from_pre__solver_setup :
  forall audience skill audience_limit n positions default,
    2 <= n ->
    Pre audience_limit audience skill ->
    n = Zlength audience ->
    positions = Zlength (Znth 0 skill default) ->
    Zlength (concat skill) = n * positions.
Proof.
  intros audience skill audience_limit n positions default
    Hn [Hskill [width [Hspace [Hskill' Hrows]]]]
    Haudience Hpositions.
  assert (Hskill_len : Zlength skill = n) by lia.
  assert (Hrow0 : Zlength (Znth 0 skill default) = width).
  {
    apply (proj1 (Forall_Znth _ default _)) with (i := 0) in Hrows.
    - exact Hrows.
    - rewrite Hskill_len. lia.
  }
  assert (Hwidth_eq : width = positions) by lia.
  rewrite (Zlength_concat_uniform__solver_setup skill width Hrows). lia.
Qed.
Lemma bounded_team_dp_zero_bounds__solver_setup :
  forall values positions prefix,
    0 <= positions ->
    2 ^ positions <= prefix ->
    prefix <= Zlength values ->
    AllTeamNegInf (sublist 0 prefix values) ->
    forall q, 0 <= q < 2 ^ positions ->
      TeamNegInf <= Znth q (replace_Znth 0 0 values) 0 <= 100000000000000.
Proof.
  intros values positions prefix Hpositions Hpower Hprefix Hall q Hq.
  destruct (Z.eq_dec q 0) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by lia. unfold TeamNegInf. lia.
  - rewrite Znth_replace_Znth_Diff by lia.
    rewrite (Znth_indep values q 0 TeamNegInf) by lia.
    rewrite (all_team_neg_inf_Znth__solver_setup values prefix q)
      by (try assumption; lia).
    unfold TeamNegInf. lia.
Qed.
Lemma all_team_neg_inf_Znth__solver_row_start :
  forall values hi i default,
    0 <= i < hi ->
    hi <= Zlength values ->
    AllTeamNegInf (sublist 0 hi values) ->
    Znth i values default = TeamNegInf.
Proof.
  intros values hi i default Hi Hhi Hall.
  unfold AllTeamNegInf in Hall.
  apply (proj1 (Forall_Znth _ default _)) with (i := i) in Hall.
  - rewrite Znth_sublist0 in Hall by lia.
    exact Hall.
  - rewrite Zlength_sublist0 by lia.
    lia.
Qed.
Lemma team_next_row_empty__solver_row_start :
  forall sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values hi,
    0 <= positions ->
    2 ^ positions <= hi ->
    hi <= Zlength next_values ->
    AllTeamNegInf (sublist 0 hi next_values) ->
    TeamNextRowProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values 0.
Proof.
  intros sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values hi Hpositions Hpow Hhi Hall.
  unfold TeamNextRowProgress.
  intros target Htarget.
  right. split.
  - apply (all_team_neg_inf_Znth__solver_row_start
      next_values hi target TeamNegInf).
    + lia.
    + exact Hhi.
    + exact Hall.
  - intros score Hcandidate.
    unfold TeamTransitionCandidate in Hcandidate.
    destruct Hcandidate as
      (source & source_score & Hsource & Hscore & Hfinite & Htransition).
    lia.
Qed.
Lemma Forall_Znth_local__solver_role_init :
  forall {A : Type} (P : A -> Prop) (d : A) (l : list A),
    Forall P l ->
    forall i, 0 <= i < Zlength l -> P (Znth i l d).
Proof.
  intros A P d l HForall.
  induction HForall as [|x xs Hx Hxs IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite Znth0_cons. exact Hx.
    + rewrite Znth_cons by lia. apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Znth_concat_uniform__solver_role_init :
  forall (rows : list (list Z)) m (d : list Z) i j,
    0 <= i < Zlength rows ->
    (forall r, 0 <= r < Zlength rows -> Zlength (Znth r rows d) = m) ->
    0 <= j < m ->
    Znth (i * m + j) (concat rows) 0 = Znth j (Znth i rows d) 0.
Proof.
  induction rows as [|row rows IH]; intros m d i j Hi Hlen Hj.
  - rewrite Zlength_nil in Hi. lia.
  - assert (Hrow : Zlength row = m).
    { specialize (Hlen 0). rewrite Znth0_cons in Hlen. apply Hlen.
      rewrite Zlength_cons in Hi |- *. lia. }
    destruct (Z.eq_dec i 0) as [-> | Hine].
    + simpl concat. rewrite Znth0_cons.
      rewrite app_Znth1; [reflexivity |]. rewrite Hrow. lia.
    + simpl concat. rewrite app_Znth2 by (rewrite Hrow; nia).
      replace (i * m + j - Zlength row) with ((i - 1) * m + j)
        by (rewrite Hrow; ring).
      rewrite Znth_cons by lia.
      apply IH.
      * rewrite Zlength_cons in Hi. lia.
      * intros r Hr. specialize (Hlen (r + 1)).
        rewrite Znth_cons in Hlen by lia.
        replace (r + 1 - 1) with r in Hlen by lia. apply Hlen.
        rewrite Zlength_cons. lia.
      * exact Hj.
Qed.
Lemma fold_map_upper__solver_role_init :
  forall {A : Type} (f : A -> Z) (values : list A) bound,
    0 <= bound ->
    (forall x, In x values -> 0 <= f x <= bound) ->
    fold_right Z.add 0 (map f values) <= Zlength values * bound.
Proof.
  intros A f values bound Hbound Hvalues.
  induction values as [|x xs IH].
  - simpl. lia.
  - simpl. rewrite Zlength_cons.
    pose proof (Hvalues x ltac:(simpl; auto)) as Hx.
    replace (Z.succ (Zlength xs) * bound)
      with (bound + Zlength xs * bound) by (unfold Z.succ; ring).
    apply Z.add_le_mono.
    + exact (proj2 Hx).
    + apply IH. intros y Hy. apply Hvalues. simpl. auto.
Qed.
Lemma bounded_choice_score_upper__solver_role_init :
  forall audience skill sorted_order positions audience_limit processed mask
    score n,
    1 <= audience_limit ->
    0 <= processed <= n ->
    Zlength audience = n ->
    Zlength skill = n ->
    Zlength sorted_order = n ->
    (forall r, 0 <= r < n -> Zlength (Znth r skill []) = positions) ->
    (forall person, ProcessedPerson sorted_order processed person ->
      0 <= Znth person audience 0 <= 1000000000) ->
    (forall idx, 0 <= idx < n * positions ->
      0 <= Znth idx (concat skill) 0 <= 1000000000) ->
    (forall q, 0 <= q < n -> 0 <= Znth q sorted_order 0 < n) ->
    BoundedTeamPrefixChoice audience skill sorted_order positions audience_limit
      processed mask score ->
    score <= processed * 1000000000.
Proof.
  intros audience skill sorted_order positions audience_limit processed mask
    score n Hlimit Hprocessed Haudlen Hskilllen Horderlen Hrows Haud Hflat
    Horder Hchoice.
  destruct Hchoice as
    [Hmask [assignments [audience_people
      [Hmatch [Hnodup [Hselected [Haudience_len Hscore]]]]]]].
  destruct Hmatch as [Hmask_match Hrole_bounds].
  assert (Hroles :
    fold_right Z.add 0
      (map (fun assignment =>
        Znth (fst assignment) (Znth (snd assignment) skill []) 0)
        assignments) <= Zlength assignments * 1000000000).
  {
    apply fold_map_upper__solver_role_init; [lia |].
    intros [role person] Hin. simpl.
    assert (Hrole : 0 <= role < positions).
    { rewrite Forall_forall in Hrole_bounds.
      exact (Hrole_bounds (role, person) Hin). }
    assert (Hperson_selected : ProcessedPerson sorted_order processed person).
    { rewrite Forall_forall in Hselected.
      apply Hselected. apply in_or_app. left.
      apply in_map with (f := snd) in Hin. exact Hin. }
    destruct Hperson_selected as [step [Hstep Hperson]].
    assert (Hidx : 0 <= Zlength sorted_order - 1 - step < n) by lia.
    pose proof (Horder (Zlength sorted_order - 1 - step) Hidx)
      as Hperson_bounds.
    rewrite <- Hperson in Hperson_bounds.
    assert (Hflatidx : 0 <= person * positions + role < n * positions)
      by nia.
    pose proof (Hflat (person * positions + role) Hflatidx) as Hvalue.
    assert (Hnested :
      Znth role (Znth person skill []) 0 =
      Znth (person * positions + role) (concat skill) 0).
    { symmetry. apply Znth_concat_uniform__solver_role_init.
      - rewrite Hskilllen. exact Hperson_bounds.
      - intros r Hr. apply Hrows. rewrite Hskilllen in Hr. exact Hr.
      - exact Hrole. }
    rewrite Hnested. exact Hvalue.
  }
  assert (Haudience :
    fold_right Z.add 0
      (map (fun person => Znth person audience 0) audience_people) <=
    Zlength audience_people * 1000000000).
  {
    apply fold_map_upper__solver_role_init; [lia |].
    intros person Hin.
    assert (Hperson_selected : ProcessedPerson sorted_order processed person).
    { rewrite Forall_forall in Hselected.
      apply Hselected. apply in_or_app. right. exact Hin. }
    apply Haud. exact Hperson_selected.
  }
  assert (Hcount : Zlength assignments + Zlength audience_people <= processed).
  {
    destruct (Z_le_dec audience_limit
      (processed - Zlength assignments)) as [Hle | Hgt].
    - rewrite Z.min_l in Haudience_len by lia. lia.
    - rewrite Z.min_r in Haudience_len by lia. lia.
  }
  rewrite Hscore. nia.
Qed.
Lemma bounded_dp_live_value_upper__solver_role_init :
  forall n positions audience_limit audience default skill sorted_order processed
    values source,
    2 <= n ->
    1 <= positions <= 7 ->
    1 <= audience_limit ->
    n = Zlength audience ->
    positions = Zlength (Znth 0 skill default) ->
    Zlength sorted_order = n ->
    0 <= processed < n ->
    0 <= source < 2 ^ positions ->
    Pre audience_limit audience skill ->
    (forall person, ProcessedPerson sorted_order processed person ->
      0 <= Znth person audience 0 <= 1000000000) ->
    (forall q, 0 <= q < n -> 0 <= Znth q sorted_order 0 < n) ->
    (forall idx, 0 <= idx < n * positions ->
      0 <= Znth idx (concat skill) 0 <= 1000000000) ->
    BoundedTeamDPTable audience skill sorted_order positions audience_limit
      processed values ->
    Znth source values TeamNegInf <> TeamNegInf ->
    Znth source values TeamNegInf <= processed * 1000000000.
Proof.
  intros n positions audience_limit audience default skill sorted_order processed
    values source Hn Hpositions Hlimit Haudlen Hrow0 Horderlen Hprocessed
    Hsource Hpre Haud Horder Hflat Htable Hlive.
  unfold Pre in Hpre.
  destruct Hpre as
    [Hskill_aud [width [Hspace [Hskill_aud' Hrows]]]].
  assert (Hskilllen : Zlength skill = n) by lia.
  assert (Hfirst : Zlength (Znth 0 skill default) = width).
  { apply (Forall_Znth_local__solver_role_init _ default skill Hrows).
    rewrite Hskilllen. lia. }
  assert (Hwidth_eq : width = positions) by lia.
  assert (Hrow_lengths : forall r,
    0 <= r < n -> Zlength (Znth r skill []) = positions).
  { intros r Hr.
    pose proof (Forall_Znth_local__solver_role_init
      _ [] skill Hrows r ltac:(rewrite Hskilllen; exact Hr)) as Hlen.
    rewrite Hlen. exact Hwidth_eq. }
  specialize (Htable source Hsource).
  unfold BoundedTeamDPCell in Htable.
  destruct Htable as [Hmax | [Heq Hnone]]; [|contradiction].
  unfold max_value_of_subset, max_object_of_subset in Hmax.
  destruct Hmax as [best [[Hchoice Hupper] Hvalue]].
  rewrite <- Hvalue.
  eapply (bounded_choice_score_upper__solver_role_init audience skill
    sorted_order positions audience_limit processed source best n).
  - exact Hlimit.
  - lia.
  - lia.
  - exact Hskilllen.
  - exact Horderlen.
  - exact Hrow_lengths.
  - exact Haud.
  - exact Hflat.
  - exact Horder.
  - exact Hchoice.
Qed.
Lemma bounded_team_role_update_init__solver_role_init :
  forall sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source used chosen,
    0 <= source < 2 ^ positions ->
    2 ^ positions <= Zlength next_values ->
    BitCount source used ->
    Znth source old_values TeamNegInf <> TeamNegInf ->
    BoundedTeamNextRowProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values source ->
    Znth source next_values TeamNegInf <= chosen ->
    ((processed - used < audience_limit /\
      Znth source old_values TeamNegInf <= chosen /\
      Znth source old_values TeamNegInf +
        Znth (Zlength sorted_audience - 1 - processed)
          sorted_audience 0 <= chosen /\
      (chosen = Znth source old_values TeamNegInf \/
       chosen = Znth source old_values TeamNegInf +
         Znth (Zlength sorted_audience - 1 - processed)
           sorted_audience 0)) \/
     (processed - used >= audience_limit /\
      chosen = Znth source old_values TeamNegInf)) ->
    BoundedTeamRoleUpdateProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values
      (replace_Znth source chosen next_values) source 0.
Proof.
  intros sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source used chosen Hsource Hnext_len Hcount
    Hsource_live Hprogress Hnext_le Hchoice.
  assert (Hcurrent_target : forall target score,
    TeamCurrentSourceCandidate sorted_audience sorted_order skill positions
      audience_limit processed old_values source 0 target score ->
    target = source).
  {
    intros target score Hcurrent.
    unfold TeamCurrentSourceCandidate in Hcurrent; cbn in Hcurrent.
    destruct Hcurrent as [_ [[Htarget _] |
      [[used' [_ [_ [Htarget _]]]] |
       [role [[Hrole0 Hrole1] _]]]]].
    - exact Htarget.
    - exact Htarget.
    - lia.
  }
  assert (Hcurrent_chosen :
    TeamCurrentSourceCandidate sorted_audience sorted_order skill positions
      audience_limit processed old_values source 0 source chosen).
  {
    unfold TeamCurrentSourceCandidate; cbn.
    split; [exact Hsource_live |].
    destruct Hchoice as
      [[Helig [Hsource_le [Haudience_le [Hchosen | Hchosen]]]] |
       [Hinelig Hchosen]].
    - left. split; [reflexivity | exact Hchosen].
    - right; left. exists used. repeat split; try assumption; reflexivity.
    - left. split; [reflexivity | exact Hchosen].
  }
  assert (Hcurrent_upper : forall score,
    TeamCurrentSourceCandidate sorted_audience sorted_order skill positions
      audience_limit processed old_values source 0 source score ->
    score <= chosen).
  {
    intros score Hcurrent.
    unfold TeamCurrentSourceCandidate in Hcurrent; cbn in Hcurrent.
    destruct Hcurrent as [_ [[_ Hscore] |
      [[used' [Hcount' [Helig' [_ Hscore]]]] |
       [role [[Hrole0 Hrole1] _]]]]].
    - subst score.
      destruct Hchoice as
        [[_ [Hsource_le _]] | [_ Hchosen]].
      * exact Hsource_le.
      * rewrite Hchosen. apply Z.le_refl.
    - unfold BitCount in Hcount, Hcount'.
      assert (used' = used) by lia. subst used'. subst score.
      destruct Hchoice as
        [[_ [_ [Haudience_le _]]] | [Hinelig _]].
      * exact Haudience_le.
      * lia.
    - lia.
  }
  unfold BoundedTeamRoleUpdateProgress.
  intros target Htarget.
  specialize (Hprogress target Htarget).
  destruct (Z.eq_dec target source) as [Hsame | Hdiff].
  - subst target.
    rewrite Znth_replace_Znth_Same by lia.
    left.
    unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hprogress as
      [[previous [[Hprevious Hprevious_upper] Hprevious_value]] |
       [Hprevious_empty Hno_previous]].
    + exists chosen. split; [|reflexivity]. split.
      * right. exact Hcurrent_chosen.
      * intros score [Hscore | Hscore].
        -- specialize (Hprevious_upper score Hscore).
           rewrite Hprevious_value in Hprevious_upper.
           lia.
        -- exact (Hcurrent_upper score Hscore).
    + exists chosen. split; [|reflexivity]. split.
      * right. exact Hcurrent_chosen.
      * intros score [Hscore | Hscore].
        -- exfalso. exact (Hno_previous score Hscore).
        -- exact (Hcurrent_upper score Hscore).
  - rewrite Znth_replace_Znth_Diff by lia.
    destruct Hprogress as
      [[previous [[Hprevious Hprevious_upper] Hprevious_value]] |
       [Hprevious_empty Hno_previous]].
    + left.
      unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
      exists previous. split; [|exact Hprevious_value]. split.
      * left. exact Hprevious.
      * intros score [Hscore | Hscore].
        -- exact (Hprevious_upper score Hscore).
        -- apply Hcurrent_target in Hscore. contradiction.
    + right. split; [exact Hprevious_empty |].
      intros score [Hscore | Hscore].
      * exact (Hno_previous score Hscore).
      * apply Hcurrent_target in Hscore. contradiction.
Qed.
Lemma replace_Znth_overwrite__solver_role_init :
  forall {A : Type} (i : Z) (x y : A) l,
    replace_Znth i x (replace_Znth i y l) = replace_Znth i x l.
Proof.
  intros A i x y l. unfold replace_Znth.
  set (n := Z.to_nat i). clearbody n. clear i.
  revert n. induction l as [|a l IH]; intros [|n]; simpl; auto.
  rewrite IH. reflexivity.
Qed.
Lemma bounded_team_role_update_init_skip__solver_role_init :
  forall sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source used,
    0 <= source < 2 ^ positions ->
    BitCount source used ->
    TeamNegInf <= Znth source old_values TeamNegInf ->
    Znth source old_values TeamNegInf <> TeamNegInf ->
    BoundedTeamNextRowProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values source ->
    ((processed - used < audience_limit /\
      Znth source old_values TeamNegInf <=
        Znth source next_values TeamNegInf /\
      Znth source old_values TeamNegInf +
        Znth (Zlength sorted_audience - 1 - processed)
          sorted_audience 0 <= Znth source next_values TeamNegInf) \/
     (processed - used >= audience_limit /\
      Znth source old_values TeamNegInf <=
        Znth source next_values TeamNegInf)) ->
    BoundedTeamRoleUpdateProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values source 0.
Proof.
  intros sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source used Hsource Hcount Hsource_lower
    Hsource_live Hprogress Hchoice.
  assert (Hcurrent_target : forall target score,
    TeamCurrentSourceCandidate sorted_audience sorted_order skill positions
      audience_limit processed old_values source 0 target score ->
    target = source).
  {
    intros target score Hcurrent.
    unfold TeamCurrentSourceCandidate in Hcurrent; cbn in Hcurrent.
    destruct Hcurrent as [_ [[Htarget _] |
      [[used' [_ [_ [Htarget _]]]] |
       [role [[Hrole0 Hrole1] _]]]]].
    - exact Htarget.
    - exact Htarget.
    - lia.
  }
  assert (Hcurrent_upper : forall score,
    TeamCurrentSourceCandidate sorted_audience sorted_order skill positions
      audience_limit processed old_values source 0 source score ->
    score <= Znth source next_values TeamNegInf).
  {
    intros score Hcurrent.
    unfold TeamCurrentSourceCandidate in Hcurrent; cbn in Hcurrent.
    destruct Hcurrent as [_ [[_ Hscore] |
      [[used' [Hcount' [Helig' [_ Hscore]]]] |
       [role [[Hrole0 Hrole1] _]]]]].
    - subst score. destruct Hchoice as [[_ [Hle _]] | [_ Hle]]; exact Hle.
    - unfold BitCount in Hcount, Hcount'.
      assert (used' = used) by lia. subst used'. subst score.
      destruct Hchoice as [[_ [_ Hle]] | [Hinelig _]]; [exact Hle | lia].
    - lia.
  }
  unfold BoundedTeamRoleUpdateProgress.
  intros target Htarget.
  specialize (Hprogress target Htarget).
  destruct (Z.eq_dec target source) as [Hsame | Hdiff].
  - subst target.
    destruct Hprogress as
      [[previous [[Hprevious Hprevious_upper] Hprevious_value]] |
       [Hprevious_empty Hno_previous]].
    + left. unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
      exists previous. split; [|exact Hprevious_value]. split.
      * left. exact Hprevious.
      * intros score [Hscore | Hscore].
        -- exact (Hprevious_upper score Hscore).
        -- rewrite Hprevious_value. exact (Hcurrent_upper score Hscore).
    + exfalso. lia.
  - destruct Hprogress as
      [[previous [[Hprevious Hprevious_upper] Hprevious_value]] |
       [Hprevious_empty Hno_previous]].
    + left. unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
      exists previous. split; [|exact Hprevious_value]. split.
      * left. exact Hprevious.
      * intros score [Hscore | Hscore].
        -- exact (Hprevious_upper score Hscore).
        -- apply Hcurrent_target in Hscore. contradiction.
    + right. split; [exact Hprevious_empty |].
      intros score [Hscore | Hscore].
      * exact (Hno_previous score Hscore).
      * apply Hcurrent_target in Hscore. contradiction.
Qed.
Lemma flattened_role_index_bounds__solver_role_index :
  forall person positions role people,
    0 <= person < people ->
    0 <= role < positions ->
    1 <= positions ->
    0 <= person * positions + role < people * positions.
Proof.
  intros person positions role people Hperson Hrole Hpositions.
  nia.
Qed.
Lemma mask_set_bit_bounds__solver_role_index :
  forall mask role positions,
    0 <= mask < Z.shiftl 1 positions ->
    0 <= role < positions ->
    0 <= Z.lor mask (Z.shiftl 1 role) < Z.shiftl 1 positions.
Proof.
  intros mask role positions Hmask Hrole.
  rewrite !Z.shiftl_1_l in *.
  assert (Hbit : 0 <= 2 ^ role < 2 ^ positions).
  {
    split.
    - apply Z.pow_nonneg. lia.
    - apply Z.pow_lt_mono_r; lia.
  }
  split.
  - apply Z.lor_nonneg. lia.
  - assert (Hmask_bits : Z.land mask (2 ^ positions - 1) = mask).
    {
      change (Z.land mask (Z.pred (2 ^ positions)) = mask).
      rewrite <- Z.ones_equiv.
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small; lia.
    }
    assert (Hbit_bits :
        Z.land (2 ^ role) (2 ^ positions - 1) = 2 ^ role).
    {
      change (Z.land (2 ^ role) (Z.pred (2 ^ positions)) = 2 ^ role).
      rewrite <- Z.ones_equiv.
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small; lia.
    }
    assert (Hall_bits :
        Z.land (Z.lor mask (2 ^ role)) (2 ^ positions - 1) =
        Z.lor mask (2 ^ role)).
    {
      rewrite Z.land_lor_distr_l, Hmask_bits, Hbit_bits.
      reflexivity.
    }
    change (Z.land (Z.lor mask (2 ^ role)) (Z.pred (2 ^ positions)) =
        Z.lor mask (2 ^ role)) in Hall_bits.
    rewrite <- Z.ones_equiv in Hall_bits.
    rewrite Z.land_ones in Hall_bits by lia.
    pose proof (Z.mod_pos_bound (Z.lor mask (2 ^ role))
      (2 ^ positions) ltac:(apply Z.pow_pos_nonneg; lia)).
    lia.
Qed.
Lemma bounded_team_source_close__solver_source_close :
  forall sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source,
    0 <= source ->
    BoundedTeamRoleUpdateProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values source positions ->
    BoundedTeamNextRowProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values (source + 1).
Proof.
  intros sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source Hsource Hprogress.
  unfold BoundedTeamNextRowProgress.
  intros target Htarget.
  unfold BoundedTeamRoleUpdateProgress in Hprogress.
  specialize (Hprogress target Htarget).
  assert (Hcandidate : forall score,
    TeamTransitionCandidate sorted_audience sorted_order skill positions
      audience_limit processed old_values (source + 1) target score <->
    (TeamTransitionCandidate sorted_audience sorted_order skill positions
       audience_limit processed old_values source target score \/
     TeamCurrentSourceCandidate sorted_audience sorted_order skill positions
       audience_limit processed old_values source positions target score)).
  {
    intros score. split.
    - intros Hnew. unfold TeamTransitionCandidate in Hnew.
      destruct Hnew as
        (origin & origin_score & Horigin & Hscore & Hfinite & Hcase).
      destruct (Z_lt_ge_dec origin source) as [Hlt | Hge].
      + left. unfold TeamTransitionCandidate.
        exists origin, origin_score. repeat split; try assumption; lia.
      + right. assert (origin = source) by lia. subst origin.
        subst origin_score.
        unfold TeamCurrentSourceCandidate; cbn.
        split; [exact Hfinite | exact Hcase].
    - intros [Hold | Hcurrent].
      + unfold TeamTransitionCandidate in Hold |- *.
        destruct Hold as
          (origin & origin_score & Horigin & Hscore & Hfinite & Hcase).
        exists origin, origin_score. repeat split; try assumption; lia.
      + unfold TeamCurrentSourceCandidate in Hcurrent.
        destruct Hcurrent as [Hfinite Hcase].
        unfold TeamTransitionCandidate.
        exists source, (Znth source old_values TeamNegInf).
        repeat split; try assumption; lia.
  }
  destruct Hprogress as [Hmaximum | [Hnone_value Hnone]].
  - left. unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hmaximum as [best [[Hbest Hupper] Hvalue]].
    exists best. split; [|exact Hvalue]. split.
    + apply (proj2 (Hcandidate best)). exact Hbest.
    + intros score Hscore. apply Hupper.
      apply (proj1 (Hcandidate score)). exact Hscore.
  - right. split; [exact Hnone_value |].
    intros score Hscore. apply (Hnone score).
    apply (proj1 (Hcandidate score)). exact Hscore.
Qed.
Lemma bounded_team_source_skip__solver_source_close :
  forall sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source,
    Znth source old_values TeamNegInf = TeamNegInf ->
    BoundedTeamNextRowProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values source ->
    BoundedTeamNextRowProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values (source + 1).
Proof.
  intros sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source Hsource_neg Hprogress.
  unfold BoundedTeamNextRowProgress.
  intros target Htarget.
  unfold BoundedTeamNextRowProgress in Hprogress.
  specialize (Hprogress target Htarget).
  assert (Hcandidate : forall score,
    TeamTransitionCandidate sorted_audience sorted_order skill positions
      audience_limit processed old_values (source + 1) target score <->
    TeamTransitionCandidate sorted_audience sorted_order skill positions
      audience_limit processed old_values source target score).
  {
    intros score. split.
    - intros Hnew. unfold TeamTransitionCandidate in Hnew |- *.
      destruct Hnew as
        (origin & origin_score & Horigin & Hscore & Hfinite & Hcase).
      destruct (Z_lt_ge_dec origin source) as [Hlt | Hge].
      + exists origin, origin_score. repeat split; try assumption; lia.
      + assert (origin = source) by lia. subst origin. subst origin_score.
        rewrite Hsource_neg in Hfinite. contradiction.
    - intros Hold. unfold TeamTransitionCandidate in Hold |- *.
      destruct Hold as
        (origin & origin_score & Horigin & Hscore & Hfinite & Hcase).
      exists origin, origin_score. repeat split; try assumption; lia.
  }
  destruct Hprogress as [Hmaximum | [Hnone_value Hnone]].
  - left. unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in *.
    destruct Hmaximum as [best [[Hbest Hupper] Hvalue]].
    exists best. split; [|exact Hvalue]. split.
    + apply (proj2 (Hcandidate best)). exact Hbest.
    + intros score Hscore. apply Hupper.
      apply (proj1 (Hcandidate score)). exact Hscore.
  - right. split; [exact Hnone_value |].
    intros score Hscore. apply (Hnone score).
    apply (proj1 (Hcandidate score)). exact Hscore.
Qed.
Lemma Forall_Znth_local__solver_role_update_b :
  forall {A : Type} (P : A -> Prop) (d : A) (l : list A),
    Forall P l ->
    forall i, 0 <= i < Zlength l -> P (Znth i l d).
Proof.
  intros A P d l HForall.
  induction HForall as [|x xs Hx Hxs IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + rewrite Znth0_cons. exact Hx.
    + rewrite Znth_cons by lia. apply IH.
      rewrite Zlength_cons in Hi. lia.
Qed.
Lemma Znth_concat_uniform__solver_role_update_b :
  forall (rows : list (list Z)) m (d : list Z) i j,
    0 <= i < Zlength rows ->
    (forall r, 0 <= r < Zlength rows -> Zlength (Znth r rows d) = m) ->
    0 <= j < m ->
    Znth (i * m + j) (concat rows) 0 = Znth j (Znth i rows d) 0.
Proof.
  induction rows as [|row rows IH]; intros m d i j Hi Hlen Hj.
  - rewrite Zlength_nil in Hi. lia.
  - assert (Hrow : Zlength row = m).
    { specialize (Hlen 0). rewrite Znth0_cons in Hlen. apply Hlen.
      rewrite Zlength_cons in Hi |- *. lia. }
    destruct (Z.eq_dec i 0) as [-> | Hine].
    + simpl concat. rewrite Znth0_cons.
      rewrite app_Znth1; [reflexivity |]. rewrite Hrow. lia.
    + simpl concat. rewrite app_Znth2 by (rewrite Hrow; nia).
      replace (i * m + j - Zlength row) with ((i - 1) * m + j)
        by (rewrite Hrow; ring).
      rewrite Znth_cons by lia.
      apply IH.
      * rewrite Zlength_cons in Hi. lia.
      * intros r Hr. specialize (Hlen (r + 1)).
        rewrite Znth_cons in Hlen by lia.
        replace (r + 1 - 1) with r in Hlen by lia. apply Hlen.
        rewrite Zlength_cons. lia.
      * exact Hj.
Qed.
Lemma bounded_team_role_update_write__solver_role_update_a :
  forall sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source role target score,
    0 <= role < positions ->
    target = Z.lor source (2 ^ role) ->
    Z.testbit source role = false ->
    score = Znth source old_values TeamNegInf +
      Znth role
        (Znth (Znth (Zlength sorted_order - 1 - processed)
          sorted_order 0) skill []) 0 ->
    Znth source old_values TeamNegInf <> TeamNegInf ->
    0 <= target < 2 ^ positions ->
    2 ^ positions <= Zlength next_values ->
    Znth target next_values TeamNegInf < score ->
    BoundedTeamRoleUpdateProgress sorted_audience sorted_order skill
      positions audience_limit processed old_values next_values source role ->
    BoundedTeamRoleUpdateProgress sorted_audience sorted_order skill
      positions audience_limit processed old_values
      (replace_Znth target score next_values) source (role + 1).
Proof.
  intros sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source role target score Hrole Htarget Hbit Hscore
    Hsource Htarget_range Hlength Hbetter Hprogress.
  assert (Hexpand : forall query value,
    (TeamTransitionCandidate sorted_audience sorted_order skill
       positions audience_limit processed old_values source query value \/
     TeamCurrentSourceCandidate sorted_audience sorted_order skill
       positions audience_limit processed old_values source (role + 1)
       query value) <->
    ((TeamTransitionCandidate sorted_audience sorted_order skill
        positions audience_limit processed old_values source query value \/
      TeamCurrentSourceCandidate sorted_audience sorted_order skill
        positions audience_limit processed old_values source role query value) \/
     (query = target /\ value = score))).
  {
    intros query value. split.
    - intros [Htransition | Hcurrent].
      + left. left. exact Htransition.
      + unfold TeamCurrentSourceCandidate in Hcurrent |- *; cbn in Hcurrent |- *.
        destruct Hcurrent as [Hvalid Hcase].
        destruct Hcase as [Hsame | [Haudience | Hassigned]].
        * left. right. split; [exact Hvalid | left; exact Hsame].
        * left. right. split; [exact Hvalid | right; left; exact Haudience].
        * destruct Hassigned as
            (assigned_role & Hassigned_range & Hassigned_bit &
             Hassigned_target & Hassigned_score).
          destruct (Z_lt_ge_dec assigned_role role) as [Hlt | Hge].
          -- left. right. split; [exact Hvalid | right; right].
             exists assigned_role. repeat split; try assumption; lia.
          -- right.
             assert (assigned_role = role) by lia. subst assigned_role.
             split.
             ++ rewrite Hassigned_target, Htarget. reflexivity.
             ++ rewrite Hassigned_score, Hscore. reflexivity.
    - intros [[Htransition | Hcurrent] | [Hquery Hvalue]].
      + left. exact Htransition.
      + right.
        unfold TeamCurrentSourceCandidate in Hcurrent |- *; cbn in Hcurrent |- *.
        destruct Hcurrent as [Hvalid Hcase]. split; [exact Hvalid |].
        destruct Hcase as [Hsame | [Haudience | Hassigned]].
        * left. exact Hsame.
        * right. left. exact Haudience.
        * right. right.
          destruct Hassigned as
            (assigned_role & Hassigned_range & Hassigned_bit &
             Hassigned_target & Hassigned_score).
          exists assigned_role. repeat split; try assumption; lia.
      + subst query value. right.
        unfold TeamCurrentSourceCandidate; cbn. split; [exact Hsource |].
        right. right. exists role. repeat split; try assumption; lia.
  }
  unfold BoundedTeamRoleUpdateProgress in Hprogress |- *.
  intros query Hquery.
  specialize (Hprogress query Hquery).
  assert (Hquery_list : 0 <= query < Zlength next_values) by lia.
  assert (Htarget_list : 0 <= target < Zlength next_values) by lia.
  destruct (Z.eq_dec query target) as [Heq | Hneq].
  - subst query.
    rewrite Znth_replace_Znth_Same by exact Htarget_list.
    destruct Hprogress as [Hmaximum | [Hempty_value Hempty]].
    + left.
      unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hmaximum |- *.
      destruct Hmaximum as [best [[Hbest Hupper] Hbest_value]].
      exists score. split; [|reflexivity]. split.
      * apply (proj2 (Hexpand target score)). right. split; reflexivity.
      * intros value Hvalue.
        apply (proj1 (Hexpand target value)) in Hvalue.
        destruct Hvalue as [Hold | [_ ->]].
        -- specialize (Hupper value Hold). lia.
        -- lia.
    + left.
      unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
      exists score. split; [|reflexivity]. split.
      * apply (proj2 (Hexpand target score)). right. split; reflexivity.
      * intros value Hvalue.
        apply (proj1 (Hexpand target value)) in Hvalue.
        destruct Hvalue as [Hold | [_ ->]].
        -- exfalso. exact (Hempty value Hold).
        -- lia.
  - rewrite (Znth_replace_Znth_Diff TeamNegInf next_values target query score)
      by (try assumption; lia).
    destruct Hprogress as [Hmaximum | [Hempty_value Hempty]].
    + left.
      unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset in Hmaximum |- *.
      destruct Hmaximum as [best [[Hbest Hupper] Hbest_value]].
      exists best. split; [|exact Hbest_value]. split.
      * apply (proj2 (Hexpand query best)). left. exact Hbest.
      * intros value Hvalue.
        apply (proj1 (Hexpand query value)) in Hvalue.
        destruct Hvalue as [Hold | [Heq _]].
        -- exact (Hupper value Hold).
        -- contradiction.
    + right. split; [exact Hempty_value |].
      intros value Hvalue.
      apply (proj1 (Hexpand query value)) in Hvalue.
      destruct Hvalue as [Hold | [Heq _]].
      * exact (Hempty value Hold).
      * contradiction.
Qed.
Lemma team_role_update_skip_core__solver_role_update_b :
  forall (sorted_audience sorted_order : list Z) (skill : list (list Z))
    (positions audience_limit processed : Z) (old_values next_values : list Z)
    (source role : Z),
    0 <= role < positions ->
    Z.testbit source role = false ->
    TeamNegInf <
      Znth source old_values TeamNegInf +
      Znth role
        (Znth
          (Znth (Zlength sorted_order - 1 - processed) sorted_order 0)
          skill (@nil Z)) 0 ->
    Znth source old_values TeamNegInf +
      Znth role
        (Znth
          (Znth (Zlength sorted_order - 1 - processed) sorted_order 0)
          skill (@nil Z)) 0 <=
      Znth (Z.lor source (2 ^ role)) next_values TeamNegInf ->
    TeamRoleUpdateProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values source role ->
    TeamRoleUpdateProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values source (role + 1).
Proof.
  intros sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source role Hrole Hbit Hnew_gt Hnew_le Hprogress.
  unfold TeamRoleUpdateProgress in Hprogress |- *.
  intros target Htarget.
  specialize (Hprogress target Htarget).
  destruct Hprogress as [Hmax | [Hnone_value Hnone]].
  - left.
    destruct Hmax as [best [[Hin Hall] Hbest]].
    exists best. split.
    + split.
      * destruct Hin as [Htransition | Hcurrent].
        -- left. exact Htransition.
        -- right.
           unfold TeamCurrentSourceCandidate in Hcurrent |- *.
           destruct Hcurrent as [Hsource [Hsame | [Haudience | Hroles]]].
           ++ split; [exact Hsource | left; exact Hsame].
           ++ split; [exact Hsource | right; left; exact Haudience].
           ++ split; [exact Hsource | right; right].
              destruct Hroles as [scanned [Hscanned [Hscanned_bit [Hscanned_target Hscanned_score]]]].
              exists scanned. repeat split; try assumption; lia.
      * intros score Hscore.
        destruct Hscore as [Htransition | Hcurrent].
        -- apply Hall. left. exact Htransition.
        -- unfold TeamCurrentSourceCandidate in Hcurrent.
           destruct Hcurrent as [Hsource [Hsame | [Haudience | Hroles]]].
           ++ apply Hall. right. unfold TeamCurrentSourceCandidate.
              split; [exact Hsource | left; exact Hsame].
           ++ apply Hall. right. unfold TeamCurrentSourceCandidate.
              split; [exact Hsource | right; left; exact Haudience].
           ++ destruct Hroles as [scanned [Hscanned [Hscanned_bit [Hscanned_target Hscanned_score]]]].
              destruct (Z.eq_dec scanned role) as [Heq | Hneq].
              ** subst scanned. subst target. subst score.
                 rewrite <- Hbest in Hnew_le. exact Hnew_le.
              ** apply Hall. right. unfold TeamCurrentSourceCandidate.
                 split; [exact Hsource | right; right].
                 exists scanned. repeat split; try assumption; lia.
    + exact Hbest.
  - destruct (Z.eq_dec target (Z.lor source (2 ^ role))) as [Heq | Hneq].
    + subst target. lia.
    + right. split; [exact Hnone_value |].
      intros score [Htransition | Hcurrent].
      * apply (Hnone score). left. exact Htransition.
      * unfold TeamCurrentSourceCandidate in Hcurrent.
        destruct Hcurrent as [Hsource [Hsame | [Haudience | Hroles]]].
        -- apply (Hnone score). right. unfold TeamCurrentSourceCandidate.
           split; [exact Hsource | left; exact Hsame].
        -- apply (Hnone score). right. unfold TeamCurrentSourceCandidate.
           split; [exact Hsource | right; left; exact Haudience].
        -- destruct Hroles as [scanned [Hscanned [Hscanned_bit [Hscanned_target Hscanned_score]]]].
           destruct (Z.eq_dec scanned role) as [Heq | Hne].
           ++ subst scanned. contradiction.
           ++ apply (Hnone score). right. unfold TeamCurrentSourceCandidate.
              split; [exact Hsource | right; right].
              exists scanned. repeat split; try assumption; lia.
Qed.
Lemma team_role_update_skip__solver_role_update_b :
  forall n p k aud default skill sorted_audience sorted_order processed
    old_values next_values source role person full mask,
    2 <= n ->
    1 <= p <= 7 ->
    n = Zlength aud ->
    p = Zlength (Znth 0 skill default) ->
    Zlength sorted_order = n ->
    person = Znth (n - 1 - processed) sorted_order 0 ->
    0 <= person < n ->
    Zlength old_values = 128 ->
    Zlength next_values = 128 ->
    0 <= source < full ->
    full <= 128 ->
    0 <= role < p ->
    mask = Z.shiftl 1 role ->
    Z.land source mask = 0 ->
    0 <= Z.lor source mask ->
    Z.lor source mask < full ->
    Znth source old_values 0 <> TeamNegInf ->
    Pre k aud skill ->
    (forall idx, 0 <= idx < n * p ->
      1 <= Znth idx (concat skill) 0 <= 1000000000) ->
    (forall q, 0 <= q < full ->
      (TeamNegInf <= Znth q old_values 0 <= 100000000000000 /\
       TeamNegInf <= Znth q next_values 0) /\
      Znth q next_values 0 <= 100000000000000) ->
    Znth source old_values 0 + Znth (person * p + role) (concat skill) 0 <=
      Znth (Z.lor source mask) next_values 0 ->
    TeamRoleUpdateProgress sorted_audience sorted_order skill p k processed
      old_values next_values source role ->
    TeamRoleUpdateProgress sorted_audience sorted_order skill p k processed
      old_values next_values source (role + 1).
Proof.
  intros n p k aud default skill sorted_audience sorted_order processed
    old_values next_values source role person full mask Hn Hp Hn_aud Hp_row
    Horder_len Hperson Hperson_bounds Hold_len Hnext_len Hsource Hfull
    Hrole Hmask Hland Htarget_nonneg Htarget_full Hsource_live Hpre Hflat_bounds
    Htable_bounds Hcandidate_le Hprogress.
  assert (Hpow : Z.shiftl 1 role = 2 ^ role).
  { rewrite Z.shiftl_mul_pow2 by lia. lia. }
  assert (Hbit : Z.testbit source role = false).
  { assert (Hlandbit :
      Z.testbit (Z.land source mask) role = false).
    { rewrite Hland, Z.testbit_0_l. reflexivity. }
    rewrite Z.land_spec in Hlandbit.
    assert (Hsingle : Z.testbit mask role = true).
    { rewrite Hmask, Z.shiftl_spec by lia.
      replace (role - role) with 0 by lia. reflexivity. }
    rewrite Hsingle, Bool.andb_true_r in Hlandbit. exact Hlandbit. }
  unfold Pre in Hpre.
  destruct Hpre as
    [Hskill_aud [width [Hwidth_k [Hskill_aud' Hrows]]]].
  assert (Hskill_len : Zlength skill = n) by lia.
  assert (Hrow0 : Zlength (Znth 0 skill default) = width).
  { apply (Forall_Znth_local__solver_role_update_b _ default skill Hrows).
    rewrite Hskill_len. lia. }
  assert (Hwidth_eq : width = p) by lia.
  assert (Hrow_lengths : forall r,
    0 <= r < Zlength skill -> Zlength (Znth r skill (@nil Z)) = p).
  { intros r Hr.
    pose proof (Forall_Znth_local__solver_role_update_b
      _ (@nil Z) skill Hrows r Hr) as Hrlen.
    rewrite Hwidth_eq in Hrlen. exact Hrlen. }
  assert (Hperson_index :
    Znth (Zlength sorted_order - 1 - processed) sorted_order 0 = person).
  { replace (Zlength sorted_order - 1 - processed) with (n - 1 - processed)
      by lia.
    symmetry. exact Hperson. }
  assert (Hflat :
    Znth (person * p + role) (concat skill) 0 =
    Znth role
      (Znth (Znth (Zlength sorted_order - 1 - processed) sorted_order 0)
        skill (@nil Z)) 0).
  { rewrite Hperson_index.
    apply Znth_concat_uniform__solver_role_update_b.
    - rewrite Hskill_len. exact Hperson_bounds.
    - exact Hrow_lengths.
    - exact Hrole. }
  eapply team_role_update_skip_core__solver_role_update_b.
  - exact Hrole.
  - exact Hbit.
  - rewrite <- Hflat.
    rewrite (Znth_indep old_values source TeamNegInf 0) by lia.
    specialize (Hflat_bounds (person * p + role) ltac:(nia)).
    specialize (Htable_bounds source ltac:(lia)).
    unfold TeamNegInf in Hsource_live, Htable_bounds |- *. lia.
  - rewrite <- Hflat.
    rewrite (Znth_indep old_values source TeamNegInf 0) by lia.
    rewrite (Znth_indep next_values (Z.lor source (2 ^ role)) TeamNegInf 0).
    2: { rewrite <- Hpow, <- Hmask. lia. }
    rewrite <- Hpow, <- Hmask. exact Hcandidate_le.
  - exact Hprogress.
Qed.
Lemma bounded_team_role_update_skip__solver_role_update_b :
  forall n p k aud default skill sorted_audience sorted_order processed
    old_values next_values source role person full mask,
    2 <= n ->
    1 <= p <= 7 ->
    n = Zlength aud ->
    p = Zlength (Znth 0 skill default) ->
    Zlength sorted_order = n ->
    person = Znth (n - 1 - processed) sorted_order 0 ->
    0 <= person < n ->
    Zlength old_values = 128 ->
    Zlength next_values = 128 ->
    0 <= source < full ->
    full <= 128 ->
    0 <= role < p ->
    mask = Z.shiftl 1 role ->
    Z.land source mask = 0 ->
    0 <= Z.lor source mask ->
    Z.lor source mask < full ->
    Znth source old_values 0 <> TeamNegInf ->
    Pre k aud skill ->
    (forall idx, 0 <= idx < n * p ->
      1 <= Znth idx (concat skill) 0 <= 1000000000) ->
    (forall q, 0 <= q < full ->
      (TeamNegInf <= Znth q old_values 0 <= 100000000000000 /\
       TeamNegInf <= Znth q next_values 0) /\
      Znth q next_values 0 <= 100000000000000) ->
    Znth source old_values 0 + Znth (person * p + role) (concat skill) 0 <=
      Znth (Z.lor source mask) next_values 0 ->
    BoundedTeamRoleUpdateProgress sorted_audience sorted_order skill p k processed
      old_values next_values source role ->
    BoundedTeamRoleUpdateProgress sorted_audience sorted_order skill p k processed
      old_values next_values source (role + 1).
Proof.
  intros n p k aud default skill sorted_audience sorted_order processed
    old_values next_values source role person full mask Hn Hp Hn_aud Hp_row
    Horder_len Hperson Hperson_bounds Hold_len Hnext_len Hsource Hfull
    Hrole Hmask Hland Htarget_nonneg Htarget_full Hsource_live Hpre Hflat_bounds
    Htable_bounds Hcandidate_le Hprogress.
  change (TeamRoleUpdateProgress sorted_audience sorted_order skill p k processed
    old_values next_values source role) in Hprogress.
  change (TeamRoleUpdateProgress sorted_audience sorted_order skill p k processed
    old_values next_values source (role + 1)).
  eapply team_role_update_skip__solver_role_update_b; eauto.
Qed.
Lemma testbit_from_land_shiftl_one__solver_role_update_c :
  forall value bit,
    0 <= bit ->
    Z.land value (Z.shiftl 1 bit) <> 0 ->
    Z.testbit value bit = true.
Proof.
  intros value bit Hbit Hnonzero.
  destruct (Z.testbit value bit) eqn:Hvalue; [reflexivity |].
  exfalso. apply Hnonzero.
  apply Z.bits_inj. intro k.
  rewrite Z.testbit_0_l, Z.land_spec.
  destruct (Z_lt_ge_dec k bit) as [Hlow | Hhigh].
  - rewrite Z.shiftl_spec_low by lia.
    rewrite Bool.andb_false_r. reflexivity.
  - rewrite Z.shiftl_spec by lia.
    destruct (Z.eq_dec k bit) as [-> | Hne].
    + replace (bit - bit) with 0 by lia. simpl. rewrite Hvalue. reflexivity.
    + rewrite (Z.bits_above_log2 1 (k - bit)) by (simpl; lia).
      rewrite Bool.andb_false_r. reflexivity.
Qed.
Lemma bounded_team_role_update_skip_or_write__solver_role_update_c :
  forall sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source roles_scanned,
    0 <= roles_scanned ->
    Z.testbit source roles_scanned = true ->
    BoundedTeamRoleUpdateProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values source roles_scanned ->
    BoundedTeamRoleUpdateProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values source (roles_scanned + 1).
Proof.
  intros sorted_audience sorted_order skill positions audience_limit processed
    old_values next_values source roles_scanned Hroles Hbit Hprogress.
  assert (Hcurrent : forall target score,
    TeamCurrentSourceCandidate sorted_audience sorted_order skill positions
      audience_limit processed old_values source (roles_scanned + 1)
      target score ->
    TeamCurrentSourceCandidate sorted_audience sorted_order skill positions
      audience_limit processed old_values source roles_scanned target score).
  {
    intros target score Hcandidate.
    unfold TeamCurrentSourceCandidate in Hcandidate |- *.
    destruct Hcandidate as [Hsource [Hsame | [Haudience | Hrole]]].
    - split; [exact Hsource | left; exact Hsame].
    - split; [exact Hsource | right; left; exact Haudience].
    - destruct Hrole as [role [Hrange [Hrolebit Hrest]]].
      split; [exact Hsource | right; right].
      exists role. split.
      + destruct Hrange as [Hrole_nonneg Hrole_upper].
        split; [exact Hrole_nonneg |].
        destruct (Z.eq_dec role roles_scanned) as [Heq | Hneq].
        * subst role. rewrite Hbit in Hrolebit. discriminate.
        * lia.
      + split; [exact Hrolebit | exact Hrest].
  }
  unfold BoundedTeamRoleUpdateProgress in Hprogress |- *.
  intros target Htarget.
  specialize (Hprogress target Htarget).
  destruct Hprogress as [Hmax | [Hnone_value Hnone]].
  - left.
    unfold max_value_of_subset, max_object_of_subset in Hmax |- *.
    destruct Hmax as [best [[[Htransition | Hcandidate] Hupper] Heq]].
    + exists best. split; [split | exact Heq].
      * left. exact Htransition.
      * intros score [Htransition' | Hcandidate']; apply Hupper.
        -- left. exact Htransition'.
        -- right. apply Hcurrent. exact Hcandidate'.
    + exists best. split; [split | exact Heq].
      * right.
        unfold TeamCurrentSourceCandidate in Hcandidate |- *.
        destruct Hcandidate as [Hsource [Hsame | [Haudience | Hrole]]].
        -- split; [exact Hsource | left; exact Hsame].
        -- split; [exact Hsource | right; left; exact Haudience].
        -- destruct Hrole as [role [Hrange Hrest]].
           split; [exact Hsource | right; right].
           exists role. split; [lia | exact Hrest].
      * intros score [Htransition' | Hcandidate']; apply Hupper.
        -- left. exact Htransition'.
        -- right. apply Hcurrent. exact Hcandidate'.
  - right. split; [exact Hnone_value |].
    intros score Hnew.
    apply (Hnone score).
    destruct Hnew as [Htransition | Hcandidate].
    + left. exact Htransition.
    + right. apply Hcurrent. exact Hcandidate.
Qed.
Lemma map_snd_combine__solver_row_close_dispatch :
  forall (xs ys : list Z),
    Zlength xs = Zlength ys ->
    map snd (combine xs ys) = ys.
Proof. exact map_snd_combine__solver_row_close. Qed.
Lemma processed_audience_dominates_new__solver_row_close_dispatch :
  forall audience order_values sorted_audience sorted_order processed old_person,
    SortedPeopleState audience order_values sorted_audience sorted_order ->
    Zlength sorted_audience = Zlength sorted_order ->
    0 <= processed < Zlength sorted_order ->
    ProcessedPerson sorted_order processed old_person ->
    Znth (Znth (Zlength sorted_order - 1 - processed) sorted_order 0)
      audience 0 <= Znth old_person audience 0.
Proof. exact processed_audience_dominates_new__solver_row_close. Qed.
Lemma bounded_dp_choice_upper__solver_row_close_dispatch :
  forall audience skill order positions audience_limit processed values mask score,
    0 <= mask < 2 ^ positions ->
    BoundedTeamDPTable audience skill order positions audience_limit processed values ->
    BoundedTeamPrefixChoice audience skill order positions audience_limit processed
      mask score ->
    score <= Znth mask values TeamNegInf.
Proof. exact bounded_dp_choice_upper__solver_row_close. Qed.
Lemma fold_right_add_app__solver_row_close_dispatch :
  forall left right,
    fold_right Z.add 0 (left ++ right) =
    fold_right Z.add 0 left + fold_right Z.add 0 right.
Proof. exact fold_right_add_app__solver_row_close. Qed.
Lemma fold_bit_count_filter__solver_row_close_dispatch :
  forall (f : Z -> bool) values,
    fold_right Z.add 0
      (map (fun bit => if f bit then 1 else 0) values) =
    Zlength (filter f values).
Proof. exact fold_bit_count_filter__solver_row_close. Qed.
Lemma bounded_mask_high_bit_false__solver_row_close_dispatch :
  forall mask positions bit,
    0 <= mask < 2 ^ positions ->
    0 <= positions -> positions <= bit ->
    Z.testbit mask bit = false.
Proof. exact bounded_mask_high_bit_false__solver_row_close. Qed.
Lemma bitcount_assignments_length__solver_row_close_dispatch :
  forall positions mask assignments used,
    0 <= positions <= 7 ->
    0 <= mask < 2 ^ positions ->
    BoundedAssignmentsMatchMask positions mask assignments ->
    BitCount mask used ->
    used = Zlength assignments.
Proof. exact bitcount_assignments_length__solver_row_close. Qed.
Lemma identity_order_nodup__solver_row_close_dispatch :
  forall order n,
    Zlength order = n ->
    (forall q, 0 <= q < n -> Znth q order 0 = q) ->
    NoDup order.
Proof. exact identity_order_nodup__solver_row_close. Qed.
Lemma sorted_order_nodup__solver_row_close_dispatch :
  forall aud order_values sorted_audience sorted_order n,
    Zlength aud = n ->
    Zlength order_values = n ->
    Zlength sorted_audience = n ->
    Zlength sorted_order = n ->
    (forall q, 0 <= q < n -> Znth q order_values 0 = q) ->
    PeoplePermutation aud order_values sorted_audience sorted_order ->
    NoDup sorted_order.
Proof. exact sorted_order_nodup__solver_row_close. Qed.
Lemma nodup_Znth_injective__solver_row_close_dispatch :
  forall (values : list Z) i j,
    NoDup values ->
    0 <= i < Zlength values ->
    0 <= j < Zlength values ->
    Znth i values 0 = Znth j values 0 ->
    i = j.
Proof. exact nodup_Znth_injective__solver_row_close. Qed.
Lemma processed_person_lift__solver_row_close_dispatch :
  forall order processed person,
    ProcessedPerson order processed person ->
    ProcessedPerson order (processed + 1) person.
Proof. exact processed_person_lift__solver_row_close. Qed.
Lemma processed_person_not_new__solver_row_close_dispatch :
  forall order processed person,
    NoDup order ->
    0 <= processed < Zlength order ->
    ProcessedPerson order processed person ->
    person <> Znth (Zlength order - 1 - processed) order 0.
Proof. exact processed_person_not_new__solver_row_close. Qed.
Lemma bounded_dp_finite_choice__solver_row_close_dispatch :
  forall aud skill order positions audience_limit processed values mask,
    0 <= mask < 2 ^ positions ->
    BoundedTeamDPTable aud skill order positions audience_limit processed values ->
    Znth mask values TeamNegInf <> TeamNegInf ->
    BoundedTeamPrefixChoice aud skill order positions audience_limit processed
      mask (Znth mask values TeamNegInf).
Proof. exact bounded_dp_finite_choice__solver_row_close. Qed.
Lemma max_value_cofinal__solver_row_close_dispatch :
  forall (P Q : Z -> Prop) value,
    (forall p, P p -> exists q, Q q /\ p <= q) ->
    (forall q, Q q -> exists p, P p /\ q <= p) ->
    max_value_of_subset Z.le P (fun x => x) value ->
    max_value_of_subset Z.le Q (fun x => x) value.
Proof. exact max_value_cofinal__solver_row_close. Qed.
Lemma Zlength_Zrange_zero__solver_row_close_dispatch :
  forall high, 0 <= high -> Zlength (Zrange 0 high) = high.
Proof. exact Zlength_Zrange_zero__solver_row_close. Qed.
Lemma processed_person_in_people__solver_row_close_dispatch :
  forall order processed person,
    0 <= processed ->
    (ProcessedPerson order processed person <->
     In person
       (map (fun step => Znth (Zlength order - 1 - step) order 0)
         (Zrange 0 processed))).
Proof. exact processed_person_in_people__solver_row_close. Qed.
Lemma processed_people_nodup__solver_row_close_dispatch :
  forall order processed,
    NoDup order ->
    0 <= processed <= Zlength order ->
    NoDup
      (map (fun step => Znth (Zlength order - 1 - step) order 0)
        (Zrange 0 processed)).
Proof. exact processed_people_nodup__solver_row_close. Qed.
Lemma processed_selection_card__solver_row_close_dispatch :
  forall order processed selected,
    0 <= processed ->
    NoDup selected ->
    Forall (ProcessedPerson order processed) selected ->
    Zlength selected <= processed.
Proof. exact processed_selection_card__solver_row_close. Qed.
Lemma processed_missing_person__solver_row_close_dispatch :
  forall order processed selected,
    NoDup order ->
    0 <= processed <= Zlength order ->
    NoDup selected ->
    Zlength selected < processed ->
    exists person,
      ProcessedPerson order processed person /\ ~ In person selected.
Proof. exact processed_missing_person__solver_row_close. Qed.
Lemma processed_person_succ_cases__solver_row_close_dispatch :
  forall order processed person,
    0 <= processed ->
    ProcessedPerson order (processed + 1) person ->
    person = Znth (Zlength order - 1 - processed) order 0 \/
    ProcessedPerson order processed person.
Proof. exact processed_person_succ_cases__solver_row_close. Qed.
Lemma testbit_pow2__solver_row_close_dispatch :
  forall role bit,
    0 <= role -> 0 <= bit ->
    Z.testbit (2 ^ role) bit = Z.eqb bit role.
Proof. exact testbit_pow2__solver_row_close. Qed.
Lemma small_mask_remove_bit__solver_row_close_dispatch :
  forall positions target role,
    0 <= positions <= 7 ->
    0 <= target < 2 ^ positions ->
    0 <= role < positions ->
    Z.testbit target role = true ->
    let source := Z.ldiff target (2 ^ role) in
    0 <= source < 2 ^ positions /\
    Z.testbit source role = false /\
    Z.lor source (2 ^ role) = target /\
    forall other,
      0 <= other < positions -> other <> role ->
      Z.testbit source other = Z.testbit target other.
Proof. exact small_mask_remove_bit__solver_row_close. Qed.
Lemma mask_set_bit_bounds__solver_row_close_dispatch :
  forall mask role positions,
    0 <= mask < Z.shiftl 1 positions ->
    0 <= role < positions ->
    0 <= Z.lor mask (Z.shiftl 1 role) < Z.shiftl 1 positions.
Proof. exact mask_set_bit_bounds__solver_row_close. Qed.
Lemma small_mask_add_bit__solver_row_close_dispatch :
  forall positions source role,
    0 <= positions <= 7 ->
    0 <= source < 2 ^ positions ->
    0 <= role < positions ->
    Z.testbit source role = false ->
    let target := Z.lor source (2 ^ role) in
    0 <= target < 2 ^ positions /\
    Z.testbit target role = true /\
    forall other,
      0 <= other < positions -> other <> role ->
      Z.testbit target other = Z.testbit source other.
Proof. exact small_mask_add_bit__solver_row_close. Qed.
Lemma bounded_match_cons__solver_row_close_dispatch :
  forall positions source assignments role person,
    0 <= positions <= 7 ->
    0 <= source < 2 ^ positions ->
    BoundedAssignmentsMatchMask positions source assignments ->
    0 <= role < positions ->
    Z.testbit source role = false ->
    BoundedAssignmentsMatchMask positions (Z.lor source (2 ^ role))
      ((role, person) :: assignments).
Proof. exact bounded_match_cons__solver_row_close. Qed.
Lemma bounded_match_remove__solver_row_close_dispatch :
  forall positions target before after role person,
    0 <= positions <= 7 ->
    0 <= target < 2 ^ positions ->
    BoundedAssignmentsMatchMask positions target
      (before ++ (role, person) :: after) ->
    exists source,
      0 <= source < 2 ^ positions /\
      Z.testbit source role = false /\
      Z.lor source (2 ^ role) = target /\
      BoundedAssignmentsMatchMask positions source (before ++ after).
Proof. exact bounded_match_remove__solver_row_close. Qed.
Lemma transition_to_bounded_choice__solver_row_close_dispatch :
  forall audience sorted_audience skill order positions audience_limit processed
    old_values target score,
    0 <= positions <= 7 ->
    1 <= audience_limit ->
    0 <= processed < Zlength order ->
    NoDup order ->
    Znth (Zlength sorted_audience - 1 - processed) sorted_audience 0 =
      Znth (Znth (Zlength order - 1 - processed) order 0) audience 0 ->
    1 <= Znth (Zlength sorted_audience - 1 - processed) sorted_audience 0 ->
    BoundedTeamDPTable audience skill order positions audience_limit processed
      old_values ->
    TeamTransitionCandidate sorted_audience order skill positions audience_limit
      processed old_values (2 ^ positions) target score ->
    exists choice_score,
      BoundedTeamPrefixChoice audience skill order positions audience_limit
        (processed + 1) target choice_score /\
      score <= choice_score.
Proof. exact transition_to_bounded_choice__solver_row_close. Qed.
Lemma fold_right_add_nonnegative__solver_row_close_dispatch :
  forall values,
    Forall (fun value => 0 <= value) values ->
    0 <= fold_right Z.add 0 values.
Proof. exact fold_right_add_nonnegative__solver_row_close. Qed.
Lemma bounded_choice_score_nonnegative__solver_row_close_dispatch :
  forall audience skill order positions audience_limit processed mask score,
    (forall person,
      ProcessedPerson order processed person ->
      0 <= Znth person audience 0) ->
    (forall role person,
      0 <= role < positions ->
      ProcessedPerson order processed person ->
      0 <= Znth role (Znth person skill []) 0) ->
    BoundedTeamPrefixChoice audience skill order positions audience_limit
      processed mask score ->
    0 <= score.
Proof. exact bounded_choice_score_nonnegative__solver_row_close. Qed.
Lemma fold_map_middle__solver_row_close_dispatch :
  forall {A : Type} (f : A -> Z) before x after,
    fold_right Z.add 0 (map f (before ++ x :: after)) =
    f x + fold_right Z.add 0 (map f (before ++ after)).
Proof. exact (@fold_map_middle__solver_row_close). Qed.
Lemma processed_selection_without_new__solver_row_close_dispatch :
  forall order processed before after,
    0 <= processed ->
    let new_person :=
      Znth (Zlength order - 1 - processed) order 0 in
    NoDup (before ++ new_person :: after) ->
    Forall (ProcessedPerson order (processed + 1))
      (before ++ new_person :: after) ->
    Forall (ProcessedPerson order processed) (before ++ after).
Proof. exact processed_selection_without_new__solver_row_close. Qed.
Lemma team_neg_inf_negative__solver_row_close_dispatch : TeamNegInf < 0.
Proof. exact team_neg_inf_negative__solver_row_close. Qed.
Lemma bounded_choice_to_transition__solver_row_close_dispatch :
  forall audience sorted_audience skill order positions audience_limit processed
    old_values target choice_score,
    0 <= positions <= 7 ->
    1 <= audience_limit ->
    0 <= processed < Zlength order ->
    NoDup order ->
    Znth (Zlength sorted_audience - 1 - processed) sorted_audience 0 =
      Znth (Znth (Zlength order - 1 - processed) order 0) audience 0 ->
    (forall old_person,
      ProcessedPerson order processed old_person ->
      Znth (Znth (Zlength order - 1 - processed) order 0) audience 0 <=
        Znth old_person audience 0) ->
    (forall person,
      ProcessedPerson order processed person ->
      0 <= Znth person audience 0) ->
    (forall role person,
      0 <= role < positions ->
      ProcessedPerson order processed person ->
      0 <= Znth role (Znth person skill []) 0) ->
    BoundedTeamDPTable audience skill order positions audience_limit processed
      old_values ->
    BoundedTeamPrefixChoice audience skill order positions audience_limit
      (processed + 1) target choice_score ->
    exists transition_score,
      TeamTransitionCandidate sorted_audience order skill positions
        audience_limit processed old_values (2 ^ positions) target
        transition_score /\
      choice_score <= transition_score.
Proof. exact bounded_choice_to_transition__solver_row_close. Qed.
Lemma bounded_team_row_close_core__solver_row_close_dispatch :
  forall audience sorted_audience skill order positions audience_limit processed
    old_values next_values,
    0 <= positions <= 7 ->
    1 <= audience_limit ->
    0 <= processed < Zlength order ->
    NoDup order ->
    Znth (Zlength sorted_audience - 1 - processed) sorted_audience 0 =
      Znth (Znth (Zlength order - 1 - processed) order 0) audience 0 ->
    1 <= Znth (Zlength sorted_audience - 1 - processed)
      sorted_audience 0 ->
    (forall old_person,
      ProcessedPerson order processed old_person ->
      Znth (Znth (Zlength order - 1 - processed) order 0) audience 0 <=
        Znth old_person audience 0) ->
    (forall person,
      ProcessedPerson order processed person ->
      0 <= Znth person audience 0) ->
    (forall role person,
      0 <= role < positions ->
      ProcessedPerson order processed person ->
      0 <= Znth role (Znth person skill []) 0) ->
    BoundedTeamDPTable audience skill order positions audience_limit processed
      old_values ->
    BoundedTeamNextRowProgress sorted_audience order skill positions
      audience_limit processed old_values next_values (2 ^ positions) ->
    BoundedTeamDPTable audience skill order positions audience_limit
      (processed + 1) next_values.
Proof. exact bounded_team_row_close_core__solver_row_close. Qed.
Theorem bounded_team_next_row_closes__solver_row_close_dispatch :
  forall n audience skill order_values sorted_audience sorted_order
    positions audience_limit processed old_values next_values,
    2 <= n ->
    1 <= positions <= 7 ->
    1 <= audience_limit ->
    n = Zlength audience ->
    positions = Zlength (Znth 0 skill []) ->
    Zlength order_values = n ->
    Zlength sorted_audience = n ->
    Zlength sorted_order = n ->
    Pre audience_limit audience skill ->
    (forall idx, 0 <= idx < n * positions ->
      1 <= Znth idx (concat skill) 0 <= 1000000000) ->
    SortedPeopleState audience order_values sorted_audience sorted_order ->
    (forall q, 0 <= q < n -> 1 <= Znth q sorted_audience 0) ->
    (forall q, 0 <= q < n -> Znth q order_values 0 = q) ->
    0 <= processed < n ->
    BoundedTeamDPTable audience skill sorted_order positions audience_limit
      processed old_values ->
    BoundedTeamNextRowProgress sorted_audience sorted_order skill positions
      audience_limit processed old_values next_values (2 ^ positions) ->
    BoundedTeamDPTable audience skill sorted_order positions audience_limit
      (processed + 1) next_values.
Proof.
  intros n audience skill order_values sorted_audience sorted_order positions
    audience_limit processed old_values next_values Hn Hpositions
    Haudience_limit Hn_audience Hpositions_row0 Horder_values_len
    Hsorted_audience_len Hsorted_order_len Hpre Hflat Hsorted
    Hsorted_audience_positive Hidentity Hprocessed Htable Hprogress.
  assert (Hpre_shape := Hpre).
  unfold Pre in Hpre_shape.
  destruct Hpre_shape as
    [Hskill_audience [width [Hcapacity [Hskill_audience' Hrows]]]].
  assert (Hskill_len : Zlength skill = n) by lia.
  assert (Hrow0_len : Zlength (Znth 0 skill []) = width).
  {
    apply (Forall_Znth_local__solver_role_update_b
      (fun row => Zlength row = width) [] skill Hrows).
    rewrite Hskill_len. lia.
  }
  assert (Hwidth_eq : width = positions) by lia.
  assert (Hrow_lengths : forall person,
    0 <= person < Zlength skill ->
    Zlength (Znth person skill []) = positions).
  {
    intros person Hperson.
    pose proof (Forall_Znth_local__solver_role_update_b
      (fun row => Zlength row = width) [] skill Hrows person Hperson)
      as Hrow_len.
    rewrite Hwidth_eq in Hrow_len. exact Hrow_len.
  }
  assert (Hskill_values :
    Forall (Forall (fun x => 1 <= x <= 1000000000)) skill).
  {
    apply (proj2 (Forall_Znth
      (Forall (fun x => 1 <= x <= 1000000000)) [] skill)).
    intros person Hperson.
    apply (proj2 (Forall_Znth
      (fun x => 1 <= x <= 1000000000) 0 (Znth person skill []))).
    intros role Hrole.
    assert (Hrole_positions : 0 <= role < positions).
    { pose proof (Hrow_lengths person Hperson). lia. }
    specialize (Hflat (person * positions + role)).
    rewrite (Znth_concat_uniform__solver_role_update_b
      skill positions [] person role Hperson Hrow_lengths Hrole_positions) in Hflat.
    apply Hflat. rewrite Hskill_len in Hperson. nia.
  }
  eapply bounded_team_next_row_closes__solver_row_close.
  - exact Hn.
  - exact Hpositions.
  - exact Haudience_limit.
  - exact Hn_audience.
  - exact Hpositions_row0.
  - exact Horder_values_len.
  - exact Hsorted_audience_len.
  - exact Hsorted_order_len.
  - exact Hpre.
  - exact Hskill_values.
  - exact Hsorted.
  - exact Hsorted_audience_positive.
  - exact Hidentity.
  - exact Hprocessed.
  - exact Htable.
  - exact Hprogress.
Qed.
Lemma assigned_role_reverse_transition__solver_row_close_dispatch :
  forall audience sorted_audience skill order positions audience_limit processed
    old_values target choice_score before after audience_people role,
    0 <= positions <= 7 ->
    0 <= processed < Zlength order ->
    (forall person,
      ProcessedPerson order processed person ->
      0 <= Znth person audience 0) ->
    (forall assigned_role person,
      0 <= assigned_role < positions ->
      ProcessedPerson order processed person ->
      0 <= Znth assigned_role (Znth person skill []) 0) ->
    BoundedTeamDPTable audience skill order positions audience_limit processed
      old_values ->
    0 <= target < 2 ^ positions ->
    BoundedAssignmentsMatchMask positions target
      (before ++
       (role, Znth (Zlength order - 1 - processed) order 0) :: after) ->
    NoDup
      (map snd
         (before ++
          (role, Znth (Zlength order - 1 - processed) order 0) :: after) ++
       audience_people) ->
    Forall (ProcessedPerson order (processed + 1))
      (map snd
         (before ++
          (role, Znth (Zlength order - 1 - processed) order 0) :: after) ++
       audience_people) ->
    Zlength audience_people =
      Z.min audience_limit
        (processed + 1 -
         Zlength
           (before ++
            (role, Znth (Zlength order - 1 - processed) order 0) :: after)) ->
    choice_score =
      fold_right Z.add 0
        (map
          (fun assignment =>
             Znth (fst assignment)
               (Znth (snd assignment) skill []) 0)
          (before ++
           (role, Znth (Zlength order - 1 - processed) order 0) :: after)) +
      fold_right Z.add 0
        (map (fun person => Znth person audience 0) audience_people) ->
    exists transition_score,
      TeamTransitionCandidate sorted_audience order skill positions
        audience_limit processed old_values (2 ^ positions) target
        transition_score /\
      choice_score <= transition_score.
Proof.
  intros audience sorted_audience skill order positions audience_limit processed
    old_values target choice_score before after audience_people role Hpositions
    Hprocessed Haudience_nonnegative Hskill_nonnegative Htable Htarget Hmatch
    Hselected Hprocessed_all Haudience_len Hchoice_score.
  set (new_person :=
    Znth (Zlength order - 1 - processed) order 0) in *.
  set (role_score := fun assignment : Z * Z =>
    Znth (fst assignment) (Znth (snd assignment) skill []) 0).
  set (audience_score := fun person : Z => Znth person audience 0).
  change (choice_score =
    fold_right Z.add 0
      (map role_score (before ++ (role, new_person) :: after)) +
    fold_right Z.add 0 (map audience_score audience_people))
    in Hchoice_score.
  destruct (bounded_match_remove__solver_row_close_dispatch positions target before
    after role new_person Hpositions Htarget Hmatch) as
    [source [Hsource [Hsource_bit [Hsource_target Hsource_match]]]].
  assert (Hselected_shape :
    map snd (before ++ (role, new_person) :: after) ++ audience_people =
    map snd before ++ new_person :: (map snd after ++ audience_people)).
  { rewrite map_app. simpl. rewrite <- app_assoc. reflexivity. }
  rewrite Hselected_shape in Hselected, Hprocessed_all.
  assert (Hold_selected :
    NoDup (map snd (before ++ after) ++ audience_people)).
  {
    rewrite map_app, <- app_assoc.
    apply NoDup_remove_1 with (a := new_person).
    exact Hselected.
  }
  assert (Hold_processed :
    Forall (ProcessedPerson order processed)
      (map snd (before ++ after) ++ audience_people)).
  {
    rewrite map_app, <- app_assoc.
    eapply processed_selection_without_new__solver_row_close_dispatch;
      [lia | exact Hselected | exact Hprocessed_all].
  }
  assert (Hold_choice :
    BoundedTeamPrefixChoice audience skill order positions audience_limit
      processed source
      (fold_right Z.add 0 (map role_score (before ++ after)) +
       fold_right Z.add 0 (map audience_score audience_people))).
  {
    split; [exact Hsource |].
    exists (before ++ after), audience_people.
    split; [exact Hsource_match |].
    split; [exact Hold_selected |].
    split; [exact Hold_processed |].
    split.
    - rewrite !Zlength_correct in Haudience_len |- *.
      rewrite length_app in Haudience_len |- *.
      simpl in Haudience_len. lia.
    - reflexivity.
  }
  assert (Hold_nonnegative :
    0 <= fold_right Z.add 0 (map role_score (before ++ after)) +
      fold_right Z.add 0 (map audience_score audience_people)).
  {
    eapply bounded_choice_score_nonnegative__solver_row_close_dispatch;
      [exact Haudience_nonnegative | exact Hskill_nonnegative |].
    exact Hold_choice.
  }
  pose proof (bounded_dp_choice_upper__solver_row_close_dispatch audience skill order
    positions audience_limit processed old_values source
    (fold_right Z.add 0 (map role_score (before ++ after)) +
     fold_right Z.add 0 (map audience_score audience_people))
    Hsource Htable Hold_choice) as Hupper.
  assert (Hlive : Znth source old_values TeamNegInf <> TeamNegInf).
  {
    intro Heq. rewrite Heq in Hupper.
    pose proof team_neg_inf_negative__solver_row_close_dispatch. lia.
  }
  assert (Hrole : 0 <= role < positions).
  {
    destruct Hmatch as [_ Hbounds].
    apply Forall_forall with (x := (role, new_person)) in Hbounds.
    - exact Hbounds.
    - apply in_or_app. right. simpl. auto.
  }
  exists (Znth source old_values TeamNegInf +
    Znth role (Znth new_person skill []) 0).
  split.
  - exists source, (Znth source old_values TeamNegInf).
    split; [exact Hsource |].
    split; [reflexivity |].
    split; [exact Hlive |].
    right. right. exists role.
    split; [exact Hrole |].
    split; [exact Hsource_bit |].
    split; [symmetry; exact Hsource_target |].
    reflexivity.
  - rewrite (fold_map_middle__solver_row_close_dispatch role_score before
      (role, new_person) after) in Hchoice_score.
    unfold role_score, audience_score in *.
    simpl in Hchoice_score. lia.
Qed.
Lemma In_Zrange_aux__solver_result : forall n low x,
  In x (Zrange_aux low n) <-> low <= x < low + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros low x; simpl.
  - split; [tauto | lia].
  - rewrite IH. lia.
Qed.
Lemma In_Zrange__solver_result : forall low high x,
  low <= x < high <-> In x (Zrange low high).
Proof.
  intros low high x. unfold Zrange.
  rewrite In_Zrange_aux__solver_result. lia.
Qed.
Lemma NoDup_Zrange_aux__solver_result : forall n low,
  NoDup (Zrange_aux low n).
Proof.
  induction n as [|n IH]; intros low; simpl.
  - constructor.
  - constructor.
    + rewrite In_Zrange_aux__solver_result. lia.
    + apply IH.
Qed.
Lemma NoDup_Zrange__solver_result : forall low high,
  NoDup (Zrange low high).
Proof.
  intros low high. unfold Zrange. apply NoDup_Zrange_aux__solver_result.
Qed.
Lemma Zlength_Zrange_aux__solver_result : forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m.
Proof.
  intros low m. revert low. induction m as [|m IH]; intros low; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__solver_result : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high Hle. unfold Zrange.
  rewrite Zlength_Zrange_aux__solver_result. lia.
Qed.
Lemma Znth_Zrange_aux__solver_result : forall m low i,
  0 <= i < Z.of_nat m ->
  Znth i (Zrange_aux low m) 0 = low + i.
Proof.
  induction m as [|m IH]; intros low i Hi; [lia |].
  simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
  - rewrite Znth0_cons. lia.
  - rewrite Znth_cons by lia.
    rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
Qed.
Lemma Znth_Zrange__solver_result : forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i.
Proof.
  intros low high i Hle Hi. unfold Zrange.
  rewrite Znth_Zrange_aux__solver_result by lia. lia.
Qed.
Lemma map_fst_combine__solver_result : forall (xs ys : list Z),
  Zlength xs = Zlength ys -> map fst (combine xs ys) = xs.
Proof.
  intros xs. induction xs as [|x xs IH]; intros ys Hlen.
  - reflexivity.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma map_snd_combine__solver_result : forall (xs ys : list Z),
  Zlength xs = Zlength ys -> map snd (combine xs ys) = ys.
Proof.
  intros xs. induction xs as [|x xs IH]; intros ys Hlen.
  - rewrite Zlength_nil in Hlen.
    destruct ys as [|y ys].
    + reflexivity.
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct ys as [|y ys].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + simpl. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma combine_map_fst_snd__solver_result : forall (ps : list (Z * Z)),
  combine (map fst ps) (map snd ps) = ps.
Proof.
  intros ps. induction ps as [|[x y] ps IH]; simpl; f_equal; assumption.
Qed.
Lemma fold_add_permutation__solver_result : forall xs ys : list Z,
  Permutation xs ys ->
  fold_right Z.add 0 xs = fold_right Z.add 0 ys.
Proof.
  intros xs ys Hperm. induction Hperm; simpl; try lia.
Qed.
Lemma In_Znth_index__solver_result : forall {A : Type} (xs : list A) x d,
  In x xs -> exists i, 0 <= i < Zlength xs /\ Znth i xs d = x.
Proof.
  intros A xs. induction xs as [|a xs IH]; intros x d Hin.
  - contradiction.
  - simpl in Hin. destruct Hin as [-> | Hin].
    + exists 0. split.
      * rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
      * reflexivity.
    + destruct (IH x d Hin) as [i [Hi Hnth]].
      exists (i + 1). split.
      * rewrite Zlength_cons. lia.
      * rewrite Znth_cons by lia. replace (i + 1 - 1) with i by lia.
        exact Hnth.
Qed.
Lemma identity_order_zrange__solver_result : forall order n,
  0 <= n ->
  Zlength order = n ->
  (forall q, 0 <= q < n -> Znth q order 0 = q) ->
  order = Zrange 0 n.
Proof.
  intros order n Hn Hlen Hpoint.
  apply (proj2 (list_eq_ext order (Zrange 0 n) 0)). split.
  - rewrite Zlength_Zrange__solver_result by lia. lia.
  - intros i Hi.
    rewrite Znth_Zrange__solver_result by lia. apply Hpoint. lia.
Qed.
Lemma sorted_order_permutation__solver_result :
  forall aud order sorted_aud sorted_order n,
    0 <= n ->
    n = Zlength aud ->
    Zlength order = n ->
    (forall q, 0 <= q < n -> Znth q order 0 = q) ->
    SortedPeopleState aud order sorted_aud sorted_order ->
    Permutation (Zrange 0 n) sorted_order.
Proof.
  intros aud order sorted_aud sorted_order n Hn Haud Horder Hidentity Hsorted.
  destruct Hsorted as [Hsorted_aud [Hsorted_order [Hpairs _]]].
  assert (Hleft : map snd (combine aud order) = order).
  { apply map_snd_combine__solver_result. lia. }
  assert (Hright : map snd (combine sorted_aud sorted_order) = sorted_order).
  { apply map_snd_combine__solver_result. lia. }
  pose proof (Permutation_map snd Hpairs) as Hmap.
  rewrite Hleft, Hright in Hmap.
  rewrite (identity_order_zrange__solver_result order n Hn Horder Hidentity)
    in Hmap.
  exact Hmap.
Qed.
Lemma processed_person_iff_range__solver_result :
  forall sorted_order n person,
    0 <= n ->
    Zlength sorted_order = n ->
    Permutation (Zrange 0 n) sorted_order ->
    (ProcessedPerson sorted_order n person <-> 0 <= person < n).
Proof.
  intros sorted_order n person Hn Hlen Hperm. split.
  - intros [step [Hstep ->]].
    assert (Hidx : 0 <= n - 1 - step < Zlength sorted_order) by lia.
    pose proof (Znth_In_Zlength sorted_order 0 (n - 1 - step) Hidx) as Hin.
    assert (Hinrange : In (Znth (n - 1 - step) sorted_order 0) (Zrange 0 n)).
    { eapply Permutation_in; [exact (Permutation_sym Hperm) | exact Hin]. }
    rewrite <- In_Zrange__solver_result in Hinrange. rewrite Hlen. exact Hinrange.
  - intros Hperson.
    assert (Hinrange : In person (Zrange 0 n)).
    { rewrite <- In_Zrange__solver_result. exact Hperson. }
    assert (Hinsorted : In person sorted_order).
    { eapply Permutation_in; [exact Hperm | exact Hinrange]. }
    destruct (In_Znth_index__solver_result sorted_order person 0 Hinsorted)
      as [i [Hi Hnth]].
    exists (n - 1 - i). split; [lia |].
    replace (Zlength sorted_order - 1 - (n - 1 - i)) with i by lia.
    symmetry. exact Hnth.
Qed.
Lemma full_mask_testbit__solver_result : forall positions role,
  0 <= role < positions ->
  Z.testbit (2 ^ positions - 1) role = true.
Proof.
  intros positions role Hrole.
  replace (2 ^ positions - 1) with (Z.ones positions).
  2: { rewrite Z.ones_equiv. lia. }
  rewrite Z.testbit_ones_nonneg by lia.
  apply Z.ltb_lt. lia.
Qed.
Lemma full_mask_assignment_roles__solver_result :
  forall positions assignments,
    0 <= positions ->
    BoundedAssignmentsMatchMask positions (2 ^ positions - 1) assignments ->
    Permutation (map fst assignments) (Zrange 0 positions).
Proof.
  intros positions assignments Hpositions [[Hnodup Hbits] Hbounds].
  apply NoDup_Permutation.
  - exact Hnodup.
  - apply NoDup_Zrange__solver_result.
  - intros role. split.
    + intros Hin.
      rewrite Forall_forall in Hbounds.
      destruct (in_map_iff fst assignments role) as [Hto _].
      destruct (Hto Hin) as [[r person] [Heq Hinpair]]. simpl in Heq. subst r.
      specialize (Hbounds (role, person) Hinpair). simpl in Hbounds.
      rewrite <- In_Zrange__solver_result. exact Hbounds.
    + intros Hin.
      rewrite <- In_Zrange__solver_result in Hin.
      specialize (Hbits role Hin).
      destruct (proj1 Hbits (full_mask_testbit__solver_result positions role Hin))
        as [person Hinpair].
      apply in_map with (f := fst) in Hinpair. exact Hinpair.
Qed.
Lemma canonicalize_assignments__solver_result :
  forall positions (assignments : list (Z * Z)),
    Permutation (map fst assignments) (Zrange 0 positions) ->
    exists canonical,
      Permutation assignments canonical /\
      map fst canonical = Zrange 0 positions.
Proof.
  intros positions assignments Hperm.
  destruct (@Permutation_map_inv (Z * Z) Z fst
    (Zrange 0 positions) assignments (Permutation_sym Hperm))
    as [canonical [Hmap Hcanonical]].
  exists canonical. split.
  - exact Hcanonical.
  - symmetry. exact Hmap.
Qed.
Lemma bounded_full_choice_iff__solver_result :
  forall aud skill sorted_order positions audience_limit n score,
    0 <= positions ->
    0 <= audience_limit ->
    positions + audience_limit <= n ->
    n = Zlength aud ->
    positions = Zlength (Znth 0 skill []) ->
    Zlength sorted_order = n ->
    Permutation (Zrange 0 n) sorted_order ->
    (BoundedTeamPrefixChoice aud skill sorted_order positions audience_limit n
       (2 ^ positions - 1) score <->
     TeamChoice aud skill audience_limit score).
Proof.
  intros aud skill sorted_order positions audience_limit n score
    Hpositions Hlimit Hspace Haud Hskill Horder Hperm.
  assert (Hprocessed : forall person,
    ProcessedPerson sorted_order n person <-> 0 <= person < n).
  { intro person. apply processed_person_iff_range__solver_result; try assumption; lia. }
  split.
  - intros [Hmask [assignments [audience_people
      [Hmatch [Hnodup [Hall [Halen Hscore]]]]]]].
    pose proof (full_mask_assignment_roles__solver_result
      positions assignments Hpositions Hmatch) as Hroles.
    destruct (canonicalize_assignments__solver_result positions assignments Hroles)
      as [canonical [Hcanonical Hcanonical_roles]].
    set (players := map snd canonical).
    assert (Hcanonical_eq :
      canonical = combine (Zrange 0 positions) players).
    { subst players. rewrite <- Hcanonical_roles at 1.
      symmetry. apply combine_map_fst_snd__solver_result. }
    assert (Hcanonical_len : Zlength canonical = positions).
    { assert (Hrange_len : Zlength (Zrange 0 positions) = positions).
      { rewrite Zlength_Zrange__solver_result by lia. lia. }
      rewrite <- Hrange_len, <- Hcanonical_roles.
      rewrite !Zlength_correct, length_map. reflexivity. }
    assert (Hplayers_len : Zlength players = positions).
    { subst players. rewrite Zlength_correct, length_map, <- Zlength_correct.
      exact Hcanonical_len. }
    unfold TeamChoice. exists players, audience_people.
    repeat split.
    + lia.
    + assert (Hassign_len : Zlength assignments = positions).
      { pose proof (Permutation_length Hcanonical) as Hlength.
        rewrite !Zlength_correct in Hcanonical_len |- *. lia. }
      rewrite Hassign_len in Halen. rewrite Z.min_l in Halen by lia. exact Halen.
    + assert (Hpeople_perm : Permutation (map snd assignments) players).
      { subst players. apply Permutation_map. exact Hcanonical. }
      eapply Permutation_NoDup.
      * apply Permutation_app_tail. exact Hpeople_perm.
      * exact Hnodup.
    + rewrite Forall_forall in Hall |- *.
      intros person Hin.
      rewrite <- Haud. apply (proj1 (Hprocessed person)).
      apply Hall.
      assert (Hpeople_perm : Permutation (map snd assignments ++ audience_people)
        (players ++ audience_people)).
      { apply Permutation_app_tail. subst players.
        apply Permutation_map. exact Hcanonical. }
      eapply Permutation_in; [exact (Permutation_sym Hpeople_perm) | exact Hin].
    + rewrite Hscore. f_equal.
      assert (Hcontrib_perm :
        Permutation
          (map (fun assignment =>
             Znth (fst assignment) (Znth (snd assignment) skill []) 0)
             assignments)
          (map (fun assignment =>
             Znth (fst assignment) (Znth (snd assignment) skill []) 0)
             canonical)).
      { apply Permutation_map. exact Hcanonical. }
      rewrite (fold_add_permutation__solver_result _ _ Hcontrib_perm).
      rewrite Hcanonical_eq, <- Hplayers_len. reflexivity.
  - intros [players [audience_people
      [Hplayers_len [Halen [Hnodup [Hall Hscore]]]]]].
    set (assignments := combine (Zrange 0 positions) players).
    assert (Hrange_len : Zlength (Zrange 0 positions) = Zlength players).
    { rewrite Zlength_Zrange__solver_result by lia. lia. }
    unfold BoundedTeamPrefixChoice. split.
    + pose proof (Z.pow_pos_nonneg 2 positions ltac:(lia) Hpositions). lia.
    + exists assignments, audience_people. split.
      * split.
        -- unfold AssignmentsMatchMask. split.
           ++ subst assignments. rewrite map_fst_combine__solver_result by exact Hrange_len.
              apply NoDup_Zrange__solver_result.
           ++ intros role Hrole. split; intro H.
              ** exists (Znth role players 0). subst assignments.
                 assert (Hnth :
                   Znth role (combine (Zrange 0 positions) players) (0, 0) =
                   (role, Znth role players 0)).
                 { assert (Hrole_range :
                     0 <= role < Zlength (Zrange 0 positions)).
                   { rewrite Zlength_Zrange__solver_result by lia. lia. }
                   rewrite (Znth_combine__sift_transition_exit
                     (Zrange 0 positions) players role 0 0 Hrange_len Hrole_range).
                   rewrite Znth_Zrange__solver_result by lia. simpl. f_equal; lia. }
                 rewrite <- Hnth.
                 apply Znth_In_Zlength with (default := (0, 0)) (i := role).
                 rewrite Zlength_combine_eq__sift_transition_exit by exact Hrange_len.
                 rewrite Zlength_Zrange__solver_result by lia. lia.
              ** apply full_mask_testbit__solver_result. exact Hrole.
        -- rewrite Forall_forall. intros [role person] Hin. simpl.
           subst assignments. apply in_combine_l in Hin.
           rewrite <- In_Zrange__solver_result in Hin. exact Hin.
      * split.
        -- subst assignments. rewrite map_snd_combine__solver_result by exact Hrange_len.
           exact Hnodup.
        -- split.
           ++ subst assignments. rewrite map_snd_combine__solver_result by exact Hrange_len.
              rewrite Forall_forall in Hall |- *.
              intros person Hin. apply (proj2 (Hprocessed person)).
              rewrite Haud. apply Hall. exact Hin.
           ++ split.
              ** subst assignments.
                 rewrite Zlength_combine_eq__sift_transition_exit by exact Hrange_len.
                 rewrite Zlength_Zrange__solver_result by lia.
                 rewrite Z.min_l by lia. exact Halen.
              ** subst assignments.
                 assert (Hplayers_positions : Zlength players = positions) by lia.
                 rewrite Hplayers_positions in Hscore. exact Hscore.
Qed.
Lemma team_choice_exists__solver_result :
  forall aud skill positions audience_limit n,
    0 <= positions ->
    0 <= audience_limit ->
    positions + audience_limit <= n ->
    n = Zlength aud ->
    positions = Zlength (Znth 0 skill []) ->
    exists score, TeamChoice aud skill audience_limit score.
Proof.
  intros aud skill positions audience_limit n Hpositions Hlimit Hspace Haud Hskill.
  set (players := Zrange 0 positions).
  set (audience_people := Zrange positions (positions + audience_limit)).
  set (score :=
    fold_right Z.add 0
      (map (fun q => Znth (fst q) (Znth (snd q) skill []) 0)
        (combine (Zrange 0 (Zlength players)) players)) +
    fold_right Z.add 0 (map (fun i => Znth i aud 0) audience_people)).
  exists score. unfold TeamChoice. exists players, audience_people.
  repeat split.
  - subst players. rewrite Zlength_Zrange__solver_result by lia. lia.
  - subst audience_people. rewrite Zlength_Zrange__solver_result by lia. lia.
  - apply NoDup_app.
    + subst players. apply NoDup_Zrange__solver_result.
    + subst audience_people. apply NoDup_Zrange__solver_result.
    + intros person Hplayer Haudience.
      subst players audience_people.
      rewrite <- In_Zrange__solver_result in Hplayer, Haudience. lia.
  - rewrite Forall_forall. intros person Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + subst players. rewrite <- In_Zrange__solver_result in Hin. lia.
    + subst audience_people. rewrite <- In_Zrange__solver_result in Hin. lia.
Qed.
Lemma bounded_full_mask_to_team_choice__solver_result :
  forall aud skill order sorted_aud sorted_order positions audience_limit n values,
    0 <= positions ->
    0 <= audience_limit ->
    positions + audience_limit <= n ->
    n = Zlength aud ->
    positions = Zlength (Znth 0 skill []) ->
    Zlength order = n ->
    (forall q, 0 <= q < n -> Znth q order 0 = q) ->
    SortedPeopleState aud order sorted_aud sorted_order ->
    Zlength values = 128 ->
    2 ^ positions <= 128 ->
    BoundedTeamDPTable aud skill sorted_order positions audience_limit n values ->
    Spec audience_limit aud skill (Znth (2 ^ positions - 1) values 0).
Proof.
  intros aud skill order sorted_aud sorted_order positions audience_limit n values
    Hpositions Hlimit Hspace Haud Hskill Horder Hidentity Hsorted
    Hvalues Hpower Htable.
  assert (Hsorted_order : Zlength sorted_order = n).
  { pose proof Hsorted as Hsorted_copy.
    unfold SortedPeopleState in Hsorted_copy.
    destruct Hsorted_copy as [_ [Hsorted_order_length _]]. lia. }
  assert (Hperm : Permutation (Zrange 0 n) sorted_order).
  { eapply sorted_order_permutation__solver_result.
    - lia.
    - exact Haud.
    - exact Horder.
    - exact Hidentity.
    - exact Hsorted. }
  assert (Hmask : 0 <= 2 ^ positions - 1 < 2 ^ positions).
  { pose proof (Z.pow_pos_nonneg 2 positions ltac:(lia) Hpositions). lia. }
  specialize (Htable (2 ^ positions - 1) Hmask).
  unfold BoundedTeamDPCell in Htable.
  assert (Hdefault :
    Znth (2 ^ positions - 1) values TeamNegInf =
    Znth (2 ^ positions - 1) values 0).
  { apply Znth_indep. lia. }
  rewrite Hdefault in Htable.
  unfold Spec. destruct Htable as [Hmax | [Hneg Hempty]].
  - unfold max_value_of_subset, max_object_of_subset in Hmax |- *.
    destruct Hmax as [winner [[Hchoice Hgreatest] Hvalue]].
    exists winner. split.
    + split.
      * apply (proj1 (bounded_full_choice_iff__solver_result
          aud skill sorted_order positions audience_limit n winner
          Hpositions Hlimit Hspace Haud Hskill Hsorted_order Hperm)).
        exact Hchoice.
      * intros candidate Hcandidate.
        apply Hgreatest.
        apply (proj2 (bounded_full_choice_iff__solver_result
          aud skill sorted_order positions audience_limit n candidate
          Hpositions Hlimit Hspace Haud Hskill Hsorted_order Hperm)).
        exact Hcandidate.
    + exact Hvalue.
  - destruct (team_choice_exists__solver_result aud skill positions audience_limit n
      Hpositions Hlimit Hspace Haud Hskill) as [score Hchoice].
    exfalso. apply (Hempty score).
    apply (proj2 (bounded_full_choice_iff__solver_result
      aud skill sorted_order positions audience_limit n score
      Hpositions Hlimit Hspace Haud Hskill Hsorted_order Hperm)).
    exact Hchoice.
Qed.
