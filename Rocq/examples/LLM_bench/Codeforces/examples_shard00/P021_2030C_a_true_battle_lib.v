Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition HasAdjacentOnes (values : list Z) : Prop :=
  exists i,
    0 <= i /\
    i + 1 < Zlength values /\
    Znth i values 0 = 49 /\
    Znth (i + 1) values 0 = 49.

Definition NoAdjacentOnesBefore (values : list Z) (upto : Z) : Prop :=
  forall i,
    0 <= i < upto ->
    Znth i values 0 <> 49 \/ Znth (i + 1) values 0 <> 49.

Definition WinningCriterion (values : list Z) : Prop :=
  Znth 0 values 0 = 49 \/
  Znth (Zlength values - 1) values 0 = 49 \/
  HasAdjacentOnes values.

Definition Pre (values : list Z) : Prop :=
  2 <= Zlength values <= 200000 /\
  (* Character codes: '0' = 48, '1' = 49. *)
  Forall (fun c => c = 48 \/ c = 49) values.

Definition Spec (values : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\ (out = 1 <-> WinningCriterion values).

Require Import Coq.micromega.Lia.
Lemma no_adjacent_ones_before_succ__loop_transition :
  forall (values : list Z) (i : Z),
    0 <= i ->
    NoAdjacentOnesBefore values i ->
    (Znth i values 0 <> 49 \/ Znth (i + 1) values 0 <> 49) ->
    NoAdjacentOnesBefore values (i + 1).
Proof.
  unfold NoAdjacentOnesBefore.
  intros values i Hi Hold Hnew k Hk.
  destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
  - apply Hold. lia.
  - assert (k = i) by lia.
    subst k.
    exact Hnew.
Qed.
Lemma spec_zero_from_completed_scan__final_results :
  forall (values : list Z) (n i : Z),
    n = Zlength values ->
    0 <= i ->
    i <= n - 1 ->
    i + 1 >= n ->
    Znth 0 values 0 <> 49 ->
    Znth (Zlength values - 1) values 0 <> 49 ->
    NoAdjacentOnesBefore values i ->
    Spec values 0.
Proof.
  intros values n i Hn Hi0 Hi_upper Hi_done Hfirst Hlast Hscan.
  assert (Hi : i = n - 1) by lia.
  unfold Spec.
  split.
  - left; reflexivity.
  - split.
    + lia.
    + intro Hwin.
      exfalso.
      unfold WinningCriterion in Hwin.
      destruct Hwin as [Hwin | [Hwin | Hwin]].
      * exact (Hfirst Hwin).
      * exact (Hlast Hwin).
      * unfold HasAdjacentOnes in Hwin.
        destruct Hwin as [j [Hj0 [Hj_bound [Hj Hjsucc]]]].
        specialize (Hscan j).
        assert (Hj_before : 0 <= j < i) by lia.
        specialize (Hscan Hj_before).
        destruct Hscan as [Hneq | Hneq].
        -- exact (Hneq Hj).
        -- exact (Hneq Hjsucc).
Qed.
