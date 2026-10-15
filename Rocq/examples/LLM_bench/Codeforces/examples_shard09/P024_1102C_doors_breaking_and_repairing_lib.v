Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* If the attack is stronger than the repair, every door can eventually be
   destroyed.  Otherwise only doors whose initial durability is at most x can
   be destroyed, and optimal repair saves every second such door. *)
Definition WeakDoorCount (x : Z) (a : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength a /\ Znth i a 0 <= x).
Definition Pre (x y:Z) (a:list Z) : Prop :=
  (* Every clause below is stated explicitly in the P024 solver Require, which
     therefore omits the Pre(...) call:
       1 <= Zlength a <= 100 /\
       1 <= x <= 100000 /\ 1 <= y <= 100000 /\
       Forall (fun z => 1 <= z <= 100000) a. *)
  True.
Definition Spec (x y:Z) (a:list Z) (out:Z) : Prop :=
  out = if Z.ltb y x then Zlength a else (WeakDoorCount x a + 1) / 2.

Require Import Coq.micromega.Lia.
Lemma set_card_empty__count_transitions :
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
Lemma set_card_iff__count_transitions :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros z.
      rewrite <- (@enum_ok A P FP z), <- (@enum_ok A Q FQ z).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun _ acc => 1 + acc) 0 l =
            1 + fold_right (fun _ acc => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma set_card_Z_as_sum__count_transitions :
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
Lemma set_card_Z_extend_true__count_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__count_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [_ | Hnot]; [lia | contradiction].
Qed.
Lemma set_card_Z_extend_false__count_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__count_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [Hp | _]; [contradiction | lia].
Qed.
Lemma weak_door_count_empty__count_transitions :
  forall x a, WeakDoorCount x (sublist 0 0 a) = 0.
Proof.
  intros x a.
  unfold WeakDoorCount.
  apply set_card_empty__count_transitions.
  intros z (Hz & _).
  rewrite Zlength_sublist0 in Hz by (pose proof (Zlength_nonneg a); lia).
  lia.
Qed.
Lemma weak_door_count_sublist_succ_le__count_transitions :
  forall x a i,
    0 <= i < Zlength a ->
    Znth i a 0 <= x ->
    WeakDoorCount x (sublist 0 (i + 1) a) =
    WeakDoorCount x (sublist 0 i a) + 1.
Proof.
  intros x a i Hi Hle.
  unfold WeakDoorCount.
  rewrite !Zlength_sublist0 by lia.
  assert (Hsucc :
    #(fun z : Z => 0 <= z < i + 1 /\ Znth z (sublist 0 (i + 1) a) 0 <= x) =
    #(fun z : Z => 0 <= z < i + 1 /\ Znth z a 0 <= x)).
  {
    apply set_card_iff__count_transitions.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  assert (Hold :
    #(fun z : Z => 0 <= z < i /\ Znth z (sublist 0 i a) 0 <= x) =
    #(fun z : Z => 0 <= z < i /\ Znth z a 0 <= x)).
  {
    apply set_card_iff__count_transitions.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  rewrite Hsucc, Hold.
  apply set_card_Z_extend_true__count_transitions.
  - lia.
  - exact Hle.
Qed.
Lemma weak_door_count_sublist_succ_gt__count_transitions :
  forall x a i,
    0 <= i < Zlength a ->
    Znth i a 0 > x ->
    WeakDoorCount x (sublist 0 (i + 1) a) =
    WeakDoorCount x (sublist 0 i a).
Proof.
  intros x a i Hi Hgt.
  unfold WeakDoorCount.
  rewrite !Zlength_sublist0 by lia.
  assert (Hsucc :
    #(fun z : Z => 0 <= z < i + 1 /\ Znth z (sublist 0 (i + 1) a) 0 <= x) =
    #(fun z : Z => 0 <= z < i + 1 /\ Znth z a 0 <= x)).
  {
    apply set_card_iff__count_transitions.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  assert (Hold :
    #(fun z : Z => 0 <= z < i /\ Znth z (sublist 0 i a) 0 <= x) =
    #(fun z : Z => 0 <= z < i /\ Znth z a 0 <= x)).
  {
    apply set_card_iff__count_transitions.
    intros z. split; intros [Hz Hvalue]; split; try exact Hz.
    - rewrite Znth_sublist0 in Hvalue by lia. exact Hvalue.
    - rewrite Znth_sublist0 by lia. exact Hvalue.
  }
  rewrite Hsucc, Hold.
  apply set_card_Z_extend_false__count_transitions; [lia | lia].
Qed.
Lemma weak_door_count_sublist_full__return_specs :
  forall (x : Z) (a : list Z),
    WeakDoorCount x (sublist 0 (Zlength a) a) = WeakDoorCount x a.
Proof.
  intros x a.
  assert (Hsub : sublist 0 (Zlength a) a = a).
  {
    pose proof (sublist_app_exact1 a (@nil Z)) as H.
    rewrite app_nil_r in H.
    exact H.
  }
  rewrite Hsub.
  reflexivity.
Qed.
