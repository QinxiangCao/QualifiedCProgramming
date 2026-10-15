Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

(* Position i runs a program that already ran on the same cpu, and j is that
   previous run: no position between them used that cpu. *)
Definition HotStart (prog cpu : list Z) (i j : Z) : Prop :=
  0 <= j < i /\ Znth j cpu 0 = Znth i cpu 0 /\
  (forall q, j < q < i -> Znth q cpu 0 <> Znth i cpu 0) /\
  Znth j prog 0 = Znth i prog 0.

(* What position i costs: the hot time after such a previous run, the cold time
   otherwise. *)
Definition RunTime (prog cold hot cpu times : list Z) (i : Z) : Prop :=
  (exists j, HotStart prog cpu i j /\
     Znth i times 0 = Znth (Znth i prog 0 - 1) hot 0) \/
  ((~ exists j, HotStart prog cpu i j) /\
   Znth i times 0 = Znth (Znth i prog 0 - 1) cold 0).

Definition RunTimes (prog cold hot cpu times : list Z) : Prop :=
  Zlength times = Zlength prog /\
  forall i, 0 <= i < Zlength prog -> RunTime prog cold hot cpu times i.

(* Every program is run on one of the two cpus, in the given order. *)
Definition ValidSchedule (prog cpu : list Z) : Prop :=
  Zlength cpu = Zlength prog /\ Forall (fun x => x = 1 \/ x = 2) cpu.

Definition RunCost (prog cold hot cpu : list Z) (cost : Z) : Prop :=
  ValidSchedule prog cpu /\
  exists times, RunTimes prog cold hot cpu times /\
    cost = fold_right Z.add 0 times.
Definition Pre (prog cold hot : list Z) : Prop :=
  (* The solver Require states these constraints explicitly:
       1 <= Zlength prog <= 300000 /\
       1 <= Zlength cold <= 300000 /\
       Zlength hot = Zlength cold /\
       Forall (fun x => 1 <= x <= Zlength cold) prog /\
       forall i, 0 <= i < Zlength cold ->
         1 <= Znth i hot 0 <= Znth i cold 0 /\
         Znth i cold 0 <= 1000000000. *)
  True.

Definition Spec (prog cold hot : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (fun v => exists cpu, RunCost prog cold hot cpu v) (fun x => x) out.

(* The scratch vector uses this value exactly for an unreachable other-CPU
   state.  All real costs in the frozen input range are far below it. *)
Definition DP_INF : Z := 4557430888798830399.

(* After a nonempty prefix, the cpu that ran the final position is the active
   cpu.  [other] is zero when the other cpu has never run; otherwise it is the
   program at the last position assigned to that other cpu. *)
Definition OtherCpuLastProgram (prog cpu : list Z) (other : Z) : Prop :=
  0 < Zlength prog /\
  Zlength cpu = Zlength prog /\
  let active := Znth (Zlength prog - 1) cpu 0 in
  (other = 0 /\
     forall q, 0 <= q < Zlength prog -> Znth q cpu 0 = active) \/
  (exists q,
     0 <= q < Zlength prog /\
     Znth q cpu 0 <> active /\
     other = Znth q prog 0 /\
     forall r, q < r < Zlength prog -> Znth r cpu 0 = active).

(* A schedule cost belonging to the state indexed by [other] after exactly
   [prefix_len] jobs have been processed. *)
Definition PrefixStateCost
    (prog cold hot : list Z) (prefix_len other total : Z) : Prop :=
  exists cpu,
    RunCost (sublist 0 prefix_len prog) cold hot cpu total /\
    OtherCpuLastProgram (sublist 0 prefix_len prog) cpu other.

Definition PrefixStateMinimum
    (prog cold hot : list Z) (prefix_len other total : Z) : Prop :=
  min_value_of_subset Z.le
    (PrefixStateCost prog cold hot prefix_len other)
    (fun x => x) total.

(* A finite cell stores its state minimum relative to the common offset;
   DP_INF is used exactly when the corresponding schedule class is empty. *)
Definition NormalizedScheduleCell
    (prog cold hot : list Z) (prefix_len other off value : Z) : Prop :=
  (value < DP_INF /\
   PrefixStateMinimum prog cold hot prefix_len other (off + value)) \/
  (value = DP_INF /\
   ~ exists total, PrefixStateCost prog cold hot prefix_len other total).

(* Mathematical meaning of the normalized DP vector at a main-loop head.
   Machine ranges, list lengths, and all spatial ownership remain explicit in
   the C invariant; this predicate owns only schedule-cost semantics. *)
Definition NormalizedScheduleState
    (prog cold hot : list Z) (prefix_len : Z)
    (dp : list Z) (off mind : Z) : Prop :=
  (forall other,
     0 <= other <= Zlength cold ->
     NormalizedScheduleCell prog cold hot prefix_len other off
       (Znth other dp DP_INF)) /\
  min_value_of_subset Z.le
    (fun value =>
       exists other,
         0 <= other <= Zlength cold /\
         value = Znth other dp DP_INF /\
         value < DP_INF)
    (fun x => x) mind /\
  Spec (sublist 0 prefix_len prog) cold hot (off + mind).

Lemma normalized_schedule_state_cell :
  forall prog cold hot prefix_len dp off mind other,
    NormalizedScheduleState prog cold hot prefix_len dp off mind ->
    0 <= other <= Zlength cold ->
    NormalizedScheduleCell prog cold hot prefix_len other off
      (Znth other dp DP_INF).
Proof.
  intros prog cold hot prefix_len dp off mind other Hstate Hother.
  unfold NormalizedScheduleState in Hstate.
  destruct Hstate as [Hcells _].
  apply Hcells; exact Hother.
Qed.

Lemma normalized_schedule_state_full_spec :
  forall prog cold hot dp off mind,
    NormalizedScheduleState prog cold hot (Zlength prog) dp off mind ->
    Spec prog cold hot (off + mind).
Proof.
  intros prog cold hot dp off mind Hstate.
  unfold NormalizedScheduleState in Hstate.
  destruct Hstate as [_ [_ Hspec]].
  replace (sublist 0 (Zlength prog) prog) with prog in Hspec.
  - exact Hspec.
  - symmetry. apply sublist_self. reflexivity.
Qed.

Require Import Coq.micromega.Lia.

Lemma sublist_0_succ__normalized_step :
  forall (A : Type) (d : A) (xs : list A) i,
    0 <= i < Zlength xs ->
    sublist 0 (i + 1) xs = sublist 0 i xs ++ [Znth i xs d].
Proof.
  intros A d xs i Hi.
  rewrite (sublist_split 0 (i + 1) i xs) by lia.
  rewrite (sublist_single d i xs) by lia.
  reflexivity.
Qed.

Lemma Znth_app_left__normalized_step :
  forall (A : Type) (d : A) (xs ys : list A) i,
    0 <= i < Zlength xs ->
    Znth i (xs ++ ys) d = Znth i xs d.
Proof.
  intros A d xs ys i Hi.
  rewrite Zlength_correct in Hi.
  unfold Znth.
  rewrite app_nth1 by lia.
  reflexivity.
Qed.

Lemma Znth_app_last__normalized_step :
  forall (A : Type) (d : A) (xs : list A) x,
    Znth (Zlength xs) (xs ++ [x]) d = x.
Proof.
  intros A d xs x.
  unfold Znth.
  rewrite Zlength_correct, Nat2Z.id.
  rewrite app_nth2 by lia.
  replace (length xs - length xs)%nat with O by lia.
  reflexivity.
Qed.

Lemma fold_right_add_snoc__normalized_step :
  forall xs x,
    fold_right Z.add 0 (xs ++ [x]) = fold_right Z.add 0 xs + x.
Proof.
  intros xs x. induction xs as [|a xs IH].
  - simpl. lia.
  - simpl in *. lia.
Qed.

Definition other_cpu_label (active : Z) : Z :=
  if Z.eq_dec active 1 then 2 else 1.

Lemma other_cpu_label_valid__normalized_step :
  forall active,
    active = 1 \/ active = 2 ->
    other_cpu_label active = 1 \/ other_cpu_label active = 2.
Proof.
  intros active Hactive.
  unfold other_cpu_label.
  destruct (Z.eq_dec active 1); auto.
Qed.

Lemma other_cpu_label_neq__normalized_step :
  forall active,
    active = 1 \/ active = 2 ->
    other_cpu_label active <> active.
Proof.
  intros active Hactive.
  unfold other_cpu_label.
  destruct (Z.eq_dec active 1); destruct Hactive; subst; lia.
Qed.

Lemma binary_label_other__normalized_step :
  forall active label,
    (active = 1 \/ active = 2) ->
    (label = 1 \/ label = 2) ->
    label <> active ->
    label = other_cpu_label active.
Proof.
  intros active label Hactive Hlabel Hneq.
  unfold other_cpu_label.
  destruct (Z.eq_dec active 1); destruct Hactive; destruct Hlabel; subst; lia.
Qed.

Lemma valid_schedule_active_label__normalized_step :
  forall prog cpu,
    ValidSchedule prog cpu ->
    0 < Zlength prog ->
    Znth (Zlength prog - 1) cpu 0 = 1 \/
    Znth (Zlength prog - 1) cpu 0 = 2.
Proof.
  intros prog cpu [Hlen Hall] Hpos.
  rewrite Forall_nth in Hall.
  specialize (Hall (Z.to_nat (Zlength prog - 1)) 0).
  assert (Hindex : (Z.to_nat (Zlength prog - 1) < length cpu)%nat).
  { apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  specialize (Hall Hindex).
  unfold Znth. exact Hall.
Qed.

Lemma valid_schedule_snoc__normalized_step :
  forall prog cpu x label,
    ValidSchedule prog cpu ->
    (label = 1 \/ label = 2) ->
    ValidSchedule (prog ++ [x]) (cpu ++ [label]).
Proof.
  intros prog cpu x label [Hlen Hall] Hlabel.
  split.
  - rewrite !Zlength_app, Hlen. reflexivity.
  - apply Forall_app. split; [exact Hall|].
    constructor; [exact Hlabel|constructor].
Qed.

Lemma hot_start_snoc_old_iff__normalized_step :
  forall prog cpu x label pos previous,
    Zlength cpu = Zlength prog ->
    0 <= pos < Zlength prog ->
    (HotStart prog cpu pos previous <->
     HotStart (prog ++ [x]) (cpu ++ [label]) pos previous).
Proof.
  intros prog cpu x label pos previous Hlen Hpos.
  unfold HotStart. split.
  - intros [[Hprev0 Hprevlt] [Hcpu [Hbetween Hprog]]].
    split; [lia|]. split.
    + rewrite !Znth_app_left__normalized_step by lia. exact Hcpu.
    + split.
      * intros q Hq.
        rewrite !Znth_app_left__normalized_step by lia.
        apply Hbetween; exact Hq.
      * rewrite !Znth_app_left__normalized_step by lia. exact Hprog.
  - intros [[Hprev0 Hprevlt] [Hcpu [Hbetween Hprog]]].
    split; [lia|]. split.
    + rewrite !Znth_app_left__normalized_step in Hcpu by lia. exact Hcpu.
    + split.
      * intros q Hq.
        specialize (Hbetween q Hq).
        rewrite !Znth_app_left__normalized_step in Hbetween by lia.
        exact Hbetween.
      * rewrite !Znth_app_left__normalized_step in Hprog by lia. exact Hprog.
Qed.

Lemma run_time_snoc_old_iff__normalized_step :
  forall prog cold hot cpu times x label t pos,
    Zlength cpu = Zlength prog ->
    Zlength times = Zlength prog ->
    0 <= pos < Zlength prog ->
    (RunTime prog cold hot cpu times pos <->
     RunTime (prog ++ [x]) cold hot (cpu ++ [label])
       (times ++ [t]) pos).
Proof.
  intros prog cold hot cpu times x label t pos Hcpu Htimes Hpos.
  unfold RunTime.
  rewrite !Znth_app_left__normalized_step by lia.
  assert (Hhot : forall j,
      HotStart prog cpu pos j <->
      HotStart (prog ++ [x]) (cpu ++ [label]) pos j).
  { intros j. apply hot_start_snoc_old_iff__normalized_step; assumption. }
  split.
  - intros [[j [Hj Hvalue]] | [Hnone Hvalue]].
    + left. exists j. split; [apply Hhot; exact Hj|exact Hvalue].
    + right. split; [|exact Hvalue].
      intros [j Hj]. apply Hnone. exists j. apply Hhot. exact Hj.
  - intros [[j [Hj Hvalue]] | [Hnone Hvalue]].
    + left. exists j. split; [apply Hhot; exact Hj|exact Hvalue].
    + right. split; [|exact Hvalue].
      intros [j Hj]. apply Hnone. exists j. apply Hhot. exact Hj.
Qed.

Lemma other_cpu_last_continue__normalized_step :
  forall prog cpu other x,
    OtherCpuLastProgram prog cpu other ->
    OtherCpuLastProgram (prog ++ [x])
      (cpu ++ [Znth (Zlength prog - 1) cpu 0]) other.
Proof.
  intros prog cpu other x Hstate.
  unfold OtherCpuLastProgram in *.
  destruct Hstate as [Hpos [Hlen Hcases]].
  set (active := Znth (Zlength prog - 1) cpu 0) in *.
  assert (Hnewlen : Zlength (prog ++ [x]) = Zlength prog + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hnewactive :
      Znth (Zlength (prog ++ [x]) - 1) (cpu ++ [active]) 0 = active).
  { rewrite Hnewlen. replace (Zlength prog + 1 - 1) with (Zlength prog) by lia.
    rewrite <- Hlen.
    apply Znth_app_last__normalized_step. }
  split; [rewrite Hnewlen; lia|].
  split.
  - rewrite !Zlength_app, Hlen. reflexivity.
  - rewrite Hnewactive. destruct Hcases as [[Hzero Hall] | Hused].
    + left. split; [exact Hzero|].
      intros q Hq. destruct (Z_lt_ge_dec q (Zlength prog)).
      * rewrite Znth_app_left__normalized_step by lia. apply Hall; lia.
      * assert (q = Zlength prog) by lia. subst q.
        rewrite <- Hlen.
        apply Znth_app_last__normalized_step.
    + right. destruct Hused as [q [Hq [Hneq [Hother Hafter]]]].
      exists q. repeat split; try lia.
      * rewrite Znth_app_left__normalized_step by lia. exact Hneq.
      * rewrite Znth_app_left__normalized_step by lia. exact Hother.
      * intros r Hr. destruct (Z_lt_ge_dec r (Zlength prog)).
        -- rewrite Znth_app_left__normalized_step by lia. apply Hafter; lia.
        -- assert (r = Zlength prog) by lia. subst r.
           rewrite <- Hlen.
           apply Znth_app_last__normalized_step.
Qed.

Lemma other_cpu_last_switch__normalized_step :
  forall prog cpu x,
    ValidSchedule prog cpu ->
    0 < Zlength prog ->
    OtherCpuLastProgram (prog ++ [x])
      (cpu ++ [other_cpu_label (Znth (Zlength prog - 1) cpu 0)])
      (Znth (Zlength prog - 1) prog 0).
Proof.
  intros prog cpu x Hvalid Hpos.
  destruct Hvalid as [Hlen Hall].
  set (active := Znth (Zlength prog - 1) cpu 0).
  assert (Hactive : active = 1 \/ active = 2).
  { apply valid_schedule_active_label__normalized_step with (prog := prog).
    - split; assumption.
    - exact Hpos. }
  assert (Hflip : other_cpu_label active <> active).
  { apply other_cpu_label_neq__normalized_step; exact Hactive. }
  unfold OtherCpuLastProgram.
  assert (Hnewlen : Zlength (prog ++ [x]) = Zlength prog + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hnewactive :
      Znth (Zlength (prog ++ [x]) - 1)
        (cpu ++ [other_cpu_label active]) 0 = other_cpu_label active).
  { rewrite Hnewlen. replace (Zlength prog + 1 - 1) with (Zlength prog) by lia.
    rewrite <- Hlen.
    apply Znth_app_last__normalized_step. }
  split; [rewrite Hnewlen; lia|]. split.
  - rewrite !Zlength_app, Hlen. reflexivity.
  - rewrite Hnewactive. right.
    exists (Zlength prog - 1). repeat split; try lia.
    + rewrite Znth_app_left__normalized_step by lia.
      intro Heq. apply Hflip. symmetry. exact Heq.
    + rewrite Znth_app_left__normalized_step by lia. reflexivity.
    + intros r Hr.
      assert (r = Zlength prog) by (rewrite Hnewlen in Hr; lia).
      subst r. rewrite <- Hlen. apply Znth_app_last__normalized_step.
Qed.

Lemma hot_start_continue_final_iff__normalized_step :
  forall prog cpu x,
    Zlength cpu = Zlength prog ->
    0 < Zlength prog ->
    ((exists previous,
        HotStart (prog ++ [x])
          (cpu ++ [Znth (Zlength prog - 1) cpu 0])
          (Zlength prog) previous) <->
     x = Znth (Zlength prog - 1) prog 0).
Proof.
  intros prog cpu x Hlen Hpos.
  set (active := Znth (Zlength prog - 1) cpu 0).
  split.
  - intros [previous Hhot]. unfold HotStart in Hhot.
    destruct Hhot as [[Hprev0 Hprevlt] [Hsame [Hbetween Hprog]]].
    assert (Hprevle : previous <= Zlength prog - 1) by lia.
    destruct (Z.eq_dec previous (Zlength prog - 1)) as [Heq|Hneq].
    + subst previous.
      rewrite Znth_app_left__normalized_step in Hprog by lia.
      rewrite Znth_app_last__normalized_step in Hprog.
      symmetry. exact Hprog.
    + assert (Hstrict : previous < Zlength prog - 1) by lia.
      specialize (Hbetween (Zlength prog - 1) ltac:(lia)).
      rewrite Znth_app_left__normalized_step in Hbetween by lia.
      replace (Zlength prog) with (Zlength cpu) in Hbetween by lia.
      rewrite Znth_app_last__normalized_step in Hbetween.
      rewrite Hlen in Hbetween.
      unfold active in Hbetween. exfalso. apply Hbetween. reflexivity.
  - intros Hx. exists (Zlength prog - 1).
    unfold HotStart. split; [lia|]. split.
    + rewrite Znth_app_left__normalized_step by lia.
      replace (Zlength prog) with (Zlength cpu) by lia.
      rewrite Znth_app_last__normalized_step.
      unfold active. rewrite <- Hlen. reflexivity.
    + split.
      * intros q Hq. exfalso. lia.
      * rewrite Znth_app_left__normalized_step by lia.
        rewrite Znth_app_last__normalized_step. symmetry. exact Hx.
Qed.

Lemma hot_start_switch_final_iff__normalized_step :
  forall prog cpu other x,
    ValidSchedule prog cpu ->
    OtherCpuLastProgram prog cpu other ->
    0 < Zlength prog ->
    0 < x ->
    ((exists previous,
        HotStart (prog ++ [x])
          (cpu ++ [other_cpu_label (Znth (Zlength prog - 1) cpu 0)])
          (Zlength prog) previous) <->
     other = x).
Proof.
  intros prog cpu other x Hvalid Hstate Hpos Hxpos.
  destruct Hvalid as [Hlen Hall].
  set (active := Znth (Zlength prog - 1) cpu 0) in *.
  assert (Hactive : active = 1 \/ active = 2).
  { apply valid_schedule_active_label__normalized_step with (prog := prog).
    - split; assumption.
    - exact Hpos. }
  assert (Hflipvalid : other_cpu_label active = 1 \/
                       other_cpu_label active = 2).
  { apply other_cpu_label_valid__normalized_step; exact Hactive. }
  assert (Hflipneq : other_cpu_label active <> active).
  { apply other_cpu_label_neq__normalized_step; exact Hactive. }
  unfold OtherCpuLastProgram in Hstate.
  destruct Hstate as [_ [_ Hcases]].
  split.
  - intros [previous Hhot]. unfold HotStart in Hhot.
    destruct Hhot as [[Hprev0 Hprevlt] [Hsame [Hbetween Hprog]]].
    replace (Zlength prog) with (Zlength cpu) in Hsame by lia.
    rewrite Znth_app_last__normalized_step in Hsame.
    rewrite Znth_app_left__normalized_step in Hsame by lia.
    rewrite Znth_app_last__normalized_step in Hprog.
    rewrite Znth_app_left__normalized_step in Hprog by lia.
    destruct Hcases as [[Hzero Hidle] | [q [Hq [Hqneq [Hother Hafter]]]]].
    + specialize (Hidle previous ltac:(lia)).
      rewrite Hidle in Hsame. exfalso. apply Hflipneq. symmetry. exact Hsame.
    + assert (Hprevious_label : Znth previous cpu 0 = other_cpu_label active)
        by exact Hsame.
      assert (Hq_label : Znth q cpu 0 = other_cpu_label active).
      { apply binary_label_other__normalized_step; try assumption.
        rewrite Forall_nth in Hall.
        specialize (Hall (Z.to_nat q) 0).
        assert (Hqi : (Z.to_nat q < length cpu)%nat).
        { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
          rewrite <- Zlength_correct. lia. }
        specialize (Hall Hqi). unfold Znth in Hall. exact Hall. }
      assert (previous = q).
      { destruct (Z.lt_trichotomy previous q) as [Hlt|[Heq|Hgt]]; auto.
        - specialize (Hbetween q ltac:(lia)).
          rewrite Znth_app_left__normalized_step in Hbetween by lia.
          replace (Zlength prog) with (Zlength cpu) in Hbetween by lia.
          rewrite Znth_app_last__normalized_step in Hbetween.
          rewrite Hq_label in Hbetween.
          exfalso. apply Hbetween. reflexivity.
        - specialize (Hafter previous ltac:(lia)).
          rewrite Hafter in Hprevious_label.
          exfalso. apply Hflipneq. symmetry. exact Hprevious_label. }
      subst previous. rewrite <- Hprog, <- Hother. reflexivity.
  - intros Hotherx.
    destruct Hcases as [[Hzero Hidle] | [q [Hq [Hqneq [Hother Hafter]]]]].
    + subst other. lia.
    + exists q. unfold HotStart. split; [lia|]. split.
      * rewrite Znth_app_left__normalized_step by lia.
        replace (Zlength prog) with (Zlength cpu) by lia.
        rewrite Znth_app_last__normalized_step.
        apply binary_label_other__normalized_step; try assumption.
        rewrite Forall_nth in Hall.
        specialize (Hall (Z.to_nat q) 0).
        assert (Hqi : (Z.to_nat q < length cpu)%nat).
        { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
          rewrite <- Zlength_correct. lia. }
        specialize (Hall Hqi). unfold Znth in Hall. exact Hall.
      * split.
        -- intros r Hr. rewrite Znth_app_left__normalized_step by lia.
           replace (Zlength prog) with (Zlength cpu) by lia.
           rewrite Znth_app_last__normalized_step.
           rewrite Hafter by lia.
           intro Heq. apply Hflipneq. symmetry. exact Heq.
        -- rewrite Znth_app_left__normalized_step by lia.
           rewrite Znth_app_last__normalized_step.
           rewrite <- Hother, Hotherx. reflexivity.
Qed.

Lemma run_time_continue_final_iff__normalized_step :
  forall prog cold hot cpu times x t,
    Zlength cpu = Zlength prog ->
    Zlength times = Zlength prog ->
    0 < Zlength prog ->
    (RunTime (prog ++ [x]) cold hot
       (cpu ++ [Znth (Zlength prog - 1) cpu 0]) (times ++ [t])
       (Zlength prog) <->
     (x = Znth (Zlength prog - 1) prog 0 /\
      t = Znth (x - 1) hot 0) \/
     (x <> Znth (Zlength prog - 1) prog 0 /\
      t = Znth (x - 1) cold 0)).
Proof.
  intros prog cold hot cpu times x t Hlen Htimes Hpos.
  pose proof (hot_start_continue_final_iff__normalized_step
                prog cpu x Hlen Hpos) as Hhot.
  assert (Htimeslast : Znth (Zlength prog) (times ++ [t]) 0 = t).
  { rewrite <- Htimes. apply Znth_app_last__normalized_step. }
  unfold RunTime. rewrite Htimeslast, !Znth_app_last__normalized_step.
  split.
  - intros [[previous [Hstart Ht]] | [Hnone Ht]].
    + left. split; [apply Hhot; eauto|exact Ht].
    + right. split; [|exact Ht].
      intro Heq. apply Hnone. apply Hhot. exact Heq.
  - intros [[Heq Ht] | [Hneq Ht]].
    + left. destruct (proj2 Hhot Heq) as [previous Hstart].
      exists previous. split; assumption.
    + right. split; [|exact Ht].
      intro Hexists. apply Hneq. apply Hhot. exact Hexists.
Qed.

Lemma run_time_switch_final_iff__normalized_step :
  forall prog cold hot cpu times other x t,
    ValidSchedule prog cpu ->
    OtherCpuLastProgram prog cpu other ->
    Zlength times = Zlength prog ->
    0 < Zlength prog ->
    0 < x ->
    (RunTime (prog ++ [x]) cold hot
       (cpu ++ [other_cpu_label (Znth (Zlength prog - 1) cpu 0)])
       (times ++ [t]) (Zlength prog) <->
     (other = x /\ t = Znth (x - 1) hot 0) \/
     (other <> x /\ t = Znth (x - 1) cold 0)).
Proof.
  intros prog cold hot cpu times other x t Hvalid Hstate Htimes Hpos Hxpos.
  pose proof (hot_start_switch_final_iff__normalized_step
                prog cpu other x Hvalid Hstate Hpos Hxpos) as Hhot.
  assert (Htimeslast : Znth (Zlength prog) (times ++ [t]) 0 = t).
  { rewrite <- Htimes. apply Znth_app_last__normalized_step. }
  unfold RunTime. rewrite Htimeslast, !Znth_app_last__normalized_step.
  split.
  - intros [[previous [Hstart Ht]] | [Hnone Ht]].
    + left. split; [apply Hhot; eauto|exact Ht].
    + right. split; [|exact Ht].
      intro Heq. apply Hnone. apply Hhot. exact Heq.
  - intros [[Heq Ht] | [Hneq Ht]].
    + left. destruct (proj2 Hhot Heq) as [previous Hstart].
      exists previous. split; assumption.
    + right. split; [|exact Ht].
      intro Hexists. apply Hneq. apply Hhot. exact Hexists.
Qed.

(* The two local runtime facts above assemble into a complete execution of the
   extended schedule.  This is the forward half of the DP-step decomposition;
   it is deliberately stated independently of either branch so that the same
   proof supports the continuing and switching successor. *)
Lemma run_times_snoc__normalized_step :
  forall prog cold hot cpu times x label t,
    Zlength cpu = Zlength prog ->
    RunTimes prog cold hot cpu times ->
    RunTime (prog ++ [x]) cold hot (cpu ++ [label]) (times ++ [t])
      (Zlength prog) ->
    RunTimes (prog ++ [x]) cold hot (cpu ++ [label]) (times ++ [t]).
Proof.
  intros prog cold hot cpu times x label t Hcpu [Htimes Hall] Hfinal.
  unfold RunTimes. split.
  - rewrite !Zlength_app, Htimes. reflexivity.
  - intros pos Hpos.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hpos.
    destruct (Z_lt_ge_dec pos (Zlength prog)) as [Hold | Hlast].
    + apply (proj1 (run_time_snoc_old_iff__normalized_step
                     prog cold hot cpu times x label t pos Hcpu Htimes
                     ltac:(lia))).
      apply Hall; lia.
    + assert (pos = Zlength prog) by lia. subst pos. exact Hfinal.
Qed.

Lemma run_cost_snoc__normalized_step :
  forall prog cold hot cpu times total x label t,
    ValidSchedule prog cpu ->
    (label = 1 \/ label = 2) ->
    RunTimes prog cold hot cpu times ->
    total = fold_right Z.add 0 times ->
    RunTime (prog ++ [x]) cold hot (cpu ++ [label]) (times ++ [t])
      (Zlength prog) ->
    RunCost (prog ++ [x]) cold hot (cpu ++ [label]) (total + t).
Proof.
  intros prog cold hot cpu times total x label t
    Hvalid Hlabel Htimes Htotal Hfinal.
  split.
  - apply valid_schedule_snoc__normalized_step; assumption.
  - exists (times ++ [t]). split.
    + apply run_times_snoc__normalized_step.
      * exact (proj1 Hvalid).
      * exact Htimes.
      * exact Hfinal.
    + rewrite fold_right_add_snoc__normalized_step, <- Htotal. reflexivity.
Qed.

Lemma run_cost_single__initialization :
  forall p cold hot cpu total,
    RunCost [p] cold hot cpu total ->
    total = Znth (p - 1) cold 0.
Proof.
  intros p cold hot cpu total Hrun.
  unfold RunCost, ValidSchedule in Hrun.
  destruct Hrun as [[Hcpu_len Hcpu_values] [times [Htimes Htotal]]].
  unfold RunTimes in Htimes.
  destruct Htimes as [Htimes_len Htimes].
  destruct times as [|t times'];
    [rewrite Zlength_cons, !Zlength_nil in Htimes_len; lia|].
  destruct times' as [|t' times'];
    [|pose proof (Zlength_nonneg times');
      repeat rewrite Zlength_cons in Htimes_len;
      rewrite Zlength_nil in Htimes_len; lia].
  specialize (Htimes 0 ltac:(rewrite Zlength_cons, Zlength_nil; lia)).
  unfold RunTime in Htimes.
  destruct Htimes as [[q [Hhot _]] | [_ Hcold]].
  - unfold HotStart in Hhot. lia.
  - simpl in Hcold, Htotal.
    subst total.
    repeat rewrite Znth0_cons in Hcold.
    lia.
Qed.
Lemma run_cost_single_exists__initialization :
  forall p cold hot,
    exists cpu, RunCost [p] cold hot cpu (Znth (p - 1) cold 0).
Proof.
  intros p cold hot.
  exists [1].
  unfold RunCost, ValidSchedule, RunTimes.
  split.
  - split.
    + repeat rewrite Zlength_cons. rewrite Zlength_nil. reflexivity.
    + repeat constructor; auto.
  - exists [Znth (p - 1) cold 0].
    split.
    + split.
      * repeat rewrite Zlength_cons. rewrite Zlength_nil. reflexivity.
      * intros i Hi.
        assert (i = 0) by (rewrite Zlength_cons, Zlength_nil in Hi; lia).
        subst i.
        unfold RunTime.
        right.
        split.
        -- intros [q Hhot]. unfold HotStart in Hhot. lia.
        -- rewrite !Znth0_cons. reflexivity.
    + simpl. lia.
Qed.
Lemma other_cpu_single__initialization :
  forall p c other,
    OtherCpuLastProgram [p] [c] other <-> other = 0.
Proof.
  intros p c other.
  unfold OtherCpuLastProgram.
  simpl.
  split.
  - intros [_ [_ Hother]].
    destruct Hother as [[Hother _] | [q [Hq [Hneq _]]]].
    + exact Hother.
    + rewrite Zlength_cons, Zlength_nil in Hq.
      assert (q = 0) by lia. subst q.
      repeat rewrite Zlength_cons, Zlength_nil in Hneq.
      repeat rewrite Znth0_cons in Hneq. contradiction.
  - intros Hother.
    split; [rewrite Zlength_cons, Zlength_nil; lia|].
    split; [rewrite !Zlength_cons, !Zlength_nil; reflexivity|].
    left.
    split; [exact Hother|].
    intros q Hq.
    rewrite Zlength_cons, Zlength_nil in Hq.
    assert (q = 0) by lia. subst q.
    repeat rewrite Zlength_cons, Zlength_nil.
    repeat rewrite Znth0_cons. reflexivity.
Qed.
Lemma prefix_state_cost_one__initialization :
  forall prog cold hot other total,
    1 <= Zlength prog ->
    PrefixStateCost prog cold hot 1 other total <->
      other = 0 /\ total = Znth (Znth 0 prog 0 - 1) cold 0.
Proof.
  intros prog cold hot other total Hprog_len.
  destruct prog as [|p ps];
    [rewrite Zlength_nil in Hprog_len; lia|].
  unfold PrefixStateCost.
  cbn [sublist Znth].
  split.
  - intros [cpu [Hrun Hother]].
    assert (Htotal : total = Znth (p - 1) cold 0).
    { eapply run_cost_single__initialization; eauto. }
    unfold RunCost, ValidSchedule in Hrun.
    destruct Hrun as [[Hcpu_len _] _].
    destruct cpu as [|c cpu'];
      [change (0 = 1) in Hcpu_len; lia|].
    destruct cpu' as [|c' cpu'];
      [|exfalso; change (Zlength (c :: c' :: cpu') = 1) in Hcpu_len;
        rewrite !Zlength_cons in Hcpu_len;
        pose proof (Zlength_nonneg cpu'); lia].
    apply other_cpu_single__initialization in Hother.
    auto.
  - intros [Hother Htotal].
    subst other total.
    destruct (run_cost_single_exists__initialization p cold hot) as [cpu Hrun].
    exists cpu.
    split; [exact Hrun|].
    unfold RunCost, ValidSchedule in Hrun.
    destruct Hrun as [[Hcpu_len _] _].
    destruct cpu as [|c cpu'];
      [change (0 = 1) in Hcpu_len; lia|].
    destruct cpu' as [|c' cpu'];
      [|exfalso; change (Zlength (c :: c' :: cpu') = 1) in Hcpu_len;
        rewrite !Zlength_cons in Hcpu_len;
        pose proof (Zlength_nonneg cpu'); lia].
    apply other_cpu_single__initialization.
    reflexivity.
Qed.
Lemma normalized_schedule_state_initial__initialization :
  forall prog cold hot initialized n k,
    1 <= n ->
    n = Zlength prog ->
    1 <= k ->
    k = Zlength cold ->
    k = Zlength hot ->
    (forall q, 0 <= q < n -> 1 <= Znth q prog 0 <= k) ->
    (forall q, 0 <= q < k ->
      1 <= Znth q hot 0 <= Znth q cold 0 /\
      Znth q cold 0 <= 1000000000) ->
    Zlength initialized = k + 1 ->
    (forall q, 0 <= q < k + 1 -> Znth q initialized 0 = DP_INF) ->
    NormalizedScheduleState prog cold hot 1
      (replace_Znth 0 0 initialized)
      (Znth (Znth 0 prog 0) (0 :: cold) 0) 0.
Proof.
  intros prog cold hot initialized n k Hn Hnlen Hk Hkcold Hkhot
    Hprog Hcost Hinitlen Hinit.
  assert (Hproglen : 1 <= Zlength prog) by lia.
  assert (Hp : 1 <= Znth 0 prog 0 <= k).
  { apply Hprog. lia. }
  assert (Hpidx : 0 <= Znth 0 prog 0 - 1 < k) by lia.
  specialize (Hcost (Znth 0 prog 0 - 1) Hpidx).
  assert (Hoff : Znth (Znth 0 prog 0) (0 :: cold) 0 =
                 Znth (Znth 0 prog 0 - 1) cold 0).
  { rewrite Znth_cons by lia. reflexivity. }
  rewrite Hoff.
  unfold NormalizedScheduleState.
  split.
  - intros other Hother.
    unfold NormalizedScheduleCell.
    destruct (Z.eq_dec other 0) as [-> | Hother0].
    + left.
      rewrite Znth_replace_Znth_Same by (rewrite Hinitlen; lia).
      split.
      * unfold DP_INF. lia.
      * unfold PrefixStateMinimum, min_value_of_subset, min_object_of_subset.
        exists (Znth (Znth 0 prog 0 - 1) cold 0).
        split.
        -- split.
           ++ apply (proj2 ((prefix_state_cost_one__initialization prog cold hot 0
                (Znth (Znth 0 prog 0 - 1) cold 0)) Hproglen)).
              auto.
           ++ intros b Hb.
              apply (proj1 ((prefix_state_cost_one__initialization prog cold hot 0 b)
                Hproglen)) in Hb.
              lia.
        -- lia.
    + right.
      split.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hinitlen; lia).
        rewrite (Znth_indep initialized other DP_INF 0)
          by (rewrite Hinitlen; lia).
        apply Hinit. lia.
      * intros [total Hstate].
        apply (proj1 ((prefix_state_cost_one__initialization prog cold hot other total)
          Hproglen)) in Hstate.
        tauto.
  - split.
    + unfold min_value_of_subset, min_object_of_subset.
      exists 0.
      split.
      * split.
        -- exists 0.
           repeat split; try lia.
           rewrite Znth_replace_Znth_Same by (rewrite Hinitlen; lia).
           reflexivity.
        -- intros b [other [Hother [Hb Hfinite]]].
           destruct (Z.eq_dec other 0) as [-> | Hother0].
           ++ rewrite Znth_replace_Znth_Same in Hb by (rewrite Hinitlen; lia).
              lia.
           ++ rewrite Znth_replace_Znth_Diff in Hb by (try rewrite Hinitlen; lia).
              rewrite (Znth_indep initialized other DP_INF 0) in Hb
                by (rewrite Hinitlen; lia).
              rewrite Hinit in Hb by lia.
              unfold DP_INF in Hb, Hfinite. lia.
      * reflexivity.
    + unfold Spec, min_value_of_subset, min_object_of_subset.
      exists (Znth (Znth 0 prog 0 - 1) cold 0).
      split.
      * split.
        -- destruct prog as [|p ps];
             [rewrite Zlength_nil in Hproglen; lia|].
           cbn [sublist Znth].
           apply run_cost_single_exists__initialization.
        -- intros b [cpu Hrun].
           destruct prog as [|p ps];
             [rewrite Zlength_nil in Hproglen; lia|].
           cbn [sublist Znth] in *.
           apply run_cost_single__initialization in Hrun.
           repeat rewrite Znth0_cons.
           lia.
      * lia.
Qed.
Lemma normalized_schedule_state_min_le__state_transitions :
  forall prog cold hot prefix_len dp off mind other,
    NormalizedScheduleState prog cold hot prefix_len dp off mind ->
    0 <= other <= Zlength cold ->
    Znth other dp DP_INF < DP_INF ->
    mind <= Znth other dp DP_INF.
Proof.
  intros prog cold hot prefix_len dp off mind other Hstate Hother Hfinite.
  unfold NormalizedScheduleState in Hstate.
  destruct Hstate as [_ [Hmin _]].
  unfold min_value_of_subset, min_object_of_subset in Hmin.
  destruct Hmin as [a [[_ Hleast] Ha]].
  rewrite <- Ha.
  apply Hleast.
  exists other.
  split; [exact Hother|].
  split; [reflexivity|exact Hfinite].
Qed.
Lemma run_cost_snoc_inv__state_transitions :
  forall prog cold hot sched total x,
    RunCost (prog ++ [x]) cold hot sched total ->
    exists cpu times label t base,
      sched = cpu ++ [label] /\
      (label = 1 \/ label = 2) /\
      ValidSchedule prog cpu /\
      RunTimes prog cold hot cpu times /\
      base = fold_right Z.add 0 times /\
      total = base + t /\
      RunTime (prog ++ [x]) cold hot (cpu ++ [label])
        (times ++ [t]) (Zlength prog).
Proof.
  intros prog cold hot sched total x Hrun.
  destruct Hrun as [[Hsched_len Hlabels] [all_times [Hall_times Htotal]]].
  destruct Hall_times as [Htimes_len Htimes].
  destruct (rev sched) as [|label revcpu] eqn:Hsched_rev.
  - assert (Hsched : sched = []).
    { rewrite <- (rev_involutive sched), Hsched_rev. reflexivity. }
    subst sched.
    rewrite Zlength_nil, Zlength_app, Zlength_cons, Zlength_nil in Hsched_len.
    pose proof (Zlength_nonneg prog). lia.
  - set (cpu := rev revcpu).
    assert (Hsched : sched = cpu ++ [label]).
    { unfold cpu. rewrite <- (rev_involutive sched), Hsched_rev. reflexivity. }
    subst sched.
    destruct (rev all_times) as [|t revtimes] eqn:Htimes_rev.
    + assert (Hall_times_nil : all_times = []).
      { rewrite <- (rev_involutive all_times), Htimes_rev. reflexivity. }
      subst all_times.
      rewrite Zlength_nil, Zlength_app, Zlength_cons, Zlength_nil in Htimes_len.
      pose proof (Zlength_nonneg prog). lia.
    + set (times := rev revtimes).
      assert (Hall_times_snoc : all_times = times ++ [t]).
      { unfold times. rewrite <- (rev_involutive all_times), Htimes_rev. reflexivity. }
      subst all_times.
      assert (Hcpu_len : Zlength cpu = Zlength prog).
      { rewrite !Zlength_app, !Zlength_cons, !Zlength_nil in Hsched_len. lia. }
      assert (Htimes_old_len : Zlength times = Zlength prog).
      { rewrite !Zlength_app, !Zlength_cons, !Zlength_nil in Htimes_len. lia. }
      assert (Hlabel : label = 1 \/ label = 2).
      { apply Forall_app in Hlabels. destruct Hlabels as [_ Hlast].
        inversion Hlast; subst. assumption. }
      assert (Hold_labels : Forall (fun z => z = 1 \/ z = 2) cpu).
      { apply Forall_app in Hlabels. tauto. }
      assert (Hold_times : RunTimes prog cold hot cpu times).
      { split; [exact Htimes_old_len|].
        intros pos Hpos.
        apply (proj2 (run_time_snoc_old_iff__normalized_step
          prog cold hot cpu times x label t pos Hcpu_len Htimes_old_len Hpos)).
        apply Htimes.
        rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      assert (Hfinal : RunTime (prog ++ [x]) cold hot
          (cpu ++ [label]) (times ++ [t]) (Zlength prog)).
      { apply Htimes.
        rewrite Zlength_app, Zlength_cons, Zlength_nil.
        pose proof (Zlength_nonneg prog). lia. }
      exists cpu, times, label, t, (fold_right Z.add 0 times).
      split; [reflexivity|].
      split; [exact Hlabel|].
      split; [split; assumption|].
      split; [exact Hold_times|].
      split; [reflexivity|].
      split.
      * rewrite fold_right_add_snoc__normalized_step in Htotal. exact Htotal.
      * exact Hfinal.
Qed.
Lemma other_cpu_last_exists__state_transitions :
  forall prog cpu,
    ValidSchedule prog cpu ->
    0 < Zlength prog ->
    exists other, OtherCpuLastProgram prog cpu other.
Proof.
  intros prog.
  induction prog using rev_ind.
  - intros cpu _ Hpos. rewrite Zlength_nil in Hpos. lia.
  - intros cpu Hvalid Hpos.
    destruct (rev cpu) as [|label revcpu] eqn:Hcpu_rev.
    + assert (Hcpu_nil : cpu = []).
      { rewrite <- (rev_involutive cpu), Hcpu_rev. reflexivity. }
      subst cpu. destruct Hvalid as [Hlen _].
      rewrite Zlength_nil, Zlength_app, Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg prog). lia.
    + set (oldcpu := rev revcpu).
      assert (Hcpu : cpu = oldcpu ++ [label]).
      { unfold oldcpu. rewrite <- (rev_involutive cpu), Hcpu_rev. reflexivity. }
      subst cpu.
      destruct Hvalid as [Hlen Hall].
      assert (Holdlen : Zlength oldcpu = Zlength prog).
      { rewrite !Zlength_app, !Zlength_cons, !Zlength_nil in Hlen. lia. }
      apply Forall_app in Hall. destruct Hall as [Holdlabels Hlast].
      inversion Hlast as [|? ? Hlabel _]; subst.
      assert (Holdvalid : ValidSchedule prog oldcpu) by (split; assumption).
      destruct prog as [|p ps] eqn:Hprog.
      * destruct oldcpu as [|c cs].
        2: { rewrite Zlength_cons, Zlength_nil in Holdlen.
             pose proof (Zlength_nonneg cs). lia. }
        exists 0.
        unfold OtherCpuLastProgram.
        split.
        { rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia. }
        split; [exact Hlen|].
        left. split; [reflexivity|].
        intros q Hq.
        assert (q = 0).
        { rewrite !Zlength_app, !Zlength_cons, !Zlength_nil in Hq. lia. }
        subst q.
        cbn [app Zlength Znth]. reflexivity.
      * assert (Hprogpos : 0 < Zlength (p :: ps)).
        { rewrite Zlength_cons. pose proof (Zlength_nonneg ps). lia. }
        specialize (IHprog oldcpu Holdvalid Hprogpos).
        destruct IHprog as [other Hother].
        set (active := Znth (Zlength (p :: ps) - 1) oldcpu 0).
        destruct (Z.eq_dec label active) as [Heq|Hneq].
        -- exists other. subst label.
           apply other_cpu_last_continue__normalized_step. exact Hother.
        -- exists (Znth (Zlength (p :: ps) - 1) (p :: ps) 0).
           assert (Hactive : active = 1 \/ active = 2).
           { unfold active. eapply valid_schedule_active_label__normalized_step;
               eauto. }
           assert (Hlabel_other : label = other_cpu_label active).
           { apply binary_label_other__normalized_step; assumption. }
           rewrite Hlabel_other.
           apply other_cpu_last_switch__normalized_step; assumption.
Qed.
Lemma other_cpu_last_continue_inv__state_transitions :
  forall prog cpu other x,
    ValidSchedule prog cpu ->
    0 < Zlength prog ->
    OtherCpuLastProgram (prog ++ [x])
      (cpu ++ [Znth (Zlength prog - 1) cpu 0]) other ->
    OtherCpuLastProgram prog cpu other.
Proof.
  intros prog cpu other x [Hlen Hall] Hpos Hnew.
  set (active := Znth (Zlength prog - 1) cpu 0) in *.
  unfold OtherCpuLastProgram in Hnew.
  destruct Hnew as [_ [_ Hcases]].
  assert (Hnewlen : Zlength (prog ++ [x]) = Zlength prog + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hnewactive :
      Znth (Zlength (prog ++ [x]) - 1) (cpu ++ [active]) 0 = active).
  { rewrite Hnewlen. replace (Zlength prog + 1 - 1) with (Zlength prog) by lia.
    rewrite <- Hlen. apply Znth_app_last__normalized_step. }
  rewrite Hnewactive in Hcases.
  unfold OtherCpuLastProgram.
  split; [exact Hpos|]. split; [exact Hlen|].
  destruct Hcases as [[Hzero Hsame] | [q [Hq [Hneq [Hother Hafter]]]]].
  - left. split; [exact Hzero|].
    intros q Hq.
    specialize (Hsame q ltac:(rewrite Hnewlen; lia)).
    rewrite Znth_app_left__normalized_step in Hsame by lia.
    exact Hsame.
  - assert (Hqlt : q < Zlength prog).
    { destruct (Z_lt_ge_dec q (Zlength prog)); auto.
      assert (q = Zlength prog) by (rewrite Hnewlen in Hq; lia).
      subst q. rewrite <- Hlen, Znth_app_last__normalized_step in Hneq.
      contradiction. }
    right. exists q. repeat split; try lia.
    + rewrite Znth_app_left__normalized_step in Hneq by lia. exact Hneq.
    + rewrite Znth_app_left__normalized_step in Hother by lia. exact Hother.
    + intros r Hr.
      specialize (Hafter r ltac:(rewrite Hnewlen; lia)).
      rewrite Znth_app_left__normalized_step in Hafter by lia.
      unfold active in Hafter. exact Hafter.
Qed.
Lemma other_cpu_last_switch_value__state_transitions :
  forall prog cpu other x label,
    ValidSchedule prog cpu ->
    0 < Zlength prog ->
    label <> Znth (Zlength prog - 1) cpu 0 ->
    OtherCpuLastProgram (prog ++ [x]) (cpu ++ [label]) other ->
    other = Znth (Zlength prog - 1) prog 0.
Proof.
  intros prog cpu other x label [Hlen Hall] Hpos Hneq_label Hnew.
  set (active := Znth (Zlength prog - 1) cpu 0) in *.
  unfold OtherCpuLastProgram in Hnew.
  destruct Hnew as [_ [_ Hcases]].
  assert (Hnewlen : Zlength (prog ++ [x]) = Zlength prog + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  assert (Hnewactive :
      Znth (Zlength (prog ++ [x]) - 1) (cpu ++ [label]) 0 = label).
  { rewrite Hnewlen. replace (Zlength prog + 1 - 1) with (Zlength prog) by lia.
    rewrite <- Hlen. apply Znth_app_last__normalized_step. }
  rewrite Hnewactive in Hcases.
  destruct Hcases as [[Hzero Hsame] | [q [Hq [Hneq [Hother Hafter]]]]].
  - specialize (Hsame (Zlength prog - 1) ltac:(rewrite Hnewlen; lia)).
    rewrite Znth_app_left__normalized_step in Hsame by lia.
    exfalso. apply Hneq_label. symmetry. exact Hsame.
  - assert (Hqeq : q = Zlength prog - 1).
    { assert (Hqle : q <= Zlength prog) by (rewrite Hnewlen in Hq; lia).
      destruct (Z.eq_dec q (Zlength prog)) as [->|Hnotlast].
      - rewrite <- Hlen, Znth_app_last__normalized_step in Hneq. contradiction.
      - assert (Hqlt : q < Zlength prog) by lia.
        destruct (Z.eq_dec q (Zlength prog - 1)); auto.
        specialize (Hafter (Zlength prog - 1) ltac:(rewrite Hnewlen; lia)).
        rewrite Znth_app_left__normalized_step in Hafter by lia.
        exfalso. apply Hneq_label. symmetry. exact Hafter. }
    subst q.
    rewrite Znth_app_left__normalized_step in Hother by lia.
    exact Hother.
Qed.
Lemma prefix_state_cost_step_iff__state_transitions :
  forall prog cold hot i x y other total,
    1 <= i < Zlength prog ->
    x = Znth i prog 0 ->
    y = Znth (i - 1) prog 0 ->
    1 <= x ->
    (PrefixStateCost prog cold hot (i + 1) other total <->
      (exists oldtotal,
        PrefixStateCost prog cold hot i other oldtotal /\
        total = oldtotal +
          (if Z.eq_dec x y then Znth (x - 1) hot 0
           else Znth (x - 1) cold 0)) \/
      (other = y /\ exists oldother oldtotal,
        PrefixStateCost prog cold hot i oldother oldtotal /\
        total = oldtotal +
          (if Z.eq_dec oldother x then Znth (x - 1) hot 0
           else Znth (x - 1) cold 0))).
Proof.
  intros prog cold hot i x y other total Hi Hx Hy Hxpos.
  assert (Hprefix : sublist 0 (i + 1) prog = sublist 0 i prog ++ [x]).
  { rewrite Hx. apply sublist_0_succ__normalized_step. lia. }
  set (prefix := sublist 0 i prog).
  assert (Hprefix_len : Zlength prefix = i).
  { unfold prefix. rewrite Zlength_sublist by lia. lia. }
  assert (Hprefix_pos : 0 < Zlength prefix) by lia.
  assert (Hlast_prog : Znth (Zlength prefix - 1) prefix 0 = y).
  { rewrite Hprefix_len. unfold prefix. rewrite Znth_sublist by lia.
    replace (i - 1 + 0) with (i - 1) by lia.
    symmetry. exact Hy. }
  split.
  - intros [sched [Hrun Hother_new]].
    rewrite Hprefix in Hrun, Hother_new.
    destruct (run_cost_snoc_inv__state_transitions
      prefix cold hot sched total x Hrun)
      as [cpu [times [label [t [base
        [Hsched [Hlabel [Hvalid [Htimes [Hbase [Htotal Hfinal]]]]]]]]]]].
    subst sched.
    destruct (other_cpu_last_exists__state_transitions
      prefix cpu Hvalid Hprefix_pos) as [oldother Holdother].
    set (active := Znth (Zlength prefix - 1) cpu 0).
    destruct (Z.eq_dec label active) as [Hcontinue|Hswitch].
    + left. exists base. split.
      * unfold PrefixStateCost. fold prefix. exists cpu.
        split.
        -- unfold RunCost. split; [exact Hvalid|].
           exists times. split; [exact Htimes|exact Hbase].
        -- subst label.
           eapply other_cpu_last_continue_inv__state_transitions; eauto.
      * subst label.
        apply (proj1 (run_time_continue_final_iff__normalized_step
          prefix cold hot cpu times x t (proj1 Hvalid) (proj1 Htimes)
          Hprefix_pos)) in Hfinal.
        rewrite Hlast_prog in Hfinal.
        destruct (Z.eq_dec x y); destruct Hfinal as [[? ?]|[? ?]];
          try contradiction; lia.
    + right. split.
      * transitivity (Znth (Zlength prefix - 1) prefix 0).
        -- eapply other_cpu_last_switch_value__state_transitions; eauto.
        -- exact Hlast_prog.
      * exists oldother, base. split.
        -- unfold PrefixStateCost. fold prefix. exists cpu.
           split.
           ++ unfold RunCost. split; [exact Hvalid|].
              exists times. split; [exact Htimes|exact Hbase].
           ++ exact Holdother.
        -- assert (Hactive_valid : active = 1 \/ active = 2).
           { unfold active. eapply valid_schedule_active_label__normalized_step;
               eauto. }
           assert (Hlabel_other : label = other_cpu_label active).
           { apply binary_label_other__normalized_step; assumption. }
           rewrite Hlabel_other in Hfinal.
           apply (proj1 (run_time_switch_final_iff__normalized_step
             prefix cold hot cpu times oldother x t Hvalid Holdother
             (proj1 Htimes) Hprefix_pos ltac:(lia))) in Hfinal.
           destruct (Z.eq_dec oldother x); destruct Hfinal as [[? ?]|[? ?]];
             try contradiction; lia.
  - intros [[oldtotal [Hold Htotal_eq]] |
            [Hother_eq [oldother [oldtotal [Hold Htotal_eq]]]]].
    + subst total. destruct Hold as [cpu [Hrun Hother_old]].
      fold prefix in Hrun, Hother_old.
      unfold RunCost in Hrun.
      destruct Hrun as [Hvalid [times [Htimes Hbase]]].
      set (active := Znth (Zlength prefix - 1) cpu 0).
      exists (cpu ++ [active]).
      rewrite Hprefix. fold prefix. split.
      * destruct (Z.eq_dec x y) as [Heq|Hneq].
        -- eapply run_cost_snoc__normalized_step with
             (times := times) (total := oldtotal)
             (t := Znth (x - 1) hot 0).
           ++ exact Hvalid.
           ++ unfold active. eapply valid_schedule_active_label__normalized_step;
                eauto.
           ++ exact Htimes.
           ++ exact Hbase.
           ++ apply (proj2 (run_time_continue_final_iff__normalized_step
                prefix cold hot cpu times x (Znth (x - 1) hot 0)
                (proj1 Hvalid) (proj1 Htimes) Hprefix_pos)).
              left. rewrite Hlast_prog. auto.
        -- eapply run_cost_snoc__normalized_step with
             (times := times) (total := oldtotal)
             (t := Znth (x - 1) cold 0).
           ++ exact Hvalid.
           ++ unfold active. eapply valid_schedule_active_label__normalized_step;
                eauto.
           ++ exact Htimes.
           ++ exact Hbase.
           ++ apply (proj2 (run_time_continue_final_iff__normalized_step
                prefix cold hot cpu times x (Znth (x - 1) cold 0)
                (proj1 Hvalid) (proj1 Htimes) Hprefix_pos)).
              right. rewrite Hlast_prog. auto.
      * unfold active. apply other_cpu_last_continue__normalized_step.
        exact Hother_old.
    + subst total. destruct Hold as [cpu [Hrun Hother_old]].
      fold prefix in Hrun, Hother_old.
      unfold RunCost in Hrun.
      destruct Hrun as [Hvalid [times [Htimes Hbase]]].
      set (active := Znth (Zlength prefix - 1) cpu 0).
      exists (cpu ++ [other_cpu_label active]).
      rewrite Hprefix. fold prefix. split.
      * destruct (Z.eq_dec oldother x) as [Heq|Hneq].
        -- eapply run_cost_snoc__normalized_step with
             (times := times) (total := oldtotal)
             (t := Znth (x - 1) hot 0).
           ++ exact Hvalid.
           ++ apply other_cpu_label_valid__normalized_step.
              unfold active. eapply valid_schedule_active_label__normalized_step;
                eauto.
           ++ exact Htimes.
           ++ exact Hbase.
           ++ apply (proj2 (run_time_switch_final_iff__normalized_step
                prefix cold hot cpu times oldother x (Znth (x - 1) hot 0)
                Hvalid Hother_old (proj1 Htimes) Hprefix_pos ltac:(lia))).
              left. auto.
        -- eapply run_cost_snoc__normalized_step with
             (times := times) (total := oldtotal)
             (t := Znth (x - 1) cold 0).
           ++ exact Hvalid.
           ++ apply other_cpu_label_valid__normalized_step.
              unfold active. eapply valid_schedule_active_label__normalized_step;
                eauto.
           ++ exact Htimes.
           ++ exact Hbase.
           ++ apply (proj2 (run_time_switch_final_iff__normalized_step
                prefix cold hot cpu times oldother x (Znth (x - 1) cold 0)
                Hvalid Hother_old (proj1 Htimes) Hprefix_pos ltac:(lia))).
              right. auto.
      * rewrite Hother_eq, <- Hlast_prog.
        apply other_cpu_last_switch__normalized_step; assumption.
Qed.
Lemma min_value_member_le__state_transitions :
  forall (P : Z -> Prop) m z,
    min_value_of_subset Z.le P (fun x => x) m ->
    P z -> m <= z.
Proof.
  intros P m z [a [[Ha Hleast] Heq]] Hz. simpl in Heq. subst a.
  apply Hleast. exact Hz.
Qed.
Lemma min_value_member__state_transitions :
  forall (P : Z -> Prop) m,
    min_value_of_subset Z.le P (fun x => x) m -> P m.
Proof.
  intros P m [a [[Ha _] Heq]]. simpl in Heq. subst a. exact Ha.
Qed.
Lemma prefix_state_cost_other_bound__state_transitions :
  forall prog cold hot i other total,
    0 < i <= Zlength prog ->
    (forall q, 0 <= q < Zlength prog ->
      1 <= Znth q prog 0 <= Zlength cold) ->
    PrefixStateCost prog cold hot i other total ->
    0 <= other <= Zlength cold.
Proof.
  intros prog cold hot i other total Hi Hprog
    [cpu [Hrun Hother]].
  unfold OtherCpuLastProgram in Hother.
  destruct Hother as [_ [_ [[-> _] | [q [Hq [_ [Hother _]]]]]]].
  - pose proof (Zlength_nonneg cold). lia.
  - subst other.
    rewrite Zlength_sublist in Hq by lia.
    rewrite Znth_sublist by lia.
    replace (q + 0) with q by lia.
    pose proof (Hprog q ltac:(lia)). lia.
Qed.
Lemma normalized_switch_minimum__state_transitions :
  forall prog cold hot i dp off mind x cand,
    1 <= i < Zlength prog ->
    1 <= x <= Zlength cold ->
    (forall q, 0 <= q < Zlength prog ->
      1 <= Znth q prog 0 <= Zlength cold) ->
    Znth (x - 1) hot 0 <= Znth (x - 1) cold 0 ->
    NormalizedScheduleState prog cold hot i dp off mind ->
    cand <= mind + off + Znth (x - 1) cold 0 ->
    (Znth x dp DP_INF < DP_INF ->
      cand <= Znth x dp DP_INF + off + Znth (x - 1) hot 0) ->
    (cand = mind + off + Znth (x - 1) cold 0 \/
     (Znth x dp DP_INF < DP_INF /\
      cand = Znth x dp DP_INF + off + Znth (x - 1) hot 0)) ->
    min_value_of_subset Z.le
      (fun total => exists oldother oldtotal,
        PrefixStateCost prog cold hot i oldother oldtotal /\
        total = oldtotal +
          (if Z.eq_dec oldother x then Znth (x - 1) hot 0
           else Znth (x - 1) cold 0))
      (fun z => z) cand.
Proof.
  intros prog cold hot i dp off mind x cand Hi Hx Hprog Hhotcold
    Hstate Hcandcold Hcandhot Hattain.
  unfold NormalizedScheduleState in Hstate.
  destruct Hstate as [Hcells [Hmind Hspec]].
  unfold min_value_of_subset, min_object_of_subset.
  exists cand. split; [split|reflexivity].
  - destruct Hattain as [Hcold | [Hxfinite Hhot]].
    + destruct (min_value_member__state_transitions _ _ Hmind)
        as [oldother [Hobound [Hmindval Hfinite]]].
      specialize (Hcells oldother Hobound).
      destruct Hcells as [[_ Hcellmin] | [Hinf Hnone]].
      2: { unfold DP_INF in *; lia. }
      pose proof (min_value_member__state_transitions _ _ Hcellmin) as Holdcost.
      destruct (Z.eq_dec oldother x) as [Heq|Hneq].
      * subst oldother.
        assert (Hdpmin : Znth x dp DP_INF = mind) by lia.
        specialize (Hcandhot ltac:(lia)).
        rewrite Hdpmin in Holdcost.
        exists x, (off + mind). split; [exact Holdcost|].
        destruct (Z.eq_dec x x); [|contradiction]. lia.
      * rewrite <- Hmindval in Holdcost.
        exists oldother, (off + mind). split; [exact Holdcost|].
        destruct (Z.eq_dec oldother x); [contradiction|lia].
    + specialize (Hcells x ltac:(lia)).
      destruct Hcells as [[_ Hcellmin] | [Hinf Hnone]].
      2: { lia. }
      pose proof (min_value_member__state_transitions _ _ Hcellmin) as Holdcost.
      exists x, (off + Znth x dp DP_INF). split; [exact Holdcost|].
      destruct (Z.eq_dec x x); [lia|contradiction].
  - intros total [oldother [oldtotal [Holdcost Htotal]]].
    pose proof (prefix_state_cost_other_bound__state_transitions
      prog cold hot i oldother oldtotal ltac:(lia) Hprog Holdcost) as Hobound.
    specialize (Hcells oldother Hobound).
    destruct Hcells as [[Hfinite Hcellmin] | [Hinf Hnone]].
    2: { exfalso. apply Hnone. eauto. }
    pose proof (min_value_member_le__state_transitions _ _ _ Hcellmin Holdcost)
      as Hcell_le.
    assert (Hmind_le : mind <= Znth oldother dp DP_INF).
    { eapply min_value_member_le__state_transitions with
        (z := Znth oldother dp DP_INF).
      - exact Hmind.
      - exists oldother. split; [exact Hobound|].
        split; [reflexivity|exact Hfinite]. }
    subst total.
    destruct (Z.eq_dec oldother x) as [->|Hneq].
    + apply Z.le_trans with
        (Znth x dp DP_INF + off + Znth (x - 1) hot 0).
      * apply Hcandhot. exact Hfinite.
      * lia.
    + apply Z.le_trans with
        (mind + off + Znth (x - 1) cold 0); [exact Hcandcold|lia].
Qed.
Lemma normalized_cell_continue_step__state_transitions :
  forall prog cold hot i x y other off ca value,
    1 <= i < Zlength prog ->
    x = Znth i prog 0 -> y = Znth (i - 1) prog 0 ->
    1 <= x ->
    ca = (if Z.eq_dec x y then Znth (x - 1) hot 0
          else Znth (x - 1) cold 0) ->
    other <> y ->
    NormalizedScheduleCell prog cold hot i other off value ->
    NormalizedScheduleCell prog cold hot (i + 1) other (off + ca) value.
Proof.
  intros prog cold hot i x y other off ca value Hi Hx Hy Hxpos Hca Hneq Hcell.
  unfold NormalizedScheduleCell in *.
  destruct Hcell as [[Hfinite Hmin] | [Hinf Hnone]].
  - left. split; [exact Hfinite|].
    unfold PrefixStateMinimum, min_value_of_subset, min_object_of_subset in *.
    destruct Hmin as [oldtotal [[Hold Hleast] Heq]]. simpl in Heq. subst oldtotal.
    exists (off + value + ca). split; [split|lia].
    + apply (proj2 (prefix_state_cost_step_iff__state_transitions
        prog cold hot i x y other (off + value + ca) Hi Hx Hy Hxpos)).
      left. exists (off + value). split; [exact Hold|]. rewrite Hca. lia.
    + intros total Hnew.
      apply (proj1 (prefix_state_cost_step_iff__state_transitions
        prog cold hot i x y other total Hi Hx Hy Hxpos)) in Hnew.
      destruct Hnew as [[old [Hold' ->]] | [Heqother _]].
      * specialize (Hleast old Hold'). simpl in Hleast. rewrite Hca. lia.
      * contradiction.
  - right. split; [exact Hinf|].
    intros [total Hnew].
    apply (proj1 (prefix_state_cost_step_iff__state_transitions
      prog cold hot i x y other total Hi Hx Hy Hxpos)) in Hnew.
    destruct Hnew as [[old [Hold _]] | [Heqother _]].
    + apply Hnone. eauto.
    + contradiction.
Qed.
Lemma normalized_cell_switch_step__state_transitions :
  forall prog cold hot i x y off ca oldvalue cand ny newvalue,
    1 <= i < Zlength prog ->
    x = Znth i prog 0 -> y = Znth (i - 1) prog 0 ->
    1 <= x -> ca = (if Z.eq_dec x y then Znth (x - 1) hot 0
                     else Znth (x - 1) cold 0) ->
    cand = off + ca + ny -> ny < DP_INF ->
    min_value_of_subset Z.le
      (fun total => exists oldother oldtotal,
        PrefixStateCost prog cold hot i oldother oldtotal /\
        total = oldtotal +
          (if Z.eq_dec oldother x then Znth (x - 1) hot 0
           else Znth (x - 1) cold 0))
      (fun z => z) cand ->
    NormalizedScheduleCell prog cold hot i y off oldvalue ->
    ((ny < oldvalue /\ newvalue = ny) \/
     (oldvalue <= ny /\ newvalue = oldvalue)) ->
    NormalizedScheduleCell prog cold hot (i + 1) y (off + ca) newvalue.
Proof.
  intros prog cold hot i x y off ca oldvalue cand ny newvalue
    Hi Hx Hy Hxpos Hca Hcand Hny Hswitch Holdcell Hselect.
  destruct Hselect as [[Hlt ->] | [Hge ->]].
  - left. split; [exact Hny|].
    unfold PrefixStateMinimum, min_value_of_subset, min_object_of_subset.
    pose proof (min_value_member__state_transitions _ _ Hswitch) as Hmember.
    exists cand. split; [split|lia].
    + apply (proj2 (prefix_state_cost_step_iff__state_transitions
        prog cold hot i x y y cand Hi Hx Hy Hxpos)).
      right. split; [reflexivity|exact Hmember].
    + intros total Hnew.
      apply (proj1 (prefix_state_cost_step_iff__state_transitions
        prog cold hot i x y y total Hi Hx Hy Hxpos)) in Hnew.
      destruct Hnew as [[oldtotal [Hold ->]] | [_ Hsw]].
      * destruct Holdcell as [[_ Holdmin] | [Hinf Hnone]].
        -- pose proof (min_value_member_le__state_transitions
             _ _ _ Holdmin Hold) as Hle. lia.
        -- exfalso. apply Hnone. eauto.
      * pose proof (min_value_member_le__state_transitions
          _ _ _ Hswitch Hsw) as Hle. exact Hle.
  - destruct Holdcell as [[Hfinite Holdmin] | [Hinf Hnone]].
    + left. split; [exact Hfinite|].
      unfold PrefixStateMinimum, min_value_of_subset, min_object_of_subset in *.
      destruct Holdmin as [oldtotal [[Hold Hleast] Heq]]. simpl in Heq.
      subst oldtotal.
      exists (off + oldvalue + ca). split; [split|lia].
      * apply (proj2 (prefix_state_cost_step_iff__state_transitions
          prog cold hot i x y y (off + oldvalue + ca) Hi Hx Hy Hxpos)).
        left. exists (off + oldvalue). split; [exact Hold|]. rewrite Hca. lia.
      * intros total Hnew.
        apply (proj1 (prefix_state_cost_step_iff__state_transitions
          prog cold hot i x y y total Hi Hx Hy Hxpos)) in Hnew.
        destruct Hnew as [[old [Hold' ->]] | [_ Hsw]].
        -- specialize (Hleast old Hold'). simpl in Hleast. rewrite Hca. lia.
        -- pose proof (min_value_member_le__state_transitions
             _ _ _ Hswitch Hsw) as Hle. lia.
    + exfalso. unfold DP_INF in *. lia.
Qed.
Lemma normalized_vector_min_replace__state_transitions :
  forall (cold dp : list Z) mind y ny (newdp : list Z) newmind,
    Zlength dp = Zlength cold + 1 ->
    0 <= y <= Zlength cold ->
    ny < DP_INF ->
    min_value_of_subset Z.le
      (fun value => exists other,
        0 <= other <= Zlength cold /\
        value = Znth other dp DP_INF /\ value < DP_INF)
      (fun z => z) mind ->
    ((ny < Znth y dp DP_INF /\ newdp = replace_Znth y ny dp) \/
     (Znth y dp DP_INF <= ny /\ newdp = dp)) ->
    ((ny < mind /\ newmind = ny) \/ (mind <= ny /\ newmind = mind)) ->
    min_value_of_subset Z.le
      (fun value => exists other,
        0 <= other <= Zlength cold /\
        value = Znth other newdp DP_INF /\ value < DP_INF)
      (fun z => z) newmind.
Proof.
  intros cold dp mind y ny newdp newmind Hlen Hy Hny Hmin Hdp Hmind.
  destruct Hdp as [[Hnyold ->] | [Holdny ->]].
  2: { destruct Hmind as [[Hnymind _] | [_ ->]]; [exfalso|exact Hmin].
       pose proof (min_value_member_le__state_transitions _ _
         (Znth y dp DP_INF) Hmin).
       assert (Hmember : exists other : Z,
          0 <= other <= Zlength cold /\
          Znth y dp DP_INF = Znth other dp DP_INF /\
          Znth y dp DP_INF < DP_INF).
       { exists y. split; [exact Hy|]. split; [reflexivity|lia]. }
       specialize (H Hmember). lia. }
  destruct Hmind as [[Hnymind ->] | [Hmindny ->]].
  - unfold min_value_of_subset, min_object_of_subset.
    exists ny. split; [split|reflexivity].
    + exists y. split; [exact Hy|]. split.
      * rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia). reflexivity.
      * exact Hny.
    + intros value [other [Hother [Hvalue Hfinite]]].
      destruct (Z.eq_dec other y) as [->|Hneq].
      * rewrite Znth_replace_Znth_Same in Hvalue by (rewrite Hlen; lia). lia.
      * rewrite Znth_replace_Znth_Diff in Hvalue by (try rewrite Hlen; lia).
        assert (Hmember : exists q : Z,
          0 <= q <= Zlength cold /\ value = Znth q dp DP_INF /\ value < DP_INF).
        { exists other. tauto. }
        pose proof (min_value_member_le__state_transitions _ _ value Hmin Hmember).
        lia.
  - unfold min_value_of_subset, min_object_of_subset in *.
    destruct Hmin as [value [[Hmember Hleast] Heq]]. simpl in Heq. subst value.
    exists mind. split; [split|reflexivity].
    + destruct Hmember as [other [Hother [Hvalue Hfinite]]].
      assert (Hneq : other <> y).
      { intro Heqother. subst other. lia. }
      exists other. split; [exact Hother|]. split.
      * rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). exact Hvalue.
      * exact Hfinite.
    + intros value [other [Hother [Hvalue Hfinite]]].
      destruct (Z.eq_dec other y) as [->|Hneq].
      * rewrite Znth_replace_Znth_Same in Hvalue by (rewrite Hlen; lia). lia.
      * rewrite Znth_replace_Znth_Diff in Hvalue by (try rewrite Hlen; lia).
        apply Hleast. exists other. split; [exact Hother|]. tauto.
Qed.
Lemma normalized_cells_min_spec__state_transitions :
  forall prog cold hot prefix_len dp off mind,
    0 < prefix_len <= Zlength prog ->
    (forall q, 0 <= q < Zlength prog ->
      1 <= Znth q prog 0 <= Zlength cold) ->
    (forall other, 0 <= other <= Zlength cold ->
      NormalizedScheduleCell prog cold hot prefix_len other off
        (Znth other dp DP_INF)) ->
    min_value_of_subset Z.le
      (fun value => exists other,
        0 <= other <= Zlength cold /\
        value = Znth other dp DP_INF /\ value < DP_INF)
      (fun z => z) mind ->
    Spec (sublist 0 prefix_len prog) cold hot (off + mind).
Proof.
  intros prog cold hot prefix_len dp off mind Hi Hprog Hcells Hmin.
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists (off + mind). split; [split|reflexivity].
  - destruct (min_value_member__state_transitions _ _ Hmin)
      as [other [Hother [Hvalue Hfinite]]].
    specialize (Hcells other Hother).
    destruct Hcells as [[_ Hcellmin] | [Hinf Hnone]].
    2: { unfold DP_INF in *; lia. }
    pose proof (min_value_member__state_transitions _ _ Hcellmin) as Hcost.
    rewrite <- Hvalue in Hcost.
    destruct Hcost as [cpu [Hrun Hothercpu]]. exists cpu. exact Hrun.
  - intros total [cpu Hrun].
    assert (Hvalid : ValidSchedule (sublist 0 prefix_len prog) cpu).
    { exact (proj1 Hrun). }
    assert (Hsubpos : 0 < Zlength (sublist 0 prefix_len prog)).
    { rewrite Zlength_sublist by lia. lia. }
    destruct (other_cpu_last_exists__state_transitions _ _ Hvalid Hsubpos)
      as [other Hothercpu].
    assert (Hcost : PrefixStateCost prog cold hot prefix_len other total).
    { exists cpu. auto. }
    pose proof (prefix_state_cost_other_bound__state_transitions
      prog cold hot prefix_len other total Hi Hprog Hcost) as Hother.
    specialize (Hcells other Hother).
    destruct Hcells as [[Hfinite Hcellmin] | [Hinf Hnone]].
    2: { exfalso. apply Hnone. eauto. }
    pose proof (min_value_member_le__state_transitions _ _ _ Hcellmin Hcost)
      as Hcellle.
    assert (Hmindle : mind <= Znth other dp DP_INF).
    { eapply min_value_member_le__state_transitions with
        (z := Znth other dp DP_INF); [exact Hmin|].
      exists other. split; [exact Hother|]. split; [reflexivity|exact Hfinite]. }
    lia.
Qed.
Lemma normalized_schedule_state_step__state_transitions :
  forall prog cold hot i dp off mind x y ca cand ny newdp newmind,
    1 <= i < Zlength prog ->
    x = Znth i prog 0 ->
    y = Znth (i - 1) prog 0 ->
    Zlength dp = Zlength cold + 1 ->
    1 <= x <= Zlength cold ->
    0 <= y <= Zlength cold ->
    (forall q, 0 <= q < Zlength prog ->
      1 <= Znth q prog 0 <= Zlength cold) ->
    Znth (x - 1) hot 0 <= Znth (x - 1) cold 0 ->
    NormalizedScheduleState prog cold hot i dp off mind ->
    ca = (if Z.eq_dec x y then Znth (x - 1) hot 0
          else Znth (x - 1) cold 0) ->
    cand = off + ca + ny ->
    ny < DP_INF ->
    cand <= mind + off + Znth (x - 1) cold 0 ->
    (Znth x dp DP_INF < DP_INF ->
      cand <= Znth x dp DP_INF + off + Znth (x - 1) hot 0) ->
    (cand = mind + off + Znth (x - 1) cold 0 \/
     (Znth x dp DP_INF < DP_INF /\
      cand = Znth x dp DP_INF + off + Znth (x - 1) hot 0)) ->
    ((ny < Znth y dp DP_INF /\ newdp = replace_Znth y ny dp) \/
     (Znth y dp DP_INF <= ny /\ newdp = dp)) ->
    ((ny < mind /\ newmind = ny) \/ (mind <= ny /\ newmind = mind)) ->
    NormalizedScheduleState prog cold hot (i + 1) newdp (off + ca) newmind.
Proof.
  intros prog cold hot i dp off mind x y ca cand ny newdp newmind
    Hi Hx Hy Hlen Hxbound Hybound Hprog Hhotcold Hstate Hca Hcand Hny
    Hcandcold Hcandhot Hattain Hdpselect Hmindselect.
  pose proof Hstate as Holdstate.
  unfold NormalizedScheduleState in Holdstate.
  destruct Holdstate as [Holdcells [Holdmin Holdspec]].
  pose proof (normalized_switch_minimum__state_transitions
    prog cold hot i dp off mind x cand Hi Hxbound Hprog Hhotcold Hstate
    Hcandcold Hcandhot Hattain) as Hswitch.
  assert (Hnewcells : forall other,
      0 <= other <= Zlength cold ->
      NormalizedScheduleCell prog cold hot (i + 1) other (off + ca)
        (Znth other newdp DP_INF)).
  { intros other Hother.
    destruct (Z.eq_dec other y) as [->|Hneq].
    - apply normalized_cell_switch_step__state_transitions with
        (x := x) (y := y) (oldvalue := Znth y dp DP_INF)
        (cand := cand) (ny := ny);
        try assumption.
      + lia.
      + apply Holdcells. exact Hybound.
      + destruct Hdpselect as [[Hlt ->] | [Hge ->]].
        * left. split; [exact Hlt|].
          rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia). reflexivity.
        * right. auto.
    - assert (Hsame : Znth other newdp DP_INF = Znth other dp DP_INF).
      { destruct Hdpselect as [[_ ->] | [_ ->]]; [|reflexivity].
        rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia). reflexivity. }
      rewrite Hsame.
      eapply normalized_cell_continue_step__state_transitions with
        (x := x) (y := y).
      + exact Hi.
      + exact Hx.
      + exact Hy.
      + lia.
      + exact Hca.
      + exact Hneq.
      + apply Holdcells. exact Hother. }
  assert (Hnewmin : min_value_of_subset Z.le
      (fun value => exists other,
        0 <= other <= Zlength cold /\
        value = Znth other newdp DP_INF /\ value < DP_INF)
      (fun z => z) newmind).
  { eapply normalized_vector_min_replace__state_transitions; eauto. }
  unfold NormalizedScheduleState.
  split; [exact Hnewcells|]. split; [exact Hnewmin|].
  apply normalized_cells_min_spec__state_transitions with
    (dp := newdp) (mind := newmind).
  - lia.
  - exact Hprog.
  - exact Hnewcells.
  - exact Hnewmin.
Qed.
Lemma normalized_unequal_transition_branches__state_transitions :
  forall prog cold hot i dp off mind x y,
    1 <= i < Zlength prog ->
    x = Znth i prog 0 ->
    y = Znth (i - 1) prog 0 ->
    Zlength dp = Zlength cold + 1 ->
    1 <= x <= Zlength cold ->
    1 <= y <= Zlength cold ->
    (forall q, 0 <= q < Zlength prog ->
      1 <= Znth q prog 0 <= Zlength cold) ->
    Znth (x - 1) hot 0 <= Znth (x - 1) cold 0 ->
    NormalizedScheduleState prog cold hot i dp off mind ->
    x <> y ->
    Znth x dp 0 < DP_INF ->
    Znth x dp 0 + off + Znth (x - 1) hot 0 <
      mind + off + Znth (x - 1) cold 0 ->
    let hotc := Znth (x - 1) hot 0 in
    let coldc := Znth (x - 1) cold 0 in
    let ny := Znth x dp 0 + hotc - coldc in
      (ny >= Znth y dp 0 ->
        NormalizedScheduleState prog cold hot (i + 1) dp
          (off + coldc) mind) /\
      ((ny < Znth y dp 0 /\ ny < mind) ->
        NormalizedScheduleState prog cold hot (i + 1)
          (replace_Znth y ny dp) (off + coldc) ny) /\
      ((ny < Znth y dp 0 /\ ny >= mind) ->
        NormalizedScheduleState prog cold hot (i + 1)
          (replace_Znth y ny dp) (off + coldc) mind).
Proof.
  intros prog cold hot i dp off mind x y Hi Hx Hy Hlen Hxbound Hybound
    Hprog Hhotcold Hstate Hneq Hxfinite Hcandcold.
  cbn.
  set (hotc := Znth (x - 1) hot 0).
  set (coldc := Znth (x - 1) cold 0).
  set (ny := Znth x dp 0 + hotc - coldc).
  assert (Hxidx : 0 <= x < Zlength dp) by lia.
  assert (Hyidx : 0 <= y < Zlength dp) by lia.
  assert (Hxdefault : Znth x dp DP_INF = Znth x dp 0).
  { apply Znth_indep. exact Hxidx. }
  assert (Hydefault : Znth y dp DP_INF = Znth y dp 0).
  { apply Znth_indep. exact Hyidx. }
  assert (Hnyfinite : ny < DP_INF).
  { unfold ny, hotc, coldc. lia. }
  assert (Hstep : forall newdp newmind,
      ((ny < Znth y dp DP_INF /\ newdp = replace_Znth y ny dp) \/
       (Znth y dp DP_INF <= ny /\ newdp = dp)) ->
      ((ny < mind /\ newmind = ny) \/
       (mind <= ny /\ newmind = mind)) ->
      NormalizedScheduleState prog cold hot (i + 1) newdp
        (off + coldc) newmind).
  { intros newdp newmind Hdpselect Hmindselect.
    eapply normalized_schedule_state_step__state_transitions with
      (x := x) (y := y) (ca := coldc)
      (cand := Znth x dp 0 + off + hotc) (ny := ny).
    - exact Hi.
    - exact Hx.
    - exact Hy.
    - exact Hlen.
    - exact Hxbound.
    - lia.
    - exact Hprog.
    - exact Hhotcold.
    - exact Hstate.
    - unfold coldc.
      destruct (Z.eq_dec x y); [contradiction|reflexivity].
    - unfold ny. lia.
    - exact Hnyfinite.
    - unfold hotc, coldc in *. lia.
    - intros _. rewrite Hxdefault. unfold hotc. lia.
    - right. split; [rewrite Hxdefault; exact Hxfinite|].
      rewrite Hxdefault. unfold hotc. lia.
    - exact Hdpselect.
    - exact Hmindselect. }
  split.
  - intros Hge.
    assert (Hyfinite : Znth y dp DP_INF < DP_INF).
    { rewrite Hydefault. lia. }
    pose proof (normalized_schedule_state_min_le__state_transitions
      prog cold hot i dp off mind y Hstate ltac:(lia) Hyfinite) as Hmin.
    apply Hstep.
    + right. rewrite Hydefault. split; [lia|reflexivity].
    + right. split; [lia|reflexivity].
  - split; intros [Hlt Hmind].
    + apply Hstep.
      * left. rewrite Hydefault. split; [lia|reflexivity].
      * left. split; [lia|reflexivity].
    + apply Hstep.
      * left. rewrite Hydefault. split; [lia|reflexivity].
      * right. split; [lia|reflexivity].
Qed.
Lemma normalized_baseline_transition_branches__state_transitions :
  forall prog cold hot i dp off mind x y ca,
    1 <= i < Zlength prog -> x = Znth i prog 0 ->
    y = Znth (i - 1) prog 0 -> Zlength dp = Zlength cold + 1 ->
    1 <= x <= Zlength cold -> 1 <= y <= Zlength cold ->
    (forall q, 0 <= q < Zlength prog ->
      1 <= Znth q prog 0 <= Zlength cold) ->
    Znth (x - 1) hot 0 <= Znth (x - 1) cold 0 ->
    NormalizedScheduleState prog cold hot i dp off mind ->
    ca = (if Z.eq_dec x y then Znth (x - 1) hot 0
          else Znth (x - 1) cold 0) ->
    1 <= ca <= Znth (x - 1) cold 0 ->
    Znth (x - 1) cold 0 <= 1000000000 ->
    mind <= 0 ->
    mind + off + Znth (x - 1) cold 0 <=
      Znth x dp 0 + off + Znth (x - 1) hot 0 ->
    let coldc := Znth (x - 1) cold 0 in
    let ny := mind + coldc - ca in
      ((ny < Znth y dp 0 /\ ny < mind) ->
        NormalizedScheduleState prog cold hot (i + 1)
          (replace_Znth y ny dp) (off + ca) ny) /\
      ((ny < Znth y dp 0 /\ ny >= mind) ->
        NormalizedScheduleState prog cold hot (i + 1)
          (replace_Znth y ny dp) (off + ca) mind) /\
      (ny >= Znth y dp 0 ->
        NormalizedScheduleState prog cold hot (i + 1) dp (off + ca) mind).
Proof.
  intros prog cold hot i dp off mind x y ca Hi Hx Hy Hlen Hxbound Hybound
    Hprog Hhotcold Hstate Hca Hcabound Hcoldmax Hmind Hcandhot.
  set (coldc := Znth (x - 1) cold 0).
  set (ny := mind + coldc - ca).
  assert (Hxidx : 0 <= x < Zlength dp) by lia.
  assert (Hyidx : 0 <= y < Zlength dp) by lia.
  assert (Hxdefault : Znth x dp DP_INF = Znth x dp 0).
  { apply Znth_indep. exact Hxidx. }
  assert (Hydefault : Znth y dp DP_INF = Znth y dp 0).
  { apply Znth_indep. exact Hyidx. }
  assert (Hnyfinite : ny < DP_INF).
  { unfold ny, coldc, DP_INF. lia. }
  assert (Hstep : forall newdp,
      ((ny < Znth y dp DP_INF /\ newdp = replace_Znth y ny dp) \/
       (Znth y dp DP_INF <= ny /\ newdp = dp)) ->
      NormalizedScheduleState prog cold hot (i + 1) newdp (off + ca) mind).
  { intros newdp Hselect.
    eapply normalized_schedule_state_step__state_transitions with
      (x := x) (y := y) (ca := ca)
      (cand := mind + off + coldc) (ny := ny).
    - exact Hi. - exact Hx. - exact Hy. - exact Hlen.
    - exact Hxbound. - lia. - exact Hprog. - exact Hhotcold.
    - exact Hstate. - exact Hca. - unfold ny; lia. - exact Hnyfinite.
    - unfold coldc; lia.
    - intros _. rewrite Hxdefault. unfold coldc in *. exact Hcandhot.
    - left. unfold coldc. reflexivity.
    - exact Hselect.
    - right. split; [unfold ny, coldc; lia|reflexivity]. }
  split.
  - intros [_ Hlt]. unfold ny, coldc in Hlt. lia.
  - split.
    + intros [Hlt _]. apply Hstep. left. rewrite Hydefault.
      split; [exact Hlt|reflexivity].
    + intros Hge.
      apply Hstep. right. rewrite Hydefault. split; [unfold ny; lia|reflexivity].
Qed.
Lemma Zlength_replace_Znth__state_write_update :
  forall {A : Type} (xs : list A) i (v : A),
    Zlength (replace_Znth i v xs) = Zlength xs.
Proof.
  intros A xs i v.
  assert (Hlen : forall (B : Type) (n : nat) (ys : list B) (w : B),
      length (replace_nth n ys w) = length ys).
  { intros B n ys. revert n.
    induction ys as [| y ys IH]; intros [| n] w; simpl; auto. }
  unfold replace_Znth.
  rewrite !Zlength_correct, Hlen.
  reflexivity.
Qed.
Lemma Znth_zero_replace_positive__state_write_update :
  forall (xs : list Z) i v,
    1 <= i < Zlength xs ->
    Znth 0 xs 0 = 0 ->
    Znth 0 (replace_Znth i v xs) 0 = 0.
Proof.
  intros xs i v Hi Hzero.
  rewrite Znth_replace_Znth_Diff by lia.
  exact Hzero.
Qed.
Lemma replace_Znth_dp_bounds__state_write_update :
  forall dp k i idx value,
    Zlength dp = k + 1 ->
    1 <= idx <= k ->
    (forall q, 0 <= q <= k ->
      Znth q dp 0 = 4557430888798830399 \/
      (- i) * 1000000000 <= Znth q dp 0 <= i * 1000000000) ->
    (-(i + 1)) * 1000000000 <= value ->
    value <= (i + 1) * 1000000000 ->
    forall q, 0 <= q <= k ->
      Znth q (replace_Znth idx value dp) 0 = 4557430888798830399 \/
      (-(i + 1)) * 1000000000 <=
        Znth q (replace_Znth idx value dp) 0 <=
        (i + 1) * 1000000000.
Proof.
  intros dp k i idx value Hlen Hidx Hold Hvalue_lo Hvalue_hi q Hq.
  destruct (Z.eq_dec q idx) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
    right. lia.
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hlen; lia).
    specialize (Hold q Hq).
    destruct Hold as [Hinf | Hbounds].
    + left. exact Hinf.
    + right. lia.
Qed.
