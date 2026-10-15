Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition LockTrigger (ins : list (list Z)) (times : list Z) (i t : Z) : Prop :=
  1 <= t <= Zlength (Znth i ins []) /\ Znth (t - 1) (Znth i ins []) 0 <> 0 /\
  ((exists j u, 0 <= j < Zlength ins /\ 1 <= u < t /\ Znth j times 0 = u /\
      Znth (u - 1) (Znth j ins []) 0 = Znth (t - 1) (Znth i ins []) 0) \/
   (exists j, 0 <= j < Zlength ins /\ j <> i /\ (Znth j times 0 = 0 \/ t <= Znth j times 0) /\
      Znth (t - 1) (Znth j ins []) 0 = Znth (t - 1) (Znth i ins []) 0)).
Definition Pre (k : Z) (ins : list (list Z)) : Prop :=
  (* Stated explicitly in the P049 solver Require, so dropped here:
       1 <= Zlength ins <= 100 /\
       Forall (fun row => Zlength row = m /\ Forall (fun x => 0 <= x <= k) row) ins /\
       1 <= k <= 100   *)
  (* exists m, 1 <= m <= 100. *)
  True.

Definition Spec (k : Z) (ins : list (list Z)) (out : list Z) : Prop :=
  Zlength out = Zlength ins /\ forall i, 0 <= i < Zlength ins ->
   ((Znth i out 0 = 0 /\ ~exists t, LockTrigger ins out i t) \/
    (1 <= Znth i out 0 /\ LockTrigger ins out i (Znth i out 0) /\
     forall t, 1 <= t < Znth i out 0 -> ~LockTrigger ins out i t)).

(* The entries strictly before [t] are the lock times already settled before
   cycle [t].  Entries equal to [t] are deliberately hidden as zero. *)
Definition lock_times_before (times : list Z) (t : Z) : list Z :=
  map (fun u => if u <? t then u else 0) times.

(* A cell is dead after [upto] cycles exactly when some already locked core
   addressed it at the cycle where that core locked. *)
Definition CellWasDead
    (ins : list (list Z)) (times : list Z) (upto cell : Z) : Prop :=
  exists i,
    0 <= i < Zlength ins /\
    1 <= Znth i times 0 <= upto /\
    Znth (Znth i times 0 - 1) (Znth i ins []) 0 = cell.

(* [times] gives the earliest trigger seen in cycles 1..upto, or zero when no
   such trigger has occurred yet.  This is the mathematical prefix form of
   the frozen [Spec], independent of the concrete loop organization. *)
Definition LockTimesThrough
    (ins : list (list Z)) (times : list Z) (upto : Z) : Prop :=
  Zlength times = Zlength ins /\
  forall i, 0 <= i < Zlength ins ->
    ((Znth i times 0 = 0 /\
      forall t, 1 <= t <= upto -> ~ LockTrigger ins times i t) \/
     (1 <= Znth i times 0 <= upto /\
      LockTrigger ins times i (Znth i times 0) /\
      forall t, 1 <= t < Znth i times 0 -> ~ LockTrigger ins times i t)).

(* Logical meaning of the persistent [cell_locked] scratch array. *)
Definition DeadCellsThrough
    (ins : list (list Z)) (times : list Z)
    (k upto : Z) (dead : list Z) : Prop :=
  Zlength dead = 105 /\
  Znth 0 dead 0 = 0 /\
  forall cell, 1 <= cell <= k ->
    0 <= Znth cell dead 0 <= 1 /\
    (Znth cell dead 0 = 1 <-> CellWasDead ins times upto cell).

Definition DeadCellsBefore
    (ins : list (list Z)) (times : list Z)
    (k t : Z) (dead : list Z) : Prop :=
  DeadCellsThrough ins (lock_times_before times t) k (t - 1) dead.

(* During the first core scan of cycle [t], only writers to cells that were
   already dead before [t] are locked. *)
Definition DirectLockScan
    (ins : list (list Z)) (times : list Z) (t scanned : Z) : Prop :=
  let old := lock_times_before times t in
  LockTimesThrough ins old (t - 1) /\
  Zlength times = Zlength ins /\
  forall i, 0 <= i < Zlength ins ->
    let cell := Znth (t - 1) (Znth i ins []) 0 in
    (Znth i times 0 = t <->
       i < scanned /\ Znth i old 0 = 0 /\ cell <> 0 /\
       CellWasDead ins old (t - 1) cell) /\
    (Znth i times 0 <> t -> Znth i times 0 = Znth i old 0).

(* Exact live-writer histogram after scanning cores [0,scanned). *)
Definition WriterCounts
    (ins : list (list Z)) (times : list Z)
    (t scanned k : Z) (counts : list Z) : Prop :=
  let old := lock_times_before times t in
  Zlength counts = k + 1 /\
  forall cell, 0 <= cell <= k ->
    Znth cell counts 0 =
      #(fun i : Z =>
          0 <= i < scanned /\
          Znth i old 0 = 0 /\
          cell <> 0 /\
          Znth (t - 1) (Znth i ins []) 0 = cell /\
          ~ CellWasDead ins old (t - 1) cell) /\
    0 <= Znth cell counts 0 <= scanned.

(* Cells below [completed] have had this cycle's collision mark applied. *)
Definition CellMarksPrefix
    (ins : list (list Z)) (times counts : list Z)
    (k t completed : Z) (dead : list Z) : Prop :=
  let old := lock_times_before times t in
  Zlength dead = 105 /\
  Znth 0 dead 0 = 0 /\
  forall cell, 1 <= cell <= k ->
    0 <= Znth cell dead 0 <= 1 /\
    (Znth cell dead 0 = 1 <->
       CellWasDead ins old (t - 1) cell \/
       (cell < completed /\ 2 <= Znth cell counts 0)).

(* Same-cycle collision closure: all colliding cells below [cell_cursor] are
   complete, while [core_done] writers of the current cell have been closed. *)
Definition CollisionClosurePrefix
    (ins : list (list Z)) (times counts : list Z)
    (t cell_cursor core_done : Z) : Prop :=
  let old := lock_times_before times t in
  LockTimesThrough ins old (t - 1) /\
  Zlength times = Zlength ins /\
  forall i, 0 <= i < Zlength ins ->
    let cell := Znth (t - 1) (Znth i ins []) 0 in
    (Znth i times 0 = t <->
       Znth i old 0 = 0 /\ cell <> 0 /\
       (CellWasDead ins old (t - 1) cell \/
        (2 <= Znth cell counts 0 /\
         (cell < cell_cursor \/
          (cell = cell_cursor /\ i < core_done))))) /\
    (Znth i times 0 <> t -> Znth i times 0 = Znth i old 0).

Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical_Prop.
Lemma lock_times_through_zero__solver_init :
  forall (ins : list (list Z)) (times : list Z),
    Zlength times = Zlength ins ->
    (forall i, 0 <= i < Zlength ins -> Znth i times 0 = 0) ->
    LockTimesThrough ins times 0.
Proof.
  intros ins times Hlen Hzero.
  unfold LockTimesThrough.
  split.
  - exact Hlen.
  - intros i Hi.
    left.
    split.
    + apply Hzero; exact Hi.
    + intros t Ht.
      lia.
Qed.
Lemma dead_cells_through_zero__solver_init :
  forall (ins : list (list Z)) (times dead : list Z) (k : Z),
    Zlength dead = 105 ->
    Znth 0 dead 0 = 0 ->
    k <= 100 ->
    (forall cell, 1 <= cell <= k -> Znth cell dead 0 = 0) ->
    (forall core, 0 <= core < Zlength ins -> Znth core times 0 = 0) ->
    DeadCellsThrough ins times k 0 dead.
Proof.
  intros ins times dead k Hdeadlen Hdeadzero Hk Hzero_dead Hzero_time.
  unfold DeadCellsThrough.
  split.
  - exact Hdeadlen.
  - split.
    + exact Hdeadzero.
    + intros cell Hcell.
      rewrite Hzero_dead by exact Hcell.
      split.
      { lia. }
      split.
      { lia. }
      intros Hdead.
      unfold CellWasDead in Hdead.
      destruct Hdead as [core [Hcore [Htime Hvalue]]].
      rewrite Hzero_time in Htime by exact Hcore.
      lia.
Qed.
Lemma Znth_concat_rect__scan_entry :
  forall (rows : list (list Z)) (d : list Z) m i j,
    0 <= m ->
    (forall r, 0 <= r < Zlength rows -> Zlength (Znth r rows d) = m) ->
    0 <= i < Zlength rows ->
    0 <= j < m ->
    Znth j (Znth i rows d) 0 = Znth (i * m + j) (concat rows) 0.
Proof.
  induction rows as [|row rows IH]; intros d m i j Hm Hrows Hi Hj.
  - rewrite Zlength_nil in Hi. lia.
  - assert (Hrow : Zlength row = m).
    { assert (Hzero : 0 <= 0 < Zlength (row :: rows)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg rows). lia. }
      specialize (Hrows 0 Hzero).
      simpl in Hrows. exact Hrows. }
    destruct (Z.eq_dec i 0) as [->|Hine].
    + simpl concat. simpl Znth.
      rewrite app_Znth1 by lia.
      reflexivity.
    + assert (Hi_pos : 0 < i) by lia.
      simpl concat.
      rewrite Znth_cons by lia.
      rewrite app_Znth2 by nia.
      replace (i * m + j - Zlength row) with ((i - 1) * m + j) by nia.
      eapply IH with (d := d) (m := m) (i := i - 1) (j := j).
      * exact Hm.
      * intros r Hr.
        specialize (Hrows (r + 1)).
        rewrite Zlength_cons in Hrows.
        specialize (Hrows ltac:(lia)).
        rewrite Znth_cons in Hrows by lia.
        replace (r + 1 - 1) with r in Hrows by lia.
        exact Hrows.
      * rewrite Zlength_cons in Hi. lia.
      * exact Hj.
Qed.
Lemma xrows_cell_bounds__scan_entry :
  forall k m n xrows ins i j d,
    1 <= n -> 1 <= m ->
    (forall q, 0 <= q < n * m ->
       0 <= Znth q (concat ins) 0 <= k) ->
    n = Zlength ins ->
    (forall r, 0 <= r < n -> Zlength (Znth r ins d) = m) ->
    (forall r, 0 <= r < n ->
       sublist 0 m (Znth r xrows d) = Znth r ins d) ->
    0 <= i < n -> 0 <= j < m ->
    0 <= Znth j (Znth i xrows d) 0 <= k.
Proof.
  intros k m n xrows ins i j d Hn Hm Hbounds Hnins Hrows Hsub Hi Hj.
  specialize (Hbounds (i * m + j) ltac:(nia)).
  assert (Hrows' : forall r, 0 <= r < Zlength ins ->
      Zlength (Znth r ins d) = m).
  { intros r Hr. apply Hrows. rewrite Hnins. exact Hr. }
  assert (Hi' : 0 <= i < Zlength ins) by (rewrite <- Hnins; exact Hi).
  pose proof
    (Znth_concat_rect__scan_entry ins d m i j ltac:(lia) Hrows' Hi' Hj)
    as Hflat.
  rewrite <- Hflat in Hbounds.
  rewrite <- (Hsub i Hi) in Hbounds.
  rewrite Znth_sublist0 in Hbounds by lia.
  exact Hbounds.
Qed.
Lemma set_card_empty__scan_entry :
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
Lemma lock_times_before_succ_eq__scan_entry :
  forall ins times j,
    0 <= j ->
    LockTimesThrough ins times j ->
    lock_times_before times (j + 1) = times.
Proof.
  intros ins times j Hj Hthrough.
  destruct Hthrough as [Hlen Hcases].
  assert (Hvals : forall i, 0 <= i < Zlength times ->
      Znth i times 0 = 0 \/ 1 <= Znth i times 0 <= j).
  { intros i Hi.
    specialize (Hcases i).
    rewrite Hlen in Hi.
    specialize (Hcases Hi).
    destruct Hcases as [[Hzero _] | [Hbounds _]].
    - left. exact Hzero.
    - right. exact Hbounds. }
  unfold lock_times_before.
  clear Hlen Hcases ins.
  induction times as [|u us IH].
  - reflexivity.
  - simpl map.
    f_equal.
    + assert (H0 : 0 <= 0 < Zlength (u :: us)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg us). lia. }
      specialize (Hvals 0 H0).
      unfold Znth in Hvals. simpl in Hvals.
      destruct (u <? j + 1) eqn:Hlt; [reflexivity |].
      apply Z.ltb_ge in Hlt.
      destruct Hvals as [Hz | Hu]; lia.
    + apply IH.
      intros i Hi.
      specialize (Hvals (i + 1)).
      rewrite Zlength_cons in Hvals.
      specialize (Hvals ltac:(lia)).
      rewrite Znth_cons in Hvals by lia.
      replace (i + 1 - 1) with i in Hvals by lia.
      exact Hvals.
Qed.
Lemma direct_lock_scan_zero__scan_entry :
  forall ins times j,
    0 <= j ->
    LockTimesThrough ins times j ->
    DirectLockScan ins times (j + 1) 0.
Proof.
  intros ins times j Hj Hthrough.
  pose proof (lock_times_before_succ_eq__scan_entry ins times j Hj Hthrough)
    as Hbefore.
  unfold DirectLockScan.
  rewrite Hbefore.
  replace (j + 1 - 1) with j by lia.
  split; [exact Hthrough |].
  split.
  - exact (proj1 Hthrough).
  - intros i Hi.
    split.
    + split.
      * intro Heq.
        specialize (proj2 Hthrough i Hi) as Hcase.
        destruct Hcase as [[Hzero _] | [Hbounds _]]; lia.
      * intros [Hilt _]. lia.
    + intros _. reflexivity.
Qed.
Lemma set_card_Z_as_sum__direct_scan_step :
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
  { induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH. }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_true__direct_scan_step :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__direct_scan_step.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)); [lia | contradiction].
Qed.
Lemma set_card_Z_extend_false__direct_scan_step :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__direct_scan_step.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)); [contradiction | lia].
Qed.
Lemma replace_nth_length__direct_scan_step :
  forall {A : Type} m (a : A) l,
    length (replace_nth m l a) = length l.
Proof.
  intros A m a l; revert l.
  induction m; intros l; destruct l; simpl; try reflexivity.
  rewrite IHm; reflexivity.
Qed.
Lemma Zlength_replace_Znth__direct_scan_step :
  forall {A : Type} n (a : A) l,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros A n a l.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite replace_nth_length__direct_scan_step.
  reflexivity.
Qed.
Lemma map_replace_Znth__direct_scan_step :
  forall (A B : Type) (f : A -> B) n x (xs : list A),
    map f (replace_Znth n x xs) =
    replace_Znth n (f x) (map f xs).
Proof.
  intros A B f n x xs.
  unfold replace_Znth.
  generalize (Z.to_nat n) as k.
  induction xs as [|a xs IH]; intros k; destruct k; simpl; auto.
  rewrite IH; reflexivity.
Qed.
Lemma lock_times_before_update__direct_scan_step :
  forall times i t,
    0 <= i < Zlength times -> Znth i times 0 = 0 ->
    lock_times_before (replace_Znth i t times) t =
    lock_times_before times t.
Proof.
  intros times i t _ Hzero.
  unfold lock_times_before, replace_Znth, Znth in *.
  remember (Z.to_nat i) as n.
  clear i Heqn.
  revert times Hzero.
  induction n as [|n IH]; intros times Hzero; destruct times as [|a times];
    simpl in *; try reflexivity.
  - subst a. rewrite Z.ltb_irrefl. destruct (0 <? t); reflexivity.
  - f_equal. apply IH. exact Hzero.
Qed.
Lemma xrow_cell__direct_scan_step :
  forall xrows ins n m i j d,
    (forall r, 0 <= r < n ->
      Zlength (Znth r xrows d) = 105 /\
      sublist 0 m (Znth r xrows d) = Znth r ins d) ->
    0 <= i < n -> 0 <= j < m ->
    Znth j (Znth i xrows d) 0 = Znth j (Znth i ins d) 0.
Proof.
  intros xrows ins n m i j d Hrows Hi Hj.
  specialize (Hrows i Hi) as [_ Hsub].
  rewrite <- Hsub.
  rewrite Znth_sublist0 by lia.
  reflexivity.
Qed.
Lemma dead_cell_false__direct_scan_step :
  forall ins times k t dead cell,
    DeadCellsBefore ins times k t dead ->
    1 <= cell <= k -> Znth cell dead 0 = 0 ->
    ~ CellWasDead ins (lock_times_before times t) (t - 1) cell.
Proof.
  intros ins times k t dead cell Hdead Hcell Hzero.
  unfold DeadCellsBefore, DeadCellsThrough in Hdead.
  destruct Hdead as [_ [_ Hdead]].
  specialize (Hdead cell Hcell) as [_ Hiff].
  intro Hwas.
  apply Hiff in Hwas.
  lia.
Qed.
Lemma dead_cell_true__direct_scan_step :
  forall ins times k t dead cell,
    DeadCellsBefore ins times k t dead ->
    1 <= cell <= k -> Znth cell dead 0 <> 0 ->
    CellWasDead ins (lock_times_before times t) (t - 1) cell.
Proof.
  intros ins times k t dead cell Hdead Hcell Hnz.
  unfold DeadCellsBefore, DeadCellsThrough in Hdead.
  destruct Hdead as [_ [_ Hdead]].
  specialize (Hdead cell Hcell) as [Hbound Hiff].
  apply Hiff.
  lia.
Qed.
Lemma writer_count_increment_bound__direct_scan_step :
  forall ins times t scanned k counts cell,
    WriterCounts ins times t scanned k counts ->
    0 <= cell <= k ->
    0 <= Znth cell counts 0 <= scanned.
Proof.
  intros ins times t scanned k counts cell Hcounts Hcell.
  unfold WriterCounts in Hcounts.
  destruct Hcounts as [_ Hcounts].
  exact (proj2 (Hcounts cell Hcell)).
Qed.
Lemma writer_counts_step__direct_scan_step :
  forall ins times t i k counts cell0,
    0 <= i -> 0 <= cell0 <= k ->
    Znth i (lock_times_before times t) 0 = 0 ->
    cell0 <> 0 ->
    Znth (t - 1) (Znth i ins []) 0 = cell0 ->
    ~ CellWasDead ins (lock_times_before times t) (t - 1) cell0 ->
    WriterCounts ins times t i k counts ->
    WriterCounts ins times t (i + 1) k
      (replace_Znth cell0 (Znth cell0 counts 0 + 1) counts).
Proof.
  intros ins times t i k counts cell0 Hi Hcell0 Hold Hnz Hcur Hlive Hcounts.
  unfold WriterCounts in *.
  destruct Hcounts as [Hlen Hcounts].
  split.
  - rewrite Zlength_replace_Znth__direct_scan_step; exact Hlen.
  - intros cell Hcell.
    specialize (Hcounts cell Hcell) as [Heq Hbound].
    destruct (Z.eq_dec cell cell0) as [-> | Hdiff].
    + rewrite Znth_replace_Znth_Same by lia.
      split.
      * rewrite set_card_Z_extend_true__direct_scan_step by
          first [lia | repeat split; assumption].
        rewrite Heq. reflexivity.
      * lia.
    + rewrite Znth_replace_Znth_Diff by lia.
      split.
      * rewrite set_card_Z_extend_false__direct_scan_step.
        -- exact Heq.
        -- lia.
        -- intros [_ [_ [Heqcell _]]].
           rewrite Hcur in Heqcell. apply Hdiff. symmetry. exact Heqcell.
      * lia.
Qed.
Lemma writer_counts_skip_step__direct_scan_step :
  forall ins times t i k counts,
    0 <= i ->
    ~ (Znth i (lock_times_before times t) 0 = 0 /\
       Znth (t - 1) (Znth i ins []) 0 <> 0 /\
       ~ CellWasDead ins (lock_times_before times t) (t - 1)
          (Znth (t - 1) (Znth i ins []) 0)) ->
    WriterCounts ins times t i k counts ->
    WriterCounts ins times t (i + 1) k counts.
Proof.
  intros ins times t i k counts Hi Hskip Hcounts.
  unfold WriterCounts in *.
  destruct Hcounts as [Hlen Hcounts].
  split; [exact Hlen |].
  intros cell Hcell.
  specialize (Hcounts cell Hcell) as [Heq Hbound].
  split.
  - rewrite set_card_Z_extend_false__direct_scan_step.
    + exact Heq.
    + lia.
    + intros [Hold [Hnz [Hcell_eq Hnotdead]]].
      apply Hskip. rewrite Hcell_eq. repeat split; assumption.
  - lia.
Qed.
Lemma direct_lock_scan_step__direct_scan_step :
  forall ins times t i,
    0 <= i < Zlength ins ->
    ~ (Znth i (lock_times_before times t) 0 = 0 /\
       Znth (t - 1) (Znth i ins []) 0 <> 0 /\
       CellWasDead ins (lock_times_before times t) (t - 1)
         (Znth (t - 1) (Znth i ins []) 0)) ->
    DirectLockScan ins times t i ->
    DirectLockScan ins times t (i + 1).
Proof.
  intros ins times t i Hi Hskip Hscan.
  unfold DirectLockScan in *.
  destruct Hscan as [Hthrough [Hlen Hscan]].
  split; [exact Hthrough |].
  split; [exact Hlen |].
  intros q Hq.
  specialize (Hscan q Hq) as [Hiff Hsame].
  split; [|exact Hsame].
  destruct (Z.eq_dec q i) as [-> | Hneq].
  - assert (Hnot_t : Znth i times 0 <> t).
    { intro Heq. apply Hiff in Heq. lia. }
    split.
    + intro Heq. contradiction.
    + intros [_ Hrest]. exfalso. apply Hskip. exact Hrest.
  - rewrite Hiff.
    split; intros [Hlt Hrest]; split; try assumption; lia.
Qed.
Lemma direct_lock_scan_lock_step__direct_scan_step :
  forall ins times t i,
    0 <= i < Zlength ins ->
    Zlength times = Zlength ins ->
    Znth i times 0 = 0 ->
    Znth (t - 1) (Znth i ins []) 0 <> 0 ->
    CellWasDead ins (lock_times_before times t) (t - 1)
      (Znth (t - 1) (Znth i ins []) 0) ->
    DirectLockScan ins times t i ->
    DirectLockScan ins (replace_Znth i t times) t (i + 1).
Proof.
  intros ins times t i Hi Hlen Hzero Hcell Hdead Hscan.
  assert (Hold : lock_times_before (replace_Znth i t times) t =
      lock_times_before times t).
  { apply lock_times_before_update__direct_scan_step; [lia | exact Hzero]. }
  unfold DirectLockScan in *.
  destruct Hscan as [Hthrough [_ Hscan]].
  rewrite Hold.
  split; [exact Hthrough |].
  split.
  - rewrite Zlength_replace_Znth__direct_scan_step; exact Hlen.
  - intros q Hq.
    specialize (Hscan q Hq) as [Hiff Hsame].
    destruct (Z.eq_dec q i) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by lia.
      split.
      * split; [intro; repeat split; try lia; assumption | tauto].
      * intros Hbad; contradiction.
    + rewrite Znth_replace_Znth_Diff by lia.
      split.
      * rewrite Hiff. assert (q < i + 1 <-> q < i) by lia. tauto.
      * exact Hsame.
Qed.
Lemma dead_cells_before_lock_update__direct_scan_step :
  forall ins times k t dead i,
    0 <= i < Zlength times -> Znth i times 0 = 0 ->
    DeadCellsBefore ins times k t dead ->
    DeadCellsBefore ins (replace_Znth i t times) k t dead.
Proof.
  intros ins times k t dead i Hi Hzero Hdead.
  unfold DeadCellsBefore in *.
  rewrite lock_times_before_update__direct_scan_step by assumption.
  exact Hdead.
Qed.
Lemma ge_to_le__collision_init_mark : forall x : Z, x >= 2 -> 2 <= x.
Proof. intros x H. apply Z.ge_le. exact H. Qed.
Lemma set_card_empty__collision_init_mark :
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
Lemma direct_scan_complete__collision_init_mark :
  forall ins times counts dead t scanned k,
    1 <= k ->
    scanned = Zlength ins ->
    DirectLockScan ins times t scanned ->
    WriterCounts ins times t scanned k counts ->
    DeadCellsBefore ins times k t dead ->
    WriterCounts ins times t (Zlength ins) k counts /\
    CellMarksPrefix ins times counts k t 1 dead /\
    CollisionClosurePrefix ins times counts t 1 0.
Proof.
  intros ins times counts dead t scanned k Hk Hsc Hscan Hcounts Hdead.
  subst scanned.
  assert (Hzero_count : Znth 0 counts 0 = 0).
  {
    pose proof Hcounts as Hcounts0.
    unfold WriterCounts in Hcounts0.
    destruct Hcounts0 as [Hcountlen Hcounts0].
    specialize (Hcounts0 0 ltac:(lia)).
    destruct Hcounts0 as [Heq Hrange].
    rewrite Heq.
    apply set_card_empty__collision_init_mark.
    intros idx [_ [_ [Hfalse _]]].
    exact (Hfalse eq_refl).
  }
  split; [exact Hcounts|].
  split.
  - unfold DeadCellsBefore, DeadCellsThrough in Hdead.
    unfold CellMarksPrefix.
    destruct Hdead as [Hlen [Hzero Hall]].
    split; [exact Hlen|].
    split; [exact Hzero|].
    intros cell Hcell.
    specialize (Hall cell Hcell).
    destruct Hall as [Hrange Hiff].
    split; [exact Hrange|].
    rewrite Hiff.
    intuition lia.
  - unfold DirectLockScan in Hscan.
    unfold CollisionClosurePrefix.
    destruct Hscan as [Hthrough [Hlen Hall]].
    split; [exact Hthrough|].
    split; [exact Hlen|].
    intros idx Hidx.
    specialize (Hall idx Hidx).
    destruct Hall as [Hiff Hstable].
    split; [|exact Hstable].
    rewrite Hiff.
    split.
    + intros [_ [Hold [Hnz Hwas]]].
      repeat split; try assumption.
      left; exact Hwas.
    + intros [Hold [Hnz [Hwas | [Hcount [Hlt | [Heq Hidxneg]]]]]].
      * repeat split; try assumption; lia.
      * remember (Znth (t - 1) (Znth idx ins []) 0) as cell eqn:Hcell.
        unfold Znth in Hcount, Hzero_count.
        destruct cell; simpl in Hcount, Hzero_count; lia.
      * lia.
Qed.
Lemma Zlength_replace_Znth__collision_init_mark :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v.
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
Lemma cell_marks_set_collision__collision_init_mark :
  forall ins times counts dead k t c,
    1 <= c <= k ->
    k <= 100 ->
    2 <= Znth c counts 0 ->
    CellMarksPrefix ins times counts k t c dead ->
    CellMarksPrefix ins times counts k t (c + 1) (replace_Znth c 1 dead).
Proof.
  intros ins times counts dead k t c Hc Hk Hcount Hmarks.
  unfold CellMarksPrefix in *.
  destruct Hmarks as [Hlen [Hzero Hall]].
  split.
  - rewrite Zlength_replace_Znth__collision_init_mark; exact Hlen.
  - split.
    + rewrite Znth_replace_Znth_Diff; try lia.
    + intros cell Hcell.
      specialize (Hall cell Hcell).
      destruct Hall as [Hrange Hiff].
      destruct (Z.eq_dec cell c) as [Heq | Hneq].
      * subst cell.
        rewrite Znth_replace_Znth_Same by lia.
        split; [lia|].
        split; [intros; right; split; lia|intros; reflexivity].
      * rewrite Znth_replace_Znth_Diff by lia.
        split; [exact Hrange|].
        rewrite Hiff.
        intuition lia.
Qed.
Lemma map_replace_Znth__collision_core_closure :
  forall (A B : Type) (f : A -> B) n x (xs : list A),
    map f (replace_Znth n x xs) =
    replace_Znth n (f x) (map f xs).
Proof.
  intros A B f n x xs.
  unfold replace_Znth.
  generalize (Z.to_nat n) as k.
  induction xs as [|a xs IH]; intros k; destruct k; simpl; auto.
  rewrite IH. reflexivity.
Qed.
Lemma Znth_map_inbounds__collision_core_closure :
  forall (A B : Type) (f : A -> B) (l : list A)
    (i : Z) (da : A) (db : B),
    0 <= i < Zlength l ->
    Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f da)).
  - apply nth_indep. rewrite length_map. rewrite Zlength_correct in Hi. lia.
  - apply map_nth.
Qed.
Lemma Zlength_replace_Znth__collision_core_closure :
  forall (A : Type) (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. revert n.
  induction l; simpl in *; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat n).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n0)).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma lock_times_before_replace_current__collision_core_closure :
  forall times i t,
    0 <= i < Zlength times ->
    Znth i times 0 = 0 ->
    lock_times_before (replace_Znth i t times) t =
    lock_times_before times t.
Proof.
  intros times i t Hi Hzero.
  unfold lock_times_before.
  rewrite map_replace_Znth__collision_core_closure.
  rewrite Z.ltb_irrefl.
  set (mapped := map (fun u : Z => if u <? t then u else 0) times).
  assert (Hmapped : Znth i mapped 0 = 0).
  { unfold mapped.
    rewrite (Znth_map_inbounds__collision_core_closure
               Z Z (fun u : Z => if u <? t then u else 0) times i 0 0 Hi).
    rewrite Hzero. destruct (0 <? t); reflexivity. }
  transitivity (replace_Znth i (Znth i mapped 0) mapped).
  - rewrite Hmapped. reflexivity.
  - apply replace_Znth_Znth.
Qed.
Lemma cell_marks_current_lock_stable__collision_core_closure :
  forall ins times counts k t completed dead i,
    0 <= i < Zlength times ->
    Znth i times 0 = 0 ->
    CellMarksPrefix ins times counts k t completed dead ->
    CellMarksPrefix ins (replace_Znth i t times) counts k t completed dead.
Proof.
  intros ins times counts k t completed dead i Hi Hzero Hmarks.
  unfold CellMarksPrefix in *.
  rewrite lock_times_before_replace_current__collision_core_closure by assumption.
  exact Hmarks.
Qed.
Lemma writer_counts_current_lock_stable__collision_core_closure :
  forall ins times counts t scanned k i,
    0 <= i < Zlength times ->
    Znth i times 0 = 0 ->
    WriterCounts ins times t scanned k counts ->
    WriterCounts ins (replace_Znth i t times) t scanned k counts.
Proof.
  intros ins times counts t scanned k i Hi Hzero Hcounts.
  unfold WriterCounts in *.
  rewrite lock_times_before_replace_current__collision_core_closure by assumption.
  exact Hcounts.
Qed.
Lemma collision_closure_step_match__collision_core_closure :
  forall ins times counts t cursor i,
    0 <= i < Zlength ins ->
    Znth i times 0 = 0 ->
    Znth (t - 1) (Znth i ins []) 0 = cursor ->
    cursor <> 0 ->
    2 <= Znth cursor counts 0 ->
    CollisionClosurePrefix ins times counts t cursor i ->
    CollisionClosurePrefix ins (replace_Znth i t times) counts t cursor (i + 1).
Proof.
  intros ins times counts t cursor i Hi Hzero Hcell Hcursor Hcount Hclosure.
  unfold CollisionClosurePrefix in *.
  destruct Hclosure as [Hthrough [Hlength Hall]].
  assert (Hitimes : 0 <= i < Zlength times) by lia.
  pose proof (lock_times_before_replace_current__collision_core_closure
                times i t Hitimes Hzero) as Hold.
  rewrite Hold.
  split; [exact Hthrough|].
  split; [rewrite Zlength_replace_Znth__collision_core_closure; exact Hlength|].
  intros q Hq.
  specialize (Hall q Hq).
  destruct Hall as [Hiff Hneq].
  destruct (Z.eq_dec q i) as [->|Hqi].
  - rewrite (Znth_replace_Znth_Same 0) by exact Hitimes.
    split.
    + split.
      * intros _. rewrite Hcell. repeat split.
        -- unfold lock_times_before.
           rewrite (Znth_map_inbounds__collision_core_closure
                      Z Z (fun u : Z => if u <? t then u else 0) times i 0 0 Hitimes).
           rewrite Hzero. destruct (0 <? t); reflexivity.
        -- exact Hcursor.
        -- right. split; [exact Hcount|]. right. split; lia.
      * intros _. reflexivity.
    + intros Hbad. exfalso. apply Hbad. reflexivity.
  - assert (Hqtimes : 0 <= q < Zlength times) by lia.
    rewrite (Znth_replace_Znth_Diff 0 times i q t) by (try assumption; congruence).
    split.
    + split.
      * intro Htq. apply Hiff in Htq.
        destruct Htq as [Holdq [Hcellq Hcase]].
        repeat split; try assumption.
        destruct Hcase as [Hdead|[Hcnt [Hlt|[Heq Hlt]]]].
        -- left; exact Hdead.
        -- right; split; [exact Hcnt|]. left; exact Hlt.
        -- right; split; [exact Hcnt|]. right; split; [exact Heq|lia].
      * intros [Holdq [Hcellq Hcase]]. apply Hiff.
        repeat split; try assumption.
        destruct Hcase as [Hdead|[Hcnt [Hlt|[Heq Hlt]]]].
        -- left; exact Hdead.
        -- right; split; [exact Hcnt|]. left; exact Hlt.
        -- right; split; [exact Hcnt|]. right; split; [exact Heq|lia].
    + exact Hneq.
Qed.
Lemma collision_closure_step_skip__collision_core_closure :
  forall ins times counts t cursor i,
    0 <= i < Zlength ins ->
    (Znth i times 0 <> 0 \/
     Znth (t - 1) (Znth i ins []) 0 <> cursor) ->
    CollisionClosurePrefix ins times counts t cursor i ->
    CollisionClosurePrefix ins times counts t cursor (i + 1).
Proof.
  intros ins times counts t cursor i Hi Hskip Hclosure.
  unfold CollisionClosurePrefix in *.
  destruct Hclosure as [Hthrough [Hlen Hall]].
  split; [exact Hthrough|]. split; [exact Hlen|].
  intros q Hq. specialize (Hall q Hq).
  destruct Hall as [Hiff Hneq].
  split.
  - split.
    + intro Htq. apply Hiff in Htq.
      destruct Htq as [Holdq [Hcellq Hcase]].
      repeat split; try assumption.
      destruct Hcase as [Hdead|[Hcnt [Hlt|[Heq Hlt]]]].
      * left; exact Hdead.
      * right; split; [exact Hcnt|]. left; exact Hlt.
      * right; split; [exact Hcnt|]. right; split; [exact Heq|lia].
    + intros [Holdq [Hcellq Hcase]].
      destruct Hcase as [Hdead|[Hcnt [Hlt|[Heq Hlt]]]].
      * apply Hiff. repeat split; try assumption. left; exact Hdead.
      * apply Hiff. repeat split; try assumption.
        right; split; [exact Hcnt|]. left; exact Hlt.
      *
        destruct (Z.eq_dec q i) as [->|Hqi].
        -- destruct Hskip as [Hlocked|Hdifferent].
           ++ destruct (Z.eq_dec (Znth i times 0) t) as [Heqt|Hnet].
              ** exact Heqt.
              ** exfalso. apply Hlocked. rewrite (Hneq Hnet). exact Holdq.
           ++ exfalso. apply Hdifferent. exact Heq.
        -- apply Hiff. repeat split; try assumption.
           right. split; [exact Hcnt|]. right. split; [exact Heq|lia].
  - exact Hneq.
Qed.
Lemma Zlength_map__collision_cell_exit : forall {A B : Type} (f : A -> B) xs,
  Zlength (map f xs) = Zlength xs.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.
Lemma Znth_map__collision_cell_exit : forall {A B : Type} (f : A -> B) xs
    (da : A) (db : B) i,
  0 <= i < Zlength xs ->
  Znth i (map f xs) db = f (Znth i xs da).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intros da db i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct (Z.eq_dec i 0) as [-> | Hne].
    + simpl. rewrite !Znth0_cons. reflexivity.
    + simpl. rewrite !Znth_cons by lia.
      apply IH. rewrite Zlength_cons in Hi. lia.
Qed.
Lemma set_card_at_most_singleton__collision_cell_exit :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x,
    (forall y, P y -> y = x) -> @set_card A P FP <= 1.
Proof.
  intros A P FP x Honly. unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|a [|b l]] eqn:Henum; simpl; try lia.
  exfalso.
  assert (Ha : P a).
  { apply (proj2 (@enum_ok A P FP a)). rewrite Henum. simpl. auto. }
  assert (Hb : P b).
  { apply (proj2 (@enum_ok A P FP b)). rewrite Henum. simpl. auto. }
  pose proof (@enum_nodup A P FP) as Hnd.
  rewrite Henum in Hnd. inversion Hnd; subst.
  apply H1. left. rewrite (Honly _ Ha), (Honly _ Hb). reflexivity.
Qed.
Lemma set_card_member_other__collision_cell_exit :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x,
    P x -> 2 <= @set_card A P FP -> exists y, P y /\ y <> x.
Proof.
  intros A P FP x Hx Hcard.
  destruct (classic (exists y, P y /\ y <> x)) as [Hex | Hnone]; auto.
  exfalso.
  assert (Honly : forall y, P y -> y = x).
  { intros y Hy. destruct (classic (y = x)) as [Heq | Hneq]; auto.
    exfalso. apply Hnone. exists y. split; assumption. }
  pose proof (set_card_at_most_singleton__collision_cell_exit P FP x Honly).
  lia.
Qed.
Lemma set_card_two_members__collision_cell_exit :
  forall {A : Type} (P : A -> Prop) (FP : Finite P) x y,
    x <> y -> P x -> P y -> 2 <= @set_card A P FP.
Proof.
  intros A P FP x y Hxy Hx Hy.
  unfold set_card, SumLib.Sum.sum.
  assert (Hinx : In x (@enum A P FP)).
  { apply (proj1 (@enum_ok A P FP x)); exact Hx. }
  assert (Hiny : In y (@enum A P FP)).
  { apply (proj1 (@enum_ok A P FP y)); exact Hy. }
  assert (Hfold : forall l : list A,
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
    Z.of_nat (length l)).
  { intro l. induction l as [|z zs IH]; [reflexivity|].
    change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 zs =
            Z.of_nat (S (length zs))).
    rewrite IH, Nat2Z.inj_succ; lia. }
  rewrite Hfold.
  change (Z.of_nat 2 <= Z.of_nat (length (@enum A P FP))).
  apply (proj1 (Nat2Z.inj_le 2 (length (@enum A P FP)))).
  change (length [x; y] <= length (@enum A P FP))%nat.
  eapply NoDup_incl_length.
  - constructor.
    + simpl. intros [Heq | []]. apply Hxy; symmetry; exact Heq.
    + constructor; [simpl; tauto|constructor].
  - intros z [Hz | [Hz | []]]; subst; assumption.
Qed.
Lemma set_card_positive_member__collision_cell_exit :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    1 <= @set_card A P FP -> exists x, P x.
Proof.
  intros A P FP Hcard.
  unfold set_card, SumLib.Sum.sum in Hcard.
  destruct (@enum A P FP) as [|x xs] eqn:Henum; simpl in Hcard; [lia |].
  exists x. apply (proj2 (@enum_ok A P FP x)).
  rewrite Henum. simpl. auto.
Qed.
Lemma collision_closure_cycle_dead__collision_cell_exit :
  forall ins times counts k t cursor dead,
    1 <= t ->
    cursor > k -> cursor <= k + 1 ->
    WriterCounts ins times t (Zlength ins) k counts ->
    CellMarksPrefix ins times counts k t cursor dead ->
    CollisionClosurePrefix ins times counts t cursor 0 ->
    DeadCellsThrough ins times k t dead.
Proof.
  intros ins times counts k t cursor dead Ht Hcursor Hcursor' Hcounts Hmarks Hclosure.
  unfold WriterCounts in Hcounts; cbn zeta in Hcounts.
  unfold CellMarksPrefix in Hmarks; cbn zeta in Hmarks.
  unfold CollisionClosurePrefix in Hclosure; cbn zeta in Hclosure.
  destruct Hcounts as [Hcounts_len Hcount].
  destruct Hmarks as [Hdead_len [Hdead_zero Hmark]].
  destruct Hclosure as [Hold_through [Htimes_len Hrel]].
  unfold DeadCellsThrough.
  split; [exact Hdead_len |].
  split; [exact Hdead_zero |].
  intros cell Hcell.
  specialize (Hmark cell Hcell).
  destruct Hmark as [Hbit Hmark].
  split; [exact Hbit |].
  split; intro Hdead.
  - apply Hmark in Hdead.
    destruct Hdead as [Hwas | [Hbelow Htwo]].
    + unfold CellWasDead in Hwas |- *.
      destruct Hwas as [i [Hi [Hu Hrow]]].
      specialize (Hrel i Hi).
      destruct Hrel as [Hnew Hstable].
      destruct (Z.eq_dec (Znth i times 0) t) as [Heq | Hneq].
      * apply Hnew in Heq. lia.
      * assert (Heqtime := Hstable Hneq).
        exists i. split; [exact Hi |]. split.
        -- rewrite Heqtime. lia.
        -- rewrite Heqtime. exact Hrow.
    + specialize (Hcount cell ltac:(lia)).
      destruct Hcount as [Hcard _].
      assert (Hcard2 : 2 <= #(fun i : Z =>
          0 <= i < Zlength ins /\
          Znth i (lock_times_before times t) 0 = 0 /\
          cell <> 0 /\
          Znth (t - 1) (Znth i ins []) 0 = cell /\
          ~ CellWasDead ins (lock_times_before times t) (t - 1) cell)).
      { rewrite <- Hcard. exact Htwo. }
      assert (Hcard1 : 1 <= #(fun i : Z =>
          0 <= i < Zlength ins /\
          Znth i (lock_times_before times t) 0 = 0 /\
          cell <> 0 /\
          Znth (t - 1) (Znth i ins []) 0 = cell /\
          ~ CellWasDead ins (lock_times_before times t) (t - 1) cell)) by lia.
      destruct (@set_card_positive_member__collision_cell_exit Z
        (fun i : Z =>
          0 <= i < Zlength ins /\
          Znth i (lock_times_before times t) 0 = 0 /\
          cell <> 0 /\
          Znth (t - 1) (Znth i ins []) 0 = cell /\
          ~ CellWasDead ins (lock_times_before times t) (t - 1) cell)
        _ Hcard1)
        as [i [Hi [Hold [Hnz [Hrow Hnotdead]]]]].
      specialize (Hrel i Hi).
      destruct Hrel as [Hnew _].
      assert (Hnewtime : Znth i times 0 = t).
      { apply Hnew. split; [exact Hold |].
        split; [rewrite Hrow; exact Hnz |].
        right. split; [rewrite Hrow; exact Htwo |].
        left. rewrite Hrow. exact Hbelow. }
      unfold CellWasDead. exists i. split; [exact Hi |].
      split; [lia | rewrite Hnewtime; exact Hrow].
  - unfold CellWasDead in Hdead.
    destruct Hdead as [i [Hi [Hu Hrow]]].
    apply Hmark.
    specialize (Hrel i Hi).
    destruct Hrel as [Hnew Hstable].
    destruct (Z.eq_dec (Znth i times 0) t) as [Heq | Hneq].
    + assert (Heqtime := Heq). rewrite Heqtime in Hrow.
      apply Hnew in Heq.
      destruct Heq as [Hold [Hnz [Hwas | [Htwo [Hbelow | [Heqcell Hneg]]]]]].
      * left. rewrite Hrow in Hwas. exact Hwas.
      * right. rewrite Hrow in Htwo, Hbelow. split; assumption.
      * lia.
    + left. unfold CellWasDead. exists i. split; [exact Hi |].
      assert (Heqtime := Hstable Hneq).
      split.
      * rewrite <- Heqtime. lia.
      * rewrite <- Heqtime. exact Hrow.
Qed.
Lemma Znth_concat_uniform__collision_cell_exit :
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
Lemma collision_closure_cycle_complete__collision_cell_exit :
  forall ins times counts k t cursor,
    1 <= t ->
    cursor > k -> cursor <= k + 1 ->
    (forall i, 0 <= i < Zlength ins ->
       t <= Zlength (Znth i ins [])) ->
    (forall i, 0 <= i < Zlength ins ->
       0 <= Znth (t - 1) (Znth i ins []) 0 <= k) ->
    WriterCounts ins times t (Zlength ins) k counts ->
    CollisionClosurePrefix ins times counts t cursor 0 ->
    LockTimesThrough ins times t.
Proof.
  intros ins times counts k t cursor Ht Hcursor Hcursor' Hrowlen Hcellbound
    Hcounts Hclosure.
  unfold WriterCounts in Hcounts; cbn zeta in Hcounts.
  unfold CollisionClosurePrefix in Hclosure; cbn zeta in Hclosure.
  set (old := lock_times_before times t) in *.
  destruct Hcounts as [Hcounts_len Hcount].
  destruct Hclosure as [Hold [Htimes_len Hrel]].
  unfold LockTimesThrough in Hold.
  destruct Hold as [Hold_len Hold].
  assert (Hval : forall q v,
      0 <= q < Zlength ins -> 1 <= v < t ->
      (Znth q times 0 = v <-> Znth q old 0 = v)).
  { intros q v Hq Hv. specialize (Hrel q Hq).
    destruct Hrel as [Hnew Hstable]. split; intro Heq.
    - rewrite <- Heq. symmetry. apply Hstable. lia.
    - destruct (Z.eq_dec (Znth q times 0) t) as [Hqt | Hqnt].
      + apply Hnew in Hqt. destruct Hqt as [Hz _]. rewrite Heq in Hz. lia.
      + rewrite Hstable by exact Hqnt. exact Heq. }
  assert (Hzf : forall q u,
      0 <= q < Zlength ins -> 1 <= u < t ->
      ((Znth q times 0 = 0 \/ u <= Znth q times 0) <->
       (Znth q old 0 = 0 \/ u <= Znth q old 0))).
  { intros q u Hq Hu. specialize (Hrel q Hq).
    destruct Hrel as [Hnew Hstable]. split; intro Hcase.
    - destruct Hcase as [Hz | Hge].
      + left. rewrite <- (Hstable ltac:(lia)). exact Hz.
      + destruct (Z.eq_dec (Znth q times 0) t) as [Hqt | Hqnt].
        * left. apply Hnew in Hqt. tauto.
        * right. rewrite <- (Hstable Hqnt). exact Hge.
    - destruct Hcase as [Hz | Hge].
      + destruct (Z.eq_dec (Znth q times 0) t) as [Hqt | Hqnt].
        * right. lia.
        * left. rewrite Hstable by exact Hqnt. exact Hz.
      + destruct (Z.eq_dec (Znth q times 0) t) as [Hqt | Hqnt].
        * right. lia.
        * right. rewrite Hstable by exact Hqnt. exact Hge. }
  assert (Htrigger_before : forall i u,
      0 <= i < Zlength ins -> 1 <= u < t ->
      (LockTrigger ins times i u <-> LockTrigger ins old i u)).
  { intros i u Hi Hu. unfold LockTrigger. split; intro Htrig.
    - destruct Htrig as [Hub [Hnz Hcase]].
      split; [exact Hub |]. split; [exact Hnz |].
      destruct Hcase as [Hprior | Hother].
      + destruct Hprior as [q [v [Hq [Hv [Hqv Hsame]]]]].
        left. exists q, v. split; [exact Hq |]. split; [exact Hv |]. split.
        * apply (proj1 (Hval q v Hq ltac:(lia))); exact Hqv.
        * exact Hsame.
      + destruct Hother as [q [Hq [Hne [Hfuture Hsame]]]].
        right.
        exists q. split; [exact Hq |]. split; [exact Hne |]. split.
        * apply (proj1 (Hzf q u Hq Hu)); exact Hfuture.
        * exact Hsame.
    - destruct Htrig as [Hub [Hnz Hcase]].
      split; [exact Hub |]. split; [exact Hnz |].
      destruct Hcase as [Hprior | Hother].
      + destruct Hprior as [q [v [Hq [Hv [Hqv Hsame]]]]].
        left. exists q, v. split; [exact Hq |]. split; [exact Hv |]. split.
        * apply (proj2 (Hval q v Hq ltac:(lia))); exact Hqv.
        * exact Hsame.
      + destruct Hother as [q [Hq [Hne [Hfuture Hsame]]]].
        right.
        exists q. split; [exact Hq |]. split; [exact Hne |]. split.
        * apply (proj2 (Hzf q u Hq Hu)); exact Hfuture.
        * exact Hsame. }
  assert (Htrigger_now : forall i,
      0 <= i < Zlength ins -> Znth i old 0 = 0 ->
      (LockTrigger ins times i t <-> Znth i times 0 = t)).
  { intros i Hi Hiold. pose proof (Hrel i Hi) as Hreli.
    destruct Hreli as [Hnew Hstable].
    set (cell := Znth (t - 1) (Znth i ins []) 0) in *.
    assert (Hcell : 0 <= cell <= k) by (apply Hcellbound; exact Hi).
    split; intro Htrig.
    - unfold LockTrigger in Htrig.
      destruct Htrig as [Hub [Hnz Hcase]].
      apply Hnew. split; [exact Hiold |]. split; [exact Hnz |].
      destruct Hcase as [Hprior | Hother].
      + left. unfold CellWasDead.
        destruct Hprior as [q [u [Hq [Hu [Hqu Hsame]]]]].
        exists q. split; [exact Hq |]. split.
        * apply (proj1 (Hval q u Hq ltac:(lia))) in Hqu. lia.
        * apply (proj1 (Hval q u Hq ltac:(lia))) in Hqu.
          rewrite Hqu. exact Hsame.
      + destruct Hother as [q [Hq [Hne [Hfuture Hsame]]]].
        destruct Hfuture as [Hqzero | Hqfuture].
        * specialize (Hrel q Hq). destruct Hrel as [_ Hqstable].
          assert (Hqold : Znth q old 0 = 0).
          { rewrite <- (Hqstable ltac:(lia)); exact Hqzero. }
          destruct (classic (CellWasDead ins old (t - 1) cell)) as [Hdead | Hnotdead].
          -- left; exact Hdead.
          -- right. split.
             ++ specialize (Hcount cell Hcell). destruct Hcount as [Hcard _].
                rewrite Hcard. eapply set_card_two_members__collision_cell_exit
                  with (x := i) (y := q).
                ** intro Heq. apply Hne. symmetry. exact Heq.
                ** split; [exact Hi |]. split; [exact Hiold |].
                   split; [exact Hnz |]. split; [reflexivity | exact Hnotdead].
                ** split; [exact Hq |]. split; [exact Hqold |].
                   split; [exact Hnz |]. split; [exact Hsame | exact Hnotdead].
             ++ left. lia.
        * destruct (Z.eq_dec (Znth q times 0) t) as [Hqt | Hqnt].
          -- specialize (Hrel q Hq). destruct Hrel as [Hqnew _].
             apply Hqnew in Hqt. destruct Hqt as [_ [_ [Hdead | [Htwo _]]]].
             ++ left. rewrite Hsame in Hdead. exact Hdead.
             ++ right. split; [rewrite Hsame in Htwo; exact Htwo |]. left; lia.
          -- specialize (Hrel q Hq). destruct Hrel as [_ Hqstable].
             specialize (Hold q Hq). destruct Hold as [[Hqold _] | [Hqbound _]].
             ++ rewrite Hqstable in Hqfuture by exact Hqnt. lia.
             ++ rewrite Hqstable in Hqfuture by exact Hqnt. lia.
    - apply Hnew in Htrig.
      destruct Htrig as [_ [Hnz Hcause]].
      unfold LockTrigger. split.
      + split; [exact Ht | apply Hrowlen; exact Hi].
      + split; [exact Hnz |].
        destruct (classic (CellWasDead ins old (t - 1) cell)) as [Hwas | Hnotdead].
        * left. unfold CellWasDead in Hwas.
          destruct Hwas as [q [Hq [Hqb Hsame]]].
          exists q, (Znth q old 0). split; [exact Hq |]. split; [lia |]. split.
          -- apply (proj2 (Hval q (Znth q old 0) Hq ltac:(lia))). reflexivity.
          -- exact Hsame.
        * destruct Hcause as [Hwas | [Htwo Hdone]]; [contradiction |].
          right.
          specialize (Hcount cell Hcell). destruct Hcount as [Hcard _].
          assert (Hmember :
              0 <= i < Zlength ins /\ Znth i old 0 = 0 /\ cell <> 0 /\
              Znth (t - 1) (Znth i ins []) 0 = cell /\
              ~ CellWasDead ins old (t - 1) cell).
          { split; [exact Hi |]. split; [exact Hiold |].
            split; [exact Hnz |]. split; [reflexivity | exact Hnotdead]. }
          assert (Hcard2 : 2 <= #(fun q : Z =>
              0 <= q < Zlength ins /\ Znth q old 0 = 0 /\ cell <> 0 /\
              Znth (t - 1) (Znth q ins []) 0 = cell /\
              ~ CellWasDead ins old (t - 1) cell)).
          { rewrite <- Hcard. exact Htwo. }
          destruct (set_card_member_other__collision_cell_exit
            (fun q : Z =>
              0 <= q < Zlength ins /\ Znth q old 0 = 0 /\ cell <> 0 /\
              Znth (t - 1) (Znth q ins []) 0 = cell /\
              ~ CellWasDead ins old (t - 1) cell) _ i Hmember Hcard2)
            as [q [[Hq [Hqold [Hqnz [Hsame Hqnotdead]]]] Hqi]].
          exists q. split; [exact Hq |]. split; [exact Hqi |]. split.
          -- right. specialize (Hrel q Hq). destruct Hrel as [Hqnew _].
             assert (Hqt : Znth q times 0 = t).
             { apply Hqnew. split; [exact Hqold |]. split; [rewrite Hsame; exact Hqnz |].
               right. split; [rewrite Hsame; exact Htwo |].
               left. rewrite Hsame. lia. }
             lia.
          -- exact Hsame. }
  unfold LockTimesThrough. split; [exact Htimes_len |].
  intros i Hi. specialize (Hold i Hi).
  destruct Hold as [[Hiold Hno] | [Hibound [Hitrig Hminimal]]].
  - destruct (Z.eq_dec (Znth i times 0) t) as [Hit | Hint].
    + right. split; [lia |]. split.
      * rewrite Hit. apply (proj2 (Htrigger_now i Hi Hiold)); exact Hit.
      * intros u Hu Htrig. apply (Hno u ltac:(lia)).
        apply (proj1 (Htrigger_before i u Hi ltac:(lia))); exact Htrig.
    + left. split.
      * pose proof (Hrel i Hi) as [_ Histable].
        rewrite Histable by exact Hint. exact Hiold.
      * intros u Hu Htrig.
        destruct (Z.eq_dec u t) as [-> | Hune].
        -- assert (Hit' : Znth i times 0 = t).
           { apply (proj1 (Htrigger_now i Hi Hiold)); exact Htrig. }
           contradiction.
        -- apply (Hno u ltac:(lia)).
           apply (proj1 (Htrigger_before i u Hi ltac:(lia))); exact Htrig.
  - assert (Hint : Znth i times 0 <> t).
    { intro Hit. specialize (Hrel i Hi). destruct Hrel as [Hnew _].
      apply Hnew in Hit. destruct Hit as [Hz _]. lia. }
    assert (Hieq : Znth i times 0 = Znth i old 0).
    { specialize (Hrel i Hi). tauto. }
    right. split; [rewrite Hieq; lia |]. split.
    + rewrite Hieq. apply (proj2 (Htrigger_before i (Znth i old 0) Hi ltac:(lia))).
      exact Hitrig.
    + intros u Hu Htrig. apply (Hminimal u ltac:(rewrite Hieq in Hu; lia)).
      apply (proj1 (Htrigger_before i u Hi ltac:(rewrite Hieq in Hu; lia))).
      exact Htrig.
Qed.
Lemma cell_marks_prefix_advance_no_collision__collision_cell_exit :
  forall ins times counts k t c dead,
    1 <= c <= k ->
    Znth c counts 0 < 2 ->
    CellMarksPrefix ins times counts k t c dead ->
    CellMarksPrefix ins times counts k t (c + 1) dead.
Proof.
  intros ins times counts k t c dead Hc Hcount Hmarks.
  unfold CellMarksPrefix in *; cbn zeta in *.
  destruct Hmarks as [Hlen [Hzero Hmark]].
  split; [exact Hlen |].
  split; [exact Hzero |].
  intros cell0 Hcell.
  specialize (Hmark cell0 Hcell).
  destruct Hmark as [Hbit Hiff].
  split; [exact Hbit |].
  split; intro H.
  - apply Hiff in H.
    destruct H as [Hdead | [Hlt Htwo]].
    + left; exact Hdead.
    + right; split; [lia | exact Htwo].
  - apply Hiff.
    destruct H as [Hdead | [Hlt Htwo]].
    + left; exact Hdead.
    + right.
      destruct (Z_lt_ge_dec cell0 c) as [Hbelow | Hge].
      * split; assumption.
      * assert (cell0 = c) by lia.
        subst cell0; lia.
Qed.
Lemma collision_closure_advance_no_collision__collision_cell_exit :
  forall ins times counts t c,
    Znth c counts 0 < 2 ->
    CollisionClosurePrefix ins times counts t c 0 ->
    CollisionClosurePrefix ins times counts t (c + 1) 0.
Proof.
  intros ins times counts t c Hcount Hclosure.
  unfold CollisionClosurePrefix in *; cbn zeta in *.
  destruct Hclosure as [Hthrough [Hlen Hrel]].
  split; [exact Hthrough |].
  split; [exact Hlen |].
  intros i Hi.
  specialize (Hrel i Hi).
  destruct Hrel as [Hiff Hstable].
  split; [| exact Hstable].
  split; intro H.
  - apply Hiff in H.
    destruct H as [Hold [Hnz [Hdead | [Htwo [Hbelow | [Heq Hneg]]]]]].
    + repeat split; auto.
    + repeat split; auto; right; split; [exact Htwo | left; lia].
    + lia.
  - apply Hiff.
    destruct H as [Hold [Hnz [Hdead | [Htwo [Hbelow | [Heq Hneg]]]]]].
    + repeat split; auto.
    + repeat split; auto; right; split; [exact Htwo |].
      destruct (Z_lt_ge_dec (Znth (t - 1) (Znth i ins []) 0) c)
        as [Hlt | Hge].
      * left; exact Hlt.
      * assert (Znth (t - 1) (Znth i ins []) 0 = c) by lia.
        subst c; lia.
    + lia.
Qed.
Lemma collision_closure_cell_complete__collision_cell_exit :
  forall ins times counts t c i n,
    i >= n ->
    i <= n ->
    n = Zlength ins ->
    CollisionClosurePrefix ins times counts t c i ->
    CollisionClosurePrefix ins times counts t (c + 1) 0.
Proof.
  intros ins times counts t c i n Hge Hle Hn Hclosure.
  assert (Hi : i = n) by lia; subst i.
  unfold CollisionClosurePrefix in *; cbn zeta in *.
  destruct Hclosure as [Hthrough [Hlen Hrel]].
  split; [exact Hthrough |].
  split; [exact Hlen |].
  intros core Hcore.
  specialize (Hrel core Hcore).
  destruct Hrel as [Hiff Hstable].
  split; [| exact Hstable].
  split; intro H.
  - apply Hiff in H.
    destruct H as [Hold [Hnz [Hdead | [Htwo [Hbelow | [Heq Hdone]]]]]].
    + repeat split; auto.
    + repeat split; auto; right; split; [exact Htwo | left; lia].
    + repeat split; auto; right; split; [exact Htwo | left; lia].
  - apply Hiff.
    destruct H as [Hold [Hnz [Hdead | [Htwo [Hbelow | [Heq Hneg]]]]]].
    + repeat split; auto.
    + repeat split; auto; right; split; [exact Htwo |].
      destruct (Z_lt_ge_dec (Znth (t - 1) (Znth core ins []) 0) c)
        as [Hlt | Hgecell].
      * left; exact Hlt.
      * right; split; [lia | rewrite Hn; exact (proj2 Hcore)].
    + lia.
Qed.
Lemma lock_times_through_complete_spec__final_return :
  forall k ins locks m,
    (forall i, 0 <= i < Zlength ins -> Zlength (Znth i ins []) = m) ->
    LockTimesThrough ins locks m ->
    Spec k ins locks.
Proof.
  intros k ins locks m Hrows Hthrough.
  unfold LockTimesThrough in Hthrough.
  destruct Hthrough as [Hlength Hthrough].
  unfold Spec.
  split.
  - exact Hlength.
  - intros i Hi.
    specialize (Hthrough i Hi).
    destruct Hthrough as [[Hzero Hnone] | [[Hpositive Hbounded] [Htrigger Hearliest]]].
    + left.
      split.
      * exact Hzero.
      * intros [t Htrigger].
        apply (Hnone t).
        split.
        -- unfold LockTrigger in Htrigger.
           destruct Htrigger as [[Htone Htrow] _].
           exact Htone.
        -- unfold LockTrigger in Htrigger.
           destruct Htrigger as [[_ Htrow] _].
           rewrite (Hrows i Hi) in Htrow.
           exact Htrow.
        -- exact Htrigger.
    + right.
      exact (conj Hpositive (conj Htrigger Hearliest)).
Qed.
