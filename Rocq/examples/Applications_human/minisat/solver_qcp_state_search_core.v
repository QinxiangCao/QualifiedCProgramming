From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Export solver_qcp_lib_core.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** * S7 -- variable order heap and random seed. *)

(** ----- small generic helpers ----- *)

Lemma Z_In_dec : forall (x : Z) (l : list Z), {In x l} + {~ In x l}.
Proof.
  intros x l. induction l as [|a l IH].
  - right. intros [].
  - destruct (Z.eq_dec a x) as [->|Hne].
    + left. left. reflexivity.
    + destruct IH as [Hin|Hout].
      * left. right. exact Hin.
      * right. intros [He|He]; [apply Hne; exact He | apply Hout; exact He].
Qed.

Lemma In_Znth_ex : forall (A : Type) (l : list A) (d : A) x,
  In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l d x. induction l as [|a l IH]; intros Hin.
  - destruct Hin.
  - pose proof (Zlength_nonneg l).
    destruct Hin as [->|Hin].
    + exists 0. rewrite Zlength_cons. split; [lia|].
      rewrite Znth0_cons. reflexivity.
    + destruct (IH Hin) as [i [Hi Hval]].
      exists (i + 1). rewrite Zlength_cons. split; [lia|].
      rewrite Znth_cons by lia.
      replace (i + 1 - 1) with i by lia. exact Hval.
Qed.

(** At a propagation fixpoint every assigned variable, including one still
    present in the decision heap, already occurs below [qhead]. *)
Definition assigned_below_qhead
    (n : Z) (assigns trail : list Z) (qhead : Z) : Prop :=
  forall v, 0 <= v < n -> Znth v assigns 0 <> 0 ->
    exists i, 0 <= i < qhead /\ lit_var_c (Znth i trail 0) = v.

Lemma mtrail_wf_assigned_below_qhead : forall n t qhead,
  mtrail_wf n t ->
  qhead = Zlength (mt_trail t) ->
  assigned_below_qhead n (mt_assigns t) (mt_trail t) qhead.
Proof.
  intros n t qhead Hwf Hq v Hv Hassigned.
  pose proof
    (proj1 (mtw_assigned_iff Hwf v Hv) Hassigned) as Hin.
  apply in_map_iff in Hin. destruct Hin as [l [Hvar Hin]].
  destruct (In_Znth_ex Z (mt_trail t) 0 l Hin) as [i [Hi Hlit]].
  exists i. split; [rewrite Hq; exact Hi|].
  rewrite Hlit. exact Hvar.
Qed.

(** ----- [heap_wf] toolbox ----- *)

Lemma heap_wf_orderpos_length : forall n h,
  heap_wf n h -> Zlength (mh_orderpos h) = n.
Proof. intros n h H. apply H. Qed.

Lemma heap_wf_nodup : forall n h, heap_wf n h -> NoDup (mh_heap h).
Proof. intros n h H. apply H. Qed.

Lemma heap_wf_range : forall n h,
  heap_wf n h -> Forall (fun v => 0 <= v < n) (mh_heap h).
Proof. intros n h H. apply H. Qed.

Lemma heap_wf_inverse : forall n h i,
  heap_wf n h -> 0 <= i < Zlength (mh_heap h) ->
  Znth (Znth i (mh_heap h) (-1)) (mh_orderpos h) (-1) = i.
Proof. intros n h i H. apply H. Qed.

Lemma heap_wf_lookup : forall n h v,
  heap_wf n h -> 0 <= v < n ->
  Znth v (mh_orderpos h) (-1) <> -1 ->
  0 <= Znth v (mh_orderpos h) (-1) < Zlength (mh_heap h) /\
  Znth (Znth v (mh_orderpos h) (-1)) (mh_heap h) (-1) = v.
Proof.
  intros n h v Hwf Hv Hne.
  destruct Hwf as (_ & _ & _ & Hop & _).
  destruct (Hop v Hv) as [Hm1|Hgood]; [contradiction|exact Hgood].
Qed.

Lemma heap_wf_in_iff : forall n h v,
  heap_wf n h -> 0 <= v < n ->
  (In v (mh_heap h) <-> Znth v (mh_orderpos h) (-1) <> -1).
Proof.
  intros n h v Hwf Hv. split.
  - intros Hin.
    destruct (In_Znth_ex Z (mh_heap h) (-1) v Hin) as [i [Hi Hval]].
    pose proof (heap_wf_inverse n h i Hwf Hi) as Hinv.
    rewrite Hval in Hinv. rewrite Hinv. lia.
  - intros Hne.
    destruct (heap_wf_lookup n h v Hwf Hv Hne) as [Hr Heq].
    rewrite <- Heq. apply Znth_In. exact Hr.
Qed.

Lemma heap_wf_incl_missing_mono : forall n h h' v,
  heap_wf n h -> heap_wf n h' -> incl (mh_heap h) (mh_heap h') ->
  0 <= v < n -> Znth v (mh_orderpos h') (-1) = -1 ->
  Znth v (mh_orderpos h) (-1) = -1.
Proof.
  intros n h h' v Hwf Hwf' Hincl Hv Hmissing.
  destruct (Z.eq_dec (Znth v (mh_orderpos h) (-1)) (-1)) as [H|H];
    [exact H|].
  exfalso.
  apply (heap_wf_in_iff n h v Hwf Hv) in H.
  apply Hincl in H.
  apply (heap_wf_in_iff n h' v Hwf' Hv) in H.
  contradiction.
Qed.

Lemma heap_wf_missing_length : forall n h v,
  0 <= n ->
  heap_wf n h ->
  0 <= v < n ->
  Znth v (mh_orderpos h) (-1) = -1 ->
  Zlength (mh_heap h) < n.
Proof.
  intros n h v Hn Hwf Hv Hmissing.
  assert (Hnotin : ~ In v (mh_heap h)).
  { intro Hin.
    apply (heap_wf_in_iff n h v Hwf Hv) in Hin.
    contradiction. }
  assert (Hnodup : NoDup (v :: mh_heap h)).
  { constructor; [exact Hnotin|apply (heap_wf_nodup n h Hwf)]. }
  assert (Hbounded : forall x, In x (v :: mh_heap h) -> 0 <= x < n).
  { intros x [->|Hin]; [exact Hv|].
    pose proof (heap_wf_range n h Hwf) as Hrange.
    rewrite Forall_forall in Hrange.
    exact (Hrange x Hin). }
  pose proof (NoDup_Z_bounded_length (v :: mh_heap h) n Hn Hnodup Hbounded)
    as Hlen.
  rewrite <- Zlength_correct in Hlen.
  rewrite Zlength_cons in Hlen. lia.
Qed.

Lemma heap_wf_not_in : forall n h v,
  heap_wf n h -> 0 <= v < n ->
  ~ In v (mh_heap h) -> Znth v (mh_orderpos h) (-1) = -1.
Proof.
  intros n h v Hwf Hv Hout.
  destruct (Z.eq_dec (Znth v (mh_orderpos h) (-1)) (-1)) as [E|E];
    [exact E|].
  exfalso. apply Hout. apply (heap_wf_in_iff n h v Hwf Hv). exact E.
Qed.

Lemma heap_wf_intro : forall n h,
  Zlength (mh_orderpos h) = n ->
  NoDup (mh_heap h) ->
  Forall (fun v => 0 <= v < n) (mh_heap h) ->
  (forall v, 0 <= v < n -> ~ In v (mh_heap h) ->
     Znth v (mh_orderpos h) (-1) = -1) ->
  (forall i, 0 <= i < Zlength (mh_heap h) ->
     Znth (Znth i (mh_heap h) (-1)) (mh_orderpos h) (-1) = i) ->
  heap_wf n h.
Proof.
  intros n h H1 H2 H3 H4 H5.
  unfold heap_wf. split; [exact H1|]. split; [exact H2|].
  split; [exact H3|]. split; [|exact H5].
  intros v Hv.
  destruct (Z_In_dec v (mh_heap h)) as [Hin|Hout].
  - right.
    destruct (In_Znth_ex Z (mh_heap h) (-1) v Hin) as [i [Hi Hval]].
    pose proof (H5 i Hi) as Hinv. rewrite Hval in Hinv.
    rewrite Hinv. split; [exact Hi|exact Hval].
  - left. apply H4; assumption.
Qed.

(** ----- the ORD-INV consequence: empty heap ==> total assignment ----- *)

Lemma heap_covers_total : forall n h assigns trail qhead,
  heap_wf n h ->
  mh_heap h = [] ->
  heap_covers n h assigns trail qhead ->
  forall v, 0 <= v < n -> Znth v assigns 0 <> 0.
Proof.
  intros n h assigns trail qhead Hwf Hempty Hcov v Hv.
  assert (Hm1 : Znth v (mh_orderpos h) (-1) = -1).
  { apply (heap_wf_not_in n h v Hwf Hv). rewrite Hempty. intros []. }
  destruct (Hcov v Hv Hm1) as [Ha _]. exact Ha.
Qed.


(** ----- [heap_wf] preservation ----- *)

(** sift up / sift down: the heap array is permuted, orderpos is rebuilt as
    its inverse.  Nothing about the ORDER is asserted -- the comparisons are
    IEEE doubles. *)

Lemma heap_wf_pop : forall n h h' v,
  heap_wf n h ->
  0 <= v < n ->
  Permutation (mh_heap h) (v :: mh_heap h') ->
  Zlength (mh_orderpos h') = n ->
  Znth v (mh_orderpos h') (-1) = -1 ->
  (forall u, 0 <= u < n -> u <> v -> ~ In u (mh_heap h') ->
     Znth u (mh_orderpos h') (-1) = -1) ->
  (forall i, 0 <= i < Zlength (mh_heap h') ->
     Znth (Znth i (mh_heap h') (-1)) (mh_orderpos h') (-1) = i) ->
  heap_wf n h'.
Proof.
  intros n h h' v Hwf Hv Hperm Hlen Hpv Hout Hinv.
  assert (Hnd : NoDup (v :: mh_heap h')).
  { apply (Permutation_NoDup Hperm). apply (heap_wf_nodup n h Hwf). }
  apply heap_wf_intro; try assumption.
  - inversion Hnd; assumption.
  - pose proof (heap_wf_range n h Hwf) as Hr.
    rewrite Forall_forall in Hr |- *.
    intros x Hx. apply Hr.
    apply (Permutation_in _ (Permutation_sym Hperm)). right. exact Hx.
  - intros u Hu Hnotin.
    destruct (Z.eq_dec u v) as [->|Hne]; [exact Hpv|].
    apply Hout; assumption.
Qed.

Lemma heap_wf_insert : forall n h v,
  heap_wf n h ->
  0 <= v < n ->
  Znth v (mh_orderpos h) (-1) = -1 ->
  heap_wf n {| mh_heap := mh_heap h ++ [v];
               mh_orderpos :=
                 replace_Znth v (Zlength (mh_heap h)) (mh_orderpos h) |}.
Proof.
  intros n h v Hwf Hv Hm1.
  pose proof (heap_wf_orderpos_length n h Hwf) as Hlen.
  pose proof (heap_wf_range n h Hwf) as Hrange.
  pose proof (Zlength_nonneg (mh_heap h)) as Hhn.
  assert (Hvop : 0 <= v < Zlength (mh_orderpos h)) by lia.
  assert (Hnotin : ~ In v (mh_heap h)).
  { intros Hin.
    apply (heap_wf_in_iff n h v Hwf Hv) in Hin. contradiction. }
  apply heap_wf_intro; simpl.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - assert (HA : Add v (mh_heap h) (mh_heap h ++ [v])).
    { pose proof (Add_app v (mh_heap h) (@nil Z)) as HAdd.
      rewrite app_nil_r in HAdd. exact HAdd. }
    apply (NoDup_Add HA). split.
    + apply (heap_wf_nodup n h Hwf).
    + exact Hnotin.
  - apply Forall_app. split; [exact Hrange|].
    constructor; [exact Hv|constructor].
  - intros u Hu Hnu.
    assert (Hne : u <> v).
    { intros ->. apply Hnu. apply in_or_app. right. left. reflexivity. }
    assert (Hnh : ~ In u (mh_heap h)).
    { intros Hin. apply Hnu. apply in_or_app. left. exact Hin. }
    rewrite (Znth_replace_Znth_Diff (-1) (mh_orderpos h) v u); try lia.
    apply (heap_wf_not_in n h u Hwf Hu Hnh).
  - intros i Hi.
    rewrite Zlength_app in Hi. rewrite Zlength_cons, Zlength_nil in Hi.
    destruct (Z.eq_dec i (Zlength (mh_heap h))) as [->|Hne].
    + rewrite app_Znth2 by lia.
      replace (Zlength (mh_heap h) - Zlength (mh_heap h)) with 0 by lia.
      rewrite Znth0_cons.
      rewrite Znth_replace_Znth_Same by lia. reflexivity.
    + assert (Hi' : 0 <= i < Zlength (mh_heap h)) by lia.
      rewrite app_Znth1 by lia.
      set (u := Znth i (mh_heap h) (-1)).
      assert (Hin : In u (mh_heap h)) by (apply Znth_In; exact Hi').
      assert (Hune : u <> v) by (intros ->; contradiction).
      assert (Hur : 0 <= u < n).
      { rewrite Forall_forall in Hrange. apply Hrange. exact Hin. }
      rewrite (Znth_replace_Znth_Diff (-1) (mh_orderpos h) v u); try lia.
      apply (heap_wf_inverse n h i Hwf Hi').
Qed.

(** ----- [heap_covers] preservation ----- *)

Lemma heap_covers_weaken_heap : forall n h h' assigns trail qhead,
  heap_covers n h assigns trail qhead ->
  (forall v, 0 <= v < n -> Znth v (mh_orderpos h') (-1) = -1 ->
     Znth v (mh_orderpos h) (-1) = -1) ->
  heap_covers n h' assigns trail qhead.
Proof.
  intros n h h' assigns trail qhead Hcov Hmono v Hv Hm1.
  apply Hcov; [exact Hv|]. apply Hmono; assumption.
Qed.

Lemma heap_covers_qhead_mono : forall n h assigns trail qhead qhead',
  heap_covers n h assigns trail qhead ->
  qhead <= qhead' ->
  heap_covers n h assigns trail qhead'.
Proof.
  intros n h assigns trail qhead qhead' Hcov Hle v Hv Hm1.
  destruct (Hcov v Hv Hm1) as [Ha [i [Hi Hval]]].
  split; [exact Ha|]. exists i. split; [lia|exact Hval].
Qed.

Lemma heap_covers_enqueue : forall n h assigns assigns' trail trail' qhead qhead',
  heap_covers n h assigns trail qhead ->
  qhead <= qhead' ->
  (forall v, 0 <= v < n -> Znth v assigns 0 <> 0 -> Znth v assigns' 0 <> 0) ->
  (forall i, 0 <= i < qhead -> Znth i trail' 0 = Znth i trail 0) ->
  heap_covers n h assigns' trail' qhead'.
Proof.
  intros n h assigns assigns' trail trail' qhead qhead'
         Hcov Hq Hassign Htrail v Hv Hm1.
  destruct (Hcov v Hv Hm1) as [Ha [i [Hi Hval]]].
  split; [apply Hassign; assumption|].
  exists i. split; [lia|]. rewrite Htrail by lia. exact Hval.
Qed.

(** Pure carriers for the in-place heap loops.  The saved value [x] lives in
    a C local while one concrete array position is a logical hole.  Removing
    that one cell and adding [x] back preserves the original multiset even
    though the cell currently at the hole can be a duplicate. *)
Definition list_without_Znth (i : Z) (l : list Z) : list Z :=
  sublist 0 i l ++ sublist (i + 1) (Zlength l) l.

Definition order_heap_wf (n : Z) (heap orderpos : list Z) : Prop :=
  heap_wf n {| mh_heap := heap; mh_orderpos := orderpos |}.

(** The [NoDup] and [Forall]-range conjuncts on [origin] are what make the
    loop-exit write ([heap[hole] := x; orderpos[x] := hole]) re-establish
    [order_heap_wf]; see [order_heap_one_hole_close].  Both are carried on
    [origin] rather than on [heap] because [origin] is the ghost anchor:
    [Permutation] transports them to [x :: list_without_Znth hole heap], and
    the cell sitting at [hole] is junk that neither must constrain.

    Without [NoDup origin] the lifted [x] may duplicate a live entry --
    [order_heap_one_hole 4 [3;3] 3 0 [0;3] [-1;-1;-1;1]] holds but closes to
    the heap [[3;3]], refuting [NoDup].  Without [Forall (0 <= _ < n) origin]
    a NEGATIVE cell survives the forward inverse below, because [Znth] at a
    negative index returns the HEAD of the list, not the default: with
    [heap = [7;-3]] and [orderpos = [1;-1]] one has
    [Znth (Znth 1 heap (-1)) orderpos (-1) = Znth (-3) orderpos (-1) = 1].

    Note that [Znth x orderpos (-1)] is deliberately NOT constrained: at the
    [order_select] sift entry it is the STALE pre-truncation index, one past
    the end of the truncated heap, so any
    [heap_wf]-shaped constraint on it would be unsatisfiable there.  The code
    overwrites it at loop exit, which is exactly what [_close] models. *)
Definition order_heap_one_hole
    (n : Z) (origin : list Z) (x hole : Z)
    (heap orderpos : list Z) : Prop :=
  Zlength orderpos = n /\
  Zlength heap = Zlength origin /\
  0 <= hole < Zlength heap /\
  0 <= x < n /\
  NoDup origin /\
  Forall (fun v => 0 <= v < n) origin /\
  Permutation origin (x :: list_without_Znth hole heap) /\
  (forall i, 0 <= i < Zlength heap -> i <> hole ->
     Znth (Znth i heap (-1)) orderpos (-1) = i) /\
  (forall v, 0 <= v < n -> ~ In v origin ->
     Znth v orderpos (-1) = -1).

Definition order_update_pre
    (n v : Z) (heap orderpos : list Z) : Prop :=
  order_heap_wf n heap orderpos /\
  0 <= v < n /\ Znth v orderpos (-1) <> -1.

Definition order_update_loop_inv
    (n v : Z) (origin : list Z) (x i : Z)
    (heap orderpos : list Z) : Prop :=
  0 <= v < n /\ In v origin /\
  order_heap_one_hole n origin x i heap orderpos.

Definition order_update_post
    (n v : Z) (before_heap before_pos after_heap after_pos : list Z) : Prop :=
  order_update_pre n v before_heap before_pos /\
  order_heap_wf n after_heap after_pos /\
  Permutation before_heap after_heap /\
  (forall u, 0 <= u < n ->
     (Znth u before_pos (-1) = -1 <-> Znth u after_pos (-1) = -1)).

Definition order_unassigned_pre
    (n v : Z) (heap orderpos : list Z) : Prop :=
  order_heap_wf n heap orderpos /\
  0 <= v < n /\ 2 * n <= INT_MAX.

Definition order_unassigned_post
    (n v : Z) (before_heap before_pos : list Z)
    (after_heap after_pos : list Z) : Prop :=
  order_heap_wf n after_heap after_pos /\
  ((Znth v before_pos (-1) = -1 /\
    Permutation after_heap (before_heap ++ [v])) \/
   (Znth v before_pos (-1) <> -1 /\
    after_heap = before_heap /\ after_pos = before_pos)).

Definition order_select_pre
    (n : Z) (heap orderpos assigns trail : list Z) (qhead : Z) : Prop :=
  2 * n <= INT_MAX /\
  order_heap_wf n heap orderpos /\
  heap_covers n {| mh_heap := heap; mh_orderpos := orderpos |}
    assigns trail qhead /\
  assigned_below_qhead n assigns trail qhead /\
  Zlength assigns = n /\
  Forall (fun x => x = -1 \/ x = 0 \/ x = 1) assigns.

Definition order_select_loop_inv
    (n : Z) (origin heap orderpos assigns trail : list Z) (qhead : Z) : Prop :=
  order_select_pre n heap orderpos assigns trail qhead /\
  incl heap origin.

Definition order_select_sift_inv
    (n popped x hole : Z)
    (origin before heap orderpos assigns trail : list Z) (qhead : Z) : Prop :=
  2 * n <= INT_MAX /\
  0 <= popped < n /\
  incl before origin /\
  Zlength assigns = n /\
  Forall (fun a => a = -1 \/ a = 0 \/ a = 1) assigns /\
  assigned_below_qhead n assigns trail qhead /\
  heap_covers_except n {| mh_heap := heap; mh_orderpos := orderpos |}
    assigns trail qhead popped /\
  order_heap_one_hole n (list_without_Znth 0 before)
    x hole heap orderpos.

Definition order_select_post
    (n ret : Z) (before_heap after_heap after_pos assigns trail : list Z)
    (qhead : Z) : Prop :=
  order_heap_wf n after_heap after_pos /\
  incl after_heap before_heap /\
  ((ret = -1 /\ after_heap = [] /\
    forall v, 0 <= v < n -> Znth v assigns 0 <> 0) \/
   (0 <= ret < n /\ Znth ret assigns 0 = 0 /\
    heap_covers_except n
      {| mh_heap := after_heap; mh_orderpos := after_pos |}
      assigns trail qhead ret)).

Lemma Zlength_list_without_Znth : forall i l,
  0 <= i < Zlength l ->
  Zlength (list_without_Znth i l) = Zlength l - 1.
Proof.
  intros i l Hi. unfold list_without_Znth.
  rewrite Zlength_app.
  rewrite (Zlength_sublist 0 i l) by lia.
  rewrite (Zlength_sublist (i + 1) (Zlength l) l) by lia.
  lia.
Qed.

Lemma list_without_Znth_perm : forall (d : Z) i l,
  0 <= i < Zlength l ->
  Permutation l (Znth i l d :: list_without_Znth i l).
Proof.
  intros d i l Hi. unfold list_without_Znth.
  pose proof (Znth_split d l i Hi) as E.
  remember (Znth i l d) as a eqn:Ha.
  remember (sublist 0 i l) as A eqn:HA.
  remember (sublist (i + 1) (Zlength l) l) as B eqn:HB.
  rewrite E. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma list_without_Znth_replace_perm : forall (d v : Z) i l,
  0 <= i < Zlength l ->
  Permutation (replace_Znth i v l) (v :: list_without_Znth i l).
Proof.
  intros d v i l Hi.
  rewrite (replace_Znth_split i v l Hi).
  unfold list_without_Znth.
  apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma In_list_without_Znth : forall (d : Z) i j l,
  0 <= i < Zlength l -> 0 <= j < Zlength l -> i <> j ->
  In (Znth i l d) (list_without_Znth j l).
Proof.
  intros d i j l Hi Hj Hne. unfold list_without_Znth.
  apply in_or_app.
  destruct (Z.lt_ge_cases i j) as [Hlt|Hge].
  - left. rewrite <- (Znth_sublist0 d i j l) by lia.
    apply Znth_In. rewrite Zlength_sublist0 by lia. lia.
  - right.
    assert (E : Znth i l d
                = Znth (i - (j + 1)) (sublist (j + 1) (Zlength l) l) d).
    { rewrite (Znth_sublist d (j + 1) (i - (j + 1)) (Zlength l) l) by lia.
      f_equal. lia. }
    rewrite E. apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma In_replace_Znth_same : forall (x i : Z) (l : list Z),
  0 <= i < Zlength l -> In x (replace_Znth i x l).
Proof.
  intros x i l Hi.
  pose proof (Znth_In Z (replace_Znth i x l) (-1) i) as HI.
  rewrite (Znth_replace_Znth_Same (-1) l i x) in HI by lia.
  apply HI. rewrite Zlength_replace_Znth. lia.
Qed.

(** ----- [order_heap_one_hole] toolbox ----- *)

Lemma order_heap_one_hole_cell_in : forall n origin x hole heap orderpos i,
  order_heap_one_hole n origin x hole heap orderpos ->
  0 <= i < Zlength heap -> i <> hole ->
  In (Znth i heap (-1)) origin.
Proof.
  intros n origin x hole heap orderpos i
         (Hoplen & Hlen & Hhole & Hx & Hnd & Hrng & Hperm & Hinv & Hout) Hi Hne.
  apply (Permutation_in _ (Permutation_sym Hperm)).
  right. apply In_list_without_Znth; [lia|lia|lia].
Qed.

Lemma order_heap_one_hole_cell_range : forall n origin x hole heap orderpos i,
  order_heap_one_hole n origin x hole heap orderpos ->
  0 <= i < Zlength heap -> i <> hole ->
  0 <= Znth i heap (-1) < n.
Proof.
  intros n origin x hole heap orderpos i H Hi Hne.
  pose proof (order_heap_one_hole_cell_in n origin x hole heap orderpos i H Hi
                Hne) as Hin.
  destruct H as (Hoplen & Hlen & Hhole & Hx & Hnd & Hrng & Hperm & Hinv & Hout).
  rewrite Forall_forall in Hrng. exact (Hrng _ Hin).
Qed.

Lemma order_heap_one_hole_perm : forall n origin x hole heap orderpos,
  order_heap_one_hole n origin x hole heap orderpos ->
  Permutation origin (replace_Znth hole x heap).
Proof.
  intros n origin x hole heap orderpos
         (Hoplen & Hlen & Hhole & Hx & Hnd & Hrng & Hperm & Hinv & Hout).
  apply (Permutation_trans Hperm). apply Permutation_sym.
  apply (list_without_Znth_replace_perm (-1)). lia.
Qed.

Lemma order_heap_one_hole_close : forall n origin x hole heap orderpos,
  order_heap_one_hole n origin x hole heap orderpos ->
  order_heap_wf n (replace_Znth hole x heap) (replace_Znth x hole orderpos).
Proof.
  intros n origin x hole heap orderpos H.
  pose proof H as Hfull.
  destruct H as (Hoplen & Hlen & Hhole & Hx & Hnd & Hrng & Hperm & Hinv & Hout).
  assert (Hph : Permutation (replace_Znth hole x heap)
                            (x :: list_without_Znth hole heap))
    by (apply (list_without_Znth_replace_perm (-1)); lia).
  assert (Hpo : Permutation origin (replace_Znth hole x heap))
    by (apply (Permutation_trans Hperm (Permutation_sym Hph))).
  assert (Hnd2 : NoDup (x :: list_without_Znth hole heap))
    by (apply (Permutation_NoDup Hperm); exact Hnd).
  assert (HxNI : ~ In x (list_without_Znth hole heap))
    by (inversion Hnd2; assumption).
  unfold order_heap_wf. apply heap_wf_intro; cbn [mh_heap mh_orderpos].
  - rewrite Zlength_replace_Znth. exact Hoplen.
  - apply (Permutation_NoDup Hpo). exact Hnd.
  - rewrite Forall_forall. intros u Hu.
    apply (Permutation_in _ (Permutation_sym Hpo)) in Hu.
    rewrite Forall_forall in Hrng. exact (Hrng u Hu).
  - intros v Hv Hnotin.
    assert (Hvx : v <> x).
    { intros Hev. apply Hnotin. rewrite Hev.
      apply In_replace_Znth_same. lia. }
    rewrite (Znth_replace_Znth_Diff (-1) orderpos x v hole) by lia.
    apply Hout; [lia|]. intros Hin. apply Hnotin.
    apply (Permutation_in _ Hpo). exact Hin.
  - intros i Hi. rewrite Zlength_replace_Znth in Hi.
    destruct (Z.eq_dec i hole) as [->|Hne].
    + rewrite (Znth_replace_Znth_Same (-1) heap hole x) by lia.
      rewrite (Znth_replace_Znth_Same (-1) orderpos x hole) by lia.
      reflexivity.
    + rewrite (Znth_replace_Znth_Diff (-1) heap hole i x) by lia.
      assert (Hne2 : Znth i heap (-1) <> x).
      { intros E. apply HxNI. rewrite <- E.
        apply In_list_without_Znth; lia. }
      assert (Hr : 0 <= Znth i heap (-1) < n)
        by (apply (order_heap_one_hole_cell_range n origin x hole heap orderpos
                     i Hfull); [lia|lia]).
      rewrite (Znth_replace_Znth_Diff (-1) orderpos x (Znth i heap (-1)) hole)
        by lia.
      apply Hinv; [lia|lia].
Qed.

Lemma order_heap_one_hole_close_missing :
  forall n origin x hole heap orderpos u,
  order_heap_one_hole n origin x hole heap orderpos ->
  0 <= u < n ->
  (Znth u (replace_Znth x hole orderpos) (-1) = -1 <-> ~ In u origin).
Proof.
  intros n origin x hole heap orderpos u H Hu.
  pose proof (order_heap_one_hole_close n origin x hole heap orderpos H) as Hwf.
  pose proof (order_heap_one_hole_perm n origin x hole heap orderpos H) as Hpo.
  unfold order_heap_wf in Hwf.
  pose proof (heap_wf_in_iff n
    {| mh_heap := replace_Znth hole x heap;
       mh_orderpos := replace_Znth x hole orderpos |} u Hwf Hu) as Hiff.
  cbn [mh_heap mh_orderpos] in Hiff.
  split.
  - intros Hm1 Hin. apply (Permutation_in _ Hpo) in Hin.
    apply Hiff in Hin. contradiction.
  - intros Hnin.
    destruct (Z.eq_dec (Znth u (replace_Znth x hole orderpos) (-1)) (-1))
      as [E|E]; [exact E|].
    exfalso. apply Hnin. apply (Permutation_in _ (Permutation_sym Hpo)).
    apply Hiff. exact E.
Qed.

(** PRESERVATION.  One sift step: the hole moves to [child] and that child's
    value is shifted up into the old hole. *)
Lemma order_heap_one_hole_step :
  forall n origin x hole child heap orderpos,
  order_heap_one_hole n origin x hole heap orderpos ->
  0 <= child < Zlength heap -> child <> hole ->
  order_heap_one_hole n origin x child
    (replace_Znth hole (Znth child heap (-1)) heap)
    (replace_Znth (Znth child heap (-1)) hole orderpos).
Proof.
  intros n origin x hole child heap orderpos H Hchild Hne.
  pose proof H as Hfull.
  destruct H as (Hoplen & Hlen & Hhole & Hx & Hnd & Hrng & Hperm & Hinv & Hout).
  assert (Hw : 0 <= Znth child heap (-1) < n)
    by (apply (order_heap_one_hole_cell_range n origin x hole heap orderpos
                 child Hfull); [lia|lia]).
  assert (Hcw : Znth child (replace_Znth hole (Znth child heap (-1)) heap) (-1)
                = Znth child heap (-1))
    by (apply (Znth_replace_Znth_Diff (-1) heap hole child); lia).
  assert (Hlh : Zlength (replace_Znth hole (Znth child heap (-1)) heap)
                = Zlength heap) by apply Zlength_replace_Znth.
  assert (Hp1 : Permutation (replace_Znth hole (Znth child heap (-1)) heap)
                  (Znth child heap (-1) :: list_without_Znth hole heap))
    by (apply (list_without_Znth_replace_perm (-1)); lia).
  assert (Hp2 : Permutation (replace_Znth hole (Znth child heap (-1)) heap)
                  (Znth child heap (-1)
                   :: list_without_Znth child
                        (replace_Znth hole (Znth child heap (-1)) heap))).
  { rewrite <- Hcw at 2.
    apply (list_without_Znth_perm (-1)). lia. }
  assert (Hp3 : Permutation (list_without_Znth hole heap)
                  (list_without_Znth child
                     (replace_Znth hole (Znth child heap (-1)) heap))).
  { apply (Permutation_cons_inv (a := Znth child heap (-1))).
    apply (Permutation_trans (Permutation_sym Hp1) Hp2). }
  unfold order_heap_one_hole.
  split; [rewrite Zlength_replace_Znth; exact Hoplen|].
  split; [rewrite Zlength_replace_Znth; exact Hlen|].
  split; [rewrite Hlh; lia|].
  split; [lia|].
  split; [exact Hnd|].
  split; [exact Hrng|].
  split; [apply (Permutation_trans Hperm); apply perm_skip; exact Hp3|].
  split.
  - intros i Hi Hic. rewrite Hlh in Hi.
    destruct (Z.eq_dec i hole) as [->|Hih].
    + rewrite (Znth_replace_Znth_Same (-1) heap hole (Znth child heap (-1)))
        by lia.
      apply (Znth_replace_Znth_Same (-1) orderpos (Znth child heap (-1)) hole).
      lia.
    + rewrite (Znth_replace_Znth_Diff (-1) heap hole i (Znth child heap (-1)))
        by lia.
      assert (Hu : 0 <= Znth i heap (-1) < n)
        by (apply (order_heap_one_hole_cell_range n origin x hole heap orderpos
                     i Hfull); [lia|lia]).
      assert (Hune : Znth i heap (-1) <> Znth child heap (-1)).
      { intros E. pose proof (Hinv i ltac:(lia) Hih) as E1.
        pose proof (Hinv child ltac:(lia) Hne) as E2.
        rewrite E in E1. lia. }
      rewrite (Znth_replace_Znth_Diff (-1) orderpos (Znth child heap (-1))
                 (Znth i heap (-1)) hole) by lia.
      apply Hinv; [lia|lia].
  - intros v Hv Hvout.
    assert (Hvw : v <> Znth child heap (-1)).
    { intros E. apply Hvout. rewrite E.
      apply (order_heap_one_hole_cell_in n origin x hole heap orderpos child
               Hfull); [lia|lia]. }
    rewrite (Znth_replace_Znth_Diff (-1) orderpos (Znth child heap (-1)) v hole)
      by lia.
    apply Hout; [lia|exact Hvout].
Qed.

(** ESTABLISHMENT 1 -- [order_update]: [i := orderpos[v]; x := heap[i]]
    turns the incoming [order_heap_wf] into the loop invariant (and, as a
    by-product, [x] is [v] itself). *)
Lemma order_update_loop_inv_init : forall n v i x heap orderpos,
  order_update_pre n v heap orderpos ->
  i = Znth v orderpos (-1) ->
  x = Znth i heap (-1) ->
  0 <= i < Zlength heap /\ x = v /\
  order_update_loop_inv n v heap x i heap orderpos.
Proof.
  intros n v i x heap orderpos (Hwf & Hv & Hne) Hi Hx.
  unfold order_heap_wf in Hwf.
  pose proof (heap_wf_lookup n _ v Hwf Hv) as Hlk.
  cbn [mh_heap mh_orderpos] in Hlk.
  destruct (Hlk Hne) as [Hirange Hival].
  rewrite <- Hi in Hirange, Hival.
  pose proof (heap_wf_orderpos_length n _ Hwf) as Hoplen.
  pose proof (heap_wf_nodup n _ Hwf) as Hnd.
  pose proof (heap_wf_range n _ Hwf) as Hrng.
  pose proof (fun j => heap_wf_inverse n
                 {| mh_heap := heap; mh_orderpos := orderpos |} j Hwf) as Hinv.
  cbn [mh_heap mh_orderpos] in Hoplen, Hnd, Hrng, Hinv.
  assert (Hxv : x = v) by (rewrite Hx; exact Hival).
  assert (Hin : In v heap) by (rewrite <- Hival; apply Znth_In; lia).
  split; [lia|]. split; [exact Hxv|].
  unfold order_update_loop_inv, order_heap_one_hole.
  split; [lia|]. split; [exact Hin|].
  split; [exact Hoplen|].
  split; [reflexivity|].
  split; [lia|].
  split; [lia|].
  split; [exact Hnd|].
  split; [exact Hrng|].
  split; [rewrite Hx; apply (list_without_Znth_perm (-1)); lia|].
  split.
  - intros j Hj _. apply Hinv. lia.
  - intros u Hu Hout.
    apply (heap_wf_not_in n {| mh_heap := heap; mh_orderpos := orderpos |} u
             Hwf Hu Hout).
Qed.

(** ESTABLISHMENT 2 -- [order_select]: after [veci_resize(order, size)] and
    [orderpos[next] := -1], the truncated array with the saved last element
    [x] and a hole at index 0 is a one-hole heap over the ghost anchor
    [list_without_Znth 0 before]. *)
Lemma order_heap_one_hole_init_select :
  forall n size before orderpos next x,
  order_heap_wf n before orderpos ->
  Zlength before = size + 1 ->
  0 < size ->
  next = Znth 0 before (-1) ->
  x = Znth size before (-1) ->
  order_heap_one_hole n (list_without_Znth 0 before) x 0
    (sublist 0 size before)
    (replace_Znth next (-1) orderpos).
Proof.
  intros n size before orderpos next x Hwf Hlen0 Hsz Hnext Hx.
  unfold order_heap_wf in Hwf.
  pose proof (heap_wf_orderpos_length n _ Hwf) as Hoplen.
  pose proof (heap_wf_nodup n _ Hwf) as Hnd.
  pose proof (heap_wf_range n _ Hwf) as Hrng.
  pose proof (fun j => heap_wf_inverse n
                 {| mh_heap := before; mh_orderpos := orderpos |} j Hwf) as Hinv.
  cbn [mh_heap mh_orderpos] in Hoplen, Hnd, Hrng, Hinv.
  rewrite Forall_forall in Hrng.
  assert (Hhl : Zlength (sublist 0 size before) = size)
    by (apply Zlength_sublist0; lia).
  assert (Hnr : 0 <= next < n)
    by (rewrite Hnext; apply Hrng; apply Znth_In; lia).
  assert (Hxr : 0 <= x < n)
    by (rewrite Hx; apply Hrng; apply Znth_In; lia).
  assert (Hn0 : Znth 0 (sublist 0 size before) (-1) = next)
    by (rewrite Hnext; apply Znth_sublist0; lia).
  assert (Hpb : Permutation before (next :: list_without_Znth 0 before)).
  { rewrite Hnext. apply (list_without_Znth_perm (-1)). lia. }
  assert (Hph : Permutation (sublist 0 size before)
                  (next :: list_without_Znth 0 (sublist 0 size before))).
  { rewrite <- Hn0. apply (list_without_Znth_perm (-1)). lia. }
  assert (Hsplit : before = sublist 0 size before ++ [x]).
  { pose proof (Znth_split (-1) before size ltac:(lia)) as Hs.
    rewrite Hlen0 in Hs.
    rewrite (Zsublist_nil before (size + 1) (size + 1) ltac:(lia)) in Hs.
    rewrite <- Hx in Hs. exact Hs. }
  assert (Hbx : Permutation before (x :: sublist 0 size before)).
  { rewrite Hsplit at 1. apply Permutation_sym. apply Permutation_cons_append. }
  assert (Hndb : NoDup (next :: list_without_Znth 0 before))
    by (apply (Permutation_NoDup Hpb); exact Hnd).
  unfold order_heap_one_hole.
  split; [rewrite Zlength_replace_Znth; exact Hoplen|].
  split; [rewrite Hhl, Zlength_list_without_Znth by lia; lia|].
  split; [lia|].
  split; [lia|].
  split; [inversion Hndb; assumption|].
  split.
  { rewrite Forall_forall. intros u Hu. apply Hrng.
    apply (Permutation_in _ (Permutation_sym Hpb)). right. exact Hu. }
  split.
  { apply (Permutation_cons_inv (a := next)).
    apply (Permutation_trans (Permutation_sym Hpb)).
    apply (Permutation_trans Hbx).
    apply (Permutation_trans (perm_skip x Hph)).
    apply perm_swap. }
  split.
  - intros i Hi Hi0. rewrite Hhl in Hi.
    rewrite (Znth_sublist0 (-1) i size before) by lia.
    assert (Hur : 0 <= Znth i before (-1) < n)
      by (apply Hrng; apply Znth_In; lia).
    assert (Hune : Znth i before (-1) <> next).
    { intros E. pose proof (Hinv i ltac:(lia)) as E1.
      pose proof (Hinv 0 ltac:(lia)) as E2. rewrite <- Hnext in E2.
      rewrite E in E1. lia. }
    rewrite (Znth_replace_Znth_Diff (-1) orderpos next (Znth i before (-1)) (-1))
      by lia.
    apply Hinv. lia.
  - intros v Hv Hvout.
    destruct (Z.eq_dec v next) as [->|Hvn].
    + apply (Znth_replace_Znth_Same (-1) orderpos next (-1)). lia.
    + rewrite (Znth_replace_Znth_Diff (-1) orderpos next v (-1)) by lia.
      apply (heap_wf_not_in n {| mh_heap := before; mh_orderpos := orderpos |}
               v Hwf Hv).
      cbn [mh_heap]. intros Hin.
      destruct (Permutation_in _ Hpb Hin) as [He|He];
        [apply Hvn; symmetry; exact He|apply Hvout; exact He].
Qed.


Lemma heap_covers_except_weaken : forall n h assigns trail qhead v0,
  heap_covers n h assigns trail qhead ->
  heap_covers_except n h assigns trail qhead v0.
Proof.
  intros n h assigns trail qhead v0 Hcov v Hv _ Hm1.
  exact (Hcov v Hv Hm1).
Qed.

Lemma heap_covers_except_intro : forall n h h' assigns trail qhead v0,
  heap_covers n h assigns trail qhead ->
  (forall u, 0 <= u < n -> Znth u (mh_orderpos h') (-1) = -1 ->
     u = v0 \/ Znth u (mh_orderpos h) (-1) = -1) ->
  heap_covers_except n h' assigns trail qhead v0.
Proof.
  intros n h h' assigns trail qhead v0 Hcov Hmono v Hv Hne Hm1.
  destruct (Hmono v Hv Hm1) as [->|Hold].
  - exact (False_ind _ (Hne eq_refl)).
  - exact (Hcov v Hv Hold).
Qed.

Lemma heap_covers_except_assume :
  forall n h assigns assigns' trail trail' qhead qhead' v0,
  heap_covers_except n h assigns trail qhead v0 ->
  qhead <= qhead' ->
  (forall v, 0 <= v < n -> Znth v assigns 0 <> 0 ->
     Znth v assigns' 0 <> 0) ->
  (forall i, 0 <= i < qhead -> Znth i trail' 0 = Znth i trail 0) ->
  heap_covers_except n h assigns' trail' qhead' v0.
Proof.
  intros n h assigns assigns' trail trail' qhead qhead' v0
         Hcov Hq Hassign Htrail v Hv Hne Hm1.
  destruct (Hcov v Hv Hne Hm1) as [Ha [i [Hi Hval]]].
  split; [apply Hassign; assumption|].
  exists i. split; [lia|]. rewrite Htrail by lia. exact Hval.
Qed.

Lemma heap_covers_except_qhead :
  forall n h assigns trail qhead qhead' v0,
  heap_covers_except n h assigns trail qhead v0 ->
  qhead <= qhead' ->
  Znth v0 assigns 0 <> 0 ->
  (exists i, 0 <= i < qhead' /\ lit_var_c (Znth i trail 0) = v0) ->
  heap_covers n h assigns trail qhead'.
Proof.
  intros n h assigns trail qhead qhead' v0 Hcov Hq Ha0 Hi0 v Hv Hm1.
  destruct (Z.eq_dec v v0) as [->|Hne].
  - split; assumption.
  - destruct (Hcov v Hv Hne Hm1) as [Ha [i [Hi Hval]]].
    split; [exact Ha|]. exists i. split; [lia|exact Hval].
Qed.

(** The [order_unassigned] loop of [solver_canceluntil] runs
    downwards over [[bound, qhead)]; this is its invariant. *)
Definition cancel_reinserted (h : mheap) (trail : list Z) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi ->
    Znth (lit_var_c (Znth i trail 0)) (mh_orderpos h) (-1) <> -1.

Lemma cancel_reinserted_init : forall h trail hi,
  cancel_reinserted h trail hi hi.
Proof. intros h trail hi i Hi. lia. Qed.


(** Heap coverage survives [solver_canceluntil] even though the
    reinsertion loop is asymmetric: variables in [[qhead, qtail)] are
    unassigned WITHOUT being reinserted, but the new [qhead] is [bound], so
    they are no longer required to be covered.  Trail variable-distinctness
    is what rules out a variable being both below [bound] and cancelled. *)
Lemma heap_covers_cancel : forall n h h' assigns assigns' trail bound qhead qtail,
  heap_covers n h assigns trail qhead ->
  0 <= bound <= qhead ->
  qhead <= qtail ->
  (forall i j, 0 <= i < qtail -> 0 <= j < qtail ->
     lit_var_c (Znth i trail 0) = lit_var_c (Znth j trail 0) -> i = j) ->
  (forall v, 0 <= v < n -> Znth v assigns' 0 = 0 -> Znth v assigns 0 <> 0 ->
     exists i, bound <= i < qtail /\ lit_var_c (Znth i trail 0) = v) ->
  cancel_reinserted h' trail bound qhead ->
  (forall v, 0 <= v < n -> Znth v (mh_orderpos h') (-1) = -1 ->
     Znth v (mh_orderpos h) (-1) = -1) ->
  heap_covers n h' assigns' trail bound.
Proof.
  intros n h h' assigns assigns' trail bound qhead qtail
         Hcov Hb Hq Hdist Hcancel Hre Hmono v Hv Hm1.
  destruct (Hcov v Hv (Hmono v Hv Hm1)) as [Ha [i [Hi Hval]]].
  assert (Hlow : i < bound).
  { destruct (Z_lt_le_dec i bound) as [Hlt|Hge]; [exact Hlt|].
    exfalso. apply (Hre i); [lia|]. rewrite Hval. exact Hm1. }
  assert (Ha' : Znth v assigns' 0 <> 0).
  { intros Hz.
    destruct (Hcancel v Hv Hz Ha) as [j [Hj Hjval]].
    assert (i = j).
    { apply Hdist; [lia|lia|]. rewrite Hval, Hjval. reflexivity. }
    lia. }
  split; [exact Ha'|]. exists i. split; [lia|exact Hval].
Qed.


Lemma activity_state_undef : forall c learnt size,
  activity_state c learnt size |-- activity_undef c learnt size.
Proof.
  intros c learnt size. unfold activity_state, activity_undef. destruct learnt.
  - Intros a. apply store_float_undef_store_float.
  - msat_entailer_with lia.
Qed.

