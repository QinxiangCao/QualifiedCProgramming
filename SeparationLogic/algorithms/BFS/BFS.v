Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import SetsClass.SetsClass.
From MonadLib.MonadErr Require Import MonadErrBasic MonadErrHoare MonadErrHoarePartial MonadErrLoop.
From TraceLib.MonadErr Require Import TraceBasicErr GhostCodeErr TraceLoopErr CommonTacticsErr.
Require Import TraceLib.TraceLogic.
From GraphLib Require Import graph_basic reachable_basic bfs_dist.
Require Import Algorithms.MapLib.

Import SetsNotation.
Import MonadNotation.
Local Open Scope list.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope trace_scope.

Ltac intro_state :=
  apply Hoare_state_intro; intros.

Lemma Hoare_get_s {Σ A}:
  forall (P: Σ -> Prop) (Pa: Σ -> A -> Prop),
    Hoare P (get Pa) (fun a s => Pa s a /\ P s).
Proof. apply Hoare_get. Qed.

Lemma Hoare_get' {Σ A}:
  forall (P: Σ -> Prop) (f: Σ -> A),
    Hoare P (get' f) (fun a s => a = f s /\ P s).
Proof.
  intros.
  unfold get'.
  eapply Hoare_cons_post.
  2: apply Hoare_get.
  intros a s [Ha HP]; split; auto.
Qed.

Lemma Hoare_update' {Σ}:
  forall (P: Σ -> Prop) (f: Σ -> Σ),
    Hoare P (update' f) (fun _ s2 => exists s1, s2 = f s1 /\ P s1).
Proof.
  intros.
  unfold update'.
  eapply Hoare_cons_post.
  2: apply Hoare_update.
  intros [] s2 [s1 [Hs HP]].
  exists s1; auto.
Qed.

Lemma Hoare_conseq_post {Σ A}:
  forall (P: Σ -> Prop) (c: program Σ A) (Q1 Q2: A -> Σ -> Prop),
    (forall a s, Q2 a s -> Q1 a s) ->
    Hoare P c Q2 ->
    Hoare P c Q1.
Proof. intros; eapply Hoare_cons_post; eauto. Qed.

Section BFS.
Context
	{G V E: Type}
	`{graph: Graph G V E}
	{gv: GValid G}
	{stepvalid: @StepValid G V E graph gv}
	{finite_graph: @FiniteGraph G V E graph gv}
	(g: G)
	`{eq_dec: EqDec V eq}.

Notation step := (step g).
Notation reachable := (reachable g).

Record St: Type := mkSt {
	dist: V -> option nat;
	q: list V;
}.

Context
  (g_valid: gvalid g)
  (src: V)
  (src_valid: vvalid g src).

Local Notation path_of_len := (path_of_len g).
Local Notation bfs_dist := (bfs_dist g src).
Local Notation bfs_dist_le := (bfs_dist_le g src).
Local Notation pol_S := (pol_S g).
Local Notation bfs_dist_0_iff_src := (bfs_dist_0_iff_src g src).
Local Notation bfs_dist_le_0_iff_src := (bfs_dist_le_0_iff_src g src).
Local Notation path_of_len_min := (path_of_len_min g src).
Local Notation bfs_dist_unique := (bfs_dist_unique g src).
Local Notation bfs_dist_not_le_lt := (bfs_dist_not_le_lt g src).
Local Notation bfs_dist_S_pred := (bfs_dist_S_pred g src).
Local Notation bfs_dist_no_layer_succ := (bfs_dist_no_layer_succ g src).
Local Notation bfs_dist_no_layer_ge := (bfs_dist_no_layer_ge g src).
Local Notation reachable_iff_bfs_dist := (reachable_iff_bfs_dist g src).
Local Notation finite_bfs_dist_bound :=
  (finite_bfs_dist_bound g src g_valid src_valid).

Definition bfs_cond (s: St): Prop :=
	exists u, In u (q s).

Definition bfs_init : program St unit :=
	update' (fun _ => {|
		dist := (fun v => if eq_dec v src then Some 0 else None);
		q := src::nil
	|}).

Definition bfs_init_state : St := {|
  dist := (fun v => if eq_dec v src then Some 0 else None);
  q := src :: nil
|}.

Definition bfs_body : program St unit :=
    tail <- any (list V);;
	u <- get (fun s head => s.(q) = head :: tail);;
	d_u <- get (fun s d_u => s.(dist) u = Some d_u);;
	update' (fun s => {|
		dist := s.(dist);
		q := tail
	|});;
	tovisit <- get' (fun s v => step u v /\ s.(dist) v = None);;
	forset tovisit
		(fun v => update' (fun s => {|
			dist := v !-> (Some (S (d_u))); s.(dist);
			q := s.(q) ++ v::nil
		|})
		).

(** The executable BFS program used for the ordinary correctness theorem. *)
Definition BFS : program St unit :=
	bfs_init;;
	whileP bfs_cond bfs_body.

(** Ghost-instrumented BFS.  It has the same concrete behavior as [BFS], but
    records the states seen at loop boundaries. *)
Definition BFS_t : programTS St unit :=
	liftG bfs_init;;
	snapshot_loop bfs_cond bfs_body.

Lemma Gequiv_BFS:
	Gequiv BFS BFS_t.
Proof.
	unfold BFS, BFS_t.
	apply Gequiv_bind.
	- apply Gequiv_liftG.
	- intros [].
	  apply Gequiv_snapshot_loop.
Qed.

(** Default / placeholder state: every distance is [None], queue is empty. *)
Definition St_default : St := {| dist := fun _ => None; q := nil |}.

(** The BFS inductive hypothesis as stated in the textbook:
    At state [s], distance layer [d] has been fully processed:
    - (1) Every node at BFS distance ≤ d has its distance correctly set.
    - (2) Every node not reachable within distance d still has dist = None.
    - (3) The queue holds exactly the nodes at BFS distance d.
    The additional clause (3') fixes that this moment is at the *start* of a
    while-loop iteration (or right after initialisation), i.e. the queue is
    non-empty iff there exist nodes at distance d. *)
Definition BFS_IH (d: nat) (s: St) : Prop :=
  (* (1) correctly set for nodes at distance ≤ d *)
  (forall v d', bfs_dist v d' -> d' <= d -> s.(dist) v = Some d') /\
  (* (2) None for nodes not yet discovered:
         either unreachable from src, or reachable only at distance > d.
         Equivalently: ~bfs_dist_le v d, i.e. no path of length ≤ d exists. *)
  (forall v, ~bfs_dist_le v d -> s.(dist) v = None) /\
  (* (3) queue = exactly the nodes at BFS distance d *)
  (forall v, In v s.(q) <-> bfs_dist v d).

Definition BFSOneStepPre :=
  fun '(u, l2, dmap, d) s =>
    s.(q) = u :: l2 /\
    s.(dist) = dmap /\
    dmap u = Some d.

Definition BFSOneStepPost :=
  fun '(u, l2, dmap, d) s =>
    exists l3,
      s.(q) = l2 ++ l3 /\
      (forall v, In v l3 <-> step u v /\ dmap v = None) /\
      (forall v, In v l3 -> s.(dist) v = Some (S d)) /\
      (forall v, ~ In v l3 -> s.(dist) v = dmap v).

Definition BFSOneStep (s1 s2: St) : Prop :=
  forall lv, BFSOneStepPre lv s1 -> BFSOneStepPost lv s2.

Definition BFSLayerCond (d: nat) (s: St) : Prop :=
  exists v, In v s.(q) /\ bfs_dist v d.

Definition BFSLayerInv (d: nat) (s: St) : Prop :=
  (* All vertices from completed layers [<= d] already have their final
     shortest-path distances recorded in [dist]. *)
  (forall v d', bfs_dist v d' -> d' <= d -> s.(dist) v = Some d') /\
  (* Vertices outside the completed/current frontier [<= S d] are still
     undiscovered. *)
  (forall v, ~ bfs_dist_le v (S d) -> s.(dist) v = None) /\
  exists qd qnext,
    (* The queue is split into the unprocessed remainder of layer [d] and the
       already-discovered vertices of the next layer. *)
    s.(q) = qd ++ qnext /\
    (* The current-layer part of the queue contains only distance-[d]
       vertices. *)
    (forall v, In v qd -> bfs_dist v d) /\
    (* The next-layer queue is exactly the set of vertices whose distance has
       already been set to [S d]. *)
    (forall v, In v qnext <-> s.(dist) v = Some (S d)) /\
    (* Every vertex already placed in [qnext] is a next-layer neighbor
       of some current-layer vertex. *)
    (forall v, In v qnext ->
      exists u, bfs_dist u d /\ step u v /\ bfs_dist v (S d)) /\
    (* On the other hand, all popped current-layer vertice's next-layer neighbors are placed in [qnext]. *)
    (forall u v,
      bfs_dist u d -> ~ In u qd ->
      step u v -> bfs_dist v (S d) -> In v qnext) /\
    (* Other next-layer vertices have not been discovered yet. *)
    (forall v, bfs_dist v (S d) -> ~ In v qnext -> s.(dist) v = None).

Lemma BFSLayerInv_qnext_sound :
  forall d s (qnext: list V),
    (forall v, In v qnext ->
      exists u, bfs_dist u d /\ step u v /\ bfs_dist v (S d)) ->
    (forall v, In v qnext <-> s.(dist) v = Some (S d)) ->
    forall v, s.(dist) v = Some (S d) -> bfs_dist v (S d).
Proof.
  intros d s qnext Hqnext_step Hqnext v Hdist.
  apply Hqnext in Hdist.
  destruct (Hqnext_step v Hdist) as [u [_ [_ Hv_Sd]]].
  exact Hv_Sd.
Qed.

Lemma BFS_IH_0_init :
  BFS_IH 0 bfs_init_state.
Proof.
  unfold BFS_IH, bfs_init_state.
  split.
  - intros v d' Hd Hdle.
    assert (d' = 0) by lia.
    subst d'.
    apply bfs_dist_0_iff_src in Hd.
    subst v.
    simpl.
    destruct (eq_dec src src) as [_|Hcontra].
    + reflexivity.
    + exfalso; apply Hcontra; reflexivity.
  - split.
    + intros v Hnot.
      simpl.
      destruct (eq_dec v src) as [Heqv|Hneqv].
      * exfalso.
        apply Hnot.
        apply bfs_dist_le_0_iff_src.
        exact Heqv.
      * reflexivity.
    + intros v.
      split.
      * intros Hin.
        simpl in Hin.
        destruct Hin as [Heqv | Hfalse].
        -- subst v.
           apply bfs_dist_0_iff_src.
           reflexivity.
        -- contradiction.
      * intros Hv.
        apply bfs_dist_0_iff_src in Hv.
        subst v.
        simpl.
        auto.
Qed.

Lemma BFS_IH_to_BFSLayerInv :
  forall d s,
    BFS_IH d s ->
    BFSLayerInv d s.
Proof.
  intros d s [Hcorrect [Hnone Hqueue]].
  unfold BFSLayerInv.
  split.
  - exact Hcorrect.
  - split.
    + intros v Hnot_le_S.
      apply Hnone.
      intro Hle_d.
      apply Hnot_le_S.
      destruct Hle_d as [k [Hk Hkle]].
      exists k.
      split; [exact Hk | lia].
    + exists s.(q), nil.
      split.
      * rewrite app_nil_r. reflexivity.
      * split.
        -- intros v Hin.
           apply Hqueue.
           exact Hin.
        -- split.
           ++ intros v.
              split; intro H.
              ** contradiction.
              ** assert (~ bfs_dist_le v d).
                 {
                   intro Hle.
                   destruct Hle as [k [Hk Hkle]].
                   pose proof (Hcorrect v k Hk Hkle) as Hsome.
                   rewrite H in Hsome.
                   inversion Hsome.
                   lia.
                 }
                 pose proof (Hnone v H0) as Hnone_v.
                 rewrite H in Hnone_v.
                 discriminate.
           ++ split.
              ** intros v Hin.
                 contradiction.
              ** split.
                 --- intros u v Hu Hnotin _ _.
                     apply Hnotin.
                     apply Hqueue.
                     exact Hu.
                 --- intros v HvS _.
                     apply Hnone.
                     eapply bfs_dist_not_le_lt;
                       [exact HvS | lia].
Qed.

Lemma BFS_IH_nonempty_to_BFSLayerCond :
  forall d s,
    BFS_IH d s ->
    s.(q) <> nil ->
    BFSLayerCond d s.
Proof.
  intros d s [_ [_ Hqueue]] Hqnn.
  unfold BFSLayerCond.
  destruct s.(q) as [|u qs] eqn:Hq.
  - contradiction.
  - exists u.
    split.
    + simpl. auto.
    + apply Hqueue.
      simpl. auto.
Qed.

Lemma BFSLayerInv_done_BFS_IH :
  forall d s,
    BFSLayerInv d s ->
    ~ BFSLayerCond d s ->
    BFS_IH (S d) s.
Proof.
  intros d s Hinv Hnotcond.
  destruct Hinv as [Hcorrect [Hnone Hrest]].
  destruct Hrest as
    [qd [qnext
      [Hq [Hqd [Hqnext [Hqnext_step [Hcomplete Hnext_none]]]]]]].
  assert (Hqd_nil: qd = nil).
  {
    destruct qd as [|u qd']; [reflexivity |].
    exfalso.
    apply Hnotcond.
    unfold BFSLayerCond.
    exists u.
    split.
    - rewrite Hq. simpl. auto.
    - apply Hqd. simpl. auto.
  }
  unfold BFS_IH.
  split.
  - intros v d' Hdist Hdle.
    destruct (Nat.eq_dec d' (S d)) as [Heq | Hneq].
    + subst d'.
      pose proof Hdist as Hpred.
      apply bfs_dist_S_pred in Hpred.
      destruct Hpred as [u [Hu Hstep]].
      apply Hqnext.
      eapply Hcomplete; [exact Hu | | exact Hstep | exact Hdist].
      rewrite Hqd_nil.
      intros Hin.
      contradiction.
    + apply Hcorrect with (d' := d'); [exact Hdist | lia].
  - split.
    + intros v Hnot.
      apply Hnone.
      intro Hle.
      apply Hnot.
      destruct Hle as [k [Hk Hkle]].
      exists k.
      split; [exact Hk | lia].
    + intros v.
      split.
      * intros Hin.
        rewrite Hq, Hqd_nil in Hin.
        simpl in Hin.
        apply Hqnext in Hin.
        eapply BFSLayerInv_qnext_sound; eauto.
      * intros Hdist.
        rewrite Hq, Hqd_nil.
        simpl.
        pose proof Hdist as Hpred.
        apply bfs_dist_S_pred in Hpred.
        destruct Hpred as [u [Hu Hstep]].
        eapply Hcomplete; [exact Hu | | exact Hstep | exact Hdist].
        rewrite Hqd_nil.
        intros Hin.
        contradiction.
Qed.

Lemma bfs_body_BFSOneStep :
  forall lv, Hoare (BFSOneStepPre lv) bfs_body (fun _ => BFSOneStepPost lv).
Proof.
  intros [[[u l2] dmap] d].
  unfold BFSOneStepPre, BFSOneStepPost.
    intro_state.
    destruct H as [Hq [Hdist Hud]].
    assert (Hud0 : dist s0 u = Some d) by (rewrite Hdist; exact Hud).
    unfold bfs_body.
    apply Hoare_any_bind; intros tail.
    eapply Hoare_bind.
    {
      apply Hoare_get_s.
    }
    intros u0.
    apply Hoare_state_intro; intros st [Hqt Hst]; subst st.
    rewrite Hq in Hqt. simpl in Hqt.
    inversion Hqt; subst tail u0.
    eapply Hoare_bind.
    {
      apply Hoare_get_s.
    }
    intros d_u.
    apply Hoare_state_intro; intros st [Hdu Hst]; subst st.
    rewrite Hud0 in Hdu. inversion Hdu; subst d_u.
    eapply Hoare_bind.
    {
      apply Hoare_update'.
    }
    intros a.
    simpl.
    eapply Hoare_bind.
    {
      apply Hoare_get'.
    }
    intros U.
    apply Hoare_state_intro; intros st [HU Hpre].
    destruct Hpre as [sold [Hst Hsold]].
    subst sold st U.
    set (I :=
      fun done (s : St) =>
        exists l3,
          s.(q) = l2 ++ l3 /\
          (forall v, In v l3 <-> done v) /\
          (forall v, done v -> s.(dist) v = Some (S d)) /\
          (forall v, ~ done v -> s.(dist) v = dist s0 v)).
    eapply Hoare_conseq with
      (P2 := I (fun _ : V => False))
      (Q2 := fun _ s => I (fun v => step u v /\ dist s0 v = None) s).
    {
      intros s ->.
      exists nil.
      split.
      - simpl. rewrite app_nil_r. reflexivity.
      - split.
        + intros x. split; intro Hx; contradiction.
        + split.
          * intros x Hx. contradiction.
          * intros x _. reflexivity.
    }
    {
      intros _ s [l3 [Hqdone [Hl3 [Hset Hkeep]]]].
      exists l3.
      split.
      * exact Hqdone.
      * split.
        + intro x; split; intro Hx.
          { apply Hl3 in Hx.
            rewrite Hdist in Hx.
            exact Hx. }
          { destruct Hx as [Hstep Hdnone].
            apply Hl3.
            split; [assumption|].
            rewrite Hdist.
            assumption. }
        + split.
          { intros x Hx.
            apply Hset.
            apply Hl3.
            exact Hx. }
          { intros x Hnin.
            rewrite <- Hdist.
            apply Hkeep.
            intro Hx.
            apply Hnin.
            apply Hl3.
            exact Hx. }
    }
    change
      (Hoare (I (fun _ : V => False))
         (forset (fun v : V => step u v /\ dist s0 v = None)
            (fun v : V =>
               update'
                 (fun s : St =>
                    {| dist := v !-> Some (S d); dist s;
                       q := q s ++ v :: nil |})))
         (fun (_ : unit) (s : St) =>
            I (fun v => step u v /\ dist s0 v = None) s)).
    eapply (@Hoare_forset St V I
        (fun v => step u v /\ dist s0 v = None)
        (fun v =>
           update'
             (fun s : St =>
                {| dist := v !-> Some (S d); dist s;
                   q := q s ++ v :: nil |}))).
    {
      intros done1 done2 Heq s1 s2 Hs.
      subst s2.
      unfold I in *.
      firstorder.
    }
    {
      intros done a0 Hsub.
      intro_state.
      destruct H as [[l3 [Hqdone [Hl3 [Hset Hkeep]]]] [Ha0 Hnotin]].
      eapply Hoare_conseq_post.
      2: apply Hoare_update'.
      intros ? ? [sold [Hs HPold]].
      subst sold.
      exists (l3 ++ a0 :: nil).
      split.
      - rewrite Hs. simpl. rewrite Hqdone, app_assoc. reflexivity.
      - split.
        + intro x.
          rewrite in_app_iff.
          simpl.
          split; intro Hv.
          * destruct Hv as [Hv | [Hv | []]].
            { left. apply Hl3. exact Hv. }
            { subst x. right. sets_unfold. auto. }
          * destruct Hv as [Hv | Hv].
            { left. apply Hl3. exact Hv. }
            { right. simpl in Hv. destruct Hv; auto. }
        + split.
          * intros x Hv.
            sets_unfold in Hv.
            destruct Hv as [Hv | Hv].
            { simpl.
              rewrite Hs.
              simpl.
              unfold t_set.
              destruct (equiv_dec a0 x) as [Heq | Hneq].
              - destruct Heq.
                exfalso.
                apply Hnotin.
                exact Hv.
              - apply Hset. exact Hv. }
            { subst x. rewrite Hs. simpl. unfold t_set.
              destruct (equiv_dec a0 a0) as [_ | Hcontra].
              - reflexivity.
              - exfalso. apply Hcontra. reflexivity. }
          * intros x Hv.
            rewrite Hs.
            simpl.
            unfold t_set.
            destruct (equiv_dec a0 x) as [Heq | Hneq].
            { destruct Heq.
              exfalso.
              apply Hv.
              sets_unfold. auto. }
            { apply Hkeep.
              intro Hdone.
              apply Hv.
              sets_unfold. auto. }
    }
Qed.

Lemma bfs_body_BFSLayerInv :
  forall d,
    Hoare
      (fun s => BFSLayerInv d s /\ BFSLayerCond d s)
      bfs_body
      (fun _ => BFSLayerInv d).
Proof.
  intros d.
  intro_state.
  destruct H as [Hinv Hcond_layer].
  destruct Hinv as [Hcorrect [Hnone Hrest]].
  destruct Hrest as
    [qd [qnext
      [Hq [Hqd [Hqnext [Hqnext_step [Hcomplete Hnext_none]]]]]]].
  assert (Hqd_nonempty: qd <> nil).
  {
    destruct Hcond_layer as [v [Hin Hv_d]].
    rewrite Hq in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin_qd | Hin_qnext].
    - intro Hnil. rewrite Hnil in Hin_qd. contradiction.
    - apply Hqnext in Hin_qnext.
      pose proof (BFSLayerInv_qnext_sound
        d s0 qnext Hqnext_step Hqnext v Hin_qnext) as Hv_Sd.
      pose proof (bfs_dist_unique v d (S d) Hv_d Hv_Sd).
      lia.
  }
  destruct qd as [|u qd']; [contradiction |].
  set (tail := qd' ++ qnext).
  assert (Hu_d: bfs_dist u d).
  { apply Hqd. simpl. auto. }
  pose proof Hu_d as [Hpath_u _].
  assert (Hpre: BFSOneStepPre (u, tail, dist s0, d) s0).
  {
    unfold BFSOneStepPre.
    split.
    - rewrite Hq. simpl. reflexivity.
    - split; [reflexivity |].
      apply Hcorrect with (d' := d); [exact Hu_d | lia].
  }
  eapply Hoare_conseq with
    (P2 := BFSOneStepPre (u, tail, dist s0, d))
    (Q2 := fun _ => BFSOneStepPost (u, tail, dist s0, d)).
  - intros s Hs.
    subst s.
    exact Hpre.
  - intros _ s2 Hpost.
    unfold BFSOneStepPost in Hpost.
    destruct Hpost as [l3 [Hq2 [Hl3 [Hset Hkeep]]]].
    unfold BFSLayerInv.
    split.
    + intros v k Hv_k Hk_le.
      destruct (classic (In v l3)) as [Hin3 | Hnin3].
      * apply Hl3 in Hin3.
        destruct Hin3 as [_ Hold_none].
        pose proof (Hcorrect v k Hv_k Hk_le) as Hold_some.
        rewrite Hold_some in Hold_none.
        discriminate.
      * rewrite Hkeep by exact Hnin3.
        apply Hcorrect with (d' := k); assumption.
    + split.
      * intros v Hnot_le.
        rewrite Hkeep.
        -- apply Hnone. exact Hnot_le.
        -- intro Hin3.
           apply Hl3 in Hin3.
           destruct Hin3 as [Hstep Hold_none].
           apply Hnot_le.
           destruct (path_of_len_min v (S d)
             ltac:(eapply pol_S; [exact Hpath_u | eauto])) as [k [Hk Hkle]].
           exists k.
           split; [exact Hk | exact Hkle].
      * exists qd', (qnext ++ l3).
        split.
        -- rewrite Hq2.
           unfold tail.
           rewrite app_assoc.
           reflexivity.
        -- split.
           ++ intros v Hin.
              apply Hqd. simpl. auto.
           ++ split.
              ** intros v.
                 rewrite in_app_iff.
                 split; intro H.
                 --- destruct H as [Hin_qnext | Hin_l3].
                     { destruct (classic (In v l3)) as [Hin3 | Hnin3].
                       { apply Hset. exact Hin3. }
                       { rewrite Hkeep by exact Hnin3.
                         apply Hqnext. exact Hin_qnext. } }
                     { apply Hset. exact Hin_l3. }
                 --- destruct (classic (In v l3)) as [Hin3 | Hnin3].
                     { right. exact Hin3. }
                     { left.
                       apply Hqnext.
                       rewrite <- Hkeep by exact Hnin3.
                       exact H. }
              ** split.
                 --- intros v Hin.
                     apply in_app_or in Hin.
                     destruct Hin as [Hin_qnext | Hin_l3].
                     +++ apply Hqnext_step.
                         exact Hin_qnext.
                     +++ apply Hl3 in Hin_l3.
                         destruct Hin_l3 as [Hstep Hold_none].
                         exists u.
                         split; [exact Hu_d |].
                         split; [exact Hstep |].
                         destruct (path_of_len_min v (S d)
                           ltac:(eapply pol_S; [exact Hpath_u | eauto])) as [k [Hk Hkle]].
                         destruct (Nat.eq_dec k (S d)) as [Heq | Hneq].
                         { subst k. exact Hk. }
                         { assert (Hk_le_d: k <= d) by lia.
                           pose proof (Hcorrect v k Hk Hk_le_d) as Hold_some.
                           rewrite Hold_some in Hold_none.
                           discriminate. }
                 --- split.
                     +++ intros u0 v Hu0 Hnotin_qd' Hstep0 Hv_Sd.
                         destruct (classic (u0 = u)) as [Hu0_eq | Hu0_neq].
                         { subst u0.
                           destruct (classic (In v qnext)) as [Hin_qnext | Hnotin_qnext].
                           { apply in_or_app.
                             left. exact Hin_qnext. }
                           { apply in_or_app.
                             right.
                             apply Hl3.
                             split; [exact Hstep0 |].
                             apply Hnext_none; assumption. } }
                         { apply in_or_app.
                           left.
                           eapply Hcomplete; [exact Hu0 | | exact Hstep0 | exact Hv_Sd].
                           intro Hin_qd.
                           simpl in Hin_qd.
                           destruct Hin_qd as [Hu0_eq | Hin_qd'].
                           { apply Hu0_neq. symmetry. exact Hu0_eq. }
                           { apply Hnotin_qd'. exact Hin_qd'. } }
                     +++ intros v Hv_Sd Hnotin_new.
                         rewrite Hkeep.
                         { apply Hnext_none.
                           - exact Hv_Sd.
                           - intro Hin_qnext.
                             apply Hnotin_new.
                             apply in_or_app.
                             left. exact Hin_qnext. }
                         { intro Hin_l3.
                           apply Hnotin_new.
                           apply in_or_app.
                           right. exact Hin_l3. }
  - apply bfs_body_BFSOneStep.
Qed.

Lemma BFSLayerCond_implies_bfs_cond :
  forall d s,
    BFSLayerCond d s ->
    bfs_cond s.
Proof.
  intros d s [v [Hin _]].
  unfold bfs_cond.
  exists v.
  exact Hin.
Qed.

#[local] Instance bfs_body_safe : SnapshotBodySafe bfs_body.
Proof.
  constructor.
  unfold bfs_body.
  apply Hoare_any_bind; intros tail.
  eapply Hoare_bind; [apply Hoare_get|]; intros u.
  eapply Hoare_bind; [apply Hoare_get|]; intros d_u.
  eapply Hoare_bind; [apply Hoare_update'|]; intros [].
  eapply Hoare_bind; [apply Hoare_get'|]; intros tovisit.
  eapply Hoare_cons_pre.
  2:{
    eapply Hoare_cons_post.
    2:{
      eapply (@Hoare_forset St V (fun _ _ => True)
        tovisit
        (fun v : V =>
          update'
            (fun s : St =>
              {| dist := v !-> Some (S d_u); dist s;
                 q := q s ++ v :: nil |}))).
      - unfold Proper, respectful; tauto.
      - intros done a Hsub.
        eapply Hoare_cons_post.
        2: apply Hoare_update'.
        intros [] s H; exact I.
    }
    intros [] s _; exact I.
  }
  intros s _; exact I.
Qed.

Lemma liftG_bfs_init_state :
  Hoare
    (fun '(_, tr) => tr = @nil St)
    (liftG bfs_init)
    (fun _ '(s, tr) => s = bfs_init_state /\ tr = @nil St).
Proof.
  eapply Hoare_liftG'.
  intros tr.
  unfold Hoare, bfs_init, update', update; sets_unfold.
  split.
  - intros s1 a s2 Hpre Heval.
    split.
    + unfold bfs_init_state. exact Heval.
    + exact Hpre.
  - intros s1 Hpre Herr; tauto.
Qed.

Lemma BFS_IH_empty_queue_succ :
  forall d s,
    BFS_IH d s ->
    s.(q) = nil ->
    BFS_IH (S d) s.
Proof.
  intros d s HIH Hqnil.
  destruct HIH as [Hcorrect [Hnone Hq]].
  assert (Hno_d: forall v, ~ bfs_dist v d).
  {
    intros v Hv.
    apply Hq in Hv.
    rewrite Hqnil in Hv.
    exact Hv.
  }
  assert (Hno_Sd: forall v, ~ bfs_dist v (S d)).
  {
    apply bfs_dist_no_layer_succ.
    exact Hno_d.
  }
  unfold BFS_IH.
  split.
  - intros v d' Hdist Hdle.
    destruct (Nat.eq_dec d' (S d)) as [Heq | Hneq].
    + subst d'. exfalso. exact (Hno_Sd v Hdist).
    + apply Hcorrect with (d' := d'); [exact Hdist | lia].
  - split.
    + intros v Hnot.
      apply Hnone.
      intro Hle.
      apply Hnot.
      destruct Hle as [k [Hk Hkle]].
      exists k.
      split; [exact Hk | lia].
    + intros v.
      split.
      * intros Hin.
        rewrite Hqnil in Hin.
        contradiction.
      * intros Hdist.
        exfalso.
        exact (Hno_Sd v Hdist).
Qed.

Lemma BFS_trace_step_from_inner :
  forall d tr,
    TraceImplies
      (haveS (sLift (BFSLayerInv d)))
      (haveS (sLift (fun s => BFSLayerInv d s /\ ~ BFSLayerCond d s)))
      tr ->
    TraceImplies
      (haveS (sLift (BFS_IH d)))
      (haveS (sLift (BFS_IH (S d))))
      tr.
Proof.
  intros d tr Hinner.
  unfold TraceImplies, impliesS, trace_implies, last_satisfyS in *.
  intro Hhave_IH.
  destruct (haveS_exists_nth tr (BFS_IH d) St_default Hhave_IH)
    as [i [Hi HIH_i]].
  destruct (q (nth i tr St_default)) as [|u qs] eqn:Hq_i.
  - apply nth_haveS with (i := i) (d := St_default); [exact Hi |].
    apply BFS_IH_empty_queue_succ with (d := d); assumption.
  - assert (Hcond_i: BFSLayerCond d (nth i tr St_default)).
    {
      apply BFS_IH_nonempty_to_BFSLayerCond; [exact HIH_i |].
      rewrite Hq_i.
      discriminate.
    }
    assert (Hinv_i: BFSLayerInv d (nth i tr St_default)).
    { apply BFS_IH_to_BFSLayerInv. exact HIH_i. }
    assert (Hhave_inner:
      last_satisfyS
        (haveS (sLift (BFSLayerInv d))) tr).
    {
      apply nth_haveS with (i := i) (d := St_default); [exact Hi |].
      exact Hinv_i.
    }
    specialize (Hinner Hhave_inner).
    destruct (haveS_exists_nth tr
      (fun s => BFSLayerInv d s /\ ~ BFSLayerCond d s)
      St_default Hinner) as [j [Hj [Hinv_j Hdone_j]]].
    apply nth_haveS with (i := j) (d := St_default); [exact Hj |].
    eapply BFSLayerInv_done_BFS_IH; eauto.
Qed.

Lemma snapshot_loop_BFS_IH_step :
  forall d,
    Hoare
      (fun '(_, tr) => tr = nil)
      (snapshot_loop bfs_cond bfs_body)
      (fun _ '(_, tr) =>
        TraceImplies
          (haveS (sLift (BFS_IH d)))
          (haveS (sLift (BFS_IH (S d))))
          tr).
Proof.
  intros d.
  eapply Hoare_conseq_post.
  2:{
    eapply snapshot_loop_inner_have with
      (inner_cond := BFSLayerCond d)
      (inner_inv := BFSLayerInv d).
    - exact bfs_body_safe.
    - apply BFSLayerCond_implies_bfs_cond.
    - apply bfs_body_BFSLayerInv.
  }
  intros _ (s, tr) Hinner.
  apply BFS_trace_step_from_inner.
  exact Hinner.
Qed.

Theorem BFS_t_IH0_have :
  Hoare
    (fun '(_, tr) => tr = nil)
    BFS_t
    (fun _ '(_, tr) => TraceHave (BFS_IH 0) tr).
Proof.
  unfold BFS_t.
  eapply Hoare_bind with
    (Q := fun _ '(s, tr) => s = bfs_init_state /\ tr = nil).
  - apply liftG_bfs_init_state.
  - intros _.
    change (Hoare
      (fun '(s, tr) => s = bfs_init_state /\ tr = nil)
      (snapshot_loop bfs_cond bfs_body)
      (fun _ '(_, tr) => TraceHave (BFS_IH 0) tr)).
    eapply snapshot_loop_initial_have.
    + exact bfs_body_safe.
    + intros s Hs.
      subst s.
      apply BFS_IH_0_init.
Qed.

Theorem BFS_t_IH_step_implies :
  Hoare
    (fun '(_, tr) => tr = nil)
    BFS_t
    (fun _ '(_, tr) =>
      forall d,
        TraceImplies
          (haveS (sLift (BFS_IH d)))
          (haveS (sLift (BFS_IH (S d))))
          tr).
Proof.
  unfold BFS_t.
  eapply Hoare_bind with
    (Q := fun _ '(s, tr) => s = bfs_init_state /\ tr = nil).
  - apply liftG_bfs_init_state.
  - intros _.
    unfold Hoare.
    split.
    + intros [] [s1 tr1] [s2 tr2] [_ Hnil] Hrun d.
      destruct (snapshot_loop_BFS_IH_step d) as [Hnrm _].
      change (TraceImplies
        (haveS (sLift (BFS_IH d)))
        (haveS (sLift (BFS_IH (S d))))
        tr2).
      pose proof (Hnrm tt (s1, tr1) (s2, tr2) Hnil Hrun) as Hstep.
      exact Hstep.
    + intros [s1 tr1] [_ Hnil] Herr.
      destruct (snapshot_loop_BFS_IH_step 0) as [_ Herr_step].
      eapply (Herr_step (s1, tr1)); [exact Hnil | exact Herr].
Qed.

(** Trace-method formalization of the textbook induction.
    The base case is [have (IH 0)].  The inductive step is a trace-level
    implication [have (IH d) s-> have (IH (S d))], obtained from the
    inner-condition/inner-invariant rule [snapshot_loop_BFS_IH_step]. *)
Theorem BFS_trace_IH_have :
  Hoare
    (fun '(_, tr) => tr = nil)
    BFS_t
    (fun _ '(_, tr) => forall d, TraceHave (BFS_IH d) tr).
Proof.
  eapply Hoare_conseq_post.
  2:{
    apply Hoare_conj.
    - apply BFS_t_IH0_have.
    - apply BFS_t_IH_step_implies.
  }
  intros _ (s, tr) [Hbase Hstep] d.
  induction d as [|d IH].
  - exact Hbase.
  - specialize (Hstep d).
    unfold TraceHave in *.
    unfold TraceImplies, impliesS, trace_implies, last_satisfyS in Hstep.
    exact (Hstep IH).
Qed.

Lemma BFS_IH_empty_correct :
  forall d s,
    BFS_IH d s ->
    s.(q) = nil ->
    forall v k, bfs_dist v k <-> s.(dist) v = Some k.
Proof.
  intros d s HIH Hqnil.
  destruct HIH as [Hcorrect [Hnone Hqueue]].
  assert (Hno_layer_d: forall v, ~ bfs_dist v d).
  {
    intros v Hv.
    apply Hqueue in Hv.
    rewrite Hqnil in Hv.
    exact Hv.
  }
  intros v k.
  split.
  - intro Hdist.
    destruct (le_gt_dec k d) as [Hle | Hgt].
    + apply Hcorrect; assumption.
    + exfalso.
      pose proof (bfs_dist_no_layer_ge d k ltac:(lia) Hno_layer_d v) as Hno.
      exact (Hno Hdist).
  - intro Hsome.
    destruct (classic (bfs_dist_le v d)) as [[k0 [Hk0 Hk0le]] | Hnot].
    + pose proof (Hcorrect v k0 Hk0 Hk0le) as Hsome0.
      rewrite Hsome in Hsome0.
      inversion Hsome0.
      subst k0.
      exact Hk0.
    + pose proof (Hnone v Hnot) as Hnone_v.
      rewrite Hsome in Hnone_v.
	      discriminate.
Qed.

(** If layer [d] is empty, then any state satisfying [BFS_IH d] is already a
    loop-exit state. *)
Lemma BFS_IH_no_layer_no_cond :
  forall d,
    (forall v, ~ bfs_dist v d) ->
    forall s, BFS_IH d s -> ~ bfs_cond s.
Proof.
  intros d Hno_layer s [_ [_ Hqueue]] Hcond.
  destruct Hcond as [v Hin].
  apply (Hno_layer v).
  apply Hqueue.
  exact Hin.
Qed.

Lemma BFS_IH_no_layer_queue_nil :
  forall d,
    (forall v, ~ bfs_dist v d) ->
    forall s, BFS_IH d s -> s.(q) = nil.
Proof.
  intros d Hno_layer s HIH.
  destruct s.(q) as [|v qs] eqn:Hq; [reflexivity |].
  exfalso.
  eapply BFS_IH_no_layer_no_cond; eauto.
  unfold bfs_cond.
  exists v.
  rewrite Hq.
  simpl.
  auto.
Qed.

Lemma BFS_t_have_final_BFS_IH :
  forall d,
    (forall v, ~ bfs_dist v d) ->
    Hoare
      (fun '(_, tr) => tr = nil)
      BFS_t
      (fun _ '(s, tr) => TraceHave (BFS_IH d) tr -> BFS_IH d s).
Proof.
  intros d Hno_layer.
  unfold BFS_t.
  eapply Hoare_bind with
    (Q := fun _ '(s, tr) => s = bfs_init_state /\ tr = nil).
  - apply liftG_bfs_init_state.
  - intros _.
    eapply Hoare_conseq with
      (P2 := fun '(_, tr) => tr = nil)
      (Q2 := fun _ '(s, tr) => TraceHave (BFS_IH d) tr -> BFS_IH d s).
    + intros [s tr] [_ Hnil].
      exact Hnil.
    + intros _ (s, tr) Hfinal.
      exact Hfinal.
    + eapply (@snapshot_loop_have_final St St_default
        bfs_cond (BFS_IH d) bfs_body bfs_body_safe).
      intros s HIH.
      eapply BFS_IH_no_layer_no_cond; eauto.
Qed.

(** Final loop-exit invariant, now following the standard finite-graph
    argument.  Let [dmax] bound every reachable shortest-path distance.  The
    layer [S dmax] is empty, and [snapshot_loop_have_final] turns the trace
    occurrence of [BFS_IH (S dmax)] into a fact about the final state. *)
Theorem BFS_t_exit_IH :
  Hoare
    (fun '(_, tr) => tr = nil)
    BFS_t
    (fun _ '(s, tr) => exists d, BFS_IH d s /\ s.(q) = nil).
Proof.
  destruct finite_bfs_dist_bound as [dmax Hbound].
  set (dmax_plus_one := S dmax).
  assert (Hno_layer: forall v, ~ bfs_dist v dmax_plus_one).
  {
    intros v Hdist.
    unfold dmax_plus_one in Hdist.
    pose proof (Hbound v (S dmax) Hdist).
    lia.
  }
  eapply Hoare_conseq_post.
  2:{
    apply Hoare_conj.
    - apply BFS_t_IH0_have.
    - apply Hoare_conj.
      + apply BFS_t_IH_step_implies.
      + apply BFS_t_have_final_BFS_IH.
        exact Hno_layer.
  }
  intros _ (s, tr) [Hbase [Hstep Hfinal]].
  exists dmax_plus_one.
  assert (Hall_have: forall d, TraceHave (BFS_IH d) tr).
  {
    intro d.
    induction d as [|d IH].
    - exact Hbase.
    - specialize (Hstep d).
      unfold TraceHave in *.
      unfold TraceImplies, impliesS, trace_implies, last_satisfyS in Hstep.
      exact (Hstep IH).
  }
  assert (Hhave_target: TraceHave (BFS_IH dmax_plus_one) tr).
  { apply Hall_have. }
  assert (HIH_final: BFS_IH dmax_plus_one s).
  {
    apply Hfinal.
    exact Hhave_target.
  }
  split.
  - exact HIH_final.
  - eapply BFS_IH_no_layer_queue_nil; eauto.
Qed.

Theorem BFS_t_correct :
  Hoare
    (fun '(_, tr) => tr = nil)
    BFS_t
    (fun _ '(s, tr) => forall v d, bfs_dist v d <-> s.(dist) v = Some d).
Proof.
  eapply Hoare_conseq_post.
  2: apply BFS_t_exit_IH.
  intros _ (s, tr) [d [HIH Hqnil]].
  apply BFS_IH_empty_correct with (d := d); assumption.
Qed.

(** Ordinary BFS correctness is obtained by erasing the trace from [BFS_t]. *)
Theorem BFS_correct:
  Hoare
    (fun _ => True)
    BFS
    (fun _ s => forall v d, bfs_dist v d <-> s.(dist) v = Some d).
Proof.
  eapply Hoare_fromG with
    (c' := BFS_t)
    (P' := fun '(_, tr) => tr = nil).
  - apply Gequiv_BFS.
  - intros s _.
    exists (@nil St).
    reflexivity.
  - apply BFS_t_correct.
Qed.

End BFS.
