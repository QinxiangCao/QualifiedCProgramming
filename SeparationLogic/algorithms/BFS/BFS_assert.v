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
Require Import Algorithms.BFS.BFS.

Import SetsNotation.
Import MonadNotation.
Local Open Scope list.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.
Local Open Scope trace_scope.

Ltac intro_state :=
  apply Hoare_state_intro; intros.

Section BFSAssert.
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

Context
  (g_valid: gvalid g)
  (src: V)
  (src_valid: vvalid g src).

Local Notation bfs_dist := (bfs_dist g src).
Local Notation St' := (@St V).

Definition bfs_queue_visited (s: St') : Prop :=
  forall v, In v s.(q) -> exists d, s.(dist) v = Some d.

Definition bfs_queue_reachable (s: St') : Prop :=
  forall v, In v s.(q) -> reachable src v.

Definition bfs_assert_inv (s: St') : Prop :=
  bfs_queue_reachable s /\ bfs_queue_visited s.

Definition bfs_body_assert : program St' unit :=
  assertS bfs_assert_inv;; bfs_body g.

(** The refinement-friendly variant: before each loop body execution, it
    asserts the local queue facts needed by downstream refinements: every
    queued vertex is reachable and already has a distance entry. *)
Definition BFS_assert : program St' unit :=
  bfs_init src;;
  whileP bfs_cond bfs_body_assert.

Definition BFS_assert_t : programTS St' unit :=
  liftG (bfs_init src);;
  snapshot_loop bfs_cond bfs_body_assert.

Lemma Gequiv_BFS_assert:
  Gequiv BFS_assert BFS_assert_t.
Proof.
  unfold BFS_assert, BFS_assert_t.
  apply Gequiv_bind.
  - apply Gequiv_liftG.
  - intros [].
    apply Gequiv_snapshot_loop.
Qed.

Lemma bfs_body_assert_BFSOneStep_nrm :
  forall (lv: V * list V * (V -> option nat) * nat),
    Hoare_nrm (BFSOneStepPre lv) bfs_body_assert
      (fun _ => BFSOneStepPost g lv).
Proof.
  intros lv.
  unfold bfs_body_assert.
  apply Hoare_nrm_assertS_bind_intro.
  apply Hoare_implies_nrm.
  apply bfs_body_BFSOneStep.
Qed.

Lemma bfs_body_assert_BFSLayerInv_nrm :
  forall d,
    Hoare_nrm
      (fun s => BFSLayerInv g src d s /\ BFSLayerCond g src d s)
      bfs_body_assert
      (fun _ => BFSLayerInv g src d).
Proof.
  intros d.
  unfold bfs_body_assert.
  apply Hoare_nrm_assertS_bind_intro.
  apply Hoare_implies_nrm.
  apply bfs_body_BFSLayerInv.
Qed.

Lemma snapshot_loop_BFS_IH_step_nrm :
  forall d,
    Hoare_nrm
      (fun '(_, tr) => tr = nil)
      (snapshot_loop bfs_cond bfs_body_assert)
      (fun _ '(_, tr) =>
        TraceImplies
          (haveS (sLift (BFS_IH g src d)))
          (haveS (sLift (BFS_IH g src (S d))))
          tr).
Proof.
  intros d.
  eapply Hoare_nrm_cons_post.
  2:{
    eapply snapshot_loop_inner_have_nrm with
      (inner_cond := BFSLayerCond g src d)
      (inner_inv := BFSLayerInv g src d).
    - apply BFSLayerCond_implies_bfs_cond.
    - apply bfs_body_assert_BFSLayerInv_nrm.
  }
  intros _ (s, tr) Hinner.
  apply BFS_trace_step_from_inner.
  exact Hinner.
Qed.

Lemma bfs_init_queue_visited :
  bfs_queue_visited (bfs_init_state src).
Proof.
  intros v Hin.
  unfold bfs_queue_visited, bfs_init_state in *.
  cbn in Hin |- *.
  destruct Hin as [Hv | []].
  subst v.
  exists 0.
  destruct (eq_dec src src) as [_|Hcontra].
  - reflexivity.
  - exfalso; apply Hcontra; reflexivity.
Qed.

Lemma bfs_init_queue_reachable :
  bfs_queue_reachable (bfs_init_state src).
Proof.
  intros v Hin.
  unfold bfs_queue_reachable, bfs_init_state in *.
  cbn in Hin.
  destruct Hin as [Hv | []].
  subst v.
  reflexivity.
Qed.

Theorem BFS_assert_t_trace_shape_nrm :
  Hoare_nrm
    (fun '(_, tr) => tr = nil)
    BFS_assert_t
    (fun _ '(s, tr) =>
      TraceShape St_default bfs_cond (fun s => s = bfs_init_state src) s tr).
Proof.
  unfold BFS_assert_t.
  eapply Hoare_nrm_bind with
    (Q := fun _ '(s, tr) => s = bfs_init_state src /\ tr = nil).
  - eapply Hoare_nrm_liftG'.
    intros tr.
    eapply Hoare_nrm_cons_post.
    2:{ apply Hoare_implies_nrm, Hoare_update'. }
    intros [] s [s0 [Hs Htr]].
    split.
    + unfold bfs_init_state.
      exact Hs.
    + exact Htr.
  - intros [].
    eapply snapshot_loop_trace_shape_nrm.
Qed.

Theorem BFS_assert_trace_IH_have_nrm :
  Hoare_nrm
    (fun '(_, tr) => tr = nil)
    BFS_assert_t
    (fun _ '(_, tr) => forall d, TraceHave (BFS_IH g src d) tr).
Proof.
  unfold BFS_assert_t.
  eapply Hoare_nrm_bind with
    (Q := fun _ '(s, tr) => s = bfs_init_state src /\ tr = nil).
  - eapply Hoare_nrm_liftG'.
    intros tr.
    eapply Hoare_nrm_cons_post.
    2:{ apply Hoare_implies_nrm, Hoare_update'. }
    intros [] s [s0 [Hs Htr]].
    split.
    + unfold bfs_init_state.
      exact Hs.
    + exact Htr.
  - intros [].
    eapply Hoare_nrm_cons_post with
      (Q := fun _ x =>
        (let '(_, tr) := x in TraceHave (BFS_IH g src 0) tr) /\
        (let '(_, tr) := x in
          forall d,
            TraceImplies
              (haveS (sLift (BFS_IH g src d)))
              (haveS (sLift (BFS_IH g src (S d))))
              tr)).
    + intros _ (s, tr) [Hbase Hstep] d.
      induction d as [|d IH].
      * exact Hbase.
      * specialize (Hstep d).
        unfold TraceHave in *.
        unfold TraceImplies, impliesS, trace_implies, last_satisfyS in Hstep.
        exact (Hstep IH).
    + eapply Hoare_nrm_conj.
      * eapply snapshot_loop_initial_have_nrm.
        intros s Hs.
        subst s.
        apply BFS_IH_0_init.
      * unfold Hoare_nrm.
        intros [] [s1 tr1] [s2 tr2] [_ Hnil] Hrun d.
        pose proof (snapshot_loop_BFS_IH_step_nrm d) as Hstep.
        exact (Hstep tt (s1, tr1) (s2, tr2) Hnil Hrun).
Qed.

Theorem BFS_assert_trace_nrm :
  Hoare_nrm
    (fun _ => True)
    BFS_assert
    (fun _ s =>
      exists tr,
        TraceShape St_default bfs_cond (fun s => s = bfs_init_state src) s tr /\
        (forall d, TraceHave (BFS_IH g src d) tr)).
Proof.
  eapply Hoare_nrm_fromG with
    (c' := BFS_assert_t)
    (P' := fun '(_, tr) => tr = nil).
  - apply Gequiv_BFS_assert.
  - intros s _.
    exists (@nil St').
    reflexivity.
  - eapply Hoare_nrm_cons_post with
      (Q := fun _ st =>
        (let '(s, tr) := st in
          TraceShape St_default bfs_cond (fun s => s = bfs_init_state src) s tr) /\
        (let '(_, tr) := st in
          forall d, TraceHave (BFS_IH g src d) tr)).
    + intros _ (s, tr) [Hshape Hhave].
      exists tr.
      split; assumption.
    + eapply (@Hoare_nrm_conj unit (St' * list St')
        (fun '(_, tr) => tr = nil)
        BFS_assert_t
        (fun _ '(s, tr) =>
          TraceShape St_default bfs_cond (fun s => s = bfs_init_state src) s tr)
        (fun _ '(_, tr) => forall d, TraceHave (BFS_IH g src d) tr)).
      * apply BFS_assert_t_trace_shape_nrm.
      * apply BFS_assert_trace_IH_have_nrm.
Qed.

Lemma bfs_init_state_neq_default :
  bfs_init_state src <> St_default.
Proof.
  intro Heq.
  pose proof (f_equal q Heq) as Hq.
  unfold bfs_init_state, St_default in Hq.
  simpl in Hq.
  discriminate.
Qed.

Lemma nth_last_default :
  forall (l: list St') i d,
    l <> nil ->
    i = length l - 1 ->
    nth i l d = last l d.
Proof.
  intros l.
  induction l as [|x xs IH]; intros i d Hnn Hi.
  - contradiction.
  - destruct xs as [|y ys].
    + simpl in *. subst i. reflexivity.
    + simpl in *.
      destruct i as [|i].
      * lia.
      * apply IH.
        -- discriminate.
        -- lia.
Qed.

Lemma BFS_correct_from_trace_have :
  forall s tr,
    TraceShape St_default bfs_cond (fun s => s = bfs_init_state src) s tr ->
    (forall d, TraceHave (BFS_IH g src d) tr) ->
    forall v d, bfs_dist v d <-> s.(dist) v = Some d.
Proof.
  intros s tr Hshape Hall_have.
  assert (Hall: forall d, exists i,
    i < length tr /\ BFS_IH g src d (nth i tr St_default)).
  {
    intro d.
    specialize (Hall_have d).
    unfold TraceHave in Hall_have.
    exact (haveS_exists_nth tr (BFS_IH g src d) St_default Hall_have).
  }
  destruct Hshape as [Hhd [Hlast [Hncond Hprefix]]].
  assert (Htr_nonempty: tr <> nil).
  {
    intro Hnil.
    subst tr.
    simpl in Hhd.
    apply bfs_init_state_neq_default.
    symmetry.
    exact Hhd.
  }
  destruct (finite_bfs_dist_bound g src g_valid src_valid) as [dmax Hbound].
  set (dmax_plus_one := S dmax).
  assert (Hno_layer: forall v, ~ bfs_dist v dmax_plus_one).
  {
    intros v Hdist.
    unfold dmax_plus_one in Hdist.
    pose proof (Hbound v (S dmax) Hdist).
    lia.
  }
  destruct (Hall dmax_plus_one) as [i [Hi_lt HIH_i]].
  assert (Hq_nil: q (nth i tr St_default) = nil).
  {
    destruct (q (nth i tr St_default)) as [|u qs] eqn:Hq; [reflexivity |].
    exfalso.
    apply (Hno_layer u).
    destruct HIH_i as [_ [_ Hqueue]].
    apply Hqueue.
    rewrite Hq.
    simpl.
    auto.
  }
  assert (Hi_eq: i = length tr - 1).
  {
    destruct (Nat.lt_ge_cases i (length tr - 1)) as [Hi_final | Hfinal_i].
    - exfalso.
      assert (Hcond_i: bfs_cond (nth i tr St_default)).
      { apply Hprefix; lia. }
      unfold bfs_cond in Hcond_i.
      destruct Hcond_i as [u Hu].
      rewrite Hq_nil in Hu.
      contradiction.
    - lia.
  }
  assert (Hlast_state: nth i tr St_default = s).
  {
    rewrite Hi_eq.
    rewrite (nth_last_default tr (length tr - 1) St_default
              Htr_nonempty eq_refl).
    exact Hlast.
  }
  rewrite Hlast_state in HIH_i, Hq_nil.
  apply BFS_IH_empty_correct with (d := dmax_plus_one); assumption.
Qed.

Theorem BFS_assert_correct_nrm:
  Hoare_nrm
    (fun _ => True)
    BFS_assert
    (fun _ s => forall v d, bfs_dist v d <-> s.(dist) v = Some d).
Proof.
  eapply Hoare_nrm_conseq with
    (Q2 := fun _ s =>
      exists tr,
        TraceShape St_default bfs_cond (fun s => s = bfs_init_state src) s tr /\
        (forall d, TraceHave (BFS_IH g src d) tr)).
  - intros s Hs. exact Hs.
  - intros _ s [tr [Hshape Hhave]].
    eapply BFS_correct_from_trace_have; eauto.
  - apply BFS_assert_trace_nrm.
Qed.

Lemma bfs_body_preserves_assert_inv :
  Hoare
    (fun s => bfs_cond s /\ bfs_assert_inv s)
    (bfs_body g)
    (fun _ => bfs_assert_inv).
Proof.
  intro_state.
  destruct H as [Hcond [Hreach Hvisited]].
  destruct (q s0) as [|u tail] eqn:Hq.
  {
    unfold bfs_cond in Hcond.
    destruct Hcond as [x Hx].
    rewrite Hq in Hx.
    contradiction.
  }
  destruct (Hvisited u ltac:(rewrite Hq; simpl; auto)) as [d Hud].
  eapply Hoare_conseq with
    (P2 := BFSOneStepPre (u, tail, dist s0, d))
    (Q2 := fun _ => BFSOneStepPost g (u, tail, dist s0, d)).
  - intros s Hs.
    subst s.
    unfold BFSOneStepPre.
    split; [exact Hq |].
    split; [reflexivity | exact Hud].
  - intros _ s1 Hpost.
    unfold BFSOneStepPost in Hpost.
    destruct Hpost as [l3 [Hq1 [Hl3 [Hset Hkeep]]]].
    unfold bfs_assert_inv.
    split.
    + intros v Hin.
      rewrite Hq1 in Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin_tail | Hin_l3].
      * apply Hreach.
        rewrite Hq.
        simpl.
        right.
        exact Hin_tail.
      * apply Hl3 in Hin_l3.
        destruct Hin_l3 as [Hstep _].
        eapply reachable_step_reachable.
        -- apply Hreach.
           rewrite Hq.
           simpl.
           left.
           reflexivity.
        -- exact Hstep.
    + intros v Hin.
      rewrite Hq1 in Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin_tail | Hin_l3].
      * destruct (Hvisited v) as [d0 Hd0].
        {
          rewrite Hq.
          simpl.
          right.
          exact Hin_tail.
        }
        exists d0.
        rewrite Hkeep.
        -- exact Hd0.
        -- intro Hin3.
           apply Hl3 in Hin3.
           destruct Hin3 as [_ Hnone].
           rewrite Hd0 in Hnone.
           discriminate.
      * exists (S d).
        apply Hset.
        exact Hin_l3.
  - apply bfs_body_BFSOneStep.
Qed.

Theorem BFS_assert_safe :
  Hoare
    (fun _ => True)
    BFS_assert
    (fun _ _ => True).
Proof.
  unfold BFS_assert.
  eapply Hoare_bind with (Q := fun _ s => bfs_assert_inv s).
  - eapply Hoare_cons_post.
    2:{ apply Hoare_update'. }
    intros [] s [s0 [Hs _]].
    subst s.
    split.
    + apply bfs_init_queue_reachable.
    + apply bfs_init_queue_visited.
  - intros [].
    eapply Hoare_conseq_post.
    2:{
      eapply Hoare_whileP with (P := bfs_assert_inv).
      unfold bfs_body_assert.
      eapply Hoare_bind.
      - apply Hoare_assertS.
        intros s [Hcond Hinv].
        exact Hinv.
      - intros [].
        eapply Hoare_cons_pre.
        2:{ apply bfs_body_preserves_assert_inv. }
        intros s [Hcond Hinv].
        split; assumption.
    }
    intros _ s _.
    exact I.
Qed.

Theorem BFS_assert_correct:
  Hoare
    (fun _ => True)
    BFS_assert
    (fun _ s => forall v d, bfs_dist v d <-> s.(dist) v = Some d).
Proof.
  eapply Hoare_conseq_post.
  2:{
    eapply Hoare_nrm_Hoare_conj.
    - apply BFS_assert_correct_nrm.
    - apply BFS_assert_safe.
  }
  intros _ s [Hcorrect _].
  exact Hcorrect.
Qed.

End BFSAssert.
