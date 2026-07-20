Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.EquivDec.
Require Import SetsClass.SetsClass.
From MonadLib.MonadErr Require Import monadesafe_lib MonadErrLoop.
From TraceLib.MonadErr Require Import TraceLoopErr.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic bfs_dist.
From Algorithms Require Import MapLib BFS.
Require Import Algorithms.BFS.BFS_assert.

Module BFSP := BFS.
Module BFSA := BFS_assert.

Import SetsNotation.
Import MonadNotation.
Local Open Scope list.
Local Open Scope sets.
Local Open Scope monad.
Local Open Scope map_scope.

#[local] Existing Instance MonadErrBasic.state_rel_monad.

Section GoLiberty.

Context
  {G V E: Type}
  `{graph: Graph G V E}
  `{gv: GValid G}
  `{stepvalid: @StepValid G V E graph gv}
  `{finite_graph: @FiniteGraph G V E graph gv}
  (g: G)
  `{eq_dec: EqDec V eq}.

Notation step := (step g).
Notation reachable := (reachable g).

Inductive PointTag: Type :=
| Stone
| Liberty.

Context (tag: V -> PointTag).
Context (src: V)
        (g_valid: gvalid g)
        (src_valid: vvalid g src).

Local Notation bfs_dist := (bfs_dist g src).
Local Notation err_ret :=
  (@ret (MonadErrBasic.program BFSP.St)
    (MonadErrBasic.state_rel_monad BFSP.St)).

Definition bfs_loop : MonadErrBasic.program BFSP.St unit :=
  MonadErrLoop.whileP BFSP.bfs_cond (BFSA.bfs_body_assert g src).

Record GoSt: Type := mkGoSt {
  go_seen: V -> bool;
  go_q: list V;
}.

Definition is_stone (v: V): Prop :=
  tag v = Stone.

Definition is_liberty (v: V): Prop :=
  tag v = Liberty.

Definition go_init_state : GoSt := {|
  go_seen := src !-> true; _ !-> false;
  go_q := src :: nil;
|}.

Definition go_init : program GoSt unit :=
  update' (fun _ => go_init_state).

Definition enqueue_unseen_neighbors (u: V): program GoSt unit :=
  tovisit <- get' (fun s v => step u v /\ s.(go_seen) v = false);;
  forset tovisit
    (fun v =>
      update' (fun s => {|
        go_seen := v !-> true; s.(go_seen);
        go_q := s.(go_q) ++ v :: nil;
      |})).

Definition go_body (_: unit): program GoSt (CntOrBrk unit bool) :=
  choice
    (assume (fun s => s.(go_q) = nil);;
     break false)
    (tail <- any (list V);;
     u <- get (fun s u => s.(go_q) = u :: tail);;
     update' (fun s => {|
       go_seen := s.(go_seen);
       go_q := tail;
     |});;
     match tag u with
     | Liberty => break true
     | Stone =>
         enqueue_unseen_neighbors u;;
         continue tt
     end).

Definition go_liberty : program GoSt bool :=
  go_init;;
  repeat_break go_body tt.

(** [GoBFSRel] is the simulation relation between the concrete Go search and
    the abstract BFS program.  The queues are kept syntactically equal, while
    Go's boolean [seen] map is related to BFS's distance map by
    [seen v = true <-> dist v = Some _].  The latter is why [BFS_assert]
    asserts both reachability and "queued vertices have a distance entry". *)
Definition GoBFSRel (go_s: GoSt) (bfs_s: BFSP.St) : Prop :=
  go_s.(go_q) = bfs_s.(BFSP.q) /\
  forall v,
    go_s.(go_seen) v = true <->
    exists d, bfs_s.(BFSP.dist) v = Some d.

(** This auxiliary invariant is only about the concrete Go state.  It lets the
    false exit case conclude that no already-seen liberty exists once the queue
    is empty. *)
Definition GoLibSeenOnlyInQueue (s: GoSt): Prop :=
  forall v, s.(go_seen) v = true -> tag v = Liberty -> In v s.(go_q).

Lemma GoBFSRel_init :
  GoBFSRel go_init_state (BFSP.bfs_init_state src).
Proof.
  unfold GoBFSRel, go_init_state, BFSP.bfs_init_state.
  simpl.
  split; [reflexivity|].
  intro v.
  unfold t_set, t_empty.
  destruct (equiv_dec src v) as [Heq | Hneq].
  - subst.
    split; intros _.
    + exists 0.
      destruct (eq_dec v src) as [_ | Hcontra]; [reflexivity|].
      exfalso; apply Hcontra; symmetry; exact Heq.
    + destruct (equiv_dec v v) as [_ | Hcontra]; [reflexivity|].
      exfalso; apply Hcontra; reflexivity.
  - split; intros H.
    + discriminate.
    + destruct H as [d Hd].
      destruct (eq_dec v src) as [Heq | _].
      * exfalso; apply Hneq; symmetry; exact Heq.
      * discriminate.
Qed.

Lemma GoLibSeenOnlyInQueue_init :
  GoLibSeenOnlyInQueue go_init_state.
Proof.
  unfold GoLibSeenOnlyInQueue, go_init_state.
  simpl.
  intros v Hseen _.
  unfold t_set, t_empty in Hseen.
  destruct (equiv_dec src v) as [Heq | Hneq].
  - subst; simpl; auto.
  - discriminate.
Qed.

Lemma GoBFSRel_seen_false_none go_s bfs_s v:
  GoBFSRel go_s bfs_s ->
  go_s.(go_seen) v = false ->
  bfs_s.(BFSP.dist) v = None.
Proof.
  intros [_ Hseen] Hfalse.
  destruct (bfs_s.(BFSP.dist) v) as [d|] eqn:Hd; [|reflexivity].
  exfalso.
  pose proof (proj2 (Hseen v) (ex_intro _ d Hd)) as Htrue.
  rewrite Hfalse in Htrue.
  discriminate.
Qed.

Lemma safeExec_BFS_assert_after_init X:
  safeExec (fun _ => True) (BFSA.BFS_assert g src) X ->
  safeExec (GoBFSRel go_init_state) bfs_loop X.
Proof.
  intro Hsafe.
  unfold BFSA.BFS_assert, BFSP.bfs_init in Hsafe.
  change (BFSP.bfs_init_state src) with
    ((fun _ : BFSP.St => BFSP.bfs_init_state src) (BFSP.bfs_init_state src)).
  apply safeExec_update'_bind in Hsafe.
  eapply safeExec_conseq; eauto.
  intros s [s0 [Hs _]].
  subst s.
  apply GoBFSRel_init.
Qed.

Lemma safeExec_bfs_loop_exit go_s X:
  go_s.(go_q) = nil ->
  safeExec (GoBFSRel go_s) bfs_loop X ->
  forall v,
    safeExec
      (fun bfs_s =>
        go_s.(go_seen) v = true <->
        exists d, bfs_s.(BFSP.dist) v = Some d)
      (err_ret tt) X.
Proof.
  intros Hqnil Hsafe v.
  unfold bfs_loop, BFSA.bfs_body_assert in Hsafe.
  rewrite MonadErrLoop.whileP_unfold in Hsafe.
  safe_choice_r Hsafe.
  eapply safeExec_conseq; eauto.
  intros bfs_s Hrel.
  apply Hrel.
  intros bfs_s [Hqrel _].
  unfold BFSP.bfs_cond.
  rewrite <- Hqrel.
  rewrite Hqnil.
  intros [u Hu].
  contradiction.
Qed.

Lemma safeExec_bfs_loop_head_reachable go_s u tail X:
  go_s.(go_q) = u :: tail ->
  safeExec (GoBFSRel go_s) bfs_loop X ->
  reachable src u.
Proof.
  intros Hq Hsafe.
  unfold bfs_loop, BFSA.bfs_body_assert in Hsafe.
  rewrite MonadErrLoop.whileP_unfold in Hsafe.
  safe_choice_l Hsafe.
  2:{
    intros bfs_s [Hqrel _].
    unfold BFSP.bfs_cond.
    exists u.
    rewrite <- Hqrel.
    rewrite Hq.
    simpl.
    auto.
  }
  apply safeExec_assertS_seq in Hsafe.
  destruct Hsafe as [bfs_s [[Hreach Hrel] _]].
  unfold BFSA.bfs_queue_reachable in Hreach.
  apply Hreach.
  destruct Hrel as [Hqrel _].
  rewrite <- Hqrel.
  rewrite Hq.
  simpl.
  auto.
Qed.

Lemma safeExec_err_forset_pick {Σ A B: Type}
  (universe: A -> Prop)
  (body: A -> MonadErrBasic.program Σ unit)
  (c: MonadErrBasic.program Σ B)
  (P: Σ -> Prop) X a:
  a ∈ universe ->
  safeExec P
    (bind (MonadErrLoop.forset universe body) (fun _ => c)) X ->
  safeExec P
    (bind (body a) (fun _ =>
       bind
         (MonadErrLoop.forset (fun x => universe x /\ x <> a) body)
         (fun _ => c)))
    X.
Proof.
  intros Ha Hsafe.
  eapply safeExec_proequiv in Hsafe.
  2:{
    eapply (@MonadErrBasic.bind_equiv Σ unit B
      (MonadErrLoop.forset universe body)
      (MonadErrBasic.choice
        (bind
          (MonadErrBasic.get (fun _ a0 => a0 ∈ universe))
          (fun a0 =>
            bind (body a0) (fun _ =>
              MonadErrLoop.forset (fun x => x ∈ universe /\ x <> a0) body)))
        (bind
          (MonadErrBasic.testPure (universe == ∅)%sets)
          (fun _ => ret tt)))
      (fun _ => c)
      (fun _ => c)).
    - apply MonadErrLoop.forset_unfold.
    - hnf; intros []; constructor; simpl; reflexivity.
  }
  prog_nf in Hsafe.
  safe_choice_l Hsafe.
  eapply (highstepbind_derive _ _ _ a P) in Hsafe.
  - eapply safeExec_proequiv.
    + apply MonadErrBasic.bind_assoc.
    + exact Hsafe.
  - unfold hs_eval.
    intros σ HP.
    exists σ.
    split.
    + unfold MonadErrBasic.get.
      simpl.
      split; auto.
    + exact HP.
Qed.

Lemma safeExec_err_forset_empty {Σ A B: Type}
  (universe: A -> Prop)
  (body: A -> MonadErrBasic.program Σ unit)
  (c: MonadErrBasic.program Σ B)
  (P: Σ -> Prop) X:
  (universe == ∅)%sets ->
  safeExec P
    (bind (MonadErrLoop.forset universe body) (fun _ => c)) X ->
  safeExec P c X.
Proof.
  intros Hempty Hsafe.
  eapply safeExec_proequiv in Hsafe.
  2:{
    eapply (@MonadErrBasic.bind_equiv Σ unit B
      (MonadErrLoop.forset universe body)
      (MonadErrBasic.choice
        (bind
          (MonadErrBasic.get (fun _ a0 => a0 ∈ universe))
          (fun a0 =>
            bind (body a0) (fun _ =>
              MonadErrLoop.forset (fun x => x ∈ universe /\ x <> a0) body)))
        (bind
          (MonadErrBasic.testPure (universe == ∅)%sets)
          (fun _ => ret tt)))
      (fun _ => c)
      (fun _ => c)).
    - apply MonadErrLoop.forset_unfold.
    - hnf; intros []; constructor; simpl; reflexivity.
  }
  prog_nf in Hsafe.
  safe_choice_r Hsafe.
  exact Hsafe.
Qed.

Lemma safeExec_err_forset_pick_no_bind {Σ A: Type}
  (universe: A -> Prop)
  (body: A -> MonadErrBasic.program Σ unit)
  (P: Σ -> Prop) X a:
  a ∈ universe ->
  safeExec P (MonadErrLoop.forset universe body) X ->
  safeExec P
    (bind (body a) (fun _ =>
       MonadErrLoop.forset (fun x => universe x /\ x <> a) body))
    X.
Proof.
  intros Ha Hsafe.
  eapply safeExec_proequiv in Hsafe.
  2:{ apply MonadErrLoop.forset_unfold. }
  prog_nf in Hsafe.
  safe_choice_l Hsafe.
  eapply (highstepbind_derive _ _ _ a P) in Hsafe.
  - exact Hsafe.
  - unfold hs_eval.
    intros σ HP.
    exists σ.
    split.
    + unfold MonadErrBasic.get.
      simpl.
      split; auto.
    + exact HP.
Qed.

Lemma safeExec_err_forset_empty_no_bind {Σ A: Type}
  (universe: A -> Prop)
  (body: A -> MonadErrBasic.program Σ unit)
  (P: Σ -> Prop) X:
  (universe == ∅)%sets ->
  safeExec P (MonadErrLoop.forset universe body) X ->
  safeExec P (ret tt) X.
Proof.
  intros Hempty Hsafe.
  eapply safeExec_proequiv in Hsafe.
  2:{ apply MonadErrLoop.forset_unfold. }
  prog_nf in Hsafe.
  safe_choice_r Hsafe.
  exact Hsafe.
Qed.

Lemma safeExec_err_ret {Σ A: Type} (a: A) (P: Σ -> Prop) X:
  safeExec P (ret a) X ->
  exists s, P s /\ X a s.
Proof.
  unfold safeExec, safe.
  intros [s [HP Hwp]].
  rewrite MonadErrHoare.wp_ret in Hwp.
  exists s; tauto.
Qed.

Lemma safeExec_get_exists_bind {Σ A B: Type}
  (Pa: Σ -> A -> Prop)
  (P: Σ -> Prop)
  (c: A -> MonadErrBasic.program Σ B)
  X:
  (forall s, P s -> exists a, Pa s a) ->
  safeExec P (a <- MonadErrBasic.get Pa;; c a) X ->
  exists a, safeExec (fun s => P s /\ Pa s a) (c a) X.
Proof.
  intros Hexists Hsafe.
  apply safeExec_bind in Hsafe.
  destruct Hsafe as [X' [Hget Hcont]].
  unfold safeExec, safe in Hget.
  destruct Hget as [s [HP Hwp]].
  destruct (Hexists s HP) as [a Ha].
  exists a.
  eapply Hcont.
  unfold safeExec, safe.
  exists s.
  split; [split; assumption|].
  rewrite MonadErrHoare.wp_ret.
  rewrite MonadErrHoare.wp_get in Hwp.
  apply Hwp.
  exact Ha.
Qed.

Lemma safeExec_get'_bind {Σ A B: Type}
  (a: A) (f: Σ -> A) (P: Σ -> Prop)
  (c: A -> MonadErrBasic.program Σ B) X:
  (forall s, P s -> a = f s) ->
  safeExec P (a0 <- MonadErrBasic.get' f;; c a0) X ->
  safeExec P (c a) X.
Proof.
  intros Hget.
  eapply safeExec_bind_reta with (a:= a).
  intros X' Hsafe.
  eapply safeExec_get' with (f:= f); auto.
Qed.

Lemma GoLibSeenOnlyInQueue_pop go_s u tail:
  go_s.(go_q) = u :: tail ->
  tag u = Stone ->
  GoLibSeenOnlyInQueue go_s ->
  GoLibSeenOnlyInQueue {| go_seen := go_s.(go_seen); go_q := tail |}.
Proof.
  intros Hq Htag Hlib v Hseen Hvlib.
  specialize (Hlib v Hseen Hvlib).
  rewrite Hq in Hlib.
  simpl in Hlib.
  destruct Hlib as [Hu | Hin]; [subst; congruence|exact Hin].
Qed.

Lemma GoLibSeenOnlyInQueue_enqueue s a:
  GoLibSeenOnlyInQueue s ->
  GoLibSeenOnlyInQueue
    {| go_seen := a !-> true; s.(go_seen);
       go_q := s.(go_q) ++ a :: nil |}.
Proof.
  intros Hlib v Hseen Hvlib.
  simpl in *.
  unfold t_set in Hseen.
  destruct (equiv_dec a v) as [Ha | Ha].
  - apply in_or_app.
    right; simpl; left.
    destruct Ha; reflexivity.
  - apply in_or_app.
    left.
    eapply Hlib; eauto.
Qed.

Lemma GoBFSRel_enqueue go_s bfs_s a d:
  GoBFSRel go_s bfs_s ->
  GoBFSRel
    {| go_seen := a !-> true; go_s.(go_seen);
       go_q := go_s.(go_q) ++ a :: nil |}
    {| BFSP.dist := a !-> Some d; bfs_s.(BFSP.dist);
       BFSP.q := bfs_s.(BFSP.q) ++ a :: nil |}.
Proof.
  intros [Hq Hseen].
  split.
  - simpl.
    rewrite Hq.
    reflexivity.
  - intros v.
    simpl.
    unfold t_set.
    destruct (equiv_dec a v) as [Ha | Ha].
    + destruct Ha.
      split; intros _; [exists d; destruct (equiv_dec a a); congruence|].
      destruct (equiv_dec a a); [reflexivity|congruence].
    + split; intros H.
      * apply Hseen in H.
        destruct H as [d0 Hd0].
        exists d0.
        destruct (equiv_dec a v); [congruence|exact Hd0].
      * destruct H as [d0 Hd0].
        destruct (equiv_dec a v); [congruence|].
        apply Hseen.
        exists d0; exact Hd0.
Qed.

(** Unroll one Stone iteration of the abstract asserted BFS loop.

    Starting from [safeExec (GoBFSRel go_s) bfs_loop X] and a concrete queue
    head [u], this lemma consumes the abstract loop guard, assertion, queue pop,
    and [get'] of the neighbor set.  What remains is exactly the abstract
    [forset] that enqueues BFS successors, together with:
    - [Xtail], the continuation after that [forset];
    - a continuation rule that plugs [ret tt] under [Xtail] back into
      [bfs_loop];
    - a pointwise equivalence between the concrete unseen-neighbor set and the
      abstract [dist = None] neighbor set.

    The Stone proof below can then focus on synchronizing the two [forset]s. *)
Lemma safeExec_bfs_loop_stone_unroll go_s u tail X:
  go_s.(go_q) = u :: tail ->
  safeExec (GoBFSRel go_s) bfs_loop X ->
  exists bfs_s0 d_u Xtail,
    BFSA.bfs_assert_inv g src bfs_s0 /\
    GoBFSRel go_s bfs_s0 /\
    safeExec
      (GoBFSRel {| go_seen := go_s.(go_seen); go_q := tail |})
      (MonadErrLoop.forset
        (fun v : V => step u v /\ BFSP.dist bfs_s0 v = None)
        (fun v : V =>
          MonadErrBasic.update'
            (fun s : BFSP.St =>
              {| BFSP.dist := v !-> Some (S d_u); BFSP.dist s;
                 BFSP.q := BFSP.q s ++ v :: nil |})))
      Xtail /\
    (forall P',
      safeExec P' (err_ret tt) Xtail ->
      safeExec P' bfs_loop X) /\
    (forall v,
      (step u v /\ go_s.(go_seen) v = false) <->
      (step u v /\ BFSP.dist bfs_s0 v = None)).
Proof.
  intros Hq Hsafe.
  unfold bfs_loop, BFSA.bfs_body_assert in Hsafe.
  rewrite MonadErrLoop.whileP_unfold in Hsafe.
  safe_choice_l Hsafe.
  2:{
    intros bfs_s [Hqrel _].
    unfold BFSP.bfs_cond.
    exists u.
    rewrite <- Hqrel, Hq.
    simpl; auto.
  }
  apply safeExec_assertS_seq in Hsafe.
  destruct Hsafe as [bfs_s0 [[Hassert Hrel0] Hsafe]].
  assert (Hsafebody:
    safeExec
      (fun s => s = bfs_s0 /\ BFSA.bfs_assert_inv g src s /\ GoBFSRel go_s s)
      (BFSP.bfs_body g;;
       MonadErrLoop.whileP BFSP.bfs_cond
         (MonadErrBasic.assertS (BFSA.bfs_assert_inv g src);; BFSP.bfs_body g))
      X).
  {
    exists bfs_s0.
    split.
    - split; [reflexivity|split; assumption].
    - exact Hsafe.
  }
  clear Hsafe.
  apply safeExec_bind in Hsafebody.
  destruct Hsafebody as [Xtail [Hbody Hcont_tail]].
  unfold BFSP.bfs_body in Hbody.
  eapply (@safeExec_any_bind BFSP.St unit (list V)) with (a:=tail) in Hbody.
  eapply safeExec_get_bind with (a:=u) in Hbody.
  2:{
    intros bfs_s [Hbfs_eq [_ Hrel]].
    subst bfs_s.
    destruct Hrel as [Hqrel _].
    rewrite <- Hqrel.
    exact Hq.
  }
  apply safeExec_get_exists_bind in Hbody.
  2:{
    intros s [Hs [Hassert_s Hrel_s]].
    subst s.
    destruct Hassert_s as [_ Hvisited].
    apply Hvisited.
    destruct Hrel_s as [Hqrel _].
    rewrite <- Hqrel, Hq.
    simpl; auto.
  }
  destruct Hbody as [d_u Hbody].
  apply safeExec_update'_bind in Hbody.
  set (abs_universe := fun v : V => step u v /\ BFSP.dist bfs_s0 v = None).
  set (abs_body := fun v : V =>
    MonadErrBasic.update'
      (fun s : BFSP.St =>
        {| BFSP.dist := v !-> Some (S d_u); BFSP.dist s;
           BFSP.q := BFSP.q s ++ v :: nil |})).
  eapply safeExec_get'_bind with (a:=abs_universe) in Hbody.
  2:{
    intros s [s0 [Hs [[Hs0 [_ _]] _]]].
    subst s0 s.
    reflexivity.
  }
  change (safeExec
    (fun s : BFSP.St =>
      exists s0 : BFSP.St,
        s = {| BFSP.dist := BFSP.dist s0; BFSP.q := tail |} /\
        (s0 = bfs_s0 /\ BFSA.bfs_assert_inv g src s0 /\ GoBFSRel go_s s0) /\
        BFSP.dist s0 u = Some d_u)
    (MonadErrLoop.forset abs_universe abs_body) Xtail) in Hbody.
  exists bfs_s0, d_u, Xtail.
  split; [exact Hassert|].
  split; [exact Hrel0|].
  split.
  - eapply safeExec_conseq; [exact Hbody|].
    intros bfs_s [s0 [Hbfs [[Hs0 [_ Hrel]] _]]].
    subst s0 bfs_s.
    destruct Hrel as [_ Hseenrel].
    split; simpl; [reflexivity|exact Hseenrel].
  - split.
    + intros P' Hret.
      pose proof (Hcont_tail P' tt Hret) as Hloop.
      unfold bfs_loop, BFSA.bfs_body_assert.
      exact Hloop.
    + intro v.
      unfold abs_universe.
      split.
      * intros [Hstep Hseen_false].
        split; [assumption|].
        eapply GoBFSRel_seen_false_none; eauto.
      * intros [Hstep Hnone].
        split; [assumption|].
        destruct (go_s.(go_seen) v) eqn:Hseen_bool; [|reflexivity].
        destruct Hrel0 as [_ Hseenrel].
        pose proof (proj1 (Hseenrel v) Hseen_bool) as [d Hd].
        rewrite Hnone in Hd.
        discriminate.
Qed.

(** Synchronize [enqueue_unseen_neighbors] with the remaining abstract BFS
    [forset] produced by [safeExec_bfs_loop_stone_unroll].

    The concrete side uses [Hoare_forset].  Its loop invariant records:
    - the concrete invariant [GoLibSeenOnlyInQueue];
    - an abstract remaining set [rem], equal to the abstract universe minus the
      concrete [done] set;
    - a [safeExec] proof that the abstract [forset rem] can still complete.

    In the inductive step we consume the same element [a] from the abstract
    [forset], execute both updates, and re-establish [GoBFSRel] via
    [GoBFSRel_enqueue]. *)
Lemma safeExec_bfs_loop_stone_step go_s u tail X:
  go_s.(go_q) = u :: tail ->
  tag u = Stone ->
  GoLibSeenOnlyInQueue go_s ->
  safeExec (GoBFSRel go_s) bfs_loop X ->
  StateRelHoare.Hoare
    (fun s => s = {|
      go_seen := go_s.(go_seen);
      go_q := tail;
    |})
    (enqueue_unseen_neighbors u)
    (fun _ s => GoLibSeenOnlyInQueue s /\ safeExec (GoBFSRel s) bfs_loop X).
Proof.
  intros Hq Htag Hlib Hsafe.
  set (go_pop := {| go_seen := go_s.(go_seen); go_q := tail |}).
  set (universe := fun v : V => step u v /\ go_s.(go_seen) v = false).
  destruct (safeExec_bfs_loop_stone_unroll go_s u tail X Hq Hsafe)
    as [bfs_s0 [d_u [Xtail
      [Hassert [Hrel0 [Hsafe_abs0 [Hcont_tail Huniv_abs]]]]]]].
  set (abs_universe := fun v : V => step u v /\ BFSP.dist bfs_s0 v = None).
  set (abs_body := fun v : V =>
    MonadErrBasic.update'
      (fun s : BFSP.St =>
        {| BFSP.dist := v !-> Some (S d_u); BFSP.dist s;
           BFSP.q := BFSP.q s ++ v :: nil |})).
  unfold enqueue_unseen_neighbors.
  apply StateRelHoare.Hoare_state_intro.
  intros s0 Hs0.
  subst s0.
  eapply StateRelHoare.Hoare_bind.
  - apply StateRelHoare.Hoare_get'.
  - intros tovisit.
    apply StateRelHoare.Hoare_state_intro.
    intros s Hget.
    destruct Hget as [Hs Htovisit].
    subst s tovisit.
    (* [done] is the set already processed by the concrete [forset].  The
       existential [rem] is the abstract set still to be processed.  Keeping
       them related by a pointwise iff avoids needing function extensionality
       or setoid rewriting over predicate-valued sets. *)
    set (I := fun done (s : GoSt) =>
      GoLibSeenOnlyInQueue s /\
      exists rem,
        (forall x, rem x <-> abs_universe x /\ ~ done x) /\
        safeExec (GoBFSRel s) (MonadErrLoop.forset rem abs_body) Xtail).
    eapply StateRelHoare.Hoare_conseq with
      (P2 := I (fun _ : V => False))
      (Q2 := fun _ s => I universe s).
    + intros s Hs.
      subst s.
      split.
      * eapply GoLibSeenOnlyInQueue_pop; eauto.
      * exists abs_universe.
        split.
        -- firstorder.
        -- exact Hsafe_abs0.
    + intros [] s HI.
      destruct HI as [Hlib_s [rem [Hrem Hsafe_rem]]].
      split; [exact Hlib_s|].
      assert (Hempty: (rem == ∅)%sets).
      {
        sets_unfold.
        intro x.
        split; intro Hx; [|contradiction].
        apply Hrem in Hx.
        destruct Hx as [Habs Hnot].
        apply Huniv_abs in Habs.
        contradiction.
      }
      pose proof (safeExec_err_forset_empty_no_bind rem abs_body
        (GoBFSRel s) Xtail Hempty Hsafe_rem) as Hret.
      exact (Hcont_tail (GoBFSRel s) Hret).
    + eapply (@StateRelHoare.Hoare_forset GoSt V I universe
        (fun v : V =>
          update' (fun s : GoSt =>
            {| go_seen := v !-> true; s.(go_seen);
               go_q := s.(go_q) ++ v :: nil |}))).
      * intros done1 done2 Heq s1 s2 Hs.
        subst s2.
        unfold I.
        sets_unfold in Heq.
        split; intros [Hlib1 [rem [Hrem Hsafe_rem]]].
        -- split; [exact Hlib1|].
           exists rem.
           split; [|exact Hsafe_rem].
           intro x.
           specialize (Hrem x).
           rewrite Hrem.
           split.
           ++ intros [Habs Hnot].
              split; [assumption|].
              intro Hdone2.
              apply Hnot.
              apply Heq.
              exact Hdone2.
           ++ intros [Habs Hnot].
              split; [assumption|].
              intro Hdone1.
              apply Hnot.
              apply Heq.
              exact Hdone1.
        -- split; [exact Hlib1|].
           exists rem.
           split; [|exact Hsafe_rem].
           intro x.
           specialize (Hrem x).
           rewrite Hrem.
           split.
           ++ intros [Habs Hnot].
              split; [assumption|].
              intro Hdone1.
              apply Hnot.
              apply Heq.
              exact Hdone1.
           ++ intros [Habs Hnot].
              split; [assumption|].
              intro Hdone2.
              apply Hnot.
              apply Heq.
              exact Hdone2.
      * intros done a Hsub Ha Hnotin.
        apply StateRelHoare.Hoare_state_intro.
        intros s HI.
        destruct HI as [Hlib_s [rem [Hrem Hsafe_rem]]].
        eapply StateRelHoare.Hoare_conseq_post.
        2:{ apply StateRelHoare.Hoare_update'. }
        intros [] s' Hs'.
        subst s'.
        split.
        -- apply GoLibSeenOnlyInQueue_enqueue.
           exact Hlib_s.
        -- exists (fun x => rem x /\ x <> a).
           split.
           ++ intro x.
              rewrite Hrem.
              sets_unfold.
              split.
              ** intros [[Habs Hnotdone] Hxa].
                 split; [assumption|].
                 intros [Hdone | Hx]; [apply Hnotdone; exact Hdone|].
                 apply Hxa; symmetry; exact Hx.
              ** intros [Habs Hnotdonea].
                 split.
                 --- split; [assumption|].
                     intro Hdone.
                     apply Hnotdonea.
                     left; exact Hdone.
                 --- intro Hx.
                     apply Hnotdonea.
                     right; symmetry; exact Hx.
           ++ assert (Ha_rem: a ∈ rem).
              {
                apply Hrem.
                split.
                - apply Huniv_abs.
                  exact Ha.
                - exact Hnotin.
              }
              pose proof (safeExec_err_forset_pick_no_bind rem abs_body
                (GoBFSRel s) Xtail a Ha_rem Hsafe_rem) as Hsafe_pick.
              unfold abs_body in Hsafe_pick.
              apply safeExec_update'_bind in Hsafe_pick.
              eapply safeExec_conseq; [exact Hsafe_pick|].
              intros bfs_s [bfs_old [Hbfs Hrel_old]].
              subst bfs_s.
              apply GoBFSRel_enqueue.
              exact Hrel_old.
Qed.

(** Main refinement bridge.  The Go program is still written in
    [StateRelMonad], while [BFSA.BFS_assert] is a [MonadErr] program.  The
    invariant of the Go loop stores a [safeExec] proof for the remaining
    abstract BFS loop, so every concrete branch can consume the corresponding
    abstract behavior:
    - empty queue: consume the abstract loop exit;
    - Stone head: use [safeExec_bfs_loop_stone_step];
    - Liberty head: use the asserted BFS queue facts to obtain reachability. *)
Theorem go_liberty_BFS_rel X:
  safeExec (fun _ => True) (BFSA.BFS_assert g src) X ->
  StateRelHoare.Hoare (fun _ => True) 
        (go_liberty) 
        (fun b s =>
          match b with
          | true => exists v, reachable src v /\ tag v = Liberty
          | false =>
              (forall v, s.(go_seen) v = true -> tag v <> Liberty) /\
              (forall v, safeExec (fun bfs_s => s.(go_seen) v = true <-> exists d, bfs_s.(BFSP.dist) v = Some d) (err_ret tt) X)
          end).
Proof.
  intro Hsafe0.
  unfold go_liberty.
  eapply StateRelHoare.Hoare_bind with
    (Q := fun _ s => GoLibSeenOnlyInQueue s /\ safeExec (GoBFSRel s) bfs_loop X).
  - eapply StateRelHoare.Hoare_conseq_post.
    2: apply StateRelHoare.Hoare_update.
    intros [] s [s0 [Hs _]].
    subst s.
    split.
    + apply GoLibSeenOnlyInQueue_init.
    + apply safeExec_BFS_assert_after_init; exact Hsafe0.
  - intros [].
    refine ((StateRelHoare.Hoare_repeat_break go_body
      (fun _ s => GoLibSeenOnlyInQueue s /\ safeExec (GoBFSRel s) bfs_loop X)
      (fun b s =>
       if b then exists v : V, reachable src v /\ tag v = Liberty
       else (forall v : V, go_seen s v = true -> tag v <> Liberty) /\
         (forall v : V,
          safeExec
            (fun bfs_s : BFSP.St =>
             go_seen s v = true <-> (exists d : nat, BFSP.dist bfs_s v = Some d))
            (err_ret tt) X))
      _) tt).
    intros [].
    unfold go_body.
    apply StateRelHoare.Hoare_choice.
    (* Concrete queue is empty: the abstract BFS loop must also be able to exit,
       and the concrete queue invariant rules out any seen liberty. *)
    + apply StateRelHoare.Hoare_assume_bind.
      apply StateRelHoare.Hoare_ret'.
      intros s [Hqnil [Hlib Hsafe]].
      split.
      * intros v Hseen Htag.
        specialize (Hlib v Hseen Htag).
        rewrite Hqnil in Hlib; contradiction.
      * apply safeExec_bfs_loop_exit; assumption.
    + eapply StateRelHoare.Hoare_bind.
      * apply StateRelHoare.Hoare_any.
      * intros tail.
        eapply StateRelHoare.Hoare_bind.
        -- apply StateRelHoare.Hoare_get.
        -- intros u.
           eapply StateRelHoare.Hoare_bind.
           { apply StateRelHoare.Hoare_update. }
           { intros [].
              apply StateRelHoare.Hoare_state_intro.
              intros s Hpre.
              destruct Hpre as [s1 [Hs [Hq [Hlib Hsafe]]]].
              subst s.
              destruct (tag u) eqn:Htag.
              (* Stone: process one BFS layer step in lock-step. *)
              * eapply StateRelHoare.Hoare_bind.
                -- eapply safeExec_bfs_loop_stone_step; eauto.
                -- intros [].
                   apply StateRelHoare.Hoare_ret'.
                   intros s H; exact H.
              (* Liberty: the asserted BFS invariant says the queue head is
                 reachable, so Go can return [true] immediately. *)
              * apply StateRelHoare.Hoare_ret'.
                intros s _.
                exists u.
                split; [| exact Htag].
                eapply safeExec_bfs_loop_head_reachable; eauto. }
Qed.

(** Final correctness uses the refinement bridge and the already-proved
    correctness of asserted BFS.  The false case reads the abstract final
    distance-map specification through [GoBFSRel]. *)
Theorem go_liberty_correct:
  StateRelHoare.Hoare
    (fun _ => True)
    go_liberty
    (fun b _ => match b with
      | true => exists v, reachable src v /\ tag v = Liberty
      | false => ~ exists v, reachable src v /\ tag v = Liberty
      end).
Proof.
  eapply StateRelHoare.Hoare_conseq_post with
    (Q2 := fun (b: bool) s =>
      if b then exists v : V, reachable src v /\ tag v = Liberty
      else (forall v : V, go_seen s v = true -> tag v <> Liberty) /\
        (forall v : V,
          safeExec
            (fun bfs_s : BFSP.St =>
             go_seen s v = true <-> (exists d : nat, BFSP.dist bfs_s v = Some d))
            (err_ret tt)
            (fun (_ : unit) (bfs_s : BFSP.St) =>
              forall v d, bfs_dist v d <-> BFSP.dist bfs_s v = Some d))).
  - intros b s Hpost.
    destruct b; simpl in *.
    + exact Hpost.
    + destruct Hpost as [Hnolib Hrel].
      intros [v [Hreach Htag]].
      specialize (Hrel v).
      apply safeExec_err_ret in Hrel.
      destruct Hrel as [bfs_s [Hseen Hcorrect]].
      apply Hnolib with (v := v).
      * apply Hseen.
        apply reachable_iff_bfs_dist in Hreach.
        destruct Hreach as [d Hd].
        exists d.
        apply Hcorrect.
        exact Hd.
      * exact Htag.
  - eapply (go_liberty_BFS_rel
      (fun _ bfs_s => forall v d, bfs_dist v d <-> BFSP.dist bfs_s v = Some d)).
    eapply safeExec_X_subset.
    + apply Hoare_result_state.
      apply BFSA.BFS_assert_correct; assumption.
    + apply safeExec_result_state.
      exists (BFSP.bfs_init_state src).
      split; [exact I|].
      pose proof (BFSA.BFS_assert_correct
        (equiv0:=equiv0) (eq_dec:=eq_dec) g g_valid src src_valid) as HBFS.
      destruct HBFS as [_ Hnoerr].
      intro Herr.
      eapply Hnoerr; eauto.
Qed.

End GoLiberty.
