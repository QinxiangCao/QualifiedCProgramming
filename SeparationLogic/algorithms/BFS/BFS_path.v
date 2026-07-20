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

Lemma Hoare_conseq_pre {Σ A}:
  forall (P1 P2: Σ -> Prop) (c: program Σ A) (Q: A -> Σ -> Prop),
    (forall s, P1 s -> P2 s) ->
    Hoare P2 c Q ->
    Hoare P1 c Q.
Proof. intros; eapply Hoare_cons_pre; eauto. Qed.

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
	path: V -> option (list V * list E);
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

(** Path witnesses carried by BFS_path.  The vertex list and edge list are
    extended in lock-step when BFS discovers a fresh successor. *)
Inductive bfs_path_from (start: V) : list V -> list E -> V -> Prop :=
| bfs_path_from_nil :
    bfs_path_from start (start :: nil) nil start
| bfs_path_from_snoc :
    forall vs es u e v,
      bfs_path_from start vs es u ->
      step_aux g e u v ->
      bfs_path_from start (vs ++ v :: nil) (es ++ e :: nil) v.

Definition bfs_visited_path (s: St): Prop :=
  forall v d,
    s.(dist) v = Some d ->
    exists vs es,
      s.(path) v = Some (vs, es) /\
      bfs_path_from src vs es v /\
      length es = d.

Definition bfs_simple_path (s: St): Prop :=
  forall v d vs es,
    s.(dist) v = Some d ->
    s.(path) v = Some (vs, es) ->
    NoDup vs /\
    forall x, In x vs -> exists dx, s.(dist) x = Some dx.

Definition bfs_cond (s: St): Prop :=
	exists u, In u (q s).

Definition bfs_init : program St unit :=
	update' (fun _ => {|
		dist := (fun v => if eq_dec v src then Some 0 else None);
		q := src::nil;
		path := (fun v => if eq_dec v src then Some (src :: nil, nil) else None)
	|}).

Definition bfs_init_state : St := {|
  dist := (fun v => if eq_dec v src then Some 0 else None);
  q := src :: nil;
  path := (fun v => if eq_dec v src then Some (src :: nil, nil) else None)
|}.

Definition bfs_body : program St unit :=
    tail <- any (list V);;
	u <- get (fun s head => s.(q) = head :: tail);;
	d_u <- get (fun s d_u => s.(dist) u = Some d_u);;
	p_u <- get (fun s p_u => s.(path) u = Some p_u);;
	update' (fun s => {|
		dist := s.(dist);
		q := tail;
		path := s.(path)
	|});;
	tovisit <- get' (fun s v => step u v /\ s.(dist) v = None);;
	forset tovisit
		(fun v =>
      e <- get (fun _ e => step_aux g e u v);;
      update' (fun s => {|
			  dist := v !-> (Some (S (d_u))); s.(dist);
			  q := s.(q) ++ v::nil;
        path := v !-> Some (fst p_u ++ v :: nil, snd p_u ++ e :: nil); s.(path)
		  |})
		).

Definition bfs_queue_visited (s: St): Prop :=
  forall v, In v s.(q) -> exists d, s.(dist) v = Some d.

Definition bfs_queue_reachable (s: St): Prop :=
  forall v, In v s.(q) -> reachable src v.

Definition bfs_assert_inv (s: St): Prop :=
  bfs_queue_reachable s /\
  bfs_queue_visited s /\
  bfs_visited_path s /\
  bfs_simple_path s.

Definition bfs_body_assert : program St unit :=
  assertS bfs_assert_inv;; bfs_body.

(** The executable BFS program used for the ordinary correctness theorem. *)
Definition BFS : program St unit :=
	bfs_init;;
	whileP bfs_cond bfs_body.

(** The refinement-friendly variant: before each loop body execution, it
    asserts the local queue facts needed by downstream refinements: every
    queued vertex is reachable and already has a distance entry. *)
Definition BFS_assert : program St unit :=
	bfs_init;;
	whileP bfs_cond bfs_body_assert.

(** Ghost-instrumented BFS.  It has the same concrete behavior as [BFS], but
    records the states seen at loop boundaries.  The trace proof below is
    shared by both [BFS] and [BFS_assert]. *)
Definition BFS_t : programTS St unit :=
	liftG bfs_init;;
	snapshot_loop bfs_cond bfs_body.

Definition BFS_assert_t : programTS St unit :=
	liftG bfs_init;;
	snapshot_loop bfs_cond bfs_body_assert.

Lemma Gequiv_BFS:
	Gequiv BFS BFS_t.
Proof.
	unfold BFS, BFS_t.
	apply Gequiv_bind.
	- apply Gequiv_liftG.
	- intros [].
	  apply Gequiv_snapshot_loop.
Qed.

Lemma Gequiv_BFS_assert:
	Gequiv BFS_assert BFS_assert_t.
Proof.
	unfold BFS_assert, BFS_assert_t.
	apply Gequiv_bind.
	- apply Gequiv_liftG.
	- intros [].
	  apply Gequiv_snapshot_loop.
Qed.

(** Default / placeholder state: every distance is [None], queue is empty. *)
Definition St_default : St := {| dist := fun _ => None; q := nil; path := fun _ => None |}.

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
    (* Every next-layer neighbor of an already-popped current-layer vertex has
       already been placed in [qnext]. *)
    (forall u v,
      bfs_dist u d -> ~ In u qd ->
      step u v -> bfs_dist v (S d) -> In v qnext) /\
    (* Other next-layer vertices have not been discovered yet. *)
    (forall v, bfs_dist v (S d) -> ~ In v qnext -> s.(dist) v = None).

Definition BFSRelPre (n: nat) :=
  fun '(l1, l2, dmap, d) s =>
    s.(q) = l1 ++ l2 /\
	length l1 = n /\
	s.(dist) = dmap /\
	(forall v, In v l1 -> dmap v = Some d).

Definition BFSRelPost (_: nat) :=
  fun '(l1, l2, dmap, d) s =>
	exists l3,
	s.(q) = l2 ++ l3 /\
	(forall v, 
	  In v l3 <-> 
	  exists u, In u l1 /\ step u v /\ dmap v = None) /\
	(forall v, In v l3 -> s.(dist) v = Some (S d)) /\
	(forall v, ~ In v l3 -> s.(dist) v = dmap v).

Definition BFSRel := AbsRel BFSRelPre BFSRelPost.

Lemma bfs_init_state_neq_default :
  bfs_init_state <> St_default.
Proof.
  intro Heq.
  pose proof (f_equal q Heq) as Hq.
  unfold bfs_init_state, St_default in Hq.
  simpl in Hq.
  discriminate.
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

Lemma BFSRel_assoc m n s1 s2 s3:
	BFSRel m s1 s2 ->
	BFSRel n s2 s3 ->
	BFSRel (m + n) s1 s3.
Proof.
	unfold BFSRel, AbsRel, BFSRelPre, BFSRelPost.
	intros Hm Hn l Hpre.
	destruct l as [[[l1 l2] dmap] d].
	simpl in *.
	destruct Hpre as [Hq1 [Hlen1 [Hdist1 Hall1]]].

	set (l1a := firstn m l1).
	set (l1b := skipn m l1).

	assert (Hl1_split: l1 = l1a ++ l1b).
	{
		unfold l1a, l1b.
		symmetry. apply firstn_skipn.
	}

	assert (Hl1a_len: length l1a = m).
	{
		unfold l1a.
		apply firstn_length_le.
		lia.
	}

	assert (Hpre_m: BFSRelPre m (l1a, l1b ++ l2, dmap, d) s1).
	{
		unfold BFSRelPre.
		simpl.
		split.
		- rewrite Hq1, Hl1_split, app_assoc. reflexivity.
		- split.
			+ exact Hl1a_len.
			+ split.
				* exact Hdist1.
				* intros v Hin.
					apply Hall1.
					rewrite Hl1_split.
					apply in_or_app.
					left. exact Hin.
	}

	specialize (Hm (l1a, l1b ++ l2, dmap, d) Hpre_m).
	destruct Hm as [l3a [Hq2 [Hrel2 [Hset2 Hkeep2]]]].

	assert (Hpre_n: BFSRelPre n (l1b, l2 ++ l3a, dist s2, d) s2).
	{
		unfold BFSRelPre.
		simpl.
		split.
		- rewrite Hq2, app_assoc. reflexivity.
		- split.
			+ unfold l1b.
			rewrite length_skipn, Hlen1.
				lia.
			+ split.
				* reflexivity.
				* intros v Hinb.
					assert (Hin_l1: In v l1).
					{
						rewrite Hl1_split.
						apply in_or_app.
						right. exact Hinb.
					}
					assert (Hdmap_v: dmap v = Some d) by (apply Hall1; exact Hin_l1).
					assert (~ In v l3a).
					{
						intro Hin3a.
						apply Hrel2 in Hin3a.
						destruct Hin3a as [u [_ [_ Hdnone]]].
						rewrite Hdmap_v in Hdnone.
						discriminate.
					}
					rewrite Hkeep2; auto.
	}

	specialize (Hn (l1b, l2 ++ l3a, dist s2, d) Hpre_n).
	destruct Hn as [l3b [Hq3 [Hrel3 [Hset3 Hkeep3]]]].

	exists (l3a ++ l3b).
	split.
	- rewrite Hq3, app_assoc. reflexivity.
	- split.
		+ intros v; split; intro Hin.
			* apply in_app_iff in Hin.
				destruct Hin as [Hin3a | Hin3b].
				-- apply Hrel2 in Hin3a.
					 destruct Hin3a as [u [Hina [Hstep Hdnone]]].
					 exists u.
					 split.
					 ++ rewrite Hl1_split.
							apply in_or_app.
							left. exact Hina.
					 ++ split; assumption.
				-- apply Hrel3 in Hin3b.
					 destruct Hin3b as [u [Hinb [Hstep Hdist2none]]].
					 assert (Hdnone: dmap v = None).
					 {
						 destruct (classic (In v l3a)) as [Hin3a | Hnin3a].
						 - apply Hrel2 in Hin3a.
							 destruct Hin3a as [u' [_ [_ Hdnone]]].
							 exact Hdnone.
						 - rewrite Hkeep2 in Hdist2none; auto.
					 }
					 exists u.
					 split.
					 ++ rewrite Hl1_split.
							apply in_or_app.
							right. exact Hinb.
					 ++ split; assumption.
			* destruct Hin as [u [Hinu [Hstep Hdnone]]].
				rewrite Hl1_split in Hinu.
				apply in_app_iff in Hinu.
				destruct Hinu as [Hina | Hinb].
				-- apply in_app_iff.
					 left.
					 apply Hrel2.
					 exists u.
					 repeat split; assumption.
				-- destruct (classic (In v l3a)) as [Hin3a | Hnin3a].
					 ++ apply in_app_iff.
							left. exact Hin3a.
					 ++ apply in_app_iff.
							right.
							apply Hrel3.
							exists u.
							split; [exact Hinb|].
							split; [exact Hstep|].
							rewrite Hkeep2; auto.
		+ split.
			* intros v Hin.
				apply in_app_iff in Hin.
				destruct Hin as [Hin3a | Hin3b].
				-- destruct (classic (In v l3b)) as [Hin3b' | Hnin3b].
					 ++ apply Hset3. exact Hin3b'.
					 ++ rewrite Hkeep3; auto.
				-- apply Hset3. exact Hin3b.
			* intros v Hnin.
				assert (Hnin3a: ~ In v l3a).
				{
					intro Hin3a.
					apply Hnin.
					apply in_app_iff.
					left. exact Hin3a.
				}
				assert (Hnin3b: ~ In v l3b).
				{
					intro Hin3b.
					apply Hnin.
					apply in_app_iff.
					right. exact Hin3b.
				}
				rewrite Hkeep3; [| exact Hnin3b].
				rewrite Hkeep2; [reflexivity | exact Hnin3a].
Qed.

(** --------------------------------------------------------------------------
    Local body abstraction: one iteration of [bfs_body] "processes" the head
    of the queue, i.e. it corresponds to one step of BFSRel.

    We phrase this as: from any state satisfying [BFSRelPre 1 lv], executing
    [bfs_body] produces a state satisfying [BFSRelPost 1 lv], where the
    logical variable [lv] encodes the single element poped plus the remainder
    of the current queue.
    This is exactly what [snapshot_loop_AbsRel] requires.
 --------------------------------------------------------------------------- *)
Lemma bfs_body_AbsRel :
  forall lv, Hoare (BFSRelPre 1 lv) bfs_body (fun _ => BFSRelPost 1 lv).
Proof.
  intros [[[l1 l2] dmap] d].
  unfold BFSRelPre, BFSRelPost.
  destruct l1 as [|u l1'].
  - unfold Hoare.
    split; intros.
    + destruct H as [_ [Hlen _]].
      simpl in Hlen. discriminate.
    + destruct H as [_ [Hlen _]].
      simpl in Hlen. discriminate.
  - destruct l1' as [|u' l1''].
    2: {
      unfold Hoare.
      split; intros.
      + destruct H as [_ [Hlen _]].
        simpl in Hlen. discriminate.
      + destruct H as [_ [Hlen _]].
        simpl in Hlen. discriminate.
    }
    simpl.
    intro_state.
    destruct H as [Hq [Hlen [Hdist Hu]]].
    assert (Hud : dist s0 u = Some d).
    {
      rewrite Hdist.
      apply Hu.
      simpl. auto.
    }
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
    rewrite Hud in Hdu. inversion Hdu; subst d_u.
    eapply Hoare_bind.
    {
      apply Hoare_get_s.
    }
    intros p_u.
    apply Hoare_state_intro; intros st [_ Hst]; subst st.
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
            exists u.
            split; [simpl; auto |].
            rewrite Hdist in Hx.
            exact Hx. }
          { destruct Hx as [u' [Hu' [Hstep Hdnone]]].
            simpl in Hu'. destruct Hu' as [Hu' | []]. subst u'.
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
                 e <- get (fun _ e => step_aux g e u v);;
	               update'
	                 (fun s : St =>
	                    {| dist := v !-> Some (S d); dist s;
	                       q := q s ++ v :: nil;
	                       path := v !-> Some (fst p_u ++ v :: nil,
                                            snd p_u ++ e :: nil); path s |})))
         (fun (_ : unit) (s : St) =>
            I (fun v => step u v /\ dist s0 v = None) s)).
    eapply (@Hoare_forset St V I
        (fun v => step u v /\ dist s0 v = None)
	        (fun v =>
             e <- get (fun _ e => step_aux g e u v);;
	           update'
	             (fun s : St =>
	                {| dist := v !-> Some (S d); dist s;
	                   q := q s ++ v :: nil;
	                   path := v !-> Some (fst p_u ++ v :: nil,
                                      snd p_u ++ e :: nil); path s |}))).
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
      eapply Hoare_bind.
      {
        apply Hoare_get_s.
      }
      intros e0.
      apply Hoare_state_intro; intros st [_ Hst]; subst st.
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
  assert (Hpre: BFSRelPre 1 ((u :: nil), tail, dist s0, d) s0).
  {
    unfold BFSRelPre.
    simpl.
    split.
    - rewrite Hq. simpl. reflexivity.
    - split; [reflexivity |].
      split; [reflexivity |].
      intros v Hin.
      simpl in Hin.
      destruct Hin as [Hv | []].
      subst v.
      apply Hcorrect with (d' := d); [exact Hu_d | lia].
  }
  eapply Hoare_conseq with
    (P2 := BFSRelPre 1 ((u :: nil), tail, dist s0, d))
    (Q2 := fun _ => BFSRelPost 1 ((u :: nil), tail, dist s0, d)).
  - intros s Hs.
    subst s.
    exact Hpre.
  - intros _ s2 Hpost.
    unfold BFSRelPost in Hpost.
    simpl in Hpost.
    destruct Hpost as [l3 [Hq2 [Hl3 [Hset Hkeep]]]].
    assert (Hl3_one:
      forall v, In v l3 <-> step u v /\ dist s0 v = None).
    {
      intro v.
      split; intro Hv.
      - destruct (proj1 (Hl3 v) Hv) as [u0 [Hu0 [Hstep_v Hnone_v]]].
        simpl in Hu0.
        destruct Hu0 as [Hu0 | []].
        subst u0.
        split; assumption.
      - apply (proj2 (Hl3 v)).
        exists u.
        split; [simpl; auto |].
        destruct Hv as [Hstep_v Hnone_v].
        split; assumption.
    }
    unfold BFSLayerInv.
    split.
    + intros v k Hv_k Hk_le.
      destruct (classic (In v l3)) as [Hin3 | Hnin3].
      * apply Hl3_one in Hin3.
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
           apply Hl3_one in Hin3.
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
                     +++ apply Hl3_one in Hin_l3.
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
                             apply Hl3_one.
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
  - apply bfs_body_AbsRel.
Qed.

Lemma bfs_body_assert_AbsRel_nrm :
  forall lv, Hoare_nrm (BFSRelPre 1 lv) bfs_body_assert (fun _ => BFSRelPost 1 lv).
Proof.
  intros lv.
  unfold bfs_body_assert.
  apply Hoare_nrm_assertS_bind_intro.
  apply Hoare_implies_nrm.
  apply bfs_body_AbsRel.
Qed.

#[local] Instance bfs_body_safe : SnapshotBodySafe bfs_body.
Proof.
  constructor.
  unfold bfs_body.
	  apply Hoare_any_bind; intros tail.
	  eapply Hoare_bind; [apply Hoare_get|]; intros u.
	  eapply Hoare_bind; [apply Hoare_get|]; intros d_u.
	  eapply Hoare_bind; [apply Hoare_get|]; intros p_u.
	  eapply Hoare_bind; [apply Hoare_update'|]; intros [].
  eapply Hoare_bind; [apply Hoare_get'|]; intros tovisit.
  eapply Hoare_cons_pre.
  2:{
    eapply Hoare_cons_post.
    2:{
      eapply (@Hoare_forset St V (fun _ _ => True)
	        tovisit
	        (fun v : V =>
            e <- get (fun _ e => step_aux g e u v);;
	          update'
	            (fun s : St =>
	              {| dist := v !-> Some (S d_u); dist s;
	                 q := q s ++ v :: nil;
	                 path := v !-> Some (fst p_u ++ v :: nil,
                                    snd p_u ++ e :: nil); path s |}))).
      - unfold Proper, respectful; tauto.
	      - intros done a Hsub.
	        eapply Hoare_bind; [apply Hoare_get|]; intros e.
	        eapply Hoare_cons_post.
        2: apply Hoare_update'.
        intros [] s H; exact I.
    }
    intros [] s _; exact I.
  }
  intros s _; exact I.
Qed.

Lemma BFSRel_BFS_IH_step :
  forall d s1 s2,
    BFS_IH d s1 ->
    BFSRel (length s1.(q)) s1 s2 ->
    BFS_IH (S d) s2.
Proof.
  intros d s1 s2 HIH Hrel.
  unfold BFSRel, AbsRel in Hrel.
  specialize (Hrel (s1.(q), nil, s1.(dist), d)).
  assert (Hpre: BFSRelPre (length s1.(q)) (s1.(q), nil, s1.(dist), d) s1).
  {
    unfold BFSRelPre.
    simpl.
    split.
    - rewrite app_nil_r. reflexivity.
    - split.
      + reflexivity.
      + split.
        * reflexivity.
        * intros v Hin.
          destruct HIH as [Hset [_ Hq]].
          apply Hset with (d' := d).
          -- apply Hq. exact Hin.
          -- lia.
  }
  specialize (Hrel Hpre).
  unfold BFSRelPost in Hrel.
  destruct Hrel as [l3 [Hq2 [Hl3 [Hset2 Hkeep2]]]].
  destruct HIH as [Hcorrect [Hnone Hq1]].
  unfold BFS_IH.
  split.
  - intros v d' Hdist Hdle.
    destruct (Nat.eq_dec d' (S d)) as [Heq | Hneq].
    + subst d'.
      destruct (classic (In v l3)) as [Hin | Hnin].
      * apply Hset2. exact Hin.
      * exfalso.
        apply Hnin.
        apply Hl3.
        pose proof Hdist as HdistS.
        apply bfs_dist_S_pred in Hdist.
        destruct Hdist as [u [Hu Hstep]].
        exists u.
        split.
        -- apply Hq1. exact Hu.
        -- split; [exact Hstep |].
           apply Hnone.
           apply bfs_dist_not_le_lt with (d := S d); [exact HdistS | lia].
    + assert (Hd'le: d' <= d) by lia.
      rewrite Hkeep2.
      * apply Hcorrect with (d' := d'); assumption.
      * intro Hin.
        apply Hl3 in Hin.
        destruct Hin as [u [_ [_ Hnone_v]]].
        rewrite (Hcorrect v d' Hdist Hd'le) in Hnone_v.
        discriminate.
  - split.
    + intros v Hnot.
      rewrite Hkeep2.
      * apply Hnone.
        intro Hle.
        apply Hnot.
        destruct Hle as [k [Hk Hkle]].
        exists k.
        split; [exact Hk | lia].
      * intro Hin.
        apply Hl3 in Hin.
        destruct Hin as [u [Hu [Hstep Hdist_none]]].
        apply Hnot.
        apply Hq1 in Hu.
        destruct Hu as [Hpath_u Hmin_u].
        apply path_of_len_min with (n := S d).
        eapply pol_S; eauto.
    + intros v.
      rewrite Hq2.
      simpl.
      split.
      * intros Hin.
        apply Hl3 in Hin.
        destruct Hin as [u [Hu [Hstep Hdist_none]]].
        apply Hq1 in Hu.
        destruct Hu as [Hpath_u Hmin_u].
        destruct (path_of_len_min v (S d)) as [k [Hk Hkle]].
        { eapply pol_S; eauto. }
        assert (k = S d).
        {
          destruct (Nat.eq_dec k (S d)) as [Heq | Hneq]; [exact Heq |].
          assert (k <= d) by lia.
          exfalso.
          rewrite (Hcorrect v k Hk H) in Hdist_none.
          discriminate.
        }
        subst k.
        exact Hk.
      * intros Hdist.
        apply Hl3.
        pose proof Hdist as HdistS.
        apply bfs_dist_S_pred in Hdist.
        destruct Hdist as [u [Hu Hstep]].
        exists u.
        split.
        -- apply Hq1. exact Hu.
        -- split; [exact Hstep |].
           apply Hnone.
           apply bfs_dist_not_le_lt with (d := S d); [exact HdistS | lia].
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

Lemma nth_last_default :
  forall (l: list St) i d,
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

Lemma skipn_not_nil_lt :
  forall (A: Type) (l: list A) n,
    n < length l ->
    skipn n l <> nil.
Proof.
  intros A l n Hlt Hnil.
  pose proof (f_equal (@length A) Hnil) as Hlen.
  rewrite length_skipn in Hlen.
  simpl in Hlen.
  lia.
Qed.

Lemma in_firstn_In :
  forall (A: Type) n (l: list A) x,
    In x (firstn n l) -> In x l.
Proof.
  intros A n l x.
  revert n.
  induction l as [|a l IH]; intros n Hin.
  - destruct n; simpl in Hin; contradiction.
  - destruct n as [|n].
    + simpl in Hin. contradiction.
    + simpl in Hin.
      destruct Hin as [Hx | Hin].
      * left. exact Hx.
      * right. apply IH with (n := n). exact Hin.
Qed.

(** If a state [s1] already satisfies the BFS layer invariant for distance [d],
    then every vertex in its queue is a distance-[d] vertex.  Running only a
    proper prefix of that queue cannot empty the queue completely.

    The proof packages the first [k] queue vertices as the already-processed
    part [l1] and the remaining suffix as [l2].  The [BFSRel k] relation says
    that after processing [l1], the new queue is [l2] followed by newly
    discovered vertices.  Since [k < length s1.(q)], [l2] is nonempty, so the
    resulting queue is nonempty as well.

    This lemma is the small bridge used later to show that the trace index
    [i + length (q si)] cannot lie beyond the final snapshot: if it did, a
    proper prefix of a nonempty queue would still be nonempty at the final
    state, contradicting termination of the BFS loop. *)
Lemma BFSRel_queue_nonempty_prefix :
  forall d k s1 s2,
    BFS_IH d s1 ->
    k < length s1.(q) ->
    BFSRel k s1 s2 ->
    s2.(q) <> nil.
Proof.
  intros d k s1 s2 HIH Hk Hrel.
  unfold BFSRel, AbsRel in Hrel.
  set (l1 := firstn k s1.(q)).
  set (l2 := skipn k s1.(q)).
  specialize (Hrel (l1, l2, s1.(dist), d)).
  assert (Hpre: BFSRelPre k (l1, l2, s1.(dist), d) s1).
  {
    unfold BFSRelPre.
    simpl.
    split.
    - unfold l1, l2. rewrite firstn_skipn. reflexivity.
    - split.
      + unfold l1. rewrite firstn_length_le; lia.
      + split.
        * reflexivity.
        * intros v Hin.
          destruct HIH as [Hcorrect [_ Hq]].
          apply Hcorrect with (d' := d).
          -- apply Hq.
             unfold l1 in Hin.
             apply in_firstn_In in Hin.
             exact Hin.
          -- lia.
  }
  specialize (Hrel Hpre).
  unfold BFSRelPost in Hrel.
  destruct Hrel as [l3 [Hq2 _]].
  rewrite Hq2.
  intro Hnil.
  apply app_eq_nil in Hnil.
  destruct Hnil as [Hl2 _].
  apply (skipn_not_nil_lt V s1.(q) k Hk).
  unfold l2 in Hl2.
  exact Hl2.
Qed.

Lemma bfs_init_queue_visited :
  bfs_queue_visited bfs_init_state.
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
  bfs_queue_reachable bfs_init_state.
Proof.
  intros v Hin.
  unfold bfs_queue_reachable, bfs_init_state in *.
  cbn in Hin.
  destruct Hin as [Hv | []].
  subst v.
  reflexivity.
Qed.

Lemma BFSRel_queue_visited_step :
  forall s1 s2,
    bfs_queue_visited s1 ->
    bfs_cond s1 ->
    BFSRel 1 s1 s2 ->
    bfs_queue_visited s2.
Proof.
  intros s1 s2 Hvisited Hcond1 Hrel v Hin.
  unfold BFSRel, AbsRel in Hrel.
  destruct (q s1) as [|u l2] eqn:Hq1.
  {
    unfold bfs_cond in Hcond1.
    destruct Hcond1 as [x Hx].
    rewrite Hq1 in Hx.
    contradiction.
  }
  destruct (Hvisited u ltac:(rewrite Hq1; simpl; auto)) as [d Hud].
  specialize (Hrel ((u :: nil), l2, dist s1, d)).
  assert (Hpre: BFSRelPre 1 ((u :: nil), l2, dist s1, d) s1).
  {
    unfold BFSRelPre.
    split.
    - simpl. exact Hq1.
    - split.
      + reflexivity.
      + split.
        * reflexivity.
        * intros x Hinx.
          simpl in Hinx.
          destruct Hinx as [Hx | []]. subst x.
          exact Hud.
  }
  specialize (Hrel Hpre).
  unfold BFSRelPost in Hrel.
  destruct Hrel as [l3 [Hq2 [Hl3 [Hset Hkeep]]]].
  rewrite Hq2 in Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin_l2 | Hin_l3].
  - unfold bfs_queue_visited in Hvisited.
    destruct (Hvisited v) as [d0 Hd0].
    {
      rewrite Hq1.
      simpl.
      right.
      exact Hin_l2.
    }
    exists d0.
    rewrite Hkeep.
    + exact Hd0.
    + intro Hin3.
      apply Hl3 in Hin3.
      destruct Hin3 as [u0 [_ [_ Hnone]]].
      rewrite Hd0 in Hnone.
      discriminate.
  - exists (S d).
    apply Hset.
    exact Hin_l3.
Qed.

Lemma BFSRel_queue_reachable_step :
  forall s1 s2,
    bfs_queue_reachable s1 ->
    bfs_queue_visited s1 ->
    bfs_cond s1 ->
    BFSRel 1 s1 s2 ->
    bfs_queue_reachable s2.
Proof.
  intros s1 s2 Hreach Hvisited Hcond1 Hrel v Hin.
  unfold BFSRel, AbsRel in Hrel.
  destruct (q s1) as [|u l2] eqn:Hq1.
  {
    unfold bfs_cond in Hcond1.
    destruct Hcond1 as [x Hx].
    rewrite Hq1 in Hx.
    contradiction.
  }
  destruct (Hvisited u ltac:(rewrite Hq1; simpl; auto)) as [d Hud].
  specialize (Hrel ((u :: nil), l2, dist s1, d)).
  assert (Hpre: BFSRelPre 1 ((u :: nil), l2, dist s1, d) s1).
  {
    unfold BFSRelPre.
    split.
    - simpl. exact Hq1.
    - split.
      + reflexivity.
      + split.
        * reflexivity.
        * intros x Hinx.
          simpl in Hinx.
          destruct Hinx as [Hx | []]. subst x.
          exact Hud.
  }
  specialize (Hrel Hpre).
  unfold BFSRelPost in Hrel.
  destruct Hrel as [l3 [Hq2 [Hl3 _]]].
  rewrite Hq2 in Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin_l2 | Hin_l3].
  - apply Hreach.
    rewrite Hq1.
    simpl.
    right.
    exact Hin_l2.
  - apply Hl3 in Hin_l3.
    destruct Hin_l3 as [u0 [Hu0 [Hstep _]]].
    eapply reachable_step_reachable.
    + apply Hreach.
      rewrite Hq1.
      simpl.
      destruct Hu0 as [Hu0 | []].
      subst u0.
      auto.
    + exact Hstep.
Qed.

(** Pure trace fact: if a trace has the expected loop shape and adjacent
    snapshots compose according to [BFSRel], then every BFS distance layer has
    some snapshot satisfying the textbook invariant [BFS_IH].

    The proof follows the standard BFS argument.
    - For [d = 0], the first snapshot is the initialized state.
    - For [S d], start from a snapshot satisfying [BFS_IH d].  If its queue is
      empty, the next layer is vacuous.  Otherwise, jump forward by exactly the
      current queue length; [TraceAbsRel] turns that trace segment into
      [BFSRel], and [BFSRel_BFS_IH_step] advances the invariant.

    The only delicate point is proving that this jump is still inside the
    trace.  [BFSRel_queue_nonempty_prefix] rules out the contrary case: after
    processing only a proper prefix of a nonempty queue, the final state would
    still have a nonempty queue, contradicting the exit fact from
    [TraceShape]. *)
Lemma BFS_trace_IH_from_facts :
  forall s tr,
    TraceShape St_default bfs_cond (fun s => s = bfs_init_state) s tr ->
    TraceAbsRel St_default BFSRelPre BFSRelPost tr ->
    forall d, exists i,
      i < length tr /\
      BFS_IH d (nth i tr St_default).
Proof.
  intros s tr Hshape Hrel.
  destruct Hshape as [Hhd [Hlast [Hncond Hcond_prefix]]].
  assert (Htr_nonempty: tr <> nil).
  {
    intro Hnil.
    subst tr.
    simpl in Hhd.
    apply bfs_init_state_neq_default.
    symmetry.
    exact Hhd.
  }
  assert (Hlen_pos: 0 < length tr).
  {
    destruct tr; [contradiction | simpl; lia].
  }
  intro d.
  induction d as [|d IH].
  - exists 0.
    split; [lia |].
    destruct tr as [|s0 tr']; [contradiction |].
    simpl in Hhd.
    rewrite Hhd.
    apply BFS_IH_0_init.
  - destruct IH as [i [Hi_lt HIH]].
    set (si := nth i tr St_default).
    destruct (q si) as [|u qs] eqn:Hq.
    + exists i.
      split; [exact Hi_lt |].
      apply BFS_IH_empty_queue_succ with (d := d); assumption.
    + set (j := i + length (q si)).
      assert (Hq_len_pos: 0 < length (q si)).
      { rewrite Hq. simpl. lia. }
      assert (Hj_lt: j < length tr).
      {
        destruct (Nat.lt_ge_cases j (length tr)) as [Hlt | Hge];
          [exact Hlt |].
        exfalso.
        set (f := length tr - 1).
        assert (Hf_lt: f < length tr).
        { unfold f. lia. }
        assert (Hi_le_f: i <= f).
        { unfold f. lia. }
        destruct (Nat.eq_dec i f) as [Hi_eq_f | Hi_neq_f].
        - subst i.
          unfold si in Hq.
          unfold f in Hq.
          rewrite (nth_last_default tr (length tr - 1) St_default
                    Htr_nonempty eq_refl) in Hq.
          rewrite Hlast in Hq.
          apply Hncond.
          unfold bfs_cond.
          exists u.
          rewrite Hq.
          simpl.
          auto.
        - assert (Hi_f: i < f) by lia.
          assert (Hk_lt: f - i < length (q si)).
          { unfold f, j in *. lia. }
          pose proof (Hrel i f Hi_f Hf_lt) as Hrel_if.
          pose proof (BFSRel_queue_nonempty_prefix d (f - i) si
            (nth f tr St_default) HIH Hk_lt Hrel_if) as Hfinal_q.
          assert (Hnth_final: nth f tr St_default = s).
          {
            unfold f.
            rewrite (nth_last_default tr (length tr - 1) St_default
                      Htr_nonempty eq_refl).
            exact Hlast.
          }
          apply Hncond.
          unfold bfs_cond.
          destruct (q s) as [|v vs] eqn:Hqs.
          * exfalso.
            apply Hfinal_q.
            rewrite Hnth_final.
            exact Hqs.
          * exists v.
            simpl.
            auto.
      }
      exists j.
      split; [exact Hj_lt |].
      pose proof (Hrel i j ltac:(unfold j; lia) Hj_lt) as Hrel_ij.
      replace (j - i) with (length (q si)) in Hrel_ij
        by (unfold j; lia).
      apply BFSRel_BFS_IH_step with (d := d) (s1 := si);
        assumption.
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

Lemma BFS_correct_from_trace_facts :
  forall s tr,
    TraceShape St_default bfs_cond (fun s => s = bfs_init_state) s tr ->
    TraceAbsRel St_default BFSRelPre BFSRelPost tr ->
    forall v d, bfs_dist v d <-> s.(dist) v = Some d.
Proof.
  intros s tr Hshape Hrel.
  pose proof (BFS_trace_IH_from_facts s tr Hshape Hrel) as Hall.
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
  destruct finite_bfs_dist_bound as [dmax Hbound].
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

Theorem BFS_assert_trace_nrm :
  Hoare_nrm
    (fun _ => True)
    BFS_assert
    (fun _ s =>
      exists tr,
        TraceShape St_default bfs_cond (fun s => s = bfs_init_state) s tr /\
        TraceAbsRel St_default BFSRelPre BFSRelPost tr).
Proof.
  eapply Hoare_nrm_fromG with
    (c' := BFS_assert_t)
    (P' := fun '(_, tr) => tr = nil).
  - apply Gequiv_BFS_assert.
  - intros s _.
    exists (@nil St).
    reflexivity.
  - unfold BFS_assert_t.
    eapply Hoare_nrm_bind with
      (Q := fun _ '(s, tr) => s = bfs_init_state /\ tr = nil).
    + eapply Hoare_nrm_liftG'.
      intros tr.
      eapply Hoare_nrm_cons_post.
      2:{ apply Hoare_implies_nrm, Hoare_update'. }
      intros [] s [s0 [Hs Htr]].
      split.
      * unfold bfs_init_state.
        exact Hs.
      * exact Htr.
    + intros [].
      eapply Hoare_nrm_cons_post with
        (Q := fun _ x =>
          (let '(s, tr) := x in
           TraceShape St_default bfs_cond (fun s => s = bfs_init_state) s tr) /\
          (let '(_, tr) := x in
           TraceAbsRel St_default BFSRelPre BFSRelPost tr)).
      * intros _ (s, tr) [Hshape Hrel].
        exists tr.
        split; assumption.
      * eapply Hoare_nrm_conj.
        -- eapply snapshot_loop_trace_shape_nrm.
        -- eapply Hoare_nrm_cons_pre.
           2:{
             eapply snapshot_loop_AbsRel_trace_nrm.
             - apply bfs_body_assert_AbsRel_nrm.
             - intros s1 s2 s3 m n.
               apply BFSRel_assoc.
           }
           intros [s0 tr0] [_ Hnil].
           exact Hnil.
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
        TraceShape St_default bfs_cond (fun s => s = bfs_init_state) s tr /\
        TraceAbsRel St_default BFSRelPre BFSRelPost tr).
  - intros s Hs. exact Hs.
  - intros _ s [tr [Hshape Hrel]].
    eapply BFS_correct_from_trace_facts; eauto.
  - apply BFS_assert_trace_nrm.
Qed.

Lemma bfs_init_visited_path :
  bfs_visited_path bfs_init_state.
Proof.
  unfold bfs_visited_path, bfs_init_state.
  simpl.
  intros v d Hdist.
  destruct (eq_dec v src) as [Heq | Hneq].
  - inversion Hdist; subst d.
    destruct Heq.
    exists (v :: nil), (@nil E).
    split.
    + destruct (eq_dec v v) as [_ | Hcontra]; [reflexivity|].
      exfalso; apply Hcontra; reflexivity.
    + split; [constructor|reflexivity].
  - discriminate.
Qed.

Lemma bfs_init_simple_path :
  bfs_simple_path bfs_init_state.
Proof.
  unfold bfs_simple_path, bfs_init_state.
  simpl.
  intros v d vs es Hdist Hpath.
  destruct (eq_dec v src) as [Heq | Hneq].
  - inversion Hdist; subst d.
    inversion Hpath; subst vs es.
    split.
    + constructor; [intro H; contradiction|constructor].
    + intros x Hin.
      simpl in Hin.
      destruct Hin as [Hx | []].
      subst x.
      exists 0%nat.
      destruct (eq_dec src src) as [_ | Hcontra]; [reflexivity|].
      exfalso; apply Hcontra; reflexivity.
  - discriminate.
Qed.

Lemma bfs_visited_path_update :
  forall s u d p a e,
    bfs_visited_path s ->
    s.(dist) u = Some d ->
    s.(path) u = Some p ->
    step_aux g e u a ->
    bfs_visited_path
      {| dist := a !-> Some (S d); s.(dist);
         q := s.(q) ++ a :: nil;
         path := a !-> Some (fst p ++ a :: nil, snd p ++ e :: nil);
                   s.(path) |}.
Proof.
  intros s u d p a e Hinv Hdu Hpu Hstep x dx Hdistx.
  simpl in *.
  unfold t_set in *.
  destruct (equiv_dec a x) as [Hax | Hax].
  - destruct Hax.
    inversion Hdistx; subst dx.
    destruct (Hinv u d Hdu) as [vs [es [Hpathu [Hvalid Hlen]]]].
    rewrite Hpu in Hpathu.
    inversion Hpathu; subst p.
    exists (vs ++ a :: nil), (es ++ e :: nil).
    split.
    + destruct (equiv_dec a a) as [_ | Hcontra]; [reflexivity|].
      exfalso; apply Hcontra; reflexivity.
    + split.
      * apply bfs_path_from_snoc with (u := u); assumption.
      * rewrite length_app. simpl. lia.
  - destruct (Hinv x dx Hdistx) as [vs [es [Hpathx [Hvalid Hlen]]]].
    exists vs, es.
    split.
    + destruct (equiv_dec a x) as [Heq | _]; [contradiction|exact Hpathx].
    + split; assumption.
Qed.

Lemma bfs_body_preserves_visited_path :
  Hoare
    bfs_visited_path
    bfs_body
    (fun _ => bfs_visited_path).
Proof.
  unfold bfs_body.
  apply Hoare_any_bind; intros tail.
  eapply Hoare_bind.
  { apply Hoare_get_s. }
  intros u.
  apply Hoare_state_intro; intros s0 [Hq Hinv0].
  eapply Hoare_bind.
  { apply Hoare_get_s. }
  intros d_u.
  apply Hoare_state_intro; intros s1 [Hdu Hs1]; subst s1.
  eapply Hoare_bind.
  { apply Hoare_get_s. }
  intros p_u.
  apply Hoare_state_intro; intros s1 [Hpu Hs1]; subst s1.
  destruct (Hinv0 u d_u Hdu) as [vs [es [Hpathu [Hvalidu Hlenu]]]].
  rewrite Hpu in Hpathu.
  inversion Hpathu; subst p_u.
  eapply Hoare_bind.
  { apply Hoare_update'. }
  intros [].
  eapply Hoare_bind.
  { apply Hoare_get'. }
  intros tovisit.
  apply Hoare_state_intro.
  intros s2 [Htovisit Hpre2].
  destruct Hpre2 as [sold [Hs2 Hinv_sold]].
  subst s2 tovisit.
  subst sold.
  simpl in *.
  set (PathP := fun (_done: V -> Prop) (s: St) => bfs_visited_path s).
  eapply Hoare_conseq with
    (P2 := PathP (fun _ : V => False))
    (Q2 := fun _ s => PathP (fun v => step u v /\ dist s0 v = None) s).
  - intros s Hs.
    subst s.
    exact Hinv0.
  - intros _ s Hs. exact Hs.
  - change
      (Hoare (PathP (fun _ : V => False))
         (forset (fun v : V => step u v /\ dist s0 v = None)
            (fun v : V =>
               e <- get (fun _ e => step_aux g e u v);;
               update'
                 (fun s : St =>
                    {| dist := v !-> Some (S d_u); dist s;
                       q := q s ++ v :: nil;
                       path := v !-> Some (vs ++ v :: nil, es ++ e :: nil);
                                 path s |})))
         (fun _ s => PathP (fun v => step u v /\ dist s0 v = None) s)).
    eapply (@Hoare_forset St V PathP
      (fun v : V => step u v /\ dist s0 v = None)
      (fun v : V =>
         e <- get (fun _ e => step_aux g e u v);;
         update'
           (fun s : St =>
              {| dist := v !-> Some (S d_u); dist s;
                 q := q s ++ v :: nil;
                 path := v !-> Some (vs ++ v :: nil, es ++ e :: nil);
                           path s |}))).
    + intros done1 done2 Heq s3 s4 Hs. subst s4. reflexivity.
    + intros done a Hsub.
      eapply Hoare_bind.
      * apply Hoare_get_s.
      * intros e.
        apply Hoare_state_intro; intros s3 [Hedge [Hpathinv [Ha _]]].
	        eapply Hoare_conseq_post.
	        2:{ apply Hoare_update'. }
	        intros [] s4 [s_before [Hs4 Hinv_before]].
	        subst s4 s_before.
          unfold bfs_visited_path in *.
          intros x dx Hdistx.
          simpl in *.
          unfold t_set in *.
          destruct (equiv_dec a x) as [Hax | Hax].
          -- destruct Hax.
             inversion Hdistx; subst dx.
             exists (vs ++ a :: nil), (es ++ e :: nil).
             split.
             ++ destruct (equiv_dec a a) as [_ | Hcontra]; [reflexivity|].
                exfalso; apply Hcontra; reflexivity.
             ++ split.
                ** apply bfs_path_from_snoc with (u := u); assumption.
                ** rewrite length_app. simpl. lia.
          -- destruct (Hpathinv x dx Hdistx) as [vsx [esx [Hpx [Hvalidx Hlenx]]]].
             exists vsx, esx.
             split.
             ++ destruct (equiv_dec a x) as [Heq | _]; [contradiction|exact Hpx].
             ++ split; assumption.
Qed.

Lemma bfs_simple_path_update :
  forall s u d vs es a e,
    bfs_simple_path s ->
    s.(dist) u = Some d ->
    s.(path) u = Some (vs, es) ->
    s.(dist) a = None ->
    bfs_simple_path
      {| dist := a !-> Some (S d); s.(dist);
         q := s.(q) ++ a :: nil;
         path := a !-> Some (vs ++ a :: nil, es ++ e :: nil);
                   s.(path) |}.
Proof.
  intros s u d vs es a e Hsimple Hdu Hpu Hnone x dx vsx esx Hdistx Hpathx.
  simpl in *.
  unfold t_set in *.
  destruct (equiv_dec a x) as [Hax | Hax].
  - destruct Hax.
    inversion Hdistx; subst dx.
    destruct (equiv_dec a a) as [_ | Hcontra]; [|exfalso; apply Hcontra; reflexivity].
    inversion Hpathx; subst vsx esx.
    destruct (Hsimple u d vs es Hdu Hpu) as [Hnodup Hseen].
    assert (Hnotin: ~ In a vs).
    {
      intro Hin.
      destruct (Hseen a Hin) as [dx Hdx].
      rewrite Hnone in Hdx.
      discriminate.
    }
    split.
    + apply NoDup_app.
      repeat split.
      * exact Hnodup.
      * constructor; [intro H; contradiction|constructor].
      * intros y Hy Hin_tail.
        simpl in Hin_tail.
        destruct Hin_tail as [Hyx | []].
        subst y.
        contradiction.
    + intros y Hin.
      apply in_app_iff in Hin.
      destruct Hin as [Hin | Hin].
      * destruct (Hseen y Hin) as [dy Hdy].
        exists dy.
        destruct (equiv_dec a y) as [Hxy | Hxy].
        -- destruct Hxy.
           rewrite Hnone in Hdy.
           discriminate.
        -- exact Hdy.
      * simpl in Hin.
        destruct Hin as [Hy | []].
        subst y.
        exists (S d).
        destruct (equiv_dec a a) as [_ | Hcontra]; [reflexivity|].
        exfalso; apply Hcontra; reflexivity.
  - destruct (equiv_dec a x) as [Heq | _]; [contradiction|].
    destruct (Hsimple x dx vsx esx Hdistx Hpathx) as [Hnodup Hseen].
    split; [exact Hnodup|].
    intros y Hin.
    destruct (Hseen y Hin) as [dy Hdy].
    exists dy.
    destruct (equiv_dec a y) as [Hay | Hay].
    + destruct Hay.
      rewrite Hnone in Hdy.
      discriminate.
    + exact Hdy.
Qed.

Lemma bfs_body_preserves_simple_path :
  Hoare
    (fun s => bfs_simple_path s /\ bfs_visited_path s)
    bfs_body
    (fun _ => bfs_simple_path).
Proof.
  unfold bfs_body.
  apply Hoare_any_bind; intros tail.
  eapply Hoare_bind.
  { apply Hoare_get_s. }
  intros u.
  apply Hoare_state_intro; intros s0 [Hq [Hsimple0 Hpaths0]].
  eapply Hoare_bind.
  { apply Hoare_get_s. }
  intros d_u.
  apply Hoare_state_intro; intros s1 [Hdu Hs1]; subst s1.
  eapply Hoare_bind.
  { apply Hoare_get_s. }
  intros p_u.
  apply Hoare_state_intro; intros s1 [Hpu Hs1]; subst s1.
  destruct p_u as [vs es].
  eapply Hoare_bind.
  { apply Hoare_update'. }
  intros [].
  eapply Hoare_bind.
  { apply Hoare_get'. }
  intros tovisit.
  apply Hoare_state_intro.
  intros s2 [Htovisit Hpre2].
  destruct Hpre2 as [sold [Hs2 Hsold]].
  subst s2 tovisit.
  subst sold.
  simpl in *.
  set (PathP := fun (done: V -> Prop) (s: St) =>
    bfs_simple_path s /\
    dist s u = Some d_u /\
    path s u = Some (vs, es) /\
    forall x, ~ done x -> dist s x = dist s0 x).
  eapply Hoare_conseq with
    (P2 := PathP (fun _ : V => False))
    (Q2 := fun _ s => PathP (fun v => step u v /\ dist s0 v = None) s).
  - intros s Hs.
    subst s.
    split; [exact Hsimple0|].
    split; [exact Hdu|].
    split; [exact Hpu|].
    intros x _. reflexivity.
  - intros _ s Hs. exact (proj1 Hs).
  - change
      (Hoare (PathP (fun _ : V => False))
         (forset (fun v : V => step u v /\ dist s0 v = None)
            (fun v : V =>
               e <- get (fun _ e => step_aux g e u v);;
               update'
                 (fun s : St =>
                    {| dist := v !-> Some (S d_u); dist s;
                       q := q s ++ v :: nil;
                       path := v !-> Some (vs ++ v :: nil, es ++ e :: nil);
                                 path s |})))
         (fun _ s => PathP (fun v => step u v /\ dist s0 v = None) s)).
    eapply (@Hoare_forset St V PathP
      (fun v : V => step u v /\ dist s0 v = None)
      (fun v : V =>
         e <- get (fun _ e => step_aux g e u v);;
         update'
           (fun s : St =>
              {| dist := v !-> Some (S d_u); dist s;
                 q := q s ++ v :: nil;
                 path := v !-> Some (vs ++ v :: nil, es ++ e :: nil);
                           path s |}))).
	    + intros done1 done2 Heq s3 s4 Hs.
	      subst s4.
	      unfold PathP in *.
	      split.
        -- intros [Hsimple [HduP [HpuP Hkeep]]].
           split; [exact Hsimple|].
           split; [exact HduP|].
           split; [exact HpuP|].
           intros x Hnot.
           apply Hkeep.
           intro Hdone1.
           apply Hnot.
           apply Heq.
           exact Hdone1.
        -- intros [Hsimple [HduP [HpuP Hkeep]]].
           split; [exact Hsimple|].
           split; [exact HduP|].
           split; [exact HpuP|].
           intros x Hnot.
           apply Hkeep.
           intro Hdone2.
           apply Hnot.
           apply Heq.
           exact Hdone2.
    + intros done a Hsub.
      eapply Hoare_bind.
      * apply Hoare_get_s.
      * intros e.
        apply Hoare_state_intro; intros s3 [_ [HpathP [Ha Hnotdone]]].
        destruct HpathP as [Hsimple [Hdu_cur [Hpu_cur Hkeep]]].
        assert (Hnone_cur: dist s3 a = None).
        {
          rewrite Hkeep.
          - exact (proj2 Ha).
          - exact Hnotdone.
        }
        eapply Hoare_conseq_post.
        2:{ apply Hoare_update'. }
        intros [] s4 [s_before [Hs4 Hsimple_before]].
        subst s4 s_before.
        split.
        -- eapply bfs_simple_path_update; eauto.
        -- split.
           ++ simpl.
              unfold t_set.
              destruct (equiv_dec a u) as [Hau | Hau].
              ** destruct Hau.
                 rewrite Hkeep in Hdu_cur by exact Hnotdone.
                 rewrite (proj2 Ha) in Hdu_cur.
                 discriminate.
              ** exact Hdu_cur.
           ++ split.
              ** simpl.
                 unfold t_set.
                 destruct (equiv_dec a u) as [Hau | Hau].
                 --- destruct Hau.
                     rewrite Hkeep in Hdu_cur by exact Hnotdone.
                     rewrite (proj2 Ha) in Hdu_cur.
                     discriminate.
                 --- exact Hpu_cur.
              ** intros x Hnot.
                 simpl.
                 unfold t_set.
                 destruct (equiv_dec a x) as [Hax | Hax].
                 --- destruct Hax.
                     exfalso.
                     apply Hnot.
                     sets_unfold.
                     right.
                     reflexivity.
                 --- apply Hkeep.
                     intro Hdone.
                     apply Hnot.
                     sets_unfold.
                     left.
                     exact Hdone.
Qed.

Lemma bfs_body_preserves_queue_assert_inv :
  Hoare
    (fun s => bfs_cond s /\ bfs_queue_reachable s /\ bfs_queue_visited s)
    bfs_body
    (fun _ s => bfs_queue_reachable s /\ bfs_queue_visited s).
Proof.
  eapply Hoare_spec_derivation
    with (SpecP := BFSRelPre 1) (SpecQ := fun lv _ s => BFSRelPost 1 lv s).
  - apply bfs_body_AbsRel.
  - intros s [Hcond [_ Hvisited]].
    destruct (q s) as [|u tail] eqn:Hq.
    {
      unfold bfs_cond in Hcond.
      destruct Hcond as [x Hx].
      rewrite Hq in Hx.
      contradiction.
    }
    destruct (Hvisited u ltac:(rewrite Hq; simpl; auto)) as [d Hd].
    exists ((u :: nil, tail, dist s, d)).
    unfold BFSRelPre.
    split.
    + simpl. exact Hq.
    + split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- intros x Hinx.
           simpl in Hinx.
           destruct Hinx as [Hx | []].
           subst x.
           exact Hd.
  - intros s0 [] s1 [Hcond [Hreach Hvisited]] Hall.
    assert (Hrel: BFSRel 1 s0 s1).
    {
      unfold BFSRel, AbsRel.
      exact Hall.
    }
    split.
    + eapply BFSRel_queue_reachable_step; eauto.
    + eapply BFSRel_queue_visited_step; eauto.
Qed.

Lemma bfs_body_preserves_assert_inv :
  Hoare
    (fun s => bfs_cond s /\ bfs_assert_inv s)
    bfs_body
    (fun _ => bfs_assert_inv).
Proof.
  eapply Hoare_conseq_post.
  2:{
    eapply Hoare_conj.
	    - eapply Hoare_cons_pre.
	      2:{ apply bfs_body_preserves_queue_assert_inv. }
	      intros s [Hcond [Hreach [Hvisited _]]].
	      repeat split; assumption.
	    - eapply Hoare_conj.
        + eapply Hoare_cons_pre.
	        2:{ apply bfs_body_preserves_visited_path. }
	        intros s [_ [_ [_ [Hpath _]]]].
	        exact Hpath.
        + eapply Hoare_cons_pre.
	        2:{ apply bfs_body_preserves_simple_path. }
	        intros s [_ [_ [_ [Hpath Hsimple]]]].
	        split; assumption.
	  }
	  intros [] s [[Hreach Hvisited] [Hpath Hsimple]].
    split; [exact Hreach|].
    split; [exact Hvisited|].
    split; assumption.
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
	    + split.
	      * apply bfs_init_queue_visited.
	      * split.
          -- apply bfs_init_visited_path.
          -- apply bfs_init_simple_path.
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

Theorem BFS_assert_inv_correct:
  Hoare
    (fun _ => True)
    BFS_assert
    (fun _ s => bfs_assert_inv s).
Proof.
  unfold BFS_assert.
  eapply Hoare_bind with (Q := fun _ s => bfs_assert_inv s).
  - eapply Hoare_cons_post.
    2:{ apply Hoare_update'. }
    intros [] s [s0 [Hs _]].
    subst s.
    split.
    + apply bfs_init_queue_reachable.
    + split.
      * apply bfs_init_queue_visited.
      * split.
        -- apply bfs_init_visited_path.
        -- apply bfs_init_simple_path.
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
    intros _ s [Hinv _].
    exact Hinv.
Qed.

Theorem BFS_assert_correct_full:
  Hoare
    (fun _ => True)
    BFS_assert
    (fun _ s =>
      (forall v d, bfs_dist v d <-> s.(dist) v = Some d) /\
      bfs_visited_path s /\
      bfs_simple_path s).
Proof.
  eapply Hoare_conseq_post.
  2:{
    eapply Hoare_conj.
    - apply BFS_assert_correct.
    - apply BFS_assert_inv_correct.
  }
  intros [] s [Hdist [_ [_ [Hpath Hsimple]]]].
  split; [exact Hdist|].
  split; assumption.
Qed.

Theorem BFS_path_witness_correct:
  Hoare
    (fun _ => True)
    BFS
    (fun _ s => bfs_visited_path s).
Proof.
  unfold BFS, bfs_init.
  eapply Hoare_bind with (Q := fun _ s => bfs_visited_path s).
  - eapply Hoare_conseq_post.
	    2:{ apply Hoare_update'. }
	    intros [] s [s0 [Hs _]].
	    subst s.
      unfold bfs_visited_path.
      simpl.
      intros v d Hdist.
      destruct (eq_dec v src) as [Heq | Hneq].
      * inversion Hdist; subst d.
        destruct Heq.
        exists (v :: nil), (@nil E).
        split.
        -- destruct (eq_dec v v) as [_ | Hcontra]; [reflexivity|].
           exfalso; apply Hcontra; reflexivity.
        -- split; [constructor|reflexivity].
      * discriminate.
  - intros [].
    eapply Hoare_conseq_post.
    2:{
      eapply Hoare_whileP with (P := bfs_visited_path).
      eapply Hoare_cons_pre.
      2:{ apply bfs_body_preserves_visited_path. }
      intros s [_ Hpath].
      exact Hpath.
    }
    intros [] s [Hpath _].
    exact Hpath.
Qed.

Theorem BFS_correct_with_path:
  Hoare
    (fun _ => True)
    BFS
    (fun _ s =>
      (forall v d, bfs_dist v d <-> s.(dist) v = Some d) /\
      bfs_visited_path s).
Proof.
  eapply Hoare_conseq_post.
  2:{
    eapply Hoare_conj.
    - apply BFS_correct.
    - apply BFS_path_witness_correct.
  }
  intros [] s [Hdist Hpath].
  split; assumption.
Qed.

End BFS.
