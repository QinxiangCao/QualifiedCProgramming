From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.Applications_human.minisat Require Import solver_qcp_shared_semantics.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.

(** * S10 -- concrete pure-state consistency witnesses.

    These are ghost consistency and semantic witnesses; they do not claim API
    execution reachability or construct a spatial heap. *)


(** ** Witness 0 : the pre-solve state.                                  *)


Definition w0_n : Z := 2.

Definition w0_F : cnf := [[Pos 0; Pos 1]].

(** The clause object: packed literals [0 = Pos 0] and [2 = Pos 1]. *)
Definition w0_obj : clause_obj :=
  {| co_lits := [0; 2]; co_learnt := false |}.

Definition w0_core : mtrail :=
  {| mt_assigns := [0; 0];
     mt_levels  := [0; 0];
     mt_trail   := [];
     mt_lim     := [];
     mt_qhead   := 0 |}.

Definition w0 : msolver := {|
  ms_size           := 2;
  ms_cap            := 2;
  ms_qtail          := 0;
  ms_capacity_pending_qhead := 0;
  ms_capacity_root_propagation_pending := 0;
  ms_core           := w0_core;
  ms_root_level     := 0;
  ms_reason_words   := [0; 0];
  ms_reason_of      := fun _ => None;
  ms_prob           := [(8, w0_obj)];
  ms_learnt         := [];
  ms_binary         := 16;
  ms_binary_lits    := [0; 0];
  (* binary clause: [wlists[~0] = wlists[1]] holds [tag_of_lit 2 = 5] and
     [wlists[~2] = wlists[3]] holds [tag_of_lit 0 = 1]. *)
  ms_wm             := [[]; [5]; []; [1]];
  ms_activity       := [msat_fp64_zero; msat_fp64_zero];
  ms_orderpos       := [0; 1];
  ms_order          := [0; 1];
  ms_model          := [0; 0];
  ms_tags           := [0; 0];
  ms_tagged         := [];
  ms_stack          := [];
  ms_var_inc        := msat_fp64_zero;
  ms_var_decay      := msat_fp64_zero;
  ms_cla_inc        := msat_fp32_zero;
  ms_cla_decay      := msat_fp32_zero;
  ms_random_seed    := msat_fp64_zero;
  ms_progress       := msat_fp64_zero;
  ms_simpdb_assigns := 0;
  ms_simpdb_props   := 0;
  ms_verbosity      := 0;
  ms_stats          := [0;0;0;0;0;0;0;0;0;0;0]
|}.

Lemma w0_denote_prob : db_clauses (ms_prob w0) = [[Pos 0; Pos 1]].
Proof. vm_compute. reflexivity. Qed.

Lemma w0_unassigned : forall x b, mt_pv w0_core x = Some b -> False.
Proof.
  intros x b H. unfold mt_pv in H.
  destruct (0 <=? x) eqn:E; [|discriminate].
  apply Z.leb_le in E.
  assert (Hz : Znth x (mt_assigns w0_core) 0 = 0).
  { destruct (Z_lt_le_dec x 2) as [Hlt|Hge].
    - assert (Hx : x = 0 \/ x = 1) by lia.
      destruct Hx as [->| ->]; reflexivity.
    - apply znth_out_of_bounds; [lia|].
      assert (HL : Zlength (mt_assigns w0_core) = 2) by reflexivity. lia. }
  unfold assigns_pv, assigns_val in H. rewrite Hz in H.
  vm_compute in H. discriminate.
Qed.

Lemma w0_trail_len : Zlength (mt_trail w0_core) = 0.
Proof. reflexivity. Qed.

Lemma w0_trail_wf : mtrail_wf w0_n w0_core.
Proof.
  pose proof w0_trail_len as HT.
  assert (HQ : mt_qhead w0_core = 0) by reflexivity.
  constructor.
  - unfold w0_n. lia.
  - reflexivity.
  - reflexivity.
  - do 2 (constructor; [unfold lbool_cell; lia|]). constructor.
  - lia.
  - unfold w0_n. lia.
  - constructor.
  - constructor.
  - constructor.
  - exact I.
  - constructor.
  - intros i Hi. lia.
  - intros v Hv. unfold w0_n in Hv.
    assert (Hx : v = 0 \/ v = 1) by lia.
    split.
    + intro H. exfalso. destruct Hx as [->| ->]; apply H; reflexivity.
    + intro H. simpl in H. contradiction.
Qed.

Lemma w0_stable : stable_view (msolver_view w0_n w0).
Proof.
  assert (HC : current_level (msolver_view w0_n w0) = 0) by reflexivity.
  split.
  - intros x b H. exfalso. exact (w0_unassigned x b H).
  - split; [|split].
    + lia.
    + intros x b d H _. exfalso. exact (w0_unassigned x b H).
    + intros d Hd. lia.
Qed.

Lemma w0_db_wf : db_wf w0_n (msolver_db w0).
Proof.
  unfold db_wf, msolver_db. simpl. split; [|split].
  - constructor; [simpl; tauto | constructor].
  - constructor; [simpl; split; [lia|reflexivity] | constructor].
  - constructor; [|constructor].
    simpl. unfold obj_wf. simpl. split; [|split].
    + reflexivity.
    + do 2 (constructor; [unfold lit_wf_c, w0_n; lia|]). constructor.
    + vm_compute. msat_nodup.
Qed.

Lemma w0_wmap : wmap_exact w0_n (msolver_db w0) (ms_wm w0).
Proof.
  split; [reflexivity|].
  intros l Hl. unfold w0_n in Hl.
  assert (Hc : l = 0 \/ l = 1 \/ l = 2 \/ l = 3) by lia.
  destruct Hc as [->|[->|[->| ->]]]; vm_compute; apply Permutation_refl.
Qed.

Lemma w0_heap_eq :
  msolver_heap w0 = {| mh_heap := [0; 1]; mh_orderpos := [0; 1] |}.
Proof. reflexivity. Qed.

Lemma w0_heap_wf : heap_wf w0_n (msolver_heap w0).
Proof.
  rewrite w0_heap_eq. unfold heap_wf, w0_n. simpl mh_heap. simpl mh_orderpos.
  split; [|split; [|split; [|split]]].
  - reflexivity.
  - msat_nodup.
  - do 2 (constructor; [lia|]). constructor.
  - intros v Hv.
    assert (Hx : v = 0 \/ v = 1) by lia.
    assert (EL : Zlength [0; 1] = 2) by reflexivity.
    assert (E0 : Znth 0 [0; 1] (-1) = 0) by reflexivity.
    assert (E1 : Znth 1 [0; 1] (-1) = 1) by reflexivity.
    destruct Hx as [-> | ->]; right; (split; [lia | reflexivity]).
  - intros i Hi.
    assert (EL : Zlength [0; 1] = 2) by reflexivity.
    assert (Hx : i = 0 \/ i = 1) by lia.
    destruct Hx as [->| ->]; reflexivity.
Qed.

Example w0_weak : msolver_inv_weak w0_n w0_F [] [] w0.
Proof.
  constructor.
  - reflexivity.
  - unfold w0_n. lia.
  - unfold solver_shape. simpl. unfold w0_n. repeat split; try reflexivity; try lia; try (right; reflexivity).
  - split; [unfold w0_n; lia|].
    constructor; [|constructor].
    do 2 (constructor; [unfold literal_wf, var_in_range, w0_n; simpl; lia|]).
    constructor.
  - constructor.
  - exact w0_trail_wf.
  - assert (E : Zlength (mt_lim (ms_core w0)) = 0) by reflexivity.
    unfold w0_n. lia.
  - assert (E : Zlength (mt_lim (ms_core w0)) = 0) by reflexivity.
    assert (E' : ms_root_level w0 = 0) by reflexivity. lia.
  - reflexivity.
  - apply incl_refl.
  - constructor.
  - exact w0_stable.
  - intros x c H. vm_compute in H. discriminate.
  - intros x c H. vm_compute in H. discriminate.
  - intros i l Hi Hl.
    assert (E : Zlength (mt_trail (ms_core w0)) = 0) by reflexivity. lia.
  - exact w0_db_wf.
  - unfold db_matches_cnf. rewrite w0_denote_prob.
    constructor; [|constructor].
    exists [Pos 0; Pos 1]. split; [left; reflexivity | apply Permutation_refl].
  - unfold db_implied. simpl. constructor.
  - intros c Hc. vm_compute in Hc. destruct Hc as [<-|[]].
    left. exists [Pos 0; Pos 1]. split.
    + rewrite w0_denote_prob. left. reflexivity.
    + apply Permutation_refl.
  - unfold learnt_db. simpl. constructor.
  - unfold prob_db. simpl. repeat constructor.
  - vm_compute. intros [H|[]]. lia.
  - intros v Hv. unfold w0_n in Hv.
    assert (Hx : v = 0 \/ v = 1) by lia.
    destruct Hx as [->| ->]; reflexivity.
  - intros v co Hv _ Hnz _. exfalso.
    assert (ES : ms_size w0 = 2) by reflexivity.
    assert (Hx : v = 0 \/ v = 1) by lia.
    destruct Hx as [->| ->]; apply Hnz; reflexivity.
  - intros v Hv Ht. exfalso.
    assert (ES : ms_size w0 = 2) by reflexivity.
    assert (Hx : v = 0 \/ v = 1) by lia.
    destruct Hx as [->| ->]; vm_compute in Ht; discriminate.
  - exact w0_wmap.
  - unfold solver_tags_clear, w0. simpl. repeat constructor.
  - exact w0_heap_wf.
  - exact msat_fp32_zero_nonnegative.
  - unfold msolver_seed_ok. apply msat_fp64_zero_finite.
Qed.

Example w0_inv : msolver_inv w0_n w0_F [] [] w0.
Proof.
  constructor.
  - exact w0_weak.
  - (* prop_level: no decision levels yet *)
    unfold prop_level.
    assert (EL : mt_lim (ms_core w0) = []) by reflexivity.
    rewrite EL. constructor.
  - apply minisat_watch_frontier_before_first_dequeue. reflexivity.
  - intros v Hv Hop. exfalso.
    unfold w0_n in Hv. assert (Hx : v = 0 \/ v = 1) by lia.
    destruct Hx as [->| ->]; vm_compute in Hop; discriminate.
  - unfold current_reasonless_earliest, w0, w0_core. simpl.
    intros d Hrange. change (0 < d <= 0) in Hrange. lia.
Qed.

(** ** The tagged-reason shape.                                         *)


(** A tagged reason denotes the implied literal together with the negation of
    its propagator.  In particular, the tag variable need not be the implied
    variable. *)
Theorem inv_tagged_reason_shape : forall n F A_arr A_inst M v b,
  msolver_inv n F A_arr A_inst M ->
  0 <= v < n ->
  assignment (msolver_view n M) v = Some b ->
  is_tag (Znth v (ms_reason_words M) 0) = true ->
  ms_reason_of M v
  = Some [satisfying_literal v b;
          literal_neg (lit_denote (tag_lit (Znth v (ms_reason_words M) 0)))].
Proof.
  intros n F A_arr A_inst M v b Hinv Hv Ha Htag.
  assert (Hrw : reason_word_ok (ms_core M) v (msolver_db M)
                  (Znth v (ms_reason_words M) 0) (ms_reason_of M v))
    by (apply (msi_reasons_mem Hinv); exact Hv).
  assert (Hw0 : (Znth v (ms_reason_words M) 0 =? 0) = false).
  { apply Z.eqb_neq. intro Hz. unfold is_tag in Htag. rewrite Hz in Htag.
    discriminate. }
  unfold reason_word_ok in Hrw. rewrite Hw0, Htag in Hrw.
  destruct Hrw as [_ Hrw].
  rewrite Hrw.
  rewrite msolver_view_assignment in Ha.
  rewrite (trail_lit_of_denote (ms_core M) v b ltac:(lia) Ha).
  reflexivity.
Qed.


(** ** Witness 2 : a tagged reason word, and a tagged watcher whose      *)
(**    literal sits at a STRICTLY LOWER level.                           *)


(** [n = 3], [F = {{x2}, {~x0,x2}, {~x0,x1}}].  The level-0 unit [x2]
    remains true while propagation of the level-1 decision [x0] retains its
    binary watcher and enqueues [x1] with a tagged reason.  Thus the witness
    simultaneously exercises a lower-level satisfied watcher and a tag whose
    variable differs from the implied variable.  The final queue is drained,
    so the SAT endgame applies. *)

Definition w2_n : Z := 3.

Definition w2_F : cnf := [[Pos 2]; [Neg 0; Pos 2]; [Neg 0; Pos 1]].

(** {~x0, x2} and {~x0, x1}, packed. *)
Definition w2_c1 : clause_obj := {| co_lits := [1; 4]; co_learnt := false |}.

Definition w2_c2 : clause_obj := {| co_lits := [1; 2]; co_learnt := false |}.

Definition w2_core : mtrail :=
  {| mt_assigns := [1; 1; 1];
     mt_levels  := [1; 1; 0];
     mt_trail   := [4; 0; 2];
     mt_lim     := [1];
     mt_qhead   := 3 |}.

(** The tagged arm decodes [reasons[1] = 1] to:
    {x1, ~x0} -- the enqueued literal together with the NEGATION of the
    propagator in [solver_propagate]. *)
Definition w2_reason_clause : clause := [Pos 1; Neg 0].

Definition w2 : msolver := {|
  ms_size           := 3;
  ms_cap            := 3;
  ms_qtail          := 3;
  ms_capacity_pending_qhead := 0;
  ms_capacity_root_propagation_pending := 0;
  ms_core           := w2_core;
  ms_root_level     := 0;
  (* reasons[1] = clause_from_lit(0) = tag_of_lit 0 = 1 *)
  ms_reason_words   := [0; 1; 0];
  ms_reason_of      := fun v => if v =? 1 then Some w2_reason_clause else None;
  ms_prob           := [(8, w2_c1); (24, w2_c2)];
  ms_learnt         := [];
  ms_binary         := 16;
  ms_binary_lits    := [0; 0];
  (* both objects are binary, so both are watched by TAGS:
     wlists[~1] = wlists[0] holds tag_of_lit 4 = 9 (from c1) and
                              tag_of_lit 2 = 5 (from c2);
     wlists[~4] = wlists[5] and wlists[~2] = wlists[3] hold tag_of_lit 1 = 3 *)
  ms_wm             := [[9; 5]; []; []; [3]; []; [3]];
  ms_activity       := [msat_fp64_zero; msat_fp64_zero; msat_fp64_zero];
  ms_orderpos       := [-1; -1; -1];
  ms_order          := [];
  ms_model          := [1; 1; 1];
  ms_tags           := [0; 0; 0];
  ms_tagged         := [];
  ms_stack          := [];
  ms_var_inc        := msat_fp64_zero;
  ms_var_decay      := msat_fp64_zero;
  ms_cla_inc        := msat_fp32_zero;
  ms_cla_decay      := msat_fp32_zero;
  ms_random_seed    := msat_fp64_zero;
  ms_progress       := msat_fp64_zero;
  ms_simpdb_assigns := 0;
  ms_simpdb_props   := 0;
  ms_verbosity      := 0;
  ms_stats          := [0;0;0;0;0;0;0;0;0;0;0]
|}.

Definition w2_view : cdcl_view := msolver_view w2_n w2.

(** *** state readings. *)
(** Suffix legend: [_cl] current level, [_a<i>] assignment at index [i],
    [_l<i>] level_of at index [i], [_k<i>] assignment_rank at
    index [i], [_r<i>] reason_of at index [i]. *)

Lemma w2_cl : current_level w2_view = 1.
Proof. reflexivity. Qed.

Lemma w2_a0 : assignment w2_view 0 = Some true.  Proof. reflexivity. Qed.

Lemma w2_a1 : assignment w2_view 1 = Some true.  Proof. reflexivity. Qed.

Lemma w2_l0 : level_of w2_view 0 = Some 1.  Proof. reflexivity. Qed.

Lemma w2_l1 : level_of w2_view 1 = Some 1.  Proof. reflexivity. Qed.

Lemma w2_l2 : level_of w2_view 2 = Some 0.  Proof. reflexivity. Qed.

Lemma w2_k0 : assignment_rank w2_view 0 = Some 1%nat.  Proof. reflexivity. Qed.

Lemma w2_k1 : assignment_rank w2_view 1 = Some 2%nat.  Proof. reflexivity. Qed.

Lemma w2_k2 : assignment_rank w2_view 2 = Some 0%nat.  Proof. reflexivity. Qed.

Lemma w2_r0 : reason_of w2_view 0 = None.  Proof. reflexivity. Qed.

Lemma w2_r1 : reason_of w2_view 1 = Some w2_reason_clause.
Proof. reflexivity. Qed.

Lemma w2_r2 : reason_of w2_view 2 = None.  Proof. reflexivity. Qed.

Lemma w2_assign : forall x b, mt_pv w2_core x = Some b ->
  (x = 0 \/ x = 1 \/ x = 2) /\ b = true.
Proof.
  intros x b H. unfold mt_pv in H.
  destruct (0 <=? x) eqn:E; [|discriminate].
  apply Z.leb_le in E.
  destruct (Z_lt_le_dec x 3) as [Hlt|Hge].
  - assert (Hc : x = 0 \/ x = 1 \/ x = 2) by lia.
    destruct Hc as [-> | [-> | ->]]; vm_compute in H; injection H as H; subst b.
    + split; [left; reflexivity | reflexivity].
    + split; [right; left; reflexivity | reflexivity].
    + split; [right; right; reflexivity | reflexivity].
  - exfalso.
    assert (Hz : Znth x (mt_assigns w2_core) 0 = 0).
    { apply znth_out_of_bounds; [lia|].
      assert (HL : Zlength (mt_assigns w2_core) = 3) by reflexivity. lia. }
    unfold assigns_pv, assigns_val in H. rewrite Hz in H.
    vm_compute in H. discriminate.
Qed.

Lemma w2_assign_view : forall x b, assignment w2_view x = Some b ->
  (x = 0 \/ x = 1 \/ x = 2) /\ b = true.
Proof. intros x b H. apply w2_assign. exact H. Qed.

Lemma w2_trail_wf : mtrail_wf w2_n w2_core.
Proof.
  assert (HT : Zlength (mt_trail w2_core) = 3) by reflexivity.
  assert (HQ : mt_qhead w2_core = 3) by reflexivity.
  assert (EL : mt_lim w2_core = [1]) by reflexivity.
  assert (EV : map lit_var_c (mt_trail w2_core) = [2; 0; 1]) by reflexivity.
  constructor.
  - unfold w2_n. lia.
  - reflexivity.
  - reflexivity.
  - do 3 (constructor; [unfold lbool_cell; lia|]). constructor.
  - lia.
  - unfold w2_n. lia.
  - do 3 (constructor; [unfold lit_wf_c, w2_n; lia|]). constructor.
  - rewrite EV. msat_nodup.
  - do 3 (constructor; [reflexivity|]). constructor.
  - rewrite EL. simpl. split; [constructor | exact I].
  - rewrite EL. constructor; [lia | constructor].
  - intros i Hi.
    assert (Hc : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hc as [-> | [-> | ->]]; reflexivity.
  - intros v Hv. unfold w2_n in Hv. rewrite EV.
    assert (Hc : v = 0 \/ v = 1 \/ v = 2) by lia.
    destruct Hc as [-> | [-> | ->]].
    + split; intro H; [right; left; reflexivity | discriminate].
    + split; intro H; [right; right; left; reflexivity | discriminate].
    + split; intro H; [left; reflexivity | discriminate].
Qed.

(** *** the algebra: the tagged reason really is [reason_valid]. *)

Lemma w2_reason_valid : reason_valid w2_view 1 w2_reason_clause.
Proof.
  exists true, 1, 2%nat.
  split; [exact w2_a1|].
  split; [exact w2_l1|].
  split; [exact w2_k1|].
  split.
  -
    left. reflexivity.
  - intros l Hl Hne. unfold w2_reason_clause in Hl. simpl in Hl.
    destruct Hl as [<-|[<-|[]]].
    + exfalso. apply Hne. reflexivity.
    + split; [reflexivity|].
      exists 1, 1%nat.
      split; [exact w2_l0 | split; [exact w2_k0 | split; lia]].
Qed.

Lemma w2_grounded : grounded_at w2_view.
Proof.
  intros x b Hx.
  destruct (w2_assign_view x b Hx) as [[-> | [-> | ->]] ->].
  - (* the level-1 decision *)
    exists 1, 1%nat.
    split; [exact w2_l0 | split; [exact w2_k0 | left; exact w2_r0]].
  - (* propagated by a BINARY clause: a tagged reason word *)
    exists 1, 2%nat.
    split; [exact w2_l1 | split; [exact w2_k1 |]].
    right. exists w2_reason_clause.
    split; [exact w2_r1 | exact w2_reason_valid].
  - (* the level-0 unit fact: NULL reason at level 0 *)
    exists 0, 0%nat.
    split; [exact w2_l2 | split; [exact w2_k2 | left; exact w2_r2]].
Qed.

Lemma w2_closed : closed_levels w2_view.
Proof.
  split; [|split].
  - rewrite w2_cl. lia.
  - intros x b d Ha Hd. rewrite w2_cl.
    destruct (w2_assign_view x b Ha) as [[-> | [-> | ->]] _].
    + rewrite w2_l0 in Hd. injection Hd as Hd. lia.
    + rewrite w2_l1 in Hd. injection Hd as Hd. lia.
    + rewrite w2_l2 in Hd. injection Hd as Hd. lia.
  - intros d Hd. rewrite w2_cl in Hd.
    assert (Hd1 : d = 1) by lia. subst d.
    exists 0.
    split; [exists true; exact w2_a0 | split; [exact w2_l0 | exact w2_r0]].
Qed.

Lemma w2_stable : stable_view w2_view.
Proof. split; [exact w2_grounded | exact w2_closed]. Qed.

(** *** reason bookkeeping. *)

Lemma w2_reason_cases : forall x c,
  reason_of w2_view x = Some c -> x = 1 /\ c = w2_reason_clause.
Proof.
  intros x c H.
  assert (E : reason_of w2_view x
              = match trail_pos (ms_core w2) x with
                | Some _ => if x =? 1 then Some w2_reason_clause else None
                | None => None
                end) by reflexivity.
  rewrite E in H.
  destruct (trail_pos (ms_core w2) x); [|discriminate].
  destruct (x =? 1) eqn:E2; [|discriminate].
  apply Z.eqb_eq in E2. split; [exact E2 | congruence].
Qed.

(** The tagged reason clause is [F]-entailed -- via the DB binary clause it
    came from, up to the swap [wmap_tag_witness] leaves behind. *)
Lemma w2_reason_entailed : entails_clause w2_F w2_reason_clause.
Proof.
  apply (entails_clause_perm w2_F [Neg 0; Pos 1]).
  - apply perm_swap.
  - apply entails_clause_in. right. right. left. reflexivity.
Qed.

Lemma w2_reasons_entailed : reasons_entailed w2_F w2_view.
Proof.
  intros x c H. destruct (w2_reason_cases x c H) as [_ ->].
  exact w2_reason_entailed.
Qed.

Lemma w2_reason_injective : clause_var_injective w2_reason_clause.
Proof.
  intros l1 l2 H1 H2 Hv. unfold w2_reason_clause in H1, H2.
  simpl in H1, H2.
  (* The two literals of the clause, in the four combinations: the diagonal
     is reflexivity, the off-diagonal contradicts [Hv]. *)
  destruct H1 as [<-|[<-|[]]]; destruct H2 as [<-|[<-|[]]];
    simpl in Hv; [ reflexivity | exfalso; lia | exfalso; lia | reflexivity ].
Qed.

Lemma w2_reasons_inj : reasons_var_injective w2_view.
Proof.
  intros x c H. destruct (w2_reason_cases x c H) as [_ ->].
  exact w2_reason_injective.
Qed.

(** *** TRAIL-IMPLIED.  The level-0 fact is justified by the unit clause of
    [F]; [grounded_at] does not carry that justification, so it is supplied
    here as its own entailment. *)

Lemma w2_ti0 :
  entails_clause [[Pos 2]; [Neg 0; Pos 2]; [Neg 0; Pos 1]] [Pos 2].
Proof. apply entails_clause_in. left. reflexivity. Qed.

Lemma w2_ti1 :
  entails_clause [[Pos 2]; [Neg 0; Pos 2]; [Neg 0; Pos 1]; [Pos 0]] [Pos 0].
Proof. apply entails_clause_in. right. right. right. left. reflexivity. Qed.

Lemma w2_ti2 :
  entails_clause [[Pos 2]; [Neg 0; Pos 2]; [Neg 0; Pos 1]; [Pos 0]] [Pos 1].
Proof.
  intros rho Hm. unfold models in Hm. rewrite Forall_forall in Hm.
  assert (HC : clause_satisfied rho [Neg 0; Pos 1])
    by (apply Hm; right; right; left; reflexivity).
  assert (H0 : clause_satisfied rho [Pos 0])
    by (apply Hm; right; right; right; left; reflexivity).
  destruct H0 as [l0 [Hin0 Hev0]]. simpl in Hin0. destruct Hin0 as [<-|[]].
  destruct HC as [l [Hin Hev]]. simpl in Hin.
  destruct Hin as [<-|[<-|[]]].
  - simpl in Hev, Hev0. apply negb_true_iff in Hev. congruence.
  - exists (Pos 1). split; [left; reflexivity | exact Hev].
Qed.

Lemma w2_trail_implied : trail_implied w2_F (ms_core w2).
Proof.
  intros i l Hi Hl.
  assert (ET : Zlength (mt_trail (ms_core w2)) = 3) by reflexivity.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2) by lia.
  destruct Hc as [-> | [-> | ->]]; subst l.
  - exact w2_ti0.
  - exact w2_ti1.
  - exact w2_ti2.
Qed.

(** *** database, watchers, heap. *)

Lemma w2_db_wf : db_wf w2_n (msolver_db w2).
Proof.
  unfold db_wf, msolver_db. simpl. split; [|split].
  - constructor;
      [ simpl; intros [H|[]]; lia
      | constructor; [simpl; tauto | constructor] ].
  - constructor; [simpl; split; [lia|reflexivity]|].
    constructor; [simpl; split; [lia|reflexivity] | constructor].
  - constructor; [|constructor; [|constructor]].
    + simpl. unfold obj_wf. simpl. split; [|split].
      * assert (E : Zlength [1; 4] = 2) by reflexivity. lia.
      * do 2 (constructor; [unfold lit_wf_c, w2_n; lia|]). constructor.
      * vm_compute. msat_nodup.
    + simpl. unfold obj_wf. simpl. split; [|split].
      * assert (E : Zlength [1; 2] = 2) by reflexivity. lia.
      * do 2 (constructor; [unfold lit_wf_c, w2_n; lia|]). constructor.
      * vm_compute. msat_nodup.
Qed.

Lemma w2_wmap : wmap_exact w2_n (msolver_db w2) (ms_wm w2).
Proof.
  split; [reflexivity|].
  intros l Hl. unfold w2_n in Hl.
  assert (Hc : l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5) by lia.
  destruct Hc as [->|[->|[->|[->|[-> | ->]]]]];
    vm_compute; apply Permutation_refl.
Qed.

Lemma w2_watch_frontier :
  minisat_watch_frontier w2_n (msolver_db w2)
    (mt_assigns (ms_core w2)) (mt_trail (ms_core w2))
    (mt_qhead (ms_core w2)).
Proof.
  unfold minisat_watch_frontier, watch_frontier,
    minisat_watch_occurrences, msolver_db, w2, w2_c1, w2_c2. cbn.
  constructor.
  - intros [_ Hright].
    assert (Hwf : lit_wf_c w2_n 5) by (unfold lit_wf_c, w2_n; lia).
    apply (proj1 (minisat_processed_denote
      w2_n [1; 1; 1] [4; 0; 2] 3 5 Hwf)) in Hright.
    destruct Hright as [Htrue _]. vm_compute in Htrue. discriminate.
  - constructor.
    + intros [_ Hright].
      assert (Hwf : lit_wf_c w2_n 3) by (unfold lit_wf_c, w2_n; lia).
      apply (proj1 (minisat_processed_denote
        w2_n [1; 1; 1] [4; 0; 2] 3 3 Hwf)) in Hright.
      destruct Hright as [Htrue _]. vm_compute in Htrue. discriminate.
    + constructor.
Qed.

Lemma w2_heap_eq :
  msolver_heap w2 = {| mh_heap := []; mh_orderpos := [-1; -1; -1] |}.
Proof. reflexivity. Qed.

Lemma w2_heap_wf : heap_wf w2_n (msolver_heap w2).
Proof.
  rewrite w2_heap_eq. unfold heap_wf, w2_n. simpl mh_heap. simpl mh_orderpos.
  split; [|split; [|split; [|split]]].
  - reflexivity.
  - constructor.
  - constructor.
  - intros v Hv.
    assert (Hc : v = 0 \/ v = 1 \/ v = 2) by lia.
    destruct Hc as [-> | [-> | ->]]; left; reflexivity.
  - intros i Hi.
    assert (EL : Zlength (@nil Z) = 0) by reflexivity. lia.
Qed.

Lemma w2_heap_covers :
  heap_covers w2_n (msolver_heap w2) (mt_assigns (ms_core w2))
              (mt_trail (ms_core w2)) (mt_qhead (ms_core w2)).
Proof.
  intros v Hv Hop. unfold w2_n in Hv.
  assert (EQ : mt_qhead (ms_core w2) = 3) by reflexivity.
  assert (Hc : v = 0 \/ v = 1 \/ v = 2) by lia.
  destruct Hc as [-> | [-> | ->]].
  - split; [discriminate | exists 1; split; [lia | reflexivity]].
  - split; [discriminate | exists 2; split; [lia | reflexivity]].
  - split; [discriminate | exists 0; split; [lia | reflexivity]].
Qed.

Example w2_weak : msolver_inv_weak w2_n w2_F [] [] w2.
Proof.
  constructor.
  - reflexivity.
  - unfold w2_n. lia.
  - unfold solver_shape. simpl. repeat split; try reflexivity; try lia; try (right; reflexivity).
  - split; [unfold w2_n; lia|].
    do 3 (constructor;
      [ repeat (constructor;
                [unfold literal_wf, var_in_range, w2_n; simpl; lia|]);
        constructor |]).
    constructor.
  - constructor.
  - exact w2_trail_wf.
  - assert (E : Zlength (mt_lim (ms_core w2)) = 1) by reflexivity.
    unfold w2_n. lia.
  - assert (E : Zlength (mt_lim (ms_core w2)) = 1) by reflexivity.
    assert (E' : ms_root_level w2 = 0) by reflexivity. lia.
  - reflexivity.
  - apply incl_refl.
  - constructor.
  - exact w2_stable.
  - exact w2_reasons_entailed.
  - exact w2_reasons_inj.
  - exact w2_trail_implied.
  - exact w2_db_wf.
  - unfold db_matches_cnf.
    assert (E : db_clauses (ms_prob w2) = [[Neg 0; Pos 2]; [Neg 0; Pos 1]])
      by reflexivity.
    rewrite E. constructor; [|constructor; [|constructor]].
    + exists [Neg 0; Pos 2].
      split; [right; left; reflexivity | apply Permutation_refl].
    + exists [Neg 0; Pos 1].
      split; [right; right; left; reflexivity | apply Permutation_refl].
  - unfold db_implied. simpl. constructor.
  - intros c Hc. vm_compute in Hc.
    assert (E : db_clauses (ms_prob w2) = [[Neg 0; Pos 2]; [Neg 0; Pos 1]])
      by reflexivity.
    destruct Hc as [<-|[<-|[<-|[]]]].
    + (* the unit clause: never in the database, root-satisfied instead *)
      right. exists (Pos 2).
      split; [left; reflexivity|]. split; reflexivity.
    + left. exists [Neg 0; Pos 2].
      split; [rewrite E; left; reflexivity | apply Permutation_refl].
    + left. exists [Neg 0; Pos 1].
      split; [rewrite E; right; left; reflexivity | apply Permutation_refl].
  - unfold learnt_db. simpl. constructor.
  - unfold prob_db. simpl. repeat constructor.
  - vm_compute. intros [H|[H|[]]]; lia.
  - intros v Hv. unfold w2_n in Hv.
    assert (Hc : v = 0 \/ v = 1 \/ v = 2) by lia.
    destruct Hc as [-> | [-> | ->]].
    + reflexivity.
    + vm_compute. split; [discriminate | reflexivity].
    + reflexivity.
  - intros v co Hv Htag Hnz Hin.
    assert (ES : ms_size w2 = 3) by reflexivity.
    assert (Hc : v = 0 \/ v = 1 \/ v = 2) by lia.
    destruct Hc as [-> | [-> | ->]].
    + exfalso. apply Hnz. reflexivity.
    + exfalso. vm_compute in Htag. discriminate.
    + exfalso. apply Hnz. reflexivity.
  - (* binary_reason_same_level: the tag word at variable 1 decodes to
       literal 0, which is in range; the tag variable 0 and the implied
       variable 1 are both at level 1 -- INV-PROP-LEVEL's consequence at the
       propagate site *)
    intros v Hv Ht.
    assert (ES : ms_size w2 = 3) by reflexivity.
    assert (Hc : v = 0 \/ v = 1 \/ v = 2) by lia.
    destruct Hc as [-> | [-> | ->]].
    + exfalso. vm_compute in Ht. discriminate.
    + split; [| split; [reflexivity | discriminate]].
      unfold lit_wf_c. rewrite ES.
      assert (E : tag_lit (Znth 1 (ms_reason_words w2) 0) = 0) by reflexivity.
      rewrite E. lia.
    + exfalso. vm_compute in Ht. discriminate.
  - exact w2_wmap.
  - unfold solver_tags_clear, w2. simpl. repeat constructor.
  - exact w2_heap_wf.
  - exact msat_fp32_zero_nonnegative.
  - unfold msolver_seed_ok. apply msat_fp64_zero_finite.
Qed.

Example w2_inv : msolver_inv w2_n w2_F [] [] w2.
Proof.
  constructor.
  - exact w2_weak.
  - unfold prop_level.
    assert (EL : mt_lim (ms_core w2) = [1]) by reflexivity.
    assert (EQ : mt_qhead (ms_core w2) = 3) by reflexivity.
    rewrite EL, EQ. constructor; [lia|]. constructor.
  - exact w2_watch_frontier.
  - exact w2_heap_covers.
  - unfold current_reasonless_earliest.
    intros d Hd v Hlev Hraw.
    change (0 < d <= 1) in Hd.
    assert (d = 1) by lia. subst d.
    destruct (Z.eq_dec v 0) as [->|Hv0].
    + split; reflexivity.
    + destruct (Z.eq_dec v 1) as [->|Hv1].
      * vm_compute in Hraw. discriminate.
      * exfalso. pose proof Hlev as Hlev0.
        unfold msolver_view, level_of, view_of, trail_pos in Hlev.
        destruct (find_var_pos v (mt_trail (ms_core w2))) as [k |] eqn:E;
          [|discriminate].
        pose proof (find_var_pos_some_in
          v (mt_trail (ms_core w2)) k E) as Hin.
        unfold w2, w2_core in Hin. simpl in Hin.
        destruct Hin as [Hv2 | [Hv0' | [Hv1' | []]]].
        -- subst v. change (level_of w2_view 2 = Some 1) in Hlev0.
           rewrite w2_l2 in Hlev0. discriminate.
        -- subst v. contradiction.
        -- subst v. contradiction.
Qed.

Example w2_tagged_reason_shape :
  is_tag (Znth 1 (ms_reason_words w2) 0) = true /\
  lit_var_c (tag_lit (Znth 1 (ms_reason_words w2) 0)) <> 1 /\
  ms_reason_of w2 1 = Some [satisfying_literal 1 true;
                            literal_neg (lit_denote
                              (tag_lit (Znth 1 (ms_reason_words w2) 0)))].
Proof.
  split; [reflexivity|].
  split; [intro H; vm_compute in H; discriminate|].
  exact (inv_tagged_reason_shape w2_n w2_F [] [] w2 1 true
           w2_inv ltac:(unfold w2_n; lia) w2_a1 eq_refl).
Qed.

Example w2_model_copies : model_copies w2_n w2.
Proof.
  split; [reflexivity|]. intros v Hv. unfold w2_n in Hv.
  assert (Hv' : v = 0 \/ v = 1 \/ v = 2) by lia.
  destruct Hv' as [-> | [-> | ->]]; reflexivity.
Qed.

Example w2_model_saved : model_saved w2_n w2_F [] w2.
Proof.
  eapply sat_endgame_model;
    [ exact (msi_weak w2_inv) | exact (msi_watch_frontier w2_inv)
    | exact (msi_heap_covers w2_inv) | reflexivity | reflexivity
    | exact w2_model_copies ].
Qed.


(** ** Witness 3 : the UNSAT endgame, end to end.                        *)


(** [n = 2], [F = {{~x0,~x1}, {x0}, {x1}}], no assumptions.  The state
    models:

      addclause {~x0,~x1}   one binary database object at ghost pointer 8
      addclause {x0}        unit -> level-0 trail fact, NULL reason
      addclause {x1}        unit -> level-0 trail fact, NULL reason
      solve -> propagate:   p = trail[0] = lit(x0) = 0, qhead 0 -> 1;
                            wlists[0] = [tag_of_lit 3]; the tag literal is
                            [~x1], which is FALSE, so enqueue fails and
                            propagate sets confl = s->binary with lits
                            [~x1; ~x0] and returns
      search:               solver_dlevel(s) = 0 = s->root_level, so
                            [return l_False]

    Here [qhead = 1] because conflict aborts the current scan.  The persistent
    weak invariant holds and is exactly what the UNSAT endgame consumes. *)

Definition w3_n : Z := 2.

Definition w3_F : cnf := [[Neg 0; Neg 1]; [Pos 0]; [Pos 1]].

Definition w3_obj : clause_obj := {| co_lits := [1; 3]; co_learnt := false |}.

Definition w3_core : mtrail :=
  {| mt_assigns := [1; 1];
     mt_levels  := [0; 0];
     mt_trail   := [0; 2];
     mt_lim     := [];
     mt_qhead   := 1 |}.

Definition w3 : msolver := {|
  ms_size           := 2;
  ms_cap            := 2;
  ms_qtail          := 2;
  ms_capacity_pending_qhead := 0;
  ms_capacity_root_propagation_pending := 0;
  ms_core           := w3_core;
  ms_root_level     := 0;
  ms_reason_words   := [0; 0];
  ms_reason_of      := fun _ => None;
  ms_prob           := [(8, w3_obj)];
  ms_learnt         := [];
  ms_binary         := 16;
  (* the scratch conflict clause [solver_propagate] wrote: {~x1, ~x0} *)
  ms_binary_lits    := [3; 1];
  (* wlists[~1] = wlists[0] holds tag_of_lit 3 = 7;
     wlists[~3] = wlists[2] holds tag_of_lit 1 = 3 *)
  ms_wm             := [[7]; []; [3]; []];
  ms_activity       := [msat_fp64_zero; msat_fp64_zero];
  ms_orderpos       := [0; 1];
  ms_order          := [0; 1];
  ms_model          := [0; 0];
  ms_tags           := [0; 0];
  ms_tagged         := [];
  ms_stack          := [];
  ms_var_inc        := msat_fp64_zero;
  ms_var_decay      := msat_fp64_zero;
  ms_cla_inc        := msat_fp32_zero;
  ms_cla_decay      := msat_fp32_zero;
  ms_random_seed    := msat_fp64_zero;
  ms_progress       := msat_fp64_zero;
  ms_simpdb_assigns := 0;
  ms_simpdb_props   := 0;
  ms_verbosity      := 0;
  ms_stats          := [0;0;0;0;0;0;0;0;0;0;0]
|}.

Definition w3_view : cdcl_view := msolver_view w3_n w3.

Lemma w3_assign : forall x b, mt_pv w3_core x = Some b ->
  (x = 0 \/ x = 1) /\ b = true.
Proof.
  intros x b H. unfold mt_pv in H.
  destruct (0 <=? x) eqn:E; [|discriminate].
  apply Z.leb_le in E.
  destruct (Z_lt_le_dec x 2) as [Hlt|Hge].
  - assert (Hc : x = 0 \/ x = 1) by lia.
    destruct Hc as [-> | ->]; vm_compute in H; injection H as H; subst b.
    + split; [left; reflexivity | reflexivity].
    + split; [right; reflexivity | reflexivity].
  - exfalso.
    assert (Hz : Znth x (mt_assigns w3_core) 0 = 0).
    { apply znth_out_of_bounds; [lia|].
      assert (HL : Zlength (mt_assigns w3_core) = 2) by reflexivity. lia. }
    unfold assigns_pv, assigns_val in H. rewrite Hz in H.
    vm_compute in H. discriminate.
Qed.

Lemma w3_assign_view : forall x b, assignment w3_view x = Some b ->
  (x = 0 \/ x = 1) /\ b = true.
Proof. intros x b H. apply w3_assign. exact H. Qed.

Lemma w3_trail_wf : mtrail_wf w3_n w3_core.
Proof.
  assert (HT : Zlength (mt_trail w3_core) = 2) by reflexivity.
  assert (HQ : mt_qhead w3_core = 1) by reflexivity.
  assert (EV : map lit_var_c (mt_trail w3_core) = [0; 1]) by reflexivity.
  constructor.
  - unfold w3_n. lia.
  - reflexivity.
  - reflexivity.
  - do 2 (constructor; [unfold lbool_cell; lia|]). constructor.
  - lia.
  - unfold w3_n. lia.
  - do 2 (constructor; [unfold lit_wf_c, w3_n; lia|]). constructor.
  - rewrite EV. msat_nodup.
  - do 2 (constructor; [reflexivity|]). constructor.
  - exact I.
  - constructor.
  - intros i Hi.
    assert (Hc : i = 0 \/ i = 1) by lia.
    destruct Hc as [-> | ->]; reflexivity.
  - intros v Hv. unfold w3_n in Hv. rewrite EV.
    assert (Hc : v = 0 \/ v = 1) by lia.
    destruct Hc as [-> | ->].
    + split; intro H; [left; reflexivity | discriminate].
    + split; intro H; [right; left; reflexivity | discriminate].
Qed.

(** Both level-0 facts are NULL-reason assignments: no reason word, so
    nothing to make the stable view depend on. *)
Lemma w3_stable : stable_view w3_view.
Proof.
  assert (HC : current_level w3_view = 0) by reflexivity.
  split.
  - intros x b Hx.
    destruct (w3_assign_view x b Hx) as [[-> | ->] ->].
    + exists 0, 0%nat.
      split; [reflexivity | split; [reflexivity | left; reflexivity]].
    + exists 0, 1%nat.
      split; [reflexivity | split; [reflexivity | left; reflexivity]].
  - split; [|split].
    + rewrite HC. lia.
    + intros x b d Hx Hd. rewrite HC.
      destruct (w3_assign_view x b Hx) as [[-> | ->] _].
      * assert (HL : level_of w3_view 0 = Some 0) by reflexivity.
        rewrite HL in Hd. injection Hd as Hd. lia.
      * assert (HL : level_of w3_view 1 = Some 0) by reflexivity.
        rewrite HL in Hd. injection Hd as Hd. lia.
    + intros d Hd. rewrite HC in Hd. lia.
Qed.

Lemma w3_no_reason : forall x c, reason_of w3_view x = Some c -> False.
Proof.
  intros x c H.
  assert (E : reason_of w3_view x
              = match trail_pos (ms_core w3) x with
                | Some _ => @None clause
                | None => None
                end) by reflexivity.
  rewrite E in H.
  destruct (trail_pos (ms_core w3) x); discriminate.
Qed.

Lemma w3_ti0 : entails_clause [[Neg 0; Neg 1]; [Pos 0]; [Pos 1]] [Pos 0].
Proof. apply entails_clause_in. right. left. reflexivity. Qed.

Lemma w3_ti1 : entails_clause [[Neg 0; Neg 1]; [Pos 0]; [Pos 1]] [Pos 1].
Proof. apply entails_clause_in. right. right. left. reflexivity. Qed.

Lemma w3_trail_implied : trail_implied w3_F (ms_core w3).
Proof.
  intros i l Hi Hl.
  assert (ET : Zlength (mt_trail (ms_core w3)) = 2) by reflexivity.
  assert (Hc : i = 0 \/ i = 1) by lia.
  destruct Hc as [-> | ->]; subst l.
  - exact w3_ti0.
  - exact w3_ti1.
Qed.

Lemma w3_db_wf : db_wf w3_n (msolver_db w3).
Proof.
  unfold db_wf, msolver_db. simpl. split; [|split].
  - constructor; [simpl; tauto | constructor].
  - constructor; [simpl; split; [lia|reflexivity] | constructor].
  - constructor; [|constructor].
    simpl. unfold obj_wf. simpl. split; [|split].
    + assert (E : Zlength [1; 3] = 2) by reflexivity. lia.
    + do 2 (constructor; [unfold lit_wf_c, w3_n; lia|]). constructor.
    + vm_compute. msat_nodup.
Qed.

Lemma w3_wmap : wmap_exact w3_n (msolver_db w3) (ms_wm w3).
Proof.
  split; [reflexivity|].
  intros l Hl. unfold w3_n in Hl.
  assert (Hc : l = 0 \/ l = 1 \/ l = 2 \/ l = 3) by lia.
  destruct Hc as [->|[->|[-> | ->]]]; vm_compute; apply Permutation_refl.
Qed.

Lemma w3_heap_wf : heap_wf w3_n (msolver_heap w3).
Proof.
  assert (EH : msolver_heap w3
               = {| mh_heap := [0; 1]; mh_orderpos := [0; 1] |}) by reflexivity.
  rewrite EH. unfold heap_wf, w3_n. simpl mh_heap. simpl mh_orderpos.
  split; [|split; [|split; [|split]]].
  - reflexivity.
  - msat_nodup.
  - do 2 (constructor; [lia|]). constructor.
  - intros v Hv.
    assert (Hc : v = 0 \/ v = 1) by lia.
    assert (EL : Zlength [0; 1] = 2) by reflexivity.
    assert (E0 : Znth 0 [0; 1] (-1) = 0) by reflexivity.
    assert (E1 : Znth 1 [0; 1] (-1) = 1) by reflexivity.
    destruct Hc as [-> | ->]; right; (split; [lia | reflexivity]).
  - intros i Hi.
    assert (EL : Zlength [0; 1] = 2) by reflexivity.
    assert (Hc : i = 0 \/ i = 1) by lia.
    destruct Hc as [-> | ->]; reflexivity.
Qed.

Example w3_weak : msolver_inv_weak w3_n w3_F [] [] w3.
Proof.
  constructor.
  - reflexivity.
  - unfold w3_n. lia.
  - unfold solver_shape. simpl. repeat split; try reflexivity; try lia; try (right; reflexivity).
  - split; [unfold w3_n; lia|].
    do 3 (constructor;
      [ repeat (constructor;
                [unfold literal_wf, var_in_range, w3_n; simpl; lia|]);
        constructor |]).
    constructor.
  - constructor.
  - exact w3_trail_wf.
  - assert (E : Zlength (mt_lim (ms_core w3)) = 0) by reflexivity.
    unfold w3_n. lia.
  - assert (E : Zlength (mt_lim (ms_core w3)) = 0) by reflexivity.
    assert (E' : ms_root_level w3 = 0) by reflexivity. lia.
  - reflexivity.
  - apply incl_refl.
  - constructor.
  - exact w3_stable.
  - intros x c H. exfalso. exact (w3_no_reason x c H).
  - intros x c H. exfalso. exact (w3_no_reason x c H).
  - exact w3_trail_implied.
  - exact w3_db_wf.
  - unfold db_matches_cnf.
    assert (E : db_clauses (ms_prob w3) = [[Neg 0; Neg 1]]) by reflexivity.
    rewrite E. constructor; [|constructor].
    exists [Neg 0; Neg 1]. split; [left; reflexivity | apply Permutation_refl].
  - unfold db_implied. simpl. constructor.
  - intros c Hc. vm_compute in Hc.
    assert (E : db_clauses (ms_prob w3) = [[Neg 0; Neg 1]]) by reflexivity.
    destruct Hc as [<-|[<-|[<-|[]]]].
    + left. exists [Neg 0; Neg 1].
      split; [rewrite E; left; reflexivity | apply Permutation_refl].
    + right. exists (Pos 0). split; [left; reflexivity|].
      split; reflexivity.
    + right. exists (Pos 1). split; [left; reflexivity|].
      split; reflexivity.
  - unfold learnt_db. simpl. constructor.
  - unfold prob_db. simpl. repeat constructor.
  - vm_compute. intros [H|[]]. lia.
  - intros v Hv. unfold w3_n in Hv.
    assert (Hc : v = 0 \/ v = 1) by lia.
    destruct Hc as [-> | ->]; vm_compute; reflexivity.
  - intros v co Hv Htag Hnz Hin. exfalso.
    assert (ES : ms_size w3 = 2) by reflexivity.
    assert (Hc : v = 0 \/ v = 1) by lia.
    destruct Hc as [-> | ->]; apply Hnz; reflexivity.
  - intros v Hv Ht. exfalso.
    assert (ES : ms_size w3 = 2) by reflexivity.
    assert (Hc : v = 0 \/ v = 1) by lia.
    destruct Hc as [-> | ->]; vm_compute in Ht; discriminate.
  - exact w3_wmap.
  - unfold solver_tags_clear, w3. simpl. repeat constructor.
  - exact w3_heap_wf.
  - exact msat_fp32_zero_nonnegative.
  - unfold msolver_seed_ok. apply msat_fp64_zero_finite.
Qed.

(** The [s->binary] scratch clause the C reports is a
    permutation of that very database clause -- recovered from the watcher
    tag by [wmap_tag_witness], the route the watcher-tag model prescribes. *)
Example w3_binary_route :
  exists p co, In (p, co) (msolver_db w3) /\
               Zlength (co_lits co) = 2 /\
               Permutation (co_lits co) [lit_neg_c 0; tag_lit 7].
Proof.
  apply (wmap_tag_witness w3_n (msolver_db w3) (ms_wm w3) 0 7
           w3_db_wf w3_wmap ltac:(unfold w3_n; lia)
           ltac:(left; reflexivity) eq_refl).
Qed.

Lemma w3_binary_lits_denote :
  lits_denote (ms_binary_lits w3) = [Neg 1; Neg 0].
Proof. reflexivity. Qed.

Example w3_unsat_via_binary : cnf_unsat w3_n (cnf_with_units w3_F []).
Proof.
  apply (unsat_endgame w3_n w3_F [] [] w3 [] (lits_denote (ms_binary_lits w3))).
  - exact w3_weak.
  - reflexivity.
  - apply incl_refl.
  - rewrite w3_binary_lits_denote.
    apply (entails_clause_perm w3_F [Neg 0; Neg 1]).
    + apply perm_swap.
    + apply entails_clause_in. left. reflexivity.
  - rewrite w3_binary_lits_denote. intros l Hl. simpl in Hl.
    destruct Hl as [<-|[<-|[]]]; reflexivity.
  - rewrite w3_binary_lits_denote.
    do 2 (constructor; [unfold literal_wf, var_in_range, w3_n; simpl; lia|]).
    constructor.
Qed.

Example w3_assuming_conflict_unsat :
  cnf_unsat w3_n (cnf_with_units w3_F []).
Proof.
  apply (assuming_conflict_unsat
           w3_n w3_F [] [] w3 (lits_denote (ms_binary_lits w3))).
  - exact (msolver_inv_weak_assuming
             w3_n w3_F [] [] w3 w3_weak eq_refl).
  - rewrite w3_binary_lits_denote.
    apply (entails_clause_perm w3_F [Neg 0; Neg 1]);
      [apply perm_swap|apply entails_clause_in; left; reflexivity].
  - rewrite w3_binary_lits_denote. intros l Hl. simpl in Hl.
    destruct Hl as [<-|[<-|[]]]; reflexivity.
  - rewrite w3_binary_lits_denote.
    do 2 (constructor;
      [unfold literal_wf, var_in_range, w3_n; simpl; lia|]).
    constructor.
Qed.

Theorem msolver_inv_weak_unsat_inhabited :
  exists n F A_arr A_inst M,
    msolver_inv_weak n F A_arr A_inst M /\
    solver_at_root M /\
    cnf_unsat n (cnf_with_units F A_arr).
Proof.
  exists w3_n, w3_F, (@nil literal), (@nil literal), w3.
  split; [exact w3_weak|].
  split; [reflexivity | exact w3_unsat_via_binary].
Qed.


(** ** Witness 4 : a non-empty processed-assumption prefix.              *)


(** [n = 4], [F = {{x2}, {x1,x3}, {~x3,~x2,x1}}].  The trail contains the
    processed caller assumption [x0] at level 1.  [w4_at] varies only the
    stored root field, so [w4_assuming_gen] demonstrates that the mid-loop
    bundle depends on the current decision level and processed prefix rather
    than that stale field.  [w4_false_assumption_unsat] then exercises the
    cursor-assumption-false route with an unprocessed [~x2]. *)

Definition w4_n : Z := 4.

Definition w4_F : cnf := [[Pos 2]; [Pos 1; Pos 3]; [Neg 3; Neg 2; Pos 1]].

(** {x1, x3} packed; {~x3, ~x2, x1} packed AFTER the level-0 watch move;
    the learnt {x1, ~x2} packed. *)
Definition w4_c1 : clause_obj := {| co_lits := [2; 6]; co_learnt := false |}.

Definition w4_c2 : clause_obj := {| co_lits := [7; 2; 5]; co_learnt := false |}.

Definition w4_learnt_obj : clause_obj :=
  {| co_lits := [2; 5]; co_learnt := true |}.

Definition w4_core : mtrail :=
  {| mt_assigns := [1; 1; 1; 0];
     mt_levels  := [1; 1; 0; 2];
     mt_trail   := [4; 0; 2];
     mt_lim     := [1];
     mt_qhead   := 3 |}.

(** The ghost decode of [reasons[1] = 40]: the learnt clause, head first. *)
Definition w4_reason_clause : clause := [Pos 1; Neg 2].

Definition w4_at (root : Z) : msolver := {|
  ms_size           := 4;
  ms_cap            := 4;
  ms_qtail          := 3;
  ms_capacity_pending_qhead := 0;
  ms_capacity_root_propagation_pending := 0;
  ms_core           := w4_core;
  ms_root_level     := root;
  (* reasons[1] = the learnt object's pointer; everything else NULL *)
  ms_reason_words   := [0; 40; 0; 0];
  ms_reason_of      := fun v => if v =? 1 then Some w4_reason_clause else None;
  ms_prob           := [(8, w4_c1); (24, w4_c2)];
  ms_learnt         := [(40, w4_learnt_obj)];
  ms_binary         := 16;
  ms_binary_lits    := [0; 0];
  (* wlists[3]: tag 13 (c1), ptr 24 (c2 after the move), tag 11 (learnt);
     wlists[4]: tag 5 (learnt) -- the clamp shape;
     wlists[6]: ptr 24 (c2's other watch); wlists[7]: tag 5 (c1) *)
  ms_wm             := [[]; []; []; [13; 24; 11]; [5]; []; [24]; [5]];
  ms_activity       := [msat_fp64_zero; msat_fp64_zero;
                        msat_fp64_zero; msat_fp64_zero];
  ms_orderpos       := [-1; 1; -1; 0];
  ms_order          := [3; 1];
  ms_model          := [0; 0; 0; 0];
  ms_tags           := [0; 0; 0; 0];
  ms_tagged         := [];
  ms_stack          := [];
  ms_var_inc        := msat_fp64_zero;
  ms_var_decay      := msat_fp64_zero;
  ms_cla_inc        := msat_fp32_zero;
  ms_cla_decay      := msat_fp32_zero;
  ms_random_seed    := msat_fp64_zero;
  ms_progress       := msat_fp64_zero;
  ms_simpdb_assigns := 0;
  ms_simpdb_props   := 0;
  ms_verbosity      := 0;
  ms_stats          := [0;0;0;0;0;0;0;0;0;0;0]
|}.

(** The shipped assumption path enters search with [root_level = 1]. *)
Definition w4 : msolver := w4_at 1.

Definition w4_view : cdcl_view := msolver_view w4_n w4.

(** *** state readings. *)

Lemma w4_cl : current_level w4_view = 1.
Proof. reflexivity. Qed.

Lemma w4_a0 : assignment w4_view 0 = Some true.  Proof. reflexivity. Qed.

Lemma w4_a1 : assignment w4_view 1 = Some true.  Proof. reflexivity. Qed.

Lemma w4_l0 : level_of w4_view 0 = Some 1.  Proof. reflexivity. Qed.

Lemma w4_l1 : level_of w4_view 1 = Some 1.  Proof. reflexivity. Qed.

Lemma w4_l2 : level_of w4_view 2 = Some 0.  Proof. reflexivity. Qed.

Lemma w4_k0 : assignment_rank w4_view 0 = Some 1%nat.  Proof. reflexivity. Qed.

Lemma w4_k1 : assignment_rank w4_view 1 = Some 2%nat.  Proof. reflexivity. Qed.

Lemma w4_k2 : assignment_rank w4_view 2 = Some 0%nat.  Proof. reflexivity. Qed.

Lemma w4_r0 : reason_of w4_view 0 = None.  Proof. reflexivity. Qed.

Lemma w4_r1 : reason_of w4_view 1 = Some w4_reason_clause.
Proof. reflexivity. Qed.

Lemma w4_r2 : reason_of w4_view 2 = None.  Proof. reflexivity. Qed.

Lemma w4_assign : forall x b, mt_pv w4_core x = Some b ->
  (x = 0 \/ x = 1 \/ x = 2) /\ b = true.
Proof.
  intros x b H. unfold mt_pv in H.
  destruct (0 <=? x) eqn:E; [|discriminate].
  apply Z.leb_le in E.
  destruct (Z_lt_le_dec x 4) as [Hlt|Hge].
  - assert (Hc : x = 3 \/ x = 0 \/ x = 1 \/ x = 2) by lia.
    destruct Hc as [-> | [-> | [-> | ->]]].
    + vm_compute in H. discriminate.
    + vm_compute in H. injection H as H. subst b.
      split; [left; reflexivity | reflexivity].
    + vm_compute in H. injection H as H. subst b.
      split; [right; left; reflexivity | reflexivity].
    + vm_compute in H. injection H as H. subst b.
      split; [right; right; reflexivity | reflexivity].
  - exfalso.
    assert (Hz : Znth x (mt_assigns w4_core) 0 = 0).
    { apply znth_out_of_bounds; [lia|].
      assert (HL : Zlength (mt_assigns w4_core) = 4) by reflexivity. lia. }
    unfold assigns_pv, assigns_val in H. rewrite Hz in H.
    vm_compute in H. discriminate.
Qed.

Lemma w4_assign_view : forall x b, assignment w4_view x = Some b ->
  (x = 0 \/ x = 1 \/ x = 2) /\ b = true.
Proof. intros x b H. apply w4_assign. exact H. Qed.

Lemma w4_trail_wf : mtrail_wf w4_n w4_core.
Proof.
  assert (HT : Zlength (mt_trail w4_core) = 3) by reflexivity.
  assert (HQ : mt_qhead w4_core = 3) by reflexivity.
  assert (EL : mt_lim w4_core = [1]) by reflexivity.
  assert (EV : map lit_var_c (mt_trail w4_core) = [2; 0; 1]) by reflexivity.
  constructor.
  - unfold w4_n. lia.
  - reflexivity.
  - reflexivity.
  - do 4 (constructor; [unfold lbool_cell; lia|]). constructor.
  - lia.
  - unfold w4_n. lia.
  - do 3 (constructor; [unfold lit_wf_c, w4_n; lia|]). constructor.
  - rewrite EV. msat_nodup.
  - do 3 (constructor; [reflexivity|]). constructor.
  - rewrite EL. simpl. split; [constructor | exact I].
  - rewrite EL. constructor; [lia | constructor].
  - intros i Hi.
    assert (Hc : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hc as [-> | [-> | ->]]; reflexivity.
  - intros v Hv. unfold w4_n in Hv. rewrite EV.
    assert (Hc : v = 0 \/ v = 1 \/ v = 2 \/ v = 3) by lia.
    destruct Hc as [-> | [-> | [-> | ->]]].
    + split; intro H; [right; left; reflexivity | discriminate].
    + split; intro H; [right; right; left; reflexivity | discriminate].
    + split; intro H; [left; reflexivity | discriminate].
    + split; intro H;
        [ exfalso; apply H; reflexivity
        | exfalso; simpl in H; destruct H as [H|[H|[H|[]]]]; lia ].
Qed.

(** *** the algebra: the learnt-clause reason is [reason_valid]. *)

Lemma w4_reason_valid : reason_valid w4_view 1 w4_reason_clause.
Proof.
  exists true, 1, 2%nat.
  split; [exact w4_a1|].
  split; [exact w4_l1|].
  split; [exact w4_k1|].
  split.
  - (* the head IS the satisfying literal: record's lits[0] discipline *)
    left. reflexivity.
  - intros l Hl Hne. unfold w4_reason_clause in Hl. simpl in Hl.
    destruct Hl as [<-|[<-|[]]].
    + exfalso. apply Hne. reflexivity.
    + split; [reflexivity|].
      exists 0, 0%nat.
      split; [exact w4_l2 | split; [exact w4_k2 | split; lia]].
Qed.

Lemma w4_grounded : grounded_at w4_view.
Proof.
  intros x b Hx.
  destruct (w4_assign_view x b Hx) as [[-> | [-> | ->]] ->].
  - (* the assumption decision at level 1 *)
    exists 1, 1%nat.
    split; [exact w4_l0 | split; [exact w4_k0 | left; exact w4_r0]].
  - (* enqueued by solver_record with the learnt clause as reason *)
    exists 1, 2%nat.
    split; [exact w4_l1 | split; [exact w4_k1 |]].
    right. exists w4_reason_clause.
    split; [exact w4_r1 | exact w4_reason_valid].
  - (* the level-0 unit fact: NULL reason at level 0 *)
    exists 0, 0%nat.
    split; [exact w4_l2 | split; [exact w4_k2 | left; exact w4_r2]].
Qed.

Lemma w4_closed : closed_levels w4_view.
Proof.
  split; [|split].
  - rewrite w4_cl. lia.
  - intros x b d Ha Hd. rewrite w4_cl.
    destruct (w4_assign_view x b Ha) as [[-> | [-> | ->]] _].
    + rewrite w4_l0 in Hd. injection Hd as Hd. lia.
    + rewrite w4_l1 in Hd. injection Hd as Hd. lia.
    + rewrite w4_l2 in Hd. injection Hd as Hd. lia.
  - intros d Hd. rewrite w4_cl in Hd.
    assert (Hd1 : d = 1) by lia. subst d.
    exists 0.
    split; [exists true; exact w4_a0 | split; [exact w4_l0 | exact w4_r0]].
Qed.

Lemma w4_stable : stable_view w4_view.
Proof. split; [exact w4_grounded | exact w4_closed]. Qed.

(** *** reason bookkeeping. *)

Lemma w4_reason_cases : forall x c,
  reason_of w4_view x = Some c -> x = 1 /\ c = w4_reason_clause.
Proof.
  intros x c H.
  assert (E : reason_of w4_view x
              = match trail_pos (ms_core w4) x with
                | Some _ => if x =? 1 then Some w4_reason_clause else None
                | None => None
                end) by reflexivity.
  rewrite E in H.
  destruct (trail_pos (ms_core w4) x); [|discriminate].
  destruct (x =? 1) eqn:E2; [|discriminate].
  apply Z.eqb_eq in E2. split; [exact E2 | congruence].
Qed.

Lemma w4_learnt_entailed : entails_clause w4_F [Pos 1; Neg 2].
Proof.
  intros rho Hm. unfold models in Hm. rewrite Forall_forall in Hm.
  assert (H3 : clause_satisfied rho [Pos 1; Pos 3])
    by (apply Hm; right; left; reflexivity).
  assert (HC : clause_satisfied rho [Neg 3; Neg 2; Pos 1])
    by (apply Hm; right; right; left; reflexivity).
  destruct H3 as [l3 [Hin3 Hev3]]. simpl in Hin3.
  destruct Hin3 as [<-|[<-|[]]].
  - exists (Pos 1). split; [left; reflexivity | exact Hev3].
  - destruct HC as [lc [Hinc Hevc]]. simpl in Hinc.
    destruct Hinc as [<-|[<-|[<-|[]]]].
    + simpl in Hevc, Hev3. apply negb_true_iff in Hevc. congruence.
    + exists (Neg 2). split; [right; left; reflexivity | exact Hevc].
    + exists (Pos 1). split; [left; reflexivity | exact Hevc].
Qed.

Lemma w4_reasons_entailed : reasons_entailed w4_F w4_view.
Proof.
  intros x c H. destruct (w4_reason_cases x c H) as [_ ->].
  exact w4_learnt_entailed.
Qed.

Lemma w4_reason_injective : clause_var_injective w4_reason_clause.
Proof.
  intros l1 l2 H1 H2 Hv. unfold w4_reason_clause in H1, H2.
  simpl in H1, H2.
  (* The two literals of the clause, in the four combinations: the diagonal
     is reflexivity, the off-diagonal contradicts [Hv]. *)
  destruct H1 as [<-|[<-|[]]]; destruct H2 as [<-|[<-|[]]];
    simpl in Hv; [ reflexivity | exfalso; lia | exfalso; lia | reflexivity ].
Qed.

Lemma w4_reasons_inj : reasons_var_injective w4_view.
Proof.
  intros x c H. destruct (w4_reason_cases x c H) as [_ ->].
  exact w4_reason_injective.
Qed.

(** *** TRAIL-IMPLIED.  [F |= x1] outright: the learnt clause {x1,~x2}
    resolved with the unit {x2}. *)

Lemma w4_ti0 :
  entails_clause [[Pos 2]; [Pos 1; Pos 3]; [Neg 3; Neg 2; Pos 1]] [Pos 2].
Proof. apply entails_clause_in. left. reflexivity. Qed.

Lemma w4_ti1 :
  entails_clause [[Pos 2]; [Pos 1; Pos 3]; [Neg 3; Neg 2; Pos 1]; [Pos 0]]
                 [Pos 0].
Proof. apply entails_clause_in. right. right. right. left. reflexivity. Qed.

Lemma w4_ti2 :
  entails_clause [[Pos 2]; [Pos 1; Pos 3]; [Neg 3; Neg 2; Pos 1]; [Pos 0]]
                 [Pos 1].
Proof.
  intros rho Hm. unfold models in Hm. rewrite Forall_forall in Hm.
  assert (H2 : clause_satisfied rho [Pos 2])
    by (apply Hm; left; reflexivity).
  assert (H3 : clause_satisfied rho [Pos 1; Pos 3])
    by (apply Hm; right; left; reflexivity).
  assert (HC : clause_satisfied rho [Neg 3; Neg 2; Pos 1])
    by (apply Hm; right; right; left; reflexivity).
  destruct H2 as [l2 [Hin2 Hev2]]. simpl in Hin2. destruct Hin2 as [<-|[]].
  destruct H3 as [l3 [Hin3 Hev3]]. simpl in Hin3.
  destruct Hin3 as [<-|[<-|[]]].
  - exists (Pos 1). split; [left; reflexivity | exact Hev3].
  - destruct HC as [lc [Hinc Hevc]]. simpl in Hinc.
    destruct Hinc as [<-|[<-|[<-|[]]]].
    + simpl in Hevc, Hev3. apply negb_true_iff in Hevc. congruence.
    + simpl in Hevc, Hev2. apply negb_true_iff in Hevc. congruence.
    + exists (Pos 1). split; [left; reflexivity | exact Hevc].
Qed.

Lemma w4_trail_implied : trail_implied w4_F (ms_core w4).
Proof.
  intros i l Hi Hl.
  assert (ET : Zlength (mt_trail (ms_core w4)) = 3) by reflexivity.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2) by lia.
  destruct Hc as [-> | [-> | ->]]; subst l.
  - exact w4_ti0.
  - exact w4_ti1.
  - exact w4_ti2.
Qed.

(** *** database, watchers, heap. *)

Lemma w4_db_wf : db_wf w4_n (msolver_db w4).
Proof.
  unfold db_wf, msolver_db. simpl. split; [|split].
  - constructor; [simpl; intros [H|[H|[]]]; lia|].
    constructor; [simpl; intros [H|[]]; lia|].
    constructor; [simpl; tauto | constructor].
  - constructor; [simpl; split; [lia|reflexivity]|].
    constructor; [simpl; split; [lia|reflexivity]|].
    constructor; [simpl; split; [lia|reflexivity] | constructor].
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + simpl. unfold obj_wf. simpl. split; [|split].
      * assert (E : Zlength [2; 6] = 2) by reflexivity. lia.
      * do 2 (constructor; [unfold lit_wf_c, w4_n; lia|]). constructor.
      * vm_compute. msat_nodup.
    + simpl. unfold obj_wf. simpl. split; [|split].
      * assert (E : Zlength [7; 2; 5] = 3) by reflexivity. lia.
      * do 3 (constructor; [unfold lit_wf_c, w4_n; lia|]). constructor.
      * vm_compute. msat_nodup.
    + simpl. unfold obj_wf. simpl. split; [|split].
      * assert (E : Zlength [2; 5] = 2) by reflexivity. lia.
      * do 2 (constructor; [unfold lit_wf_c, w4_n; lia|]). constructor.
      * vm_compute. msat_nodup.
Qed.

Lemma w4_wmap : wmap_exact w4_n (msolver_db w4) (ms_wm w4).
Proof.
  split; [reflexivity|].
  intros l Hl. unfold w4_n in Hl.
  assert (Hc : l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/
               l = 6 \/ l = 7) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[-> | ->]]]]]]];
    vm_compute; apply Permutation_refl.
Qed.

Lemma w4_heap_eq :
  msolver_heap w4 = {| mh_heap := [3; 1]; mh_orderpos := [-1; 1; -1; 0] |}.
Proof. reflexivity. Qed.

Lemma w4_heap_wf : heap_wf w4_n (msolver_heap w4).
Proof.
  rewrite w4_heap_eq. unfold heap_wf, w4_n. simpl mh_heap. simpl mh_orderpos.
  split; [|split; [|split; [|split]]].
  - reflexivity.
  - msat_nodup.
  - do 2 (constructor; [lia|]). constructor.
  - intros v Hv.
    assert (EL2 : Zlength [3; 1] = 2) by reflexivity.
    assert (EP1 : Znth 1 [-1; 1; -1; 0] (-1) = 1) by reflexivity.
    assert (EP3 : Znth 3 [-1; 1; -1; 0] (-1) = 0) by reflexivity.
    assert (Hc : v = 0 \/ v = 1 \/ v = 2 \/ v = 3) by lia.
    destruct Hc as [-> | [-> | [-> | ->]]].
    + left. reflexivity.
    + right. split; [lia | reflexivity].
    + left. reflexivity.
    + right. split; [lia | reflexivity].
  - intros i Hi.
    assert (EL2 : Zlength [3; 1] = 2) by reflexivity.
    assert (Hc : i = 0 \/ i = 1) by lia.
    destruct Hc as [-> | ->]; reflexivity.
Qed.

Lemma w4_F_wf : cnf_wf w4_n w4_F.
Proof.
  split; [unfold w4_n; lia|].
  do 3 (constructor;
    [ repeat (constructor;
              [unfold literal_wf, var_in_range, w4_n; simpl; lia|]);
      constructor |]).
  constructor.
Qed.

Lemma w4_db_matches : db_matches_cnf w4_F w4.
Proof.
  unfold db_matches_cnf.
  assert (E : db_clauses (ms_prob w4)
              = [[Pos 1; Pos 3]; [Neg 3; Pos 1; Neg 2]]) by reflexivity.
  rewrite E. constructor; [|constructor; [|constructor]].
  - exists [Pos 1; Pos 3].
    split; [right; left; reflexivity | apply Permutation_refl].
  - (* c2 was reordered by the level-0 watch move: a permutation *)
    exists [Neg 3; Neg 2; Pos 1].
    split; [right; right; left; reflexivity|].
    apply perm_skip. apply perm_swap.
Qed.

Lemma w4_db_implied : db_implied w4_F w4.
Proof.
  unfold db_implied.
  assert (E : db_clauses (ms_learnt w4) = [[Pos 1; Neg 2]]) by reflexivity.
  rewrite E. constructor; [exact w4_learnt_entailed | constructor].
Qed.

Lemma w4_db_complete : db_complete w4_F w4.
Proof.
  intros c Hc. vm_compute in Hc.
  assert (E : db_clauses (ms_prob w4)
              = [[Pos 1; Pos 3]; [Neg 3; Pos 1; Neg 2]]) by reflexivity.
  destruct Hc as [<-|[<-|[<-|[]]]].
  - (* the unit clause: never in the database, root-satisfied instead *)
    right. exists (Pos 2).
    split; [left; reflexivity|]. split; reflexivity.
  - left. exists [Pos 1; Pos 3].
    split; [rewrite E; left; reflexivity | apply Permutation_refl].
  - left. exists [Neg 3; Pos 1; Neg 2].
    split; [rewrite E; right; left; reflexivity|].
    apply perm_skip. apply perm_swap.
Qed.

Lemma w4_binary_out : ~ In (ms_binary w4) (map fst (msolver_db w4)).
Proof. vm_compute. intros [H|[H|[H|[]]]]; lia. Qed.

Lemma w4_learnt_in : In (40, w4_learnt_obj) (msolver_db w4).
Proof. vm_compute. right. right. left. reflexivity. Qed.

Lemma w4_reasons_mem :
  reasons_match w4_n (ms_core w4) (msolver_db w4)
                (ms_reason_words w4) (ms_reason_of w4).
Proof.
  intros v Hv. unfold w4_n in Hv.
  assert (Hc : v = 0 \/ v = 1 \/ v = 2 \/ v = 3) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]];
    [reflexivity | | reflexivity | reflexivity].
  assert (EW : Znth 1 (ms_reason_words w4) 0 = 40) by reflexivity.
  rewrite EW. unfold reason_word_ok. simpl.
  split; [discriminate |].
  exists w4_learnt_obj. split; [exact w4_learnt_in | reflexivity].
Qed.

Lemma w4_reason_head : reason_head_ok w4.
Proof.
  intros v co Hv Htag Hnz Hin.
  assert (ES : ms_size w4 = 4) by reflexivity.
  assert (Hc : v = 0 \/ v = 1 \/ v = 2 \/ v = 3) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]];
    [ exfalso; apply Hnz; reflexivity
    |
    | exfalso; apply Hnz; reflexivity
    | exfalso; apply Hnz; reflexivity ].
  vm_compute in Hin.
  destruct Hin as [Heq|[Heq|[Heq|[]]]].
  - exfalso. injection Heq as Heq _. lia.
  - exfalso. injection Heq as Heq _. lia.
  - (* the pointer components are syntactically equal, so [injection] keeps
       only the object equation *)
    injection Heq as Heq. subst co. reflexivity.
Qed.

Lemma w4_reason_bin : binary_reason_same_level w4.
Proof.
  intros v Hv Ht. exfalso.
  assert (ES : ms_size w4 = 4) by reflexivity.
  assert (Hc : v = 0 \/ v = 1 \/ v = 2 \/ v = 3) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute in Ht; discriminate.
Qed.


(** *** the mid-loop bundle (S9's [msolver_inv_assuming]), satisfied by the
    same memory REGARDLESS of the root field -- that indifference is
    precisely what makes it applicable while [s->root_level] is stale. *)

Lemma w4_assuming_gen : forall r A_arr A_proc,
  0 <= r ->
  Forall (literal_wf w4_n) A_arr ->
  incl [Pos 0] A_proc ->
  incl A_proc A_arr ->
  Forall (assump_true_at_root (ms_core w4) 1) A_proc ->
  msolver_inv_assuming w4_n w4_F A_arr A_proc (w4_at r).
Proof.
  intros r A_arr A_proc Hr HAwf Hp0 Hpa Hps.
  constructor.
  - reflexivity.
  - unfold w4_n. lia.
  - unfold solver_shape, w4_at. simpl.
    repeat split; try reflexivity; try lia; try (right; reflexivity).
  - exact w4_F_wf.
  - exact HAwf.
  - exact w4_trail_wf.
  - assert (E : Zlength (mt_lim (ms_core (w4_at r))) = 1) by reflexivity.
    unfold w4_n. lia.
  - exists [Pos 0]. split; [reflexivity | exact Hp0].
  - exact Hpa.
  - exact Hps.
  - exact w4_stable.
  - exact w4_reasons_entailed.
  - exact w4_reasons_inj.
  - exact w4_trail_implied.
  - exact w4_db_wf.
  - exact w4_db_matches.
  - exact w4_db_implied.
  - exact w4_db_complete.
  - unfold learnt_db, w4_at, w4. simpl. repeat constructor.
  - unfold prob_db, w4_at, w4. simpl. repeat constructor.
  - exact w4_binary_out.
  - exact w4_reasons_mem.
  - exact w4_reason_head.
  - exact w4_reason_bin.
  - exact w4_wmap.
  - unfold solver_tags_clear, w4_at. simpl. repeat constructor.
  - exact w4_heap_wf.
  - exact msat_fp32_zero_nonnegative.
  - unfold msolver_seed_ok. apply msat_fp64_zero_finite.
Qed.

(** Route 1 of the assumption loop: enlarge the caller's array with a second
    assumption
    [Neg 2] whose negation [Pos 2] is already on the trail (index 0).  The
    processed prefix stays [[Pos 0]]: the CURSOR element [Neg 2] is NOT in
    it.  [F /\ x0 /\ ~x2] is unsatisfiable because [F |= x2]. *)
Example w4_false_assumption_unsat :
  cnf_unsat w4_n (cnf_with_units w4_F [Pos 0; Neg 2]).
Proof.
  apply (assuming_false_assumption_unsat w4_n w4_F [Pos 0; Neg 2] [Pos 0] w4
           (Neg 2) 0).
  - unfold w4. apply w4_assuming_gen.
    + lia.
    + do 2 (constructor;
              [unfold literal_wf, var_in_range, w4_n; simpl; lia|]).
      constructor.
    + apply incl_refl.
    + intros y Hy. destruct Hy as [<-|[]]. left. reflexivity.
    + constructor; [|constructor].
      split; [reflexivity|].
      assert (E : Znth (literal_var (Pos 0)) (mt_levels (ms_core w4)) 0 = 1)
        by reflexivity.
      lia.
  - right. left. reflexivity.
  - assert (E : Zlength (mt_trail (ms_core w4)) = 3) by reflexivity. lia.
  - reflexivity.
Qed.


Example w0_no_seed_shadow : ~ msolver_seed_shadow w0.
Proof. apply msat_fp64_zero_no_shadow. reflexivity. Qed.

(** [w0] reseeded with MiniSat's default.  Only the seed field differs, so
    the strong bundle transfers and [w0] itself -- together with every
    endgame that flows through it -- is untouched. *)
Definition w0s : msolver := msolver_reseed w0 msat_fp64_seed.

Example w0s_inv : msolver_inv w0_n w0_F [] [] w0s.
Proof.
  apply msolver_inv_reseed; [exact w0_inv | exact msat_fp64_seed_finite].
Qed.

Example w0s_seed_shadow : msolver_seed_shadow w0s.
Proof. apply msat_fp64_seed_shadow. reflexivity. Qed.

Example w0s_normal_root : solver_normal_root w0_n w0_F w0s.
Proof.
  unfold solver_normal_root.
  split; [exact w0s_inv|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; reflexivity.
Qed.

Example w0s_operational_root : solver_operational_root w0_n w0_F w0s.
Proof. left. exact w0s_normal_root. Qed.

Theorem solver_solve_pre_pure_inhabited :
  solver_query_entry w0_n w0_F w0s /\ msolver_seed_shadow w0s.
Proof.
  split; [apply solver_operational_root_query_entry__solve; exact w0s_operational_root
         | exact w0s_seed_shadow].
Qed.


Example w3s_weak : msolver_inv_weak w3_n w3_F [] [] (msolver_reseed w3 msat_fp64_seed).
Proof.
  apply msolver_inv_weak_reseed; [exact w3_weak | exact msat_fp64_seed_finite].
Qed.

Example w3s_seed_shadow : msolver_seed_shadow (msolver_reseed w3 msat_fp64_seed).
Proof. apply msat_fp64_seed_shadow. reflexivity. Qed.

