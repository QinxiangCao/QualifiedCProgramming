Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import Lia.

Local Open Scope sets.

Section SCC.

Context {G V E: Type}
        (g: G)
        `{pg: Graph G V E}
        `{gv: GValid G}
        `{stepvalid: StepValid G V E}.

(* ================================================================= *)
(* 1. Mutually Reachable                                             *)
(* ================================================================= *)

Definition mutually_reachable (u v: V) : Prop :=
  reachable g u v /\ reachable g v u.

Lemma mutually_reachable_refl : forall u,
  vvalid g u -> mutually_reachable u u.
Proof.
  intros u Hu.
  unfold mutually_reachable, reachable.
  split; reflexivity.
Qed.

Lemma mutually_reachable_sym : forall u v,
  mutually_reachable u v -> mutually_reachable v u.
Proof.
  unfold mutually_reachable; tauto.
Qed.

Lemma mutually_reachable_trans : forall u v w,
  mutually_reachable u v -> mutually_reachable v w -> mutually_reachable u w.
Proof.
  intros u v w [Huv Hvu] [Hvw Hwv].
  unfold mutually_reachable.
  split; unfold reachable in *;
  etransitivity; eauto.
Qed.

(* ================================================================= *)
(* 2. Strongly Connected Component                                   *)
(* ================================================================= *)

Definition is_SCC (s: V -> Prop) : Prop :=
  (exists v, s v /\ vvalid g v) /\
  (forall u v, s u -> s v -> mutually_reachable u v) /\
  (forall u v, s u -> vvalid g v -> mutually_reachable u v -> s v).

Lemma is_SCC_vvalid : forall s u,
  is_SCC s -> s u -> vvalid g u.
Proof.
  intros s u [Hnonempty [Hinternal Hmaximal]] Hsu.
  destruct Hnonempty as [w [Hsw Hvw]].
  destruct (classic (u = w)).
  - subst; auto.
  - apply Hinternal with u w in Hsu; [|exact Hsw].
    destruct Hsu as [Huw _].
    apply reachable_vvalid with (x := u) (y := w) in Huw; auto.
    destruct Huw; auto.
Qed.

Lemma is_SCC_closed_under_mr : forall s u v,
  is_SCC s -> s u -> mutually_reachable u v -> s v.
Proof.
  intros s u v Hscc Hsu Hmr.
  destruct Hscc as [Hnonempty [Hinternal Hmaximal]].
  destruct (classic (u = v)) as [Heq|Hneq].
  - subst; exact Hsu.
  - assert (Hvv : vvalid g v).
    { destruct Hmr as [Huv _].
      apply reachable_vvalid with (x := u) (y := v) in Huv; auto.
      destruct Huv; auto. }
    apply Hmaximal with u; auto.
Qed.

Lemma is_SCC_maximal : forall s1 s2,
  is_SCC s1 -> is_SCC s2 ->
  (forall v, s1 v -> s2 v) -> (forall v, s2 v -> s1 v).
Proof.
  intros s1 s2 Hscc1 Hscc2 Hsubset v Hsv.
  destruct Hscc1 as [Hnonempty1 [Hinternal1 Hmaximal1]].
  destruct Hnonempty1 as [u [Hsu Hvu]].
  assert (Hsu2 : s2 u) by (apply Hsubset; auto).
  assert (Hmr : mutually_reachable u v)
    by (destruct Hscc2 as [_ [Hinternal2 _]]; eapply Hinternal2; eauto).
  assert (Hvv : vvalid g v) by (eapply is_SCC_vvalid; eauto).
  apply Hmaximal1 with u; auto.
Qed.

(* ================================================================= *)
(* 3. SCC Partition                                                  *)
(* ================================================================= *)

Definition scc_partition (sccs: list (V -> Prop)) : Prop :=
  (forall v, vvalid g v -> exists s, In s sccs /\ s v) /\
  (forall s, In s sccs -> is_SCC s) /\
  (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2).

Lemma mutually_reachable_same_SCC : forall u v sccs,
  vvalid g u -> scc_partition sccs -> mutually_reachable u v ->
  exists s, In s sccs /\ s u /\ s v.
Proof.
  intros u v sccs Hvu Hpart Hmr.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  destruct (Hcover u Hvu) as [su [Hin_su Hsu]].
  exists su; split; [auto|split; auto].
  apply (is_SCC_closed_under_mr su u v); [apply Hsccs; auto|auto|auto].
Qed.

Context {finitegraph: FiniteGraph G V E}.
Context {Hgvalid: gvalid g}.

Definition equiv_class (v: V) : V -> Prop :=
  fun w => vvalid g w /\ mutually_reachable v w.

Lemma equiv_class_is_SCC : forall v,
  vvalid g v -> is_SCC (equiv_class v).
Proof.
  intros v Hv.
  split.
  - exists v; split.
    + unfold equiv_class; split; auto.
      apply mutually_reachable_refl; auto.
    + auto.
  - split.
    + intros u w [Hvu Hmru] [Hvw Hmrw].
      apply mutually_reachable_trans with v; auto.
      apply mutually_reachable_sym; auto.
    + intros u w [Hvu Hmru] Hvw Hmruw.
      unfold equiv_class.
      split; auto.
      apply mutually_reachable_trans with u; auto.
Qed.

Lemma build_scc_partition_aux : forall (vertices: list V),
  exists sccs,
    (forall v, vvalid g v -> In v vertices -> exists s, In s sccs /\ s v) /\
    (forall s, In s sccs -> is_SCC s) /\
    (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2).
Proof.
  induction vertices as [|a rest IH].
  - exists nil; simpl; split; [|split].
    + intros v Hv Hin. inversion Hin.
    + intros s Hin. inversion Hin.
    + intros s1 s2 v Hin1 Hin2. inversion Hin1.
  - destruct IH as [sccs_rest [Hcover_rest [Hsccs_rest Hdisjoint_rest]]].
    destruct (classic (exists s, In s sccs_rest /\ s a)).
    + exists sccs_rest; split; [|split]; auto.
      intros v Hv Hin.
      destruct Hin as [Hva|Hrest'].
      * subst v. destruct H as [s [Hin_s Hsa]].
        exists s; split; auto.
      * apply Hcover_rest; auto.
    + destruct (classic (vvalid g a)).
      * exists (equiv_class a :: sccs_rest).
        split; [|split].
        -- intros v Hv Hin.
           destruct Hin as [Hva|Hrest'].
           ++ subst v.
              exists (equiv_class a); split; [left; reflexivity|].
              unfold equiv_class; split; auto.
              apply mutually_reachable_refl; auto.
           ++ destruct (Hcover_rest v Hv Hrest') as [s [Hin_s Hsv]].
              exists s; split; auto. right; auto.
        -- intros s Hin.
           destruct Hin as [Hin|Hin].
           ++ subst s. apply equiv_class_is_SCC; auto.
           ++ apply Hsccs_rest; auto.
        -- intros s1 s2 v Hind Hind' Hv1 Hv2.
           apply in_inv in Hind; apply in_inv in Hind'.
           destruct Hind as [Heq1|Hin1]; destruct Hind' as [Heq2|Hin2].
           ++ subst s1; subst s2; auto.
           ++ subst s1; exfalso; apply H.
              { unfold equiv_class in Hv1; destruct Hv1 as [_ Hmr0].
                assert (Hscc_s2 : is_SCC s2) by (apply Hsccs_rest; auto).
                assert (Hs2a : s2 a).
                { assert (Hvv_v : vvalid g v) by (eapply is_SCC_vvalid; eauto).
                  apply (is_SCC_closed_under_mr s2 v a); auto.
                  apply mutually_reachable_sym; auto. }
                exists s2; split; auto. }
           ++ subst s2; exfalso; apply H.
              { unfold equiv_class in Hv2; destruct Hv2 as [_ Hmr0].
                assert (Hscc_s1 : is_SCC s1) by (apply Hsccs_rest; auto).
                assert (Hs1a : s1 a).
                { assert (Hvv_v : vvalid g v) by (eapply is_SCC_vvalid; eauto).
                  apply (is_SCC_closed_under_mr s1 v a); auto.
                  apply mutually_reachable_sym; auto. }
                exists s1; split; auto. }
           ++ eapply Hdisjoint_rest; eauto.
      * exists sccs_rest; split; [|split]; auto.
        intros v Hv Hin.
        destruct Hin as [Hva|Hrest'].
        -- subst v. exfalso; auto.
        -- apply Hcover_rest; auto.
Qed.

Lemma listV_contains_valid (v : V) : vvalid g v -> In v (listV g).
Proof.
  intro Hv.
  apply (finite_vertices g Hgvalid v); auto.
Qed.

Theorem scc_partition_exists : exists sccs, scc_partition sccs.
Proof.
  destruct (build_scc_partition_aux (listV g)) as [sccs [Hcover [Hsccs Hdisjoint]]].
  exists sccs.
  split; [|split].
  - intros v Hv. apply (Hcover v Hv). apply listV_contains_valid; auto.
  - apply Hsccs.
  - apply Hdisjoint.
Qed.

(* ================================================================= *)
(* 4. Condensation DAG Acyclicity                                    *)
(* ================================================================= *)

Definition condensation_edge (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ step g u v.

Inductive condensation_reachable (sccs: list (V -> Prop)) : (V -> Prop) -> (V -> Prop) -> Prop :=
| cr_edge : forall s1 s2,
    condensation_edge sccs s1 s2 ->
    condensation_reachable sccs s1 s2
| cr_trans : forall s1 s2 s3,
    condensation_reachable sccs s1 s2 ->
    condensation_reachable sccs s2 s3 ->
    condensation_reachable sccs s1 s3.

Lemma condensation_reachable_In : forall sccs s1 s2,
  condensation_reachable sccs s1 s2 ->
  In s1 sccs /\ In s2 sccs.
Proof.
  intros sccs s1 s2 Hcr.
  induction Hcr as [s1' s2' Hedge | s1' s2' s3' Hcr1 IHcr1 Hcr2 IHcr2].
  - destruct Hedge as [Hin1 [Hin2 _]]; split; auto.
  - destruct IHcr1 as [Hin1 _].
    destruct IHcr2 as [_ Hin2].
    split; auto.
Qed.

Lemma condensation_reachable_implies_reachable : forall sccs s1 s2,
  scc_partition sccs ->
  condensation_reachable sccs s1 s2 ->
  s1 <> s2 ->
  exists u v, s1 u /\ s2 v /\ reachable g u v.
Proof.
  intros sccs s1 s2 Hpart Hcr Hneq.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  induction Hcr as [s1 s2 Hedge | s1 s2 s3 Hcr1 IH1 Hcr2 IH2].
  - destruct Hedge as [_ [_ [_ [u [v [Hu [Hv Hstep]]]]]]].
    exists u, v.
    split; [|split]; auto.
    apply step_rt; auto.
  - destruct (classic (s1 = s2)) as [Heq12|Hneq12].
    + subst s2. apply IH2; auto.
    + destruct (classic (s2 = s3)) as [Heq23|Hneq23].
      * subst s3. apply IH1; auto.
      * destruct (IH1 Hneq12) as [u1 [v2 [Hu1 [Hv2 Hreach12]]]].
        destruct (IH2 Hneq23) as [u2 [v3 [Hu2 [Hv3 Hreach23]]]].
        apply condensation_reachable_In in Hcr1 as [_ Hin2].
        apply Hsccs in Hin2; destruct Hin2 as [_ [Hinternal2 _]].
        assert (Hmr2 : mutually_reachable v2 u2) by (apply Hinternal2; auto).
        exists u1, v3.
        split; [|split]; auto.
        unfold reachable in *.
        etransitivity; [apply Hreach12|].
        destruct Hmr2 as [Hv2u2 _].
        etransitivity; [apply Hv2u2|].
        apply Hreach23.
Qed.

Theorem no_cycle_between_different_SCCs : forall sccs,
  scc_partition sccs ->
  ~ exists s1 s2, In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
    (exists u1 v1, s1 u1 /\ s2 v1 /\ reachable g u1 v1) /\
    (exists u2 v2, s2 u2 /\ s1 v2 /\ reachable g u2 v2).
Proof.
  intros sccs Hpart.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  unfold not; intros Hcycle.
  destruct Hcycle as [s1 [s2 [Hin1 [Hin2 [Hneq [Hforward Hback]]]]]].

  destruct Hforward as [u1 [v1 [Hsu1 [Hsv1 Hreach_fwd]]]].
  destruct Hback as [u2 [v2 [Hsu2 [Hsv2 Hreach_bwd]]]].

  pose proof Hsccs _ Hin1 as Hscc1_full.
  pose proof Hsccs _ Hin2 as Hscc2_full.

  destruct Hscc1_full as [_ [Hinternal1 _]].
  destruct Hscc2_full as [_ [Hinternal2 _]].

  assert (Hmr_s2 : mutually_reachable v1 u2) by (apply Hinternal2; auto).
  assert (Hmr_s1 : mutually_reachable v2 u1) by (apply Hinternal1; auto).

  assert (Hmr_u1u2 : mutually_reachable u1 u2).
  { unfold mutually_reachable.
    split; unfold reachable in *.
    - etransitivity; [apply Hreach_fwd|].
      destruct Hmr_s2. exact H.
    - etransitivity; [apply Hreach_bwd|].
      destruct Hmr_s1. exact H. }

  assert (Hs1u2 : s1 u2).
  { apply (is_SCC_closed_under_mr s1 u1 u2 (Hsccs _ Hin1)); auto. }

  apply Hneq.
  eapply Hdisjoint with (v := u2); eauto.
Qed.

Theorem condensation_is_acyclic : forall sccs s1 s2,
  scc_partition sccs ->
  condensation_edge sccs s1 s2 ->
  ~ condensation_reachable sccs s2 s1.
Proof.
  intros sccs s1 s2 Hpart Hedge Hback.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  destruct Hedge as [Hin1 [Hin2 [Hneq [u [v [Hu [Hv Hstep]]]]]]].
  assert (Hfwd : reachable g u v) by (apply step_rt; auto).
  assert (Hneq_sym : s2 <> s1) by (intro Heq; apply Hneq; symmetry; auto).
  destruct (condensation_reachable_implies_reachable sccs s2 s1
    (conj Hcover (conj Hsccs Hdisjoint)) Hback Hneq_sym)
    as [u' [v' [Hu' [Hv' Hback_reach]]]].
  pose proof (Hsccs _ Hin2) as Hscc2_full.
  destruct Hscc2_full as [_ [Hinternal2 _]].
  assert (Hmr2 : mutually_reachable v u') by (apply Hinternal2; auto).
  pose proof (Hsccs _ Hin1) as Hscc1_full.
  destruct Hscc1_full as [_ [Hinternal1 _]].
  assert (Hmr1 : mutually_reachable v' u) by (apply Hinternal1; auto).
  assert (Hcycle : mutually_reachable u u').
  { unfold mutually_reachable.
    split; unfold reachable in *.
    - etransitivity; [apply Hfwd|].
      destruct Hmr2 as [Hvu' _]. exact Hvu'.
    - etransitivity; [apply Hback_reach|].
      destruct Hmr1 as [Hv'u _]. exact Hv'u. }
  assert (Hu'_in_s1 : s1 u').
  { exact (is_SCC_closed_under_mr s1 u u' (Hsccs _ Hin1) Hu Hcycle). }
  apply Hneq.
  eapply Hdisjoint with (v := u'); eauto.
Qed.

Lemma vertex_reachable_condensation : forall sccs s1 s2 u v,
  scc_partition sccs ->
  In s1 sccs -> In s2 sccs ->
  s1 u -> s2 v ->
  reachable g u v ->
  s1 = s2 \/ condensation_reachable sccs s1 s2.
Proof.
  intros sccs s1 s2 u v Hpart Hin1 Hin2 Hsu Hsv Hreach.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  unfold reachable in Hreach.
  destruct Hreach as [n Hreach].
  revert u v Hreach s1 Hin1 Hsu s2 Hin2 Hsv.
  induction n as [|n IH]; intros u v Hreach s1 Hin1 Hsu s2 Hin2 Hsv.
  - simpl in Hreach; compute in Hreach.
    destruct Hreach; subst.
    left; eapply Hdisjoint; eauto.
  - simpl in Hreach; compute in Hreach.
    sets_unfold in Hreach.
    destruct Hreach as [w [Hstep Hrest]].
    assert (Hvw : vvalid g w) by (apply step_vvalid in Hstep; destruct Hstep; auto).
    destruct (Hcover w Hvw) as [sw [Hin_sw Hsw]].
    destruct (classic (sw = s1)) as [Heq_same|Hneq].
    + subst sw; apply IH with (u := w) (v := v) (s1 := s1); auto.
    + assert (Hedge : condensation_edge sccs s1 sw).
      { unfold condensation_edge.
        split; [exact Hin1|].
        split; [exact Hin_sw|].
        split; [intro H; apply Hneq; symmetry; exact H|].
        exists u, w; split; [exact Hsu|]; split; [exact Hsw|]; exact Hstep. }
      destruct (IH w v Hrest sw Hin_sw Hsw s2 Hin2 Hsv) as [Heq | Hcr].
      * subst sw; right; apply cr_edge; exact Hedge.
      * right; apply cr_trans with (s2 := sw); [apply cr_edge; exact Hedge| exact Hcr].
Qed.

Corollary vertex_reachable_rev_condensation : forall sccs s1 s2 u v,
  scc_partition sccs ->
  In s1 sccs -> In s2 sccs ->
  s1 u -> s2 v ->
  reachable g v u ->
  s1 = s2 \/ condensation_reachable sccs s2 s1.
Proof.
  intros.
  destruct (vertex_reachable_condensation sccs s2 s1 v u H H1 H0 H3 H2 H4) as [Heq | Hcr].
  - left; symmetry; auto.
  - right; exact Hcr.
Qed.

(* ================================================================= *)
(* 5. Reversed Graph Reachability (for Kosaraju)                     *)
(* ================================================================= *)

Definition step_rev (x y: V) : Prop :=
  step g y x.

Inductive reachable_rev (u : V) : V -> Prop :=
| rr_refl : reachable_rev u u
| rr_step v w : step_rev u v -> reachable_rev v w -> reachable_rev u w.

Lemma reachable_rev_intro : forall x y,
  reachable g y x -> reachable_rev x y.
Proof.
  intros x y H.
  unfold reachable in H.
  pose proof (nsteps_nsteps'_indexed_union (step g) : (clos_refl_trans (step g) == ⋃ (nsteps' (step g)))%sets) as Hconv.
  apply Hconv in H.
  destruct H as [n H].
  revert x y H; induction n as [|n IH]; intros x y H.
  - simpl in H; destruct H; subst; constructor.
  - simpl in H; sets_unfold in H; destruct H as [w [Hrest Hstep]].
    econstructor 2 with (v := w).
    + unfold step_rev; exact Hstep.
    + apply IH with (x := w); exact Hrest.
Qed.

Lemma reachable_rev_step_reachable_rev : forall x y z,
  reachable_rev x y -> step_rev y z -> reachable_rev x z.
Proof.
  intros x y z H.
  revert z.
  induction H using reachable_rev_ind; intros z Hstep.
  - econstructor 2 with (v := z); [exact Hstep | constructor].
  - econstructor 2 with (v := v); [exact H | apply IHreachable_rev; exact Hstep].
Qed.

Lemma reachable_iff_reachable_rev : forall x y,
  reachable g x y <-> reachable_rev y x.
Proof.
  split.
  - intros H; apply reachable_rev_intro; auto.
  - intros H; induction H using reachable_rev_ind.
    + unfold reachable; reflexivity.
    + match goal with
      | Hstep : step_rev _ _ |- _ => rename Hstep into Hstep_edge
      end.
      eapply reachable_step_reachable; [exact IHreachable_rev | unfold step_rev; exact Hstep_edge].
Qed.

Definition mutually_reachable_rev (u v: V) : Prop :=
  reachable_rev u v /\ reachable_rev v u.

Lemma mutually_reachable_rev_equiv : forall u v,
  mutually_reachable_rev u v <-> mutually_reachable u v.
Proof.
  unfold mutually_reachable_rev, mutually_reachable.
  split; intros [H1 H2]; split.
  - apply (proj2 (reachable_iff_reachable_rev u v)); exact H2.
  - apply (proj2 (reachable_iff_reachable_rev v u)); exact H1.
  - apply (proj1 (reachable_iff_reachable_rev v u)); exact H2.
  - apply (proj1 (reachable_iff_reachable_rev u v)); exact H1.
Qed.

(* ================================================================= *)
(* 6. Head and Tail SCCs in the Condensation DAG                     *)
(* ================================================================= *)

Definition is_tail_SCC (sccs: list (V -> Prop)) (s: V -> Prop) : Prop :=
  In s sccs /\
  forall s', condensation_edge sccs s s' -> False.

Definition is_head_SCC (sccs: list (V -> Prop)) (s: V -> Prop) : Prop :=
  In s sccs /\
  forall s', condensation_edge sccs s' s -> False.

Lemma tail_SCC_no_outgoing : forall sccs s u v,
  scc_partition sccs ->
  is_tail_SCC sccs s -> s u -> step g u v -> s v.
Proof.
  intros sccs s u v Hpart [Hin Hno_out] Hsu Hstep.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  destruct Hstep as [e Hstep].
  destruct (classic (s v)) as [|Hnv]; auto.
  assert (Hvv : vvalid g v) by (eapply step_vvalid2; eauto).
  destruct (Hcover v Hvv) as [s' [Hin' Hsv]].
  destruct (classic (s' = s)) as [Heq|Hneq]; [subst; tauto|].
  exfalso; apply Hno_out with (s' := s').
  unfold condensation_edge.
  repeat split; auto.
  exists u, v; split; [|split]; auto.
  exists e; auto.
Qed.

Lemma tail_SCC_closed_under_reachable : forall sccs s u v,
  scc_partition sccs ->
  is_tail_SCC sccs s -> s u -> reachable g u v -> s v.
Proof.
  intros sccs s u v Hpart Htail Hsu Hreach.
  unfold reachable in Hreach.
  destruct Hreach as [n Hreach].
  revert u v Hreach Hsu.
  induction n as [|n IH]; intros u v Hreach Hsu.
  - simpl in Hreach.
    destruct Hreach; subst; auto.
  - simpl in Hreach.
    sets_unfold in Hreach.
    destruct Hreach as [w [Hstep Hrest]].
    apply IH with (u := w); auto.
    eapply tail_SCC_no_outgoing; eauto.
Qed.

Lemma head_SCC_no_incoming : forall sccs s v u,
  scc_partition sccs ->
  is_head_SCC sccs s -> s v -> step g u v -> s u.
Proof.
  intros sccs s v u Hpart [Hin Hno_in] Hsv Hstep.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  destruct Hstep as [e Hstep].
  destruct (classic (s u)) as [|Hnu]; auto.
  assert (Hvu : vvalid g u) by (eapply step_vvalid1; eauto).
  destruct (Hcover u Hvu) as [s' [Hin' Hsu]].
  destruct (classic (s' = s)) as [Heq|Hneq]; [subst; tauto|].
  exfalso; apply Hno_in with (s' := s').
  unfold condensation_edge.
  repeat split; auto.
  exists u, v; split; [|split]; auto.
  exists e; auto.
Qed.

Lemma head_SCC_closed_under_reachable : forall sccs s u v,
  scc_partition sccs ->
  is_head_SCC sccs s -> s v -> reachable g u v -> s u.
Proof.
  intros sccs s u v Hpart Hhead Hsv Hreach.
  unfold reachable in Hreach.
  pose proof (nsteps_nsteps'_indexed_union (step g) u v) as Hconv.
  apply Hconv in Hreach.
  destruct Hreach as [n' Hreach].
  clear Hconv.
  revert u v Hreach Hsv.
  induction n' as [|n' IH]; intros u v Hreach Hsv.
  - simpl in Hreach.
    destruct Hreach; subst; auto.
  - simpl in Hreach.
    sets_unfold in Hreach.
    destruct Hreach as [w [Hreach_w Hstep]].
    apply (IH u w Hreach_w).
    eapply head_SCC_no_incoming; eauto.
Qed.

Lemma reachable_stays_in_scc_is_tail : forall sccs s u,
  scc_partition sccs ->
  In s sccs ->
  s u ->
  (forall v, reachable g u v -> s v) ->
  is_tail_SCC sccs s.
Proof.
  intros sccs s u Hpart Hin Hsu Hreach_stay.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  split; [exact Hin|].
  intros s' Hedge.
  destruct Hedge as [Hin1 [Hin2 [Hneq [x [y [Hsx [Hsy Hstep]]]]]]].
  destruct (Hsccs s Hin) as [Hnonempty [Hinternal Hmaximal]].
  pose proof (Hinternal u x Hsu Hsx) as Hmut.
  destruct Hmut as [Hrux _].
  assert (Hruy : reachable g u y).
  { eapply reachable_step_reachable; [exact Hrux|]. exact Hstep. }
  assert (Hsy' : s y) by (apply Hreach_stay; auto).
  apply Hneq; eapply Hdisjoint with (v := y); eauto.
Qed.

Lemma reachable_stays_in_scc_is_head : forall sccs s v,
  scc_partition sccs ->
  In s sccs ->
  s v ->
  (forall u, reachable g u v -> s u) ->
  is_head_SCC sccs s.
Proof.
  intros sccs s v Hpart Hin Hsv Hreach_stay.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  split; [exact Hin|].
  intros s' Hedge.
  destruct Hedge as [Hin1 [Hin2 [Hneq [x [y [Hsx [Hsy Hstep]]]]]]].
  destruct (Hsccs s Hin) as [Hnonempty [Hinternal Hmaximal]].
  pose proof (Hinternal v y Hsv Hsy) as Hmut.
  destruct Hmut as [_ Hryv].
  assert (Hrxv : reachable g x v).
  { eapply step_reachable_reachable; [exact Hstep|]. exact Hryv. }
  assert (Hsx' : s x) by (apply Hreach_stay; auto).
  apply Hneq; eapply Hdisjoint with (v := x); eauto.
Qed.

Lemma tail_scc_iff_reachable_stays : forall sccs s u,
  scc_partition sccs ->
  In s sccs ->
  s u ->
  (is_tail_SCC sccs s <-> forall v, reachable g u v -> s v).
Proof.
  intros sccs s u Hpart Hin Hsu.
  split.
  - intros Htail v Hreach.
    eapply tail_SCC_closed_under_reachable; eauto.
  - intros Hstay.
    eapply reachable_stays_in_scc_is_tail; eauto.
Qed.

Lemma head_scc_iff_reachable_stays : forall sccs s v,
  scc_partition sccs ->
  In s sccs ->
  s v ->
  (is_head_SCC sccs s <-> forall u, reachable g u v -> s u).
Proof.
  intros sccs s v Hpart Hin Hsv.
  split.
  - intros Hhead u Hreach.
    eapply head_SCC_closed_under_reachable; eauto.
  - intros Hstay.
    eapply reachable_stays_in_scc_is_head; eauto.
Qed.

Definition condensation_edge_rev (sccs: list (V -> Prop)) (s1 s2: V -> Prop) : Prop :=
  In s1 sccs /\ In s2 sccs /\ s1 <> s2 /\
  exists u v, s1 u /\ s2 v /\ step_rev u v.

Lemma condensation_edge_rev_iff : forall sccs s1 s2,
  condensation_edge_rev sccs s1 s2 <-> condensation_edge sccs s2 s1.
Proof.
  unfold condensation_edge_rev, condensation_edge, step_rev.
  split.
  - intros [Hin1 [Hin2 [Hneq [u [v [Hu [Hv Hstep]]]]]]].
    split; [exact Hin2|].
    split; [exact Hin1|].
    split; [intro H; apply Hneq; symmetry; exact H|].
    exists v, u; split; [exact Hv|]; split; [exact Hu|]; exact Hstep.
  - intros [Hin2 [Hin1 [Hneq [u [v [Hu [Hv Hstep]]]]]]].
    split; [exact Hin1|].
    split; [exact Hin2|].
    split; [intro H; apply Hneq; symmetry; exact H|].
    exists v, u; split; [exact Hv|]; split; [exact Hu|]; exact Hstep.
Qed.

Lemma is_tail_SCC_rev_is_head : forall sccs s,
  (In s sccs /\ forall s', condensation_edge_rev sccs s s' -> False) <->
  is_head_SCC sccs s.
Proof.
  unfold is_head_SCC.
  split.
  - intros [Hin Hno]; split; auto.
    intros s' Hedge.
    apply Hno with (s' := s').
    apply condensation_edge_rev_iff; auto.
  - intros [Hin Hno]; split; auto.
    intros s' Hedge.
    apply Hno with (s' := s').
    apply condensation_edge_rev_iff; auto.
Qed.

Lemma is_head_SCC_rev_is_tail : forall sccs s,
  (In s sccs /\ forall s', condensation_edge_rev sccs s' s -> False) <->
  is_tail_SCC sccs s.
Proof.
  unfold is_tail_SCC.
  split.
  - intros [Hin Hno]; split; auto.
    intros s' Hedge.
    apply Hno with (s' := s').
    apply condensation_edge_rev_iff; auto.
  - intros [Hin Hno]; split; auto.
    intros s' Hedge.
    apply Hno with (s' := s').
    apply condensation_edge_rev_iff; auto.
Qed.

End SCC.
