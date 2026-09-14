Require Import GraphLib.graph_basic.
Require Import GraphLib.reachable.reachable_basic.
Require Import GraphLib.reachable.reachable_restricted.
Require Import GraphLib.Syntax.
Require Import SetsClass.SetsClass.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalChoice.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Arith.
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
  split; eapply reachable_trans; eauto.
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
    (forall s1 s2 v, In s1 sccs -> In s2 sccs -> s1 v -> s2 v -> s1 = s2) /\
    NoDup sccs.
Proof.
  induction vertices as [|a rest IH].
  - exists nil.
    refine (conj _ (conj _ (conj _ _))).
    + intros v Hv Hin; inversion Hin.
    + intros t Hin; inversion Hin.
    + intros t1 t2 v Hin1 Hin2; inversion Hin1.
    + exact (NoDup_nil _).
  - destruct IH as [sccs_rest [Hcover_rest [Hsccs_rest [Hdisjoint_rest Hnodup_rest]]]].
    destruct (classic (exists s, In s sccs_rest /\ s a)).
    + exists sccs_rest.
      refine (conj _ (conj _ (conj _ _))).
      * intros v Hv Hin.
        destruct Hin as [Heqa|Hrest'].
        -- subst v; destruct H as [s [Hin_s Hsa]]; exists s; split; auto.
        -- apply Hcover_rest; auto.
      * exact Hsccs_rest.
      * exact Hdisjoint_rest.
      * exact Hnodup_rest.
    +     destruct (classic (vvalid g a)) as [Hva | Hnva].
      * exists (equiv_class a :: sccs_rest).
        refine (conj _ (conj _ (conj _ _))).
         -- intros v Hv Hin.
            destruct Hin as [Heqa|Hrest'].
            ++ subst v.
              exists (equiv_class a); split; [left; reflexivity|].
              unfold equiv_class; split; auto.
              apply mutually_reachable_refl; auto.
           ++ destruct (Hcover_rest v Hv Hrest') as [s [Hin_s Hsv]].
              exists s; split; auto; right; auto.
        -- intros s Hin.
           destruct Hin as [Hin|Hin].
           ++ subst s; apply equiv_class_is_SCC; auto.
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
        -- apply NoDup_cons; [| exact Hnodup_rest].
           intro Hin; apply H; exists (equiv_class a); split; auto.
           unfold equiv_class; split; [apply Hva | apply mutually_reachable_refl; auto].
      * exists sccs_rest.
        refine (conj _ (conj _ (conj _ _))).
         -- intros v Hv Hin.
            destruct Hin as [Heqa|Hrest'].
            ++ subst v; exfalso; exact (Hnva Hv).
            ++ apply Hcover_rest; auto.
        -- exact Hsccs_rest.
        -- exact Hdisjoint_rest.
        -- exact Hnodup_rest.
Qed.

Lemma listV_contains_valid (v : V) : vvalid g v -> In v (listV g).
Proof.
  intro Hv.
  apply (finite_vertices g Hgvalid v); auto.
Qed.

Theorem scc_partition_exists : exists sccs, scc_partition sccs /\ NoDup sccs.
Proof.
  destruct (build_scc_partition_aux (listV g)) as [sccs [Hcover [Hsccs [Hdisjoint Hnodup]]]].
  exists sccs; split.
  - split; [|split].
    + intros v Hv. apply (Hcover v Hv). apply listV_contains_valid; auto.
    + apply Hsccs.
    + apply Hdisjoint.
  - apply Hnodup.
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
        destruct Hmr2 as [Hv2u2 _].
        exists u1, v3.
        split; [|split]; auto.
        eapply reachable_trans; [exact Hreach12|].
        eapply reachable_trans; [exact Hv2u2 | exact Hreach23].
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
  { split.
    - eapply reachable_trans; [exact Hreach_fwd | exact (proj1 Hmr_s2)].
    - eapply reachable_trans; [exact Hreach_bwd | exact (proj1 Hmr_s1)]. }

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
  { split.
    - eapply reachable_trans; [exact Hfwd | exact (proj1 Hmr2)].
    - eapply reachable_trans; [exact Hback_reach | exact (proj1 Hmr1)]. }
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
  generalize dependent s1.
  induction_1n Hreach.
  - left; eapply Hdisjoint; eauto.
  - destruct (step_vvalid _ _ H) as [_ Hvu0].
    destruct (Hcover u0 Hvu0) as [sw [Hin_sw Hsw]].
    assert (IH : forall s0, In s0 sccs -> s0 u0 ->
                 s0 = s2 \/ condensation_reachable sccs s0 s2).
    { intros s0 Hin0 Hs0. apply IHrt; assumption. }
    destruct (classic (sw = s1)) as [Heq_same|Hneq].
    + subst sw; apply (IH s1 Hin1 Hsw).
    + assert (Hedge : condensation_edge sccs s1 sw).
      { unfold condensation_edge.
        split; [exact Hin1|].
        split; [exact Hin_sw|].
        split; [intro Heq; apply Hneq; symmetry; exact Heq|].
        exists u, u0; split; [exact Hsu|]; split; [exact Hsw|]; exact H. }
      destruct (IH sw Hin_sw Hsw) as [Heq | Hcr].
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

Definition reachable_rev (x y: V) : Prop := reachable g y x.

Lemma rr_refl : forall u, reachable_rev u u.
Proof.
  intros u; unfold reachable_rev, reachable; reflexivity.
Qed.

Lemma rr_step : forall u v w,
  step_rev u v -> reachable_rev v w -> reachable_rev u w.
Proof.
  intros u v w Hs Hr; unfold reachable_rev, step_rev in *.
  eapply reachable_step_reachable; [exact Hr | exact Hs].
Qed.

Lemma reachable_rev_ind : forall (P : V -> V -> Prop),
  (forall u, P u u) ->
  (forall u v w, step_rev u v -> reachable_rev v w -> P v w -> P u w) ->
  forall u v, reachable_rev u v -> P u v.
Proof.
  intros P Hrefl Hstep u v Hrev.
  unfold reachable_rev, reachable in Hrev.
  clear Hgvalid stepvalid finitegraph gv gv0.
  induction_n1 Hrev.
  - apply Hrefl.
  - eapply Hstep.
    + unfold step_rev; exact H.
    + unfold reachable_rev, reachable; exact Hrev.
    + apply IHrt; assumption.
Qed.

Lemma reachable_rev_intro : forall x y,
  reachable g y x -> reachable_rev x y.
Proof.
  intros x y H; exact H.
Qed.

Lemma reachable_rev_step_reachable_rev : forall x y z,
  reachable_rev x y -> step_rev y z -> reachable_rev x z.
Proof.
  intros x y z Hr Hs; unfold reachable_rev, step_rev in *.
  eapply step_reachable_reachable; [exact Hs | exact Hr].
Qed.

Lemma reachable_iff_reachable_rev : forall x y,
  reachable g x y <-> reachable_rev y x.
Proof.
  intros x y; unfold reachable_rev; reflexivity.
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
  revert Hsu.
  induction_1n Hreach.
  - auto.
  - apply IHrt; auto.
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
  revert Hsv.
  induction_n1 Hreach.
  - auto.
  - apply IHrt; auto.
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

(* ================================================================= *)
(* 7. Topological Ordering of the Condensation DAG                    *)
(* ================================================================= *)

Definition is_SCC_list (l : list (V -> Prop)) : Prop :=
  forall s, In s l -> is_SCC s.

Lemma scc_partition_is_SCC_list : forall sccs,
  scc_partition sccs -> is_SCC_list sccs.
Proof.
  intros sccs [_ [Hsccs _]]; exact Hsccs.
Qed.

Definition condensation_acyclic_on (l : list (V -> Prop)) : Prop :=
  ~ exists s1 s2, condensation_edge l s1 s2 /\ condensation_reachable l s2 s1.

Lemma condensation_acyclic_on_scc_partition : forall sccs,
  scc_partition sccs -> condensation_acyclic_on sccs.
Proof.
  unfold condensation_acyclic_on; intros sccs Hpart [s1 [s2 [Hedge Hreach]]].
  eapply condensation_is_acyclic; eauto.
Qed.

Lemma length_app_cons : forall {A} (l1 l2 : list A) (x : A),
  length (l1 ++ x :: l2) = S (length (l1 ++ l2)).
Proof.
  induction l1; intros l2 x; simpl; [| rewrite IHl1]; auto.
Qed.

Lemma NoDup_incl_length : forall {A} (l1 l2 : list A),
  NoDup l1 -> (forall x, In x l1 -> In x l2) -> length l1 <= length l2.
Proof.
  intros A l1 l2 Hnodup Hincl.
  revert l2 Hincl.
  induction Hnodup as [|a l1' Ha Hnodup' IH]; intros l2 Hincl; simpl.
  - lia.
  - assert (Hin_a : In a l2) by (apply Hincl; left; auto).
    apply In_split in Hin_a.
    destruct Hin_a as [l2a [l2b Hl2]].
    subst l2. rewrite length_app_cons.
    apply le_n_S. apply IH; intros x Hx.
    assert (Hx_in : In x (a :: l1')) by (right; auto).
    apply Hincl in Hx_in.
    apply in_app_or in Hx_in.
    destruct Hx_in as [Hx_l2a | [Hx_a | Hx_l2b]].
    + apply in_or_app; left; auto.
    + subst x; exfalso; apply Ha; exact Hx.
    + apply in_or_app; right; auto.
Qed.

Lemma iter_stays_in_sccs : forall (sccs : list (V -> Prop)) f (s : V -> Prop) (k : nat),
  (forall x, In x sccs -> In (f x) sccs) ->
  In s sccs ->
  In (Nat.iter k f s) sccs.
Proof.
  intros sccs f s k Hf_in Hs_in.
  induction k as [|k IH]; auto.
  apply Hf_in; auto.
Qed.

Lemma iter_condensation_path : forall (sccs : list (V -> Prop)) f (s : V -> Prop) (k : nat),
  (forall x, In x sccs -> condensation_edge sccs x (f x)) ->
  In s sccs ->
  k >= 1 ->
  condensation_reachable sccs s (Nat.iter k f s).
Proof.
  intros sccs f s k Hf_edge Hs_in Hk1.
  assert (Hf_in : forall x, In x sccs -> In (f x) sccs).
  { intros x Hx; destruct (Hf_edge x Hx) as [_ [Hin _]]; exact Hin. }
  induction k as [|k IH]; [lia |].
  destruct k as [|k'].
  - simpl; apply cr_edge; apply Hf_edge; auto.
  - simpl; eapply cr_trans.
    + apply IH; lia.
    + apply cr_edge; apply Hf_edge.
      apply iter_stays_in_sccs with (s := s) (k := S k'); auto.
Qed.

Lemma exists_tail_SCC : forall sccs,
  scc_partition sccs -> sccs <> nil ->
  exists t, is_tail_SCC sccs t.
Proof.
  intros sccs Hpart Hnonempty.
  destruct Hpart as [Hcover [Hsccs Hdisjoint]].
  destruct (classic (exists t, is_tail_SCC sccs t)) as [Htail | Hnotail]; [exact Htail |].

  assert (Hall_out : forall s, In s sccs -> exists s', condensation_edge sccs s s').
  { intros s Hs.
    assert (Hnot_tail : ~ is_tail_SCC sccs s).
    { intro Htail; apply Hnotail; exists s; exact Htail. }
    unfold is_tail_SCC in Hnot_tail.
    assert (Hno_forall : ~ (forall s', ~ condensation_edge sccs s s')).
    { intro Hforall; apply Hnot_tail; split; auto. }
    apply not_all_ex_not in Hno_forall.
    destruct Hno_forall as [s' Hnn].
    apply NNPP in Hnn.
    exists s'; exact Hnn. }

  destruct sccs as [|s0 sccs']; [exfalso; apply Hnonempty; auto |].
  assert (Hs0_in : In s0 (s0 :: sccs')) by (left; auto).

  assert (Hchoice : exists f : (V -> Prop) -> (V -> Prop),
    forall s, In s (s0 :: sccs') -> condensation_edge (s0 :: sccs') s (f s)).
  { apply (choice (fun s s' => In s (s0 :: sccs') -> condensation_edge (s0 :: sccs') s s')).
    intros s; destruct (classic (In s (s0 :: sccs'))) as [Hs_in | Hs_notin].
    - destruct (Hall_out s Hs_in) as [s' Hedge]; exists s'; auto.
    - exists s0; intro Hfalse; exfalso; apply Hs_notin; auto. }
  destruct Hchoice as [f Hf].

  assert (Hf_in : forall x, In x (s0 :: sccs') -> In (f x) (s0 :: sccs')).
  { intros x Hx; destruct (Hf x Hx) as [_ [Hin _]]; exact Hin. }

  assert (Hiter_in : forall m, In (Nat.iter m f s0) (s0 :: sccs')).
  { intro m; induction m as [|m IH]; [exact Hs0_in | apply Hf_in; auto]. }

  set (n := length (s0 :: sccs')) in *.

  destruct (classic (exists i j, i < j <= n /\ Nat.iter i f s0 = Nat.iter j f s0))
    as [Hrep | Hnodup].
  - (* Repeat → cycle contradicts condensation_is_acyclic *)
    destruct Hrep as [i [j [Hlt Heq]]].
    set (s := Nat.iter i f s0).
    set (k := j - i).
    assert (Hkpos : k >= 1) by lia.
    assert (Hs_in : In s (s0 :: sccs')) by (apply Hiter_in).
    assert (Hfs_in : In (f s) (s0 :: sccs')) by (apply Hf_in; auto).
    assert (Hedge_succ : condensation_edge (s0 :: sccs') s (f s)) by (apply Hf; auto).
    assert (H_neq : s <> f s)
      by (destruct Hedge_succ as [_ [_ [Hneq _]]]; exact Hneq).
    assert (Hk_ge2 : k >= 2).
    { destruct (Nat.eq_dec (j - i) 1) as [Hdiff1 | Hdiff_not1].
      - exfalso; apply H_neq. destruct Hlt as [Hij Hjn].
        assert (Hj : j = i + 1) by lia. subst j.
        unfold s; rewrite (Nat.add_1_r i) in Heq; simpl in Heq; exact Heq.
      - unfold k; lia. }
    assert (Heq_iter : Nat.iter k f s = s).
    { unfold s, k; rewrite <- Nat.iter_add; rewrite (Nat.sub_add i j) by lia;
      rewrite Heq; reflexivity. }
    assert (Hcalc : Nat.iter (k-1) f (f s) = s).
    { assert (Heq' : Nat.iter (k-1) f (f s) = Nat.iter ((k-1)+1) f s).
      { rewrite (Nat.iter_add (k-1) 1 (V -> Prop) f s). simpl. reflexivity. }
      rewrite Heq'. rewrite (Nat.sub_add 1 k) by lia. exact Heq_iter. }
    assert (Hkminus1 : k-1 >= 1) by lia.
    assert (Hreach : condensation_reachable (s0 :: sccs') (f s) s).
    { pose proof (iter_condensation_path (s0 :: sccs') f (f s) (k-1) Hf Hfs_in Hkminus1) as Hp.
      rewrite Hcalc in Hp; exact Hp. }
    exfalso; exact (condensation_is_acyclic (s0 :: sccs') s (f s)
      (conj Hcover (conj Hsccs Hdisjoint)) Hedge_succ Hreach).

  - (* No repeat → NoDup_incl_length contradiction *)
    set (iterates := map (fun i => Nat.iter i f s0) (seq 0 (n+1))).
    assert (Hiter_len : length iterates = n+1)
      by (unfold iterates; rewrite length_map, length_seq; auto).
    assert (Hiter_in_all : forall x, In x iterates -> In x (s0 :: sccs')).
    { intros x Hx; unfold iterates in Hx; apply in_map_iff in Hx.
      destruct Hx as [i [Heq' Hi]]; subst x.
      apply in_seq in Hi; destruct Hi as [Hil Hih].
      apply Hiter_in. }
    assert (Hnodup_iter : NoDup iterates).
    { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
      intros i j Hi Hj Heq_iter.
      apply in_seq in Hi; apply in_seq in Hj.
      destruct Hi as [Hil Hih]; destruct Hj as [Hjl Hjh].
      destruct (lt_eq_lt_dec i j) as [[Hlt' | Heqij] | Hgt'].
      - exfalso; apply Hnodup; exists i, j; split;
          [split; [exact Hlt' | lia] | exact Heq_iter].
      - exact Heqij.
      - exfalso; apply Hnodup; exists j, i; split;
          [split; [exact Hgt' | lia] | symmetry; exact Heq_iter]. }
    assert (Hlen_contra : length iterates <= n).
    { apply (NoDup_incl_length iterates (s0 :: sccs') Hnodup_iter Hiter_in_all). }
    unfold iterates in *; rewrite Hiter_len in Hlen_contra; lia.
Qed.

Fixpoint remove_one (sccs : list (V -> Prop)) (t : V -> Prop) : list (V -> Prop) :=
  match sccs with
  | nil => nil
  | s :: sccs' =>
      if excluded_middle_informative (s = t) then sccs'
      else s :: remove_one sccs' t
  end.

Lemma in_remove_one_forward : forall (sccs : list (V -> Prop)) (s t : V -> Prop),
  In s (remove_one sccs t) -> In s sccs.
Proof.
  intros sccs s t Hin; induction sccs as [|a sccs' IH]; [contradiction |].
  simpl in Hin; destruct (excluded_middle_informative (a = t)) as [Heq | Hneq].
  - subst a; right; exact Hin.
  - simpl in Hin; destruct Hin as [Heq' | Hin']; [subst; left; auto | right; apply IH; auto].
Qed.

Lemma in_remove_one_backward : forall (sccs : list (V -> Prop)) (s t : V -> Prop),
  In s sccs -> s <> t -> In s (remove_one sccs t).
Proof.
  intros sccs s t Hin Hneq; induction sccs as [|a sccs' IH]; [contradiction |].
  simpl; destruct (excluded_middle_informative (a = t)) as [Heq | Hneq_a_t].
  - subst a; destruct Hin as [Heq' | Hin']; [exfalso; apply Hneq; auto | exact Hin'].
  - destruct Hin as [Heq' | Hin']; [left; auto | right; apply IH; auto].
Qed.

Lemma NoDup_remove_one : forall (sccs : list (V -> Prop)) (t : V -> Prop),
  NoDup sccs -> NoDup (remove_one sccs t).
Proof.
  intros sccs t Hnodup; induction sccs as [|a sccs' IH]; [exact (NoDup_nil (V -> Prop)) |].
  simpl; destruct (excluded_middle_informative (a = t)) as [Heq | Hneq].
  - subst a; inversion Hnodup; exact H2.
  - inversion Hnodup; apply NoDup_cons.
    + intro Hin; apply H1; apply (in_remove_one_forward _ _ _ Hin).
    + apply IH; exact H2.
Qed.

Lemma in_remove_one_forward_neq : forall (sccs : list (V -> Prop)) (x y : V -> Prop),
  NoDup sccs -> In x (remove_one sccs y) -> x <> y.
Proof.
  intros sccs x y Hndp Hin; induction sccs as [|a sccs' IH]; [contradiction |].
  simpl in Hin; destruct (excluded_middle_informative (a = y)) as [Heq | Hneq].
  - subst a; pose proof (NoDup_cons_iff y sccs') as [Hfw _].
    destruct (Hfw Hndp) as [Ha Hnodup'].
    intro Heq_x_y; subst x; exact (Ha Hin).
  - pose proof (NoDup_cons_iff a sccs') as [Hfw _].
    destruct (Hfw Hndp) as [Ha Hnodup'].
    simpl in Hin; destruct Hin as [Heq' | Hin']; [subst; auto | apply IH; auto].
Qed.

Lemma in_remove_one : forall (sccs : list (V -> Prop)) (s t : V -> Prop),
  NoDup sccs -> (In s (remove_one sccs t) <-> In s sccs /\ s <> t).
Proof.
  intros sccs s t Hnodup; split.
  - intros Hin; split; [apply (in_remove_one_forward _ _ t); exact Hin |
                       exact (in_remove_one_forward_neq sccs s t Hnodup Hin)].
  - intros [Hin Hneq]; apply in_remove_one_backward; auto.
Qed.

Lemma remove_one_length_lt : forall (sccs : list (V -> Prop)) (t : V -> Prop),
  In t sccs -> length (remove_one sccs t) < length sccs.
Proof.
  intros sccs t Hin; induction sccs as [|s sccs' IH]; [contradiction |]; simpl.
  destruct (excluded_middle_informative (s = t)) as [Heq | Hneq].
  - subst s; simpl; lia.
  - destruct (in_inv Hin) as [Heq' | Hin']; [exfalso; apply Hneq; auto |].
    simpl; auto with arith; apply IH; auto.
Qed.

Lemma is_SCC_list_remove_one : forall (sccs : list (V -> Prop)) (t : V -> Prop),
  is_SCC_list sccs -> is_SCC_list (remove_one sccs t).
Proof.
  intros sccs t Hisccs.
  induction sccs as [|a sccs' IH].
  - intros s Hsin; simpl in Hsin; contradiction.
  - intros s Hsin; simpl in Hsin.
    destruct (excluded_middle_informative (a = t)) as [Heq | Hneq].
    + subst a; apply Hisccs; right; exact Hsin.
    + destruct Hsin as [Heq' | Hsin'].
      * subst s; apply Hisccs; left; auto.
      * apply (IH (fun s' Hs' => Hisccs s' (or_intror Hs')) s Hsin').
Qed.

Lemma in_remove_one_condensation_edge : forall (sccs : list (V -> Prop)) (t s1 s2 : V -> Prop),
  condensation_edge (remove_one sccs t) s1 s2 -> condensation_edge sccs s1 s2.
Proof.
  intros sccs t s1 s2 [Hin1 [Hin2 [Hneq [u [v [Hu [Hv Hstep]]]]]]].
  apply in_remove_one_forward in Hin1; apply in_remove_one_forward in Hin2.
  repeat split; try assumption; exists u, v; split; [exact Hu | split; [exact Hv | exact Hstep]].
Qed.

Lemma in_remove_one_condensation_reachable : forall (sccs : list (V -> Prop)) (t s1 s2 : V -> Prop),
  condensation_reachable (remove_one sccs t) s1 s2 -> condensation_reachable sccs s1 s2.
Proof.
  intros sccs t s1 s2 Hreach.
  induction Hreach as [s1' s2' Hedge | s1' s2' s3' Hr1 IH1 Hr2 IH2].
  - apply cr_edge; apply in_remove_one_condensation_edge with (t := t); exact Hedge.
  - eapply cr_trans; [apply IH1 | apply IH2].
Qed.

Lemma condensation_acyclic_on_remove_one : forall (sccs : list (V -> Prop)) (t : V -> Prop),
  condensation_acyclic_on sccs -> condensation_acyclic_on (remove_one sccs t).
Proof.
  unfold condensation_acyclic_on; intros sccs t Hac [s1 [s2 [Hedge Hreach]]].
  apply Hac; exists s1, s2; split.
  - apply in_remove_one_condensation_edge with (t := t); exact Hedge.
  - apply in_remove_one_condensation_reachable with (t := t); exact Hreach.
Qed.

Lemma exists_tail_SCC_on : forall (sccs : list (V -> Prop)),
  is_SCC_list sccs -> condensation_acyclic_on sccs -> sccs <> nil ->
  exists t, is_tail_SCC sccs t.
Proof.
  intros sccs Hisccs Hac Hnonempty.
  destruct (classic (exists t, is_tail_SCC sccs t)) as [Htail | Hnotail]; [exact Htail |].

  assert (Hall_out : forall s, In s sccs -> exists s', condensation_edge sccs s s').
  { intros s Hs.
    assert (Hnot_tail : ~ is_tail_SCC sccs s).
    { intro Htail; apply Hnotail; exists s; exact Htail. }
    unfold is_tail_SCC in Hnot_tail.
    assert (Hno_forall : ~ (forall s', ~ condensation_edge sccs s s')).
    { intro Hforall; apply Hnot_tail; split; auto. }
    apply not_all_ex_not in Hno_forall.
    destruct Hno_forall as [s' Hnn].
    apply NNPP in Hnn.
    exists s'; exact Hnn. }

  destruct sccs as [|s0 sccs']; [exfalso; apply Hnonempty; auto |].
  assert (Hs0_in : In s0 (s0 :: sccs')) by (left; auto).

  assert (Hchoice : exists f : (V -> Prop) -> (V -> Prop),
    forall s, In s (s0 :: sccs') -> condensation_edge (s0 :: sccs') s (f s)).
  { apply (choice (fun s s' => In s (s0 :: sccs') -> condensation_edge (s0 :: sccs') s s')).
    intros s; destruct (classic (In s (s0 :: sccs'))) as [Hs_in | Hs_notin].
    - destruct (Hall_out s Hs_in) as [s' Hedge]; exists s'; auto.
    - exists s0; intro Hfalse; exfalso; apply Hs_notin; auto. }
  destruct Hchoice as [f Hf].

  assert (Hf_in : forall x, In x (s0 :: sccs') -> In (f x) (s0 :: sccs')).
  { intros x Hx; destruct (Hf x Hx) as [_ [Hin _]]; exact Hin. }

  assert (Hiter_in : forall m, In (Nat.iter m f s0) (s0 :: sccs')).
  { intro m; induction m as [|m IH]; [exact Hs0_in | apply Hf_in; auto]. }

  set (n := length (s0 :: sccs')) in *.

  destruct (classic (exists i j, i < j <= n /\ Nat.iter i f s0 = Nat.iter j f s0))
    as [Hrep | Hnodup].
  - destruct Hrep as [i [j [Hlt Heq]]].
    set (s := Nat.iter i f s0).
    set (k := j - i).
    assert (Hkpos : k >= 1) by lia.
    assert (Hs_in : In s (s0 :: sccs')) by (apply Hiter_in).
    assert (Hfs_in : In (f s) (s0 :: sccs')) by (apply Hf_in; auto).
    assert (Hedge_succ : condensation_edge (s0 :: sccs') s (f s)) by (apply Hf; auto).
    assert (H_neq : s <> f s)
      by (destruct Hedge_succ as [_ [_ [Hneq _]]]; exact Hneq).
    assert (Hk_ge2 : k >= 2).
    { destruct (Nat.eq_dec (j - i) 1) as [Hdiff1 | Hdiff_not1].
      - exfalso; apply H_neq. destruct Hlt as [Hij Hjn].
        assert (Hj : j = i + 1) by lia. subst j.
        unfold s; rewrite (Nat.add_1_r i) in Heq; simpl in Heq; exact Heq.
      - unfold k; lia. }
    assert (Heq_iter : Nat.iter k f s = s).
    { unfold s, k; rewrite <- Nat.iter_add; rewrite (Nat.sub_add i j) by lia;
      rewrite Heq; reflexivity. }
    assert (Hcalc : Nat.iter (k-1) f (f s) = s).
    { assert (Heq' : Nat.iter (k-1) f (f s) = Nat.iter ((k-1)+1) f s).
      { rewrite (Nat.iter_add (k-1) 1 (V -> Prop) f s). simpl. reflexivity. }
      rewrite Heq'. rewrite (Nat.sub_add 1 k) by lia. exact Heq_iter. }
    assert (Hkminus1 : k-1 >= 1) by lia.
    assert (Hreach : condensation_reachable (s0 :: sccs') (f s) s).
    { pose proof (iter_condensation_path (s0 :: sccs') f (f s) (k-1) Hf Hfs_in Hkminus1) as Hp.
      rewrite Hcalc in Hp; exact Hp. }
    exfalso; apply Hac; exists s, (f s); split; auto.

  - set (iterates := map (fun i => Nat.iter i f s0) (seq 0 (n+1))).
    assert (Hiter_len : length iterates = n+1)
      by (unfold iterates; rewrite length_map, length_seq; auto).
    assert (Hiter_in_all : forall x, In x iterates -> In x (s0 :: sccs')).
    { intros x Hx; unfold iterates in Hx; apply in_map_iff in Hx.
      destruct Hx as [i [Heq' Hi]]; subst x.
      apply in_seq in Hi; destruct Hi as [Hil Hih].
      apply Hiter_in. }
    assert (Hnodup_iter : NoDup iterates).
    { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
      intros i j Hi Hj Heq_iter.
      apply in_seq in Hi; apply in_seq in Hj.
      destruct Hi as [Hil Hih]; destruct Hj as [Hjl Hjh].
      destruct (lt_eq_lt_dec i j) as [[Hlt' | Heqij] | Hgt'].
      - exfalso; apply Hnodup; exists i, j; split;
          [split; [exact Hlt' | lia] | exact Heq_iter].
      - exact Heqij.
      - exfalso; apply Hnodup; exists j, i; split;
          [split; [exact Hgt' | lia] | symmetry; exact Heq_iter]. }
    assert (Hlen_contra : length iterates <= n).
    { apply (NoDup_incl_length iterates (s0 :: sccs') Hnodup_iter Hiter_in_all). }
    unfold iterates in *; rewrite Hiter_len in Hlen_contra; lia.
Qed.

Lemma exists_topological_order_aux : forall (sccs : list (V -> Prop)),
  is_SCC_list sccs -> condensation_acyclic_on sccs -> NoDup sccs ->
  exists prec : (V -> Prop) -> (V -> Prop) -> Prop,
    (forall s1 s2, condensation_edge sccs s1 s2 -> prec s1 s2) /\
    (forall s1 s2, In s1 sccs -> In s2 sccs -> s1 <> s2 -> prec s1 s2 \/ prec s2 s1) /\
    (forall s1 s2, prec s1 s2 -> ~ prec s2 s1) /\
    (forall s1 s2 s3, prec s1 s2 -> prec s2 s3 -> prec s1 s3).
Proof.
  intro sccs; revert sccs.
  refine (well_founded_induction_type (well_founded_ltof _ (@length _)) _ _).
  intros sccs IH Hisccs Hac Hnodup.
  destruct (classic (sccs = nil)) as [Hnil | Hnonnil].
  - subst sccs; exists (fun _ _ => False).
    split; [| split; [| split]].
    + intros s1 s2 H; destruct H as [? _]; inversion H.
    + intros s1 s2 H1 ? ?; inversion H1.
    + intros ? ? H ?; exact H.
    + intros ? ? ? H1 ?; exact H1.
  - destruct (exists_tail_SCC_on sccs Hisccs Hac Hnonnil) as [t [Hin_t Hno_out]].
    set (sccs' := remove_one sccs t).
    assert (Hnodup_sccs' : NoDup sccs') by (apply NoDup_remove_one; exact Hnodup).
    assert (Hlen' : length sccs' < length sccs) by (apply remove_one_length_lt; auto).
    assert (Hisccs' : is_SCC_list sccs') by (apply is_SCC_list_remove_one; auto).
    assert (Hac' : condensation_acyclic_on sccs') by (apply condensation_acyclic_on_remove_one; auto).
    destruct (IH sccs' Hlen' Hisccs' Hac' Hnodup_sccs') as [prec' Hprec'].
    destruct Hprec' as [Hedge' [Htotal' [Hasym' Htrans']]].
    exists (fun a b => (In a sccs' /\ In b sccs' /\ prec' a b) \/
                       (In a sccs' /\ a <> t /\ b = t)).
    split; [| split; [| split]]; intros.
    { (* subgoal 1: condensation_edge s1 s2 → prec s1 s2 *)
      destruct (classic (s1 = t)) as [Heq | Hneq_s1_t].
      { subst s1; exfalso; apply Hno_out with (s' := s2).
        destruct H as [Hin1 [Hin2 [Hneq [u [v [Hu [Hv Hstep]]]]]]].
        repeat split; try assumption; exists u, v; split; [exact Hu | split; [exact Hv | exact Hstep]]. }
      { destruct (classic (s2 = t)) as [Heq_t | Hneq_s2_t].
        { subst s2; right; split.
          - destruct H as [Hin1 _]; apply in_remove_one_backward; [exact Hin1 | exact Hneq_s1_t].
          - split; [exact Hneq_s1_t | reflexivity]. }
        { left; destruct H as [Hin1 [Hin2 [Hneq [u [v [Hu [Hv Hstep]]]]]]]; split.
          - apply in_remove_one_backward; [exact Hin1 | exact Hneq_s1_t].
          - split; [apply in_remove_one_backward; [exact Hin2 | exact Hneq_s2_t] |].
            apply Hedge'; repeat split; try assumption.
            + apply in_remove_one_backward; [exact Hin1 | exact Hneq_s1_t].
            + apply in_remove_one_backward; [exact Hin2 | exact Hneq_s2_t].
            + exists u, v; split; [exact Hu | split; [exact Hv | exact Hstep]]. } }
    }
    { (* subgoal 2: totality: s1 <> s2, both in sccs *)
      destruct (classic (s1 = t)) as [Heq1 | Hneq1];
        [destruct (classic (s2 = t)) as [Heq2 | Hneq2] |
         destruct (classic (s2 = t)) as [Heq2 | Hneq2]].
      - subst s1 s2; exfalso; apply H1; auto.
      - subst s1; cbv beta iota; right; right; split; [exact (in_remove_one_backward sccs s2 t H0 Hneq2) | split; [exact Hneq2 | reflexivity]].
      - subst s2; cbv beta iota; left; right; split; [exact (in_remove_one_backward sccs s1 t H Hneq1) | split; [exact Hneq1 | reflexivity]].
      - assert (Hin1' : In s1 sccs') by (exact (in_remove_one_backward sccs s1 t H Hneq1)).
        assert (Hin2' : In s2 sccs') by (exact (in_remove_one_backward sccs s2 t H0 Hneq2)).
        destruct (Htotal' s1 s2 Hin1' Hin2' H1) as [Hp | Hp].
        + left; left; split; [| split]; auto.
        + right; left; split; [| split]; auto. }
    { (* subgoal 3: antisymmetry *)
      intro H0.
      destruct H as [[Hina1 [Hinb1 Hprec_a]] | [Hina1 [Hneq_a Heq_a]]];
        destruct H0 as [[Hina2 [Hinb2 Hprec_b]] | [Hina2 [Hneq_b Heq_b]]].
      * apply (Hasym' s1 s2 Hprec_a Hprec_b).
      * subst s1; exfalso;
          apply (in_remove_one_forward_neq sccs t t Hnodup Hina1); reflexivity.
      * subst s2; exfalso;
          apply (in_remove_one_forward_neq sccs t t Hnodup Hina2); reflexivity.
      * subst s1 s2; exfalso; apply Hneq_a; reflexivity. }
    { (* subgoal 4: transitivity *)
      destruct H as [[Hina1 [Hinb1 Hprec_a]] | [Hina1 [Hneq_a Heq_a]]];
        destruct H0 as [[Hina2 [Hinb2 Hprec_b]] | [Hina2 [Hneq_b Heq_b]]].
      * left; split; [exact Hina1 | split; [exact Hinb2 | eapply Htrans'; [exact Hprec_a | exact Hprec_b]]].
      * subst s3; right; split; [exact Hina1 | split; [apply (in_remove_one_forward_neq sccs s1 t Hnodup Hina1) | reflexivity]].
      * subst s2; exfalso;
          apply (in_remove_one_forward_neq sccs t t Hnodup Hina2); reflexivity.
      * subst s2 s3; exfalso; apply Hneq_b; reflexivity. }
  Qed.

Lemma exists_topological_order : forall sccs,
  scc_partition sccs -> NoDup sccs ->
  exists prec : (V -> Prop) -> (V -> Prop) -> Prop,
    (forall s1 s2, condensation_edge sccs s1 s2 -> prec s1 s2) /\
    (forall s1 s2, In s1 sccs -> In s2 sccs -> s1 <> s2 -> prec s1 s2 \/ prec s2 s1) /\
    (forall s1 s2, prec s1 s2 -> ~ prec s2 s1) /\
    (forall s1 s2 s3, prec s1 s2 -> prec s2 s3 -> prec s1 s3).
Proof.
  intros sccs Hpart Hnodup.
  apply exists_topological_order_aux; [apply scc_partition_is_SCC_list | apply condensation_acyclic_on_scc_partition | exact Hnodup]; auto.
Qed.

End SCC.
