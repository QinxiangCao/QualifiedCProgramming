Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare FixpointLib.
From GraphLib Require Import graph_basic reachable_basic.
From Algorithms Require Import Kosaraju.SCC.
Import SetsNotation.
Import MonadNotation.
Local Open Scope sets.
Local Open Scope monad.

Class KosarajuGraph (G V E : Type) := {
  kos_graph :: Graph G V E;
  kos_gvalid :: GValid G;
  kos_stepvalid :: StepValid G V E;
  kos_unique :: StepUniqueDirected G V E;
  kos_finite :: FiniteGraph G V E;
}.

Section Kosaraju.

Context {G V E: Type}
        `{KG: KosarajuGraph G V E}
        (g: G)
        (g_valid: gvalid g).

(* ================================================================= *)
(* Program State — non-primitive inductive record (avoids Coq 8.20   *)
(* primitive record restrictions on intros/subst/destruct/rewrite)   *)
(* ================================================================= *)

Inductive St : Type := MkSt {
  timer    : nat;
  finish   : V -> nat;
  visited1 : V -> Prop;
  visited2 : V -> Prop;
  scc_id   : V -> nat;
  scc_next : nat;
}.

Definition init_st : St :=
  MkSt 0 (fun _ => 0) (fun _ => False) (fun _ => False) (fun _ => 0) 0.

Definition visit1 (u: V): StateRelMonad.M St unit :=
  fun st1 _ st2 =>
    visited1 st2 == visited1 st1 ∪ Sets.singleton u /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited2 st2 = visited2 st1 /\
    scc_id st2 = scc_id st1 /\
    scc_next st2 = scc_next st1.

Definition visit2 (u: V): StateRelMonad.M St unit :=
  fun st1 _ st2 =>
    visited2 st2 == visited2 st1 ∪ Sets.singleton u /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited1 st2 = visited1 st1 /\
    scc_id st2 = scc_id st1 /\
    scc_next st2 = scc_next st1.

Definition set_finish (u: V) (t: nat): StateRelMonad.M St unit :=
  fun st1 _ st2 =>
    timer st2 = S (timer st1) /\
    finish st2 u = t /\
    (forall v, v <> u -> finish st2 v = finish st1 v) /\
    visited1 st2 = visited1 st1 /\
    visited2 st2 = visited2 st1 /\
    scc_id st2 = scc_id st1 /\
    scc_next st2 = scc_next st1.

Definition set_scc_id (u root: V): StateRelMonad.M St unit :=
  fun st1 _ st2 =>
    scc_id st2 u = scc_id st1 root /\
    (forall v, v <> u -> scc_id st2 v = scc_id st1 v) /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited1 st2 = visited1 st1 /\
    visited2 st2 = visited2 st1 /\
    scc_next st2 = scc_next st1.

Definition set_scc_root_id (u: V): StateRelMonad.M St unit :=
  fun st1 _ st2 =>
    scc_id st2 u = scc_next st1 /\
    scc_next st2 = S (scc_next st1) /\
    (forall v, v <> u -> scc_id st2 v = scc_id st1 v) /\
    timer st2 = timer st1 /\
    finish st2 = finish st1 /\
    visited1 st2 = visited1 st1 /\
    visited2 st2 = visited2 st1.

(* ================================================================= *)
(* Inner DFS — Phase 1 (reversed graph)                              *)
(* ================================================================= *)

Definition step_rev (x y: V) : Prop := step g y x.
Definition reachable_rev (x y : V) : Prop := SCC.reachable_rev g x y.
Definition mutually_reachable (u v : V) : Prop := SCC.mutually_reachable g u v.

(** Local inductive for forward reachability — avoids SetsClass shadowing
    of clos_refl_trans.  rf_step extends on the RIGHT so that structural
    recursion decomposes from the end, matching Hneigh's one-step backward
    reasoning. *)
Inductive reach_fwd (v : V) : V -> Prop :=
| rf_refl : reach_fwd v v
| rf_step z w : reach_fwd v z -> step g z w -> reach_fwd v w.

Lemma reachable_rev_to_reach_fwd : forall x y,
  reachable_rev y x -> reach_fwd x y.
Proof.
  induction 1.
  - constructor.
  - econstructor 2.
    + apply IHreachable_rev.
    + unfold step_rev in H; exact H.
Qed.

Lemma reachable_to_reach_fwd : forall x y,
  reachable g x y -> reach_fwd x y.
Proof.
  intros x y H.
  apply reachable_iff_reachable_rev in H.
  apply reachable_rev_to_reach_fwd; exact H.
Qed.

Lemma reach_fwd_to_reachable : forall x y,
  reach_fwd x y -> reachable g x y.
Proof.
  induction 1.
  - apply reachable_iff_reachable_rev; constructor.
  - eapply reachable_step_reachable; eauto.
Qed.

Definition DFS_finish_f
           (W: V -> StateRelMonad.M St unit)
           (u: V): StateRelMonad.M St unit :=
  visit1 u;;
  repeat_break
    (fun e_set =>
       choice
         (e <- any E;;
          v <- any V;;
          assume (fun _ => ~ e ∈ e_set);;
          assume (fun st => ~ visited1 st v);;
           assume (fun _ => step_aux g e v u);;
           W v;;
           continue (e_set ∪ Sets.singleton e))
          (assume (fun st =>
                     forall (e:E) (v:V),
                       step_aux g e v u ->
                       e ∈ e_set \/ visited1 st v);;
          t <- get (fun st t => t = timer st);;
          set_finish u t;;
          break tt))
    ∅.

Definition DFS_finish (u: V): StateRelMonad.M St unit :=
  Lfix (DFS_finish_f) u.

(* ================================================================= *)
(* Inner DFS — Phase 2 (original graph, assign SCC root)             *)
(* ================================================================= *)

Definition DFS_scc_f
           (root: V)
           (W: V -> StateRelMonad.M St unit)
           (u: V): StateRelMonad.M St unit :=
  visit2 u;;
  set_scc_id u root;;
  repeat_break
    (fun e_set =>
       choice
         (e <- any E;;
          v <- any V;;
          assume (fun _ => ~ e ∈ e_set);;
          assume (fun st => ~ visited2 st v);;
          assume (fun _ => step_aux g e u v);;
          W v;;
          continue (e_set ∪ Sets.singleton e))
         (assume (fun st =>
                    forall (e:E) (v:V),
                      step_aux g e u v ->
                      e ∈ e_set \/ visited2 st v);;
          break tt))
    ∅.

Definition DFS_scc (root u: V): StateRelMonad.M St unit :=
  Lfix (DFS_scc_f root) u.

(* ================================================================= *)
(* Pick an unvisited vertex with maximal finish number               *)
(* ================================================================= *)

Definition pick_unvisited1 : StateRelMonad.M St V :=
  get (fun st v => ~ visited1 st v).

Definition pick_unvisited2 : StateRelMonad.M St V :=
  get (fun st v =>
    ~ visited2 st v /\
    forall w, ~ visited2 st w -> finish st v >= finish st w).

(* ================================================================= *)
(* Full Kosaraju algorithm                                           *)
(* ================================================================= *)

Definition kosaraju_finish_f
           (W: unit -> StateRelMonad.M St unit)
           (u: unit): StateRelMonad.M St unit :=
  choice
    (u <- pick_unvisited1;;
     DFS_finish u;;
     W tt)
    (assume (fun st => forall v, visited1 st v);;
     skip).

Definition kosaraju_finish : StateRelMonad.M St unit :=
  Lfix kosaraju_finish_f tt.

Definition kosaraju_scc_f
           (W: unit -> StateRelMonad.M St unit)
           (u: unit): StateRelMonad.M St unit :=
  choice
    (u <- pick_unvisited2;;
     set_scc_root_id u;;
     DFS_scc u u;;
     W tt)
    (assume (fun st => forall v, visited2 st v);;
     skip).

Definition kosaraju_scc : StateRelMonad.M St unit :=
  Lfix kosaraju_scc_f tt.

Definition kosaraju : StateRelMonad.M St unit :=
  kosaraju_finish;; kosaraju_scc.

(* ================================================================= *)
(* 0. Hoare Helper Theorems (from C10909)                            *)
(* ================================================================= *)

(** Lifts a pointwise Hoare triple to a general precondition P. *)
Theorem Hoare_normalize {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q: A -> Σ -> Prop),
    (forall s0, P s0 -> Hoare (fun s => s = s0) f Q) ->
    Hoare P f Q.
Proof.
  unfold Hoare. intros.
  revert H1.
  apply (H s1); tauto.
Qed.

(** If P holds at s0, then assume P;; f has the Hoare triple for
    singleton precondition s = s0. Used for assume-guard elimination. *)
Theorem Hoare_normal_assume_bind {Σ A: Type}:
  forall (P: Σ -> Prop) f (Q: A -> Σ -> Prop) s0,
    (P s0 -> Hoare (fun s => s = s0) f Q) ->
    (Hoare (fun s => s = s0) (assume P;; f) Q).
Proof.
  intros.
  apply Hoare_assume_bind.
  apply Hoare_normalize.
  intros.
  destruct H0.
  subst; tauto.
Qed.

(** Lfix induction principle: if f W a satisfies Q a s0 under the
    hypothesis that W a does, then Lfix f a also satisfies Q a s0. *)
Theorem Hoare_normal_LFix {Σ A B: Type}:
  forall (Q: A -> Σ -> B -> Σ -> Prop)
         (f: (A -> StateRelMonad.M Σ B) -> (A -> StateRelMonad.M Σ B)),
    (forall (W: A -> StateRelMonad.M Σ B),
       (forall s0 a, Hoare (fun s => s = s0) (W a) (Q a s0)) ->
       (forall s0 a, Hoare (fun s => s = s0) (f W a) (Q a s0))) ->
    (forall s0 a, Hoare (fun s => s = s0) (Lfix f a) (Q a s0)).
Proof.
  intros.
  unfold Hoare.
  intros s1 b s2 ? ?.
  change (exists n, (s1, b, s2) ∈ Nat.iter n f ∅ a) in H1.
  destruct H1 as [n ?].
  revert s1 b s2 H0 H1.
  change (Hoare (fun s => s = s0) (Nat.iter n f ∅ a) (Q a s0)).
  revert s0 a.
  induction n.
  + unfold Hoare; simpl; sets_unfold; tauto.
  + simpl.
    apply H.
    apply IHn.
Qed.

(** Lfix induction with an invariant R closed under the recursive step.
    Variant of Hoare_normal_LFix carrying an extra hypothesis R s0. *)
Theorem Hoare_normal_LFix_closed {Σ A B: Type}:
  forall (R: Σ -> Prop)
         (Q: A -> Σ -> B -> Σ -> Prop)
         (f: (A -> StateRelMonad.M Σ B) -> (A -> StateRelMonad.M Σ B)),
    (forall (W: A -> StateRelMonad.M Σ B),
       (forall s0 a, R s0 -> Hoare (fun s => s = s0) (W a) (Q a s0)) ->
       (forall s0 a, R s0 -> Hoare (fun s => s = s0) (f W a) (Q a s0))) ->
    (forall s0 a, R s0 -> Hoare (fun s => s = s0) (Lfix f a) (Q a s0)).
Proof.
  intros R Q f H s0 a HR.
  unfold Hoare. intros s1 b s2 H0 H1.
  change (exists n, (s1, b, s2) ∈ Nat.iter n f ∅ a) in H1.
  destruct H1 as [n ?].
  revert s1 b s2 H0 H1.
  change (Hoare (fun s => s = s0) (Nat.iter n f ∅ a) (Q a s0)).
  revert s0 a HR.
  induction n.
  + unfold Hoare; simpl; sets_unfold; tauto.
  + simpl. apply H. apply IHn.
Qed.

(* ================================================================= *)
(* 1. Helper Hoare Lemmas for State Primitives                       *)
(* ================================================================= *)

(** visit1 u adds u to visited1; all other fields unchanged.
    Proved property: visited1 s' == visited1 s0 ∪ {u} *)
Lemma Hoare_visit1 : forall s0 u P,
  (forall s1, visited1 s1 == visited1 s0 ∪ Sets.singleton u -> P s1) ->
  Hoare (fun st => st = s0) (visit1 u) (fun _ => P).
Proof.
  intros s0 u P H; unfold Hoare, visit1.
  intros s1 a s2 Hs1 Hprog.
  rewrite Hs1 in *.
  destruct Hprog as [Hv [Htimer [Hfin [Hv2 [Hsid _]]]]].
  apply H; assumption.
Qed.

(** visit2 u adds u to visited2; all other fields unchanged.
    Proved property: visited2 s' == visited2 s0 ∪ {u} *)
Lemma Hoare_visit2 : forall s0 u P,
  (forall s1, visited2 s1 == visited2 s0 ∪ Sets.singleton u -> P s1) ->
  Hoare (fun st => st = s0) (visit2 u) (fun _ => P).
Proof.
  intros s0 u P H; unfold Hoare, visit2.
  intros s1 a s2 Hs1 Hprog.
  rewrite Hs1 in *.
  destruct Hprog as [Hv [Htimer [Hfin [Hv1 [Hsid _]]]]].
  apply H; assumption.
Qed.

(** get timer then set_finish u t captures the current timer as finish[u],
    increments timer, and preserves finish for other vertices.
    Proved property: timer s' = S(timer s0) /\ finish s' u = timer s0 /\ ... *)
Lemma Hoare_set_finish : forall s0 u,
  Hoare (fun st => st = s0) (t <- get (fun st t => t = timer st);; set_finish u t)
    (fun _ s' =>
       timer s' = S (timer s0) /\
       finish s' u = timer s0 /\
       (forall v, v <> u -> finish s' v = finish s0 v) /\
       visited1 s' = visited1 s0 /\
       visited2 s' = visited2 s0 /\
       scc_id s' = scc_id s0).
Proof.
  intros s0 u; unfold Hoare, bind, get, set_finish.
  intros s1 a s2 Hs1 Hprog.
  rewrite Hs1 in *.
  destruct Hprog as [t [s' [[Ht Hs'] Hset]]].
  rewrite Hs' in *.
  destruct Hset as [Htimer [Hfinish [Hfinish_other [Hv1 [Hv2 [Hsid _]]]]]].
  split; [exact Htimer|].
  split; [rewrite <- Ht; exact Hfinish|].
  split; [exact Hfinish_other|].
  split; [exact Hv1|].
  split; [exact Hv2|].
  exact Hsid.
Qed.

(* ================================================================= *)
(* 2. Inner DFS Phase 1 — Core Properties                            *)
(* ================================================================= *)

(** [DFS_finish_visited_incr]
    Monotonicity of visited1: if the recursive body W preserves the
    subset relation visited1 s0 ⊆ visited1 s', then so does DFS_finish_f W.
    Proved property: visited1 s0 ⊆ visited1 s' *)
Lemma DFS_finish_visited_incr : forall W,
  (forall s0 u,
     Hoare (fun st => st = s0) (W u) (fun _ s' => visited1 s0 ⊆ visited1 s')) ->
  (forall s0 u,
     Hoare (fun st => st = s0) (DFS_finish_f W u) (fun _ s' => visited1 s0 ⊆ visited1 s')).
Proof.
  intros W IH s0 u.
  unfold DFS_finish_f.
  eapply Hoare_bind.
  - apply Hoare_visit1.
    intros s1 Hv.
    apply (Sets_included_trans (visited1 s0) (visited1 s0 ∪ Sets.singleton u) (visited1 s1)).
    + apply Sets_included_union1.
    + destruct (proj1 (Sets_equiv_Sets_included (visited1 s1) (visited1 s0 ∪ Sets.singleton u)) Hv) as [_ Hv2].
      exact Hv2.
  - intro; apply Hoare_repeat_break with (P := fun e_set st => visited1 s0 ⊆ visited1 st).
    intros e_set.
    apply Hoare_normalize.
    intros s1 Hs1.
    apply Hoare_choice.
    + apply Hoare_any_bind.
      intros e.
      apply Hoare_any_bind.
      intros v.
      apply Hoare_normal_assume_bind.
      intros H_not_e.
      apply Hoare_normal_assume_bind.
      intros H_not_vis.
      apply Hoare_normal_assume_bind.
      intros H_step.
      eapply Hoare_bind with (Q := fun (_:unit) (s':St) => visited1 s1 ⊆ visited1 s').
      { exact (IH s1 v). }
      { simpl; intro H_unit; apply Hoare_ret'.
        intros s2 Hsub.
        etransitivity; [exact Hs1 | exact Hsub]. }
    + apply Hoare_normal_assume_bind.
      intros Hall.
      unfold Hoare, bind, get, break, ret.
      intros s1' a_brk s2 Hs1' Hprog.
      rewrite Hs1' in *.
      destruct Hprog as [t [s' [[Ht Hs'] [v [s'' [Hset [Hbrk_eq Hstate_eq]]]]]]].
      unfold set_finish in Hset; cbv beta in Hset.
      destruct Hset as [Htime [Hfin [Hfinh [Hvis1 [Hvis2 [Hsid _]]]]]].
      rewrite Hbrk_eq; simpl; rewrite <- Hstate_eq; rewrite Hvis1; rewrite <- Hs'.
      exact Hs1.
Qed.

(** [DFS_finish_visited_self]
    After DFS_finish_f W u, the start vertex u is visited.
    Proved property: visited1 s' u *)
Lemma DFS_finish_visited_self : forall W,
  (forall s0 u,
     Hoare (fun st => st = s0) (W u) (fun _ s' => visited1 s0 ⊆ visited1 s')) ->
  (forall s0 u,
     Hoare (fun st => st = s0) (DFS_finish_f W u) (fun _ s' => visited1 s' u)).
Proof.
  intros W IH s0 u.
  unfold DFS_finish_f.
  eapply Hoare_bind.
  - apply Hoare_visit1 with (P := fun s1 => visited1 s1 u).
    intros s1 Hv.
    sets_unfold in Hv.
    apply Hv.
    auto.
  - intro; apply Hoare_repeat_break with (P := fun e_set st => visited1 st u).
    intros e_set.
    apply Hoare_normalize.
    intros s1 Hs1.
    apply Hoare_choice.
    + apply Hoare_any_bind; intros e.
      apply Hoare_any_bind; intros v.
      apply Hoare_normal_assume_bind; intros H_not_e.
      apply Hoare_normal_assume_bind; intros H_not_vis.
      apply Hoare_normal_assume_bind; intros H_step.
      eapply Hoare_bind with (Q := fun (_:unit) (s':St) => visited1 s1 ⊆ visited1 s').
      { exact (IH s1 v). }
      { intros _; apply Hoare_ret'.
        intros s2 Hsub.
        apply Hsub.
        exact Hs1. }
    + apply Hoare_normal_assume_bind; intros Hall.
      unfold Hoare, bind, get, break, ret.
      intros s1' x s2 Hs1' Hprog.
      rewrite Hs1' in *.
      destruct Hprog as [t [s_mid [[Ht Hmid] Hrest]]].
      destruct Hrest as [uu [s_mid2' [Hset' Hbrk']]].
      destruct Hbrk' as [Hbrk_eq Hstate_eq].
      unfold set_finish in Hset'; cbv beta in Hset'.
      destruct Hset' as [Htime [Hfin [Hfinh [Hvis1 [Hvis2 [Hsid _]]]]]].
      rewrite Hbrk_eq; simpl.
      rewrite <- Hstate_eq.
      rewrite Hvis1.
      rewrite <- Hmid.
      exact Hs1.
Qed.

(** Postcondition weakening: Hoare P f Q and Q -> R gives Hoare P f R. *)
Lemma Hoare_imp_post {Σ A: Type} (P: Σ -> Prop) (f: program Σ A) (Q R: A -> Σ -> Prop) :
  Hoare P f Q -> (forall a s, Q a s -> R a s) -> Hoare P f R.
Proof.
  unfold Hoare; firstorder.
Qed.

Definition Q_step_visited (u' : V) (s0' : St) (_ : unit) (s' : St) : Prop :=
  visited1 s0' ⊆ visited1 s' /\
  visited1 s' u' /\
  (forall v, step_rev u' v -> visited1 s' v).

(** [DFS_finish_step_visited]
    All step_rev neighbors of u are visited1 after DFS_finish u completes.
    Proved property: forall v, step_rev u v -> visited1 s' v *)
Lemma DFS_finish_step_visited : forall s0 u,
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' => forall v, step_rev u v -> visited1 s' v).
Proof.
  intros s0 u.
  apply Hoare_imp_post with (Q := Q_step_visited u s0).
  - unfold DFS_finish.
    apply Hoare_normal_LFix with (Q := Q_step_visited).
    intros W IH s0' u'.
    unfold DFS_finish_f.
    set (P_loop := fun (e_set: E -> Prop) (st: St) =>
      visited1 s0' ⊆ visited1 st /\
      visited1 st u' /\
      (forall e, e ∈ e_set -> forall v, step_aux g e v u' -> visited1 st v)).
    eapply Hoare_bind.
    + apply Hoare_visit1 with (P := fun s1 => P_loop ∅ s1).
      intros s1 Hv.
      unfold P_loop.
      sets_unfold in Hv.
      repeat split.
      * intros w Hw. apply Hv; left; exact Hw.
      * apply Hv; auto.
      * intros e He; exfalso; exact He.
    + intro; apply Hoare_repeat_break with
        (P := P_loop)
        (Q := Q_step_visited u' s0').
      intros e_set.
      apply Hoare_normalize.
      intros s1 [Hsubset [Hs1_vis Hexplored]].
      apply Hoare_choice.
      { apply Hoare_any_bind; intros e.
        apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros H_not_e.
        apply Hoare_normal_assume_bind; intros H_not_vis.
        apply Hoare_normal_assume_bind; intros H_step.
        eapply Hoare_bind with (Q := Q_step_visited v s1).
        { exact (IH s1 v). }
        { intro a_res; apply Hoare_ret'.
          intros s2 [Hsubset2 [Hvis_v Hsub]].
          unfold P_loop.
          repeat split.
          { etransitivity; [exact Hsubset | exact Hsubset2]. }
          { apply Hsubset2, Hs1_vis. }
          { intros e' He'.
            destruct (classic (e' = e)) as [He'_eq | He'_ne].
            - subst e'.
              intros v' Hstep_aux'.
              destruct (KG.(kos_unique).(step_aux_unique) g e v u' v' u' g_valid H_step Hstep_aux') as [Hv'_eq _].
              subst v'; exact Hvis_v.
            - sets_unfold in He'.
              destruct He' as [He'_in | He'_sing].
              + intros v' Hstep_aux'.
                apply Hsubset2; apply (Hexplored e' He'_in v' Hstep_aux').
              + exfalso; apply He'_ne; symmetry; exact He'_sing. } } }
      { apply Hoare_normal_assume_bind; intros Hall.
        unfold Hoare, bind, get, break, ret.
        intros s1' x s2 Hs1' Hprog.
        rewrite Hs1' in *.
        destruct Hprog as [t [s_mid [[Ht Hmid] Hrest]]].
        destruct Hrest as [uu [s_mid2' [Hset' Hbrk']]].
        destruct Hbrk' as [Hbrk_eq Hstate_eq].
        unfold set_finish in Hset'; cbv beta in Hset'.
        destruct Hset' as [Htime [Hfin [Hfinh [Hvis1 [Hvis2 [Hsid _]]]]]].
        rewrite Hbrk_eq; simpl.
        rewrite <- Hstate_eq.
        unfold Q_step_visited.
        rewrite Hvis1; rewrite <- Hmid.
        repeat split.
        * exact Hsubset.
        * exact Hs1_vis.
        * intros v Hstep.
          destruct Hstep as [e Hstep_aux].
          destruct (Hall e v Hstep_aux) as [He_in | Hvis_v].
          { apply (Hexplored e He_in v Hstep_aux). }
          { exact Hvis_v. } }
  - intros _ s' [Hsubset [Hvis Hstep_vis]]; exact Hstep_vis.
Qed.

Definition neighbor_visited_rev (st : St) (v : V) : Prop :=
  forall w, step_rev v w -> visited1 st w.

(** [DFS_finish_neighbor_visited_aux]
    Helper for the neighbor_visited_rev invariant. Under the induction
    hypothesis (W preserves visited1, subset, and neighbor_visited_rev),
    DFS_finish_f W also preserves them.
    Proved property: visited1 s' u /\ visited1 s0 ⊆ visited1 s' /\
      (forall v, visited1 s' v -> visited1 s0 v \/ neighbor_visited_rev s' v) *)
Lemma DFS_finish_neighbor_visited_aux : forall W,
  (forall s0 u,
     Hoare (fun st => st = s0) (W u)
       (fun _ s' =>
          visited1 s' u /\
          visited1 s0 ⊆ visited1 s' /\
          (forall v, visited1 s' v -> visited1 s0 v \/ neighbor_visited_rev s' v))) ->
  (forall s0 u,
     Hoare (fun st => st = s0) (DFS_finish_f W u)
       (fun _ s' =>
          visited1 s' u /\
          visited1 s0 ⊆ visited1 s' /\
          (forall v, visited1 s' v -> visited1 s0 v \/ neighbor_visited_rev s' v))).
Proof.
  intros W IH s0 u.
  unfold DFS_finish_f.
  set (P_loop := fun (e_set: E -> Prop) (st: St) =>
    visited1 st u /\
    (forall v, visited1 st v -> visited1 s0 v \/ v = u \/ neighbor_visited_rev st v) /\
    (forall e v, e ∈ e_set -> step_aux g e v u -> visited1 st v) /\
    visited1 s0 ⊆ visited1 st).
  eapply Hoare_bind.
  - apply Hoare_visit1 with (P := fun s1 => P_loop ∅ s1).
    intros s1 Hv.
    unfold P_loop.
    sets_unfold in Hv.
    repeat split.
    + apply Hv; auto.
    + intros v Hv_vis.
      apply Hv in Hv_vis.
      destruct Hv_vis as [Hv0 | H_eq].
      * left; exact Hv0.
      * subst; right; left; reflexivity.
    + intros e v He; exfalso; exact He.
    + intros w Hw; apply Hv; left; exact Hw.
  - intro; apply Hoare_repeat_break with
      (P := P_loop)
      (Q := fun (_:unit) (s':St) =>
        visited1 s' u /\ visited1 s0 ⊆ visited1 s' /\
        (forall v, visited1 s' v -> visited1 s0 v \/ neighbor_visited_rev s' v)).
    intros e_set.
    apply Hoare_normalize.
    intros s1 [Hs1_vis [P_vis [Hexplored Hincl]]].
    apply Hoare_choice.
    + apply Hoare_any_bind; intros e.
      apply Hoare_any_bind; intros v.
      apply Hoare_normal_assume_bind; intros H_not_e.
      apply Hoare_normal_assume_bind; intros H_not_vis.
      apply Hoare_normal_assume_bind; intros H_step.
      eapply Hoare_bind with (Q := fun (_:unit) (s':St) =>
        visited1 s' v /\ visited1 s1 ⊆ visited1 s' /\
        (forall w, visited1 s' w -> visited1 s1 w \/ neighbor_visited_rev s' w)).
      { exact (IH s1 v). }
      { intros _; apply Hoare_ret'.
        intros s2 [Hvis_v [Hsubset2 Hneigh2]].
        unfold P_loop.
        repeat split.
        - apply Hsubset2, Hs1_vis.
        - intros w Hvis_w.
          destruct (classic (w = v)) as [Hw_eq | Hw_ne].
          + subst w; right; right.
            destruct (Hneigh2 v Hvis_v) as [Hv_s1 | Hv_neigh];
            [exfalso; apply H_not_vis; exact Hv_s1 | exact Hv_neigh].
          + destruct (classic (visited1 s1 w)) as [Hw_s1 | Hw_not_s1].
            * destruct (P_vis w Hw_s1) as [Hw_s0 | [Hw_u | Hw_neigh]].
              { left; exact Hw_s0. }
              { right; left; exact Hw_u. }
              { right; right; intros x Hstep_rev;
                apply Hsubset2; apply Hw_neigh; exact Hstep_rev. }
            * destruct (Hneigh2 w Hvis_w) as [Hw_s1' | Hw_neigh].
              { exfalso; apply Hw_not_s1; exact Hw_s1'. }
              { right; right; exact Hw_neigh. }
        - intros e' v' He' Hstep_aux'.
          sets_unfold in He'.
          destruct He' as [He'_in | He'_sing].
          + destruct (classic (e' = e)) as [He'_eq | He'_ne].
            * subst e'.
              destruct (KG.(kos_unique).(step_aux_unique) g e v u v' u g_valid H_step Hstep_aux') as [Hv'_eq _].
              subst v'; exact Hvis_v.
            * apply Hsubset2; apply (Hexplored e' v' He'_in Hstep_aux').
          + subst e'.
            destruct (KG.(kos_unique).(step_aux_unique) g e v u v' u g_valid H_step Hstep_aux') as [Hv'_eq _].
            subst v'; exact Hvis_v.
        - etransitivity; eauto. }
    + apply Hoare_normal_assume_bind; intros Hall.
      unfold Hoare, bind, get, break, ret.
      intros s1' x s2 Hs1' Hprog.
      rewrite Hs1' in *.
      destruct Hprog as [t [s_mid [[Ht Hmid] Hrest]]].
      destruct Hrest as [uu [s_mid2' [Hset' Hbrk']]].
      destruct Hbrk' as [Hbrk_eq Hstate_eq].
      unfold set_finish in Hset'; cbv beta in Hset'.
      destruct Hset' as [Htime [Hfin [Hfinh [Hvis1 [Hvis2 [Hsid _]]]]]].
      rewrite Hbrk_eq; simpl.
      rewrite <- Hstate_eq.
      rewrite Hvis1; rewrite <- Hmid.
      repeat split.
      * exact Hs1_vis.
      * exact Hincl.
      * intros v Hvis_v.
        destruct (P_vis v Hvis_v) as [Hv_s0 | [Hv_u | Hv_neigh]].
        { left; exact Hv_s0. }
        { subst v; right; unfold neighbor_visited_rev.
          rewrite Hvis1, <- Hmid.
          intros w Hstep.
          destruct Hstep as [e Hstep_aux].
          destruct (Hall e w Hstep_aux) as [He_in | Hvis_w].
          { apply (Hexplored e w He_in Hstep_aux). }
          { exact Hvis_w. } }
        { right; unfold neighbor_visited_rev; rewrite Hvis1, <- Hmid; exact Hv_neigh. }
Qed.

(** [DFS_finish_neighbor_visited_strong]
    Fixed-point version of the neighbor_visited_rev property for DFS_finish.
    Proved property: visited1 s' u /\ visited1 s0 ⊆ visited1 s' /\
      (forall v, visited1 s' v -> visited1 s0 v \/ neighbor_visited_rev s' v) *)
Lemma DFS_finish_neighbor_visited_strong : forall s0 u,
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' => visited1 s' u /\ visited1 s0 ⊆ visited1 s' /\
      (forall v, visited1 s' v -> visited1 s0 v \/ neighbor_visited_rev s' v)).
Proof.
  intros s0 u.
  unfold DFS_finish.
  apply Hoare_normal_LFix with (Q := fun (u' : V) (s0' : St) (_ : unit) (s' : St) =>
    visited1 s' u' /\ visited1 s0' ⊆ visited1 s' /\
    (forall v, visited1 s' v -> visited1 s0' v \/ neighbor_visited_rev s' v)).
  intros W IH s0' u'.
  apply DFS_finish_neighbor_visited_aux.
  exact IH.
Qed.

(** [DFS_finish_neighbor_visited]
    Simplified corollary: every newly visited vertex is either already in
    s0, or has all its step_rev neighbors visited.
    Proved property: forall v, visited1 s' v -> visited1 s0 v \/ neighbor_visited_rev s' v *)
Lemma DFS_finish_neighbor_visited : forall s0 u,
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' => forall v, visited1 s' v -> visited1 s0 v \/ neighbor_visited_rev s' v).
Proof.
  intros s0 u.
  eapply Hoare_imp_post.
  - apply DFS_finish_neighbor_visited_strong.
  - intros _ s' [Hvis_u [Hsubset Hneigh]]; exact Hneigh.
Qed.


(** [DFS_finish_reachable_rev_aux]
    Helper: every newly visited vertex is reachable_rev from u (or was
    already in s0). Uses the induction hypothesis on W.
    Proved property: forall v, visited1 s' v -> visited1 s0 v \/ reachable_rev u v *)
Lemma DFS_finish_reachable_rev_aux : forall W,
  (forall s0 u,
     Hoare (fun st => st = s0) (W u)
       (fun _ s' => forall v, visited1 s' v -> visited1 s0 v \/ reachable_rev u v)) ->
  (forall s0 u,
     Hoare (fun st => st = s0) (DFS_finish_f W u)
       (fun _ s' => forall v, visited1 s' v -> visited1 s0 v \/ reachable_rev u v)).
Proof.
  intros W IH s0 u.
  unfold DFS_finish_f.
  eapply Hoare_bind.
  - apply Hoare_visit1 with (P := fun s1 => forall v, visited1 s1 v -> visited1 s0 v \/ reachable_rev u v).
    intros s1 Hv.
    sets_unfold in Hv.
    intros v Hv_vis.
    apply Hv in Hv_vis.
    destruct Hv_vis as [H_vis0 | H_eq].
    + left; exact H_vis0.
    + subst v.
      right.
      constructor.
  - intro; apply Hoare_repeat_break with (P := fun e_set st => forall v, visited1 st v -> visited1 s0 v \/ reachable_rev u v).
    intros e_set.
    apply Hoare_normalize.
    intros s1' Hs1'.
    apply Hoare_choice.
    + apply Hoare_any_bind; intros e.
      apply Hoare_any_bind; intros v.
      apply Hoare_normal_assume_bind; intros H_not_e.
      apply Hoare_normal_assume_bind; intros H_not_vis.
      apply Hoare_normal_assume_bind; intros H_step.
      eapply Hoare_bind with (Q := fun (_:unit) (s':St) => forall w, visited1 s' w -> visited1 s1' w \/ reachable_rev v w).
      { exact (IH s1' v). }
      { intros _.
        apply Hoare_ret'.
        intros s2 Hsub.
        intros w Hvis.
        destruct (Hsub w Hvis) as [Hw | Hreach].
        - apply Hs1'.
          exact Hw.
        - right.
          econstructor 2 with (v := v).
          + unfold step_rev; eexists; exact H_step.
          + exact Hreach.
      }
    + apply Hoare_normal_assume_bind; intros Hall.
      unfold Hoare, bind, get, break, ret.
      intros s1'' x s2 Hs1'' Hprog.
      rewrite Hs1'' in *.
      destruct Hprog as [t [s_mid [[Ht Hmid] Hrest]]].
      destruct Hrest as [uu [s_mid2' [Hset' Hbrk']]].
      destruct Hbrk' as [Hbrk_eq Hstate_eq].
      unfold set_finish in Hset'; cbv beta in Hset'.
      destruct Hset' as [Htime [Hfin [Hfinh [Hvis1 [Hvis2 [Hsid _]]]]]].
      rewrite Hbrk_eq; simpl.
      rewrite <- Hstate_eq.
      rewrite Hvis1.
      rewrite <- Hmid.
      exact Hs1'.
Qed.

(** [DFS_finish_reachable_rev]
    Fixed-point version: after DFS_finish u, every newly visited vertex is
    reachable_rev from u (or was already in s0).
    Proved property: forall v, visited1 s' v -> visited1 s0 v \/ reachable_rev u v *)
Lemma DFS_finish_reachable_rev : forall s0 u,
  Hoare (fun st => st = s0) (DFS_finish u)
    (fun _ s' => forall v, visited1 s' v -> visited1 s0 v \/ reachable_rev u v).
Proof.
  intros s0 u.
  unfold DFS_finish.
  apply Hoare_normal_LFix with (Q := fun u' s0' _ s' => forall v, visited1 s' v -> visited1 s0' v \/ reachable_rev u' v).
  intros W IH s0' u'.
  apply DFS_finish_reachable_rev_aux.
  exact IH.
Qed.

(* Combined Q for Lfix: includes visited subset, visited, finish < timer,
   finish preservation for already-visited vertices (excluding u'),
   timer monotonicity, and finish ordering *)
Definition Q_finish_after (u' : V) (s0' : St) (_ : unit) (s' : St) : Prop :=
  visited1 s0' ⊆ visited1 s' /\
  visited1 s' u' /\
  finish s' u' < timer s' /\
  (forall z, visited1 s0' z -> z <> u' -> finish s' z = finish s0' z) /\
  timer s0' <= timer s' /\
  (forall v, v <> u' -> visited1 s' v -> visited1 s0' v \/ finish s' v < finish s' u').

(** [DFS_finish_Q_after]
    Core postcondition for DFS_finish u:
    - visited1 s0 ⊆ visited1 s' (monotonicity)
    - visited1 s' u (self-visit)
    - finish s' u < timer s' (finish time < timer)
    - finish times of old vertices are preserved
    - timer s0 <= timer s' (timer monotonicity)
    - for v ≠ u, visited1 s' v -> visited1 s0 v \/ finish s' v < finish s' u
    Proved property: Q_finish_after u s0 *)
Lemma DFS_finish_Q_after : forall s0 u,
  Hoare (fun st => st = s0) (DFS_finish u) (Q_finish_after u s0).
Proof.
  intros s0 u.
  unfold DFS_finish.
  apply Hoare_normal_LFix with (Q := fun u' s0' => Q_finish_after u' s0').
  intros W IH s0' u'.
  unfold DFS_finish_f.
  set (P_loop := fun (e_set: E -> Prop) (st: St) =>
    visited1 s0' ⊆ visited1 st /\
    visited1 st u' /\
    (forall z, visited1 s0' z -> finish st z = finish s0' z) /\
    timer s0' <= timer st /\
    (forall v, v <> u' -> visited1 st v -> visited1 s0' v \/ finish st v < timer st)).
  apply Hoare_bind with (Q := fun (_:unit) => P_loop ∅).
  + unfold P_loop, Hoare, visit1.
    intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    destruct Hprog as [Hv [Htimer [Hfin [Hv2 [Hsid _]]]]].
    repeat split.
    { sets_unfold. intros w Hw. apply Hv; left; exact Hw. }
    { apply Hv. right; reflexivity. }
    { intros z Hz. rewrite Hfin; reflexivity. }
    { rewrite Htimer; auto with arith. }
    { intros w Hw_neq Hw_vis.
      apply Hv in Hw_vis.
      destruct Hw_vis as [Hw0 | Hw_eq].
      - left; exact Hw0.
      - exfalso; apply Hw_neq; symmetry; exact Hw_eq. }
  + intro a_res.
    apply Hoare_repeat_break with
      (P := P_loop)
      (Q := Q_finish_after u' s0').
    intros e_set.
    apply Hoare_normalize.
    intros s1 [Hsubset [Hs1_vis [Hfin_pres [Htimer_mono Hs1_fin]]]].
    apply Hoare_choice.
    { apply Hoare_any_bind; intros e.
      apply Hoare_any_bind; intros v.
      apply Hoare_normal_assume_bind; intros H_not_e.
      apply Hoare_normal_assume_bind; intros H_not_vis.
      apply Hoare_normal_assume_bind; intros H_step.
      eapply Hoare_bind with (Q := Q_finish_after v s1).
      - exact (IH s1 v).
      - intro a_ret.
        apply Hoare_ret'.
        intros s2 [Hsubset2 [Hvis_v [Hfin_lt_v [Hfin_pres2 [Htimer2 Hfin_rel2]]]]].
        unfold P_loop.
        repeat split.
        + etransitivity; eauto.
        + apply Hsubset2, Hs1_vis.
        + intros z Hz.
          rewrite (Hfin_pres2 z).
          * apply Hfin_pres; exact Hz.
          * apply Hsubset, Hz.
          * intro H_eq; apply H_not_vis; rewrite <- H_eq; apply Hsubset, Hz.
        + etransitivity; eauto.
        + intros w Hw_neq Hw_vis2.
          destruct (classic (w = v)) as [Hw_eq | Hw_ne2].
          * subst w; right; exact Hfin_lt_v.
          * destruct (classic (visited1 s1 w)) as [Hw_vis1 | Hw_not_vis1].
            { destruct (Hs1_fin w Hw_neq Hw_vis1) as [Hw_s0 | Hw_fin].
              - left; exact Hw_s0.
              - right; rewrite (Hfin_pres2 w Hw_vis1 Hw_ne2); lia. }
            { destruct (Hfin_rel2 w Hw_ne2 Hw_vis2) as [Hw_vis1' | Hw_fin'].
              - exfalso; apply Hw_not_vis1; exact Hw_vis1'.
              - right; lia. } }
    { apply Hoare_normal_assume_bind; intros Hall.
      unfold Hoare, bind, get, break, ret.
      intros s1' x s2 Hs1' Hprog.
      rewrite Hs1' in *.
      destruct Hprog as [t [s_mid [[Ht Hmid] Hrest]]].
      destruct Hrest as [uu [s_mid2' [Hset' Hbrk']]].
      destruct Hbrk' as [Hbrk_eq Hstate_eq].
      unfold set_finish in Hset'; cbv beta in Hset'.
      destruct Hset' as [Htime [Hfin [Hfinh [Hvis1 [Hvis2 [Hsid _]]]]]].
      rewrite Hbrk_eq; simpl.
      rewrite <- Hstate_eq.
      unfold Q_finish_after.
      repeat split.
      - rewrite Hvis1, <- Hmid; exact Hsubset.
      - rewrite Hvis1, <- Hmid; exact Hs1_vis.
      - rewrite Htime, Hfin, Ht, Hmid; auto with arith.
      - intros z Hz Hz_ne.
        rewrite Hfinh; [| exact Hz_ne].
        rewrite <- Hmid.
        exact (Hfin_pres z Hz).
      - rewrite Htime; apply le_S; rewrite <- (f_equal timer Hmid); exact Htimer_mono.
      - intros v Hv_neq Hv_vis.
        rewrite Hvis1 in Hv_vis; rewrite <- Hmid in Hv_vis.
        destruct (Hs1_fin v Hv_neq Hv_vis) as [Hv_s0 | Hv_fin].
        + left; exact Hv_s0.
        + right; rewrite Hfin; rewrite (Hfinh v Hv_neq); rewrite <- Hmid;
            apply (eq_rect_r (fun x => finish s1 v < x) Hv_fin Ht). }
Qed.

(** visit1 preserves finish. Trivial but needed for set_finish reasoning.
    Proved property: finish s' = finish s0 *)
Lemma Hoare_visit1_preserve_finish : forall s0 u,
  Hoare (fun st => st = s0) (visit1 u) (fun _ s' => finish s' = finish s0).
Proof.
  intros s0 u.
  unfold Hoare, visit1.
  intros s1 a s2 Hs1 Hprog.
  rewrite Hs1 in *.
  destruct Hprog as [Hv [Htimer [Hfin [Hv2 [Hsid _]]]]].
  exact Hfin.
Qed.

Definition TimerDominates (s: St) : Prop :=
  forall v, visited1 s v -> finish s v < timer s.

Definition TimerDominates_except (s: St) (u: V) : Prop :=
  forall v, visited1 s v -> v <> u -> finish s v < timer s.

(** TimerDominates implies TimerDominates_except. Trivial weakening. *)
Lemma TDom_implies_except : forall s u,
  TimerDominates s -> TimerDominates_except s u.
Proof.
  unfold TimerDominates, TimerDominates_except; intros s u Htd v Hvis Hv_ne; apply Htd; assumption.
Qed.

(** [DFS_finish_preserves_TimerDominates]
    DFS_finish u preserves the TimerDominates invariant (every visited1
    vertex has finish < timer), provided u was not already visited1.
    Proved property: TimerDominates s' *)
Lemma DFS_finish_preserves_TimerDominates : forall s0 u,
  TimerDominates s0 ->
  ~ visited1 s0 u ->
  Hoare (fun st => st = s0) (DFS_finish u) (fun _ s' => TimerDominates s').
Proof.
  intros s0 u Htdom Hnot_vis.
  apply (Hoare_imp_post (fun st => st = s0) (DFS_finish u)
    (Q_finish_after u s0) (fun _ s' => TimerDominates s')).
  - apply DFS_finish_Q_after.
  - intros a s' Hq.
    destruct Hq as [Hsub [Hvis_u [Hfin_lt_u [Hfin_pres [Htimer_mono Hrest]]]]].
    unfold TimerDominates.
    intros v Hvis_v.
    destruct (classic (v = u)) as [Hv_eq | Hv_ne].
    + subst v; exact Hfin_lt_u.
    + destruct (classic (visited1 s0 v)) as [Hv_s0 | Hv_not_s0].
      * rewrite (Hfin_pres v Hv_s0 Hv_ne).
        apply Htdom in Hv_s0; lia.
      * destruct (Hrest v Hv_ne Hvis_v) as [Hv_s0' | Hfin_lt_v];
          [exfalso; exact (Hv_not_s0 Hv_s0') | lia].
Qed.

Definition ReachRevClosed (s: St) : Prop :=
  forall v w, visited1 s v -> reachable_rev v w -> visited1 s w.

Definition R_non_closed (u : V) (st : St) : Prop :=
  forall v, visited1 st v ->
    ~ (forall w, step_rev v w -> visited1 st w) ->
    reachable_rev v u.

Definition ForwardReachClosed (s: St) : Prop :=
  forall v w, visited2 s v -> reachable g v w -> visited2 s w.

(** reachable_rev is transitive. *)
Lemma reachable_rev_trans : forall x y z,
  reachable_rev x y -> reachable_rev y z -> reachable_rev x z.
Proof.
  intros x y z Hxy Hyz.
  unfold reachable_rev in *; revert z Hyz.
  induction Hxy; intros z Hyz.
  - exact Hyz.
  - econstructor 2; eauto.
Qed.

(** Combining two Hoare triples for the same program into a conjunction. *)
Lemma Hoare_conj (Σ A: Type) (P: Σ -> Prop) (f: program Σ A) (Q1 Q2: A -> Σ -> Prop) :
  Hoare P f Q1 -> Hoare P f Q2 -> Hoare P f (fun a s => Q1 a s /\ Q2 a s).
Proof.
  intros H1 H2 s1 a s2 Hpre Hin; split.
  - apply (H1 s1 a s2 Hpre Hin).
  - apply (H2 s1 a s2 Hpre Hin).
Qed.

(** [DFS_finish_combined_post]
    Conjunction of reachable_rev and neighbor_visited_rev properties
    into a single triple-postcondition.
    Proved property: (reachable_rev u v) /\ visited u /\ subset /\ neighbor_visited_rev *)
Lemma DFS_finish_combined_post : forall s0 u,
  Hoare (fun st => st = s0) (DFS_finish u) (fun _ s' =>
    (forall v, visited1 s' v -> visited1 s0 v \/ reachable_rev u v) /\
    visited1 s' u /\
    visited1 s0 ⊆ visited1 s' /\
    (forall v, visited1 s' v -> visited1 s0 v \/ neighbor_visited_rev s' v)).
Proof.
  intros s0 u.
  apply Hoare_conj with
    (Q1 := fun _ s' => forall v, visited1 s' v -> visited1 s0 v \/ reachable_rev u v)
    (Q2 := fun _ s' => visited1 s' u /\
                      visited1 s0 ⊆ visited1 s' /\
                      (forall v, visited1 s' v -> visited1 s0 v \/ neighbor_visited_rev s' v));
    [apply DFS_finish_reachable_rev | apply DFS_finish_neighbor_visited_strong].
Qed.

(** [DFS_finish_preserves_ReachRevClosed]
    DFS_finish u preserves the ReachRevClosed invariant (visited1 is
    closed under reachable_rev), provided u was not already visited1.
    Proved property: ReachRevClosed s' *)
Lemma DFS_finish_preserves_ReachRevClosed : forall s0 u,
  ~ visited1 s0 u ->
  ReachRevClosed s0 ->
  Hoare (fun st => st = s0) (DFS_finish u) (fun _ s' => ReachRevClosed s').
Proof.
  intros s0 u Hnot_vis Hclosed.
  eapply Hoare_imp_post.
  - apply DFS_finish_combined_post.
  - intros _ s' [Hreach [Hvis_u [Hsub Hneigh]]].
    unfold ReachRevClosed.
    intros v w0 Hvis_v Hrev_vw0.
    destruct (classic (visited1 s0 v)) as [Hv_s0 | Hv_not].
    + sets_unfold in Hsub; apply (Hsub w0); apply (Hclosed v w0); assumption.
    + sets_unfold in Hsub.
      refine ((fix aux (v0 : V) (Hvis_v0 : visited1 s' v0) (Hnot0 : ~ visited1 s0 v0)
                      (w' : V) (Hrev' : reachable_rev v0 w') {struct Hrev'} : visited1 s' w' :=
        match Hrev' with
        | SCC.rr_refl _ _ => Hvis_v0
        | SCC.rr_step _ _ v1 w'' Hstep Hrest =>
          match Hneigh v0 Hvis_v0 with
          | or_introl Hv0_s0 => False_ind _ (Hnot0 Hv0_s0)
          | or_intror Hn_v0 =>
            match classic (visited1 s0 v1) with
            | or_introl Hv1_s0 => Hsub w'' (Hclosed v1 w'' Hv1_s0 Hrest)
            | or_intror Hv1_not_s0 => aux v1 (Hn_v0 v1 Hstep) Hv1_not_s0 w'' Hrest
            end
          end
        end) v Hvis_v Hv_not w0 Hrev_vw0).
Qed.

(** [DFS_finish_finish_ge_timer]
    For every newly visited vertex v (visited1 s' v but not visited1 s0 v),
    the finish time is at least timer s0.
    Proved property: timer s0 <= finish s' v *)
Lemma DFS_finish_finish_ge_timer : forall s0 u,
  ~ visited1 s0 u ->
  Hoare (fun st => st = s0) (DFS_finish u) (fun _ s' =>
    forall v, visited1 s' v -> ~ visited1 s0 v -> timer s0 <= finish s' v).
Proof.
  intros s0 u Hnot_vis.
  unfold DFS_finish.
  eapply Hoare_imp_post.
  { apply Hoare_normal_LFix 
      with (Q := fun (u':V) (s0':St) (_:unit) (s':St) =>
        timer s0' <= timer s' /\
        (forall v, visited1 s' v -> ~ visited1 s0' v -> timer s0' <= finish s' v) /\
        (forall v, visited1 s0' v -> v <> u' -> finish s' v = finish s0' v) /\
        visited1 s0' ⊆ visited1 s').
    intros W IH s0' u'.
    unfold DFS_finish_f.
    set (P_loop := fun (e_set: E -> Prop) (st: St) =>
      timer s0' <= timer st /\
      (forall v, visited1 st v -> ~ visited1 s0' v -> v <> u' -> timer s0' <= finish st v) /\
      (forall v, visited1 s0' v -> v <> u' -> finish st v = finish s0' v) /\
      visited1 s0' ⊆ visited1 st).
    eapply Hoare_bind with (Q := fun (_:unit) (s:St) => P_loop ∅ s).
    { unfold Hoare, visit1; intros s1 a s2 Hs1 Hprog.
      destruct Hprog as [Hv [Htimer [Hfin [Hv2 [Hsid _]]]]].
      unfold P_loop.
      rewrite Htimer, Hfin, <- Hs1.
      split; [apply le_n | split; [| split]].
      - intros v' Hvis_v' Hv'_new Hv'_ne.
        apply Hv in Hvis_v'. sets_unfold in Hvis_v'.
        destruct Hvis_v' as [Hv'_s0 | Hv'_u'].
        + exfalso; apply Hv'_new; exact Hv'_s0.
        + exfalso; apply Hv'_ne; symmetry; exact Hv'_u'.
      - intros v' Hvis_v' Hv'_ne. reflexivity.
      - intros w Hw. apply Hv. left. exact Hw. }
    { intro u_res.
      apply Hoare_repeat_break with
        (P := P_loop) (Q := fun (_:unit) (s':St) => timer s0' <= timer s' /\
          (forall v, visited1 s' v -> ~ visited1 s0' v -> timer s0' <= finish s' v) /\
          (forall v, visited1 s0' v -> v <> u' -> finish s' v = finish s0' v) /\
          visited1 s0' ⊆ visited1 s').
      intros e_set.
      apply Hoare_normalize.
      intros s1 [Htimer_mono [Hge_finish [Hfin_pres_s1 Hsub1]]].
      apply Hoare_choice.
      { apply Hoare_any_bind; intros e.
        apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros H_not_e.
        apply Hoare_normal_assume_bind; intros H_not_vis.
        apply Hoare_normal_assume_bind; intros H_step.
        eapply Hoare_bind.
        - apply (IH s1 v).
        - intro uu; apply Hoare_ret'.
          intros s2 [Htimer_mono2 [Hge_timer2 [Hfin_pres_s2 Hsub2]]].
          unfold P_loop.
          split; [etransitivity; eauto | split; [| split]].
          + intros w Hvis_w Hw_new Hw_ne.
            destruct (classic (visited1 s1 w)) as [Hw_s1 | Hw_not_s1].
            { rewrite (Hfin_pres_s2 w Hw_s1).
              - apply Hge_finish; auto.
              - intro Heq; subst w; contradiction. }
            { apply Hge_timer2 in Hvis_w; auto; lia. }
          + intros w Hw_s0 Hw_ne.
            assert (Hw_not_v : w <> v).
            { intro Heq; subst w. apply H_not_vis. apply Hsub1; exact Hw_s0. }
            rewrite (Hfin_pres_s2 w (Hsub1 w Hw_s0) Hw_not_v).
            apply Hfin_pres_s1; auto.
          + etransitivity; eauto. }
      { apply Hoare_normal_assume_bind; intros Hall.
        unfold Hoare, bind, get, break, ret.
        intros s1' x s2 Hs1' Hprog.
        rewrite Hs1' in *.
        destruct Hprog as [t [s_mid [[Ht Hmid] Hrest]]].
        destruct Hrest as [uu [s_mid2' [Hset' Hbrk']]].
        destruct Hbrk' as [Hbrk_eq Hstate_eq].
        unfold set_finish in Hset'; cbv beta in Hset'.
        destruct Hset' as [Htime [Hfin_u [Hfinh [Hvis1 [Hvis2 [Hsid _]]]]]].
        rewrite Hbrk_eq; simpl; rewrite <- Hstate_eq.
      split; [| split; [| split]].
        { rewrite Htime; apply le_S; rewrite <- (f_equal timer Hmid); exact Htimer_mono. }
        { intros w Hvis_w Hw_new.
          rewrite Hvis1, <- Hmid in Hvis_w.
          destruct (classic (w = u')) as [Hw_eq | Hw_ne].
          - subst w. rewrite Hfin_u, Ht. exact Htimer_mono.
          - rewrite (Hfinh w Hw_ne), <- Hmid. apply Hge_finish; auto. }
        { intros w Hw_s0 Hw_ne.
          rewrite (Hfinh w Hw_ne), <- Hmid. apply Hfin_pres_s1; auto. }
        { rewrite Hvis1, <- Hmid; exact Hsub1. } }
    }
  }
  { intros _ s' [_ [Hge _]]; exact Hge. }
Qed.

(** [finished_rev_to_root]
    Under ReachRevClosed s0' and visited1 s0' ⊆ visited1 st, if a is a
    non-root new vertex that has been finished (its subtree returned),
    b is not yet visited, and a can reachable_rev b, then the path
    a →* b must pass through the current DFS root u'.
    Uses ReachRevClosed s0' (not st) so it works at intermediate
    loop states where st may not be closed under reachable_rev. *)
Lemma finished_rev_to_root :
  forall st s0' u' a b,
  ReachRevClosed s0' ->
  visited1 s0' ⊆ visited1 st ->
  visited1 st a -> ~ visited1 s0' a -> a <> u' ->
  (forall v w, visited1 st v -> ~ visited1 s0' v -> v <> u' -> step_rev v w -> visited1 st w) ->
  ~ visited1 st b ->
  reachable_rev a b ->
  reachable_rev a u'.
Proof.
  fix aux 13.
  intros st s0' u' a b Hclosed Hsub Hvis_a Hnew_a Hne_a Hstep_vis Hunvis_b Hreach.
  destruct Hreach as [| v w Hstep Hreach'].
  - exfalso. exact (Hunvis_b Hvis_a).
  - pose proof (Hstep_vis a v Hvis_a Hnew_a Hne_a Hstep) as Hvis_v.
    destruct (classic (visited1 s0' v)) as [Hv_s0 | Hv_new].
    + exfalso. apply Hunvis_b. apply Hsub, (Hclosed v w Hv_s0 Hreach').
    + destruct (classic (v = u')) as [Hv_u' | Hv_ne].
      * subst v. apply (SCC.rr_step g a u' u' Hstep (SCC.rr_refl g u')).
      * apply (SCC.rr_step g a v u' Hstep).
        apply (aux st s0' u' v w Hclosed Hsub Hvis_v Hv_new Hv_ne Hstep_vis Hunvis_b Hreach').
Qed.

(** [visited_boundary_not_closed]
    Purely set-theoretic: if [b] ∈ visited can reachable_rev some
    [c] ∉ visited, then the path [b →* c] must cross the boundary
    of [visited] at a vertex [v] ∈ visited that has a step_rev
    neighbour outside [visited] (hence [v] is not step_rev-closed).
    Moreover [reachable_rev b v]. *)
Lemma visited_boundary_not_closed :
  forall (visited : V -> Prop) (b c : V),
  visited b ->
  ~ visited c ->
  reachable_rev b c ->
  exists v, visited v /\ ~ (forall w, step_rev v w -> visited w) /\ reachable_rev b v.
Proof.
  unfold reachable_rev.
  fix aux 6.
  intros visited b c Hvis_b Hunvis_c Hreach.
  destruct Hreach as [| v w Hstep Hreach'].
  - exfalso. exact (Hunvis_c Hvis_b).
  - destruct (classic (visited v)) as [Hvis_v | Hunvis_v].
    + destruct (aux visited v w Hvis_v Hunvis_c Hreach')
        as [x [Hvis_x [Hnot_closed Hreach_x]]].
      exists x. split; [exact Hvis_x | split; [exact Hnot_closed |]].
      apply (SCC.rr_step g b v x Hstep Hreach_x).
    + exists b. split; [exact Hvis_b | split].
      * intro Hclosed_b. apply Hunvis_v, Hclosed_b. exact Hstep.
      * apply SCC.rr_refl.
Qed.

(** [DFS_finish_step_rev_closed]
    After any DFS_finish (or sub-DFS) call, every newly visited vertex
    — including the root u itself — is step_rev-closed: all its step_rev
    neighbours are in visited1.  The root's closure follows from the Hall
    condition at the break branch (all edges explored). *)
Lemma DFS_finish_step_rev_closed : forall s0 u,
  Hoare (fun st => st = s0) (DFS_finish u) (fun _ s' =>
    forall v w, visited1 s' v -> ~ visited1 s0 v -> step_rev v w -> visited1 s' w).
Proof.
  intros s0 u.
  unfold DFS_finish.

  set (Q_closed := fun (u': V) (s0': St) (_: unit) (s': St) =>
    visited1 s0' ⊆ visited1 s' /\
    visited1 s' u' /\
    (forall v w, visited1 s' v -> ~ visited1 s0' v -> step_rev v w -> visited1 s' w)).

  cut (Hoare (fun st => st = s0) (Lfix DFS_finish_f u) (Q_closed u s0)).
  { intro H. eapply Hoare_imp_post; [exact H | simpl; intros _ s' [_ [_ Hclosed]]; exact Hclosed]. }

  apply Hoare_normal_LFix with (Q := fun u' s0' => Q_closed u' s0').
  intros W IH s0' u'.
  unfold DFS_finish_f, Q_closed.

  set (P_loop := fun (e_set: E -> Prop) (st: St) =>
    visited1 s0' ⊆ visited1 st /\
    visited1 st u' /\
    (forall v w, visited1 st v -> ~ visited1 s0' v -> v <> u' -> step_rev v w -> visited1 st w) /\
    (forall e v, e ∈ e_set -> step_aux g e v u' -> visited1 st v)).

  apply Hoare_bind with (Q := fun (_:unit) => P_loop ∅).
  + (* visit1 u' *)
    unfold P_loop, Hoare, visit1.
    intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *. destruct Hprog as [Hv [Htimer [Hfin [Hv2 [Hsid _]]]]].
    repeat split.
    - intros w Hw. sets_unfold. apply Hv. left. exact Hw.
    - apply Hv. right. reflexivity.
    - intros v' w Hvis_v' Hnew_v' Hne_v' Hstep_v'w.
      sets_unfold in Hv. apply Hv in Hvis_v'.
      destruct Hvis_v' as [Hv0 | Hv_eq]; [exfalso; exact (Hnew_v' Hv0)|].
      subst v'. exfalso; exact (Hne_v' eq_refl).
    - intros e' v' He'. exfalso; exact He'.
  + intro a_res.
    apply Hoare_repeat_break with (P := P_loop) (Q := fun (_:unit) (s':St) =>
      visited1 s0' ⊆ visited1 s' /\
      visited1 s' u' /\
      (forall v w, visited1 s' v -> ~ visited1 s0' v -> step_rev v w -> visited1 s' w)).
    intros e_set.
    apply Hoare_normalize.
    intros s1 [Hsubset [Hvis_u' [Hstep_nonroot He_set]]].
    apply Hoare_choice.
    { (* recursive branch *)
      apply Hoare_any_bind; intros e.
      apply Hoare_any_bind; intros v.
      apply Hoare_normal_assume_bind; intros H_not_e.
      apply Hoare_normal_assume_bind; intros H_not_vis.
      apply Hoare_normal_assume_bind; intros H_step.
      eapply Hoare_bind with (Q := Q_closed v s1).
      - exact (IH s1 v).
      - intro a_ret. apply Hoare_ret'. intros s2 [Hsub2 [Hvis_v2 Hclosed_v]].
        unfold P_loop. repeat split.
        * etransitivity; eauto.
        * apply Hsub2, Hvis_u'.
        * intros v' w Hvis_v' Hnew_v' Hne_v' Hstep_v'w.
          destruct (classic (visited1 s1 v')) as [Hv'_s1 | Hv'_new].
          -- apply Hsub2. apply (Hstep_nonroot v' w Hv'_s1 Hnew_v' Hne_v' Hstep_v'w).
          -- apply (Hclosed_v v' w Hvis_v' Hv'_new Hstep_v'w).
        * intros e' v' He' Hstep_e'.
           sets_unfold in He'; destruct He' as [He'_in | He'_eq].
           -- apply Hsub2. apply (He_set e' v' He'_in Hstep_e').
           -- subst e'. destruct (KG.(kos_unique).(step_aux_unique) g e v u' v' u' g_valid H_step Hstep_e') as [-> _].
              exact Hvis_v2.
      }
    { (* break branch *)
      apply Hoare_normal_assume_bind; intros Hall.
      unfold Hoare, bind, get, break, ret.
      intros s1' x s2 Hs1' Hprog.
      rewrite Hs1' in *.
      destruct Hprog as [t [s_mid [[Ht Hmid] Hrest]]].
      destruct Hrest as [uu [s_mid2' [Hset' Hbrk']]].
      destruct Hbrk' as [Hbrk_eq Hstate_eq].
      unfold set_finish in Hset'; cbv beta in Hset'.
      destruct Hset' as [Htime [Hfin_u [Hfinh [Hvis1 [Hvis2 [Hsid _]]]]]].
      rewrite Hbrk_eq; simpl; rewrite <- Hstate_eq.
      rewrite Hvis1, <- Hmid.
      split; [exact Hsubset | split].
      - exact Hvis_u'.
      - intros v w Hvis_v Hnew_v Hstep_vw.
        destruct (classic (v = u')) as [Hv_eq | Hv_ne].
        + subst v.
          unfold step_rev in Hstep_vw; simpl in Hstep_vw.
          destruct Hstep_vw as [e Hstep_aux].
          destruct (Hall e w Hstep_aux) as [He_set' | Hvis_w].
          * apply (He_set e w He_set' Hstep_aux).
          * exact Hvis_w.
         + apply (Hstep_nonroot v w Hvis_v Hnew_v Hv_ne Hstep_vw). }
Qed.

Definition ReachRevClosedEx (s: St) (x: V) : Prop :=
  forall v w, visited1 s v -> v <> x -> reachable_rev v w -> visited1 s w.

(** Phase 1 postcondition: if a can reverse-reach b but not vice versa,
    then a's SCC contains a vertex c whose finish exceeds b's finish.
    Encodes the condensation-DAG edge direction: larger finish values
    lie further "upstream" in the forward graph. *)
Definition Phase1_Order (s : St) : Prop :=
  forall a b, reachable_rev a b -> ~ reachable_rev b a ->
    exists c, mutually_reachable a c /\ finish s b < finish s c.
    
(* ================================================================= *)
(* 3. Outer Phase 1 — kosaraju_finish                                 *)
(* ================================================================= *)

(** [kosaraju_finish_visited_all_aux]
    Helper: if the remaining computation W visits all vertices, then one
    iteration of kosaraju_finish_f (pick unvisited, DFS_finish, recurse) also
    visits all vertices.
    Proved property: forall v, visited1 s' v *)
Lemma kosaraju_finish_visited_all_aux : forall W,
  (forall s0, Hoare (fun st => st = s0) (W tt) (fun _ s' => forall v, visited1 s' v)) ->
  (forall s0, Hoare (fun st => st = s0) (kosaraju_finish_f W tt) (fun _ s' => forall v, visited1 s' v)).
Proof.
  intros W IH s0.
  unfold kosaraju_finish_f.
  apply Hoare_choice.
  { apply Hoare_bind with (Q := fun (u:V) (s':St) => s' = s0 /\ ~ visited1 s' u).
    { unfold Hoare, pick_unvisited1, get.
      intros s1 u s2 Hs1 Hprog.
      rewrite Hs1 in *.
      destruct Hprog as [Hnot_vis Hsame].
      rewrite Hsame in Hnot_vis; split; [symmetry; exact Hsame | exact Hnot_vis]. }
    { intro u.
      apply Hoare_normalize.
      intros s1 [Hs1_eq Hunvis].
      rewrite Hs1_eq.
      simpl.
      apply Hoare_bind with (Q := fun (_:unit) (s':St) => visited1 s' u).
      { eapply Hoare_imp_post.
        { apply DFS_finish_Q_after. }
        { intros _ s' [_ [Hvis_u _]]; exact Hvis_u. } }
      { intro a; apply Hoare_normalize; intros s2 _; apply (IH s2). } } }
  { apply Hoare_assume_bind with (Q := fun st => forall v, visited1 st v).
    apply Hoare_ret'.
    intros s1 [Hall _]; exact Hall. }
Qed.

(** [kosaraju_finish_visited_all]
    After the full kosaraju_finish, all vertices are visited1.
    Proved property: forall v, visited1 s' v *)
Lemma kosaraju_finish_visited_all : forall s0,
  Hoare (fun st => st = s0) kosaraju_finish (fun _ s' => forall v, visited1 s' v).
Proof.
  intros s0.
  unfold kosaraju_finish.
  apply Hoare_normal_LFix with (Q := fun (_:unit) (s0':St) (_:unit) (s':St) => forall v, visited1 s' v).
  intros W IH s0' u.
  apply kosaraju_finish_visited_all_aux.
  intro s0''; apply (IH s0'' tt).
Qed.

(* ================================================================= *)
(* 3a. Inner Phase 1 — Phase1_Order for a single DFS tree             *)
(* ================================================================= *)

Definition Q_phase1 (u' : V) (s0' : St) (_ : unit) (s' : St) : Prop :=
  visited1 s0' ⊆ visited1 s' /\
  visited1 s' u' /\
  (forall v w, visited1 s' v -> ~visited1 s0' v ->
               step_rev v w -> visited1 s' w) /\
  (forall v, visited1 s' v -> ~visited1 s0' v -> reachable_rev u' v) /\
  finish s' u' < timer s' /\
  (forall z, visited1 s0' z -> z <> u' -> finish s' z = finish s0' z) /\
  timer s0' <= timer s' /\
  (forall v, v <> u' -> visited1 s' v ->
             visited1 s0' v \/ finish s' v < finish s' u') /\
  (forall v, visited1 s' v -> ~visited1 s0' v -> timer s0' <= finish s' v) /\
  (R_non_closed u' s0' -> R_non_closed u' s') /\
  (R_non_closed u' s0' ->
   forall a b,
     visited1 s' a -> ~visited1 s0' a ->
     visited1 s' b -> ~visited1 s0' b ->
     reachable_rev a b -> ~reachable_rev b a ->
     exists c, mutually_reachable a c /\ finish s' b < finish s' c).

Lemma DFS_finish_phase1 : forall s0 u,
  Hoare (fun st => st = s0) (DFS_finish u) (Q_phase1 u s0).
Proof.
  intros s0 u. unfold DFS_finish.
  apply Hoare_normal_LFix with (Q := Q_phase1).
  intros W IH s0' u'.
  unfold DFS_finish_f, Q_phase1.

  set (P_loop := fun (e_set : E -> Prop) (st : St) =>
    visited1 s0' ⊆ visited1 st /\
    visited1 st u' /\
    (forall v w, visited1 st v -> ~visited1 s0' v -> v <> u' ->
                 step_rev v w -> visited1 st w) /\
    (forall v, visited1 st v -> ~visited1 s0' v -> reachable_rev u' v) /\
    (forall z, visited1 s0' z -> finish st z = finish s0' z) /\
    timer s0' <= timer st /\
    (forall v, v <> u' -> visited1 st v ->
               visited1 s0' v \/ finish st v < timer st) /\
    (forall v, visited1 st v -> ~visited1 s0' v -> v <> u' ->
               timer s0' <= finish st v) /\
    (forall e v, e ∈ e_set -> step_aux g e v u' -> visited1 st v) /\
    (R_non_closed u' s0' -> R_non_closed u' st) /\
    (R_non_closed u' s0' ->
     forall a b,
       visited1 st a -> ~visited1 s0' a ->
       visited1 st b -> ~visited1 s0' b ->
       reachable_rev a b -> ~reachable_rev b a ->
       (exists c, mutually_reachable a c /\ finish st b < finish st c) \/
       (mutually_reachable a u' /\ finish st b < timer st))).

  apply Hoare_bind with (Q := fun (_:unit) => P_loop ∅).
  { (* visit1 u' establishes P_loop ∅ *)
    unfold P_loop, Hoare, visit1.
    intros s1 a s2 Hs1 Hprog. rewrite Hs1 in *.
    destruct Hprog as [Hv [Htimer [Hfin [Hv2 [Hsid _]]]]].
    sets_unfold in Hv.
    repeat split.
    - intros w Hw. apply Hv. left. exact Hw.
    - apply Hv. right. reflexivity.
    - intros v w Hvis Hnew Hne. apply Hv in Hvis.
      destruct Hvis as [H0|Heq]; [exfalso; exact (Hnew H0)|subst; exfalso; exact (Hne eq_refl)].
    - intros v Hvis Hnew. apply Hv in Hvis.
      destruct Hvis as [H0|Heq]; [exfalso; exact (Hnew H0)|subst; constructor].
    - intros z Hz. rewrite Hfin. reflexivity.
    - rewrite Htimer. lia.
    - intros v Hne Hvis. apply Hv in Hvis.
      destruct Hvis as [H0|Heq]; [left; exact H0|exfalso; exact (Hne (eq_sym Heq))].
    - intros v Hvis Hnew Hne. apply Hv in Hvis.
      destruct Hvis as [H0|Heq]; [exfalso; exact (Hnew H0)|subst; exfalso; exact (Hne eq_refl)].
    - intros e v He. exfalso. exact He.
    - intros HR v Hvis Hnot_closed. apply Hv in Hvis.
      destruct Hvis as [H0|Heq].
      + apply HR; [exact H0|].
        intro Hcl. apply Hnot_closed. intros w Hstep. apply Hv. left. apply Hcl. exact Hstep.
      + subst v. constructor.
    - intros HR a0 b0 Ha0 Hna0 Hb0 Hnb0. apply Hv in Ha0. apply Hv in Hb0.
      destruct Ha0 as [H0|Heq]; [exfalso; exact (Hna0 H0)|subst a0].
      destruct Hb0 as [H0|Heq]; [exfalso; exact (Hnb0 H0)|subst b0].
      intros _ Hnot. exfalso. apply Hnot. constructor. }

  intro a_res.
  apply Hoare_repeat_break with
    (P := P_loop)
    (Q := fun (_:unit) (s':St) =>
      visited1 s0' ⊆ visited1 s' /\
      visited1 s' u' /\
      (forall v w, visited1 s' v -> ~visited1 s0' v ->
                   step_rev v w -> visited1 s' w) /\
      (forall v, visited1 s' v -> ~visited1 s0' v -> reachable_rev u' v) /\
      finish s' u' < timer s' /\
      (forall z, visited1 s0' z -> z <> u' -> finish s' z = finish s0' z) /\
      timer s0' <= timer s' /\
      (forall v, v <> u' -> visited1 s' v ->
                 visited1 s0' v \/ finish s' v < finish s' u') /\
      (forall v, visited1 s' v -> ~visited1 s0' v -> timer s0' <= finish s' v) /\
      (R_non_closed u' s0' -> R_non_closed u' s') /\
      (R_non_closed u' s0' ->
       forall a b,
         visited1 s' a -> ~visited1 s0' a ->
         visited1 s' b -> ~visited1 s0' b ->
         reachable_rev a b -> ~reachable_rev b a ->
         exists c, mutually_reachable a c /\ finish s' b < finish s' c)).

  intros e_set.
  apply Hoare_normalize.
  intros s1 HP.
  destruct HP as [Hsub [Hvis_u [Hclosed_new [Hreach_new
                  [Hfin_old [Htimer_mono [Hfin_lt_timer [Hge_timer
                  [He_set [HR_pres HPO_pres]]]]]]]]]].
  apply Hoare_choice.

  { (* ---- continue branch ---- *)
    apply Hoare_any_bind; intros e.
    apply Hoare_any_bind; intros v.
    apply Hoare_normal_assume_bind; intros H_not_e.
    apply Hoare_normal_assume_bind; intros H_not_vis.
    apply Hoare_normal_assume_bind; intros H_step.
    eapply Hoare_bind with (Q := Q_phase1 v s1).
    { exact (IH s1 v). }
    { intro junk. apply Hoare_ret'.
      intros s2 HQ.
      destruct HQ as [Hsub2 [Hvis_v2 [Hclosed2 [Hreach2
                      [Hfin_v_lt [Hfin_old2 [Htimer2 [Hfin_lt_v [Hge2
                      [HR2 HPO2]]]]]]]]]].
      unfold P_loop. repeat split.
      (* 1. visited1 monotonicity *)
      - etransitivity; eauto.
      (* 2. visited1 st u' *)
      - apply Hsub2. exact Hvis_u.
      (* 3. step_rev_closed for new non-root *)
      - intros x w Hvis_x Hnew_x Hne_x Hstep_xw.
        destruct (classic (visited1 s1 x)) as [Hx_s1|Hx_ns1].
        + apply Hsub2. exact (Hclosed_new x w Hx_s1 Hnew_x Hne_x Hstep_xw).
        + exact (Hclosed2 x w Hvis_x Hx_ns1 Hstep_xw).
      (* 4. reachable_rev u' for new *)
      - intros x Hvis_x Hnew_x.
        destruct (classic (visited1 s1 x)) as [Hx_s1|Hx_ns1].
        + exact (Hreach_new x Hx_s1 Hnew_x).
        + apply (reachable_rev_trans u' v x).
          * unfold reachable_rev. econstructor 2; [eexists; exact H_step | constructor].
          * exact (Hreach2 x Hvis_x Hx_ns1).
      (* 5. old finish preserved *)
      - intros z Hz.
        assert (Hz_s1 : visited1 s1 z) by (apply Hsub; exact Hz).
        assert (Hz_ne_v : z <> v) by (intro Heq; subst; exact (H_not_vis Hz_s1)).
        rewrite (Hfin_old2 z Hz_s1 Hz_ne_v). exact (Hfin_old z Hz).
      (* 6. timer monotonicity *)
      - etransitivity; eauto.
      (* 7. non-root new: finish < timer *)
      - intros x Hne Hvis_x.
        destruct (classic (visited1 s1 x)) as [Hx_s1|Hx_ns1].
        + destruct (Hfin_lt_timer x Hne Hx_s1) as [Hx_old|Hx_lt].
          * left. exact Hx_old.
          * right. assert (Hx_ne_v : x <> v)
              by (intro Heq; subst; exact (H_not_vis Hx_s1)).
            rewrite (Hfin_old2 x Hx_s1 Hx_ne_v). lia.
        + right. destruct (classic (x = v)) as [->|Hx_ne_v].
          * exact Hfin_v_lt.
          * destruct (Hfin_lt_v x Hx_ne_v Hvis_x) as [Hx_s1'|Hx_lt];
              [exfalso; exact (Hx_ns1 Hx_s1')|lia].
      (* 8. finish_ge_timer for new non-root *)
      - intros x Hvis_x Hnew_x Hne_x.
        destruct (classic (visited1 s1 x)) as [Hx_s1|Hx_ns1].
        + assert (Hx_ne_v : x <> v)
            by (intro Heq; subst; exact (H_not_vis Hx_s1)).
          rewrite (Hfin_old2 x Hx_s1 Hx_ne_v).
          exact (Hge_timer x Hx_s1 Hnew_x Hne_x).
        + pose proof (Hge2 x Hvis_x Hx_ns1). lia.
      (* 9. explored edges *)
      - intros e0 v0 He0 Hstep0.
        sets_unfold in He0. destruct He0 as [He0_in|He0_eq].
        + apply Hsub2. exact (He_set e0 v0 He0_in Hstep0).
        + subst e0.
          destruct (KG.(kos_unique).(step_aux_unique) g e v u' v0 u' g_valid H_step Hstep0) as [Hv_eq _].
          subst v0. exact Hvis_v2.
      (* 10. R preservation *)
      - intros HR0 z Hvis_z Hnot_closed_z.
        pose proof (HR_pres HR0) as HR1.
        destruct (classic (visited1 s1 z)) as [Hz_s1|Hz_ns1].
        + apply HR1; [exact Hz_s1|].
          intro Hcl. apply Hnot_closed_z.
          intros w Hstep. apply Hsub2. exact (Hcl w Hstep).
        + exfalso. apply Hnot_closed_z.
          intros w Hstep. exact (Hclosed2 z w Hvis_z Hz_ns1 Hstep).
      (* 11. Phase1_Order disjunctive *)
      - intros HR0 a0 b0 Ha0 Hna0 Hb0 Hnb0 Hrev Hnrev.
        pose proof (HR_pres HR0) as HR1.
        assert (Hrv : reachable_rev u' v).
        { unfold reachable_rev. econstructor 2.
          - eexists. exact H_step.
          - constructor. }
        assert (HR_v : R_non_closed v s1).
        { intros z Hz Hnc.
          apply (reachable_rev_trans z u' v); [exact (HR1 z Hz Hnc)|exact Hrv]. }
        assert (Hb0_ne_u' : b0 <> u').
        { intro Heq; subst b0; apply Hnrev.
          destruct (classic (visited1 s1 a0)) as [Ha0_s1|Ha0_ns1].
          - exact (Hreach_new a0 Ha0_s1 Hna0).
          - apply (reachable_rev_trans u' v a0); [exact Hrv|].
            exact (Hreach2 a0 Ha0 Ha0_ns1). }
        destruct (classic (visited1 s1 a0)) as [Ha0_s1|Ha0_ns1];
        destruct (classic (visited1 s1 b0)) as [Hb0_s1|Hb0_ns1].
        + (* Case B: both from s1 *)
          assert (Hb0_ne_v : b0 <> v) by (intro Heq; subst; exact (H_not_vis Hb0_s1)).
          destruct (HPO_pres HR0 a0 b0 Ha0_s1 Hna0 Hb0_s1 Hnb0 Hrev Hnrev)
            as [[c [Hmr Hfin]]|[Hmr Hfin]].
          * destruct (classic (visited1 s1 c)) as [Hc_s1|Hc_ns1].
            -- left. exists c. split; [exact Hmr|].
               assert (Hc_ne_v : c <> v) by (intro Heq; subst; exact (H_not_vis Hc_s1)).
               rewrite (Hfin_old2 b0 Hb0_s1 Hb0_ne_v), (Hfin_old2 c Hc_s1 Hc_ne_v).
               exact Hfin.
            -- right. split.
               ++ split.
                  ** apply reachable_iff_reachable_rev.
                     exact (Hreach_new a0 Ha0_s1 Hna0).
                  ** apply reachable_iff_reachable_rev.
                     destruct Hmr as [_ Hca0].
                     apply reachable_iff_reachable_rev in Hca0.
                     pose proof (visited_boundary_not_closed (visited1 s1) a0 c
                                   Ha0_s1 Hc_ns1 Hca0) as [z [Hz_vis [Hz_nc Hz_reach]]].
                     exact (reachable_rev_trans a0 z u' Hz_reach (HR1 z Hz_vis Hz_nc)).
               ++ rewrite (Hfin_old2 b0 Hb0_s1 Hb0_ne_v).
                  destruct (Hfin_lt_timer b0 Hb0_ne_u' Hb0_s1) as [Hb0_old|Hb0_lt];
                    [exfalso; exact (Hnb0 Hb0_old)|lia].
          * right. split; [exact Hmr|].
            rewrite (Hfin_old2 b0 Hb0_s1 Hb0_ne_v). lia.
        + (* Case C: a from s1, b from W — boundary + R *)
          right. split.
          * split.
            -- apply reachable_iff_reachable_rev.
               exact (Hreach_new a0 Ha0_s1 Hna0).
            -- apply reachable_iff_reachable_rev.
               pose proof (visited_boundary_not_closed (visited1 s1) a0 b0
                             Ha0_s1 Hb0_ns1 Hrev) as [z [Hz_vis [Hz_nc Hz_reach]]].
               exact (reachable_rev_trans a0 z u' Hz_reach (HR1 z Hz_vis Hz_nc)).
          * destruct (classic (b0 = v)) as [->|Hb0_ne_v].
            -- exact Hfin_v_lt.
            -- destruct (Hfin_lt_v b0 Hb0_ne_v Hb0) as [Hb0_s1'|Hb0_lt];
                 [exfalso; exact (Hb0_ns1 Hb0_s1')|lia].
        + (* Case D: a from W, b from s1 *)
          assert (Hb0_ne_v : b0 <> v) by (intro Heq; subst; exact (H_not_vis Hb0_s1)).
          left. exists a0. split.
          * unfold mutually_reachable, SCC.mutually_reachable.
            split; unfold reachable; reflexivity.
          * rewrite (Hfin_old2 b0 Hb0_s1 Hb0_ne_v).
            assert (Hfin_b0 : finish s1 b0 < timer s1).
            { destruct (Hfin_lt_timer b0 Hb0_ne_u' Hb0_s1) as [Hb0_old|Hb0_lt];
                [exfalso; exact (Hnb0 Hb0_old)|exact Hb0_lt]. }
            pose proof (Hge2 a0 Ha0 Ha0_ns1). lia.
        + (* Case A: both from W *)
          left. exact (HPO2 HR_v a0 b0 Ha0 Ha0_ns1 Hb0 Hb0_ns1 Hrev Hnrev). } }

  { (* ---- break branch ---- *)
    apply Hoare_normal_assume_bind; intros Hall.
    unfold Hoare, bind, get, set_finish, break, ret.
    intros s1' x s2 Hs1' Hprog.
    rewrite Hs1' in *.
    destruct Hprog as [t [s_mid [[Ht Hmid] Hrest]]].
    destruct Hrest as [uu [s_mid2' [Hset' Hbrk']]].
    destruct Hbrk' as [Hbrk_eq Hstate_eq].
    unfold set_finish in Hset'; cbv beta in Hset'.
    destruct Hset' as [Htime [Hfin_u [Hfinh [Hvis1 [Hvis2 [Hsid _]]]]]].
    rewrite Hbrk_eq; simpl; rewrite <- Hstate_eq.
    rewrite Hvis1, <- Hmid.
    repeat split.
    (* 1. visited1 monotonicity *)
    - exact Hsub.
    (* 2. visited1 s' u' *)
    - exact Hvis_u.
    (* 3. step_rev_closed for new — including u' via Hall *)
    - intros x0 w0 Hvis_x0 Hnew_x0 Hstep_x0.
      destruct (classic (x0 = u')) as [->|Hne].
      + unfold step_rev in Hstep_x0. destruct Hstep_x0 as [e0 Hstep_aux0].
        destruct (Hall e0 w0 Hstep_aux0) as [He0|Hw0]; [apply (He_set e0 w0 He0 Hstep_aux0)|exact Hw0].
      + apply (Hclosed_new x0 w0 Hvis_x0 Hnew_x0 Hne Hstep_x0).
    (* 4. reachable_rev u' for new *)
    - exact Hreach_new.
    (* 5. finish u' < timer *)
    - rewrite Hfin_u, Ht, Hmid, Htime. lia.
    (* 6. old finish preserved *)
    - intros z Hz Hz_ne. rewrite (Hfinh z Hz_ne), <- Hmid. apply Hfin_old. exact Hz.
    (* 7. timer monotonicity *)
    - rewrite Htime. apply le_S. rewrite <- (f_equal timer Hmid). exact Htimer_mono.
    (* 8. non-root new: finish < finish u' *)
    - intros x0 Hne Hvis_x0.
      destruct (Hfin_lt_timer x0 Hne Hvis_x0) as [Hx_old|Hx_lt].
      + left. exact Hx_old.
      + right. rewrite Hfin_u.
        rewrite (Hfinh x0 Hne), <- Hmid. exact (eq_rect_r (fun y => finish s1 x0 < y) Hx_lt Ht).
    (* 9. finish_ge_timer for new *)
    - intros x0 Hvis_x0 Hnew_x0.
      destruct (classic (x0 = u')) as [->|Hne].
      + rewrite Hfin_u, Ht. exact Htimer_mono.
      + rewrite (Hfinh x0 Hne), <- Hmid. apply Hge_timer; auto.
    (* 10. R preservation *)
    - intro HR0. unfold R_non_closed.
      intros z Hz Hnc.
      rewrite Hvis1, <- Hmid in Hz.
      assert (Hnc' : ~ (forall w, step_rev z w -> visited1 s1 w)).
      { intro Hcl. apply Hnc. intros w Hstep.
        rewrite Hvis1, <- Hmid. exact (Hcl w Hstep). }
      exact (HR_pres HR0 z Hz Hnc').
    (* 11. Phase1_Order — resolve disjunction via finish u' = timer *)
    - intro HR0. intros a0 b0 Ha0 Hna0 Hb0 Hnb0 Hrev Hnrev.
      assert (Hb0_ne_u' : b0 <> u')
        by (intro Heq; subst b0; apply Hnrev; exact (Hreach_new a0 Ha0 Hna0)).
      destruct (HPO_pres HR0 a0 b0 Ha0 Hna0 Hb0 Hnb0 Hrev Hnrev)
        as [[c [Hmr Hfin]]|[Hmr Hfin]].
      + destruct (classic (c = u')) as [->|Hc_ne].
        * exists u'. split; [exact Hmr|].
          rewrite Hfin_u, Ht, (Hfinh b0 Hb0_ne_u'), <- Hmid.
          destruct (Hfin_lt_timer b0 Hb0_ne_u' Hb0) as [Hb0_old|Hb0_lt];
            [exfalso; exact (Hnb0 Hb0_old)|exact Hb0_lt].
        * exists c. split; [exact Hmr|].
          rewrite (Hfinh b0 Hb0_ne_u'), (Hfinh c Hc_ne), <- Hmid. exact Hfin.
      + exists u'. split; [exact Hmr|].
        rewrite Hfin_u, Ht, (Hfinh b0 Hb0_ne_u'), <- Hmid. exact Hfin. }
Qed.

Lemma DFS_finish_finish_unvisited : forall s0 u,
  Hoare (fun st => st = s0) (DFS_finish u) (fun _ s' =>
    forall c, ~visited1 s' c -> finish s' c = finish s0 c).
Proof.
  intros s0 u. unfold DFS_finish.
  apply Hoare_imp_post with (Q := fun _ s' =>
    visited1 s0 ⊆ visited1 s' /\
    (forall c, ~visited1 s' c -> finish s' c = finish s0 c)).
  2: { intros _ s' [_ H]; exact H. }
  apply Hoare_normal_LFix with
    (Q := fun _ s0' _ s' =>
      visited1 s0' ⊆ visited1 s' /\
      (forall c, ~visited1 s' c -> finish s' c = finish s0' c)).
  intros W IH s0' u'. unfold DFS_finish_f.
  set (P := fun (_ : E -> Prop) st =>
    visited1 s0' ⊆ visited1 st /\
    visited1 st u' /\
    (forall c, ~visited1 st c -> finish st c = finish s0' c)).
  apply Hoare_bind with (Q := fun _ => P ∅).
  { unfold P, Hoare, visit1. intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *. destruct Hprog as [Hv [_ [Hfin _]]].
    repeat split.
    - intros w Hw. apply Hv. left. exact Hw.
    - apply Hv. right. reflexivity.
    - intros c Hc. rewrite Hfin. reflexivity. }
  intro. apply Hoare_repeat_break with (P := P)
    (Q := fun _ s' => visited1 s0' ⊆ visited1 s' /\
      (forall c, ~visited1 s' c -> finish s' c = finish s0' c)).
  intros e_set. apply Hoare_normalize. intros s1 [Hsub1 [Hvis_u1 HP1]].
  apply Hoare_choice.
  { apply Hoare_any_bind; intros e0. apply Hoare_any_bind; intros v0.
    apply Hoare_normal_assume_bind; intros _.
    apply Hoare_normal_assume_bind; intros _.
    apply Hoare_normal_assume_bind; intros _.
    eapply Hoare_bind. { exact (IH s1 v0). }
    intro. apply Hoare_ret'. intros s2 [Hsub2 HW2]. unfold P. repeat split.
    - etransitivity; eauto.
    - apply Hsub2. exact Hvis_u1.
    - intros c Hc. rewrite (HW2 c Hc). apply HP1.
      intro Hv. apply Hc. apply Hsub2. exact Hv. }
  { apply Hoare_normal_assume_bind; intros _.
    unfold Hoare, bind, get, set_finish, break, ret.
    intros s1' x s2 Hs1' Hprog. rewrite Hs1' in *.
    destruct Hprog as [t [s_mid [[Ht Hmid] [uu [s_mid2' [Hset' [Hbrk_eq Hstate_eq]]]]]]].
    unfold set_finish in Hset'; cbv beta in Hset'.
    destruct Hset' as [_ [_ [Hfinh [Hvis1 _]]]].
    rewrite Hbrk_eq; simpl; rewrite <- Hstate_eq. split.
    - rewrite Hvis1, <- Hmid. exact Hsub1.
    - intros c Hc. rewrite Hvis1, <- Hmid in Hc.
      assert (Hc_ne : c <> u') by (intro Heq; subst; exact (Hc Hvis_u1)).
      rewrite (Hfinh c Hc_ne), <- Hmid. exact (HP1 c Hc). }
Qed.

(** Phase 1 establishes the condensation-DAG ordering: if a can
    reverse-reach b but not vice versa, then a's SCC contains a
    vertex with strictly larger finish than b's. *)
Lemma kosaraju_finish_phase1_order :
  Hoare (fun st => st = init_st) kosaraju_finish (fun _ s' => Phase1_Order s').
Proof.
  unfold kosaraju_finish.
  set (Inv := fun (s : St) =>
    ReachRevClosed s /\ TimerDominates s /\
    (forall v, ~visited1 s v -> finish s v = 0) /\
    (forall a b, visited1 s a -> visited1 s b ->
       reachable_rev a b -> ~reachable_rev b a ->
       exists c, mutually_reachable a c /\ finish s b < finish s c)).
  apply Hoare_imp_post with (Q := fun _ s' =>
    (forall v, visited1 s' v) /\ Inv s').
  2: { intros _ s' [Hall [_ [_ [_ HPO]]]].
       intros a b Hrev Hnrev. apply HPO; auto. }
  apply Hoare_conj.
  - apply kosaraju_finish_visited_all.
  - apply Hoare_normal_LFix_closed with (R := Inv)
      (Q := fun _ _ _ s' => Inv s').
    2: { unfold Inv, init_st; cbn. split; [|split; [|split]].
         - intros v w Hv; exfalso; exact Hv.
         - intros v Hv; exfalso; exact Hv.
         - intros v Hv; reflexivity.
         - intros a b Ha; exfalso; exact Ha. }
    intros W IH s0' u0 HInv.
    destruct HInv as [HRC [HTD [Hfin0 HPO_vis]]].
    unfold kosaraju_finish_f.
    apply Hoare_choice.
    + apply Hoare_bind with (Q := fun (u:V) (s':St) => s' = s0' /\ ~visited1 s' u).
      { unfold Hoare, pick_unvisited1, get.
        intros s1 u s2 Hs1 Hprog. rewrite Hs1 in *.
        destruct Hprog as [Hnot_vis Hsame].
        rewrite Hsame in Hnot_vis; split; auto. }
      intro u. apply Hoare_normalize. intros s1 [Hs1_eq Hunvis]; subst s1.
      eapply Hoare_bind.
      { apply Hoare_conj.
        - apply Hoare_conj.
          + apply (DFS_finish_preserves_ReachRevClosed s0' u Hunvis HRC).
          + apply (DFS_finish_preserves_TimerDominates s0' u HTD Hunvis).
        - apply Hoare_conj.
          + apply (DFS_finish_finish_unvisited s0' u).
          + apply (DFS_finish_phase1 s0' u). }
      { intro junk. apply Hoare_normalize.
        intros s2 [[HRC2 HTD2] [Hunvis2 HQ]].
        destruct HQ as [Hsub2 [_ [Hclosed2 [Hreach2
                        [_ [Hfin_old2 [Htimer2 [_ [Hge2 [_ HPO2]]]]]]]]]].
        assert (HR_trivial : R_non_closed u s0').
        { intros v Hv Hnc. exfalso. apply Hnc.
          intros w Hstep. apply (HRC v w Hv).
          econstructor 2; [exact Hstep | constructor]. }
        assert (HInv_s2 : Inv s2).
        { unfold Inv. split; [exact HRC2 | split; [exact HTD2 | split]].
          - intros v Hv.
            destruct (classic (visited1 s0' v)) as [Hv_s0|Hv_ns0].
            + exfalso. apply Hv. apply Hsub2. exact Hv_s0.
            + rewrite (Hunvis2 v Hv). exact (Hfin0 v Hv_ns0).
          - intros a b Ha Hb Hrev Hnrev.
            destruct (classic (visited1 s0' a)) as [Ha_s0|Ha_ns0];
            destruct (classic (visited1 s0' b)) as [Hb_s0|Hb_ns0].
            + (* old-old *)
              assert (Ha_ne_u : a <> u) by (intro Heq; subst; exact (Hunvis Ha_s0)).
              assert (Hb_ne_u : b <> u) by (intro Heq; subst; exact (Hunvis Hb_s0)).
              destruct (HPO_vis a b Ha_s0 Hb_s0 Hrev Hnrev) as [c [Hmr Hfin_c]].
              destruct (classic (visited1 s0' c)) as [Hc_s0|Hc_ns0].
              * exists c. split; [exact Hmr|].
                assert (Hc_ne_u : c <> u) by (intro Heq; subst; exact (Hunvis Hc_s0)).
                rewrite (Hfin_old2 b Hb_s0 Hb_ne_u), (Hfin_old2 c Hc_s0 Hc_ne_u).
                exact Hfin_c.
              * exfalso. pose proof (Hfin0 c Hc_ns0). lia.
            + (* old-new: impossible *)
              exfalso. exact (Hb_ns0 (HRC a b Ha_s0 Hrev)).
            + (* new-old: timer ordering *)
              assert (Hb_ne_u : b <> u) by (intro Heq; subst; exact (Hunvis Hb_s0)).
              exists a. split.
              * unfold mutually_reachable, SCC.mutually_reachable.
                split; unfold reachable; reflexivity.
              * rewrite (Hfin_old2 b Hb_s0 Hb_ne_u).
                pose proof (HTD b Hb_s0). pose proof (Hge2 a Ha Ha_ns0). lia.
            + (* new-new *)
              exact (HPO2 HR_trivial a b Ha Ha_ns0 Hb Hb_ns0 Hrev Hnrev). }
        exact (IH s2 tt HInv_s2). }
    + apply Hoare_normal_assume_bind with
        (P := fun st => forall v, visited1 st v) (f := skip)
        (Q := fun _ s' => Inv s') (s0 := s0').
      intros _. apply Hoare_ret'.
      intros s Hs; subst s. exact (conj HRC (conj HTD (conj Hfin0 HPO_vis))).
Qed.

(* ================================================================= *)
(* 4. Inner DFS Phase 2 — Core Properties                            *)
(* ================================================================= *)

Definition neighbor_visited (st : St) (v : V) : Prop :=
  forall w, step g v w -> visited2 st w.

(** set_scc_id u root assigns scc_id[u] := scc_id[root]; other fields unchanged.
    Proved property: scc_id s' u = scc_id s0 root /\ ... *)
Lemma Hoare_set_scc_id : forall s0 u root P,
  (forall s1,
     scc_id s1 u = scc_id s0 root /\
     (forall v, v <> u -> scc_id s1 v = scc_id s0 v) /\
     timer s1 = timer s0 /\
     finish s1 = finish s0 /\
     visited1 s1 = visited1 s0 /\
     visited2 s1 = visited2 s0 /\
     scc_next s1 = scc_next s0 -> P s1) ->
  Hoare (fun st => st = s0) (set_scc_id u root) (fun _ => P).
Proof.
  intros s0 u root P H; unfold Hoare, set_scc_id.
  intros s1 a s2 Hs1 Hprog.
  rewrite Hs1 in *.
  destruct Hprog as [Huid [Hother [Htimer [Hfin [Hv1 [Hv2 Hscc_next]]]]]].
  apply H; split; [exact Huid | split; [exact Hother | split; [exact Htimer | split; [exact Hfin | split; [exact Hv1 | split; [exact Hv2 | exact Hscc_next]]]]]].
Qed.

(** set_scc_root_id u assigns a fresh scc_id (scc_next) to u, then
    increments scc_next; other scc_id values unchanged.
    Proved property: scc_id s' u = scc_next s0 /\ scc_next s' = S(scc_next s0) /\ ... *)
Lemma Hoare_set_scc_root_id : forall s0 u P,
  (forall s1,
     scc_id s1 u = scc_next s0 /\
     scc_next s1 = S (scc_next s0) /\
     (forall v, v <> u -> scc_id s1 v = scc_id s0 v) /\
     timer s1 = timer s0 /\
     finish s1 = finish s0 /\
     visited1 s1 = visited1 s0 /\
     visited2 s1 = visited2 s0 -> P s1) ->
  Hoare (fun st => st = s0) (set_scc_root_id u) (fun _ => P).
Proof.
  intros s0 u P H; unfold Hoare, set_scc_root_id.
  intros s1 a s2 Hs1 Hprog.
  rewrite Hs1 in *.
  destruct Hprog as [Huid [Hscc_next [Hother [Htimer [Hfin [Hv1 Hv2]]]]]].
  apply H; split; [exact Huid | split; [exact Hscc_next | split; [exact Hother | split; [exact Htimer | split; [exact Hfin | split; [exact Hv1 | exact Hv2]]]]]].
Qed.

(** [DFS_scc_visited_incr]
    Monotonicity of visited2: if W preserves visited2 s0 ⊆ visited2 s',
    then DFS_scc_f root W also preserves it.
    Proved property: visited2 s0 ⊆ visited2 s' *)
Lemma DFS_scc_visited_incr : forall W,
  (forall s0 u,
     Hoare (fun st => st = s0) (W u) (fun _ s' => visited2 s0 ⊆ visited2 s')) ->
  (forall s0 root u,
     Hoare (fun st => st = s0) (DFS_scc_f root W u) (fun _ s' => visited2 s0 ⊆ visited2 s')).
Proof.
  intros W IH s0 root u.
  unfold DFS_scc_f.
  eapply Hoare_bind.
  - apply Hoare_visit2.
    intros s1 Hv.
    apply (Sets_included_trans (visited2 s0) (visited2 s0 ∪ Sets.singleton u) (visited2 s1)).
    + apply Sets_included_union1.
    + destruct (proj1 (Sets_equiv_Sets_included (visited2 s1) (visited2 s0 ∪ Sets.singleton u)) Hv) as [_ Hv2].
      exact Hv2.
  - intro; eapply Hoare_bind.
    + apply (Hoare_normalize (fun st => visited2 s0 ⊆ visited2 st) (set_scc_id u root) (fun _ st => visited2 s0 ⊆ visited2 st)).
      intros s1 Hvis.
      apply Hoare_set_scc_id with (P := fun s' => visited2 s0 ⊆ visited2 s').
      intros s' [Hscc [Hother [Htimer [Hfin [Hv1 [Hv2 Hscc_next]]]]]].
      rewrite Hv2. exact Hvis.
    + intro. apply Hoare_repeat_break with (P := fun e_set st => visited2 s0 ⊆ visited2 st).
      intros e_set.
      apply Hoare_normalize.
      intros s1 Hs1.
      apply Hoare_choice.
      * apply Hoare_any_bind; intros e.
        apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros H_not_e.
        apply Hoare_normal_assume_bind; intros H_not_vis.
        apply Hoare_normal_assume_bind; intros H_step.
        eapply Hoare_bind with (Q := fun (_:unit) (s':St) => visited2 s1 ⊆ visited2 s').
        { exact (IH s1 v). }
        { intro; apply Hoare_ret'.
          intros s2 Hsub.
          etransitivity; [exact Hs1 | exact Hsub]. }
      * apply Hoare_normal_assume_bind; intros Hall.
        unfold Hoare, break, ret.
        intros ss aa tt HH Hret.
        rewrite HH in *.
        destruct Hret as [-> ->].
        simpl. exact Hs1.
Qed.

(** [DFS_scc_visited_self]
    After DFS_scc_f root W u, the start vertex u is visited2.
    Proved property: visited2 s' u *)
Lemma DFS_scc_visited_self : forall W,
  (forall s0 u,
     Hoare (fun st => st = s0) (W u) (fun _ s' => visited2 s0 ⊆ visited2 s')) ->
  (forall s0 root u,
     Hoare (fun st => st = s0) (DFS_scc_f root W u) (fun _ s' => visited2 s' u)).
Proof.
  intros W IH s0 root u.
  unfold DFS_scc_f.
  eapply Hoare_bind.
  - apply Hoare_visit2 with (P := fun s1 => visited2 s1 u).
    intros s1 Hv.
    sets_unfold in Hv. apply Hv.
    auto.
  - intro; eapply Hoare_bind.
    + apply (Hoare_normalize (fun st => visited2 st u) (set_scc_id u root) (fun _ st => visited2 st u)).
      intros s1 Hvis.
      apply Hoare_set_scc_id with (P := fun s' => visited2 s' u).
      intros s' [Hscc [Hother [Htimer [Hfin [Hv1 [Hv2 Hscc_next]]]]]].
      rewrite Hv2. exact Hvis.
    + intro. apply Hoare_repeat_break with (P := fun e_set st => visited2 st u).
      intros e_set.
      apply Hoare_normalize.
      intros s1 Hs1.
      apply Hoare_choice.
      * apply Hoare_any_bind; intros e.
        apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros H_not_e.
        apply Hoare_normal_assume_bind; intros H_not_vis.
        apply Hoare_normal_assume_bind; intros H_step.
        eapply Hoare_bind with (Q := fun (_:unit) (s':St) => visited2 s1 ⊆ visited2 s').
        { exact (IH s1 v). }
        { intro; apply Hoare_ret'.
          intros s2 Hsub; apply Hsub; exact Hs1. }
       * apply Hoare_normal_assume_bind; intros Hall.
         unfold Hoare, break, ret.
         intros ss aa tt HH Hret.
         rewrite HH in *.
         destruct Hret as [-> ->].
         simpl. exact Hs1.
Qed.

Definition Q_scc_step_visited (u' : V) (s0' : St) (_ : unit) (s' : St) : Prop :=
  visited2 s0' ⊆ visited2 s' /\
  visited2 s' u' /\
  (forall v, step g u' v -> visited2 s' v).

(** [DFS_scc_step_visited]
    All step (forward edge) neighbors of u are visited2 after DFS_scc root u
    completes on the original graph.
    Proved property: forall v, step g u v -> visited2 s' v *)
Lemma DFS_scc_step_visited : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u)
    (fun _ s' => forall v, step g u v -> visited2 s' v).
Proof.
  intros s0 root u.
  apply Hoare_imp_post with (Q := Q_scc_step_visited u s0).
  - unfold DFS_scc.
    apply Hoare_normal_LFix with (Q := Q_scc_step_visited).
    intros W IH s0' u'.
    unfold DFS_scc_f.
    set (P_loop := fun (e_set: E -> Prop) (st: St) =>
      visited2 s0' ⊆ visited2 st /\
      visited2 st u' /\
      (forall e, e ∈ e_set -> forall v, step_aux g e u' v -> visited2 st v)).
    eapply Hoare_bind.
    + apply Hoare_visit2 with (P := fun s1 => P_loop ∅ s1).
      intros s1 Hv.
      unfold P_loop.
      sets_unfold in Hv.
      repeat split.
      * intros w Hw. apply Hv; left; exact Hw.
      * apply Hv; auto.
      * intros e He; exfalso; exact He.
    + intro; eapply Hoare_bind.
      * apply (Hoare_normalize (P_loop ∅) (set_scc_id u' root) (fun _ => P_loop ∅)).
        intros s1 HP.
        apply Hoare_set_scc_id with (P := fun s' => P_loop ∅ s').
        intros s' [Hscc [Hother [Htimer [Hfin [Hv1 [Hv2 Hscc_next]]]]]].
        unfold P_loop in HP; simpl in *.
        destruct HP as [Hsubset [Hvis Hexpl]].
        unfold P_loop. rewrite Hv2. repeat split; auto.
      * intro. apply Hoare_repeat_break with
          (P := P_loop)
          (Q := Q_scc_step_visited u' s0').
        intros e_set.
        apply Hoare_normalize.
        intros s1 [Hsubset [Hs1_vis Hexplored]].
        apply Hoare_choice.
        { apply Hoare_any_bind; intros e.
          apply Hoare_any_bind; intros v.
          apply Hoare_normal_assume_bind; intros H_not_e.
          apply Hoare_normal_assume_bind; intros H_not_vis.
          apply Hoare_normal_assume_bind; intros H_step.
          eapply Hoare_bind with (Q := Q_scc_step_visited v s1).
          - exact (IH s1 v).
          - intro a_res; apply Hoare_ret'.
            intros s2 [Hsubset2 [Hvis_v Hsub]].
            unfold P_loop. split; [| split].
            { etransitivity; [exact Hsubset | exact Hsubset2]. }
            { apply (Hsubset2 u'); exact Hs1_vis. }
            { intros e' He'.
              destruct (classic (e' = e)) as [He'_eq | He'_ne].
              { subst e'.
                intros v' Hstep_aux'.
               destruct (KG.(kos_unique).(step_aux_unique) g e u' v u' v' g_valid H_step Hstep_aux') as [_ Hv'_eq].
                subst v'; exact Hvis_v. }
              { sets_unfold in He'; destruct He' as [He'_in | He'_sing].
                { intros v' Hstep_aux'; apply Hsubset2; apply (Hexplored e' He'_in v' Hstep_aux'). }
                { exfalso; apply He'_ne; symmetry; exact He'_sing. } } } }
         { apply Hoare_normal_assume_bind; intros Hall.
           unfold Hoare, break, ret.
            intros s' b s'' Hs' Hprog.
           rewrite Hs' in *.
           destruct Hprog as [-> ->].
           simpl.
           unfold Q_scc_step_visited.
          repeat split.
          - exact Hsubset.
          - exact Hs1_vis.
          - intros v Hstep.
            destruct Hstep as [e Hstep_aux].
            destruct (Hall e v Hstep_aux) as [He_in | Hvis_v].
            + apply (Hexplored e He_in v Hstep_aux).
            + exact Hvis_v. }
  - intros _ s' [Hsubset [Hvis Hstep_vis]]; exact Hstep_vis.
Qed.

(** [DFS_scc_neighbor_visited_aux]
    Helper for the neighbor_visited invariant (forward graph analog of
    neighbor_visited_rev). Preserves visited2, subset, and neighbor_visited.
    Proved property: visited2 s' u /\ visited2 s0 ⊆ visited2 s' /\
      (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v) *)
Lemma DFS_scc_neighbor_visited_aux : forall W,
  (forall s0 u,
     Hoare (fun st => st = s0) (W u)
       (fun _ s' =>
          visited2 s' u /\
          visited2 s0 ⊆ visited2 s' /\
          (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v))) ->
  (forall s0 root u,
     Hoare (fun st => st = s0) (DFS_scc_f root W u)
       (fun _ s' =>
          visited2 s' u /\
          visited2 s0 ⊆ visited2 s' /\
          (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v))).
Proof.
  intros W IH s0 root u.
  unfold DFS_scc_f.
  set (P_loop := fun (e_set: E -> Prop) (st: St) =>
    visited2 st u /\
    (forall v, visited2 st v -> visited2 s0 v \/ v = u \/ neighbor_visited st v) /\
    (forall e v, e ∈ e_set -> step_aux g e u v -> visited2 st v) /\
    visited2 s0 ⊆ visited2 st).
  eapply Hoare_bind.
  - apply Hoare_visit2 with (P := fun s1 => P_loop ∅ s1).
    intros s1 Hv.
    unfold P_loop.
    sets_unfold in Hv.
    repeat split.
    + apply Hv; auto.
    + intros v Hv_vis.
      apply Hv in Hv_vis.
      destruct Hv_vis as [Hv0 | H_eq].
      * left; exact Hv0.
      * subst; right; left; reflexivity.
    + intros e v He; exfalso; exact He.
    + intros w Hw. apply Hv; left; exact Hw.
  - intro; eapply Hoare_bind.
    + apply (Hoare_normalize (P_loop ∅) (set_scc_id u root) (fun _ => P_loop ∅)).
      intros s1 HP.
      apply Hoare_set_scc_id with (P := fun s' => P_loop ∅ s').
      intros s' [Hscc [Hother [Htimer [Hfin [Hv1 [Hv2 Hscc_next]]]]]].
      unfold P_loop; simpl in *.
      destruct HP as [Hs1_vis [P_vis [Hexplored Hincl]]].
      unfold P_loop. split; [rewrite Hv2; exact Hs1_vis | split; [| split; [| rewrite Hv2; exact Hincl]]].
      { intros v Hv. rewrite Hv2 in Hv.
        destruct (P_vis v Hv) as [H0 | [H1 | H2]].
        - left; exact H0.
        - right; left; exact H1.
        - right; right; unfold neighbor_visited; intros w Hstep; rewrite Hv2; apply H2; exact Hstep. }
      { intros e' v' He' Hstep. exfalso; exact He'. }
    + intro. apply Hoare_repeat_break with
        (P := P_loop)
        (Q := fun (_:unit) (s':St) =>
          visited2 s' u /\ visited2 s0 ⊆ visited2 s' /\
          (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v)).
      intros e_set.
      apply Hoare_normalize.
      intros s1 [Hs1_vis [P_vis [Hexplored Hincl]]].
      apply Hoare_choice.
      { apply Hoare_any_bind; intros e.
        apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros H_not_e.
        apply Hoare_normal_assume_bind; intros H_not_vis.
        apply Hoare_normal_assume_bind; intros H_step.
        eapply Hoare_bind with (Q := fun (_:unit) (s':St) =>
          visited2 s' v /\ visited2 s1 ⊆ visited2 s' /\
          (forall w, visited2 s' w -> visited2 s1 w \/ neighbor_visited s' w)).
        { exact (IH s1 v). }
        { intros _; apply Hoare_ret'.
          intros s2 [Hvis_v [Hsubset2 Hneigh2]].
          unfold P_loop.
          repeat split.
          - apply Hsubset2, Hs1_vis.
          - intros w Hvis_w.
            destruct (classic (w = v)) as [Hw_eq | Hw_ne].
            + subst w; right; right.
              destruct (Hneigh2 v Hvis_v) as [Hv_s1 | Hv_neigh];
              [exfalso; apply H_not_vis; exact Hv_s1 | exact Hv_neigh].
            + destruct (classic (visited2 s1 w)) as [Hw_s1 | Hw_not_s1].
              * destruct (P_vis w Hw_s1) as [Hw_s0 | [Hw_u | Hw_neigh]].
                { left; exact Hw_s0. }
                { right; left; exact Hw_u. }
                { right; right; intros x Hstep;
                  apply Hsubset2; apply Hw_neigh; exact Hstep. }
              * destruct (Hneigh2 w Hvis_w) as [Hw_s1' | Hw_neigh].
                { exfalso; apply Hw_not_s1; exact Hw_s1'. }
                { right; right; exact Hw_neigh. }
          - intros e' v' He' Hstep_aux'.
            sets_unfold in He'.
            destruct He' as [He'_in | He'_sing].
            + destruct (classic (e' = e)) as [He'_eq | He'_ne].
              * subst e'.
                destruct (KG.(kos_unique).(step_aux_unique) g e u v u v' g_valid H_step Hstep_aux') as [_ Hv'_eq].
                subst v'; exact Hvis_v.
              * apply Hsubset2; apply (Hexplored e' v' He'_in Hstep_aux').
            + subst e'.
              destruct (KG.(kos_unique).(step_aux_unique) g e u v u v' g_valid H_step Hstep_aux') as [_ Hv'_eq].
              subst v'; exact Hvis_v.
          - etransitivity; eauto. } }
      { apply Hoare_normal_assume_bind; intros Hall.
        unfold Hoare, break, ret.
        intros s' b s'' Hs' Hprog.
        rewrite Hs' in *.
        destruct Hprog as [-> ->].
        simpl.
        repeat split.
        - exact Hs1_vis.
        - exact Hincl.
        - intros w Hvis_w.
          destruct (P_vis w Hvis_w) as [Hw_s0 | [Hw_u | Hw_neigh]].
          + left; exact Hw_s0.
          + subst w; right; unfold neighbor_visited.
            intros v0 Hstep.
            destruct Hstep as [e0 Hstep_aux].
            destruct (Hall e0 v0 Hstep_aux) as [He_in | Hvis_v0].
            { apply (Hexplored e0 v0 He_in Hstep_aux). }
            { exact Hvis_v0. }
          + right; exact Hw_neigh. }
Qed.

(** [DFS_scc_neighbor_visited_strong]
    Fixed-point version of neighbor_visited for DFS_scc.
    Proved property: visited2 s' u /\ visited2 s0 ⊆ visited2 s' /\
      (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v) *)
Lemma DFS_scc_neighbor_visited_strong : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u)
    (fun _ s' => visited2 s' u /\ visited2 s0 ⊆ visited2 s' /\
      (forall v, visited2 s' v -> visited2 s0 v \/ neighbor_visited s' v)).
Proof.
  intros s0 root u.
  unfold DFS_scc.
  apply Hoare_normal_LFix with (Q := fun (u' : V) (s0' : St) (_ : unit) (s' : St) =>
    visited2 s' u' /\ visited2 s0' ⊆ visited2 s' /\
    (forall v, visited2 s' v -> visited2 s0' v \/ neighbor_visited s' v)).
  intros W IH s0' u'.
  apply DFS_scc_neighbor_visited_aux.
  exact IH.
Qed.

(* SCC membership properties for Phase 2 correctness *)
(* L0a: all vertices newly visited by DFS_scc are reachable from u (the
   current vertex) in the original graph.  Direct mirror of
   DFS_finish_reachable_rev with step_rev replaced by step g. *)
(** [DFS_scc_reachable_aux]
    Helper: every newly visited2 vertex is reachable from u (forward graph)
    or was already in s0.
    Proved property: forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v *)
Lemma DFS_scc_reachable_aux : forall root W,
  (forall s0 u,
     Hoare (fun st => st = s0) (W u) (fun _ s' =>
       forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v)) ->
  (forall s0 u,
     Hoare (fun st => st = s0) (DFS_scc_f root W u) (fun _ s' =>
       forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v)).
Proof.
  intros root W IH s0 u.
  unfold DFS_scc_f.
  eapply Hoare_bind.
  - apply Hoare_visit2 with
      (P := fun s1 => forall v, visited2 s1 v -> visited2 s0 v \/ reachable g u v).
    intros s1 Hv.
    sets_unfold in Hv.
    intros v Hv_vis.
    apply Hv in Hv_vis.
    destruct Hv_vis as [H_vis0 | H_eq].
    + left; exact H_vis0.
    + subst v. right. unfold reachable; reflexivity.
  - intro; eapply Hoare_bind.
    + apply (Hoare_normalize (fun st => forall v, visited2 st v -> visited2 s0 v \/ reachable g u v) (set_scc_id u root) (fun _ st => forall v, visited2 st v -> visited2 s0 v \/ reachable g u v)).
      intros s1 HP.
      apply Hoare_set_scc_id with
        (P := fun s' => forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v).
      intros s' [Hscc [Hother [Htimer [Hfin [Hv1 [Hv2 Hscc_next]]]]]].
      rewrite Hv2. exact HP.
    + intro. apply Hoare_repeat_break with
        (P := fun e_set st => forall v, visited2 st v -> visited2 s0 v \/ reachable g u v).
      intros e_set.
      apply Hoare_normalize.
      intros s1 HP.
      apply Hoare_choice.
      { apply Hoare_any_bind; intros e.
        apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros H_not_e.
        apply Hoare_normal_assume_bind; intros H_not_vis.
        apply Hoare_normal_assume_bind; intros H_step.
        eapply Hoare_bind with
          (Q := fun (_:unit) (s':St) =>
            forall v0, visited2 s' v0 -> visited2 s1 v0 \/ reachable g v v0).
        { exact (IH s1 v). }
        { intros _; apply Hoare_ret'.
          intros s2 Hreach_v.
          intros w Hvis_w.
          destruct (Hreach_v w Hvis_w) as [Hw_s1 | Hw_v].
          - apply HP; exact Hw_s1.
          - right. etransitivity; [apply step_rt; exists e; exact H_step | eauto]. } }
      { apply Hoare_normal_assume_bind; intros Hall.
        unfold Hoare, break, ret.
        intros s' b s'' Hs' Hprog.
        rewrite Hs' in *.
        destruct Hprog as [-> ->].
        simpl. exact HP. }
Qed.

(** [DFS_scc_reachable_from_u]
    Fixed-point version: after DFS_scc root u, newly visited2 vertices are
    reachable from u in the original graph.
    Proved property: forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v *)
Lemma DFS_scc_reachable_from_u : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' =>
    forall v, visited2 s' v -> visited2 s0 v \/ reachable g u v).
Proof.
  intros s0 root u.
  unfold DFS_scc.
  apply Hoare_normal_LFix with
    (Q := fun u' s0' _ s' => forall v, visited2 s' v -> visited2 s0' v \/ reachable g u' v).
  intros W IH s0' u'.
  apply DFS_scc_reachable_aux.
  exact IH.
Qed.

(** [DFS_scc_reachable]
    If root is reachable from root -> u, then DFS_scc root u ensures every
    newly visited2 vertex is reachable from root.
    Proved property: forall v, visited2 s' v -> ~visited2 s0 v -> reachable g root v *)
Lemma DFS_scc_reachable : forall s0 root u,
  reachable g root u ->
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' =>
    forall v, visited2 s' v -> ~visited2 s0 v -> reachable g root v).
Proof.
  intros s0 root u Hreach.
  eapply Hoare_imp_post.
  - apply DFS_scc_reachable_from_u.
  - intros junk st H v Hvis_v Hnew.
    destruct (H v Hvis_v) as [H_old | H_reach_u].
    { exfalso; exact (Hnew H_old). }
    { etransitivity; eauto. }
Qed.

(** [DFS_scc_preserves_ForwardReachClosed]
    DFS_scc root u preserves the ForwardReachClosed invariant
    (visited2 is closed under forward reachability g),
    provided u was not already visited2.
    Proved property: ForwardReachClosed s' *)
Lemma DFS_scc_preserves_ForwardReachClosed : forall s0 root u,
  ~ visited2 s0 u ->
  ForwardReachClosed s0 ->
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' => ForwardReachClosed s').
Proof.
  intros s0 root u Hnot_vis Hclosed.
  eapply Hoare_imp_post.
  - apply DFS_scc_neighbor_visited_strong.
  - intros _ s' [Hvis_u [Hsub Hneigh]].
    unfold ForwardReachClosed.
    intros v w0 Hvis_v Hreach.
    destruct (classic (visited2 s0 v)) as [Hv_s0 | Hv_not].
    + apply Hsub.
      exact (Hclosed v w0 Hv_s0 Hreach).
    + destruct (Hneigh v Hvis_v) as [Hv_s0' | Hn_v]; [exfalso; exact (Hv_not Hv_s0') |].
      apply reachable_to_reach_fwd in Hreach.
      induction Hreach as [| z w0' Hrest IH Hstep].
      * exact Hvis_v.
      * destruct (Hneigh z IH) as [Hz_s0 | Hn_z].
        -- apply Hsub.
           exact (Hclosed z w0' Hz_s0 (step_rt g z w0' Hstep)).
        -- exact (Hn_z w0' Hstep).
Qed.

(** [DFS_scc_reachable_visited_closed]
    Under ForwardReachClosed s0, DFS_scc root u visits every vertex
    reachable from u that was not already in visited2 s0.
    The closure condition ensures that the path from u to v contains
    no s0-vertex, so the DFS guard never blocks.
    Proved property: forall v, reachable g u v -> ~visited2 s0 v -> visited2 s' v *)
Lemma DFS_scc_reachable_visited_closed : forall s0 root u,
  ForwardReachClosed s0 ->
  ~ visited2 s0 u ->
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' =>
    forall v, reachable g u v -> ~ visited2 s0 v -> visited2 s' v).
Proof.
  intros s0 root u Hclosed Hnot_u.
  eapply Hoare_imp_post.
  - apply DFS_scc_neighbor_visited_strong.
  - intros _ s' [Hvis_u [Hsub Hneigh]].
    intros v Hreach_v Hnot_v.
    apply reachable_to_reach_fwd in Hreach_v.
    induction Hreach_v as [| z v' Hrest IH Hstep].
    + exact Hvis_u.
    + assert (Hnot_z : ~ visited2 s0 z).
      { intro Hz_s0.
        apply Hnot_v.
        apply (Hclosed z v' Hz_s0).
        apply step_rt; exact Hstep. }
      specialize (IH Hnot_z).
      (* IH : visited2 s' z *)
      destruct (Hneigh z IH) as [Hz_s0 | Hn_z].
      { exfalso; exact (Hnot_z Hz_s0). }
      { exact (Hn_z v' Hstep). }
Qed.

(** [mutually_reachable_from_order]
    Pure logic: if root can reach v, both are visited1, root has max finish
    among vertices not yet visited2, and v is not yet visited2, then
    root and v are mutually reachable.
    Proof: Phase1_Order gives exist c mutually-reachable v c with
    finish root < finish c; ForwardReachClosed + ~visited2 v forces
    ~visited2 c, then max-finish contradicts the strict inequality.
    Therefore reachable_rev root v must hold, giving mutually_reachable. *)
Lemma mutually_reachable_from_order : forall s root v,
  Phase1_Order s ->
  ForwardReachClosed s ->
  reachable g root v ->
  (forall w, ~ visited2 s w -> finish s root >= finish s w) ->
  ~ visited2 s v ->
  mutually_reachable root v.
Proof.
  intros s root v Hphase Hclosed Hreach Hmax Hnot2.
  apply reachable_iff_reachable_rev in Hreach.
  destruct (classic (reachable_rev root v)) as [Hrev | Hnot_rev].
  - apply reachable_iff_reachable_rev in Hreach.
    apply reachable_iff_reachable_rev in Hrev.
    split; assumption.
  - destruct (Hphase v root Hreach Hnot_rev) as (c & Hmut & Hfin_lt).
    destruct Hmut as (Hv2c & Hc2v).
    assert (Hnot_c : ~ visited2 s c) by
      (intro Hc; apply Hnot2; apply (Hclosed c v Hc Hc2v)).
    specialize (Hmax c Hnot_c); lia.
Qed.

(** [DFS_scc_mutually_reachable_root]
    Under ForwardReachClosed, OrderInv, all-visited1, and max-finish,
    every vertex newly visited2 by DFS_scc root root is mutually reachable
    with root.
    Proved property: forall v, visited2 s' v -> ~visited2 s0 v -> mutually_reachable root v *)
Lemma DFS_scc_mutually_reachable_root : forall s0 root,
  ForwardReachClosed s0 ->
  Phase1_Order s0 ->
  ~ visited2 s0 root ->
  (forall w, ~ visited2 s0 w -> finish s0 root >= finish s0 w) ->
  Hoare (fun st => st = s0) (DFS_scc root root) (fun _ s' =>
    forall v, visited2 s' v -> ~ visited2 s0 v -> mutually_reachable root v).
Proof.
  intros s0 root Hclosed Hphase Hnot2_r Hmax.
  eapply Hoare_imp_post.
  - apply DFS_scc_reachable_from_u.
  - intros a s' Hreachable.
    intros x Hvis_x Hnew.
    destruct (Hreachable x Hvis_x) as [Hx_s0 | Hreach_x].
    + exfalso; exact (Hnew Hx_s0).
    + exact (mutually_reachable_from_order s0 root x
        Hphase Hclosed Hreach_x Hmax Hnew).
Qed.

(** [DFS_scc_visits_scc]
    Under ForwardReachClosed and max-finish, DFS_scc root root visits
    every vertex mutually reachable with root that is not already visited2.
    Proof: mutual → reachable, then DFS_scc_reachable_visited_closed.
    Proved property: forall v, mutually_reachable root v -> ~visited2 s0 v -> visited2 s' v *)
Lemma DFS_scc_visits_scc : forall s0 root,
  ForwardReachClosed s0 ->
  ~ visited2 s0 root ->
  (forall w, ~ visited2 s0 w -> finish s0 root >= finish s0 w) ->
  Hoare (fun st => st = s0) (DFS_scc root root) (fun _ s' =>
    forall v, mutually_reachable root v -> ~ visited2 s0 v -> visited2 s' v).
Proof.
  intros s0 root Hclosed Hnot2_r Hmax.
  eapply Hoare_imp_post.
  - apply (DFS_scc_reachable_visited_closed s0 root root Hclosed Hnot2_r).
  - intros a s' Hreach_closed.
    intros x Hmut Hnew.
    apply Hreach_closed.
    + destruct Hmut; assumption.
    + exact Hnew.
Qed.

(* Every new vertex gets the same scc_id as root.
   Together with scc_next counter uniqueness, this gives:
   same scc_id → same SCC iteration → mutually reachable. *)
(** [DFS_scc_same_root_id]
    All newly visited2 vertices get the same scc_id as root,
    and scc_id of already-visited vertices is preserved. *)
Lemma DFS_scc_same_root_id : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' =>
    (forall v, visited2 s' v -> ~visited2 s0 v -> scc_id s' v = scc_id s' root) /\
    (forall v, visited2 s0 v -> v <> u -> scc_id s' v = scc_id s0 v) /\
    scc_id s' root = scc_id s0 root /\
    visited2 s0 ⊆ visited2 s').
Proof.
  intros s0 root u.
  unfold DFS_scc.
  set (Q := fun (u': V) (s0': St) (_ : unit) (s' : St) =>
    (forall v, visited2 s' v -> ~visited2 s0' v -> scc_id s' v = scc_id s' root) /\
    (forall v, visited2 s0' v -> v <> u' -> scc_id s' v = scc_id s0' v) /\
    scc_id s' root = scc_id s0' root /\
    visited2 s0' ⊆ visited2 s').
  eapply Hoare_imp_post.
  { apply Hoare_normal_LFix with (Q := Q).
    intros W IH s0' u'.
  unfold Q; simpl.
  unfold DFS_scc_f.
  set (P_loop := fun (e_set: E -> Prop) (st: St) =>
    (forall v, visited2 st v -> ~visited2 s0' v -> scc_id st v = scc_id st root) /\
    (forall v, visited2 s0' v -> v <> u' -> scc_id st v = scc_id s0' v) /\
    scc_id st root = scc_id s0' root /\
    visited2 s0' ⊆ visited2 st).
  apply Hoare_bind with (Q := fun (_:unit) (s':St) => visited2 s' u' /\ visited2 s' == visited2 s0' ∪ Sets.singleton u' /\ scc_id s' = scc_id s0').
  + (* visit2 u' *)
    unfold Hoare, visit2.
    intros s1 a s2 Hs1 Hprog.
    rewrite Hs1 in *.
    destruct Hprog as [Hv [Htimer [Hfin [Hv1 [Hsid Hscc_next]]]]].
    split; [| split].
    - sets_unfold. apply Hv. right; reflexivity.
    - exact Hv.
    - exact Hsid.
  + intros junk. apply Hoare_normalize.
    intros s2 [Hvis_u2 [Hv_char2 Hscc_eq]].
    eapply Hoare_bind.
    * (* set_scc_id u' root *)
      apply Hoare_set_scc_id with (P := fun s' => P_loop ∅ s').
      intros s' [Hscc [Hother [Htimer [Hfin [Hv1 [Hv2 Hscc_next]]]]]].
      unfold P_loop.
      repeat split.
      { (* first conjunct: new vertices get root's scc_id *)
        intros v Hvis_v Hnew_v.
        rewrite Hv2 in Hvis_v. apply Hv_char2 in Hvis_v.
        sets_unfold in Hvis_v.
        destruct Hvis_v as [Hv0 | Hv_eq].
        { exfalso; exact (Hnew_v Hv0). }
        { subst v.
          destruct (classic (root = u')) as [Hr_eq | Hr_ne].
          - subst root. reflexivity.
          - rewrite (Hother root Hr_ne). apply Hscc. } }
      { (* second conjunct: old vertices (except u') preserve scc_id *)
        intros v Hv0 Hv_ne.
        rewrite (Hother v Hv_ne), Hscc_eq. reflexivity. }
      { (* third conjunct: scc_id root unchanged *)
        destruct (classic (root = u')) as [Hr_eq | Hr_ne].
        - subst root. rewrite Hscc, Hscc_eq. reflexivity.
        - rewrite (Hother root Hr_ne), Hscc_eq. reflexivity. }
      { (* fourth conjunct: visited2 monotonic *)
        intros w Hw_s0. rewrite Hv2. apply (proj2 (Hv_char2 w)). left; exact Hw_s0. }
    * intro junk2. simpl.
      apply Hoare_repeat_break with (P := P_loop)
        (Q := fun (_ : unit) (s' : St) => P_loop ∅ s').
      intros e_set.
      apply Hoare_normalize.
      intros s1 [HP1 [HP2 [HP3 HP4]]].
      apply Hoare_choice.
      { (* recursive branch: pick e, v, call W v *)
        apply Hoare_any_bind; intros e.
        apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros H_not_e.
        apply Hoare_normal_assume_bind; intros H_not_vis.  (* ~visited2 s1 v *)
        apply Hoare_normal_assume_bind; intros H_step.
        eapply Hoare_bind with (Q := Q v s1).
        { exact (IH s1 v). }
        { intro junk3. simpl. apply Hoare_ret'.
          intros s3 [Hnew_s3 [Hpres_s3 [Hroot_s3 Hsub3]]].
          unfold P_loop.
          repeat split.
          - (* first conjunct: new vertices get root's scc_id *)
            intros w Hvis_w Hnew_w.
            destruct (classic (visited2 s1 w)) as [Hw_s1 | Hw_not_s1].
            + (* w already visited in s1 *)
              assert (Heq1 : scc_id s1 w = scc_id s1 root) by (apply HP1; auto).
              assert (Hw_ne_v : w <> v) by (intro Heq; subst w; exact (H_not_vis Hw_s1)).
              rewrite (Hpres_s3 w Hw_s1 Hw_ne_v).
              rewrite Hroot_s3. exact Heq1.
            + (* w is new relative to s1 *)
              apply Hnew_s3; auto.
          - (* second conjunct: old vertices preserve scc_id *)
            intros w Hw_s0 Hw_ne_u.
            assert (Heq2 : scc_id s1 w = scc_id s0' w) by (apply HP2; auto).
            assert (Hw_s1 : visited2 s1 w) by (apply HP4; exact Hw_s0).
            assert (Hw_ne_v : w <> v) by (intro Heq; subst w; exact (H_not_vis Hw_s1)).
            rewrite (Hpres_s3 w Hw_s1 Hw_ne_v). exact Heq2.
          - (* third conjunct: scc_id root unchanged *)
            rewrite Hroot_s3, HP3. reflexivity.
          - (* fourth conjunct: visited2 monotonic *)
            intros w Hw_s0. apply Hsub3, HP4; exact Hw_s0. } }
      { (* break branch *)
        apply Hoare_normal_assume_bind; intros Hall.
        unfold Hoare, break, ret.
        intros s'' b' s''' Hs'' Hprog.
        rewrite Hs'' in *.
        destruct Hprog as [-> ->].
        simpl. exact (conj HP1 (conj HP2 (conj HP3 HP4))). } }
  { simpl. intros a s' H. exact H. }
Qed.

(** [mutually_reachable_unvisited2]
    If root has max finish among unvisited vertices and is itself unvisited,
    then any vertex mutually reachable with root is also unvisited.
    Proof: if v were visited2 and reachable back to root, ForwardReachClosed
    would force root ∈ visited2, contradiction. *)
Lemma mutually_reachable_unvisited2 : forall s root v,
  ForwardReachClosed s ->
  ~ visited2 s root ->
  mutually_reachable root v ->
  ~ visited2 s v.
Proof.
  intros s root v Hclosed Hnot_r [Hr2v Hv2r] Hv.
  apply Hnot_r, (Hclosed v root Hv Hv2r).
Qed.

(** [DFS_scc_new_mutually_reachable]
    All vertices newly visited by DFS_scc root root are mutually reachable
    with each other.  Follows from DFS_scc_mutually_reachable_root
    (new → mutually reachable with root) and mutually_reachable_trans/sym.
    Proved property: forall u v, visited2 s' u -> visited2 s' v ->
      ~visited2 s0 u -> ~visited2 s0 v -> mutually_reachable u v *)
Lemma DFS_scc_new_mutually_reachable : forall s0 root,
  ForwardReachClosed s0 ->
  Phase1_Order s0 ->
  ~ visited2 s0 root ->
  (forall w, ~ visited2 s0 w -> finish s0 root >= finish s0 w) ->
  Hoare (fun st => st = s0) (DFS_scc root root) (fun _ s' =>
    forall u v, visited2 s' u -> visited2 s' v ->
      ~ visited2 s0 u -> ~ visited2 s0 v ->
      mutually_reachable u v).
Proof.
  intros s0 root Hclosed Hphase Hnot2 Hmax.
  eapply Hoare_imp_post.
  - apply (DFS_scc_mutually_reachable_root s0 root Hclosed Hphase Hnot2 Hmax).
  - intros a s' Hmut_root.
    intros u v Hvis_u Hvis_v Hnew_u Hnew_v.
    apply Hmut_root in Hvis_u; auto.
    apply Hmut_root in Hvis_v; auto.
    apply mutually_reachable_sym in Hvis_u.
    apply mutually_reachable_trans with (v := root); assumption.
Qed.

(** The invariant R(s) maintained by kosaraju_scc:
    - ForwardReachClosed: no forward edge crosses visited2 boundary
    - Phase1_Order: condensation-DAG finish ordering (immutable in Phase 2)
    - visited1-all: every vertex has been visited1 (immutable)
    - scc_id < scc_next: visited2 scc_ids from past rounds
    - correctness: scc_id equality iff mutually reachable within visited2 *)
Definition R (s : St) : Prop :=
  ForwardReachClosed s /\
  Phase1_Order s /\
  (forall v, visited1 s v) /\
  (forall v, visited2 s v -> scc_id s v < scc_next s) /\
  (forall u v, visited2 s u -> visited2 s v ->
    (scc_id s u = scc_id s v <-> mutually_reachable u v)).

Lemma set_scc_root_id_R : forall s0 root,
  R s0 -> ~ visited2 s0 root ->
  Hoare (fun st => st = s0) (set_scc_root_id root) (fun _ s1 =>
    visited2 s1 = visited2 s0 /\ visited1 s1 = visited1 s0 /\ finish s1 = finish s0 /\
    R s1 /\ scc_id s1 root = scc_next s0 /\ scc_next s1 = S (scc_next s0) /\
    (forall v, v <> root -> scc_id s1 v = scc_id s0 v)).
Proof.
  intros s0 root [Hclosed [Hphase [Hvis1 [Hscclt Hcorrect]]]] Hnot_root.
  apply Hoare_set_scc_root_id with (P := fun s1 =>
    visited2 s1 = visited2 s0 /\ visited1 s1 = visited1 s0 /\ finish s1 = finish s0 /\
    R s1 /\ scc_id s1 root = scc_next s0 /\ scc_next s1 = S (scc_next s0) /\
    (forall v, v <> root -> scc_id s1 v = scc_id s0 v)).
  intros s1 [Hroot_id [Hscc_next [Hother [Htimer [Hfin [Hv1 Hv2]]]]]].
  assert (HR1 : R s1). {
    unfold R; split; [| split; [| split; [| split]]].
    { intros u v Hvis Hreach. rewrite Hv2 in Hvis.
      specialize (Hclosed u v Hvis Hreach). rewrite Hv2; exact Hclosed. }
    { intros a b Hrev Hnot. destruct (Hphase a b Hrev Hnot) as [c [Hmut Hfin_lt]].
      exists c; split; [exact Hmut | rewrite Hfin; exact Hfin_lt]. }
    { intros v. rewrite Hv1. apply Hvis1. }
    { intros v Hvis. rewrite Hv2 in Hvis.
      destruct (classic (v = root)) as [Hv_eq | Hv_ne].
      - subst v. exfalso; apply Hnot_root; exact Hvis.
      - rewrite (Hother v Hv_ne). apply Hscclt in Hvis; rewrite Hscc_next; lia. }
    { intros u v Hvis_u Hvis_v. rewrite Hv2 in Hvis_u, Hvis_v.
      destruct (classic (u = root)) as [Hu_eq | Hu_ne];
      destruct (classic (v = root)) as [Hv_eq | Hv_ne].
      - subst u v. exfalso; apply Hnot_root; exact Hvis_u.
      - subst u. exfalso; apply Hnot_root; exact Hvis_u.
      - subst v. exfalso; apply Hnot_root; exact Hvis_v.
      - rewrite (Hother u Hu_ne), (Hother v Hv_ne). apply Hcorrect; assumption. } }
  exact (conj Hv2 (conj Hv1 (conj Hfin (conj HR1 (conj Hroot_id (conj Hscc_next Hother)))))).
Qed.

Lemma visit2_preserves_scc_next : forall s0 u,
  Hoare (fun st => st = s0) (visit2 u) (fun _ s' => scc_next s' = scc_next s0).
Proof.
  intros s0 u. intros s1 a s2 Hs1 Hprog. subst s1.
  sets_unfold in Hprog.
  unfold visit2 in Hprog.
  simpl in Hprog.
  destruct Hprog as [_ [_ [_ [_ [_ Hscc]]]]]. exact Hscc.
Qed.

Lemma set_scc_id_preserves_scc_next : forall s0 u root0,
  Hoare (fun st => st = s0) (set_scc_id u root0) (fun _ s' => scc_next s' = scc_next s0).
Proof.
  intros s0 u root0. intros s1 a s2 Hs1 Hprog. subst s1.
  sets_unfold in Hprog.
  unfold set_scc_id in Hprog. simpl in Hprog.
  destruct Hprog as [_ [_ [_ [_ [_ [_ Hscc]]]]]]. exact Hscc.
Qed.

Lemma DFS_scc_preserves_scc_next : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' => scc_next s' = scc_next s0).
Proof.
  intros s0 root u. unfold DFS_scc.
  apply Hoare_normal_LFix with
    (Q := fun (_:V) (s0':St) (_:unit) (s':St) => scc_next s' = scc_next s0').
  intros W IH s0' u'. unfold DFS_scc_f.
  apply Hoare_bind with
    (Q := fun (_:unit) (s':St) => scc_next s' = scc_next s0').
  + (* visit2 u' *) apply visit2_preserves_scc_next.
  + (* set_scc_id ;; loop *)
    intro junk. apply Hoare_normalize. intros s1 Hscc_eq1.
    apply Hoare_bind with
      (Q := fun (_:unit) (s':St) => scc_next s' = scc_next s0').
    * (* set_scc_id: postcondition is scc_next s' = scc_next s1, need to convert *)
      eapply Hoare_imp_post.
      - apply set_scc_id_preserves_scc_next.
      - simpl. intros _ s' Heq. rewrite Heq. exact Hscc_eq1.
    * intro junk2.
      apply Hoare_repeat_break with
        (P := fun _ st => scc_next st = scc_next s0')
        (Q := fun _ s' => scc_next s' = scc_next s0').
      intros e_set. apply Hoare_normalize. intros s Hinv.
      apply Hoare_choice.
      { apply Hoare_any_bind; intros e; apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros _. apply Hoare_normal_assume_bind; intros _.
        apply Hoare_normal_assume_bind; intros _. eapply Hoare_bind.
        - exact (IH s v).
        - intro; apply Hoare_ret'. intros s' Hnext. etransitivity; eauto. }
      { apply Hoare_normal_assume_bind; intros Hall.
        unfold Hoare, break, ret.
        intros s'' b' s''' Hs'' Hprog.
        rewrite Hs'' in *.
        destruct Hprog as [-> ->].
        simpl. exact Hinv. } 
Qed.

Lemma DFS_scc_preserves_visited1 : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' => visited1 s' = visited1 s0).
Proof.
  intros s0 root u. unfold DFS_scc.
  apply Hoare_normal_LFix with
    (Q := fun (_:V) (s0':St) (_:unit) (s':St) => visited1 s' = visited1 s0').
  intros W IH s0' u'. unfold DFS_scc_f.
  apply Hoare_bind with
    (Q := fun (_:unit) (s':St) => visited1 s' = visited1 s0').
  + intros s1 a s2 Hs1 Hprog. subst s1. sets_unfold in Hprog.
    unfold visit2 in Hprog. simpl in Hprog.
    destruct Hprog as [_ [_ [_ [Hv1 _]]]]. exact Hv1.
  + intro junk. apply Hoare_normalize. intros s1 Hv1_eq1.
    apply Hoare_bind with
      (Q := fun (_:unit) (s':St) => visited1 s' = visited1 s0').
    * eapply Hoare_imp_post.
      - intros s3 a s4 Hs3 Hprog. subst s3. sets_unfold in Hprog.
        unfold set_scc_id in Hprog. simpl in Hprog.
        destruct Hprog as [_ [_ [_ [_ [Hv1 _]]]]]. exact Hv1.
      - simpl. intros _ s' Heq. rewrite Heq. exact Hv1_eq1.
    * intro junk2.
      apply Hoare_repeat_break with
        (P := fun _ st => visited1 st = visited1 s0')
        (Q := fun _ s' => visited1 s' = visited1 s0').
      intros e_set. apply Hoare_normalize. intros s Hinv.
      apply Hoare_choice.
      { apply Hoare_any_bind; intros e; apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros _. apply Hoare_normal_assume_bind; intros _.
        apply Hoare_normal_assume_bind; intros _. eapply Hoare_bind.
        - exact (IH s v).
        - intro; apply Hoare_ret'. intros s' Hnext. etransitivity; eauto. }
      { apply Hoare_normal_assume_bind; intros Hall.
        unfold Hoare, break, ret.
        intros s'' b' s''' Hs'' Hprog. rewrite Hs'' in *. destruct Hprog as [-> ->].
        simpl. exact Hinv. }
Qed.

Lemma DFS_scc_preserves_finish : forall s0 root u,
  Hoare (fun st => st = s0) (DFS_scc root u) (fun _ s' => finish s' = finish s0).
Proof.
  intros s0 root u. unfold DFS_scc.
  apply Hoare_normal_LFix with
    (Q := fun (_:V) (s0':St) (_:unit) (s':St) => finish s' = finish s0').
  intros W IH s0' u'. unfold DFS_scc_f.
  apply Hoare_bind with
    (Q := fun (_:unit) (s':St) => finish s' = finish s0').
  + intros s1 a s2 Hs1 Hprog. subst s1. sets_unfold in Hprog.
    unfold visit2 in Hprog. simpl in Hprog.
    destruct Hprog as [_ [_ [Hfin _]]]. exact Hfin.
  + intro junk. apply Hoare_normalize. intros s1 Hfin_eq1.
    apply Hoare_bind with
      (Q := fun (_:unit) (s':St) => finish s' = finish s0').
    * eapply Hoare_imp_post.
      - intros s3 a s4 Hs3 Hprog. subst s3. sets_unfold in Hprog.
        unfold set_scc_id in Hprog. simpl in Hprog.
        destruct Hprog as [_ [_ [_ [Hfin _]]]]. exact Hfin.
      - simpl. intros _ s' Heq. rewrite Heq. exact Hfin_eq1.
    * intro junk2.
      apply Hoare_repeat_break with
        (P := fun _ st => finish st = finish s0')
        (Q := fun _ s' => finish s' = finish s0').
      intros e_set. apply Hoare_normalize. intros s Hinv.
      apply Hoare_choice.
      { apply Hoare_any_bind; intros e; apply Hoare_any_bind; intros v.
        apply Hoare_normal_assume_bind; intros _. apply Hoare_normal_assume_bind; intros _.
        apply Hoare_normal_assume_bind; intros _. eapply Hoare_bind.
        - exact (IH s v).
        - intro; apply Hoare_ret'. intros s' Hnext. etransitivity; eauto. }
      { apply Hoare_normal_assume_bind; intros Hall.
        unfold Hoare, break, ret.
        intros s'' b' s''' Hs'' Hprog. rewrite Hs'' in *. destruct Hprog as [-> ->].
        simpl. exact Hinv. }
Qed.

Lemma DFS_scc_R : forall s1 root,
  R s1 -> ~ visited2 s1 root ->
  (forall w, ~ visited2 s1 w -> finish s1 root >= finish s1 w) ->
  (forall v, visited2 s1 v -> scc_id s1 v < scc_id s1 root) ->
  scc_id s1 root < scc_next s1 ->
  Hoare (fun st => st = s1) (DFS_scc root root) (fun _ s' => R s').
Proof.
  intros s1 root [Hclosed [Hphase [Hvis1 [Hscclt Hcorrect]]]] Hnot_root Hmax Hlt_root Hroot_lt.
  eapply Hoare_imp_post.
  - apply Hoare_conj.
    + apply (DFS_scc_preserves_ForwardReachClosed s1 root root Hnot_root Hclosed).
    + apply Hoare_conj.
      * apply (DFS_scc_mutually_reachable_root s1 root Hclosed Hphase Hnot_root Hmax).
      * apply Hoare_conj with
          (Q1 := fun _ s' =>
            (forall v, visited2 s' v -> ~visited2 s1 v -> scc_id s' v = scc_id s' root) /\
            (forall v, visited2 s1 v -> v <> root -> scc_id s' v = scc_id s1 v) /\
            scc_id s' root = scc_id s1 root /\
            visited2 s1 ⊆ visited2 s')
          (Q2 := fun _ s' => visited1 s' = visited1 s1 /\ finish s' = finish s1 /\ scc_next s' = scc_next s1).
        -- apply (DFS_scc_same_root_id s1 root root).
        -- apply Hoare_conj.
           ++ apply (DFS_scc_preserves_visited1 s1 root root).
           ++ apply Hoare_conj.
              ** apply (DFS_scc_preserves_finish s1 root root).
              ** apply (DFS_scc_preserves_scc_next s1 root root).
  - intro a0. intro s'. simpl. intro Hpost.
    destruct Hpost as [Hclosed2 [Hmut_root [Hsame4 [Hv1_eq [Hfin_eq Hscc_next_eq]]]]].
    destruct Hsame4 as [Hsame_id [Hpres_id [Hroot_id2 Hsub2]]].
    unfold R; split; [| split; [| split; [| split]]].
    { exact Hclosed2. }
    { intros a b Hrev Hnot. destruct (Hphase a b Hrev Hnot) as [c [Hmut Hfin_lt]].
      exists c; split; [exact Hmut | rewrite Hfin_eq; exact Hfin_lt]. }
    { intro x. rewrite Hv1_eq. apply Hvis1. }
    { intros x Hvis.
      destruct (classic (visited2 s1 x)) as [Hv_s1 | Hv_new].
      - assert (Hx_ne_root : x <> root). { intro Heq; subst x. apply Hnot_root; exact Hv_s1. }
        pose proof (Hpres_id x Hv_s1 Hx_ne_root) as Heq_id.
        rewrite Heq_id. rewrite Hscc_next_eq. apply Hscclt; exact Hv_s1.
      - pose proof (Hsame_id x Hvis Hv_new) as Heq_root.
        rewrite Heq_root, Hroot_id2. rewrite Hscc_next_eq. apply Hroot_lt. }
    { intros u v Hvis_u Hvis_v.
      destruct (classic (visited2 s1 u)) as [Hu_s1 | Hu_new];
      destruct (classic (visited2 s1 v)) as [Hv_s1 | Hv_new].
      - assert (Hu_ne_root : u <> root). { intro Heq; subst u. apply Hnot_root; exact Hu_s1. }
        assert (Hv_ne_root : v <> root). { intro Heq; subst v. apply Hnot_root; exact Hv_s1. }
        rewrite (Hpres_id u Hu_s1 Hu_ne_root), (Hpres_id v Hv_s1 Hv_ne_root).
        apply Hcorrect; assumption.
      - assert (Hu_ne_root : u <> root). { intro Heq; subst u. apply Hnot_root; exact Hu_s1. }
        pose proof (Hsame_id v Hvis_v Hv_new) as Heq_v.
        rewrite (Hpres_id u Hu_s1 Hu_ne_root), Heq_v. split.
        + intro Heq. exfalso. pose proof (Hlt_root u Hu_s1) as Htemp.
          assert (Heq' : scc_id s1 u = scc_id s1 root). { transitivity (scc_id s' root); [| assumption]. apply Heq. }
          rewrite Heq' in Htemp. lia.
        + intros [Hreach _]. exfalso. apply Hv_new. apply (Hclosed u v Hu_s1 Hreach).
      - assert (Hv_ne_root : v <> root). { intro Heq; subst v. apply Hnot_root; exact Hv_s1. }
        pose proof (Hsame_id u Hvis_u Hu_new) as Heq_u.
        rewrite (Hpres_id v Hv_s1 Hv_ne_root), Heq_u. split.
        + intro Heq. exfalso. pose proof (Hlt_root v Hv_s1) as Htemp.
          assert (Heq' : scc_id s1 v = scc_id s1 root). { transitivity (scc_id s' root); [| assumption]. symmetry; assumption. }
          rewrite Heq' in Htemp. lia.
        + intros [_ Hreach]. exfalso. apply Hu_new. apply (Hclosed v u Hv_s1 Hreach).
      - pose proof (Hmut_root u Hvis_u Hu_new) as Hmut_u.
        pose proof (Hmut_root v Hvis_v Hv_new) as Hmut_v.
        pose proof (Hsame_id u Hvis_u Hu_new) as Heq_u.
        pose proof (Hsame_id v Hvis_v Hv_new) as Heq_v. 
        rewrite Heq_u, Heq_v. split.
        + intros _. apply mutually_reachable_sym in Hmut_u.
          apply mutually_reachable_trans with (v := root); assumption.
        + intros Hmut. reflexivity. } 
Qed.

(* ================================================================= *)
(* 5. Outer Phase 2 — kosaraju_scc                                    *)
(* ================================================================= *)

(** [kosaraju_scc_all_visited_aux]
    Helper: one iteration of kosaraju_scc_f visits all vertices in visited2.
    Proved property: forall v, visited2 s' v *)
Lemma kosaraju_scc_all_visited_aux : forall W,
  (forall s0, Hoare (fun st => st = s0) (W tt) (fun _ s' => forall v, visited2 s' v)) ->
  (forall s0, Hoare (fun st => st = s0) (kosaraju_scc_f W tt) (fun _ s' => forall v, visited2 s' v)).
Proof.
  intros W IH s0.
  unfold kosaraju_scc_f.
  apply Hoare_choice.
  { apply Hoare_bind with (Q := fun (u:V) (s':St) => s' = s0 /\ ~ visited2 s' u).
    { unfold Hoare, pick_unvisited2, get.
      intros s1 u s2 Hs1 Hprog.
      rewrite Hs1 in *.
      destruct Hprog as [[Hnot_vis _] Hsame].
      rewrite Hsame in Hnot_vis; split; [symmetry; exact Hsame | exact Hnot_vis]. }
    { intro u.
      apply Hoare_normalize.
      intros s1 [Hs1_eq Hunvis].
      rewrite Hs1_eq.
      simpl.
      eapply Hoare_bind with (Q := fun (_:unit) (s':St) => True).
      { apply Hoare_set_scc_root_id with (P := fun _ => True).
        intros s' _. exact I. }
      { intro junk. apply Hoare_normalize; intros s2 Htrue.
        apply Hoare_bind with (Q := fun (_:unit) (s':St) => visited2 s' u).
        { eapply Hoare_imp_post.
          { apply DFS_scc_neighbor_visited_strong. }
          { intros _ s' [Hvis_u _]; exact Hvis_u. } }
        { intro a; apply Hoare_normalize; intros s3 _; apply (IH s3). } } } }
  { apply Hoare_assume_bind with (Q := fun st => forall v, visited2 st v).
    apply Hoare_ret'.
    intros s1 [Hall _]; exact Hall. }
Qed.

(** [kosaraju_scc_all_visited]
    After the full kosaraju_scc, all vertices are visited2.
    Proved property: forall v, visited2 s' v *)
Lemma kosaraju_scc_all_visited : forall s0,
  Hoare (fun st => st = s0) kosaraju_scc (fun _ s' => forall v, visited2 s' v).
Proof.
  intros s0.
  unfold kosaraju_scc.
  apply Hoare_normal_LFix with (Q := fun (_:unit) (s0':St) (_:unit) (s':St) => forall v, visited2 s' v).
  intros W IH s0' u.
  apply kosaraju_scc_all_visited_aux.
  intro s0''; apply (IH s0'' tt).
Qed.

(** [kosaraju_scc_preserves_ForwardReachClosed]
    The outer loop kosaraju_scc preserves ForwardReachClosed.
    Each round: set_scc_root_id touches neither visited2 nor visited1;
    DFS_scc preserves it (DFS_scc_preserves_ForwardReachClosed).
    Proved property: ForwardReachClosed s' *)
Lemma kosaraju_scc_preserves_ForwardReachClosed : forall s0,
  ForwardReachClosed s0 ->
  Hoare (fun st => st = s0) kosaraju_scc (fun _ s' => ForwardReachClosed s').
Proof.
  intros s0 Hclosed.
  unfold kosaraju_scc.
  apply Hoare_normal_LFix_closed with
    (R := ForwardReachClosed)
    (Q := fun (_:unit) (_:St) (_:unit) (s':St) => ForwardReachClosed s').
  { intros W IH s0' u0 Hclosed'.
    unfold kosaraju_scc_f.
    apply Hoare_choice.
    { (* recursive branch: pick root -> set_scc_root_id -> DFS_scc -> W *)
      apply Hoare_bind with (Q := fun (u:V) (s':St) => s' = s0' /\ ~ visited2 s' u).
      { unfold Hoare, pick_unvisited2, get.
        intros s1 u s2 Hs1 Hprog.
        rewrite Hs1 in *.
        destruct Hprog as [[Hnot_vis _] Hsame].
        rewrite Hsame in Hnot_vis; split; auto. }
      { intro root.
        apply Hoare_normalize.
        intros s1 [Hs1_eq Hunvis]; subst s1.
        eapply Hoare_bind with (Q := fun (_:unit) (s':St) => visited2 s' = visited2 s0' /\ scc_id s' root = scc_next s0' /\ scc_next s' = S (scc_next s0')).
        { apply Hoare_set_scc_root_id with (P := fun s' => visited2 s' = visited2 s0' /\ scc_id s' root = scc_next s0' /\ scc_next s' = S (scc_next s0')).
          intros s' [Hroot_id [Hscc_next [Hother [Htimer [Hfin [Hv1 Hv2]]]]]].
          repeat split; auto. }
        { intro junk. apply Hoare_normalize; intros s2 [Hv2_eq [Hroot_id Hscc_next]].
          assert (Hclosed2 : ForwardReachClosed s2). {
            unfold ForwardReachClosed in *.
            intros v w Hvis Hreach.
            rewrite Hv2_eq in Hvis.
            specialize (Hclosed' v w Hvis Hreach) as Hw.
            rewrite Hv2_eq; exact Hw.
          }
          eapply Hoare_bind with (Q := fun (_:unit) (s':St) => ForwardReachClosed s').
          { apply (DFS_scc_preserves_ForwardReachClosed s2 root root).
            - rewrite Hv2_eq; exact Hunvis.
            - exact Hclosed2. }
          { intro junk2. apply Hoare_normalize; intros s3 Hclosed3.
            exact (IH s3 tt Hclosed3). } } } }
    { (* non-recursive branch: all visited, skip *)
      apply Hoare_normal_assume_bind with
        (P := fun st => forall v, visited2 st v)
        (f := skip)
        (Q := fun (_:unit) (s':St) => ForwardReachClosed s')
        (s0 := s0').
      intros Hall.
      apply Hoare_ret'; intros s Hs; subst s; exact Hclosed'. } }
  { exact Hclosed. }
Qed.

Lemma round_preserves_R : forall s0 root,
  R s0 -> ~ visited2 s0 root ->
  (forall w, ~ visited2 s0 w -> finish s0 root >= finish s0 w) ->
  Hoare (fun st => st = s0) (set_scc_root_id root ;; DFS_scc root root) (fun _ s' => R s').
Proof.
  intros s0 root HR Hnot_root Hmax.
  destruct HR as [Hclosed [Hphase [Hvis1 [Hscclt Hcorrect]]]].
  eapply Hoare_bind.
  - apply (set_scc_root_id_R s0 root (conj Hclosed (conj Hphase (conj Hvis1 (conj Hscclt Hcorrect)))) Hnot_root).
  - intro junk. apply Hoare_normalize.
    intros s1 [Hv2_eq [Hv1_eq [Hfin_eq [HR1 [Hroot_id [Hscc_next Hother]]]]]].
    assert (Hnot_root' : ~ visited2 s1 root). { rewrite Hv2_eq; exact Hnot_root. }
    assert (Hmax' : forall w, ~ visited2 s1 w -> finish s1 root >= finish s1 w). {
      intros w Hw. rewrite Hv2_eq in Hw. rewrite Hfin_eq. apply Hmax; exact Hw. }
    assert (Hlt_root : forall v, visited2 s1 v -> scc_id s1 v < scc_id s1 root). {
      intros v Hv. rewrite Hv2_eq in Hv.
      destruct (classic (v = root)) as [Hv_eq | Hv_ne].
      - subst v. exfalso. apply Hnot_root. exact Hv.
      - rewrite (Hother v Hv_ne). rewrite Hroot_id. pose proof (Hscclt v Hv). lia. }
    assert (Hroot_lt : scc_id s1 root < scc_next s1). {
      rewrite Hroot_id, Hscc_next. abstract lia. }
    apply (DFS_scc_R s1 root HR1 Hnot_root' Hmax' Hlt_root Hroot_lt).
Qed.

Lemma round_W_R : forall s0' root (W : unit -> program St unit),
  R s0' -> ~ visited2 s0' root ->
  (forall w, ~ visited2 s0' w -> finish s0' root >= finish s0' w) ->
  (forall s, R s -> Hoare (fun st => st = s) (W tt) (fun _ s' => R s')) ->
  Hoare (fun st => st = s0') (set_scc_root_id root ;; (DFS_scc root root ;; W tt)) (fun _ s' => R s').
Proof.
  intros s0' root W HR' Hnot_root2 Hmax2 IHW.
  destruct HR' as [Hclosed [Hphase [Hvis1 [Hscclt Hcorrect]]]].
  eapply Hoare_bind.
  - apply (set_scc_root_id_R s0' root (conj Hclosed (conj Hphase (conj Hvis1 (conj Hscclt Hcorrect)))) Hnot_root2).
  - intro junk. apply Hoare_normalize.
    intros s1 [Hv2_eq [Hv1_eq [Hfin_eq [HR1 [Hroot_id [Hscc_next Hother]]]]]].
    assert (Hnot_root' : ~ visited2 s1 root). { rewrite Hv2_eq; exact Hnot_root2. }
    assert (Hmax' : forall w, ~ visited2 s1 w -> finish s1 root >= finish s1 w). {
      intros w Hw. rewrite Hv2_eq in Hw. rewrite Hfin_eq. apply Hmax2; exact Hw. }
    assert (Hlt_root : forall v, visited2 s1 v -> scc_id s1 v < scc_id s1 root). {
      intros v Hv. rewrite Hv2_eq in Hv.
      destruct (classic (v = root)) as [Hv_eq | Hv_ne].
      - subst v. exfalso. apply Hnot_root2. exact Hv.
      - rewrite (Hother v Hv_ne). rewrite Hroot_id. pose proof (Hscclt v Hv). lia. }
    assert (Hroot_lt : scc_id s1 root < scc_next s1). {
      rewrite Hroot_id, Hscc_next. abstract lia. }
    eapply Hoare_bind.
    * apply (DFS_scc_R s1 root HR1 Hnot_root' Hmax' Hlt_root Hroot_lt).
    * intro junk2. apply Hoare_normalize. intros s2 HR2. apply IHW; exact HR2.
Qed.

Lemma kosaraju_scc_preserves_R : forall s0,
  R s0 -> Hoare (fun st => st = s0) kosaraju_scc (fun _ s' => R s').
Proof.
  intros s0 HR0.
  unfold kosaraju_scc.
  set (Q := fun (_:unit) (_:St) (_:unit) (s':St) => R s').
  apply Hoare_normal_LFix_closed with (R := R) (Q := Q).
  { intros W IH s0' u0 HR'.
    unfold Q; simpl. unfold kosaraju_scc_f.
    apply Hoare_choice.
    { apply Hoare_bind with (Q := fun (u:V) (s':St) =>
        s' = s0' /\ ~ visited2 s' u /\
        (forall w, ~ visited2 s' w -> finish s' u >= finish s' w)).
      { unfold Hoare, pick_unvisited2, get.
        intros s1 u s2 Hs1 Hprog. rewrite Hs1 in *.
        destruct Hprog as [[Hnot_vis Hmax2] Hsame].
        rewrite Hsame in *; repeat split; auto. }
      { intro root. apply Hoare_normalize.
        intros s1 [Hs1_eq [Hnot_root2 Hmax2]]; subst s1.
        apply (round_W_R s0' root W HR' Hnot_root2 Hmax2).
        intros s HRs. exact (IH s tt HRs). } }
    { apply Hoare_normal_assume_bind with
        (P := fun st => forall v, visited2 st v) (f := skip)
        (Q := fun (_:unit) (s':St) => R s') (s0 := s0').
      intros Hall. apply Hoare_ret'; intros s Hs; subst s; exact HR'. } }
  { exact HR0. }
Qed.

Lemma DFS_finish_preserves_visited2 : forall s0 u,
  Hoare (fun st => st = s0) (DFS_finish u) (fun _ s' => visited2 s' = visited2 s0).
Proof.
  intros s0 u. unfold DFS_finish.
  apply Hoare_normal_LFix with
    (Q := fun (u':V) (s0':St) (_:unit) (s':St) => visited2 s' = visited2 s0').
  intros W IH s0' u'. unfold DFS_finish_f.
  apply Hoare_bind with
    (Q := fun (_:unit) (s':St) => visited2 s' = visited2 s0').
  + intros s1 a s2 Hs1 Hprog. subst s1. sets_unfold in Hprog.
    unfold visit1 in Hprog. simpl in Hprog.
    destruct Hprog as [_ [_ [_ [Hv2 _]]]]. exact Hv2.
  + intro junk.
    apply Hoare_repeat_break with
      (P := fun _ st => visited2 st = visited2 s0')
      (Q := fun _ s' => visited2 s' = visited2 s0').
    intros e_set. apply Hoare_normalize. intros s Hinv.
    apply Hoare_choice.
    { apply Hoare_any_bind; intros e; apply Hoare_any_bind; intros v.
      apply Hoare_normal_assume_bind; intros _. apply Hoare_normal_assume_bind; intros _.
      apply Hoare_normal_assume_bind; intros _. eapply Hoare_bind.
      - exact (IH s v).
      - intro; apply Hoare_ret'. intros s' Hnext. etransitivity; eauto. }
    { apply Hoare_normal_assume_bind; intros Hall.
      unfold Hoare, bind, get, set_finish, break, ret.
      intros s1 a s2 Hs1 Hprog. rewrite Hs1 in *.
      destruct Hprog as [t [s' [[Ht Hs'] Hrest]]].
      destruct Hrest as [v [s'' [Hset [Hbrk_eq Hstate_eq]]]].
      rewrite Hbrk_eq. simpl. rewrite <- Hstate_eq.
      unfold set_finish in Hset; cbv beta in Hset.
      destruct Hset as [_ [_ [_ [_ [Hv2 _]]]]].
      rewrite Hv2. rewrite <- Hs'. exact Hinv. }
Qed.

Lemma kosaraju_finish_preserves_visited2 : forall s0,
  Hoare (fun st => st = s0) kosaraju_finish (fun _ s' => visited2 s' = visited2 s0).
Proof.
  intros s0. unfold kosaraju_finish.
  apply Hoare_normal_LFix with
    (Q := fun (_:unit) (s0':St) (_:unit) (s':St) => visited2 s' = visited2 s0').
  intros W IH s0' u. simpl.
  unfold kosaraju_finish_f.
  apply Hoare_choice.
  { apply Hoare_bind with (Q := fun (u0:V) (s':St) => s' = s0' /\ ~ visited1 s' u0).
    { unfold Hoare, pick_unvisited1, get.
      intros s1 u0 s2 Hs1 Hprog. rewrite Hs1 in *.
      destruct Hprog as [Hnot_vis Hsame]. rewrite Hsame in Hnot_vis. split; auto. }
    { intro u0. apply Hoare_normalize. intros s1 [Hs1_eq Hunvis]; subst s1.
      apply Hoare_bind with
        (Q := fun (_:unit) (s':St) => visited2 s' = visited2 s0').
      - apply (DFS_finish_preserves_visited2 s0' u0).
      - intro junk.
        apply Hoare_normalize. intros s3 Hv2_eq3.
        eapply Hoare_imp_post.
        { apply (IH s3 tt). }
        { simpl. intros _ s' Hv2'. rewrite Hv2'. exact Hv2_eq3. } } }
  { apply Hoare_assume_bind with (Q := fun st => forall v, visited1 st v).
    apply Hoare_ret'. intros s1 [Hall Hs]. subst s1. reflexivity. }
Qed.

Lemma kosaraju_finish_R : Hoare (fun st => st = init_st) kosaraju_finish (fun _ s' => R s').
Proof.
  unfold R.
  eapply Hoare_imp_post.
  - apply Hoare_conj.
    + apply kosaraju_finish_phase1_order.
    + apply Hoare_conj.
      * apply (kosaraju_finish_visited_all init_st).
      * apply kosaraju_finish_preserves_visited2.
  - simpl. intros _ s' [Hphase [Hvis1 Hv2_eq]].
    split; [| split; [| split; [| split]]].
    { intros u v Hvis _. rewrite Hv2_eq in Hvis. exfalso; exact Hvis. }
    { exact Hphase. }
    { exact Hvis1. }
    { intros v Hvis. rewrite Hv2_eq in Hvis. exfalso; exact Hvis. }
    { intros u v Hvis _. rewrite Hv2_eq in Hvis. exfalso; exact Hvis. }
Qed.

Lemma kosaraju_correct :
  Hoare (fun st => st = init_st) kosaraju
    (fun _ s' =>
       (forall v, visited2 s' v) /\
       (forall u v, scc_id s' u = scc_id s' v <-> mutually_reachable u v)).
Proof.
  unfold kosaraju.
  eapply Hoare_bind.
  - apply kosaraju_finish_R.
  - intro a. apply Hoare_normalize. intros s HR.
    eapply Hoare_imp_post.
    + apply Hoare_conj.
      * apply kosaraju_scc_all_visited.
      * apply (kosaraju_scc_preserves_R s HR).
    + simpl. intros _ s' [Hvisited2 HR'].
      destruct HR' as [_ [_ [_ [_ Hcorrect]]]].
      split; [exact Hvisited2 | exact (fun u v => Hcorrect u v (Hvisited2 u) (Hvisited2 v))].
Qed.

End Kosaraju.
