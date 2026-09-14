From CDCLLib Require Export sat_shared_lib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FinFun.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list.

(** * cdcl_shared_lib: representation-independent CDCL semantics.

    A [cdcl_view] is the solver state stripped of its C representation:
    a partial assignment plus, per variable, its decision level, its antecedent
    clause and its trail rank.  On top of it this file states the search
    invariants ([grounded_at], [closed_levels], [stable_view]), the pure
    transition relations the operation contracts use ([assigns_one],
    [restrict_above_level]), the learned-clause certificates, and the
    watched-literal frontier theory.  Still no separation logic and no C
    struct: every definition is a statement about lists, functions and [Z].

    Re-exports [CDCLLib.sat_shared_lib], so importing this file is enough.
    Importers:
      - the CDCL case library, and
      - the MiniSat model/library chain.
    Editing this file therefore rebuilds BOTH proof chains. *)

(* ==================== View and invariants ==================== *)
(* The solver state stripped of its C representation, plus the two search
   invariants every operation contract carries: grounded_at, saying every value
   has a justification, and closed_levels, saying the decision levels are dense
   up to the current one. *)

(* The pure solver state: a partial assignment and, per variable, its decision
   level, its antecedent clause and its rank on the trail, together with the
   installed clause database and the current decision level. *)
Record cdcl_view := {
  assignment : partial_valuation;
  level_of : Z -> option Z;
  reason_of : Z -> option clause;
  assignment_rank : Z -> option nat;
  installed_clauses : list clause;
  current_level : Z
}.

(* A recorded reason contains the literal satisfied by x.  Each literal on
   a different variable is false, has a level no greater than x's, and has a
   smaller trail rank.  Database membership is a separate client invariant;
   this predicate takes the clause value rather than its database index. *)
Definition reason_valid (a : cdcl_view) (x : Z) (c : clause) : Prop :=
  exists b d rx,
    assignment a x = Some b /\
    level_of a x = Some d /\
    assignment_rank a x = Some rx /\
    In (satisfying_literal x b) c /\
    (forall l,
       In l c -> literal_var l <> x ->
       eval_partial_literal (assignment a) l = Some false /\
       exists dy ry,
         level_of a (literal_var l) = Some dy /\
         assignment_rank a (literal_var l) = Some ry /\
         dy <= d /\ (ry < rx)%nat).

(* The recorded reason of x contains a false literal on a distinct variable
   y.  When that reason is valid, y also has a smaller trail rank than x. *)
Definition reason_dependency (a : cdcl_view) (x y : Z) : Prop :=
  exists c ly,
    reason_of a x = Some c /\
    In ly c /\ literal_var ly = y /\ y <> x /\
    eval_partial_literal (assignment a) ly = Some false.

(* Every assigned variable has a decision level and trail rank, and either
   no recorded reason or a valid reason clause.  The CDCL client adds positive
   decision levels and eager propagation in [grounded_at_cdcl]. *)
Definition grounded_at (a : cdcl_view) : Prop :=
  forall x b,
    assignment a x = Some b ->
    exists d rx,
      level_of a x = Some d /\
      assignment_rank a x = Some rx /\
      (reason_of a x = None \/
       (exists c,
          reason_of a x = Some c /\
          reason_valid a x c)).

(* x holds its value because of the decision made at level d: assigned, at
   level d, and with no antecedent clause. *)
Definition decision_at (a : cdcl_view) (x d : Z) : Prop :=
  (exists b, assignment a x = Some b) /\
  level_of a x = Some d /\ reason_of a x = None.

(* Assigned levels lie between zero and the current level, and every
   positive level up to the current one has a decision variable.  This shared
   predicate requires existence; the CDCL client adds uniqueness and excludes
   level-zero decisions in [closed_levels_cdcl]. *)
Definition closed_levels (a : cdcl_view) : Prop :=
  0 <= current_level a /\
  (forall x b d,
     assignment a x = Some b -> level_of a x = Some d ->
     0 <= d <= current_level a) /\
  (forall d, 0 < d <= current_level a -> exists x, decision_at a x d).

(* The assignment left after backjumping to level k: values assigned at a
   level at most k survive, the rest become unassigned. *)
Definition restrict_to_level
    (a : cdcl_view) (k : Z) : partial_valuation :=
  fun x =>
    match assignment a x, level_of a x with
    | Some b, Some d => if d <=? k then Some b else None
    | _, _ => None
    end.

(* ==================== Stability and certificates ==================== *)
(* The invariant bundle the operation contracts pass around, what a learned
   clause has to satisfy for conflict analysis to be sound, and the properties
   of the clause database that propagation and learning preserve. *)

(* Both search invariants at once: the form the contracts carry. *)
Definition stable_view (a : cdcl_view) : Prop :=
  grounded_at a /\ closed_levels a.

(* A sound learned clause: entailed by the original formula, and false under
   the current assignment, so it really explains the conflict. *)
Definition learned_clause_sound
    (F : cnf) (a : cdcl_view) (L : clause) : Prop :=
  entails_clause F L /\ clause_false (assignment a) L.

(** A first-UIP exit certificate is representation-independent: the
    learnt clause is entailed, has pairwise-distinct variables, and has one
    current-level head with every remaining literal strictly below it. *)
Definition uip_exit_cert
    (F : cnf) (a : cdcl_view) (L : clause) : Prop :=
  learned_clause_sound F a L /\
  NoDup (map literal_var L) /\
  exists l rest,
    L = l :: rest /\
    level_of a (literal_var l) = Some (current_level a) /\
    Forall (fun k =>
      exists dk,
        level_of a (literal_var k) = Some dk /\
        dk < current_level a) rest.

(* After backjumping to level target, L has no true literal and exactly one
   unassigned one, so it immediately forces that literal. *)
Definition clause_asserting_after
    (a : cdcl_view) (target : Z) (L : clause) : Prop :=
  clause_true_count (restrict_to_level a target) L = 0 /\
  clause_unassigned_count (restrict_to_level a target) L = 1.

(* No installed clause is false under the current assignment. *)
Definition no_conflict (a : cdcl_view) : Prop :=
  forall c, In c (installed_clauses a) ->
    ~ clause_false (assignment a) c.

(* No installed clause is unit: propagation has reached its fixed point. *)
Definition no_unit (a : cdcl_view) : Prop :=
  forall c, In c (installed_clauses a) ->
    ~ clause_unit (assignment a) c.

(* Some installed clause is false: the conflict analysis starts from this. *)
Definition database_conflict (a : cdcl_view) : Prop :=
  exists c,
    In c (installed_clauses a) /\
    clause_false (assignment a) c.

(* Every antecedent clause recorded in the view is entailed by the original
   formula, which is what makes a resolution over antecedents sound. *)
Definition reasons_entailed (F : cnf) (a : cdcl_view) : Prop :=
  forall x c, reason_of a x = Some c -> entails_clause F c.

(* Every installed clause is entailed by the original formula: soundness of
   the database once learned clauses have been added to it. *)
Definition db_entailed (F : cnf) (a : cdcl_view) : Prop :=
  forall c, In c (installed_clauses a) -> entails_clause F c.

(* No antecedent clause mentions a variable twice, so the counting lemmas of
   sat_shared_lib.v apply to it. *)
Definition reasons_var_injective (a : cdcl_view) : Prop :=
  forall x c, reason_of a x = Some c -> clause_var_injective c.

(** A single assignment transition adds x |-> b at level d with the given
    reason, preserves every other variable's fields and the clause database,
    and gives x a rank above its reason dependencies.  The current search
    level is left to the client contract. *)
Definition assigns_one
    (old new : cdcl_view) (x : Z) (b : bool)
    (d : Z) (reason : option clause) : Prop :=
  assignment old x = None /\
  assignment new x = Some b /\
  level_of new x = Some d /\
  reason_of new x = reason /\
  (exists rx,
     assignment_rank new x = Some rx /\
     forall y,
       reason_dependency new x y ->
       exists ry,
         assignment_rank new y = Some ry /\ (ry < rx)%nat) /\
  (forall y, y <> x ->
     assignment new y = assignment old y /\
     level_of new y = level_of old y /\
     reason_of new y = reason_of old y /\
     assignment_rank new y = assignment_rank old y) /\
  installed_clauses new = installed_clauses old.

(** [new] is [old] restricted to decision level [target].
    Original: new is old restricted to dl target *)
Definition restrict_above_level
    (old new : cdcl_view) (target : Z) : Prop :=
  current_level new = target /\
  installed_clauses new = installed_clauses old /\
  forall x,
    match level_of old x with
    | Some d =>
        if d <=? target
        then assignment new x = assignment old x /\
             level_of new x = level_of old x /\
             reason_of new x = reason_of old x /\
             assignment_rank new x = assignment_rank old x
        else assignment new x = None /\
             level_of new x = None /\
             reason_of new x = None /\
             assignment_rank new x = None
    | None => assignment new x = None /\
              level_of new x = None /\
              reason_of new x = None /\
              assignment_rank new x = None
    end.

(* ==================== Transitions ==================== *)
(* The two pure state changes the C operations are proved to realise: adding
   one assignment, and cutting the view back to a decision level.  The lemma
   closing the group bounds how deep the search can go. *)

(* With every assigned variable in range and the levels closed, the current
   decision level is at most n: the search cannot go deeper than the number of
   variables it has. *)
Lemma stable_search_level_bound :
  forall n a,
    0 <= n ->
    (forall x b, assignment a x = Some b -> var_in_range n x) ->
    closed_levels a ->
    current_level a <= n.
Proof.
  intros n a Hn0 Hrange Hclosed.
  unfold closed_levels in Hclosed.
  destruct Hclosed as [Hdl0 [_ Hdecisions]].
  apply Z.nlt_ge.
  intro Hnlt.
  set (levels := map Z.of_nat (seq 1 (Z.to_nat (current_level a)))).
  set (variables := map Z.of_nat (seq 0 (Z.to_nat n))).
  assert (Hlevels_nodup : NoDup levels).
  { unfold levels.
    apply Injective_map_NoDup.
    - intros u v Huv. now apply Nat2Z.inj.
    - apply seq_NoDup. }
  assert (Hlevels_decide :
    Forall
      (fun d => Exists (fun x => decision_at a x d) variables)
      levels).
  { unfold levels.
    apply Forall_forall.
    intros d Hd.
    apply in_map_iff in Hd as [k [<- Hk]].
    apply in_seq in Hk.
    assert (Hd_range : 0 < Z.of_nat k <= current_level a).
    { destruct Hk as [Hk1 Hk2].
      rewrite <- (Z2Nat.id (current_level a)) by lia.
      split; lia. }
    destruct (Hdecisions (Z.of_nat k) Hd_range) as [x Hdecision].
    pose proof Hdecision as Hdecision'.
    unfold decision_at in Hdecision'.
    destruct Hdecision' as [[b Hb] _].
    pose proof (Hrange x b Hb) as Hxrange.
    unfold var_in_range in Hxrange.
    destruct Hxrange as [Hx0 Hxn].
    apply Exists_exists.
    exists x.
    split.
    - unfold variables.
      apply in_map_iff.
      exists (Z.to_nat x).
      split.
      + apply Z2Nat.id. exact Hx0.
      + apply in_seq.
        split; [lia|].
        apply Z2Nat.inj_lt; lia.
    - exact Hdecision. }
  assert (Hlength : (List.length variables < List.length levels)%nat).
  { unfold variables, levels.
    rewrite !length_map, !length_seq.
    apply Z2Nat.inj_lt; lia. }
  destruct (Permutation_pigeonhole_rel
    (fun d x => decision_at a x d) Hlevels_decide Hlength)
    as [d [d' [rest [Hperm [x [_ [Hdecision Hdecision']]]]]]].
  pose proof (Permutation_NoDup Hperm Hlevels_nodup) as Hnodup.
  assert (Hdd' : d <> d').
  { inversion Hnodup as [|d0 tail Hnotin Htail]; subst.
    intro Heq. subst d'.
    apply Hnotin. left. reflexivity. }
  unfold decision_at in Hdecision, Hdecision'.
  destruct Hdecision as [_ [Hlevel _]].
  destruct Hdecision' as [_ [Hlevel' _]].
  congruence.
Qed.

(* ==================== Watch frontier ==================== *)
(* An occurrence records two watched literals of a clause; the frontier
   excludes processing both watches as false.  The final theorem connects
   this invariant to clause satisfaction under a total assignment. *)

(* One clause as the watch lists see it: an owner tag chosen by the
   representation, the clause body, and its two watched literals. *)
Record watch_occurrence (Owner : Type) := {
  watch_owner : Owner;
  watch_body : clause;
  watch_left : literal;
  watch_right : literal
}.

Arguments watch_owner {Owner} _.
Arguments watch_body {Owner} _.
Arguments watch_left {Owner} _.
Arguments watch_right {Owner} _.

(* Both watched literals really occur in the clause body. *)
Definition watch_occurrence_members {Owner : Type}
    (o : watch_occurrence Owner) : Prop :=
  In (watch_left o) (watch_body o) /\
  In (watch_right o) (watch_body o).

(* A well formed occurrence: every body literal in range, and both watches
   inside the body. *)
Definition watch_occurrence_wf {Owner : Type}
    (n : Z) (o : watch_occurrence Owner) : Prop :=
  Forall (literal_wf n) (watch_body o) /\
  watch_occurrence_members o.

(* No occurrence has both of its watched literals marked false: P is asked
   about the negation of a watch, so P (literal_neg w) says w is false.  This
   is the invariant the watch lists maintain between propagation steps. *)
Definition watch_frontier
    {Owner : Type} (occs : list (watch_occurrence Owner))
    (P : literal -> Prop) : Prop :=
  Forall (fun o =>
    ~(P (literal_neg (watch_left o)) /\
      P (literal_neg (watch_right o)))) occs.

(* The frontier while one literal is being processed: an occurrence may be
   violated only through the literal in focus. *)
Definition watch_frontier_except
    {Owner : Type} (occs : list (watch_occurrence Owner))
    (P : literal -> Prop) (focus : literal) : Prop :=
  Forall (fun o =>
    ~(P (literal_neg (watch_left o)) /\
      P (literal_neg (watch_right o))) \/
    focus = literal_neg (watch_left o) \/
    focus = literal_neg (watch_right o)) occs.

(* Shrinking the falsified set keeps the frontier. *)
Lemma watch_frontier_shrink :
  forall (Owner : Type)
         (occs : list (watch_occurrence Owner))
         (Pold Pnew : literal -> Prop),
    watch_frontier occs Pold ->
    (forall l, Pnew l -> Pold l) ->
    watch_frontier occs Pnew.
Proof.
  intros Owner occs Pold Pnew Hfrontier Hsub.
  unfold watch_frontier in *.
  rewrite Forall_forall in Hfrontier |- *.
  intros o Hin [Hleft Hright].
  apply (Hfrontier o Hin). split; apply Hsub; assumption.
Qed.

(* Any sub-collection of a frontier is a frontier, so a watch list may be
   split without losing the invariant. *)
Lemma watch_frontier_thin :
  forall (Owner : Type)
         (occs kept : list (watch_occurrence Owner))
         (P : literal -> Prop),
    incl kept occs ->
    watch_frontier occs P ->
    watch_frontier kept P.
Proof.
  intros Owner occs kept P Hincl Hfrontier.
  unfold watch_frontier in *.
  rewrite Forall_forall in Hfrontier |- *.
  intros o Hin. apply Hfrontier. apply Hincl. exact Hin.
Qed.

(* P holds of the negation of every in-range literal that rho makes false:
   the processing of falsified literals has caught up with rho. *)
Definition processed_false_complete
    (n : Z) (rho : valuation) (P : literal -> Prop) : Prop :=
  forall l,
    literal_wf n l ->
    eval_literal rho l = false ->
    P (literal_neg l).

(* Adding the focus literal to the falsified set turns a frontier into a
   frontier except focus: the step that begins processing a literal. *)
Lemma watch_frontier_open :
  forall (Owner : Type)
         (occs : list (watch_occurrence Owner))
         (Pold Pnew : literal -> Prop) focus,
    watch_frontier occs Pold ->
    (forall l, Pnew l <-> Pold l \/ l = focus) ->
    watch_frontier_except occs Pnew focus.
Proof.
  intros Owner occs Pold Pnew focus Hold Hstep.
  unfold watch_frontier in Hold.
  unfold watch_frontier_except.
  rewrite Forall_forall in Hold |- *.
  intros o Hin.
  specialize (Hold o Hin).
  destruct (literal_eq_dec focus (literal_neg (watch_left o)))
    as [Hleft|Hleft].
  - right. left. exact Hleft.
  - destruct (literal_eq_dec focus (literal_neg (watch_right o)))
      as [Hright|Hright].
    + right. right. exact Hright.
    + left. intros [HPleft HPright]. apply Hold. split.
      * apply (proj1 (Hstep _)) in HPleft.
        destruct HPleft as [HPleft|Heq]; [exact HPleft|].
        exfalso. apply Hleft. symmetry. exact Heq.
      * apply (proj1 (Hstep _)) in HPright.
        destruct HPright as [HPright|Heq]; [exact HPright|].
        exfalso. apply Hright. symmetry. exact Heq.
Qed.

(* Checking just the occurrences that mention focus closes the frontier
   again: the step that ends processing a literal. *)
Lemma watch_frontier_close :
  forall (Owner : Type)
         (occs : list (watch_occurrence Owner))
         (P : literal -> Prop) focus,
    watch_frontier_except occs P focus ->
    (forall o, In o occs ->
      (focus = literal_neg (watch_left o) \/
       focus = literal_neg (watch_right o)) ->
      ~(P (literal_neg (watch_left o)) /\
        P (literal_neg (watch_right o)))) ->
    watch_frontier occs P.
Proof.
  intros Owner occs P focus Hfrontier Hfocused.
  unfold watch_frontier_except in Hfrontier.
  unfold watch_frontier.
  rewrite Forall_forall in Hfrontier |- *.
  intros o Hin.
  specialize (Hfrontier o Hin).
  destruct Hfrontier as [Hsafe|Hfocus].
  - exact Hsafe.
  - apply Hfocused; assumption.
Qed.

(* Undoing focus recovers the plain frontier for the smaller falsified set,
   which is what backtracking past a propagation needs. *)
Lemma watch_frontier_rollback :
  forall (Owner : Type)
         (occs : list (watch_occurrence Owner))
         (Pold Pnew : literal -> Prop) focus,
    watch_frontier_except occs Pnew focus ->
    (forall l, Pold l -> Pnew l) ->
    ~ Pold focus ->
    watch_frontier occs Pold.
Proof.
  intros Owner occs Pold Pnew focus Hfrontier Hincl Hfresh.
  unfold watch_frontier_except in Hfrontier.
  unfold watch_frontier.
  rewrite Forall_forall in Hfrontier |- *.
  intros o Hin.
  specialize (Hfrontier o Hin).
  destruct Hfrontier as [Hsafe|[Hleft|Hright]].
  - intros [HPleft HPright]. apply Hsafe. split;
      apply Hincl; assumption.
  - intros [HPleft _]. apply Hfresh.
    rewrite Hleft. exact HPleft.
  - intros [_ HPright]. apply Hfresh.
    rewrite Hright. exact HPright.
Qed.

(* Under a total assignment, well formed watches, the frontier, and complete
   processing of false literals imply that every watched clause is satisfied. *)
Theorem watch_frontier_total_satisfies :
  forall (Owner : Type) n
         (occs : list (watch_occurrence Owner))
         (rho : valuation) (P : literal -> Prop),
    Forall (watch_occurrence_wf n) occs ->
    watch_frontier occs P ->
    processed_false_complete n rho P ->
    Forall (fun o => clause_satisfied rho (watch_body o)) occs.
Proof.
  intros Owner n occs rho P Hwf Hfrontier Hcomplete.
  unfold watch_frontier in Hfrontier.
  unfold processed_false_complete in Hcomplete.
  rewrite Forall_forall in Hwf, Hfrontier |- *.
  intros o Hin.
  specialize (Hwf o Hin).
  specialize (Hfrontier o Hin).
  destruct Hwf as [Hbody_wf [Hleft_in Hright_in]].
  rewrite Forall_forall in Hbody_wf.
  pose proof (Hbody_wf _ Hleft_in) as Hleft_wf.
  pose proof (Hbody_wf _ Hright_in) as Hright_wf.
  destruct (eval_literal rho (watch_left o)) eqn:Hleft.
  - exists (watch_left o). split; assumption.
  - destruct (eval_literal rho (watch_right o)) eqn:Hright.
    + exists (watch_right o). split; assumption.
    + exfalso. apply Hfrontier. split;
        apply Hcomplete; assumption.
Qed.
