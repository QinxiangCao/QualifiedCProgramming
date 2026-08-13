Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.FinFun.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.StrategyLib Require Import Mapping.

Import ListNotations.
Import naive_C_Rules.
Local Open Scope string.
Local Open Scope Z_scope.
Local Open Scope list.
Local Open Scope sac.
Local Set Warnings "-simpl-unfolding-modifiers".

(** The direct, proof-readable SAT layer. *)

Inductive literal : Type :=
| Pos (x : Z)
| Neg (x : Z).

Definition clause := list literal.
Definition cnf := list clause.
Definition valuation := total_mapping bool.
Definition Assignment := valuation.
Definition partial_valuation := partial_mapping bool.

Definition var_in_range (n x : Z) : Prop := 0 <= x < n.

Definition literal_var (l : literal) : Z :=
  match l with Pos x | Neg x => x end.

Definition literal_wf (n : Z) (l : literal) : Prop :=
  var_in_range n (literal_var l).

Definition cnf_wf (n : Z) (f : cnf) : Prop :=
  0 <= n /\ Forall (fun c => Forall (literal_wf n) c) f.

Definition bounded_valuation (n : Z) (rho : valuation) : Prop :=
  forall x, ~ var_in_range n x -> rho x = false.

Definition rho_of_values (n : Z) (values : list Z) : valuation :=
  fun x =>
    if andb (0 <=? x) (x <? n)
    then Z.eqb (Znth x values (-1)) 1
    else false.

Definition eval_literal (rho : valuation) (l : literal) : bool :=
  match l with
  | Pos x => rho x
  | Neg x => negb (rho x)
  end.

Definition eval_partial_literal
    (sigma : partial_valuation) (l : literal) : option bool :=
  match sigma (literal_var l) with
  | None => None
  | Some b =>
      Some (match l with Pos _ => b | Neg _ => negb b end)
  end.

Definition clause_satisfied (rho : valuation) (c : clause) : Prop :=
  exists l, In l c /\ eval_literal rho l = true.

Definition models (rho : valuation) (f : cnf) : Prop :=
  Forall (clause_satisfied rho) f.

Definition cnf_sat (n : Z) (F : cnf) : Prop :=
  cnf_wf n F /\
  exists J : Assignment, bounded_valuation n J /\ models J F.

Definition entails_clause (f : cnf) (c : clause) : Prop :=
  forall rho, models rho f -> clause_satisfied rho c.

Definition cnf_unsat (n : Z) (f : cnf) : Prop :=
  cnf_wf n f /\
  forall rho, bounded_valuation n rho -> ~ models rho f.

Definition row_wf (n : Z) (row : list Z) : Prop :=
  Zlength row = n /\
  Forall (fun z => z = -1 \/ z = 0 \/ z = 1) row.

Fixpoint dense_decode_from (x : Z) (row : list Z) : clause :=
  match row with
  | [] => []
  | z :: row' =>
      let decoded := dense_decode_from (x + 1) row' in
      if z =? 1 then Pos x :: decoded
      else if z =? -1 then Neg x :: decoded
      else decoded
  end.

Definition dense_decode (row : list Z) : clause :=
  dense_decode_from 0 row.

Definition original_prefix_exact
    (f : cnf) (original_count : Z) (installed : list clause) : Prop :=
  firstn (Z.to_nat original_count) installed = f /\
  Z.of_nat (List.length f) = original_count /\
  Forall (fun c => c <> []) f.

(** Exact summaries used as semantic state by the implementation. *)

Fixpoint clause_true_count
    (sigma : partial_valuation) (c : clause) : Z :=
  match c with
  | [] => 0
  | l :: c' =>
      match eval_partial_literal sigma l with
      | Some true => 1 + clause_true_count sigma c'
      | _ => clause_true_count sigma c'
      end
  end.

Fixpoint clause_unassigned_count
    (sigma : partial_valuation) (c : clause) : Z :=
  match c with
  | [] => 0
  | l :: c' =>
      match eval_partial_literal sigma l with
      | None => 1 + clause_unassigned_count sigma c'
      | _ => clause_unassigned_count sigma c'
      end
  end.

Definition expected_clause_state
    (sigma : partial_valuation) (c : clause) : Z :=
  let t := clause_true_count sigma c in
  let u := clause_unassigned_count sigma c in
  if 0 <? t then 0
  else if u =? 0 then 1
  else if u =? 1 then 2
  else -u.

Definition clause_summary_ok
    (sigma : partial_valuation) (c : clause)
    (state lit_state unassign_num : Z) : Prop :=
  lit_state = clause_true_count sigma c /\
  unassign_num = clause_unassigned_count sigma c /\
  state = expected_clause_state sigma c.

Definition clause_false
    (sigma : partial_valuation) (c : clause) : Prop :=
  forall l, In l c -> eval_partial_literal sigma l = Some false.

Definition clause_unit
    (sigma : partial_valuation) (c : clause) : Prop :=
  clause_true_count sigma c = 0 /\
  clause_unassigned_count sigma c = 1.

Fixpoint literal_var_count (x : Z) (c : clause) : Z :=
  match c with
  | [] => 0
  | l :: c' =>
      if literal_var l =? x
      then 1 + literal_var_count x c'
      else literal_var_count x c'
  end.

Fixpoint literal_true_at_count (x : Z) (b : bool) (c : clause) : Z :=
  match c with
  | [] => 0
  | l :: c' =>
      if literal_var l =? x
      then if eval_literal (fun _ => b) l
           then 1 + literal_true_at_count x b c'
           else literal_true_at_count x b c'
      else literal_true_at_count x b c'
  end.

Definition clear_partial
    (sigma : partial_valuation) (x : Z) : partial_valuation :=
  total_mapping_update sigma x None.

(** Semantic view of the current CDCL state. *)

Record cdcl_view := {
  assignment : partial_valuation;
  level_of : Z -> option Z;
  reason_of : Z -> option Z;
  assignment_rank : Z -> option nat;
  installed_clauses : list clause;
  current_level : Z
}.

Definition installed_clauses_sound
    (F : cnf) (original_count : Z)
    (installed : list clause) : Prop :=
  original_prefix_exact F original_count installed /\
  Forall (fun c => entails_clause F c)
    (skipn (Z.to_nat original_count) installed).

Definition satisfying_literal (x : Z) (b : bool) : literal :=
  if b then Pos x else Neg x.

Definition falsified_literal (x : Z) (b : bool) : literal :=
  if b then Neg x else Pos x.

(* Clause [i] of [installed_clauses] is what forced variable [x] to the value
   it has in [a].  Every *other* literal of that clause sits at a decision
   level <= x's, those at exactly x's level were assigned before x, and all of
   them are false under the earlier assignments -- so x's value is forced.
   Equivalently: after some transition at x's own decision level, clause [i]
   became a unit clause available for unit propagation.

   Original: installed_clauses中的第i个子句确定了变量x的取值为它在a中的取值，因为
   这一个子句中所有其他的literal的dl都低于或等于x的dl，而dl与x相等的literal在x之前
   先被确定取值，并且所有其他的literal全部因为前面的赋值而为false，因此x的取值被确定
   /在x的dl这一层级的某一次变换后，第i个子句成为可unit propagation的unit子句 *)
Definition reason_valid (a : cdcl_view) (x i : Z) : Prop :=
  exists b d rx c,
    assignment a x = Some b /\
    level_of a x = Some d /\
    assignment_rank a x = Some rx /\
    nth_error (installed_clauses a) (Z.to_nat i) = Some c /\
    In (satisfying_literal x b) c /\
    (forall l,
       In l c -> literal_var l <> x ->
       eval_partial_literal (assignment a) l = Some false /\
       exists dy ry,
         level_of a (literal_var l) = Some dy /\
         assignment_rank a (literal_var l) = Some ry /\
         dy <= d /\ (ry < rx)%nat).

(* The value currently forced for [x] depends on [y], whose value was
   determined or decided before x's.
   Original: 当前x确定的值依赖于y的赋值在x之前被确定或分配的值 *)
Definition reason_dependency (a : cdcl_view) (x y : Z) : Prop :=
  exists i c ly,
    reason_of a x = Some i /\
    nth_error (installed_clauses a) (Z.to_nat i) = Some c /\
    In ly c /\ literal_var ly = y /\ y <> x /\
    eval_partial_literal (assignment a) ly = Some false.

Definition same_level_predecessor
    (a : cdcl_view) (x y d : Z) : Prop :=
  reason_dependency a x y /\
  level_of a x = Some d /\
  level_of a y = Some d /\
  exists rx ry,
    assignment_rank a x = Some rx /\
    assignment_rank a y = Some ry /\ (ry < rx)%nat.

(* Every assigned value in [a] is either the decision made at some decision
   level, or was forced because earlier assignments turned another clause into
   a unit clause -- or was forced by an originally-unit clause.
   Original: a中所有已赋值的值，要么是某一个dl的decision值，要么是因为前面的赋值而
   导致其他子句成为unit被确定，或者原始unit子句确定 *)
Definition grounded_at (a : cdcl_view) : Prop :=
  forall x b,
    assignment a x = Some b ->
    exists d rx,
      level_of a x = Some d /\
      assignment_rank a x = Some rx /\
      ((reason_of a x = None /\ 0 < d) \/
       (exists i,
          reason_of a x = Some i /\
          reason_valid a x i /\
          (d = 0 \/ exists y, same_level_predecessor a x y d))).

Definition decision_at (a : cdcl_view) (x d : Z) : Prop :=
  (exists b, assignment a x = Some b) /\
  level_of a x = Some d /\ reason_of a x = None.

  (* No variable is assigned at a decision level above the view's own level,
     and for every level from 1 up to the view's current level there is
     exactly one variable that holds its value because of the decision made
     at that level.
     Original: 所有变量赋值的dl不会超过整个view的dl，并且从1到当前view的dl每一个dl
     恰好有一个变量是因为在这一层dl的decision被赋值为当前的值 *)
Definition closed_levels (a : cdcl_view) : Prop :=
  0 <= current_level a /\
  (forall x b d,
     assignment a x = Some b -> level_of a x = Some d ->
     0 <= d <= current_level a) /\
  (forall x, ~ decision_at a x 0) /\
  (forall d, 0 < d <= current_level a -> exists! x, decision_at a x d).

Definition restrict_to_level
    (a : cdcl_view) (k : Z) : partial_valuation :=
  fun x =>
    match assignment a x, level_of a x with
    | Some b, Some d => if d <=? k then Some b else None
    | _, _ => None
    end.

Definition active_frontier_clause
    (sigma : partial_valuation) (c : clause) : Prop :=
  clause_true_count sigma c = 0 /\
  clause_unassigned_count sigma c <= 1.

Definition literal_false_at_level
    (a : cdcl_view) (k : Z) (l : literal) : Prop :=
  eval_partial_literal (restrict_to_level a k) l = Some false /\
  level_of a (literal_var l) = Some k.

Definition no_active_clause_at (a : cdcl_view) (k : Z) : Prop :=
  forall c, In c (installed_clauses a) ->
    ~ active_frontier_clause (restrict_to_level a k) c.

Definition current_frontier_supported (a : cdcl_view) : Prop :=
  current_level a = 0 \/
  forall c,
    In c (installed_clauses a) ->
    active_frontier_clause (restrict_to_level a (current_level a)) c ->
    exists l, In l c /\ literal_false_at_level a (current_level a) l.

Definition frontier_closed (a : cdcl_view) : Prop :=
  (forall k, 0 <= k < current_level a -> no_active_clause_at a k) /\
  current_frontier_supported a.

(** The concrete lists from which the current implementation's view is derived. *)

Record dense_snapshot := {
  snap_values : list Z;
  snap_reasons : list Z;
  snap_levels : list Z;
  snap_rows : list (list Z);
  snap_states : list Z;
  snap_true_counts : list Z;
  snap_unassigned : list Z
}.

Definition decode_value_cell (z : Z) : option bool :=
  if z =? -1 then None
  else if z =? 0 then Some false
  else if z =? 1 then Some true
  else None.

Definition snapshot_assignment
    (n : Z) (snap : dense_snapshot) : partial_valuation :=
  fun x =>
    if andb (0 <=? x) (x <? n)
    then decode_value_cell (Znth x (snap_values snap) (-1))
    else None.

Definition snapshot_level
    (n : Z) (snap : dense_snapshot) : Z -> option Z :=
  fun x =>
    match snapshot_assignment n snap x with
    | None => None
    | Some _ => Some (Znth x (snap_levels snap) (-1))
    end.

Definition snapshot_reason
    (n : Z) (snap : dense_snapshot) : Z -> option Z :=
  fun x =>
    match snapshot_assignment n snap x with
    | None => None
    | Some _ =>
        let r := Znth x (snap_reasons snap) (-1) in
        if r =? -1 then None else Some r
    end.

Definition cdcl_view_of_snapshot
    (n : Z) (snap : dense_snapshot)
    (ranks : Z -> option nat) (logical_dl : Z) : cdcl_view :=
  {| assignment := snapshot_assignment n snap;
     level_of := snapshot_level n snap;
     reason_of := snapshot_reason n snap;
     assignment_rank := ranks;
     installed_clauses := map dense_decode (snap_rows snap);
     current_level := logical_dl |}.

Definition snapshot_lengths
    (n live : Z) (snap : dense_snapshot) : Prop :=
  Zlength (snap_values snap) = n /\
  Zlength (snap_reasons snap) = n /\
  Zlength (snap_levels snap) = n /\
  Zlength (snap_rows snap) = live /\
  Zlength (snap_states snap) = live /\
  Zlength (snap_true_counts snap) = live /\
  Zlength (snap_unassigned snap) = live.

Definition snapshot_cells_wf
    (n live : Z) (snap : dense_snapshot) : Prop :=
  (forall x,
     var_in_range n x ->
     let v := Znth x (snap_values snap) (-1) in
     let d := Znth x (snap_levels snap) (-1) in
     let r := Znth x (snap_reasons snap) (-1) in
     (v = -1 \/ v = 0 \/ v = 1) /\
     (v = -1 -> d = -1 /\ r = -1) /\
     (v <> -1 -> 0 <= d /\ (r = -1 \/ 0 <= r < live))) /\
  Forall (row_wf n) (snap_rows snap).

Definition summary_at
    (sigma : partial_valuation)
    (rows : list clause) (states true_counts unassigned : list Z)
    (i : Z) : Prop :=
  clause_summary_ok sigma
    (Znth i rows [])
    (Znth i states 0)
    (Znth i true_counts 0)
    (Znth i unassigned 0).

Definition snapshot_summaries_exact
    (n live : Z) (snap : dense_snapshot) : Prop :=
  forall i, 0 <= i < live ->
    summary_at (snapshot_assignment n snap)
      (map dense_decode (snap_rows snap))
      (snap_states snap) (snap_true_counts snap) (snap_unassigned snap) i.

Definition coherent_snapshot
    (F : cnf) (n live original_count : Z)
    (snap : dense_snapshot) : Prop :=
  0 <= n /\ 0 <= original_count <= live /\
  snapshot_lengths n live snap /\
  snapshot_cells_wf n live snap /\
  snapshot_summaries_exact n live snap /\
  installed_clauses_sound F original_count
    (map dense_decode (snap_rows snap)).

(** Learning and backjump interfaces. *)

Definition current_level_literal (a : cdcl_view) (l : literal) : Prop :=
  level_of a (literal_var l) = Some (current_level a).

Definition current_level_support (a : cdcl_view) (L : clause) : Prop :=
  exists l, In l L /\ current_level_literal a l.

Definition no_current_level_propagated_literal
    (a : cdcl_view) (L : clause) : Prop :=
  forall l, In l L -> current_level_literal a l ->
    reason_of a (literal_var l) = None.

Definition learned_clause_sound
    (F : cnf) (a : cdcl_view) (L : clause) : Prop :=
  entails_clause F L /\ clause_false (assignment a) L.

Definition current_learning_exit_cert
    (F : cnf) (a : cdcl_view) (L : clause) : Prop :=
  learned_clause_sound F a L /\
  (L = [] \/
   current_level_support a L /\
   no_current_level_propagated_literal a L).

Definition clause_asserting_after
    (a : cdcl_view) (target : Z) (L : clause) : Prop :=
  clause_true_count (restrict_to_level a target) L = 0 /\
  clause_unassigned_count (restrict_to_level a target) L = 1.

Definition learned_frontier_safe_after
    (a : cdcl_view) (target : Z) (L : clause) : Prop :=
  (forall k, 0 <= k < target ->
     ~ active_frontier_clause (restrict_to_level a k) L) /\
  (target = 0 \/
   exists l, In l L /\ literal_false_at_level a target l).

Definition learned_backjump_cert
    (F : cnf) (a : cdcl_view) (target : Z) (L : clause) : Prop :=
  learned_clause_sound F a L /\
  L <> [] /\
  0 <= target < current_level a /\
  clause_asserting_after a target L /\
  learned_frontier_safe_after a target L.

Definition clause_level_occurs
    (a : cdcl_view) (L : clause) (d : Z) : Prop :=
  exists l, In l L /\ level_of a (literal_var l) = Some d.

Definition clause_vars_assigned (a : cdcl_view) (L : clause) : Prop :=
  forall l, In l L ->
    exists b d,
      assignment a (literal_var l) = Some b /\
      level_of a (literal_var l) = Some d /\ 0 <= d.

(** The exact level profile computed by the current two-maximum scan.  The
    first disjunct is the implementation's special [0] result when the learned
    clause has no level below the current one; the second says [target] is the
    greatest level strictly below the current level. *)
Definition backjump_target_profile
    (a : cdcl_view) (target : Z) (L : clause) : Prop :=
  clause_vars_assigned a L /\
  current_level_support a L /\
  (forall d, clause_level_occurs a L d -> d <= current_level a) /\
  ((target = 0 /\
    forall d, clause_level_occurs a L d -> d = current_level a) \/
   (0 <= target < current_level a /\
    clause_level_occurs a L target /\
    forall d,
      clause_level_occurs a L d -> d < current_level a -> d <= target)).

(** Pure transition relations used by the operation contracts. *)

(* [new] is [old] with exactly one variable assignment added -- x |-> b at
   decision level d, with antecedent [reason] -- and everything else unchanged.
   Original: new是old增加 x->b, dl=d, antecedent = reason一个变量赋值,其他不变的view *)
Definition assigns_one
    (old new : cdcl_view) (x : Z) (b : bool)
    (d reason : Z) : Prop :=
  assignment old x = None /\
  assignment new x = Some b /\
  level_of new x = Some d /\
  reason_of new x = (if reason =? -1 then None else Some reason) /\
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

(* Assigning last := b at the current level, without changing the clause database, is the common immediate cause of
  every conflict present after this propagation step -- no immediate conflict in old
  every conflict in new is immediately caused by this assignment *)
Definition dense_conflict_batch
    (old new : cdcl_view) (last : Z) : Prop :=
  exists b,
    assignment old last = None /\
    assignment new last = Some b /\
    level_of new last = Some (current_level new) /\
    installed_clauses new = installed_clauses old /\
    (forall c,
      In c (installed_clauses new) ->
      clause_false (assignment new) c ->
      In (falsified_literal last b) c).

(* new is old restricted to dl target*)
Definition restrict_above_level
    (old new : cdcl_view) (target : Z) : Prop :=
  current_level new = target /\
  installed_clauses new = installed_clauses old /\
  (forall x,
     match level_of old x with
     | Some d =>
         if d <=? target
         then assignment new x = assignment old x /\
              level_of new x = level_of old x /\
              reason_of new x = reason_of old x /\
              assignment_rank new x = assignment_rank old x
         else assignment new x = None /\
              level_of new x = None /\ reason_of new x = None /\
              assignment_rank new x = None
     | None => assignment new x = None /\
               level_of new x = None /\
               reason_of new x = None /\
               assignment_rank new x = None
     end).


(* The backjump from old to new by going back to dl target clears all conflicts*)
Definition backjump_clears
    (old new : cdcl_view) (target : Z) : Prop :=
  restrict_above_level old new target /\
  (forall c, In c (installed_clauses old) ->
     clause_false (assignment old) c ->
     ~ clause_false (assignment new) c) /\
  (forall c, In c (installed_clauses new) ->
     ~ clause_false (assignment new) c).

Definition dense_summaries_restored
    (n live target : Z) (old_snap new_snap : dense_snapshot) : Prop :=
  snapshot_lengths n live new_snap /\
  snapshot_summaries_exact n live new_snap /\
  current_level
    (cdcl_view_of_snapshot n new_snap (fun _ => None) target) = target /\
  snap_rows new_snap = snap_rows old_snap.

(*  (rows states true_counts unassigned) state corresponds to
    valuation where 0-until + exempt is already new_sigma valuation,
    from until to end is still old sigma valuation *)
Definition mixed_clause_summaries
    (old_sigma new_sigma : partial_valuation)
    (rows : list clause) (states true_counts unassigned : list Z)
    (live capacity processed_until : Z) (exempt : option Z) : Prop :=
  live = Zlength rows /\
  Zlength states = live /\
  Zlength true_counts = live /\
  Zlength unassigned = live /\
  0 <= live <= capacity /\
  0 <= processed_until <= live /\
  forall i, 0 <= i < live ->
    (i < processed_until \/ exempt = Some i ->
       summary_at new_sigma rows states true_counts unassigned i) /\
    (processed_until <= i /\ exempt <> Some i ->
       summary_at old_sigma rows states true_counts unassigned i).

(** Spatial ownership, kept as transparent compositions of shared arrays. *)

Definition var_header_rep
    (v_data values reasons levels : Z) : Assertion :=
  &(v_data # "var_data" ->ₛ "value") # Ptr |-> values **
  &(v_data # "var_data" ->ₛ "ancient") # Ptr |-> reasons **
  &(v_data # "var_data" ->ₛ "dl") # Ptr |-> levels.

Definition clause_header_rep
    (cl_data states true_counts unassigned rows : Z) : Assertion :=
  &(cl_data # "clause_data" ->ₛ "state") # Ptr |-> states **
  &(cl_data # "clause_data" ->ₛ "lit_state") # Ptr |-> true_counts **
  &(cl_data # "clause_data" ->ₛ "unassign_num") # Ptr |-> unassigned **
  &(cl_data # "clause_data" ->ₛ "value") # Ptr |-> rows.

Definition sat_header_rep
    (s n live cap logical_dl v_data cl_data : Z) : Assertion :=
  &(s # "sat_data" ->ₛ "v_size") # Int |-> n **
  &(s # "sat_data" ->ₛ "cl_size") # Int |-> live **
  &(s # "sat_data" ->ₛ "cl_maxsize") # Int |-> cap **
  &(s # "sat_data" ->ₛ "cur_dl") # Int |-> logical_dl **
  &(s # "sat_data" ->ₛ "v_data") # Ptr |-> v_data **
  &(s # "sat_data" ->ₛ "cl_data") # Ptr |-> cl_data.

Definition sat_entry_header_rep
    (s n live cap v_data cl_data : Z) : Assertion :=
  &(s # "sat_data" ->ₛ "v_size") # Int |-> n **
  &(s # "sat_data" ->ₛ "cl_size") # Int |-> live **
  &(s # "sat_data" ->ₛ "cl_maxsize") # Int |-> cap **
  (&(s # "sat_data" ->ₛ "cur_dl")) # Int |->_ **
  &(s # "sat_data" ->ₛ "v_data") # Ptr |-> v_data **
  &(s # "sat_data" ->ₛ "cl_data") # Ptr |-> cl_data.

Definition installed_rows_capacity_rep
    (p live cap : Z) (rows : list (list Z)) : Assertion :=
  IntPtrArray2.full p live rows ** PtrArray.undef_seg p live cap.

(** The variable-indexed array bundle: the three per-variable arrays, always
    full over [0, n) and always keyed on one snapshot.  33 such runs. *)
Definition variable_arrays_rep
    (values reasons levels n : Z) (snap : dense_snapshot) : Assertion :=
  IntArray.full values n (snap_values snap) **
  IntArray.full reasons n (snap_reasons snap) **
  IntArray.full levels n (snap_levels snap).

(** The clause-indexed array bundle actually carried at stable points: the three
    clause-indexed summary arrays, each a live [seg] plus a capacity
    [seg_shape], plus the row table.  The arrays are keyed on ONE snapshot and
    ONE [live] bound here, which is exactly what lets them bundle -- 22 such
    runs in the C annotations, and it is this predicate, not the explicit
    family below, that every function's [Require]/[Ensure] and every outer loop
    invariant carries. *)
Definition solver_arrays_rep
    (states true_counts unassigned row_table live cap : Z)
    (snap : dense_snapshot) : Assertion :=
  IntArray.seg states 0 live (snap_states snap) **
  IntArray.seg_shape states live cap **
  IntArray.seg true_counts 0 live (snap_true_counts snap) **
  IntArray.seg_shape true_counts live cap **
  IntArray.seg unassigned 0 live (snap_unassigned snap) **
  IntArray.seg_shape unassigned live cap **
  installed_rows_capacity_rep row_table live cap (snap_rows snap).

(** The clause-indexed array bundle, in two layers.

    [clause_summaries_explicit_rep] owns the three clause-indexed summary
    arrays, each as a live [full] plus a capacity [seg_shape] -- six atoms.
    [clause_arrays_explicit_rep] adds the row table on top of it.  Unlike
    [solver_arrays_rep] above, both take the three summary lists explicitly
    rather than reading them out of a snapshot.

    Since the Wave-2 folds this family is load-bearing rather than staged:
    the whole-table shared head [solver_explicit_state] carries
    [clause_arrays_explicit_rep] as its clause side, the C annotations reach
    the family through that head (via the [backtrack_inner_state] wrapper,
    and directly once the decide and bcp blocks fold onto it), and the
    strategy chain (71/72, then 23/24 and 29/30) shreds it to the same raw
    atoms the longhand blocks used to spell.  The rep layers themselves are
    still not named verbatim by any C annotation -- what surfaces in the
    generated goal file are the heads.  The layering is what lets an
    assertion name the summaries without also claiming the whole row table.
    While one row is focused ([installed_row_focus_rep] below) the table is
    not [IntPtrArray2.full], so the summaries compose with a focused row
    where [solver_arrays_rep] cannot: the full table and a focused row are
    never owned together.

    Because the summary lists are explicit, the family serves exactly the
    mid-update points the snapshot-keyed bundles above cannot express: the
    arrays keyed on different snapshots -- the non-uniformity that sank the
    earlier [solver_heap_rep] attempt.  Unfold at the inner annotation where
    indexing starts. *)
Definition clause_summaries_explicit_rep
    (states true_counts unassigned live cap : Z)
    (cur_states cur_true cur_unassigned : list Z) : Assertion :=
  IntArray.full states live cur_states **
  IntArray.seg_shape states live cap **
  IntArray.full true_counts live cur_true **
  IntArray.seg_shape true_counts live cap **
  IntArray.full unassigned live cur_unassigned **
  IntArray.seg_shape unassigned live cap.

Definition clause_arrays_explicit_rep
    (states true_counts unassigned row_table live cap : Z)
    (rows : list (list Z))
    (cur_states cur_true cur_unassigned : list Z) : Assertion :=
  clause_summaries_explicit_rep
    states true_counts unassigned live cap
    cur_states cur_true cur_unassigned **
  installed_rows_capacity_rep row_table live cap rows.

Definition installed_row_focus_rep
    (p live i row_ptr : Z) (rows : list (list Z)) : Assertion :=
  StorePtrAsElement.storeA p i row_ptr **
  IntArray.full row_ptr
    (Zlength (Znth i rows [])) (Znth i rows []) **
  IntPtrArray2.missing_i p live i row_ptr rows.

Definition stable_search_facts
    (n : Z) (snap : dense_snapshot)
    (ranks : Z -> option nat) (logical_dl : Z) : Prop :=
  let a := cdcl_view_of_snapshot n snap ranks logical_dl in
  grounded_at a /\ closed_levels a /\ frontier_closed a.

Definition no_conflict (a : cdcl_view) : Prop :=
  forall c, In c (installed_clauses a) -> ~ clause_false (assignment a) c.

Definition no_unit (a : cdcl_view) : Prop :=
  forall c, In c (installed_clauses a) -> ~ clause_unit (assignment a) c.

Definition total_assignment_on (n : Z) (a : cdcl_view) : Prop :=
  forall x, var_in_range n x -> exists b, assignment a x = Some b.

(** Phase facts.  Everything from here to [unsat_terminal] is a [Prop] saying
    which phase of the search the solver is in and what holds of the state
    there.  None of them owns memory.

    These carried a [_rep] suffix until the wave-1 rename.  In QCP/VST that
    conventionally marks a *spatial* predicate, so the names were actively
    misleading -- a fossil of the Prop-demotion sweep (be2eb76), which turned
    [f(H, args) : Assertion] wrappers into [f(args) : Prop] but kept the old
    names.  Every [_rep] name left in this file is an [Assertion], and no
    [Prop] carries the suffix, so the convention now means what it says.

    Keep it that way: a new [Prop] here must not be given a [_rep] name. *)

Definition bcp_ready (a : cdcl_view) : Prop :=
  no_conflict a.

Definition propagation_quiescent
    (a : cdcl_view) : Prop :=
  no_conflict a /\ no_unit a.

Definition decision_ready := propagation_quiescent.

Definition model_ready
    (n : Z) (a : cdcl_view) : Prop :=
  propagation_quiescent a /\ total_assignment_on n a.

Definition learning_ready_conflict
    (a : cdcl_view) (i : Z) : Prop :=
  exists c,
      nth_error (installed_clauses a) (Z.to_nat i) = Some c /\
      clause_false (assignment a) c.

(* a is the current implementation's initial state, a coherent snapshot with no
    assignments and clauses exactly the same as the input formula F. *)
Definition fresh_formula
    (F : cnf) (n original_count : Z)
    (a : cdcl_view) : Prop :=
  cnf_wf n F /\
    installed_clauses a = F /\
    Z.of_nat (List.length F) = original_count /\
    current_level a = 0 /\
    (forall x,
      var_in_range n x ->
      assignment a x = None /\
      level_of a x = None /\
      reason_of a x = None /\
      assignment_rank a x = None) /\
    Forall (fun c => c <> []) F.

  (* The last assignment is the immediate cause of conflict,
  the installed_view is the conflict view with the learned clause
  added, but the backjump for installed_view is still pending *)
(** The pure content of [pending_backjump_rep], named separately so that the
    fact can be stated without an [Assertion] appearing inside a [Prop].
    [pending_backjump_rep] below is [emp && “ this ”] -- it owns no memory, so
    producing it costs a pure obligation and not an ownership one. *)
Definition pending_backjump_facts
    (F : cnf)
    (bcp_start conflict_view installed_view : cdcl_view)
    (physical_dl target last : Z) (learned : clause) : Prop :=
  physical_dl = target /\
  current_level installed_view = current_level conflict_view /\
  assignment installed_view = assignment conflict_view /\
  level_of installed_view = level_of conflict_view /\
  reason_of installed_view = reason_of conflict_view /\
  assignment_rank installed_view = assignment_rank conflict_view /\
  installed_clauses installed_view =
    installed_clauses conflict_view ++ [learned] /\
  dense_conflict_batch bcp_start conflict_view last /\
  backjump_target_profile conflict_view target learned /\
  learned_backjump_cert F conflict_view target learned.

Definition pending_backjump_rep
    (F : cnf)
    (bcp_start conflict_view installed_view : cdcl_view)
    (physical_dl target last : Z) (learned : clause) : Assertion :=
  emp &&
  “ pending_backjump_facts F bcp_start conflict_view installed_view
      physical_dl target last learned ”.

  (* decision level = 0, so no unimplied decision made, but the
  formula still entails false, so it must be unsatisfiable*)
Definition unsat_terminal
    (F : cnf) (a : cdcl_view) : Prop :=
  (current_level a = 0 /\
      exists c, In c (installed_clauses a) /\
        clause_false (assignment a) c) \/
    entails_clause F [].

(** Public solver-contract vocabulary.

    The eight definitions below are the entire surface of [cdcl_solver]'s
    contract: one input state, three result arms, and the four components they
    are composed from.  Nothing else in this file depends on them.  They exist
    so that the public contract reads as "SAT, or UNSAT, or learned-clause
    capacity exhausted" instead of as three twenty-line conjunctions.

    Three things here are load-bearing rather than cosmetic.

    [store_cnf] is built on the seg-based [solver_arrays_rep], NOT on
    [clause_arrays_explicit_rep].  Entry and all three exits are stable points,
    where the three summary arrays are keyed on one snapshot and one [live]
    bound; that is exactly what the seg family says, and it is what every
    unchanged body annotation of [cdcl_solver] carries.  The [full]-based
    explicit family is for mid-update points and would not match.

    The capacity arm owns the full row table AND a separate [IntArray.full]
    row.  That is not a double claim on one allocation: the orphan row is a
    fresh allocation, not a focused slot of the table, so
    [installed_row_focus_rep] -- which is the focused-slot mode, mutually
    exclusive with full-table ownership -- must not be used here.

    Mixed pure/spatial content is written [“ P ” && H].  The reversed spelling,
    with the [coq_prop] to the right of a separating conjunction, is forbidden:
    [coq_prop] is heap-agnostic (it is [fun _ => P], ignoring the world), so
    that slot absorbs arbitrary leftover heap and the assertion silently stops
    pinning its footprint.  It is not unsound -- everything proved about it is
    true -- but it is weaker than intended, which is worse here, because the
    weakness is invisible at the use site. *)

(** Every variable cell still holds its sentinel.  This is named rather than
    written inline because a strategy action is a first-order application and
    cannot carry a quantifier.  The cellwise [Znth] spelling is deliberately
    the one [snapshot_cells_wf] produces.  At entry this is a *derived* fact,
    not an added requirement: [coherent_snapshot] and [fresh_formula] together
    imply it, so naming it does not strengthen the precondition. *)
Definition all_unassigned_cells (n : Z) (snap : dense_snapshot) : Prop :=
  forall x, var_in_range n x ->
    Znth x (snap_values snap) (-1) = -1 /\
    Znth x (snap_reasons snap) (-1) = -1 /\
    Znth x (snap_levels snap) (-1) = -1.

(** The formula side: the three clause-indexed summary arrays and the
    installed row table, carrying the coherence facts -- exact original
    prefix and sound learned suffix, both inside [coherent_snapshot]. *)
Definition store_cnf
    (F : cnf)
    (n original_count states true_counts unassigned row_table live cap : Z)
    (snap : dense_snapshot) : Assertion :=
  “ coherent_snapshot F n live original_count snap ” &&
  solver_arrays_rep states true_counts unassigned row_table live cap snap.

(** The assignment side, in three modes.  All three own exactly the same three
    variable arrays and differ only in what they say about the stored values:
    every cell is a sentinel; the decoded valuation is exactly [J]; or nothing
    at all. *)
Definition uninitialized_Assignment
    (values reasons levels n : Z) (snap : dense_snapshot) : Assertion :=
  “ all_unassigned_cells n snap ” &&
  variable_arrays_rep values reasons levels n snap.

Definition store_Assignment
    (values reasons levels n : Z) (snap : dense_snapshot)
    (J : Assignment) : Assertion :=
  “ J = rho_of_values n (snap_values snap) ” &&
  variable_arrays_rep values reasons levels n snap.

Definition unconstrained_Assignment
    (values reasons levels n : Z) (snap : dense_snapshot) : Assertion :=
  variable_arrays_rep values reasons levels n snap.

(** The four arm cores.  Each takes the complete entry ghost vector as
    parameters, in the order [cdcl_solver]'s [With] list fixes, even where an
    arm does not inspect an entry snapshot, rank map or live count.

    The reason is NOT that the body annotations name them -- since the block-6
    fold, [snap], [ranks] and [live] have zero occurrences in C:1344-1530.  It
    is that [cdcl_solver]'s [Ensure] fixes the ghost vector universally, so
    hiding any of them existentially makes the loop-exit entailment unprovable
    (see the note at [solver_loop_state]); and the strategy rules match
    [?snap, ?ranks] positionally.

    The only existentials are the post-state values the arm genuinely does not
    determine -- final snapshot/level/live, the capacity arm's conflict
    snapshot/ranks/level and orphan row -- plus [v_data] and [cl_data].  Those
    last two are the struct-pointer intermediates that the C surface generates
    implicitly as fresh per-assertion variables; a Rocq definition has to bind
    them, and the contract never pinned them across entry and exit either. *)
Definition solver_input_core
    (s : Z) (F : cnf) (original_count : Z)
    (snap : dense_snapshot) (ranks : Z -> option nat)
    (values reasons levels states true_counts unassigned row_table
       n live cap : Z) : Assertion :=
  EX (v_data cl_data : Z),
  “ 0 <= n /\ n < INT_MAX /\
    0 <= original_count /\ original_count = live /\
    0 <= live /\ live <= cap /\
    stable_search_facts n snap ranks 0 /\
    fresh_formula F n original_count
      (cdcl_view_of_snapshot n snap ranks 0) ” &&
  (sat_entry_header_rep s n live cap v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   store_cnf F n original_count states true_counts unassigned row_table
     live cap snap **
   uninitialized_Assignment values reasons levels n snap).

Definition solver_sat_arm_core
    (s : Z) (F : cnf) (original_count : Z)
    (snap : dense_snapshot) (ranks : Z -> option nat)
    (values reasons levels states true_counts unassigned row_table
       n live cap : Z) (J : Assignment) : Assertion :=
  EX (final_snap : dense_snapshot) (final_dl final_live v_data cl_data : Z),
  “ original_count <= final_live /\ final_live <= cap ” &&
  (sat_header_rep s n final_live cap final_dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   store_cnf F n original_count states true_counts unassigned row_table
     final_live cap final_snap **
   store_Assignment values reasons levels n final_snap J).

(** The UNSAT arm.  The client-facing guarantee is [cnf_unsat n F], and it is
    stated as a visible conjunct of the C [Ensure] rather than here, so a reader
    sees the verdict without unfolding anything.

    [unsat_terminal] -- the solver's internal *certificate*, i.e. the route by
    which it justified the conclusion -- is deliberately NOT published.  It is
    how the proof gets to [cnf_unsat], not something a caller can use, and a
    postcondition should promise what the caller gets rather than recount how it
    was obtained.  Dropping it is a weakening, hence sound: a weaker Ensure is
    strictly easier to establish.  [ranks] is consequently unused here; it stays
    a parameter only to keep the four arm cores uniform. *)
Definition solver_unsat_arm_core
    (s : Z) (F : cnf) (original_count : Z)
    (snap : dense_snapshot) (ranks : Z -> option nat)
    (values reasons levels states true_counts unassigned row_table
       n live cap : Z) : Assertion :=
  EX (final_snap : dense_snapshot) (final_dl final_live v_data cl_data : Z),
  “ original_count <= final_live /\ final_live <= cap ” &&
  (sat_header_rep s n final_live cap final_dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   store_cnf F n original_count states true_counts unassigned row_table
     final_live cap final_snap **
   unconstrained_Assignment values reasons levels n final_snap).

(** The resource-limit arm: the solver gave up.  [cl_size] and [cl_maxsize] are
    both [cap] -- the clause table is full -- and the arm makes NO claim about
    [F] whatsoever.

    It states only that memory is in a good state: level bounds, a well-formed
    orphan row, the pointer/size identities, and ownership of every array plus
    the separately allocated uninstalled row.  It deliberately does not carry
    [stable_search_facts] (that the search state is a legitimate CDCL state) or
    [current_learning_exit_cert] (that the learned clause is entailed by [F]).
    Both were inherited from the loop invariant this arm exits from, not chosen:
    a return path should promise what a caller gets, and a caller of a [-2]
    result gets nothing about [F].

    Two consequences worth recording.  Dropping them is a weakening, hence
    sound -- a weaker Ensure is strictly easier to establish, so no proof can
    break.  And it makes "this arm exposes no verdict" true *by construction*
    rather than by argument: with no formula-relative pure fact present there is
    nothing to leak, so no consistency lemma is needed.  [conflict_ranks]
    disappeared with them; [ranks] stays a parameter only for uniformity. *)
Definition solver_capacity_exhausted_arm_core
    (s : Z) (F : cnf) (original_count : Z)
    (snap : dense_snapshot) (ranks : Z -> option nat)
    (values reasons levels states true_counts unassigned row_table
       n live cap : Z) : Assertion :=
  EX (conflict_snap : dense_snapshot)
     (conflict_dl row_ptr : Z) (row : list Z) (v_data cl_data : Z),
  “ 0 < conflict_dl /\ conflict_dl <= n /\ row_wf n row ” &&
  (sat_header_rep s n cap cap conflict_dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   store_cnf F n original_count states true_counts unassigned row_table
     cap cap conflict_snap **
   unconstrained_Assignment values reasons levels n conflict_snap **
   IntArray.full row_ptr n row).

(** Helper-contract vocabulary.

    Four named states, one family, one per internal helper contract:
    [solver_state] for [bcp], [decide] and [backtrack], [learning_state] for
    [clause_learning], [backjump_state] for [backtrack]'s entry and
    [propagation_result] for [bcp]'s conflict exit.  Each is exactly the
    spatial footprint its contract used to spell out as a dozen field-address
    identities plus five or six ownership atoms, and nothing beyond it.

    All four are purely spatial apart from [propagation_result]'s single batch
    witness.  Every pure fact of every helper contract -- the numeric bounds,
    [coherent_snapshot], [stable_search_facts], and the phase gate
    ([bcp_ready], [decision_ready], [learning_ready_conflict],
    [propagation_quiescent], [model_ready]) -- stays a visible conjunct of the
    C contract, on both sides.  That is load-bearing twice over: a reader sees
    what a helper assumes and promises without unfolding anything, and the
    pure/spatial split of every generated obligation at every call site is
    unchanged.  It is also why these are built on [solver_arrays_rep] and never
    on [store_cnf], which carries [coherent_snapshot] inside it.

    [v_data] and [cl_data] are local [EX] binders in all four.  The C surface
    generates them as per-assertion-fresh logical variables ([s_pre_v_data],
    [s_pre_cl_data]) and no contract ever pinned them across entry and exit, so
    a Rocq definition has to bind them rather than take them.

    Positional convention, shared by [solver_state] and [learning_state]:
    [s], then the ten untyped ghosts [values .. cap] verbatim as the helper
    [With] vectors already order them, then the decision level and the
    snapshot.  Those last two are the only positions that differ between a
    quiescent state and a committed one, so the reader can see at a glance that
    two applications describe the same memory at two moments. *)

(** The whole solver state at ONE decision level and ONE snapshot: the six
    [sat_data] header cells, the two field-pointer header bundles, the three
    variable arrays and the clause-indexed bundle.

    One predicate serves [bcp]'s entry and quiescent exit, [decide]'s entry and
    both arms, and [backtrack]'s exit -- six applications differing only in
    [dl] and [snap].  The three helper designs had reached the same Assertion
    under three names ([decision_state], [propagation_state],
    [backjump_restored]) at the same positional signature; two of them wrote the
    variable side [unconstrained_Assignment] and one wrote
    [variable_arrays_rep], which is a definitional alias of it, so the
    difference was a spelling and not a predicate.  Merging them matters beyond
    vocabulary size: it turns the file's only cut-free callee-to-callee hand-off
    -- [backtrack]'s [Ensure] feeding [bcp]'s [Require] with no intervening
    statement -- from a predicate-to-predicate entailment into a head-identical
    cancellation at unifiable arguments. *)
Definition solver_state
    (s values reasons levels states true_counts unassigned row_table
       n live cap dl : Z)
    (snap : dense_snapshot) : Assertion :=
  EX (v_data cl_data : Z),
  (sat_header_rep s n live cap dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   unconstrained_Assignment values reasons levels n snap **
   solver_arrays_rep states true_counts unassigned row_table live cap snap).

(** [clause_learning]'s footprint, and the one member of the family that is
    deliberately NOT [solver_state].

    It owns the thirteen header cells, the [reasons] and [levels] arrays, and
    the row table -- and nothing else.  [IntArray.full values] and the six
    clause-summary atoms stay in the caller's frame, because that is where they
    are at the call site: reusing [solver_state] here would strengthen the
    footprint to memory the function never touches.  [values], [states],
    [true_counts] and [unassigned] are still parameters, since they are the
    stored values of header cells; naming them does not claim their arrays.

    The learned row is not here either.  It is a fresh allocation, so
    [clause_learning]'s [Ensure] keeps it as a separate top-level conjunct
    alongside this predicate, exactly as the capacity arm keeps its orphan row.
    Full-table ownership and a focused row are mutually exclusive: this
    predicate holds the table unfocused, and the copy loop's own invariant
    holds the focused decomposition. *)
Definition learning_state
    (s values reasons levels states true_counts unassigned row_table
       n live cap logical_dl : Z)
    (snap : dense_snapshot) : Assertion :=
  EX (v_data cl_data : Z),
  (sat_header_rep s n live cap logical_dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   IntArray.full reasons n (snap_reasons snap) **
   IntArray.full levels n (snap_levels snap) **
   installed_rows_capacity_rep row_table live cap (snap_rows snap)).

(** [backtrack]'s entry state: [solver_state]'s footprint at the snapshot being
    unwound, plus the promise that the backjump is still pending.

    [pending_backjump_rep] carries the three views the promise relates -- where
    propagation started, where it conflicted, and the conflict state with the
    learned clause installed -- so the three snapshots and three rank maps are
    parameters here rather than existentials; the unchanged body annotations
    name them directly.  All three views are taken at [conflict_dl], the level
    the promise was made at, while the header's [cur_dl] cell carries [back_dl],
    the level the caller has already written.  [original_count] is a parameter
    for signature uniformity with the rest of the family and for the [Require]
    that sits next to this one; nothing spatial here depends on it.

    Compare [solver_state]: this is that predicate plus the promise, and
    [backtrack]'s job is precisely to discharge the promise and hand back the
    plain state. *)
Definition backjump_state
    (s : Z) (F : cnf) (original_count : Z)
    (start_snap conflict_snap snap : dense_snapshot)
    (start_ranks conflict_ranks ranks : Z -> option nat)
    (conflict_dl back_dl last : Z) (learned : list literal)
    (values reasons levels states true_counts unassigned row_table
       n live cap : Z) : Assertion :=
  EX (v_data cl_data : Z),
  (sat_header_rep s n live cap back_dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   variable_arrays_rep values reasons levels n snap **
   solver_arrays_rep states true_counts unassigned row_table live cap snap **
   pending_backjump_rep F
     (cdcl_view_of_snapshot n start_snap start_ranks conflict_dl)
     (cdcl_view_of_snapshot n conflict_snap conflict_ranks conflict_dl)
     (cdcl_view_of_snapshot n snap ranks conflict_dl)
     back_dl back_dl last learned).

(** The conflict result of one propagation batch: [solver_state] at the
    post-batch snapshot, plus the witness that a single variable assignment
    caused every conflict in the batch.

    [pre_snap], [pre_ranks] and [last] are bound here because no annotation
    inside [bcp] names them: they describe the state before the batch, which the
    caller neither supplies nor inspects.  Binding them here is what lets
    [bcp]'s two [Ensure] arms share one existential prefix instead of the
    quiescent arm carrying three existentials it has no use for.

    The conflict index is deliberately not a parameter.  It is [bcp]'s return
    value, and its gate [learning_ready_conflict] stays visible in the C
    contract right beside the range bound the caller consumes. *)
Definition propagation_result
    (s values reasons levels states true_counts unassigned row_table
       n live cap logical_dl : Z)
    (snap1 : dense_snapshot) (ranks1 : Z -> option nat) : Assertion :=
  EX (pre_snap : dense_snapshot) (pre_ranks : Z -> option nat) (last : Z),
  “ dense_conflict_batch
      (cdcl_view_of_snapshot n pre_snap pre_ranks logical_dl)
      (cdcl_view_of_snapshot n snap1 ranks1 logical_dl) last ” &&
  solver_state s values reasons levels states true_counts unassigned row_table
    n live cap logical_dl snap1.

(** [cdcl_solver]'s own phase states.  Where the four predicates above name a
    callee's footprint, these name the solver loop's own resting points, so the
    body reads as a sequence of named phases rather than twenty-odd lines of
    header equations repeated at each one.

    All of them keep [snap], [ranks] and [dl] existential -- those are
    [exists]-bound in the C blocks already -- and take the ten array/size
    ghosts as PARAMETERS, in the same order as [backjump_state] and the arm
    cores.  That is not a style choice: the [Ensure] fixes those ghosts
    universally, so hiding one existentially makes the loop-exit entailment
    silently unprovable (cancelling the header cells forces [values' = values]
    with nothing left to prove it from). *)

(** The top of the search loop, immediately before [bcp]. *)
Definition solver_loop_state
    (s : Z) (F : cnf)
    (original_count values reasons levels states true_counts unassigned
       row_table n live cap : Z)
    (snap : dense_snapshot) (ranks : Z -> option nat) (dl : Z) : Assertion :=
  “ 0 <= dl /\ dl <= n /\
    0 <= original_count /\ original_count <= live /\
    0 <= live /\ live <= cap /\
    coherent_snapshot F n live original_count snap /\
    stable_search_facts n snap ranks dl /\
    bcp_ready (cdcl_view_of_snapshot n snap ranks dl) ” &&
  solver_state s values reasons levels states true_counts unassigned
    row_table n live cap dl snap.

(** Which of [bcp]'s two exits the loop is at.  This is the PURE projection of
    [bcp]'s [Ensure] (CDCL_qcp.c:415-423), with the spatial [solver_state]
    hoisted out of both arms -- sound because arm 1 carries [solver_state]
    directly and arm 2 carries [propagation_result], which is
    [dense_conflict_batch && solver_state]. *)
Definition bcp_outcome
    (post pre : cdcl_view) (live conflict_cl last : Z) : Prop :=
  (conflict_cl = -1 /\ propagation_quiescent post) \/
  (0 <= conflict_cl /\ conflict_cl < live /\
   dense_conflict_batch pre post last /\
   learning_ready_conflict post conflict_cl).

(** The snapshot after the learned row is installed: variable side untouched,
    each clause-indexed list extended by exactly one entry. *)
Definition snapshot_installs
    (row : list Z) (old new : dense_snapshot) : Prop :=
  snap_values new = snap_values old /\
  snap_reasons new = snap_reasons old /\
  snap_levels new = snap_levels old /\
  snap_rows new = snap_rows old ++ [row] /\
  snap_states new = snap_states old ++ [1] /\
  snap_true_counts new = snap_true_counts old ++ [0] /\
  snap_unassigned new = snap_unassigned old ++ [0].

(** Immediately after [bcp] returns, before the conflict test. *)
Definition solver_after_bcp_state
    (s : Z) (F : cnf)
    (original_count values reasons levels states true_counts unassigned
       row_table n live cap conflict_cl : Z)
    (snap : dense_snapshot) (ranks : Z -> option nat) (dl : Z) : Assertion :=
  EX (pre_snap : dense_snapshot) (pre_ranks : Z -> option nat) (last : Z),
  “ 0 <= dl /\ dl <= n /\
    0 <= original_count /\ original_count <= live /\
    0 <= live /\ live <= cap /\
    coherent_snapshot F n live original_count snap /\
    stable_search_facts n snap ranks dl /\
    bcp_outcome
      (cdcl_view_of_snapshot n snap ranks dl)
      (cdcl_view_of_snapshot n pre_snap pre_ranks dl)
      live conflict_cl last ” &&
  solver_state s values reasons levels states true_counts unassigned
    row_table n live cap dl snap.

(** After [clause_learning] returns the learned row, before installation.
    This is the state the [-2] capacity return exits from: on the [live = cap]
    path it contains verbatim what [solver_capacity_exhausted_arm_core] needs,
    with the orphan row kept as a separate top-level conjunct. *)
Definition solver_learning_state
    (s : Z) (F : cnf)
    (original_count values reasons levels states true_counts unassigned
       row_table n live cap conflict_cl new_cl : Z)
    (row : list Z)
    (snap : dense_snapshot) (ranks : Z -> option nat) (dl : Z) : Assertion :=
  EX (pre_snap : dense_snapshot) (pre_ranks : Z -> option nat) (last : Z),
  “ 0 <= conflict_cl /\ conflict_cl < live /\
    0 < dl /\ dl <= n /\
    0 <= original_count /\ original_count <= live /\
    0 <= live /\ live <= cap /\
    coherent_snapshot F n live original_count snap /\
    stable_search_facts n snap ranks dl /\
    dense_conflict_batch
      (cdcl_view_of_snapshot n pre_snap pre_ranks dl)
      (cdcl_view_of_snapshot n snap ranks dl) last /\
    current_learning_exit_cert F
      (cdcl_view_of_snapshot n snap ranks dl) (dense_decode row) /\
    row_wf n row /\
    learning_ready_conflict
      (cdcl_view_of_snapshot n snap ranks dl) conflict_cl ” &&
  (solver_state s values reasons levels states true_counts unassigned
     row_table n live cap dl snap **
   IntArray.full new_cl n row).

(** Named code-order transients.  [H] is precisely the currently owned
    heap/coherent frame; each predicate adds only the facts for its real loop
    or write gap. *)

(** Exact cellwise operation implemented by [clause_resolution]. *)
Definition dense_cancel_cell (a b : Z) : Z :=
  if orb (andb (a =? 1) (b =? -1)) (andb (a =? -1) (b =? 1))
  then 0
  else if a =? 0 then b else a.

Definition dense_cancel_union (left right : list Z) : list Z :=
  map (fun ab => dense_cancel_cell (fst ab) (snd ab))
    (combine left right).

(** Exact leaf-helper ownership.  Resolution is post-state-only because the
    result row does not exist on entry.  Conflict analysis has one stable,
    narrow read footprint, suitable at entry and later stable points. *)
Definition resolution_rows_rep
    (wi wj result n : Z) (left right : list Z) : Assertion :=
  IntArray.full wi n left **
  IntArray.full wj n right **
  IntArray.full result n (dense_cancel_union left right).

Definition conflict_levels_rep
    (s clause n v_data levels : Z)
    (row : list Z) (snap : dense_snapshot) : Assertion :=
  &(s # "sat_data" ->ₛ "v_size") # Int |-> n **
  &(s # "sat_data" ->ₛ "v_data") # Ptr |-> v_data **
  &(v_data # "var_data" ->ₛ "dl") # Ptr |-> levels **
  IntArray.full clause n row **
  IntArray.full levels n (snap_levels snap).

(* different from assigns_one, assigns_one completes other updates
    such as decision level
     + reason
     + well-founded rank
     + complete framing of other variables*)
Definition assignment_update_only
    (old new : cdcl_view) (x : Z) (b : bool) : Prop :=
  assignment old x = None /\
  assignment new x = Some b /\
  (forall y, y <> x -> assignment new y = assignment old y) /\
  installed_clauses new = installed_clauses old.

  (* current is old being backtracked to dl target, and vars up to
  processed have been backtracked while those after have not and are
  still the same as old*)
Definition prefix_restriction
    (old current : cdcl_view) (n target processed : Z) : Prop :=
  0 <= processed <= n /\
  installed_clauses current = installed_clauses old /\
  (forall x,
    var_in_range n x ->
    (x < processed ->
      match level_of old x with
      | Some d =>
          if target <? d
          then assignment current x = None /\
               level_of current x = None /\
               reason_of current x = None /\
               assignment_rank current x = None
          else assignment current x = assignment old x /\
               level_of current x = level_of old x /\
               reason_of current x = reason_of old x /\
               assignment_rank current x = assignment_rank old x
      | None => assignment current x = assignment old x /\
                level_of current x = level_of old x /\
                reason_of current x = reason_of old x /\
                assignment_rank current x = assignment_rank old x
      end) /\
    (processed <= x ->
      assignment current x = assignment old x /\
      level_of current x = level_of old x /\
      reason_of current x = reason_of old x /\
      assignment_rank current x = assignment_rank old x)).

(* new is old with x cleared*)
Definition clears_one
    (old new : cdcl_view) (x : Z) : Prop :=
  (exists b d,
    assignment old x = Some b /\ level_of old x = Some d) /\
  assignment new x = None /\
  level_of new x = None /\
  reason_of new x = None /\
  assignment_rank new x = None /\
  (forall y, y <> x ->
    assignment new y = assignment old y /\
    level_of new y = level_of old y /\
    reason_of new y = reason_of old y /\
    assignment_rank new y = assignment_rank old y) /\
  installed_clauses new = installed_clauses old.

Definition processed_level
    (a : cdcl_view) (row : list Z) (processed d : Z) : Prop :=
  exists x,
    0 <= x < processed /\
    Znth x row 0 <> 0 /\
    level_of a x = Some d.

(* max1 is top processed level, max2 is second highest level,
 if doesn't exist will be -1*)
Definition top_two_levels_exact
    (a : cdcl_view) (row : list Z)
    (processed max1 max2 : Z) : Prop :=
  ((forall d, ~ processed_level a row processed d) /\
    max1 = -1 /\ max2 = -1) \/
  (processed_level a row processed max1 /\
   (forall d, processed_level a row processed d -> d <= max1) /\
   ((max2 = -1 /\
     forall d, processed_level a row processed d -> d = max1) \/
    (processed_level a row processed max2 /\
     max2 < max1 /\
     forall d,
       processed_level a row processed d -> d < max1 -> d <= max2))).

(* none of the clauses before next are unit, so we check if next is unit in next step*)
Definition unit_scan
    (a : cdcl_view) (live next : Z) : Prop :=
  0 <= next <= live /\
    forall i, 0 <= i < next ->
      exists c, nth_error (installed_clauses a) (Z.to_nat i) = Some c /\
        ~ clause_unit (assignment a) c.

Definition unit_variable_scan
    (a : cdcl_view)
    (n live unit_index next : Z) : Prop :=
  0 <= unit_index < live /\ 0 <= next <= n /\
    exists c, nth_error (installed_clauses a) (Z.to_nat unit_index) = Some c /\
      clause_unit (assignment a) c /\
      forall x,
        0 <= x < next ->
        assignment a x = None ->
        ~ (In (Pos x) c \/ In (Neg x) c).

Definition bcp_clause_scan
    (old new : cdcl_view)
    (x : Z) (b : bool) (d reason processed_until exempt live cap : Z)
    (rows : list clause) (states true_counts unassigned : list Z) : Prop :=
  assigns_one old new x b d reason /\
    0 <= exempt < live /\
    mixed_clause_summaries
      (assignment old) (assignment new)
      rows states true_counts unassigned
      live cap processed_until (Some exempt).

Definition decision_update
    (old new : cdcl_view)
    (x next_clause live cap : Z)
    (rows : list clause) (states true_counts unassigned : list Z) : Prop :=
  assignment_update_only old new x true /\
    mixed_clause_summaries
      (assignment old) (assignment new)
      rows states true_counts unassigned live cap next_clause None.

Definition resolution_prefix
    (left right out : list Z) (processed : Z) : Prop :=
  0 <= processed <= Zlength out /\
    Zlength left = Zlength out /\ Zlength right = Zlength out /\
    (forall i, 0 <= i < processed ->
      Znth i out 0 =
        dense_cancel_cell (Znth i left 0) (Znth i right 0)) /\
    (forall i, processed <= i < Zlength out -> Znth i out 0 = 0).

Definition learning_loop
    (F : cnf) (a : cdcl_view) (n : Z)
    (working_row : list Z) (scan : Z) : Prop :=
  let working := dense_decode working_row in
  row_wf n working_row /\
    entails_clause F working /\
    clause_false (assignment a) working /\
    (working = [] \/ current_level_support a working) /\
    0 <= scan <= n /\
    (forall x,
      0 <= x < scan ->
      Znth x working_row 0 <> 0 ->
      level_of a x = Some (current_level a) ->
      reason_of a x = None).

Definition top_two_levels_prefix
    (a : cdcl_view) (n : Z) (row : list Z)
    (processed max1 max2 : Z) : Prop :=
  row_wf n row /\
    clause_vars_assigned a (dense_decode row) /\
    0 <= processed <= n /\
    top_two_levels_exact a row processed max1 max2.

Definition installing_clause
    (F : cnf) (a : cdcl_view)
    (n cap : Z) (row : list Z) (learned : clause)
    (old_live new_live : Z) : Prop :=
  0 <= old_live < cap /\
    new_live = old_live + 1 /\
    row_wf n row /\
    dense_decode row = learned /\
    current_learning_exit_cert F a learned.

(** The write gap: [cl_size] has been bumped to [live+1] but the three summary
    cells at index [live] and the row slot are not yet written.

    This one deliberately does NOT compose with [solver_state].  The reason is
    a single cell: [sat_header_rep] holds [cl_size |-> live+1] while the arrays
    still hold [live] entries, and [solver_state] drives the header and the
    arrays from the same [live] parameter, so no instantiation serves both.
    Removing the holes would not fix that. *)
(** [slot] is the clause count the header actually holds, and [slot_at]
    ties it to [live].  It is a definition rather than an inline equation
    on purpose: the strategy engine cannot unfold it, so array_shape rule
    14 cannot prove the written cell adjacent to the following shape and
    absorb it, which would discard the value the store just wrote.  See
    reports/qcpsat-symexec-segv-upstream-20260731.md section 7a. *)
Definition slot_at (slot live : Z) : Prop := slot = live + 1.

Definition solver_install_slot_state
    (s : Z) (F : cnf)
    (original_count values reasons levels states true_counts unassigned
       row_table n live cap slot conflict_cl new_cl : Z)
    (row : list Z)
    (snap : dense_snapshot) (ranks : Z -> option nat) (dl : Z) : Assertion :=
  EX (pre_snap : dense_snapshot) (pre_ranks : Z -> option nat) (last : Z)
     (old_state old_true_count old_unassigned : Z)
     (v_data cl_data : Z),
  “ slot_at slot live /\
    0 <= conflict_cl /\ conflict_cl < live /\
    0 < dl /\ dl <= n /\
    0 <= original_count /\ original_count <= live /\
    0 <= live /\ live < cap /\
    coherent_snapshot F n live original_count snap /\
    stable_search_facts n snap ranks dl /\
    dense_conflict_batch
      (cdcl_view_of_snapshot n pre_snap pre_ranks dl)
      (cdcl_view_of_snapshot n snap ranks dl) last /\
    current_learning_exit_cert F
      (cdcl_view_of_snapshot n snap ranks dl) (dense_decode row) /\
    installing_clause F (cdcl_view_of_snapshot n snap ranks dl)
      n cap row (dense_decode row) live (live + 1) ” &&
  (sat_header_rep s n slot cap dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   variable_arrays_rep values reasons levels n snap **
   IntArray.seg states 0 live (snap_states snap) **
   StoreIntAsElement.storeA states (slot - 1) old_state **
   IntArray.seg_shape states (live + 1) cap **
   IntArray.seg true_counts 0 live (snap_true_counts snap) **
   StoreIntAsElement.storeA true_counts (slot - 1) old_true_count **
   IntArray.seg_shape true_counts (live + 1) cap **
   IntArray.seg unassigned 0 live (snap_unassigned snap) **
   StoreIntAsElement.storeA unassigned (slot - 1) old_unassigned **
   IntArray.seg_shape unassigned (live + 1) cap **
   IntPtrArray2.full row_table live (snap_rows snap) **
   StorePtrAsElement.undefstoreA row_table (slot - 1) **
   PtrArray.undef_seg row_table (live + 1) cap **
   IntArray.full new_cl n row).

(** The learned row is installed and the summaries are extended, but the
    caller still owns the row buffer separately.  Also does not compose, for
    the same [cl_size |-> live+1] reason. *)
Definition solver_installed_row_state
    (s : Z) (F : cnf)
    (original_count values reasons levels states true_counts unassigned
       row_table n live cap conflict_cl new_cl : Z)
    (row : list Z)
    (snap : dense_snapshot) (ranks : Z -> option nat) (dl : Z) : Assertion :=
  EX (pre_snap installed_snap : dense_snapshot)
     (pre_ranks : Z -> option nat) (last : Z)
     (v_data cl_data : Z),
  “ snapshot_installs row snap installed_snap /\
    0 <= conflict_cl /\ conflict_cl < live /\
    0 < dl /\ dl <= n /\
    0 <= original_count /\ original_count <= live /\
    0 <= live /\ live < cap /\
    coherent_snapshot F n live original_count snap /\
    stable_search_facts n snap ranks dl /\
    dense_conflict_batch
      (cdcl_view_of_snapshot n pre_snap pre_ranks dl)
      (cdcl_view_of_snapshot n snap ranks dl) last /\
    current_learning_exit_cert F
      (cdcl_view_of_snapshot n snap ranks dl) (dense_decode row) /\
    clause_vars_assigned
      (cdcl_view_of_snapshot n snap ranks dl) (dense_decode row) /\
    installing_clause F (cdcl_view_of_snapshot n snap ranks dl)
      n cap row (dense_decode row) live (live + 1) ” &&
  (sat_header_rep s n (live + 1) cap dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   variable_arrays_rep values reasons levels n snap **
   clause_summaries_explicit_rep states true_counts unassigned (live + 1) cap
     (snap_states installed_snap)
     (snap_true_counts installed_snap)
     (snap_unassigned installed_snap) **
   IntPtrArray2.missing_i row_table (live + 1) live new_cl
     (snap_rows installed_snap) **
   StorePtrAsElement.storeA row_table live new_cl **
   IntArray.full new_cl n row **
   PtrArray.undef_seg row_table (live + 1) cap).

Definition backtrack_outer
    (old current : cdcl_view)
    (n target next_variable live cap : Z)
    (rows : list clause) (states true_counts unassigned : list Z) : Prop :=
  0 <= target /\
    prefix_restriction old current n target next_variable /\
    mixed_clause_summaries
      (assignment current) (assignment current)
      rows states true_counts unassigned live cap live None.

Definition backtrack_inner
    (old current after_clear : cdcl_view)
    (n target variable next_clause live cap : Z)
    (rows : list clause) (states true_counts unassigned : list Z) : Prop :=
  0 <= target /\ 0 <= variable < n /\
    prefix_restriction old current n target variable /\
    clears_one current after_clear variable /\
    mixed_clause_summaries
      (assignment current) (assignment after_clear)
      rows states true_counts unassigned live cap next_clause None.

Definition clearing_variable
    (old current after_clear : cdcl_view)
    (n target variable live cap : Z)
    (rows : list clause) (states true_counts unassigned : list Z) : Prop :=
  0 <= target /\ 0 <= variable < n /\
    prefix_restriction old current n target variable /\
    clears_one current after_clear variable /\
    mixed_clause_summaries
      (assignment after_clear) (assignment after_clear)
      rows states true_counts unassigned live cap live None.

(** Foundation facts. *)


Lemma dense_decode_from_var_lower_bound : forall row base l,
  In l (dense_decode_from base row) -> base <= literal_var l.
Proof.
  induction row as [|z row IH]; intros base l Hin; simpl in Hin.
  - contradiction.
  - destruct (z =? 1) eqn:Hz1.
    + destruct Hin as [<-|Hin]; simpl; [lia|].
      specialize (IH (base + 1) l Hin); lia.
    + destruct (z =? -1) eqn:Hzm.
      * destruct Hin as [<-|Hin]; simpl; [lia|].
        specialize (IH (base + 1) l Hin); lia.
      * specialize (IH (base + 1) l Hin); lia.
Qed.

Lemma dense_decode_from_pos_cell : forall row base i,
  0 <= i < Zlength row ->
  (Znth i row 0 = 1 <->
   In (Pos (base + i)) (dense_decode_from base row)).
Proof.
  induction row as [|z row IH]; intros base i Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons. simpl.
      replace (base + 0) with base by lia.
      destruct (z =? 1) eqn:Hz1.
      * apply Z.eqb_eq in Hz1; subst.
        split; [intro; left; reflexivity|intro; reflexivity].
      * destruct (z =? -1) eqn:Hzm; split.
        -- intros H; subst; discriminate.
        -- intros [H|H]; [discriminate|].
           pose proof (dense_decode_from_var_lower_bound row (base + 1)
             (Pos base) H); simpl in H0; lia.
        -- intros H; subst; discriminate.
        -- intros H.
           pose proof (dense_decode_from_var_lower_bound row (base + 1)
             (Pos base) H); simpl in H0; lia.
    + rewrite Znth_cons by lia. simpl.
      replace (base + i) with ((base + 1) + (i - 1)) by lia.
      specialize (IH (base + 1) (i - 1) ltac:(lia)).
      destruct (z =? 1) eqn:Hz1.
      * split.
        -- intro H; right; apply IH; exact H.
        -- intros [Heq|H].
           ++ inversion Heq; lia.
           ++ apply IH; exact H.
      * destruct (z =? -1) eqn:Hzm.
        -- split.
           ++ intro H; right; apply IH; exact H.
           ++ intros [Heq|H].
              ** discriminate.
              ** apply IH; exact H.
        -- exact IH.
Qed.

Lemma dense_decode_from_neg_cell : forall row base i,
  0 <= i < Zlength row ->
  (Znth i row 0 = -1 <->
   In (Neg (base + i)) (dense_decode_from base row)).
Proof.
  induction row as [|z row IH]; intros base i Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons. simpl.
      replace (base + 0) with base by lia.
      destruct (z =? 1) eqn:Hz1.
      * split.
        -- intros H; subst; discriminate.
        -- intros [H|H]; [discriminate|].
           pose proof (dense_decode_from_var_lower_bound row (base + 1)
             (Neg base) H); simpl in H0; lia.
      * destruct (z =? -1) eqn:Hzm.
        -- apply Z.eqb_eq in Hzm; subst.
           split; [intro; left; reflexivity|intro; reflexivity].
        -- split.
           ++ intros H; subst; discriminate.
           ++ intros H.
              pose proof (dense_decode_from_var_lower_bound row (base + 1)
                (Neg base) H); simpl in H0; lia.
    + rewrite Znth_cons by lia. simpl.
      replace (base + i) with ((base + 1) + (i - 1)) by lia.
      specialize (IH (base + 1) (i - 1) ltac:(lia)).
      destruct (z =? 1) eqn:Hz1.
      * split.
        -- intro H; right; apply IH; exact H.
        -- intros [Heq|H]; [discriminate|apply IH; exact H].
      * destruct (z =? -1) eqn:Hzm.
        -- split.
           ++ intro H; right; apply IH; exact H.
           ++ intros [Heq|H].
              ** inversion Heq; lia.
              ** apply IH; exact H.
        -- exact IH.
Qed.

Lemma row_wf_cell_domain : forall n row i,
  row_wf n row -> var_in_range n i ->
  Znth i row 0 = -1 \/ Znth i row 0 = 0 \/ Znth i row 0 = 1.
Proof.
  intros n row; revert n.
  induction row as [|z row IH]; intros n i [Hlen Hdom] [Hi0 Hin].
  - rewrite Zlength_nil in Hlen; lia.
  - rewrite Zlength_cons in Hlen.
    inversion Hdom as [|? ? Hz Htail].
    destruct (Z.eq_dec i 0) as [->|Hi].
    + rewrite Znth0_cons; exact Hz.
    + rewrite Znth_cons by lia.
      apply (IH (n - 1) (i - 1)).
      * split; [lia|exact Htail].
      * split; lia.
Qed.

Lemma dense_decode_pos : forall n row x,
  row_wf n row -> var_in_range n x ->
  (Znth x row 0 = 1 <-> In (Pos x) (dense_decode row)).
Proof.
  intros n row x [Hlen Hwf] Hx.
  unfold dense_decode.
  replace x with (0 + x) at 2 by lia.
  apply dense_decode_from_pos_cell.
  rewrite Hlen; exact Hx.
Qed.

Lemma dense_decode_neg : forall n row x,
  row_wf n row -> var_in_range n x ->
  (Znth x row 0 = -1 <-> In (Neg x) (dense_decode row)).
Proof.
  intros n row x [Hlen Hwf] Hx.
  unfold dense_decode.
  replace x with (0 + x) at 2 by lia.
  apply dense_decode_from_neg_cell.
  rewrite Hlen; exact Hx.
Qed.

Lemma dense_decode_zero : forall n row x,
  row_wf n row -> var_in_range n x ->
  (Znth x row 0 = 0 <->
   ~ In (Pos x) (dense_decode row) /\
   ~ In (Neg x) (dense_decode row)).
Proof.
  intros n row x Hwf Hx.
  pose proof (dense_decode_pos n row x Hwf Hx) as Hp.
  pose proof (dense_decode_neg n row x Hwf Hx) as Hn.
  pose proof (row_wf_cell_domain n row x Hwf Hx) as Hd.
  split.
  - intro Hz; split; intro Hin.
    + apply Hp in Hin; lia.
    + apply Hn in Hin; lia.
  - intros [Hnp Hnn].
    destruct Hd as [Hm|[Hz|Hp1]]; auto.
    + exfalso; apply Hnn, Hn; exact Hm.
    + exfalso; apply Hnp, Hp; exact Hp1.
Qed.


Lemma literal_var_count_nonneg : forall x c, 0 <= literal_var_count x c.
Proof.
  intros x c; induction c as [|l c IH].
  - reflexivity.
  - cbn [literal_var_count].
    destruct (literal_var l =? x).
    + change (0 <= 1 + literal_var_count x c).
      lia.
    + exact IH.
Qed.

Lemma literal_true_at_count_nonneg : forall x b c,
  0 <= literal_true_at_count x b c.
Proof.
  intros x b c; induction c as [|l c IH].
  - reflexivity.
  - cbn [literal_true_at_count].
    destruct (literal_var l =? x).
    + destruct (eval_literal (fun _ => b) l).
      * change (0 <= 1 + literal_true_at_count x b c).
        lia.
      * exact IH.
    + exact IH.
Qed.

Lemma clause_counts_assign : forall sigma x b c,
  sigma x = None ->
  clause_unassigned_count (partial_mapping_update sigma x b) c =
    clause_unassigned_count sigma c - literal_var_count x c /\
  clause_true_count (partial_mapping_update sigma x b) c =
    clause_true_count sigma c + literal_true_at_count x b c.
Proof.
  intros sigma x b c; induction c as [|l c IH]; intro Hx.
  - split; reflexivity.
  - cbn -[eval_partial_literal partial_mapping_update Z.add Z.sub] in *.
  specialize (IH Hx).
  destruct l as [y|y];
    destruct (Z.eq_dec x y) as [->|Hxy].
  + replace (eval_partial_literal (partial_mapping_update sigma y b) (Pos y))
      with (Some b) by
        (unfold eval_partial_literal; rewrite partial_mapping_update_eq; reflexivity).
    replace (eval_partial_literal sigma (Pos y)) with (None : option bool) by
      (unfold eval_partial_literal, literal_var; destruct (sigma y) eqn:Hy;
       [rewrite Hx in Hy; discriminate|reflexivity]).
    rewrite Z.eqb_refl. destruct IH as [IHu IHt].
    destruct b; cbn -[Z.add Z.sub]; split; lia.
  + replace (eval_partial_literal (partial_mapping_update sigma x b) (Pos y))
      with (eval_partial_literal sigma (Pos y)) by
        (unfold eval_partial_literal;
         rewrite partial_mapping_update_neq by exact Hxy; reflexivity).
    assert (Hyx : (y =? x) = false) by (apply Z.eqb_neq; lia).
    replace (y =? x) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct IH as [IHu IHt].
    destruct (eval_partial_literal sigma (Pos y)) as [[|]|];
      cbn -[Z.add Z.sub]; rewrite Hyx; rewrite IHu, IHt.
    all: split; lia.
  + replace (eval_partial_literal (partial_mapping_update sigma y b) (Neg y))
      with (Some (negb b)) by
        (unfold eval_partial_literal; rewrite partial_mapping_update_eq; reflexivity).
    replace (eval_partial_literal sigma (Neg y)) with (None : option bool) by
      (unfold eval_partial_literal, literal_var; destruct (sigma y) eqn:Hy;
       [rewrite Hx in Hy; discriminate|reflexivity]).
    rewrite Z.eqb_refl. destruct IH as [IHu IHt].
    destruct b; cbn -[Z.add Z.sub]; split; lia.
  + replace (eval_partial_literal (partial_mapping_update sigma x b) (Neg y))
      with (eval_partial_literal sigma (Neg y)) by
        (unfold eval_partial_literal;
         rewrite partial_mapping_update_neq by exact Hxy; reflexivity).
    assert (Hyx : (y =? x) = false) by (apply Z.eqb_neq; lia).
    replace (y =? x) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct IH as [IHu IHt].
    destruct (eval_partial_literal sigma (Neg y)) as [[|]|];
      cbn -[Z.add Z.sub]; rewrite Hyx;
      rewrite IHu, IHt; split; lia.
Qed.

Lemma clause_counts_clear : forall sigma x b c,
  sigma x = Some b ->
  clause_unassigned_count (clear_partial sigma x) c =
    clause_unassigned_count sigma c + literal_var_count x c /\
  clause_true_count (clear_partial sigma x) c =
    clause_true_count sigma c - literal_true_at_count x b c.
Proof.
  intros sigma x b c; induction c as [|l c IH]; intro Hx.
  - split; reflexivity.
  - cbn -[eval_partial_literal clear_partial total_mapping_update Z.add Z.sub] in *.
  specialize (IH Hx).
  destruct l as [y|y];
    destruct (Z.eq_dec x y) as [->|Hxy].
  + replace (eval_partial_literal (clear_partial sigma y) (Pos y))
      with (None : option bool) by
      (unfold eval_partial_literal, clear_partial;
       rewrite total_mapping_update_eq; reflexivity).
    replace (eval_partial_literal sigma (Pos y)) with (Some b) by
      (unfold eval_partial_literal, literal_var; destruct (sigma y) eqn:Hy;
       [inversion Hx; subst; reflexivity|discriminate]).
    rewrite Z.eqb_refl. destruct IH as [IHu IHt].
    destruct b; cbn -[Z.add Z.sub]; split; lia.
  + replace (eval_partial_literal (clear_partial sigma x) (Pos y))
      with (eval_partial_literal sigma (Pos y)) by
        (unfold eval_partial_literal, clear_partial;
         rewrite total_mapping_update_neq by exact Hxy; reflexivity).
    assert (Hyx : (y =? x) = false) by (apply Z.eqb_neq; lia).
    replace (y =? x) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct IH as [IHu IHt].
    destruct (eval_partial_literal sigma (Pos y)) as [[|]|];
      cbn -[Z.add Z.sub]; rewrite Hyx;
      rewrite IHu, IHt; split; lia.
  + replace (eval_partial_literal (clear_partial sigma y) (Neg y))
      with (None : option bool) by
      (unfold eval_partial_literal, clear_partial;
       rewrite total_mapping_update_eq; reflexivity).
    replace (eval_partial_literal sigma (Neg y)) with (Some (negb b)) by
      (unfold eval_partial_literal, literal_var; destruct (sigma y) eqn:Hy;
       [inversion Hx; subst; reflexivity|discriminate]).
    rewrite Z.eqb_refl. destruct IH as [IHu IHt].
    destruct b; cbn -[Z.add Z.sub]; split; lia.
  + replace (eval_partial_literal (clear_partial sigma x) (Neg y))
      with (eval_partial_literal sigma (Neg y)) by
        (unfold eval_partial_literal, clear_partial;
         rewrite total_mapping_update_neq by exact Hxy; reflexivity).
    assert (Hyx : (y =? x) = false) by (apply Z.eqb_neq; lia).
    replace (y =? x) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct IH as [IHu IHt].
    destruct (eval_partial_literal sigma (Neg y)) as [[|]|];
      cbn -[Z.add Z.sub]; rewrite Hyx;
      rewrite IHu, IHt; split; lia.
Qed.

Definition snapshot_set_value
    (snap : dense_snapshot) (x z : Z) : dense_snapshot :=
  {| snap_values := replace_Znth x z (snap_values snap);
     snap_reasons := snap_reasons snap;
     snap_levels := snap_levels snap;
     snap_rows := snap_rows snap;
     snap_states := snap_states snap;
     snap_true_counts := snap_true_counts snap;
     snap_unassigned := snap_unassigned snap |}.


Lemma installed_rows_capacity_expose : forall p live cap rows,
  live < cap ->
  installed_rows_capacity_rep p live cap rows |--
    IntPtrArray2.full p live rows **
    StorePtrAsElement.undefstoreA p live **
    PtrArray.undef_seg p (live + 1) cap.
Proof.
  intros p live cap rows Hcap.
  unfold installed_rows_capacity_rep.
  rewrite (PtrArray.undef_seg_unfold p live cap) by lia.
  entailer!.
Qed.

Lemma installed_rows_capacity_publish : forall p live cap rows newp row,
  0 <= live < cap ->
  IntPtrArray2.full p live rows **
  StorePtrAsElement.storeA p live newp **
  IntArray.full newp (Zlength row) row **
  PtrArray.undef_seg p (live + 1) cap |--
  installed_rows_capacity_rep p (live + 1) cap (rows ++ [row]).
Proof.
  intros p live cap rows newp row Hcap.
  unfold installed_rows_capacity_rep, IntPtrArray2.full.
  Intros row_ptrs.
  match goal with
  | Hlen : Zlength row_ptrs = live /\ Zlength rows = live |- _ =>
      destruct Hlen as [Hptrs Hrows]
  end.
  assert (Hptrs_app : Zlength (row_ptrs ++ [newp]) = live + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil; lia. }
  assert (Hrows_app : Zlength (rows ++ [row]) = live + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil; lia. }
  Exists (row_ptrs ++ [newp]).
  entailer!.
  - sep_apply (PtrArray.full_to_seg p live row_ptrs).
    sep_apply (PtrArray.seg_single p live newp).
    sep_apply (PtrArray.seg_merge_to_full p 0 live (live + 1)); try lia.
    (* arch-agnostic: p + 0 * sizeA = p for any element size *)
    rewrite Z.mul_0_l, Z.add_0_r.
    replace (live + 1 - 0) with (live + 1) by lia.
    cancel.
    assert (Hlen : List.length row_ptrs = List.length rows).
    { apply Nat2Z.inj.
      rewrite <- !Zlength_correct.
      lia. }
    unfold IntPtrArray2.row_blocks.
    rewrite (combine_app row_ptrs [newp] rows [row] Hlen).
    rewrite map_app.
    rewrite <- derivable1_sepcon_iter_sepcon1.
    unfold IntPtrArray2.row_block.
    change (IntArray.full newp (Zlength row) row)
      with (IntPtrArray2.ElemArray.full newp (Zlength row) row).
    sep_apply (IntPtrArray2.single_to_iter_sepcon
      (IntPtrArray2.ElemArray.full newp (Zlength row) row)).
    simpl map.
    simpl combine.
    entailer!.
Qed.

Lemma installed_row_focus_split : forall p live i rows,
  0 <= i < live ->
  IntPtrArray2.full p live rows |--
  EX row_ptr, installed_row_focus_rep p live i row_ptr rows.
Proof.
  intros p live i rows Hi.
  unfold installed_row_focus_rep.
  apply IntPtrArray2.full_split_to_missing_i.
  exact Hi.
Qed.

Lemma installed_row_focus_merge : forall p live i row_ptr rows,
  0 <= i < live ->
  installed_row_focus_rep p live i row_ptr rows |--
  IntPtrArray2.full p live rows.
Proof.
  intros p live i row_ptr rows Hi.
  unfold installed_row_focus_rep.
  change (IntArray.full row_ptr
    (Zlength (Znth i rows [])) (Znth i rows [])) with
    (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows [])) (Znth i rows [])).
  sep_apply (IntPtrArray2.missing_i_merge_to_full
    p i live row_ptr rows (Znth i rows []) Hi).
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.

(** ===== Public solver-contract bridges =====

    The same genre as the four array-bundle lemmas above, one layer up: for
    each contract predicate, [_elim] takes the folded form to the expansion and
    [_intro] takes the expansion back to the folded form.  Together they say
    that the compact three-result contract claims exactly what the old
    eighty-two-line one claimed -- no more (soundness) and no less (utility).

    Only one of the sixteen has semantic content; the rest are definitional
    shuffles.  That one is [solver_input_core_intro], whose [-1] cell facts are
    *derived* from the entry hypotheses rather than assumed -- see
    [all_unassigned_cells_from_fresh] immediately below.  So folding the entry
    state does not strengthen the precondition.

    Two facts about these proofs worth keeping.  First, [entailer!] closing a
    goal does not by itself establish that the pure conjuncts were needed: it is
    powerful enough to close a goal without using hypotheses one believes are
    load-bearing.  So each of these bridges was checked against a negative
    control -- the pure hypothesis deleted and the whole thing wrapped in
    [Fail solve [...]] -- before being written here, and it is those controls,
    not the green, that show the pure conjuncts carry weight.  Second, [entailer!] alpha-renames a
    surface binder, so [sat_arm_bridge_elim] needs a bare [subst] -- [subst J]
    fails with [No such hypothesis: J]. *)

(** The whole soundness argument for folding the entry state.  Chain: conjunct
    5 of [fresh_formula] gives [assignment a x = None]; [cdcl_view_of_snapshot]
    makes that [snapshot_assignment]; under the range guard that is
    [decode_value_cell (Znth x (snap_values snap) (-1))], which is [None] for
    [-1] or for anything outside [{-1,0,1}]; [snapshot_cells_wf] (inside
    [coherent_snapshot]) rules out the second case; and its sentinel conjunct
    then delivers the level and reason cells. *)
Lemma all_unassigned_cells_from_fresh :
  forall F n live original_count snap ranks,
    coherent_snapshot F n live original_count snap ->
    fresh_formula F n original_count
      (cdcl_view_of_snapshot n snap ranks 0) ->
    all_unassigned_cells n snap.
Proof.
  intros F n live original_count snap ranks Hcoh Hfresh.
  destruct Hcoh as (_ & _ & _ & Hcells & _ & _).
  destruct Hcells as (Hcells & _).
  destruct Hfresh as (_ & _ & _ & _ & Hunassigned & _).
  intros x Hx.
  specialize (Hcells x Hx).
  specialize (Hunassigned x Hx).
  destruct Hunassigned as (Hassign & _ & _ & _).
  cbn in Hassign.
  unfold snapshot_assignment in Hassign.
  destruct Hx as [Hx0 Hxn].
  replace ((0 <=? x) && (x <? n))%bool with true in Hassign
    by (symmetry; apply andb_true_intro; split;
        [apply Z.leb_le | apply Z.ltb_lt]; lia).
  unfold decode_value_cell in Hassign.
  cbn in Hcells.
  destruct Hcells as (Hv & Hd & _).
  destruct Hv as [Hv | [Hv | Hv]].
  - rewrite Hv. destruct (Hd Hv) as (Hd1 & Hr1). rewrite Hd1, Hr1. auto.
  - rewrite Hv in Hassign. cbn in Hassign. discriminate.
  - rewrite Hv in Hassign. cbn in Hassign. discriminate.
Qed.

(** The four components.  [uninitialized_Assignment_intro] takes the cell facts
    as a hypothesis: they are not recoverable from the arrays alone, and the
    entry core is where they get discharged. *)

Lemma store_cnf_elim :
  forall F n original_count states true_counts unassigned row_table live cap snap,
    store_cnf F n original_count states true_counts unassigned row_table
      live cap snap
    |-- “ coherent_snapshot F n live original_count snap ” &&
        solver_arrays_rep states true_counts unassigned row_table live cap snap.
Proof. intros. unfold store_cnf. entailer!. Qed.

Lemma store_cnf_intro :
  forall F n original_count states true_counts unassigned row_table live cap snap,
    coherent_snapshot F n live original_count snap ->
    solver_arrays_rep states true_counts unassigned row_table live cap snap
    |-- store_cnf F n original_count states true_counts unassigned row_table
          live cap snap.
Proof. intros. unfold store_cnf. entailer!. Qed.

Lemma unconstrained_Assignment_elim :
  forall values reasons levels n snap,
    unconstrained_Assignment values reasons levels n snap
    |-- variable_arrays_rep values reasons levels n snap.
Proof. intros. unfold unconstrained_Assignment. entailer!. Qed.

Lemma unconstrained_Assignment_intro :
  forall values reasons levels n snap,
    variable_arrays_rep values reasons levels n snap
    |-- unconstrained_Assignment values reasons levels n snap.
Proof. intros. unfold unconstrained_Assignment. entailer!. Qed.

Lemma store_Assignment_elim :
  forall values reasons levels n snap J,
    store_Assignment values reasons levels n snap J
    |-- “ J = rho_of_values n (snap_values snap) ” &&
        variable_arrays_rep values reasons levels n snap.
Proof. intros. unfold store_Assignment. entailer!. Qed.

Lemma store_Assignment_intro :
  forall values reasons levels n snap J,
    J = rho_of_values n (snap_values snap) ->
    variable_arrays_rep values reasons levels n snap
    |-- store_Assignment values reasons levels n snap J.
Proof. intros. unfold store_Assignment. entailer!. Qed.

Lemma uninitialized_Assignment_elim :
  forall values reasons levels n snap,
    uninitialized_Assignment values reasons levels n snap
    |-- variable_arrays_rep values reasons levels n snap.
Proof. intros. unfold uninitialized_Assignment. entailer!. Qed.

Lemma uninitialized_Assignment_intro :
  forall values reasons levels n snap,
    all_unassigned_cells n snap ->
    variable_arrays_rep values reasons levels n snap
    |-- uninitialized_Assignment values reasons levels n snap.
Proof. intros. unfold uninitialized_Assignment. entailer!. Qed.

(** The entry state.  [_intro] is the direction that carries the derivation:
    its conclusion asserts the [-1] cells, and nothing in its hypotheses does. *)

Lemma solver_input_core_intro :
  forall s F original_count snap ranks values reasons levels
         states true_counts unassigned row_table n live cap v_data cl_data,
    0 <= n -> n < INT_MAX ->
    0 <= original_count -> original_count = live ->
    0 <= live -> live <= cap ->
    coherent_snapshot F n live original_count snap ->
    stable_search_facts n snap ranks 0 ->
    fresh_formula F n original_count
      (cdcl_view_of_snapshot n snap ranks 0) ->
    sat_entry_header_rep s n live cap v_data cl_data **
    var_header_rep v_data values reasons levels **
    clause_header_rep cl_data states true_counts unassigned row_table **
    variable_arrays_rep values reasons levels n snap **
    solver_arrays_rep states true_counts unassigned row_table live cap snap
    |-- solver_input_core s F original_count snap ranks values reasons levels
          states true_counts unassigned row_table n live cap.
Proof.
  intros.
  assert (Hun : all_unassigned_cells n snap)
    by (eapply all_unassigned_cells_from_fresh; eauto).
  unfold solver_input_core, store_cnf, uninitialized_Assignment.
  Exists v_data cl_data.
  entailer!.
Qed.

(** [_elim] re-exposes [coherent_snapshot] as a ninth pure conjunct -- it comes
    back out of [store_cnf] -- and simply drops the [-1] cell facts. *)
Lemma solver_input_core_elim :
  forall s F original_count snap ranks values reasons levels
         states true_counts unassigned row_table n live cap,
    solver_input_core s F original_count snap ranks values reasons levels
      states true_counts unassigned row_table n live cap
    |-- EX (v_data cl_data : Z),
        “ 0 <= n /\ n < INT_MAX /\
          0 <= original_count /\ original_count = live /\
          0 <= live /\ live <= cap /\
          coherent_snapshot F n live original_count snap /\
          stable_search_facts n snap ranks 0 /\
          fresh_formula F n original_count
            (cdcl_view_of_snapshot n snap ranks 0) ” &&
        (sat_entry_header_rep s n live cap v_data cl_data **
         var_header_rep v_data values reasons levels **
         clause_header_rep cl_data states true_counts unassigned row_table **
         variable_arrays_rep values reasons levels n snap **
         solver_arrays_rep states true_counts unassigned row_table live cap snap).
Proof.
  intros.
  unfold solver_input_core, store_cnf, uninitialized_Assignment.
  Intros v_data cl_data.
  Exists v_data cl_data.
  entailer!.
Qed.

(** The SAT arm.  [_intro] is also the phase-F repair recipe: "construct the
    stored [J]" is exactly [Exists (rho_of_values n (snap_values final_snap))],
    which is what the existing return proof already establishes. *)

Lemma sat_arm_bridge_intro :
  forall s F original_count snap ranks values reasons levels states
         true_counts unassigned row_table n live cap
         final_snap final_dl final_live v_data cl_data,
    original_count <= final_live -> final_live <= cap ->
    coherent_snapshot F n final_live original_count final_snap ->
    models (rho_of_values n (snap_values final_snap)) F ->
    sat_header_rep s n final_live cap final_dl v_data cl_data **
    var_header_rep v_data values reasons levels **
    clause_header_rep cl_data states true_counts unassigned row_table **
    variable_arrays_rep values reasons levels n final_snap **
    solver_arrays_rep states true_counts unassigned row_table
      final_live cap final_snap
    |-- EX J, “ models J F ” &&
        solver_sat_arm_core s F original_count snap ranks values reasons
          levels states true_counts unassigned row_table n live cap J.
Proof.
  intros.
  Exists (rho_of_values n (snap_values final_snap)).
  unfold solver_sat_arm_core, store_cnf, store_Assignment.
  Exists final_snap final_dl final_live v_data cl_data.
  entailer!.
Qed.

Lemma sat_arm_bridge_elim :
  forall s F original_count snap ranks values reasons levels states
         true_counts unassigned row_table n live cap J,
    models J F ->
    solver_sat_arm_core s F original_count snap ranks values reasons
      levels states true_counts unassigned row_table n live cap J
    |-- EX (final_snap : dense_snapshot) (final_dl final_live v_data cl_data : Z),
        “ original_count <= final_live /\ final_live <= cap /\
          coherent_snapshot F n final_live original_count final_snap /\
          models (rho_of_values n (snap_values final_snap)) F ” &&
        (sat_header_rep s n final_live cap final_dl v_data cl_data **
         var_header_rep v_data values reasons levels **
         clause_header_rep cl_data states true_counts unassigned row_table **
         variable_arrays_rep values reasons levels n final_snap **
         solver_arrays_rep states true_counts unassigned row_table
           final_live cap final_snap).
Proof.
  intros.
  unfold solver_sat_arm_core, store_cnf, store_Assignment.
  Intros final_snap final_dl final_live v_data cl_data.
  Exists final_snap final_dl final_live v_data cl_data.
  entailer!.
  (* bare [subst]: [entailer!] renamed the surface binder [J] to [J0]. *)
  subst. auto.
Qed.

(** The UNSAT arm.  [cnf_unsat] is deliberately NOT part of the core: it stays a
    visible conjunct of the contract's UNSAT disjunct, so a reader sees the
    verdict without unfolding anything, and it is proved at return time by the
    endgame lemmas -- exactly as today.

    [unsat_terminal] is no longer part of the core either, and the difference
    matters: it is the solver's internal certificate, still constructed inside
    the proof on the way to [cnf_unsat], but no longer *published* in the
    postcondition.  The [intro] direction therefore no longer needs it as a
    hypothesis and the [elim] direction can no longer produce it. *)

Lemma unsat_arm_bridge_intro :
  forall s F original_count snap ranks values reasons levels states
         true_counts unassigned row_table n live cap
         final_snap final_dl final_live v_data cl_data,
    original_count <= final_live -> final_live <= cap ->
    coherent_snapshot F n final_live original_count final_snap ->
    sat_header_rep s n final_live cap final_dl v_data cl_data **
    var_header_rep v_data values reasons levels **
    clause_header_rep cl_data states true_counts unassigned row_table **
    variable_arrays_rep values reasons levels n final_snap **
    solver_arrays_rep states true_counts unassigned row_table
      final_live cap final_snap
    |-- solver_unsat_arm_core s F original_count snap ranks values reasons
          levels states true_counts unassigned row_table n live cap.
Proof.
  intros.
  unfold solver_unsat_arm_core, store_cnf, unconstrained_Assignment.
  Exists final_snap final_dl final_live v_data cl_data.
  entailer!.
Qed.

Lemma unsat_arm_bridge_elim :
  forall s F original_count snap ranks values reasons levels states
         true_counts unassigned row_table n live cap,
    solver_unsat_arm_core s F original_count snap ranks values reasons
      levels states true_counts unassigned row_table n live cap
    |-- EX (final_snap : dense_snapshot) (final_dl final_live v_data cl_data : Z),
        “ original_count <= final_live /\ final_live <= cap /\
          coherent_snapshot F n final_live original_count final_snap ” &&
        (sat_header_rep s n final_live cap final_dl v_data cl_data **
         var_header_rep v_data values reasons levels **
         clause_header_rep cl_data states true_counts unassigned row_table **
         variable_arrays_rep values reasons levels n final_snap **
         solver_arrays_rep states true_counts unassigned row_table
           final_live cap final_snap).
Proof.
  intros.
  unfold solver_unsat_arm_core, store_cnf, unconstrained_Assignment.
  Intros final_snap final_dl final_live v_data cl_data.
  Exists final_snap final_dl final_live v_data cl_data.
  entailer!.
Qed.

(** The capacity arm.  Purely definitional in both directions; the six witnesses
    map one-to-one, including the orphan row, which stays a separate
    [IntArray.full] beside the full table because it is a separate allocation.

    There is no arrow-typed witness any more.  [conflict_ranks] existed only to
    feed [stable_search_facts] and the [cdcl_view_of_snapshot] under
    [current_learning_exit_cert]; with those two facts gone from the core it has
    nothing to feed, so it went with them. *)

Lemma capacity_arm_bridge_intro :
  forall s F original_count snap ranks values reasons levels states
         true_counts unassigned row_table n live cap
         conflict_snap conflict_dl row_ptr row v_data cl_data,
    0 < conflict_dl -> conflict_dl <= n ->
    coherent_snapshot F n cap original_count conflict_snap ->
    row_wf n row ->
    sat_header_rep s n cap cap conflict_dl v_data cl_data **
    var_header_rep v_data values reasons levels **
    clause_header_rep cl_data states true_counts unassigned row_table **
    variable_arrays_rep values reasons levels n conflict_snap **
    solver_arrays_rep states true_counts unassigned row_table
      cap cap conflict_snap **
    IntArray.full row_ptr n row
    |-- solver_capacity_exhausted_arm_core s F original_count snap ranks
          values reasons levels states true_counts unassigned row_table
          n live cap.
Proof.
  intros.
  unfold solver_capacity_exhausted_arm_core, store_cnf,
         unconstrained_Assignment.
  Exists conflict_snap conflict_dl row_ptr row v_data cl_data.
  entailer!.
Qed.

Lemma capacity_arm_bridge_elim :
  forall s F original_count snap ranks values reasons levels states
         true_counts unassigned row_table n live cap,
    solver_capacity_exhausted_arm_core s F original_count snap ranks
      values reasons levels states true_counts unassigned row_table
      n live cap
    |-- EX (conflict_snap : dense_snapshot)
           (conflict_dl row_ptr : Z) (row : list Z) (v_data cl_data : Z),
        “ 0 < conflict_dl /\ conflict_dl <= n /\
          coherent_snapshot F n cap original_count conflict_snap /\
          row_wf n row ” &&
        (sat_header_rep s n cap cap conflict_dl v_data cl_data **
         var_header_rep v_data values reasons levels **
         clause_header_rep cl_data states true_counts unassigned row_table **
         variable_arrays_rep values reasons levels n conflict_snap **
         solver_arrays_rep states true_counts unassigned row_table
           cap cap conflict_snap **
         IntArray.full row_ptr n row).
Proof.
  intros.
  unfold solver_capacity_exhausted_arm_core, store_cnf,
         unconstrained_Assignment.
  Intros conflict_snap conflict_dl row_ptr row v_data cl_data.
  Exists conflict_snap conflict_dl row_ptr row v_data cl_data.
  entailer!.
Qed.

(** Support for the capacity arm's "asserts nothing about F" claim: the two
    verdicts are mutually exclusive, so exhibiting one instance of each that
    satisfies the arm's pure skeleton shows the skeleton entails neither. *)
Lemma cnf_sat_not_cnf_unsat :
  forall n F, cnf_sat n F -> ~ cnf_unsat n F.
Proof.
  intros n F (_ & J & Hb & Hm) (_ & Hall).
  exact (Hall J Hb Hm).
Qed.

Lemma dense_cancel_cell_complementary : forall a b,
  (a = 1 /\ b = -1) \/ (a = -1 /\ b = 1) ->
  dense_cancel_cell a b = 0.
Proof.
  intros a b [[-> ->]|[-> ->]]; reflexivity.
Qed.

Lemma dense_cancel_cell_left_zero : forall b,
  dense_cancel_cell 0 b = b.
Proof. intros; reflexivity. Qed.

Lemma dense_cancel_cell_left_nonzero : forall a b,
  a <> 0 ->
  ~ ((a = 1 /\ b = -1) \/ (a = -1 /\ b = 1)) ->
  dense_cancel_cell a b = a.
Proof.
  intros a b Ha Hcomp.
  unfold dense_cancel_cell.
  destruct (orb (andb (a =? 1) (b =? -1)) (andb (a =? -1) (b =? 1)))
    eqn:Hc.
  - apply orb_true_iff in Hc; destruct Hc as [Hc|Hc];
      apply andb_true_iff in Hc; destruct Hc as [Ha' Hb'];
      apply Z.eqb_eq in Ha'; apply Z.eqb_eq in Hb'; exfalso; apply Hcomp; auto.
  - destruct (a =? 0) eqn:Ha0.
    + apply Z.eqb_eq in Ha0; contradiction.
    + reflexivity.
Qed.

Lemma dense_cancel_cell_domain : forall a b,
  (a = -1 \/ a = 0 \/ a = 1) ->
  (b = -1 \/ b = 0 \/ b = 1) ->
  dense_cancel_cell a b = -1 \/
  dense_cancel_cell a b = 0 \/
  dense_cancel_cell a b = 1.
Proof.
  intros a b Ha Hb.
  destruct Ha as [Ha|[Ha|Ha]]; destruct Hb as [Hb|[Hb|Hb]];
    subst a; subst b; simpl; auto.
Qed.

(** ===== Decidability, in place of classical logic =====

    Every case split in this development that once used [classic] was over a
    property of a *finite list of literals*, and each such property is
    decidable.  Discharging them constructively is what keeps the endgame
    axiom-free: [root_conflict_implies_cnf_unsat], [entails_empty_cnf_unsat],
    [root_assignment_agrees] and [model_ready_models_original] are all closed
    under the global context, so both UNSAT routes and the SAT verdict rest on
    no logical axiom.

    [Coq.Logic.Classical_Prop] is deliberately NOT imported.  Please keep it
    that way: if a new proof wants a case split, add a decision procedure here
    rather than reaching for [classic]. *)

Definition literal_eq_dec (l1 l2 : literal) : {l1 = l2} + {l1 <> l2}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* Proved by induction rather than via List.In_dec on purpose: AUXLib.ListLib
   (ListLib.v:55) shadows In_dec with a typeclass-based version whose first
   explicit argument is the element, so the stdlib spelling does not typecheck
   here.  Five self-contained lines beat depending on which In_dec is in scope. *)
Lemma clause_mem_dec :
  forall (l : literal) (c : clause), {In l c} + {~ In l c}.
Proof.
  intros l c. induction c as [|a c IH].
  - right. intros Hin. contradiction.
  - destruct (literal_eq_dec a l) as [Heq|Hne].
    + left. left. exact Heq.
    + destruct IH as [Hin|Hnin].
      * left. right. exact Hin.
      * right. intros [Ha|Hin]; [exact (Hne Ha)|exact (Hnin Hin)].
Qed.

Lemma clause_var_occurs_dec :
  forall (c : clause) (x : Z),
    {exists l, In l c /\ literal_var l = x} +
    {~ exists l, In l c /\ literal_var l = x}.
Proof.
  induction c as [|l c IH]; intros x.
  - right. intros [l' [Hin _]]. contradiction.
  - destruct (Z.eq_dec (literal_var l) x) as [Heq|Hne].
    + left. exists l. split; [left; reflexivity|exact Heq].
    + destruct (IH x) as [Hyes|Hno].
      * left. destruct Hyes as [l' [Hin Hvar]].
        exists l'. split; [right; exact Hin|exact Hvar].
      * right. intros [l' [Hin Hvar]].
        destruct Hin as [Heql|Hin'].
        -- rewrite <- Heql in Hvar. exact (Hne Hvar).
        -- exact (Hno (ex_intro _ l' (conj Hin' Hvar))).
Qed.

(** ===== SEED CANDIDATES — generic list lemmas, future ListLib promotion targets ===== *)
(* promotion target: ListLib/Forall.v *)
Lemma Forall_Znth_elim :
  forall (A : Type) (P : A -> Prop) (l : list A) (d : A) i,
    Forall P l -> 0 <= i < Zlength l -> P (Znth i l d).
Proof.
  intros A P l; induction l as [|a l IH]; intros d i Hall Hi.
  - rewrite Zlength_nil in Hi; lia.
  - inversion Hall as [|? ? Ha Htail]; subst.
    rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons; exact Ha.
    + rewrite Znth_cons by lia.
      apply IH; [exact Htail|lia].
Qed.
(* promotion target: ListLib/Length.v *)
Lemma Znth_In :
  forall (A : Type) (l : list A) (d : A) i,
    0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros A l; induction l as [|a l IH]; intros d i Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons; left; reflexivity.
    + rewrite Znth_cons by lia; right; apply IH; lia.
Qed.
(* promotion target: ListLib/Base/Positional.v *)
Lemma Znth_map :
  forall (A B : Type) (f : A -> B) (l : list A) (i : Z) (da : A) (db : B),
    0 <= i < Zlength l ->
    Znth i (List.map f l) db = f (Znth i l da).
Proof.
  intros A B f l; induction l as [|x xs IH]; intros i da db Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    cbn [List.map].
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + repeat rewrite Znth0_cons. reflexivity.
    + repeat rewrite Znth_cons by lia.
      apply IH. lia.
Qed.
Lemma replace_Znth_replace_Znth_Same :
  forall (A : Type) (l : list A) i a b,
  0 <= i ->
  replace_Znth i b (replace_Znth i a l) = replace_Znth i b l.
Proof.
  intros A l. induction l as [|z l IH]; intros i a b Hi.
  - reflexivity.
  - destruct (Z.eq_dec i 0) as [->|Hi0].
    + reflexivity.
    + rewrite !replace_Znth_cons by lia.
      f_equal. apply IH. lia.
Qed.
(* promotion target: ListLib/NoDup.v *)
Lemma NoDup_Z_bounded_length : forall xs n,
  0 <= n ->
  NoDup xs ->
  (forall x, In x xs -> 0 <= x < n) ->
  Z.of_nat (List.length xs) <= n.
Proof.
  intros xs n Hn Hnodup Hbounded.
  assert (Hmap_nodup : NoDup (map Z.to_nat xs)).
  {
    induction xs as [|x xs IH]; simpl.
    - constructor.
    - inversion Hnodup as [|? ? Hnotin Htail]; subst.
      constructor.
      + intro Hin.
        apply in_map_iff in Hin.
        destruct Hin as [y [Heq Hyin]].
        apply Hnotin.
        assert (Hx0 : 0 <= x) by
          (pose proof (Hbounded x (or_introl eq_refl)); lia).
        assert (Hy0 : 0 <= y) by
          (pose proof (Hbounded y (or_intror Hyin)); lia).
        apply Z2Nat.inj in Heq; try assumption.
        subst y. exact Hyin.
      + apply IH.
        * exact Htail.
        * intros y Hy. apply Hbounded. right. exact Hy.
  }
  assert (Hincl : incl (map Z.to_nat xs) (seq 0 (Z.to_nat n))).
  {
    intros k Hkin.
    apply in_map_iff in Hkin.
    destruct Hkin as [x [<- Hxin]].
    apply in_seq.
    pose proof (Hbounded x Hxin) as [Hx0 Hxn].
    split; [lia|].
    apply Z2Nat.inj_lt; lia.
  }
  pose proof (NoDup_incl_length Hmap_nodup Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen.
  apply Nat2Z.inj_le in Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  exact Hlen.
Qed.
(** ===== group: dense_array_prefix_kernels ===== *)
Lemma Zlength_repeat_Z__dense_array_prefix_kernels : forall (v k : Z),
  0 <= k ->
  Zlength (repeat_Z v k) = k.
Proof.
  intros v k Hk.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length, Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma Zlength_dense_cancel_union__dense_array_prefix_kernels : forall left right,
  Zlength left = Zlength right ->
  Zlength (dense_cancel_union left right) = Zlength left.
Proof.
  intros left right Heq.
  unfold dense_cancel_union.
  rewrite !Zlength_correct, length_map, length_combine.
  rewrite !Zlength_correct in Heq.
  lia.
Qed.
Lemma Znth_dense_cancel_union__dense_array_prefix_kernels : forall left right i,
  Zlength left = Zlength right ->
  0 <= i < Zlength left ->
  Znth i (dense_cancel_union left right) 0 =
  dense_cancel_cell (Znth i left 0) (Znth i right 0).
Proof.
  intros left right; revert left.
  induction right as [|b right IH]; intros left i Heq Hi.
  - rewrite Zlength_nil in Heq.
    rewrite Heq in Hi. lia.
  - destruct left as [|a left].
    + rewrite Zlength_nil in Heq.
      pose proof (Zlength_nonneg right) as Hnn.
      rewrite Zlength_cons in Heq. lia.
    + rewrite !Zlength_cons in Heq.
      rewrite !Zlength_cons in Hi.
      unfold dense_cancel_union in *.
      cbn [combine map].
      destruct (Z.eq_dec i 0) as [->|Hne].
      * rewrite !Znth0_cons. reflexivity.
      * rewrite !Znth_cons by lia.
        apply IH; lia.
Qed.
Lemma dense_cancel_union_row_wf__dense_array_prefix_kernels : forall n left right,
  row_wf n left -> row_wf n right -> row_wf n (dense_cancel_union left right).
Proof.
  intros n left right [Hlenl Hdoml] [Hlenr Hdomr].
  split.
  - rewrite Zlength_dense_cancel_union__dense_array_prefix_kernels by congruence.
    exact Hlenl.
  - apply Forall_forall.
    intros x Hx.
    unfold dense_cancel_union in Hx.
    apply in_map_iff in Hx.
    destruct Hx as [[a b] [Heqx Hin]].
    simpl in Heqx.
    subst x.
    apply dense_cancel_cell_domain.
    + eapply Forall_forall in Hdoml; [exact Hdoml | eapply in_combine_l; eauto].
    + eapply Forall_forall in Hdomr; [exact Hdomr | eapply in_combine_r; eauto].
Qed.
Lemma resolution_prefix_advance__dense_array_prefix_kernels :
  forall left right out i v,
    i < Zlength left ->
    v = dense_cancel_cell (Znth i left 0) (Znth i right 0) ->
    resolution_prefix left right out i ->
    resolution_prefix left right (replace_Znth i v out) (i + 1).
Proof.
  intros left right out i v Hi Hv HP.
  unfold resolution_prefix in *.
  destruct HP as [Hb [Hlo [Hro [Hpre Htail]]]].
  pose proof (Zlength_replace_Znth out i v) as Hzr.
  repeat split; try lia.
  - intros k Hk.
    destruct (Z.eq_dec k i) as [->|Hne].
    + rewrite Znth_replace_Znth_Same by lia. exact Hv.
    + rewrite Znth_replace_Znth_Diff by lia. apply Hpre. lia.
  - intros k Hk.
    rewrite Znth_replace_Znth_Diff by lia. apply Htail. lia.
Qed.
(** ===== group: learning_row_and_scan ===== *)
Lemma coherent_snapshot_row_wf__learning_row_and_scan :
  forall F n live original_count snap i,
    coherent_snapshot F n live original_count snap ->
    0 <= i < live ->
    row_wf n (Znth i (snap_rows snap) nil).
Proof.
  intros F n live original_count snap i Hcoh Hi.
  unfold coherent_snapshot in Hcoh.
  destruct Hcoh as [_ [_ [Hlens [Hcells [_ _]]]]].
  unfold snapshot_lengths in Hlens.
  destruct Hlens as [_ [_ [_ [Hrowslen _]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [_ Hrows].
  rewrite Forall_forall in Hrows.
  apply Hrows.
  unfold Znth.
  apply nth_In.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct, Hrowslen.
  lia.
Qed.
Lemma snapshot_reason_bounds__learning_row_and_scan :
  forall F n live original_count snap x,
    coherent_snapshot F n live original_count snap ->
    var_in_range n x ->
    Znth x (snap_reasons snap) 0 <> -1 ->
    0 <= Znth x (snap_reasons snap) 0 < live.
Proof.
  intros F n live original_count snap x Hcoh Hx Hr.
  unfold coherent_snapshot in Hcoh.
  destruct Hcoh as [_ [_ [Hlens [Hcells _]]]].
  unfold snapshot_lengths in Hlens.
  destruct Hlens as [_ [Hreasons _]].
  rewrite (Znth_indep (snap_reasons snap) x 0 (-1)) in Hr |- *
    by (rewrite Hreasons; exact Hx).
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [Hvars _].
  specialize (Hvars x Hx).
  cbn in Hvars.
  destruct Hvars as [_ [Hnone Hsome]].
  assert (Hv : Znth x (snap_values snap) (-1) <> -1).
  { intro Heq. destruct (Hnone Heq) as [_ HrEq]. contradiction. }
  specialize (Hsome Hv).
  destruct Hsome as [_ [Hminus | Hbounds]].
  - contradiction.
  - exact Hbounds.
Qed.
Lemma snapshot_level_cell__learning_row_and_scan :
  forall F n live original_count snap ranks logical_dl x,
    coherent_snapshot F n live original_count snap ->
    var_in_range n x ->
    level_of (cdcl_view_of_snapshot n snap ranks logical_dl) x =
      Some logical_dl ->
    Znth x (snap_levels snap) 0 = logical_dl.
Proof.
  intros F n live original_count snap ranks logical_dl x Hcoh Hx Hlevel.
  unfold cdcl_view_of_snapshot in Hlevel; simpl in Hlevel.
  unfold snapshot_level in Hlevel.
  destruct (snapshot_assignment n snap x) as [b|] eqn:Hassign;
    [|discriminate].
  inversion Hlevel; subst.
  unfold coherent_snapshot in Hcoh.
  destruct Hcoh as [_ [_ [Hlens _]]].
  unfold snapshot_lengths in Hlens.
  destruct Hlens as [_ [_ [Hlevels _]]].
  rewrite <- (Znth_indep (snap_levels snap) x (-1) 0).
  - reflexivity.
  - rewrite Hlevels. exact Hx.
Qed.
Lemma dense_decode_from_var_upper_bound__learning_row_and_scan :
  forall row base l,
    In l (dense_decode_from base row) ->
    literal_var l < base + Zlength row.
Proof.
  induction row as [|z row IH]; intros base l Hin; simpl in Hin.
  - contradiction.
  - destruct ((z =? 1)%Z) eqn:Hz1.
    + destruct Hin as [<- | Hin].
      * simpl. rewrite Zlength_cons. pose proof (Zlength_nonneg row). lia.
      * specialize (IH (base + 1) l Hin).
        rewrite Zlength_cons. lia.
    + destruct ((z =? -1)%Z) eqn:Hzm.
      * destruct Hin as [<- | Hin].
        -- simpl. rewrite Zlength_cons. pose proof (Zlength_nonneg row). lia.
        -- specialize (IH (base + 1) l Hin).
           rewrite Zlength_cons. lia.
      * specialize (IH (base + 1) l Hin).
        rewrite Zlength_cons. lia.
Qed.
Lemma dense_decode_var_range__learning_row_and_scan :
  forall n row l,
    row_wf n row ->
    In l (dense_decode row) ->
    var_in_range n (literal_var l).
Proof.
  intros n row l [Hlen Hdom] Hin.
  unfold dense_decode in Hin.
  split.
  - pose proof (dense_decode_from_var_lower_bound row 0 l Hin).
    lia.
  - pose proof
      (dense_decode_from_var_upper_bound__learning_row_and_scan
        row 0 l Hin).
    rewrite Hlen in H. lia.
Qed.
Lemma dense_decode_unique_var__learning_row_and_scan :
  forall n row l1 l2,
    row_wf n row ->
    In l1 (dense_decode row) ->
    In l2 (dense_decode row) ->
    literal_var l1 = literal_var l2 ->
    l1 = l2.
Proof.
  intros n row [x|x] [y|y] Hwf H1 H2 Hvar; simpl in Hvar; subst y;
    try reflexivity.
  - pose proof
      (dense_decode_var_range__learning_row_and_scan n row (Pos x) Hwf H1)
      as Hx.
    apply (proj2 (dense_decode_pos n row x Hwf Hx)) in H1.
    apply (proj2 (dense_decode_neg n row x Hwf Hx)) in H2.
    lia.
  - pose proof
      (dense_decode_var_range__learning_row_and_scan n row (Neg x) Hwf H1)
      as Hx.
    apply (proj2 (dense_decode_neg n row x Hwf Hx)) in H1.
    apply (proj2 (dense_decode_pos n row x Hwf Hx)) in H2.
    lia.
Qed.
Lemma clause_false_counts__learning_row_and_scan :
  forall sigma c,
    clause_false sigma c ->
    clause_true_count sigma c = 0 /\
    clause_unassigned_count sigma c = 0.
Proof.
  intros sigma c; induction c as [|l c IH]; intro Hfalse.
  - split; reflexivity.
  - assert (Hhead : eval_partial_literal sigma l = Some false).
    { apply Hfalse. left. reflexivity. }
    assert (Htail : clause_false sigma c).
    { intros l' Hin. apply Hfalse. right. exact Hin. }
    specialize (IH Htail).
    simpl. rewrite Hhead. simpl. exact IH.
Qed.
Lemma restrict_current_assigned__learning_row_and_scan :
  forall a x b,
    grounded_at a ->
    closed_levels a ->
    assignment a x = Some b ->
    restrict_to_level a (current_level a) x = Some b.
Proof.
  intros a x b Hground Hclosed Hassign.
  specialize (Hground x b Hassign).
  destruct Hground as [d [rx [Hlevel [Hrank Hwhy]]]].
  destruct Hclosed as [Hcur [Hbounds Hrest]].
  specialize (Hbounds x b d Hassign Hlevel).
  unfold restrict_to_level.
  rewrite Hassign, Hlevel.
  destruct ((d <=? current_level a)%Z) eqn:Hle.
  - reflexivity.
  - apply Z.leb_gt in Hle. lia.
Qed.
Lemma clause_false_restrict_current__learning_row_and_scan :
  forall a c,
    grounded_at a ->
    closed_levels a ->
    clause_false (assignment a) c ->
    clause_false (restrict_to_level a (current_level a)) c.
Proof.
  intros a c Hground Hclosed Hfalse l Hin.
  specialize (Hfalse l Hin).
  destruct l as [x|x]; unfold eval_partial_literal in *; simpl in *;
    destruct (assignment a x) as [b|] eqn:Hassign; try discriminate;
    rewrite (restrict_current_assigned__learning_row_and_scan
      a x b Hground Hclosed Hassign);
    exact Hfalse.
Qed.
Lemma conflict_current_support__learning_row_and_scan :
  forall a c,
    grounded_at a ->
    closed_levels a ->
    frontier_closed a ->
    0 < current_level a ->
    In c (installed_clauses a) ->
    clause_false (assignment a) c ->
    current_level_support a c.
Proof.
  intros a c Hground Hclosed Hfront Hdl Hin Hfalse.
  destruct Hfront as [_ Hcurrent].
  destruct Hcurrent as [Hzero | Hcurrent]; [lia|].
  assert (Hfalse_restrict :
    clause_false (restrict_to_level a (current_level a)) c).
  { apply clause_false_restrict_current__learning_row_and_scan; assumption. }
  pose proof
    (clause_false_counts__learning_row_and_scan
      (restrict_to_level a (current_level a)) c Hfalse_restrict)
    as [Htrue Hunassigned].
  assert (Hactive :
    active_frontier_clause (restrict_to_level a (current_level a)) c).
  { unfold active_frontier_clause. lia. }
  specialize (Hcurrent c Hin Hactive).
  destruct Hcurrent as [l [Hlit [Heval Hlevel]]].
  exists l. split; [exact Hlit|].
  unfold current_level_literal. exact Hlevel.
Qed.
Lemma installed_clause_entails__learning_row_and_scan :
  forall F original_count installed j c,
    installed_clauses_sound F original_count installed ->
    nth_error installed j = Some c ->
    entails_clause F c.
Proof.
  intros F original_count installed j c Hsound Hnth.
  destruct Hsound as [[Hprefix [Hcount Hnonempty]] Hlearned].
  assert (HallF : Forall (entails_clause F) F).
  { apply Forall_forall. intros c' Hc' rho Hmodels.
    unfold models in Hmodels.
    rewrite Forall_forall in Hmodels.
    apply Hmodels. exact Hc'. }
  assert (HallInstalled : Forall (entails_clause F) installed).
  { rewrite <- (firstn_skipn (Z.to_nat original_count) installed).
    apply Forall_app. split.
    - rewrite Hprefix. exact HallF.
    - exact Hlearned. }
  rewrite Forall_forall in HallInstalled.
  apply HallInstalled.
  eapply nth_error_In; eauto.
Qed.
Lemma snapshot_installed_row_at__learning_row_and_scan :
  forall n snap ranks logical_dl live i,
    snapshot_lengths n live snap ->
    0 <= i < live ->
    nth_error
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl))
      (Z.to_nat i) =
      Some (dense_decode (Znth i (snap_rows snap) nil)).
Proof.
  intros n snap ranks logical_dl live i Hlens Hi.
  unfold cdcl_view_of_snapshot; simpl.
  rewrite nth_error_map.
  unfold snapshot_lengths in Hlens.
  destruct Hlens as [_ [_ [_ [Hrows _]]]].
  assert (Hnat : (Z.to_nat i < List.length (snap_rows snap))%nat).
  { apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct, Hrows.
    lia. }
  rewrite (@nth_error_nth' (list Z) (snap_rows snap) (Z.to_nat i) nil Hnat).
  reflexivity.
Qed.
Lemma installed_conflict_learning_seed__learning_row_and_scan :
  forall F n live original_count snap ranks logical_dl wi c,
    0 < logical_dl ->
    0 <= wi < live ->
    coherent_snapshot F n live original_count snap ->
    stable_search_facts n snap ranks logical_dl ->
    nth_error
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl))
      (Z.to_nat wi) = Some c ->
    clause_false
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl)) c ->
    let row := Znth wi (snap_rows snap) nil in
    row_wf n row /\
    entails_clause F (dense_decode row) /\
    clause_false
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (dense_decode row) /\
    (dense_decode row = nil \/
      current_level_support
        (cdcl_view_of_snapshot n snap ranks logical_dl)
        (dense_decode row)).
Proof.
  intros F n live original_count snap ranks logical_dl wi c
    Hdl Hwi Hcoh Hstable Hnth Hfalse.
  pose proof
    (coherent_snapshot_row_wf__learning_row_and_scan
      F n live original_count snap wi Hcoh Hwi) as Hrowwf.
  unfold coherent_snapshot in Hcoh.
  destruct Hcoh as [_ [_ [Hlens [_ [_ Hsound]]]]].
  pose proof
    (snapshot_installed_row_at__learning_row_and_scan
      n snap ranks logical_dl live wi Hlens Hwi) as Hrowat.
  assert (Hceq : c = dense_decode (Znth wi (snap_rows snap) nil)).
  { rewrite Hnth in Hrowat. inversion Hrowat. reflexivity. }
  subst c.
  assert (Hentails : entails_clause F
    (dense_decode (Znth wi (snap_rows snap) nil))).
  { eapply installed_clause_entails__learning_row_and_scan; eauto. }
  unfold stable_search_facts in Hstable; simpl in Hstable.
  destruct Hstable as [Hground [Hclosed Hfront]].
  assert (Hin : In (dense_decode (Znth wi (snap_rows snap) nil))
    (installed_clauses
      (cdcl_view_of_snapshot n snap ranks logical_dl))).
  { eapply nth_error_In; eauto. }
  assert (Hsupport : current_level_support
    (cdcl_view_of_snapshot n snap ranks logical_dl)
    (dense_decode (Znth wi (snap_rows snap) nil))).
  { eapply conflict_current_support__learning_row_and_scan; eauto. }
  split; [exact Hrowwf|].
  split; [exact Hentails|].
  split; [exact Hfalse|].
  right. exact Hsupport.
Qed.
Lemma snapshot_reason_none_from_cell__learning_row_and_scan :
  forall F n live original_count snap ranks logical_dl x,
    coherent_snapshot F n live original_count snap ->
    var_in_range n x ->
    Znth x (snap_reasons snap) 0 = -1 ->
    reason_of (cdcl_view_of_snapshot n snap ranks logical_dl) x = None.
Proof.
  intros F n live original_count snap ranks logical_dl x Hcoh Hx Hcell.
  unfold cdcl_view_of_snapshot; simpl.
  unfold snapshot_reason.
  destruct (snapshot_assignment n snap x) as [b|] eqn:Hassign;
    [|reflexivity].
  unfold coherent_snapshot in Hcoh.
  destruct Hcoh as [_ [_ [Hlens _]]].
  unfold snapshot_lengths in Hlens.
  destruct Hlens as [_ [Hreasons _]].
  rewrite (Znth_indep (snap_reasons snap) x (-1) 0)
    by (rewrite Hreasons; exact Hx).
  rewrite Hcell. reflexivity.
Qed.
Lemma learning_loop_scan_advance__learning_row_and_scan :
  forall F a n row scan,
    0 <= scan < n ->
    (Znth scan row 0 = 0 \/
      level_of a scan <> Some (current_level a) \/
      reason_of a scan = None) ->
    learning_loop F a n row scan ->
    learning_loop F a n row (scan + 1).
Proof.
  intros F a n row scan Hscan Hskip Hpre.
  unfold learning_loop in *. cbv zeta in *.
  destruct Hpre as [Hwf [Hentails [Hfalse [Hsupport [Hrange Hold]]]]].
  split; [exact Hwf|].
  split; [exact Hentails|].
  split; [exact Hfalse|].
  split; [exact Hsupport|].
  split; [lia|].
  intros x Hx Hnonzero Hlevel.
  destruct (Z_lt_ge_dec x scan) as [Hlt | Hge].
  - eapply Hold; eauto. lia.
  - assert (x = scan) by lia. subst x.
    destruct Hskip as [Hzero | [Hnotlevel | Hnone]].
    + contradiction.
    + contradiction.
    + exact Hnone.
Qed.
Lemma dense_decode_cell_nonzero__learning_row_and_scan :
  forall n row l,
    row_wf n row ->
    In l (dense_decode row) ->
    Znth (literal_var l) row 0 <> 0.
Proof.
  intros n row [x|x] Hwf Hin Hzero.
  - pose proof
      (dense_decode_var_range__learning_row_and_scan
        n row (Pos x) Hwf Hin) as Hx.
    apply (proj2 (dense_decode_pos n row x Hwf Hx)) in Hin.
    simpl in Hzero. lia.
  - pose proof
      (dense_decode_var_range__learning_row_and_scan
        n row (Neg x) Hwf Hin) as Hx.
    apply (proj2 (dense_decode_neg n row x Hwf Hx)) in Hin.
    simpl in Hzero. lia.
Qed.
Lemma learning_loop_exit_cert__learning_row_and_scan :
  forall F a n row,
    row_wf n row ->
    entails_clause F (dense_decode row) ->
    clause_false (assignment a) (dense_decode row) ->
    (dense_decode row = nil \/
      current_level_support a (dense_decode row)) ->
    (forall x,
      0 <= x < n ->
      Znth x row 0 <> 0 ->
      level_of a x = Some (current_level a) ->
      reason_of a x = None) ->
    current_learning_exit_cert F a (dense_decode row).
Proof.
  intros F a n row Hwf Hentails Hfalse Hsupport Hprocessed.
  unfold current_learning_exit_cert, learned_clause_sound.
  split; [split; assumption|].
  destruct Hsupport as [Hempty | Hsupport].
  - left. exact Hempty.
  - right. split; [exact Hsupport|].
    intros l Hin Hlevel.
    eapply Hprocessed.
    + apply (dense_decode_var_range__learning_row_and_scan
        n row l Hwf Hin).
    + apply (dense_decode_cell_nonzero__learning_row_and_scan
        n row l Hwf Hin).
    + unfold current_level_literal in Hlevel. exact Hlevel.
Qed.
Lemma dense_cancel_union_Znth__learning_row_and_scan : forall n left right x,
    Zlength left = n -> Zlength right = n -> 0 <= x < n ->
    Znth x (dense_cancel_union left right) 0 =
      dense_cancel_cell (Znth x left 0) (Znth x right 0).
Proof.
  intros n left right x Hleft Hright Hx.
  apply Znth_dense_cancel_union__dense_array_prefix_kernels; [congruence | lia].
Qed.
Lemma dense_cancel_cell_pos_origin__learning_row_and_scan : forall a b,
    (a = -1 \/ a = 0 \/ a = 1) ->
    (b = -1 \/ b = 0 \/ b = 1) ->
    dense_cancel_cell a b = 1 -> a = 1 \/ b = 1.
Proof.
  intros a b Ha Hb Hout.
  destruct Ha as [Ha|[Ha|Ha]]; destruct Hb as [Hb|[Hb|Hb]];
    subst a; subst b; simpl in Hout; auto; discriminate.
Qed.
Lemma dense_cancel_cell_neg_origin__learning_row_and_scan : forall a b,
    (a = -1 \/ a = 0 \/ a = 1) ->
    (b = -1 \/ b = 0 \/ b = 1) ->
    dense_cancel_cell a b = -1 -> a = -1 \/ b = -1.
Proof.
  intros a b Ha Hb Hout.
  destruct Ha as [Ha|[Ha|Ha]]; destruct Hb as [Hb|[Hb|Hb]];
    subst a; subst b; simpl in Hout; auto; discriminate.
Qed.
Lemma dense_cancel_cell_left_pos__learning_row_and_scan : forall b,
    (b = -1 \/ b = 0 \/ b = 1) -> b <> -1 ->
    dense_cancel_cell 1 b = 1.
Proof.
  intros b Hb Hnot.
  destruct Hb as [Hb|[Hb|Hb]]; subst b; simpl;
    contradiction || reflexivity.
Qed.
Lemma dense_cancel_cell_left_neg__learning_row_and_scan : forall b,
    (b = -1 \/ b = 0 \/ b = 1) -> b <> 1 ->
    dense_cancel_cell (-1) b = -1.
Proof.
  intros b Hb Hnot.
  destruct Hb as [Hb|[Hb|Hb]]; subst b; simpl;
    contradiction || reflexivity.
Qed.
Lemma dense_cancel_cell_right_pos__learning_row_and_scan : forall a,
    (a = -1 \/ a = 0 \/ a = 1) -> a <> -1 ->
    dense_cancel_cell a 1 = 1.
Proof.
  intros a Ha Hnot.
  destruct Ha as [Ha|[Ha|Ha]]; subst a; simpl;
    contradiction || reflexivity.
Qed.
Lemma dense_cancel_cell_right_neg__learning_row_and_scan : forall a,
    (a = -1 \/ a = 0 \/ a = 1) -> a <> 1 ->
    dense_cancel_cell a (-1) = -1.
Proof.
  intros a Ha Hnot.
  destruct Ha as [Ha|[Ha|Ha]]; subst a; simpl;
    contradiction || reflexivity.
Qed.
Lemma dense_cancel_union_literal_origin__learning_row_and_scan :
  forall n left right out_wf l,
    row_wf n left -> row_wf n right ->
    out_wf = row_wf n (dense_cancel_union left right) ->
    out_wf -> In l (dense_decode (dense_cancel_union left right)) ->
    In l (dense_decode left) \/ In l (dense_decode right).
Proof.
  intros n left right out_wf l Hleft Hright -> Houtwf Hin.
  pose proof
    (dense_decode_var_range__learning_row_and_scan n
      (dense_cancel_union left right) l Houtwf Hin) as Hx.
  destruct Hleft as [Hllen Hldom].
  destruct Hright as [Hrlen Hrdom].
  destruct l as [x|x]; simpl in Hx.
  - apply (proj2 (dense_decode_pos n _ x Houtwf Hx)) in Hin.
    rewrite (dense_cancel_union_Znth__learning_row_and_scan
      n left right x Hllen Hrlen Hx) in Hin.
    pose proof (row_wf_cell_domain n left x (conj Hllen Hldom) Hx) as Ha.
    pose proof (row_wf_cell_domain n right x (conj Hrlen Hrdom) Hx) as Hb.
    destruct (dense_cancel_cell_pos_origin__learning_row_and_scan
      _ _ Ha Hb Hin) as [Ha1|Hb1].
    + left. apply (proj1 (dense_decode_pos n left x
        (conj Hllen Hldom) Hx)). exact Ha1.
    + right. apply (proj1 (dense_decode_pos n right x
        (conj Hrlen Hrdom) Hx)). exact Hb1.
  - apply (proj2 (dense_decode_neg n _ x Houtwf Hx)) in Hin.
    rewrite (dense_cancel_union_Znth__learning_row_and_scan
      n left right x Hllen Hrlen Hx) in Hin.
    pose proof (row_wf_cell_domain n left x (conj Hllen Hldom) Hx) as Ha.
    pose proof (row_wf_cell_domain n right x (conj Hrlen Hrdom) Hx) as Hb.
    destruct (dense_cancel_cell_neg_origin__learning_row_and_scan
      _ _ Ha Hb Hin) as [Ham|Hbm].
    + left. apply (proj1 (dense_decode_neg n left x
        (conj Hllen Hldom) Hx)). exact Ham.
    + right. apply (proj1 (dense_decode_neg n right x
        (conj Hrlen Hrdom) Hx)). exact Hbm.
Qed.
Lemma dense_cancel_union_left_false_survives__learning_row_and_scan :
  forall n left right sigma l,
    row_wf n left -> row_wf n right ->
    row_wf n (dense_cancel_union left right) ->
    clause_false sigma (dense_decode left) ->
    In l (dense_decode left) ->
    (forall r,
      In r (dense_decode right) ->
      literal_var r = literal_var l ->
      eval_partial_literal sigma r = Some false) ->
    In l (dense_decode (dense_cancel_union left right)).
Proof.
  intros n left right sigma [x|x] Hleft Hright Houtwf
    Hleftfalse Hin Hrightfalse.
  all: pose proof
    (dense_decode_var_range__learning_row_and_scan n left _ Hleft Hin) as Hx.
  - assert (Ha : Znth x left 0 = 1).
    { apply (proj2 (dense_decode_pos n left x Hleft Hx)). exact Hin. }
    assert (Hbnot : Znth x right 0 <> -1).
    { intro Hb.
      pose proof (row_wf_cell_domain n right x Hright Hx) as Hbdomain.
      assert (Hrin : In (Neg x) (dense_decode right)).
      { apply (proj1 (dense_decode_neg n right x Hright Hx)). exact Hb. }
      specialize (Hrightfalse (Neg x) Hrin eq_refl).
      specialize (Hleftfalse (Pos x) Hin).
      unfold eval_partial_literal in Hrightfalse, Hleftfalse; simpl in *.
      destruct (sigma x) as [q|]; simpl in *; try discriminate.
      destruct q; discriminate. }
    apply (proj1 (dense_decode_pos n _ x Houtwf Hx)).
    rewrite (dense_cancel_union_Znth__learning_row_and_scan n left right x
      (proj1 Hleft) (proj1 Hright) Hx), Ha.
    apply dense_cancel_cell_left_pos__learning_row_and_scan.
    + apply (row_wf_cell_domain n right x Hright Hx).
    + exact Hbnot.
  - assert (Ha : Znth x left 0 = -1).
    { apply (proj2 (dense_decode_neg n left x Hleft Hx)). exact Hin. }
    assert (Hbnot : Znth x right 0 <> 1).
    { intro Hb.
      assert (Hrin : In (Pos x) (dense_decode right)).
      { apply (proj1 (dense_decode_pos n right x Hright Hx)). exact Hb. }
      specialize (Hrightfalse (Pos x) Hrin eq_refl).
      specialize (Hleftfalse (Neg x) Hin).
      unfold eval_partial_literal in Hrightfalse, Hleftfalse; simpl in *.
      destruct (sigma x) as [q|]; simpl in *; try discriminate.
      destruct q; discriminate. }
    apply (proj1 (dense_decode_neg n _ x Houtwf Hx)).
    rewrite (dense_cancel_union_Znth__learning_row_and_scan n left right x
      (proj1 Hleft) (proj1 Hright) Hx), Ha.
    apply dense_cancel_cell_left_neg__learning_row_and_scan.
    + apply (row_wf_cell_domain n right x Hright Hx).
    + exact Hbnot.
Qed.
Lemma dense_cancel_union_right_false_survives__learning_row_and_scan :
  forall n left right sigma l,
    row_wf n left -> row_wf n right ->
    row_wf n (dense_cancel_union left right) ->
    clause_false sigma (dense_decode left) ->
    In l (dense_decode right) ->
    eval_partial_literal sigma l = Some false ->
    In l (dense_decode (dense_cancel_union left right)).
Proof.
  intros n left right sigma [x|x] Hleft Hright Houtwf
    Hleftfalse Hin Hlitfalse.
  all: pose proof
    (dense_decode_var_range__learning_row_and_scan n right _ Hright Hin) as Hx.
  - assert (Hb : Znth x right 0 = 1).
    { apply (proj2 (dense_decode_pos n right x Hright Hx)). exact Hin. }
    assert (Hanot : Znth x left 0 <> -1).
    { intro Ha.
      assert (Hlin : In (Neg x) (dense_decode left)).
      { apply (proj1 (dense_decode_neg n left x Hleft Hx)). exact Ha. }
      specialize (Hleftfalse (Neg x) Hlin).
      unfold eval_partial_literal in Hleftfalse, Hlitfalse; simpl in *.
      destruct (sigma x) as [q|]; simpl in *; try discriminate.
      destruct q; discriminate. }
    apply (proj1 (dense_decode_pos n _ x Houtwf Hx)).
    rewrite (dense_cancel_union_Znth__learning_row_and_scan n left right x
      (proj1 Hleft) (proj1 Hright) Hx), Hb.
    apply dense_cancel_cell_right_pos__learning_row_and_scan.
    + apply (row_wf_cell_domain n left x Hleft Hx).
    + exact Hanot.
  - assert (Hb : Znth x right 0 = -1).
    { apply (proj2 (dense_decode_neg n right x Hright Hx)). exact Hin. }
    assert (Hanot : Znth x left 0 <> 1).
    { intro Ha.
      assert (Hlin : In (Pos x) (dense_decode left)).
      { apply (proj1 (dense_decode_pos n left x Hleft Hx)). exact Ha. }
      specialize (Hleftfalse (Pos x) Hlin).
      unfold eval_partial_literal in Hleftfalse, Hlitfalse; simpl in *.
      destruct (sigma x) as [q|]; simpl in *; try discriminate.
      destruct q; discriminate. }
    apply (proj1 (dense_decode_neg n _ x Houtwf Hx)).
    rewrite (dense_cancel_union_Znth__learning_row_and_scan n left right x
      (proj1 Hleft) (proj1 Hright) Hx), Hb.
    apply dense_cancel_cell_right_neg__learning_row_and_scan.
    + apply (row_wf_cell_domain n left x Hleft Hx).
    + exact Hanot.
Qed.
Lemma dense_cancel_union_pivot_zero__learning_row_and_scan :
  forall n left right pivot b,
    row_wf n left -> row_wf n right ->
    In (falsified_literal pivot b) (dense_decode left) ->
    In (satisfying_literal pivot b) (dense_decode right) ->
    Znth pivot (dense_cancel_union left right) 0 = 0.
Proof.
  intros n left right pivot b Hleft Hright Hleftpivot Hrightpivot.
  pose proof
    (dense_decode_var_range__learning_row_and_scan n left
      (falsified_literal pivot b) Hleft Hleftpivot) as Hpivot.
  destruct b.
  - unfold falsified_literal in Hleftpivot.
    unfold satisfying_literal in Hrightpivot.
    apply (proj2 (dense_decode_neg n left pivot Hleft Hpivot)) in Hleftpivot.
    apply (proj2 (dense_decode_pos n right pivot Hright Hpivot)) in Hrightpivot.
    rewrite (dense_cancel_union_Znth__learning_row_and_scan n left right pivot
      (proj1 Hleft) (proj1 Hright) Hpivot), Hleftpivot, Hrightpivot.
    reflexivity.
  - unfold falsified_literal in Hleftpivot.
    unfold satisfying_literal in Hrightpivot.
    apply (proj2 (dense_decode_pos n left pivot Hleft Hpivot)) in Hleftpivot.
    apply (proj2 (dense_decode_neg n right pivot Hright Hpivot)) in Hrightpivot.
    rewrite (dense_cancel_union_Znth__learning_row_and_scan n left right pivot
      (proj1 Hleft) (proj1 Hright) Hpivot), Hleftpivot, Hrightpivot.
    reflexivity.
Qed.
Lemma literal_var_falsified__learning_row_and_scan : forall x b,
  literal_var (falsified_literal x b) = x.
Proof. intros x []; reflexivity. Qed.
Lemma literal_var_satisfying__learning_row_and_scan : forall x b,
  literal_var (satisfying_literal x b) = x.
Proof. intros x []; reflexivity. Qed.
Lemma dense_cancel_resolution_learning__learning_row_and_scan :
  forall F a n left right pivot b,
    row_wf n left ->
    row_wf n right ->
    row_wf n (dense_cancel_union left right) ->
    entails_clause F (dense_decode left) ->
    entails_clause F (dense_decode right) ->
    clause_false (assignment a) (dense_decode left) ->
    In (falsified_literal pivot b) (dense_decode left) ->
    In (satisfying_literal pivot b) (dense_decode right) ->
    (forall l,
      In l (dense_decode right) ->
      literal_var l <> pivot ->
      eval_partial_literal (assignment a) l = Some false) ->
    (forall Hlevel :
      level_of a pivot = Some (current_level a),
      exists l,
        In l (dense_decode right) /\
        literal_var l <> pivot /\
        eval_partial_literal (assignment a) l = Some false /\
        current_level_literal a l) ->
    (dense_decode left = nil \/
      current_level_support a (dense_decode left)) ->
    entails_clause F (dense_decode (dense_cancel_union left right)) /\
    clause_false (assignment a)
      (dense_decode (dense_cancel_union left right)) /\
    (dense_decode (dense_cancel_union left right) = nil \/
      current_level_support a
        (dense_decode (dense_cancel_union left right))).
Proof.
  intros F a n left right pivot b Hleft Hright Houtwf
    Hleftentails Hrightentails Hleftfalse Hleftpivot Hrightpivot
    Hrightother Hpredecessor Hleftsupport.
  assert (Hpivotrange : var_in_range n pivot).
  { pose proof (dense_decode_var_range__learning_row_and_scan n left
      (falsified_literal pivot b) Hleft Hleftpivot) as Hrange.
    rewrite literal_var_falsified__learning_row_and_scan in Hrange.
    exact Hrange. }
  assert (Hpivotzero :
    Znth pivot (dense_cancel_union left right) 0 = 0).
  { eapply dense_cancel_union_pivot_zero__learning_row_and_scan; eauto. }
  split.
  - intros rho Hmodels.
    destruct (Hleftentails rho Hmodels) as [l [Hlin Hlsat]].
    destruct (Z.eq_dec (literal_var l) pivot) as [Hlpivot|Hlother].
    + assert (Hleq : l = falsified_literal pivot b).
      { eapply dense_decode_unique_var__learning_row_and_scan;
          [exact Hleft | exact Hlin | exact Hleftpivot |].
        rewrite literal_var_falsified__learning_row_and_scan. exact Hlpivot. }
      subst l.
      destruct (Hrightentails rho Hmodels) as [r [Hrin Hrsat]].
      destruct (Z.eq_dec (literal_var r) pivot) as [Hrpivot|Hrother].
      * assert (Hreq : r = satisfying_literal pivot b).
        { eapply dense_decode_unique_var__learning_row_and_scan;
            [exact Hright | exact Hrin | exact Hrightpivot |].
          rewrite literal_var_satisfying__learning_row_and_scan. exact Hrpivot. }
        subst r. destruct b; simpl in Hlsat, Hrsat;
          destruct (rho pivot); discriminate.
      * exists r. split; [|exact Hrsat].
        eapply dense_cancel_union_right_false_survives__learning_row_and_scan;
          [exact Hleft | exact Hright | exact Houtwf |
           exact Hleftfalse | exact Hrin |].
        apply Hrightother; assumption.
    + exists l. split; [|exact Hlsat].
      eapply dense_cancel_union_left_false_survives__learning_row_and_scan;
        [exact Hleft | exact Hright | exact Houtwf |
         exact Hleftfalse | exact Hlin |].
      intros r Hrin Hsamevar.
      apply Hrightother; [exact Hrin|].
      intro Hrpivot. apply Hlother.
      rewrite <- Hsamevar. exact Hrpivot.
  - split.
    + intros l Hout.
      destruct (dense_cancel_union_literal_origin__learning_row_and_scan
        n left right (row_wf n (dense_cancel_union left right)) l
        Hleft Hright eq_refl Houtwf Hout) as [Hlin|Hrin].
      * apply Hleftfalse. exact Hlin.
      * destruct (Z.eq_dec (literal_var l) pivot) as [Hlpivot|Hlother].
        -- assert (Hleq : l = satisfying_literal pivot b).
           { eapply dense_decode_unique_var__learning_row_and_scan;
               [exact Hright | exact Hrin | exact Hrightpivot |].
             rewrite literal_var_satisfying__learning_row_and_scan. exact Hlpivot. }
           subst l. destruct b.
           ++ pose proof (proj2 (dense_decode_pos n
                (dense_cancel_union left right) pivot Houtwf Hpivotrange) Hout).
              lia.
           ++ pose proof (proj2 (dense_decode_neg n
                (dense_cancel_union left right) pivot Houtwf Hpivotrange) Hout).
              lia.
        -- apply Hrightother; assumption.
    + destruct Hleftsupport as [Hempty|Hsupport].
      * rewrite Hempty in Hleftpivot. contradiction.
      * destruct Hsupport as [l [Hlin Hlevel]].
        destruct (Z.eq_dec (literal_var l) pivot) as [Hlpivot|Hlother].
        -- assert (Hleq : l = falsified_literal pivot b).
           { eapply dense_decode_unique_var__learning_row_and_scan;
               [exact Hleft | exact Hlin | exact Hleftpivot |].
             rewrite literal_var_falsified__learning_row_and_scan. exact Hlpivot. }
           subst l.
           assert (Hpivotlevel :
             level_of a pivot = Some (current_level a)).
           { unfold current_level_literal in Hlevel.
             rewrite literal_var_falsified__learning_row_and_scan in Hlevel.
             exact Hlevel. }
           destruct (Hpredecessor Hpivotlevel) as
             [r [Hrin [Hrother [Hrfalse Hrlevel]]]].
           right. exists r. split; [|exact Hrlevel].
           eapply dense_cancel_union_right_false_survives__learning_row_and_scan;
             eauto.
        -- right. exists l. split; [|exact Hlevel].
           eapply dense_cancel_union_left_false_survives__learning_row_and_scan;
             [exact Hleft | exact Hright | exact Houtwf |
              exact Hleftfalse | exact Hlin |].
           intros r Hrin Hsamevar.
           apply Hrightother; [exact Hrin|].
           intro Hrpivot. apply Hlother.
           rewrite <- Hsamevar. exact Hrpivot.
Qed.
Lemma false_dense_pivot_assignment__learning_row_and_scan :
  forall a n row x,
    row_wf n row ->
    var_in_range n x ->
    Znth x row 0 <> 0 ->
    clause_false (assignment a) (dense_decode row) ->
    exists b,
      assignment a x = Some b /\
      In (falsified_literal x b) (dense_decode row).
Proof.
  intros a n row x Hwf Hx Hnonzero Hfalse.
  pose proof (row_wf_cell_domain n row x Hwf Hx) as Hcell.
  destruct Hcell as [Hneg|[Hzero|Hpos]]; [|contradiction|].
  - assert (Hin : In (Neg x) (dense_decode row)).
    { apply (proj1 (dense_decode_neg n row x Hwf Hx)). exact Hneg. }
    specialize (Hfalse (Neg x) Hin).
    unfold eval_partial_literal in Hfalse; simpl in Hfalse.
    destruct (assignment a x) as [q|] eqn:Hassign; try discriminate.
    destruct q; [|discriminate].
    exists true. split; [reflexivity|exact Hin].
  - assert (Hin : In (Pos x) (dense_decode row)).
    { apply (proj1 (dense_decode_pos n row x Hwf Hx)). exact Hpos. }
    specialize (Hfalse (Pos x) Hin).
    unfold eval_partial_literal in Hfalse; simpl in Hfalse.
    destruct (assignment a x) as [q|] eqn:Hassign; try discriminate.
    destruct q; [discriminate|].
    exists false. split; [reflexivity|exact Hin].
Qed.
Lemma snapshot_reason_some__learning_row_and_scan :
  forall F n live original_count snap ranks logical_dl x b j,
    coherent_snapshot F n live original_count snap ->
    var_in_range n x ->
    assignment (cdcl_view_of_snapshot n snap ranks logical_dl) x = Some b ->
    j = Znth x (snap_reasons snap) 0 ->
    0 <= j ->
    reason_of (cdcl_view_of_snapshot n snap ranks logical_dl) x = Some j.
Proof.
  intros F n live original_count snap ranks logical_dl x b j
    Hcoh Hx Hassign Hj Hjnonneg.
  change (snapshot_assignment n snap x = Some b) in Hassign.
  change (snapshot_reason n snap x = Some j).
  unfold snapshot_reason. rewrite Hassign.
  unfold coherent_snapshot in Hcoh.
  destruct Hcoh as [_ [_ [Hlens _]]].
  unfold snapshot_lengths in Hlens.
  destruct Hlens as [_ [Hreasons _]].
  rewrite (Znth_indep (snap_reasons snap) x (-1) 0)
    by (rewrite Hreasons; exact Hx).
  rewrite <- Hj.
  destruct ((j =? -1)%Z) eqn:Heq.
  - apply Z.eqb_eq in Heq. lia.
  - reflexivity.
Qed.
Lemma snapshot_resolution_learning_step__learning_row_and_scan :
  forall F n live original_count snap ranks logical_dl left i wj,
    0 < logical_dl ->
    coherent_snapshot F n live original_count snap ->
    stable_search_facts n snap ranks logical_dl ->
    var_in_range n i ->
    0 <= wj < live ->
    wj = Znth i (snap_reasons snap) 0 ->
    row_wf n
      (dense_cancel_union left (Znth wj (snap_rows snap) nil)) ->
    Znth i left 0 <> 0 ->
    row_wf n left ->
    entails_clause F (dense_decode left) ->
    clause_false
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (dense_decode left) ->
    (dense_decode left = nil \/
      current_level_support
        (cdcl_view_of_snapshot n snap ranks logical_dl)
        (dense_decode left)) ->
    entails_clause F
      (dense_decode
        (dense_cancel_union left (Znth wj (snap_rows snap) nil))) /\
    clause_false
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (dense_decode
        (dense_cancel_union left (Znth wj (snap_rows snap) nil))) /\
    (dense_decode
        (dense_cancel_union left (Znth wj (snap_rows snap) nil)) = nil \/
      current_level_support
        (cdcl_view_of_snapshot n snap ranks logical_dl)
        (dense_decode
          (dense_cancel_union left (Znth wj (snap_rows snap) nil)))).
Proof.
  intros F n live original_count snap ranks logical_dl left i wj
    Hdl Hcoh Hstable Hi Hwj Hreasoncell Houtwf Hleftcell
    Hleftwf Hleftentails Hleftfalse Hleftsupport.
  set (a := cdcl_view_of_snapshot n snap ranks logical_dl).
  set (right := Znth wj (snap_rows snap) nil).
  assert (Hrightwf : row_wf n right).
  { subst right. eapply coherent_snapshot_row_wf__learning_row_and_scan; eauto. }
  destruct (false_dense_pivot_assignment__learning_row_and_scan
    a n left i Hleftwf Hi Hleftcell Hleftfalse) as
    [b [Hassign Hleftpivot]].
  assert (Hreason : reason_of a i = Some wj).
  { subst a. eapply snapshot_reason_some__learning_row_and_scan; eauto. lia. }
  pose proof Hstable as Hstable_copy.
  unfold stable_search_facts in Hstable_copy; simpl in Hstable_copy.
  destruct Hstable_copy as [Hground [Hclosed Hfrontier]].
  specialize (Hground i b Hassign).
  destruct Hground as [d [rx [Hlevel [Hrank Hgrounded]]]].
  change (level_of a i = Some d) in Hlevel.
  destruct Hgrounded as [[Hnone Hpositive] |
    [reason_index [Hreason_index [Hvalid Hgrounded_tail]]]].
  - change (reason_of a i = None) in Hnone.
    rewrite Hreason in Hnone. discriminate.
  - change (reason_of a i = Some reason_index) in Hreason_index.
    change (reason_valid a i reason_index) in Hvalid.
    rewrite Hreason in Hreason_index. inversion Hreason_index.
    subst reason_index.
    unfold reason_valid in Hvalid.
    destruct Hvalid as
      [reason_b [reason_d [reason_rank [reason_clause
        [Hreason_assign [Hreason_level [Hreason_rank
          [Hreason_nth [Hrightpivot Hrightother]]]]]]]]].
    rewrite Hassign in Hreason_assign. inversion Hreason_assign.
    subst reason_b.
    pose proof Hcoh as Hcoh_parts.
    unfold coherent_snapshot in Hcoh_parts.
    destruct Hcoh_parts as
      [_ [_ [Hlens [Hcells [Hsummaries Hinstalled_sound]]]]].
    assert (Hrowat :
      nth_error (installed_clauses a) (Z.to_nat wj) =
      Some (dense_decode right)).
    { subst a right.
      eapply snapshot_installed_row_at__learning_row_and_scan; eauto. }
    rewrite Hrowat in Hreason_nth. inversion Hreason_nth.
    subst reason_clause.
    assert (Hrightentails : entails_clause F (dense_decode right)).
    { eapply installed_clause_entails__learning_row_and_scan;
        [exact Hinstalled_sound | exact Hrowat]. }
    assert (Hpredecessor :
      forall Hlevel_current : level_of a i = Some (current_level a),
      exists l,
        In l (dense_decode right) /\
        literal_var l <> i /\
        eval_partial_literal (assignment a) l = Some false /\
        current_level_literal a l).
    { intros Hlevel_current.
      assert (Hdcurrent : d = current_level a).
      { rewrite Hlevel in Hlevel_current. inversion Hlevel_current.
        reflexivity. }
      destruct Hgrounded_tail as [Hd0 | [y Hsame]].
      - subst d. subst a. simpl in Hdcurrent. lia.
      - unfold same_level_predecessor in Hsame.
        destruct Hsame as
          [Hdependency [Hsame_x [Hsame_y [rank_x [rank_y Hrank_order]]]]].
        unfold reason_dependency in Hdependency.
        destruct Hdependency as
          [dep_index [dep_clause [dep_lit
            [Hdep_reason [Hdep_nth [Hdep_in [Hdep_var
              [Hdep_neq Hdep_false]]]]]]]].
        change (reason_of a i = Some dep_index) in Hdep_reason.
        change (nth_error (installed_clauses a) (Z.to_nat dep_index) =
          Some dep_clause) in Hdep_nth.
        change (eval_partial_literal (assignment a) dep_lit =
          Some false) in Hdep_false.
        change (level_of a y = Some d) in Hsame_y.
        rewrite Hreason in Hdep_reason. inversion Hdep_reason.
        subst dep_index.
        rewrite Hrowat in Hdep_nth. inversion Hdep_nth.
        subst dep_clause.
        exists dep_lit. split; [exact Hdep_in|].
        split; [rewrite Hdep_var; exact Hdep_neq|].
        split; [exact Hdep_false|].
        unfold current_level_literal.
        rewrite Hdep_var.
        change (level_of a y = Some (current_level a)).
        rewrite Hsame_y, Hdcurrent. reflexivity. }
    assert (Hrightfalse : forall l,
      In l (dense_decode right) ->
      literal_var l <> i ->
      eval_partial_literal (assignment a) l = Some false).
    { intros l Hin Hneq. apply (proj1 (Hrightother l Hin Hneq)). }
    exact (dense_cancel_resolution_learning__learning_row_and_scan
      F a n left right i b Hleftwf Hrightwf Houtwf
      Hleftentails Hrightentails Hleftfalse Hleftpivot Hrightpivot
      Hrightfalse Hpredecessor Hleftsupport).
Qed.
Lemma snapshot_learning_loop_resolution__learning_row_and_scan :
  forall F n live original_count snap ranks logical_dl
    left i wj,
    0 < logical_dl ->
    coherent_snapshot F n live original_count snap ->
    stable_search_facts n snap ranks logical_dl ->
    var_in_range n i ->
    0 <= wj < live ->
    wj = Znth i (snap_reasons snap) 0 ->
    row_wf n
      (dense_cancel_union left (Znth wj (snap_rows snap) nil)) ->
    Znth i left 0 <> 0 ->
    learning_loop F
      (cdcl_view_of_snapshot n snap ranks logical_dl) n left i ->
    learning_loop F
      (cdcl_view_of_snapshot n snap ranks logical_dl) n
      (dense_cancel_union left (Znth wj (snap_rows snap) nil)) 0.
Proof.
  intros F n live original_count snap ranks logical_dl left i wj
    Hdl Hcoh Hstable Hi Hwj Hreasoncell Houtwf Hleftcell Hpre.
  unfold learning_loop in *. cbv zeta in *.
  destruct Hpre as
    [Hleftwf [Hleftentails [Hleftfalse [Hleftsupport [_ Hprocessed]]]]].
  pose proof (snapshot_resolution_learning_step__learning_row_and_scan
    F n live original_count snap ranks logical_dl left i wj
    Hdl Hcoh Hstable Hi Hwj Hreasoncell Houtwf Hleftcell
    Hleftwf Hleftentails Hleftfalse Hleftsupport) as Hsemantic.
  destruct Hsemantic as [Houtentails [Houtfalse Houtsupport]].
  unfold var_in_range in Hi.
  split; [exact Houtwf|].
  split; [exact Houtentails|].
  split; [exact Houtfalse|].
  split; [exact Houtsupport|].
  split; [lia|].
  intros x Hx. lia.
Qed.
(** ===== group: learning_to_conflict_levels ===== *)
Lemma processed_level_succ_iff__learning_to_conflict_levels :
  forall a row i d,
    0 <= i ->
    (processed_level a row (i + 1) d <->
     processed_level a row i d \/
     (Znth i row 0 <> 0 /\ level_of a i = Some d)).
Proof.
  intros a row i d Hi.
  unfold processed_level.
  split.
  - intros [x [Hrange [Hcell Hlevel]]].
    destruct (Z_lt_ge_dec x i) as [Hlt | Hge].
    + left. exists x. split; [lia |]. split; assumption.
    + right. assert (x = i) by lia. subst x. split; assumption.
  - intros [[x [Hrange [Hcell Hlevel]]] | [Hcell Hlevel]].
    + exists x. split; [lia |]. split; assumption.
    + exists i. split; [lia |]. split; assumption.
Qed.
Lemma dense_assigned_cell_level__learning_to_conflict_levels :
  forall n snap ranks logical_dl row i,
    row_wf n row ->
    clause_vars_assigned
      (cdcl_view_of_snapshot n snap ranks logical_dl) (dense_decode row) ->
    0 <= i < n ->
    Zlength (snap_levels snap) = n ->
    Znth i row 0 <> 0 ->
    level_of (cdcl_view_of_snapshot n snap ranks logical_dl) i =
      Some (Znth i (snap_levels snap) 0) /\
    0 <= Znth i (snap_levels snap) 0.
Proof.
  intros n snap ranks logical_dl row i Hwf Hassigned Hi Hlevels Hcell.
  pose proof (row_wf_cell_domain n row i Hwf Hi) as Hdomain.
  assert (Hin : In (Pos i) (dense_decode row) \/
                In (Neg i) (dense_decode row)).
  {
    destruct Hdomain as [Hneg | [Hzero | Hpos]].
    - right. apply (proj1 (dense_decode_neg n row i Hwf Hi)). exact Hneg.
    - contradiction.
    - left. apply (proj1 (dense_decode_pos n row i Hwf Hi)). exact Hpos.
  }
  destruct Hin as [Hin | Hin];
    [specialize (Hassigned (Pos i) Hin) |
     specialize (Hassigned (Neg i) Hin)];
    simpl in Hassigned.
  all: destruct Hassigned as [b [d [_ [Hlevel Hd]]]].
  all: cbn [cdcl_view_of_snapshot] in Hlevel.
  all: unfold snapshot_level in Hlevel.
  all: destruct (snapshot_assignment n snap i) eqn:Hassignment;
       try discriminate.
  all: inversion Hlevel; subst d.
  all: assert (Heq : Znth i (snap_levels snap) (-1) =
                     Znth i (snap_levels snap) 0).
  all: try (apply Znth_indep; rewrite Hlevels; exact Hi).
  all: split;
    [ change (snapshot_level n snap i =
              Some (Znth i (snap_levels snap) 0));
      unfold snapshot_level; rewrite Hassignment, Heq; reflexivity
    | rewrite <- Heq; exact Hd ].
Qed.
Lemma top_two_levels_exact_step_new_max__learning_to_conflict_levels :
  forall a row i max1 max2 e,
    0 <= i ->
    Znth i row 0 <> 0 ->
    level_of a i = Some e ->
    0 <= e ->
    top_two_levels_exact a row i max1 max2 ->
    max1 < e ->
    top_two_levels_exact a row (i + 1) e max1.
Proof.
  intros a row i max1 max2 e Hi Hcell Hlevel He Hexact Hgt.
  assert (Hnew : processed_level a row (i + 1) e).
  {
    apply (proj2
      (processed_level_succ_iff__learning_to_conflict_levels
        a row i e Hi)).
    right. split; assumption.
  }
  unfold top_two_levels_exact in Hexact |- *.
  destruct Hexact as [[Hnone [Hmax1 Hmax2]] |
    [Hmax1occ [Hmaxbound Hsecond]]].
  - subst max1. subst max2.
    right. split; [exact Hnew |].
    split.
    + intros d Hd.
      apply (proj1
        (processed_level_succ_iff__learning_to_conflict_levels
          a row i d Hi)) in Hd.
      destruct Hd as [Hold | [_ Hleveld]].
      * exfalso. exact (Hnone d Hold).
      * assert (d = e) by congruence. subst d. lia.
    + left. split; [reflexivity |].
      intros d Hd.
      apply (proj1
        (processed_level_succ_iff__learning_to_conflict_levels
          a row i d Hi)) in Hd.
      destruct Hd as [Hold | [_ Hleveld]].
      * exfalso. exact (Hnone d Hold).
      * assert (Heq : d = e) by congruence. exact Heq.
  - right. split; [exact Hnew |].
    split.
    + intros d Hd.
      apply (proj1
        (processed_level_succ_iff__learning_to_conflict_levels
          a row i d Hi)) in Hd.
      destruct Hd as [Hold | [_ Hleveld]].
      * specialize (Hmaxbound d Hold). lia.
      * assert (d = e) by congruence. subst d. lia.
    + right.
      split.
      * apply (proj2
          (processed_level_succ_iff__learning_to_conflict_levels
            a row i max1 Hi)).
        left. exact Hmax1occ.
      * split; [exact Hgt |].
        intros d Hd Hdlt.
        apply (proj1
          (processed_level_succ_iff__learning_to_conflict_levels
            a row i d Hi)) in Hd.
        destruct Hd as [Hold | [_ Hleveld]].
        -- apply Hmaxbound. exact Hold.
        -- assert (d = e) by congruence. subst d. lia.
Qed.
Lemma top_two_levels_exact_step_new_second__learning_to_conflict_levels :
  forall a row i max1 max2 e,
    0 <= i ->
    Znth i row 0 <> 0 ->
    level_of a i = Some e ->
    0 <= e ->
    top_two_levels_exact a row i max1 max2 ->
    e < max1 ->
    max2 < e ->
    top_two_levels_exact a row (i + 1) max1 e.
Proof.
  intros a row i max1 max2 e Hi Hcell Hlevel He Hexact Hlt Hgt.
  assert (Hnew : processed_level a row (i + 1) e).
  {
    apply (proj2
      (processed_level_succ_iff__learning_to_conflict_levels
        a row i e Hi)).
    right. split; assumption.
  }
  unfold top_two_levels_exact in Hexact |- *.
  destruct Hexact as [[Hnone [Hmax1 Hmax2]] |
    [Hmax1occ [Hmaxbound Hsecond]]].
  - subst max1. lia.
  - right.
    split.
    + apply (proj2
        (processed_level_succ_iff__learning_to_conflict_levels
          a row i max1 Hi)).
      left. exact Hmax1occ.
    + split.
      * intros d Hd.
        apply (proj1
          (processed_level_succ_iff__learning_to_conflict_levels
            a row i d Hi)) in Hd.
        destruct Hd as [Hold | [_ Hleveld]].
        -- exact (Hmaxbound d Hold).
        -- assert (d = e) by congruence. subst d. lia.
      * right.
        split; [exact Hnew |].
        split; [exact Hlt |].
        intros d Hd Hdlt.
        apply (proj1
          (processed_level_succ_iff__learning_to_conflict_levels
            a row i d Hi)) in Hd.
        destruct Hd as [Hold | [_ Hleveld]].
        -- destruct Hsecond as [[Hmax2none Halltop] |
             [Hmax2occ [Hmax2lt Hbelow]]].
           ++ specialize (Halltop d Hold). lia.
           ++ specialize (Hbelow d Hold Hdlt). lia.
        -- assert (d = e) by congruence. subst d. lia.
Qed.
Lemma top_two_levels_exact_step_below_second__learning_to_conflict_levels :
  forall a row i max1 max2 e,
    0 <= i ->
    Znth i row 0 <> 0 ->
    level_of a i = Some e ->
    0 <= e ->
    top_two_levels_exact a row i max1 max2 ->
    e <= max2 ->
    top_two_levels_exact a row (i + 1) max1 max2.
Proof.
  intros a row i max1 max2 e Hi Hcell Hlevel He Hexact Hle.
  unfold top_two_levels_exact in Hexact |- *.
  destruct Hexact as [[Hnone [Hmax1 Hmax2]] |
    [Hmax1occ [Hmaxbound Hsecond]]].
  - subst max2. lia.
  - right.
    split.
    + apply (proj2
        (processed_level_succ_iff__learning_to_conflict_levels
          a row i max1 Hi)).
      left. exact Hmax1occ.
    + split.
      * intros d Hd.
        apply (proj1
          (processed_level_succ_iff__learning_to_conflict_levels
            a row i d Hi)) in Hd.
        destruct Hd as [Hold | [_ Hleveld]].
        -- exact (Hmaxbound d Hold).
        -- assert (d = e) by congruence. subst d.
           destruct Hsecond as [[Hmax2none _] |
             [_ [Hmax2lt _]]]; lia.
      * destruct Hsecond as [[Hmax2none Halltop] |
          [Hmax2occ [Hmax2lt Hbelow]]].
        -- subst max2. lia.
        -- right.
           split.
           ++ apply (proj2
                (processed_level_succ_iff__learning_to_conflict_levels
                  a row i max2 Hi)).
              left. exact Hmax2occ.
           ++ split; [exact Hmax2lt |].
              intros d Hd Hdlt.
              apply (proj1
                (processed_level_succ_iff__learning_to_conflict_levels
                  a row i d Hi)) in Hd.
              destruct Hd as [Hold | [_ Hleveld]].
              ** exact (Hbelow d Hold Hdlt).
              ** assert (d = e) by congruence. subst d. exact Hle.
Qed.
Lemma top_two_levels_exact_step_equal_max__learning_to_conflict_levels :
  forall a row i max1 max2 e,
    0 <= i ->
    Znth i row 0 <> 0 ->
    level_of a i = Some e ->
    0 <= e ->
    top_two_levels_exact a row i max1 max2 ->
    e = max1 ->
    top_two_levels_exact a row (i + 1) max1 max2.
Proof.
  intros a row i max1 max2 e Hi Hcell Hlevel He Hexact Heq.
  subst e.
  unfold top_two_levels_exact in Hexact |- *.
  destruct Hexact as [[Hnone [Hmax1 Hmax2]] |
    [Hmax1occ [Hmaxbound Hsecond]]].
  - subst max1. lia.
  - right.
    split.
    + apply (proj2
        (processed_level_succ_iff__learning_to_conflict_levels
          a row i max1 Hi)).
      right. split; assumption.
    + split.
      * intros d Hd.
        apply (proj1
          (processed_level_succ_iff__learning_to_conflict_levels
            a row i d Hi)) in Hd.
        destruct Hd as [Hold | [_ Hleveld]].
        -- exact (Hmaxbound d Hold).
        -- assert (d = max1) by congruence. lia.
      * destruct Hsecond as [[Hmax2none Halltop] |
          [Hmax2occ [Hmax2lt Hbelow]]].
        -- left. split; [exact Hmax2none |].
           intros d Hd.
           apply (proj1
             (processed_level_succ_iff__learning_to_conflict_levels
               a row i d Hi)) in Hd.
           destruct Hd as [Hold | [_ Hleveld]].
           ++ exact (Halltop d Hold).
           ++ congruence.
        -- right.
           split.
           ++ apply (proj2
                (processed_level_succ_iff__learning_to_conflict_levels
                  a row i max2 Hi)).
              left. exact Hmax2occ.
           ++ split; [exact Hmax2lt |].
              intros d Hd Hdlt.
              apply (proj1
                (processed_level_succ_iff__learning_to_conflict_levels
                  a row i d Hi)) in Hd.
              destruct Hd as [Hold | [_ Hleveld]].
              ** exact (Hbelow d Hold Hdlt).
              ** assert (d = max1) by congruence. lia.
Qed.
Lemma top_two_levels_exact_step_zero__learning_to_conflict_levels :
  forall a row i max1 max2,
    0 <= i ->
    Znth i row 0 = 0 ->
    top_two_levels_exact a row i max1 max2 ->
    top_two_levels_exact a row (i + 1) max1 max2.
Proof.
  intros a row i max1 max2 Hi Hcell Hexact.
  assert (Hsame : forall d,
    processed_level a row (i + 1) d <->
    processed_level a row i d).
  {
    intro d.
    split.
    - intro Hprocessed.
      apply (proj1
        (processed_level_succ_iff__learning_to_conflict_levels
          a row i d Hi)) in Hprocessed.
      destruct Hprocessed as [Hprocessed | [Hnonzero _]].
      + exact Hprocessed.
      + congruence.
    - intro Hprocessed.
      apply (proj2
        (processed_level_succ_iff__learning_to_conflict_levels
          a row i d Hi)).
      left. exact Hprocessed.
  }
  unfold top_two_levels_exact in Hexact |- *.
  setoid_rewrite Hsame.
  exact Hexact.
Qed.
(** ===== group: bcp_safety_bounds_a ===== *)
Lemma clause_true_count_bounds__bcp_safety_bounds_a :
  forall (sigma : partial_valuation) (c : clause),
    0 <= clause_true_count sigma c <= Zlength c.
Proof.
  intros sigma c.
  induction c as [| l c IH].
  - cbn [clause_true_count].
    rewrite Zlength_nil. lia.
  - cbn [clause_true_count].
    rewrite Zlength_cons.
    destruct (eval_partial_literal sigma l) as [b|] eqn:Heval.
    + destruct b; lia.
    + exact (conj (proj1 IH)
        (Z.le_trans _ _ _ (proj2 IH) (Z.le_succ_diag_r _))).
Qed.
Lemma clause_unassigned_count_bounds__bcp_safety_bounds_a :
  forall (sigma : partial_valuation) (c : clause),
    0 <= clause_unassigned_count sigma c <= Zlength c.
Proof.
  intros sigma c.
  induction c as [| l c IH].
  - cbn [clause_unassigned_count].
    rewrite Zlength_nil. lia.
  - cbn [clause_unassigned_count].
    rewrite Zlength_cons.
    destruct (eval_partial_literal sigma l) eqn:Heval.
    + exact (conj (proj1 IH)
        (Z.le_trans _ _ _ (proj2 IH) (Z.le_succ_diag_r _))).
    + lia.
Qed.
Lemma dense_decode_from_Zlength_le__bcp_safety_bounds_a :
  forall (x : Z) (row : list Z),
    Zlength (dense_decode_from x row) <= Zlength row.
Proof.
  intros x row.
  revert x.
  induction row as [| z row IH]; intros x.
  - cbn [dense_decode_from]. apply Z.le_refl.
  - cbn [dense_decode_from].
    rewrite Zlength_cons.
    specialize (IH (x + 1)).
    destruct (z =? 1)%Z eqn:Hz1.
    + rewrite Zlength_cons. lia.
    + destruct (z =? -1)%Z eqn:Hzm1.
      * rewrite Zlength_cons. lia.
      * lia.
Qed.
Lemma dense_decode_Zlength_le__bcp_safety_bounds_a :
  forall (row : list Z),
    Zlength (dense_decode row) <= Zlength row.
Proof.
  intros row.
  unfold dense_decode.
  apply dense_decode_from_Zlength_le__bcp_safety_bounds_a.
Qed.
Lemma Znth_map_dense_decode__bcp_safety_bounds_a :
  forall (rows : list (list Z)) (i : Z),
    Znth i (List.map dense_decode rows) (nil : clause) =
    dense_decode (Znth i rows (nil : list Z)).
Proof.
  intros rows i.
  unfold Znth.
  change
    (nth (Z.to_nat i) (List.map dense_decode rows)
      (dense_decode (nil : list Z)) =
     dense_decode (nth (Z.to_nat i) rows (nil : list Z))).
  apply map_nth.
Qed.
Lemma expected_clause_state_bounds__bcp_safety_bounds_a :
  forall (sigma : partial_valuation) (c : clause),
    - Zlength c <= expected_clause_state sigma c <= 2.
Proof.
  intros sigma c.
  pose proof (clause_true_count_bounds__bcp_safety_bounds_a sigma c)
    as Htrue.
  pose proof (clause_unassigned_count_bounds__bcp_safety_bounds_a sigma c)
    as Hunassigned.
  unfold expected_clause_state.
  destruct (0 <? clause_true_count sigma c)%Z eqn:Ht.
  - apply Z.ltb_lt in Ht. lia.
  - apply Z.ltb_ge in Ht.
    destruct (clause_unassigned_count sigma c =? 0)%Z eqn:Hu0.
    + apply Z.eqb_eq in Hu0. lia.
    + apply Z.eqb_neq in Hu0.
      destruct (clause_unassigned_count sigma c =? 1)%Z eqn:Hu1.
      * apply Z.eqb_eq in Hu1. lia.
      * apply Z.eqb_neq in Hu1. lia.
Qed.
Lemma summary_machine_bounds__bcp_safety_bounds_a :
  forall
    (old_sigma new_sigma : partial_valuation)
    (dense_rows : list (list Z))
    (states true_counts unassigned : list Z)
    (live cap processed exempt i n : Z),
    mixed_clause_summaries
      old_sigma new_sigma (List.map dense_decode dense_rows)
      states true_counts unassigned live cap processed (Some exempt) ->
    0 <= i < live ->
    processed <= i ->
    i <> exempt ->
    Zlength (Znth i dense_rows (nil : list Z)) = n ->
    (0 <= Znth i true_counts 0 <= n) /\
    (0 <= Znth i unassigned 0 <= n) /\
    (- n <= Znth i states 0 <= 2).
Proof.
  intros old_sigma new_sigma dense_rows states true_counts unassigned
    live cap processed exempt i n Hmixed Hi Hprocessed Hneq Hrowlen.
  unfold mixed_clause_summaries in Hmixed.
  destruct Hmixed as
    (_ & _ & _ & _ & _ & _ & Hsummaries).
  specialize (Hsummaries i Hi).
  destruct Hsummaries as [_ Hold].
  assert (Hsome : Some exempt <> Some i) by congruence.
  specialize (Hold (conj Hprocessed Hsome)).
  unfold summary_at, clause_summary_ok in Hold.
  destruct Hold as (Htrue & Hunassigned & Hstate).
  rewrite Htrue, Hunassigned, Hstate.
  repeat rewrite Znth_map_dense_decode__bcp_safety_bounds_a.
  pose proof
    (clause_true_count_bounds__bcp_safety_bounds_a old_sigma
      (dense_decode (Znth i dense_rows (nil : list Z)))) as Htrue_bound.
  pose proof
    (clause_unassigned_count_bounds__bcp_safety_bounds_a old_sigma
      (dense_decode (Znth i dense_rows (nil : list Z))))
    as Hunassigned_bound.
  pose proof
    (expected_clause_state_bounds__bcp_safety_bounds_a old_sigma
      (dense_decode (Znth i dense_rows (nil : list Z)))) as Hstate_bound.
  pose proof
    (dense_decode_Zlength_le__bcp_safety_bounds_a
      (Znth i dense_rows (nil : list Z))) as Hdecode.
  rewrite Hrowlen in Hdecode.
  repeat split; lia.
Qed.
(** ===== group: bcp_safety_to_scan_init ===== *)
Lemma Zlength_map_dense_decode__bcp_safety_to_scan_init :
  forall rows,
    Zlength (map dense_decode rows) = Zlength rows.
Proof.
  induction rows as [|row rows IH]; cbn [map].
  - rewrite !Zlength_nil. reflexivity.
  - rewrite !Zlength_cons.
    f_equal.
    exact IH.
Qed.
Lemma Znth_map_dense_decode__bcp_safety_to_scan_init :
  forall rows i,
    0 <= i < Zlength rows ->
    Znth i (map dense_decode rows) nil =
      dense_decode (Znth i rows nil).
Proof.
  intros rows i Hi. apply Znth_map. exact Hi.
Qed.
(** ===== group: bcp_unit_to_assignment ===== *)
Lemma rank_in_clause_below_bound__bcp_unit_to_assignment :
  forall ranks c l r,
    In l c -> ranks (literal_var l) = Some r ->
    (r < S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c)) ranks c))%nat.
Proof.
  intros ranks c; induction c as [|a c IH]; intros l r Hin Hr.
  - contradiction.
  - simpl in Hin; cbn;
      simpl fold_right; simpl map.
    destruct Hin as [->|Hin].
    + cbn; rewrite Hr.
      pose proof (Nat.le_max_l r
        (fold_right Nat.max O
          (map (fun l => (fun (ranks : Z -> option nat) (x : Z) => match ranks x with Some r => r | None => O end)
                           ranks (literal_var l)) c))).
      lia.
    + pose proof (IH l r Hin Hr) as IHbound.
      cbn in IHbound.
      pose proof (Nat.le_max_r
        ((fun (ranks : Z -> option nat) (x : Z) => match ranks x with Some r => r | None => O end) ranks (literal_var a))
        (fold_right Nat.max O
          (map (fun l => (fun (ranks : Z -> option nat) (x : Z) => match ranks x with Some r => r | None => O end)
                           ranks (literal_var l)) c))).
      lia.
Qed.
Lemma clause_true_count_nonnegative_base__bcp_unit_to_assignment :
  forall sigma c, 0 <= clause_true_count sigma c.
Proof.
  intros sigma c; induction c as [|l c IH];
    cbn -[eval_partial_literal Z.add]; [lia|].
  destruct (eval_partial_literal sigma l) as [[|]|];
    cbn -[eval_partial_literal Z.add]; lia.
Qed.
Lemma clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment :
  forall sigma c, 0 <= clause_unassigned_count sigma c.
Proof.
  intros sigma c; induction c as [|l c IH];
    cbn -[eval_partial_literal Z.add]; [lia|].
  destruct (eval_partial_literal sigma l) as [[|]|];
    cbn -[eval_partial_literal Z.add]; lia.
Qed.
Lemma clause_true_count_member_true__bcp_unit_to_assignment :
  forall sigma c l,
    In l c -> eval_partial_literal sigma l = Some true ->
    1 <= clause_true_count sigma c.
Proof.
  intros sigma c; induction c as [|a c IH]; intros l Hin Heval.
  - contradiction.
  - simpl in Hin; cbn -[eval_partial_literal Z.add].
    destruct Hin as [->|Hin].
    + rewrite Heval.
      pose proof
        (clause_true_count_nonnegative_base__bcp_unit_to_assignment sigma c);
      lia.
    + specialize (IH l Hin Heval).
      destruct (eval_partial_literal sigma a) as [[|]|];
        cbn -[eval_partial_literal Z.add]; lia.
Qed.
Lemma clause_unassigned_count_member_none__bcp_unit_to_assignment :
  forall sigma c l,
    In l c -> eval_partial_literal sigma l = None ->
    1 <= clause_unassigned_count sigma c.
Proof.
  intros sigma c; induction c as [|a c IH]; intros l Hin Heval.
  - contradiction.
  - simpl in Hin; cbn -[eval_partial_literal Z.add].
    destruct Hin as [->|Hin].
    + rewrite Heval.
      pose proof
        (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment
          sigma c);
      lia.
    + specialize (IH l Hin Heval).
      destruct (eval_partial_literal sigma a) as [[|]|];
        cbn -[eval_partial_literal Z.add]; lia.
Qed.
Lemma clause_unassigned_count_two_none__bcp_unit_to_assignment :
  forall sigma c l1 l2,
    l1 <> l2 -> In l1 c -> In l2 c ->
    eval_partial_literal sigma l1 = None ->
    eval_partial_literal sigma l2 = None ->
    2 <= clause_unassigned_count sigma c.
Proof.
  intros sigma c; induction c as [|a c IH];
    intros l1 l2 Hneq H1 H2 He1 He2.
  - contradiction.
  - simpl in H1, H2; cbn -[eval_partial_literal Z.add].
    destruct H1 as [H1|H1], H2 as [H2|H2].
    + subst; contradiction.
    + subst a; rewrite He1.
      pose proof
        (clause_unassigned_count_member_none__bcp_unit_to_assignment
          sigma c l2 H2 He2); lia.
    + subst a; rewrite He2.
      pose proof
        (clause_unassigned_count_member_none__bcp_unit_to_assignment
          sigma c l1 H1 He1); lia.
    + specialize (IH l1 l2 Hneq H1 H2 He1 He2).
      destruct (eval_partial_literal sigma a) as [[|]|];
        cbn -[eval_partial_literal Z.add]; lia.
Qed.
Lemma eval_satisfying_literal_none__bcp_unit_to_assignment :
  forall sigma x b,
    sigma x = None ->
    eval_partial_literal sigma (satisfying_literal x b) = None.
Proof.
  intros sigma x []; unfold satisfying_literal, eval_partial_literal,
    literal_var; simpl; intros H; rewrite H; reflexivity.
Qed.
Lemma eval_satisfying_literal_true__bcp_unit_to_assignment :
  forall sigma x b,
    sigma x = Some b ->
    eval_partial_literal sigma (satisfying_literal x b) = Some true.
Proof.
  intros sigma x []; unfold satisfying_literal, eval_partial_literal,
    literal_var; simpl; intros H; rewrite H; reflexivity.
Qed.
Lemma eval_falsified_literal_false__bcp_unit_to_assignment :
  forall sigma x b,
    sigma x = Some b ->
    eval_partial_literal sigma (falsified_literal x b) = Some false.
Proof.
  intros sigma x []; unfold falsified_literal, eval_partial_literal,
    literal_var; simpl; intros H; rewrite H; reflexivity.
Qed.
Lemma clause_unit_other_false__bcp_unit_to_assignment :
  forall sigma c x b,
    clause_unit sigma c -> sigma x = None ->
    In (satisfying_literal x b) c ->
    forall l, In l c -> literal_var l <> x ->
      eval_partial_literal sigma l = Some false.
Proof.
  intros sigma c x b [Htrue Hunassigned] Hnone HinSat l Hin Hvar.
  pose proof
    (eval_satisfying_literal_none__bcp_unit_to_assignment
      sigma x b Hnone) as Hsatnone.
  assert (Hneq : l <> satisfying_literal x b).
  { intro Heq; subst l; unfold satisfying_literal in Hvar;
      destruct b; cbn in Hvar; contradiction. }
  destruct (eval_partial_literal sigma l) as [[|]|] eqn:Heval.
  - exfalso.
    pose proof
      (clause_true_count_member_true__bcp_unit_to_assignment
        sigma c l Hin Heval); lia.
  - reflexivity.
  - exfalso.
    pose proof
      (clause_unassigned_count_two_none__bcp_unit_to_assignment
        sigma c l (satisfying_literal x b) Hneq Hin HinSat
        Heval Hsatnone); lia.
Qed.
Lemma literal_counts_no_var__bcp_unit_to_assignment :
  forall x b c,
    (forall l, In l c -> literal_var l <> x) ->
    literal_var_count x c = 0 /\ literal_true_at_count x b c = 0.
Proof.
  intros x b c; induction c as [|l c IH]; intro Hnone.
  - split; reflexivity.
  - cbn [literal_var_count literal_true_at_count].
    assert (Hlx : literal_var l <> x) by (apply Hnone; left; reflexivity).
    assert (Heq : Z.eqb (literal_var l) x = false)
      by (apply Z.eqb_neq; exact Hlx).
    rewrite Heq.
    apply IH; intros l' Hin; apply Hnone; right; exact Hin.
Qed.
Lemma eval_partial_literal_unassigned__bcp_unit_to_assignment :
  forall sigma l,
    sigma (literal_var l) = None -> eval_partial_literal sigma l = None.
Proof.
  intros sigma [y|y]; unfold literal_var, eval_partial_literal; simpl;
    intro H; rewrite H; reflexivity.
Qed.
Lemma unit_extend_assignment_same__bcp_unit_to_assignment :
  forall old x b d reason rx,
    assignment
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) x =
    Some b.
Proof.
  intros; cbn.
  apply partial_mapping_update_eq.
Qed.
Lemma unit_extend_assignment_other__bcp_unit_to_assignment :
  forall old x b d reason rx y,
    y <> x ->
    assignment
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) y =
    assignment old y.
Proof.
  intros; cbn.
  apply partial_mapping_update_neq; lia.
Qed.
Lemma unit_extend_level_same__bcp_unit_to_assignment :
  forall old x b d reason rx,
    level_of
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) x =
    Some d.
Proof.
  intros; cbn.
  apply total_mapping_update_eq.
Qed.
Lemma unit_extend_level_other__bcp_unit_to_assignment :
  forall old x b d reason rx y,
    y <> x ->
    level_of
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) y =
    level_of old y.
Proof.
  intros; cbn.
  apply total_mapping_update_neq; lia.
Qed.
Lemma unit_extend_reason_same__bcp_unit_to_assignment :
  forall old x b d reason rx,
    reason_of
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) x =
    Some reason.
Proof.
  intros; cbn.
  apply total_mapping_update_eq.
Qed.
Lemma unit_extend_reason_other__bcp_unit_to_assignment :
  forall old x b d reason rx y,
    y <> x ->
    reason_of
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) y =
    reason_of old y.
Proof.
  intros; cbn.
  apply total_mapping_update_neq; lia.
Qed.
Lemma unit_extend_rank_same__bcp_unit_to_assignment :
  forall old x b d reason rx,
    assignment_rank
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) x =
    Some rx.
Proof.
  intros; cbn.
  apply total_mapping_update_eq.
Qed.
Lemma unit_extend_rank_other__bcp_unit_to_assignment :
  forall old x b d reason rx y,
    y <> x ->
    assignment_rank
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) y =
    assignment_rank old y.
Proof.
  intros; cbn.
  apply total_mapping_update_neq; lia.
Qed.
Lemma unit_extend_eval_other__bcp_unit_to_assignment :
  forall old x b d reason rx l,
    literal_var l <> x ->
    eval_partial_literal
      (assignment
        ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx)) l =
    eval_partial_literal (assignment old) l.
Proof.
  intros old x b d reason rx [y|y] Hneq;
    unfold literal_var, eval_partial_literal in *; simpl in *;
    rewrite partial_mapping_update_neq by lia;
    reflexivity.
Qed.
Lemma reason_dependency_unit_extend_other__bcp_unit_to_assignment :
  forall old x b d reason rx y z,
    assignment old x = None -> y <> x ->
    reason_dependency old y z ->
    reason_dependency
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) y z.
Proof.
  intros old x b d reason rx y z Hxnone Hyx
    [i [c [l [Hreason [Hnth [Hin [Hvar [Hzy Heval]]]]]]]].
  assert (Hzx : z <> x).
  { intro Heq.
    assert (Hnonevar : assignment old (literal_var l) = None).
    { rewrite Hvar, Heq; exact Hxnone. }
    pose proof
      (eval_partial_literal_unassigned__bcp_unit_to_assignment
        (assignment old) l Hnonevar); congruence. }
  exists i, c, l; repeat split.
  - rewrite unit_extend_reason_other__bcp_unit_to_assignment by exact Hyx.
    exact Hreason.
  - exact Hnth.
  - exact Hin.
  - exact Hvar.
  - exact Hzy.
  - rewrite unit_extend_eval_other__bcp_unit_to_assignment by
      (rewrite Hvar; exact Hzx).
    exact Heval.
Qed.
Lemma reason_valid_unit_extend_other__bcp_unit_to_assignment :
  forall old x b d reason rx y i,
    assignment old x = None -> y <> x -> reason_valid old y i ->
    reason_valid
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) y i.
Proof.
  intros old x b d reason rx y i Hxnone Hyx
    [bv [dy [ry [c [Hassign [Hlevel [Hrank [Hnth [Hin Hrest]]]]]]]]].
  exists bv, dy, ry, c.
  split.
  { rewrite unit_extend_assignment_other__bcp_unit_to_assignment by exact Hyx.
    exact Hassign. }
  split.
  { rewrite unit_extend_level_other__bcp_unit_to_assignment by exact Hyx.
    exact Hlevel. }
  split.
  { rewrite unit_extend_rank_other__bcp_unit_to_assignment by exact Hyx.
    exact Hrank. }
  split; [exact Hnth|].
  split; [exact Hin|].
  intros lit Hlit Hly.
    destruct (Hrest lit Hlit Hly) as
      [Heval [dl [rl [Hdl [Hrl [Hle Hlt]]]]]].
    assert (Hlx : literal_var lit <> x).
    { intro Heq.
      pose proof
        (eval_partial_literal_unassigned__bcp_unit_to_assignment
          (assignment old) lit) as Hnone.
      rewrite Heq, Hxnone in Hnone; specialize (Hnone eq_refl); congruence. }
  split.
  - rewrite unit_extend_eval_other__bcp_unit_to_assignment by exact Hlx.
    exact Heval.
  - exists dl, rl; repeat split.
    + rewrite unit_extend_level_other__bcp_unit_to_assignment by exact Hlx.
      exact Hdl.
    + rewrite unit_extend_rank_other__bcp_unit_to_assignment by exact Hlx.
      exact Hrl.
    + exact Hle.
    + exact Hlt.
Qed.
Lemma same_level_predecessor_unit_extend_other__bcp_unit_to_assignment :
  forall old x b d reason rx y z level,
    assignment old x = None -> y <> x ->
    same_level_predecessor old y z level ->
    same_level_predecessor
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx)
      y z level.
Proof.
  intros old x b d reason rx y z level Hxnone Hyx
    [Hdep [Hly [Hlz [ry [rz [Hry [Hrz Hlt]]]]]]].
  assert (Hzx : z <> x).
  { intro Heq.
    destruct Hdep as [i [c [l [_ [_ [_ [Hvar [_ Heval]]]]]]]].
    assert (Hnonevar : assignment old (literal_var l) = None).
    { rewrite Hvar, Heq; exact Hxnone. }
    pose proof
      (eval_partial_literal_unassigned__bcp_unit_to_assignment
        (assignment old) l Hnonevar); congruence. }
  repeat split.
  - eapply reason_dependency_unit_extend_other__bcp_unit_to_assignment;
      eauto.
  - rewrite unit_extend_level_other__bcp_unit_to_assignment by exact Hyx;
      exact Hly.
  - rewrite unit_extend_level_other__bcp_unit_to_assignment by exact Hzx;
      exact Hlz.
  - exists ry, rz; repeat split.
    + rewrite unit_extend_rank_other__bcp_unit_to_assignment by exact Hyx;
        exact Hry.
    + rewrite unit_extend_rank_other__bcp_unit_to_assignment by exact Hzx;
        exact Hrz.
    + exact Hlt.
Qed.
Lemma eval_partial_literal_assigned__bcp_unit_to_assignment :
  forall sigma l v,
    eval_partial_literal sigma l = Some v ->
    exists b, sigma (literal_var l) = Some b.
Proof.
  intros sigma [y|y] v; unfold literal_var, eval_partial_literal; simpl;
    destruct (sigma y) as [b|] eqn:Hcell; intro H; try discriminate;
    eauto.
Qed.
Lemma restrict_current_eq_assignment__bcp_unit_to_assignment :
  forall a,
    grounded_at a -> closed_levels a ->
    restrict_to_level a (current_level a) = assignment a.
Proof.
  intros a Hground [Hdl [Hlevels _]].
  apply functional_extensionality; intro y.
  unfold restrict_to_level.
  destruct (assignment a y) as [bv|] eqn:Hassign; [|reflexivity].
  destruct (Hground y bv Hassign) as
    [dy [ry [Hlevel Hgrounded]]].
  rewrite Hlevel.
  assert (Hle : Z.leb dy (current_level a) = true).
  { apply Z.leb_le; apply (Hlevels y bv dy Hassign Hlevel). }
  rewrite Hle; reflexivity.
Qed.
Lemma restrict_before_unit_extend__bcp_unit_to_assignment :
  forall old x b d reason rx k,
    assignment old x = None -> k < d ->
    restrict_to_level
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason rx) k =
    restrict_to_level old k.
Proof.
  intros old x b d reason rx k Hnone Hkd.
  apply functional_extensionality; intro y.
  unfold restrict_to_level.
  destruct (Z.eq_dec y x) as [->|Hyx].
  - rewrite unit_extend_assignment_same__bcp_unit_to_assignment,
      unit_extend_level_same__bcp_unit_to_assignment, Hnone.
    assert (Hle : Z.leb d k = false) by (apply Z.leb_gt; lia).
    rewrite Hle; reflexivity.
  - rewrite unit_extend_assignment_other__bcp_unit_to_assignment by exact Hyx.
    rewrite unit_extend_level_other__bcp_unit_to_assignment by exact Hyx.
    reflexivity.
Qed.
Lemma reason_valid_new_unit__bcp_unit_to_assignment :
  forall old x b d reason c,
    grounded_at old -> closed_levels old ->
    assignment old x = None -> current_level old = d ->
    nth_error (installed_clauses old) (Z.to_nat reason) = Some c ->
    clause_unit (assignment old) c ->
    In (satisfying_literal x b) c ->
    reason_valid
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason
        (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c))
          (assignment_rank old) c))) x reason.
Proof.
  intros old x b d reason c Hground Hclosed Hnone Hcur Hnth Hunit Hin.
  set (rx := S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c))
    (assignment_rank old) c)).
  exists b, d, rx, c.
  split; [apply unit_extend_assignment_same__bcp_unit_to_assignment|].
  split; [apply unit_extend_level_same__bcp_unit_to_assignment|].
  split; [apply unit_extend_rank_same__bcp_unit_to_assignment|].
  split; [exact Hnth|].
  split; [exact Hin|].
  intros l Hl Hlx.
  assert (Holdfalse : eval_partial_literal (assignment old) l = Some false).
  { eapply clause_unit_other_false__bcp_unit_to_assignment; eauto. }
  split.
  - rewrite unit_extend_eval_other__bcp_unit_to_assignment by exact Hlx.
    exact Holdfalse.
  - destruct
      (eval_partial_literal_assigned__bcp_unit_to_assignment
        (assignment old) l false Holdfalse) as [bl Hassigned].
    destruct (Hground (literal_var l) bl Hassigned) as
      [dl [rl [Hlevel Hground_l]]].
    exists dl, rl; repeat split.
    + rewrite unit_extend_level_other__bcp_unit_to_assignment by exact Hlx.
      exact Hlevel.
    + rewrite unit_extend_rank_other__bcp_unit_to_assignment by exact Hlx.
      exact (proj1 Hground_l).
    + destruct Hclosed as [_ [Hlevels _]].
      specialize (Hlevels (literal_var l) bl dl Hassigned Hlevel).
      lia.
    + unfold rx.
      eapply rank_in_clause_below_bound__bcp_unit_to_assignment;
        [exact Hl|exact (proj1 Hground_l)].
Qed.
Lemma assigns_one_new_unit__bcp_unit_to_assignment :
  forall old x b d reason c,
    grounded_at old -> closed_levels old ->
    assignment old x = None -> 0 <= reason ->
    nth_error (installed_clauses old) (Z.to_nat reason) = Some c ->
    clause_unit (assignment old) c ->
    In (satisfying_literal x b) c ->
    assigns_one old
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason
        (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c))
          (assignment_rank old) c))) x b d reason.
Proof.
  intros old x b d reason c Hground Hclosed Hnone Hreason Hnth Hunit Hin.
  set (rx := S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c))
    (assignment_rank old) c)).
  unfold assigns_one.
  split; [exact Hnone|].
  split; [apply unit_extend_assignment_same__bcp_unit_to_assignment|].
  split; [apply unit_extend_level_same__bcp_unit_to_assignment|].
  split.
  { rewrite unit_extend_reason_same__bcp_unit_to_assignment.
    assert (Heq : Z.eqb reason (-1) = false) by (apply Z.eqb_neq; lia).
    rewrite Heq; reflexivity. }
  split.
  { exists rx; split; [apply unit_extend_rank_same__bcp_unit_to_assignment|].
    intros y [i [c' [l [Hreason' [Hnth' [Hl [Hvar [Hyx Heval]]]]]]]].
    rewrite unit_extend_reason_same__bcp_unit_to_assignment in Hreason'.
    injection Hreason' as Hi; subst i.
    change (nth_error (installed_clauses old) (Z.to_nat reason) = Some c')
      in Hnth'.
    rewrite Hnth in Hnth'; inversion Hnth'; subst c'.
    assert (Hlx : literal_var l <> x) by (rewrite Hvar; exact Hyx).
    rewrite unit_extend_eval_other__bcp_unit_to_assignment in Heval by exact Hlx.
    destruct
      (eval_partial_literal_assigned__bcp_unit_to_assignment
        (assignment old) l false Heval) as [bl Hassigned].
    rewrite Hvar in Hassigned.
    destruct (Hground y bl Hassigned) as
      [dl [rl [Hlevel Hground_l]]].
    exists rl; split.
    - rewrite unit_extend_rank_other__bcp_unit_to_assignment by exact Hyx.
      exact (proj1 Hground_l).
    - unfold rx.
      eapply rank_in_clause_below_bound__bcp_unit_to_assignment;
        [exact Hl|rewrite Hvar; exact (proj1 Hground_l)]. }
  split.
  { intros y Hyx; repeat split.
    - apply unit_extend_assignment_other__bcp_unit_to_assignment; exact Hyx.
    - apply unit_extend_level_other__bcp_unit_to_assignment; exact Hyx.
    - apply unit_extend_reason_other__bcp_unit_to_assignment; exact Hyx.
    - apply unit_extend_rank_other__bcp_unit_to_assignment; exact Hyx. }
  reflexivity.
Qed.
Lemma grounded_unit_extend__bcp_unit_to_assignment :
  forall old x b d reason c,
    grounded_at old -> closed_levels old -> frontier_closed old ->
    assignment old x = None -> current_level old = d -> 0 <= reason ->
    nth_error (installed_clauses old) (Z.to_nat reason) = Some c ->
    clause_unit (assignment old) c ->
    In (satisfying_literal x b) c ->
    grounded_at
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason
        (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c))
          (assignment_rank old) c))).
Proof.
  intros old x b d reason c Hground Hclosed Hfront Hnone Hcur
    Hreason Hnth Hunit Hin.
  set (rx := S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c))
    (assignment_rank old) c)).
  intros y bv Hassign.
  destruct (Z.eq_dec y x) as [->|Hyx].
  - rewrite unit_extend_assignment_same__bcp_unit_to_assignment in Hassign.
    inversion Hassign; subst bv.
    exists d, rx.
    split; [apply unit_extend_level_same__bcp_unit_to_assignment|].
    split; [apply unit_extend_rank_same__bcp_unit_to_assignment|].
    right; exists reason.
    split; [apply unit_extend_reason_same__bcp_unit_to_assignment|].
    split.
    { unfold rx.
      eapply reason_valid_new_unit__bcp_unit_to_assignment; eauto. }
    destruct (Z.eq_dec d 0) as [->|Hd0]; [left; reflexivity|].
    right.
    destruct Hfront as [Hbefore Hsupported].
    destruct Hsupported as [Hcur0|Hsupported]; [congruence|].
    assert (Holdrestrict :
      restrict_to_level old (current_level old) = assignment old).
    { apply restrict_current_eq_assignment__bcp_unit_to_assignment;
        assumption. }
    assert (Hinc : In c (installed_clauses old)).
    { eapply nth_error_In; exact Hnth. }
    assert (Hactive :
      active_frontier_clause
        (restrict_to_level old (current_level old)) c).
    { rewrite Holdrestrict; unfold active_frontier_clause, clause_unit in *;
        lia. }
    destruct (Hsupported c Hinc Hactive) as
      [l [Hl [Heval Hlevel]]].
    rewrite Holdrestrict in Heval.
    assert (Hlx : literal_var l <> x).
    { intro Heq.
      pose proof
        (eval_partial_literal_unassigned__bcp_unit_to_assignment
          (assignment old) l) as Hnone_l.
      rewrite Heq, Hnone in Hnone_l; specialize (Hnone_l eq_refl);
        congruence. }
    destruct
      (eval_partial_literal_assigned__bcp_unit_to_assignment
        (assignment old) l false Heval) as [bl Hassigned].
    destruct (Hground (literal_var l) bl Hassigned) as
      [dl [rl [Hlevel' [Hrank Hground_l]]]].
    assert (Hdl : dl = d) by (rewrite Hcur in Hlevel; congruence).
    subst dl.
    exists (literal_var l).
    split.
    { exists reason, c, l.
      split; [apply unit_extend_reason_same__bcp_unit_to_assignment|].
      split; [exact Hnth|].
      split; [exact Hl|].
      split; [reflexivity|].
      split; [exact Hlx|].
      rewrite unit_extend_eval_other__bcp_unit_to_assignment by exact Hlx.
      exact Heval. }
    split; [apply unit_extend_level_same__bcp_unit_to_assignment|].
    split.
    { rewrite unit_extend_level_other__bcp_unit_to_assignment by exact Hlx.
      rewrite Hcur in Hlevel; exact Hlevel. }
    exists rx, rl.
    split; [apply unit_extend_rank_same__bcp_unit_to_assignment|].
    split.
    { rewrite unit_extend_rank_other__bcp_unit_to_assignment by exact Hlx.
      exact Hrank. }
    unfold rx.
    eapply rank_in_clause_below_bound__bcp_unit_to_assignment;
      [exact Hl|exact Hrank].
  - rewrite unit_extend_assignment_other__bcp_unit_to_assignment in Hassign
      by exact Hyx.
    destruct (Hground y bv Hassign) as
      [dy [ry [Hlevel [Hrank Hwhy]]]].
    exists dy, ry.
    split.
    { rewrite unit_extend_level_other__bcp_unit_to_assignment by exact Hyx;
        exact Hlevel. }
    split.
    { rewrite unit_extend_rank_other__bcp_unit_to_assignment by exact Hyx;
        exact Hrank. }
    destruct Hwhy as [[Hdecision Hdy]|[i [Hreason_old [Hvalid Hsource]]]].
    + left; split; [|exact Hdy].
      rewrite unit_extend_reason_other__bcp_unit_to_assignment by exact Hyx;
        exact Hdecision.
    + right; exists i.
      split.
      { rewrite unit_extend_reason_other__bcp_unit_to_assignment by exact Hyx;
          exact Hreason_old. }
      split.
      { eapply reason_valid_unit_extend_other__bcp_unit_to_assignment;
          eauto. }
      destruct Hsource as [Hdy0|[z Hpred]].
      * left; exact Hdy0.
      * right; exists z.
        eapply same_level_predecessor_unit_extend_other__bcp_unit_to_assignment;
          eauto.
Qed.
Lemma closed_levels_unit_extend__bcp_unit_to_assignment :
  forall old x b d reason c,
    assignment old x = None -> current_level old = d ->
    closed_levels old ->
    closed_levels
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason
        (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c))
          (assignment_rank old) c))).
Proof.
  intros old x b d reason c Hnone Hcur
    [Hdl [Hlevels [Hnozero Hunique]]].
  set (rx := S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c))
    (assignment_rank old) c)).
  split.
  { cbn; exact Hdl. }
  split.
  { intros y bv dy Hassign Hlevel.
    destruct (Z.eq_dec y x) as [->|Hyx].
    - rewrite unit_extend_assignment_same__bcp_unit_to_assignment in Hassign.
      inversion Hassign; subst bv.
      rewrite unit_extend_level_same__bcp_unit_to_assignment in Hlevel.
      inversion Hlevel; subst dy.
      change (0 <= d <= current_level old).
      rewrite <- Hcur; lia.
    - rewrite unit_extend_assignment_other__bcp_unit_to_assignment in Hassign
        by exact Hyx.
      rewrite unit_extend_level_other__bcp_unit_to_assignment in Hlevel
        by exact Hyx.
      cbn.
      eapply Hlevels; eauto. }
  split.
  { intros y Hdecision.
    destruct (Z.eq_dec y x) as [->|Hyx].
    - destruct Hdecision as [[bv Hassign] [Hlevel Hreason_new]].
      rewrite unit_extend_reason_same__bcp_unit_to_assignment in Hreason_new;
        discriminate.
    - apply (Hnozero y).
      destruct Hdecision as [[bv Hassign] [Hlevel Hreason_new]].
      split.
      + exists bv.
        rewrite unit_extend_assignment_other__bcp_unit_to_assignment in Hassign
          by exact Hyx; exact Hassign.
      + split.
        * rewrite unit_extend_level_other__bcp_unit_to_assignment in Hlevel
            by exact Hyx; exact Hlevel.
        * rewrite unit_extend_reason_other__bcp_unit_to_assignment in Hreason_new
            by exact Hyx; exact Hreason_new. }
  intros dl Hdlrange.
  cbn in Hdlrange.
  destruct (Hunique dl Hdlrange) as [y [Hy Huniq]].
  assert (Hyx : y <> x).
  { intro Heq; subst y.
    destruct Hy as [[bv Hass] _]; rewrite Hnone in Hass; discriminate. }
  exists y.
  split.
  { destruct Hy as [[bv Hass] [Hlevel Hreason_old]].
    split.
    - exists bv.
      rewrite unit_extend_assignment_other__bcp_unit_to_assignment by exact Hyx;
        exact Hass.
    - split.
      + rewrite unit_extend_level_other__bcp_unit_to_assignment by exact Hyx;
          exact Hlevel.
      + rewrite unit_extend_reason_other__bcp_unit_to_assignment by exact Hyx;
          exact Hreason_old. }
  intros z Hz.
  assert (Hzx : z <> x).
  { intro Heq; subst z.
    destruct Hz as [[bv Hass] [Hlevel Hreason_new]].
    rewrite unit_extend_reason_same__bcp_unit_to_assignment in Hreason_new;
      discriminate. }
  apply Huniq.
  destruct Hz as [[bv Hass] [Hlevel Hreason_new]].
  split.
  - exists bv.
    rewrite unit_extend_assignment_other__bcp_unit_to_assignment in Hass
      by exact Hzx; exact Hass.
  - split.
    + rewrite unit_extend_level_other__bcp_unit_to_assignment in Hlevel
        by exact Hzx; exact Hlevel.
    + rewrite unit_extend_reason_other__bcp_unit_to_assignment in Hreason_new
        by exact Hzx; exact Hreason_new.
Qed.
Lemma frontier_closed_unit_extend__bcp_unit_to_assignment :
  forall old x b d reason c,
    grounded_at old -> closed_levels old -> frontier_closed old ->
    assignment old x = None -> current_level old = d -> 0 <= reason ->
    nth_error (installed_clauses old) (Z.to_nat reason) = Some c ->
    clause_unit (assignment old) c ->
    In (satisfying_literal x b) c ->
    frontier_closed
      ((fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |}) old x b d reason
        (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c))
          (assignment_rank old) c))).
Proof.
  intros old x b d reason c Hground Hclosed Hfront Hnone Hcur
    Hreason Hnth Hunit Hin.
  set (rx := S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c))
    (assignment_rank old) c)).
  set (new := (fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |})
    old x b d reason rx).
  assert (Hground_new : grounded_at new).
  { unfold new, rx.
    eapply grounded_unit_extend__bcp_unit_to_assignment; eauto. }
  assert (Hclosed_new : closed_levels new).
  { unfold new, rx.
    eapply closed_levels_unit_extend__bcp_unit_to_assignment; eauto. }
  destruct Hfront as [Hbefore Hsupported].
  split.
  - intros k Hkrange.
    unfold no_active_clause_at.
    intros c' Hinc Hactive.
    assert (Hkold : 0 <= k < current_level old).
    { unfold new in Hkrange; simpl in Hkrange; exact Hkrange. }
    apply (Hbefore k Hkold c' Hinc).
    assert (Hrestrict : restrict_to_level new k = restrict_to_level old k).
    { unfold new, rx.
      apply restrict_before_unit_extend__bcp_unit_to_assignment;
        [exact Hnone|].
      rewrite <- Hcur; lia. }
    rewrite <- Hrestrict; exact Hactive.
  - destruct (Z.eq_dec d 0) as [Hd0|Hd0].
    + left; unfold new; simpl; rewrite Hcur, Hd0; reflexivity.
    + right.
      intros c' Hinc Hactive_new.
      assert (Holdrestrict :
        restrict_to_level old (current_level old) = assignment old).
      { apply restrict_current_eq_assignment__bcp_unit_to_assignment;
          assumption. }
      assert (Hnewrestrict :
        restrict_to_level new (current_level new) = assignment new).
      { apply restrict_current_eq_assignment__bcp_unit_to_assignment;
          assumption. }
      rewrite Hnewrestrict in Hactive_new.
      destruct (clause_mem_dec (falsified_literal x b) c') as
        [Hfalsified|Hnofalsified].
      * exists (falsified_literal x b); split; [exact Hfalsified|].
        unfold literal_false_at_level.
        split.
        -- rewrite Hnewrestrict.
           apply eval_falsified_literal_false__bcp_unit_to_assignment.
           unfold new; apply unit_extend_assignment_same__bcp_unit_to_assignment.
        -- replace (literal_var (falsified_literal x b)) with x
             by (destruct b; reflexivity).
           unfold new.
           rewrite unit_extend_level_same__bcp_unit_to_assignment.
           change (Some d = Some (current_level old)).
           rewrite Hcur; reflexivity.
      * assert (Hnosatisfying : ~ In (satisfying_literal x b) c').
        { intro Hsat.
          destruct Hactive_new as [Htrue_new Hun_new].
          assert (Heval_sat :
            eval_partial_literal (assignment new) (satisfying_literal x b) =
              Some true).
          { apply eval_satisfying_literal_true__bcp_unit_to_assignment.
            unfold new; apply unit_extend_assignment_same__bcp_unit_to_assignment. }
          pose proof
            (clause_true_count_member_true__bcp_unit_to_assignment
              (assignment new) c' (satisfying_literal x b) Hsat Heval_sat);
            lia. }
        assert (Hnovar : forall l, In l c' -> literal_var l <> x).
        { intros l Hl Hlx.
          destruct l as [y|y]; cbn in Hlx; subst y;
            destruct b; cbn [satisfying_literal falsified_literal] in *;
            contradiction. }
        destruct (literal_counts_no_var__bcp_unit_to_assignment
          x b c' Hnovar) as [Hvarcount Htruecount].
        destruct (clause_counts_assign (assignment old) x b c' Hnone) as
          [Hunassigned_eq Htrue_eq].
        assert (Hactive_old : active_frontier_clause (assignment old) c').
        { unfold active_frontier_clause in *.
          destruct Hactive_new as [Hnewtrue Hnewunassigned].
          change
            (clause_true_count
              (partial_mapping_update (assignment old) x b) c' = 0)
            in Hnewtrue.
          change
            (clause_unassigned_count
              (partial_mapping_update (assignment old) x b) c' <= 1)
            in Hnewunassigned.
          rewrite Hvarcount in Hunassigned_eq.
          rewrite Htruecount in Htrue_eq.
          split.
          - rewrite Htrue_eq in Hnewtrue; lia.
          - rewrite Hunassigned_eq in Hnewunassigned; lia. }
        assert (Hactive_old_restrict :
          active_frontier_clause
            (restrict_to_level old (current_level old)) c').
        { rewrite Holdrestrict; exact Hactive_old. }
        destruct Hsupported as [Hcur0|Hsupported]; [congruence|].
        destruct (Hsupported c' Hinc Hactive_old_restrict) as
          [l [Hl [Heval_old Hlevel_old]]].
        exists l; split; [exact Hl|].
        assert (Hlx : literal_var l <> x).
        { intro Heq.
          assert (Hnone_restrict :
            restrict_to_level old (current_level old) (literal_var l) = None).
          { unfold restrict_to_level; rewrite Heq, Hnone; reflexivity. }
          pose proof
            (eval_partial_literal_unassigned__bcp_unit_to_assignment
              (restrict_to_level old (current_level old)) l Hnone_restrict);
            congruence. }
        unfold literal_false_at_level.
        split.
        -- rewrite Hnewrestrict.
           unfold new.
           rewrite unit_extend_eval_other__bcp_unit_to_assignment by exact Hlx.
           rewrite <- Holdrestrict; exact Heval_old.
        --
           unfold new.
           rewrite unit_extend_level_other__bcp_unit_to_assignment by exact Hlx.
           exact Hlevel_old.
Qed.
Lemma snapshot_assignment_some_range__bcp_unit_to_assignment :
  forall n snap x b,
    snapshot_assignment n snap x = Some b -> var_in_range n x.
Proof.
  intros n snap x b Hassign.
  unfold snapshot_assignment in Hassign.
  destruct (andb (Z.leb 0 x) (Z.ltb x n)) eqn:Hguard; [|discriminate].
  apply andb_true_iff in Hguard; destruct Hguard as [Hx0 Hxn].
  split; [apply Z.leb_le|apply Z.ltb_lt]; assumption.
Qed.
Lemma snapshot_unit_assignment_same__bcp_unit_to_assignment :
  forall n live snap x b d reason,
    snapshot_lengths n live snap -> var_in_range n x ->
    snapshot_assignment n
      ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => {| snap_values := replace_Znth x (if b then 1 else 0) (snap_values snap); snap_reasons := replace_Znth x reason (snap_reasons snap); snap_levels := replace_Znth x d (snap_levels snap); snap_rows := snap_rows snap; snap_states := snap_states snap; snap_true_counts := snap_true_counts snap; snap_unassigned := snap_unassigned snap |}) snap x b d reason) x =
    Some b.
Proof.
  intros n live snap x b d reason Hlength [Hx0 Hxn].
  unfold snapshot_assignment;
    simpl.
  assert (Hguard : andb (Z.leb 0 x) (Z.ltb x n) = true).
  { apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; assumption. }
  rewrite Hguard.
  destruct Hlength as [Hv _].
  rewrite Znth_replace_Znth_Same by (rewrite Hv; lia).
  destruct b; reflexivity.
Qed.
Lemma snapshot_unit_assignment_other__bcp_unit_to_assignment :
  forall n live snap x b d reason y,
    snapshot_lengths n live snap -> var_in_range n x -> y <> x ->
    snapshot_assignment n
      ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => {| snap_values := replace_Znth x (if b then 1 else 0) (snap_values snap); snap_reasons := replace_Znth x reason (snap_reasons snap); snap_levels := replace_Znth x d (snap_levels snap); snap_rows := snap_rows snap; snap_states := snap_states snap; snap_true_counts := snap_true_counts snap; snap_unassigned := snap_unassigned snap |}) snap x b d reason) y =
    snapshot_assignment n snap y.
Proof.
  intros n live snap x b d reason y Hlength [Hx0 Hxn] Hyx.
  unfold snapshot_assignment;
    simpl.
  destruct (andb (Z.leb 0 y) (Z.ltb y n)) eqn:Hguard; [|reflexivity].
  apply andb_true_iff in Hguard; destruct Hguard as [Hy0 Hyn].
  apply Z.leb_le in Hy0; apply Z.ltb_lt in Hyn.
  destruct Hlength as [Hv _].
  rewrite Znth_replace_Znth_Diff; try (rewrite Hv; lia); try lia.
  reflexivity.
Qed.
Lemma snapshot_unit_assignment_eq__bcp_unit_to_assignment :
  forall n live snap x b d reason,
    snapshot_lengths n live snap -> var_in_range n x ->
    snapshot_assignment n
      ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => {| snap_values := replace_Znth x (if b then 1 else 0) (snap_values snap); snap_reasons := replace_Znth x reason (snap_reasons snap); snap_levels := replace_Znth x d (snap_levels snap); snap_rows := snap_rows snap; snap_states := snap_states snap; snap_true_counts := snap_true_counts snap; snap_unassigned := snap_unassigned snap |}) snap x b d reason) =
    partial_mapping_update (snapshot_assignment n snap) x b.
Proof.
  intros n live snap x b d reason Hlength Hx.
  apply functional_extensionality; intro y.
  destruct (Z.eq_dec y x) as [->|Hyx].
  - rewrite (snapshot_unit_assignment_same__bcp_unit_to_assignment
      n live snap x b d reason Hlength Hx).
    symmetry; apply partial_mapping_update_eq.
  - rewrite (snapshot_unit_assignment_other__bcp_unit_to_assignment
      n live snap x b d reason y Hlength Hx Hyx).
    symmetry; apply partial_mapping_update_neq; lia.
Qed.
Lemma snapshot_unit_level_eq__bcp_unit_to_assignment :
  forall n live snap x b d reason,
    snapshot_lengths n live snap -> var_in_range n x ->
    snapshot_level n
      ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => {| snap_values := replace_Znth x (if b then 1 else 0) (snap_values snap); snap_reasons := replace_Znth x reason (snap_reasons snap); snap_levels := replace_Znth x d (snap_levels snap); snap_rows := snap_rows snap; snap_states := snap_states snap; snap_true_counts := snap_true_counts snap; snap_unassigned := snap_unassigned snap |}) snap x b d reason) =
    total_mapping_update (snapshot_level n snap) x (Some d).
Proof.
  intros n live snap x b d reason Hlength Hx.
  apply functional_extensionality; intro y.
  destruct (Z.eq_dec y x) as [->|Hyx].
  - unfold snapshot_level.
    rewrite (snapshot_unit_assignment_same__bcp_unit_to_assignment
      n live snap x b d reason Hlength Hx).
    rewrite total_mapping_update_eq.
    simpl.
    destruct Hlength as [_ [_ [Hl _]]].
    rewrite Znth_replace_Znth_Same by
      (rewrite Hl; destruct Hx; lia).
    reflexivity.
  - unfold snapshot_level.
    rewrite (snapshot_unit_assignment_other__bcp_unit_to_assignment
      n live snap x b d reason y Hlength Hx Hyx).
    rewrite total_mapping_update_neq by lia.
    destruct (snapshot_assignment n snap y) as [bv|] eqn:Hassign;
      [|reflexivity].
    pose proof
      (snapshot_assignment_some_range__bcp_unit_to_assignment
        n snap y bv Hassign) as Hy.
    simpl.
    destruct Hlength as [_ [_ [Hl _]]].
    destruct Hx as [Hx0 Hxn]; destruct Hy as [Hy0 Hyn].
    rewrite Znth_replace_Znth_Diff; try (rewrite Hl; lia); try lia.
    reflexivity.
Qed.
Lemma snapshot_unit_reason_eq__bcp_unit_to_assignment :
  forall n live snap x b d reason,
    snapshot_lengths n live snap -> var_in_range n x -> 0 <= reason ->
    snapshot_reason n
      ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => {| snap_values := replace_Znth x (if b then 1 else 0) (snap_values snap); snap_reasons := replace_Znth x reason (snap_reasons snap); snap_levels := replace_Znth x d (snap_levels snap); snap_rows := snap_rows snap; snap_states := snap_states snap; snap_true_counts := snap_true_counts snap; snap_unassigned := snap_unassigned snap |}) snap x b d reason) =
    total_mapping_update (snapshot_reason n snap) x (Some reason).
Proof.
  intros n live snap x b d reason Hlength Hx Hreason.
  apply functional_extensionality; intro y.
  destruct (Z.eq_dec y x) as [->|Hyx].
  - unfold snapshot_reason.
    rewrite (snapshot_unit_assignment_same__bcp_unit_to_assignment
      n live snap x b d reason Hlength Hx).
    rewrite total_mapping_update_eq.
    simpl.
    destruct Hlength as [_ [Hr _]].
    rewrite Znth_replace_Znth_Same by
      (rewrite Hr; destruct Hx; lia).
    assert (Hneq : Z.eqb reason (-1) = false) by (apply Z.eqb_neq; lia).
    rewrite Hneq; reflexivity.
  - unfold snapshot_reason.
    rewrite (snapshot_unit_assignment_other__bcp_unit_to_assignment
      n live snap x b d reason y Hlength Hx Hyx).
    rewrite total_mapping_update_neq by lia.
    destruct (snapshot_assignment n snap y) as [bv|] eqn:Hassign;
      [|reflexivity].
    pose proof
      (snapshot_assignment_some_range__bcp_unit_to_assignment
        n snap y bv Hassign) as Hy.
    simpl.
    destruct Hlength as [_ [Hr _]].
    destruct Hx as [Hx0 Hxn]; destruct Hy as [Hy0 Hyn].
    rewrite Znth_replace_Znth_Diff; try (rewrite Hr; lia); try lia.
    reflexivity.
Qed.
Lemma snapshot_unit_view_eq__bcp_unit_to_assignment :
  forall n live snap ranks logical_dl x b reason c,
    snapshot_lengths n live snap -> var_in_range n x -> 0 <= reason ->
    cdcl_view_of_snapshot n
      ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => {| snap_values := replace_Znth x (if b then 1 else 0) (snap_values snap); snap_reasons := replace_Znth x reason (snap_reasons snap); snap_levels := replace_Znth x d (snap_levels snap); snap_rows := snap_rows snap; snap_states := snap_states snap; snap_true_counts := snap_true_counts snap; snap_unassigned := snap_unassigned snap |})
        snap x b logical_dl reason)
      ((fun (ranks : Z -> option nat) (x : Z) (rx : nat) => total_mapping_update ranks x (Some rx)) ranks x
        (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c)) ranks c)))
      logical_dl =
    (fun (old : cdcl_view) (x : Z) (b : bool) (d reason : Z) (rx : nat) => {| assignment := partial_mapping_update (assignment old) x b; level_of := total_mapping_update (level_of old) x (Some d); reason_of := total_mapping_update (reason_of old) x (Some reason); assignment_rank := total_mapping_update (assignment_rank old) x (Some rx); installed_clauses := installed_clauses old; current_level := current_level old |})
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      x b logical_dl reason
      (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c)) ranks c)).
Proof.
  intros n live snap ranks logical_dl x b reason c Hlength Hx Hreason.
  pose proof (snapshot_unit_assignment_eq__bcp_unit_to_assignment
    n live snap x b logical_dl reason Hlength Hx) as Hassignment.
  pose proof (snapshot_unit_level_eq__bcp_unit_to_assignment
    n live snap x b logical_dl reason Hlength Hx) as Hlevel.
  pose proof (snapshot_unit_reason_eq__bcp_unit_to_assignment
    n live snap x b logical_dl reason Hlength Hx Hreason) as Hreason_eq.
  unfold cdcl_view_of_snapshot.
  simpl in *.
  rewrite Hassignment, Hlevel, Hreason_eq.
  reflexivity.
Qed.
Lemma snapshot_unit_stable_assigns__bcp_unit_to_assignment :
  forall n live snap ranks logical_dl x b reason c,
    snapshot_lengths n live snap -> var_in_range n x -> 0 <= reason ->
    snapshot_assignment n snap x = None ->
    nth_error
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl))
      (Z.to_nat reason) = Some c ->
    clause_unit (snapshot_assignment n snap) c ->
    In (satisfying_literal x b) c ->
    stable_search_facts n snap ranks logical_dl ->
    stable_search_facts n
      ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => {| snap_values := replace_Znth x (if b then 1 else 0) (snap_values snap); snap_reasons := replace_Znth x reason (snap_reasons snap); snap_levels := replace_Znth x d (snap_levels snap); snap_rows := snap_rows snap; snap_states := snap_states snap; snap_true_counts := snap_true_counts snap; snap_unassigned := snap_unassigned snap |})
        snap x b logical_dl reason)
      ((fun (ranks : Z -> option nat) (x : Z) (rx : nat) => total_mapping_update ranks x (Some rx)) ranks x
        (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c)) ranks c)))
      logical_dl /\
    assigns_one (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n
        ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => {| snap_values := replace_Znth x (if b then 1 else 0) (snap_values snap); snap_reasons := replace_Znth x reason (snap_reasons snap); snap_levels := replace_Znth x d (snap_levels snap); snap_rows := snap_rows snap; snap_states := snap_states snap; snap_true_counts := snap_true_counts snap; snap_unassigned := snap_unassigned snap |})
          snap x b logical_dl reason)
        ((fun (ranks : Z -> option nat) (x : Z) (rx : nat) => total_mapping_update ranks x (Some rx)) ranks x
          (S ((fun (ranks : Z -> option nat) (c : clause) => fold_right Nat.max O (map (fun l => match ranks (literal_var l) with Some r => r | None => O end) c)) ranks c)))
        logical_dl)
      x b logical_dl reason.
Proof.
  intros n live snap ranks logical_dl x b reason c Hlength Hx Hreason
    Hnone Hnth Hunit Hin Hstable.
  unfold stable_search_facts in Hstable; simpl in Hstable.
  destruct Hstable as [Hground [Hclosed Hfront]].
  pose proof (snapshot_unit_view_eq__bcp_unit_to_assignment
    n live snap ranks logical_dl x b reason c Hlength Hx Hreason) as Hview.
  split.
  - unfold stable_search_facts; simpl.
    rewrite Hview.
    split.
    + eapply grounded_unit_extend__bcp_unit_to_assignment; eauto;
        reflexivity.
    + split.
      * eapply closed_levels_unit_extend__bcp_unit_to_assignment; eauto;
          reflexivity.
      * eapply frontier_closed_unit_extend__bcp_unit_to_assignment; eauto;
          reflexivity.
  - rewrite Hview.
    eapply assigns_one_new_unit__bcp_unit_to_assignment; eauto.
Qed.
Lemma literal_var_count_member__bcp_unit_to_assignment :
  forall x c l,
    In l c -> literal_var l = x -> 1 <= literal_var_count x c.
Proof.
  intros x c; induction c as [|a c IH]; intros l Hin Hvar.
  - contradiction.
  - cbn [literal_var_count]; simpl in Hin.
    destruct Hin as [->|Hin].
    + rewrite Hvar, Z.eqb_refl.
      pose proof (literal_var_count_nonneg x c); lia.
    + destruct (Z.eqb (literal_var a) x);
        specialize (IH l Hin Hvar); lia.
Qed.
Lemma literal_true_count_member_satisfying__bcp_unit_to_assignment :
  forall x b c,
    In (satisfying_literal x b) c ->
    1 <= literal_true_at_count x b c.
Proof.
  intros x b c; induction c as [|a c IH]; intro Hin.
  - contradiction.
  - cbn [literal_true_at_count]; simpl in Hin.
    destruct Hin as [->|Hin].
    + assert (Hvar :
        Z.eqb (literal_var (satisfying_literal x b)) x = true).
      { destruct b; cbn [satisfying_literal literal_var];
          apply Z.eqb_refl. }
      rewrite Hvar.
      assert (Heval : eval_literal (fun _ : Z => b)
        (satisfying_literal x b) = true).
      { destruct b; reflexivity. }
      rewrite Heval.
      pose proof (literal_true_at_count_nonneg x b c); lia.
    + destruct (Z.eqb (literal_var a) x);
        [destruct (eval_literal (fun _ : Z => b) a)|];
        specialize (IH Hin); lia.
Qed.
Lemma literal_true_count_le_var_count__bcp_unit_to_assignment :
  forall x b c,
    literal_true_at_count x b c <= literal_var_count x c.
Proof.
  intros x b c; induction c as [|a c IH].
  - reflexivity.
  - cbn [literal_true_at_count literal_var_count].
    destruct (Z.eqb (literal_var a) x); [destruct (eval_literal (fun _ => b) a)|];
      lia.
Qed.
Lemma unit_assignment_counts__bcp_unit_to_assignment :
  forall sigma x b c,
    sigma x = None -> clause_unit sigma c ->
    In (satisfying_literal x b) c ->
    clause_true_count (partial_mapping_update sigma x b) c = 1 /\
    clause_unassigned_count (partial_mapping_update sigma x b) c = 0.
Proof.
  intros sigma x b c Hnone [Htrue Hunassigned] Hin.
  destruct (clause_counts_assign sigma x b c Hnone) as
    [Hunassigned_eq Htrue_eq].
  assert (Hvar_ge : 1 <= literal_var_count x c).
  { eapply literal_var_count_member__bcp_unit_to_assignment;
      [exact Hin|destruct b; reflexivity]. }
  pose proof
    (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment
      (partial_mapping_update sigma x b) c) as Hnew_unassigned_nonneg.
  assert (Hvar : literal_var_count x c = 1) by lia.
  assert (Htrue_ge : 1 <= literal_true_at_count x b c).
  { apply literal_true_count_member_satisfying__bcp_unit_to_assignment;
      exact Hin. }
  pose proof (literal_true_count_le_var_count__bcp_unit_to_assignment
    x b c) as Htrue_le.
  assert (Htrue_at : literal_true_at_count x b c = 1) by lia.
  split; lia.
Qed.
Lemma mixed_summaries_unit_seed__bcp_unit_to_assignment :
  forall n live cap snap x b unitcl,
    snapshot_lengths n live snap -> var_in_range n x ->
    0 <= unitcl < live -> 0 <= live <= cap ->
    snapshot_summaries_exact n live snap ->
    snapshot_assignment n snap x = None ->
    clause_unit (snapshot_assignment n snap)
      (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal)) ->
    List.In (satisfying_literal x b)
      (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal)) ->
    mixed_clause_summaries
      (snapshot_assignment n snap)
      (snapshot_assignment n
        ((fun (snap : dense_snapshot) (x : Z) (b : bool) (d reason : Z) => {| snap_values := replace_Znth x (if b then 1 else 0) (snap_values snap); snap_reasons := replace_Znth x reason (snap_reasons snap); snap_levels := replace_Znth x d (snap_levels snap); snap_rows := snap_rows snap; snap_states := snap_states snap; snap_true_counts := snap_true_counts snap; snap_unassigned := snap_unassigned snap |})
          snap x b 0 unitcl))
      (map dense_decode (snap_rows snap))
      (replace_Znth unitcl 0 (snap_states snap))
      (replace_Znth unitcl 1 (snap_true_counts snap))
      (replace_Znth unitcl 0 (snap_unassigned snap))
      live cap 0 (Some unitcl).
Proof.
  intros n live cap snap x b unitcl Hlength Hx Hunitcl Hcap
    Hsummaries Hnone Hunit Hin.
  destruct Hlength as
    [Hv [Hr [Hl [Hrows [Hstates [Htrue Hunassigned]]]]]].
  unfold mixed_clause_summaries.
  assert (Hmapped : Zlength (map dense_decode (snap_rows snap)) = live).
  { rewrite Zlength_correct, length_map, <- Zlength_correct; exact Hrows. }
  split; [symmetry; exact Hmapped|].
  split; [rewrite Zlength_replace_Znth, Hstates; reflexivity|].
  split; [rewrite Zlength_replace_Znth, Htrue; reflexivity|].
  split; [rewrite Zlength_replace_Znth, Hunassigned; reflexivity|].
  split; [exact Hcap|].
  split; [lia|].
  intros i Hi.
    split.
    + intro Hnew.
      destruct Hnew as [Hi0|Heq]; [lia|].
      inversion Heq; subst i.
      unfold summary_at, clause_summary_ok.
      rewrite Znth_replace_Znth_Same; try (rewrite Hstates; lia); try lia.
      rewrite Znth_replace_Znth_Same; try (rewrite Htrue; lia); try lia.
      rewrite Znth_replace_Znth_Same; try (rewrite Hunassigned; lia); try lia.
      pose proof (snapshot_unit_assignment_eq__bcp_unit_to_assignment
        n live snap x b 0 unitcl) as Hassignment.
      assert (Hlength : snapshot_lengths n live snap).
      { repeat split; assumption. }
      specialize (Hassignment Hlength Hx).
      rewrite Hassignment.
      destruct (unit_assignment_counts__bcp_unit_to_assignment
        (snapshot_assignment n snap) x b
        (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal))
        Hnone
        Hunit Hin) as [Hcount_true Hcount_unassigned].
      rewrite Hcount_true, Hcount_unassigned.
      unfold expected_clause_state.
      rewrite Hcount_true, Hcount_unassigned.
      cbn; repeat split; reflexivity.
    + intros [Hi0 Hneq].
      assert (Hine : i <> unitcl).
      { intro Heq; subst i; apply Hneq; reflexivity. }
      specialize (Hsummaries i Hi).
      unfold summary_at in *.
      rewrite Znth_replace_Znth_Diff; try (rewrite Hstates; lia); try lia.
      rewrite Znth_replace_Znth_Diff; try (rewrite Htrue; lia); try lia.
      rewrite Znth_replace_Znth_Diff; try (rewrite Hunassigned; lia); try lia.
      exact Hsummaries.
Qed.
Lemma summary_state_two_iff_unit__bcp_unit_to_assignment :
  forall sigma c state lit_state unassigned,
    clause_summary_ok sigma c state lit_state unassigned ->
    (state = 2 <-> clause_unit sigma c).
Proof.
  intros sigma c state lit_state unassigned [Hlit [Hun Hstate]].
  subst lit_state unassigned state.
  unfold expected_clause_state, clause_unit.
  pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment sigma c)
    as Ht_nonneg.
  pose proof (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment sigma c)
    as Hu_nonneg.
  split.
  - intro Heq.
    destruct ((0 <? clause_true_count sigma c)%Z) eqn:Ht.
    + discriminate.
    + apply Z.ltb_ge in Ht.
      destruct ((clause_unassigned_count sigma c =? 0)%Z) eqn:Hu0.
      * discriminate.
        * destruct ((clause_unassigned_count sigma c =? 1)%Z) eqn:Hu1.
        -- apply Z.eqb_eq in Hu1; lia.
        -- lia.
  - intros [Ht Hu]. rewrite Ht, Hu; reflexivity.
Qed.
Lemma clause_counts_zero_false__bcp_unit_to_assignment :
  forall sigma c,
    clause_true_count sigma c = 0 ->
    clause_unassigned_count sigma c = 0 ->
    clause_false sigma c.
Proof.
  intros sigma c; induction c as [|l c IH]; intros Htrue Hun l' Hin.
  - contradiction.
  - simpl in Hin; cbn -[eval_partial_literal Z.add] in Htrue, Hun.
    destruct (eval_partial_literal sigma l) as [[|]|] eqn:Heval.
    + pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment
        sigma c); lia.
    + destruct Hin as [<-|Hin]; [exact Heval|].
      eapply IH; eauto.
    + pose proof (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment
        sigma c); lia.
Qed.
Lemma summary_state_one_implies_false__bcp_unit_to_assignment :
  forall sigma c state lit_state unassigned,
    clause_summary_ok sigma c state lit_state unassigned ->
    state = 1 -> clause_false sigma c.
Proof.
  intros sigma c state lit_state unassigned [Hlit [Hun Hstate]] Hone.
  subst lit_state unassigned state.
  unfold expected_clause_state in Hone.
  destruct ((0 <? clause_true_count sigma c)%Z) eqn:Htrue; [discriminate|].
  destruct ((clause_unassigned_count sigma c =? 0)%Z) eqn:Hunassigned.
  - apply clause_counts_zero_false__bcp_unit_to_assignment.
    + apply Z.ltb_ge in Htrue.
      pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment sigma c);
        lia.
    + apply Z.eqb_eq in Hunassigned; exact Hunassigned.
  - destruct ((clause_unassigned_count sigma c =? 1)%Z) eqn:Huone
      in Hone; [discriminate|].
    apply Z.eqb_neq in Hunassigned.
    pose proof (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment
      sigma c); lia.
Qed.
Lemma coherent_snapshot_row_summary__bcp_unit_to_assignment :
  forall F n live original_count snap i,
    coherent_snapshot F n live original_count snap ->
    0 <= i < live ->
    exists row,
      nth_error (snap_rows snap) (Z.to_nat i) = Some row /\
      row_wf n row /\
      clause_summary_ok (snapshot_assignment n snap) (dense_decode row)
        (Znth i (snap_states snap) 0)
        (Znth i (snap_true_counts snap) 0)
        (Znth i (snap_unassigned snap) 0).
Proof.
  intros F n live original_count snap i Hcoh Hi.
  destruct Hcoh as [_ [_ [Hlengths [Hcells [Hsums _]]]]].
  destruct Hlengths as [_ [_ [_ [Hrows _]]]].
  destruct Hcells as [_ Hrows_wf].
  assert (Hsome : nth_error (snap_rows snap) (Z.to_nat i) <> None).
  { apply (proj2 (nth_error_Some (snap_rows snap) (Z.to_nat i))).
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct, Hrows. lia. }
  destruct (nth_error (snap_rows snap) (Z.to_nat i)) as [row|] eqn:Hrow;
    [|contradiction].
  exists row; split; [reflexivity|].
  split.
  - apply (proj1 (Forall_forall _ _)) with (x := row) in Hrows_wf.
    + exact Hrows_wf.
    + eapply nth_error_In; exact Hrow.
  - specialize (Hsums i Hi).
    unfold summary_at in Hsums.
    assert (Hdecode :
      Znth i (map dense_decode (snap_rows snap)) (@nil literal) =
        dense_decode row).
    { unfold Znth. eapply nth_error_nth.
      eapply map_nth_error; exact Hrow. }
    rewrite Hdecode in Hsums; exact Hsums.
Qed.
Lemma coherent_snapshot_unit_row__bcp_unit_to_assignment :
  forall F n live original_count snap i,
    coherent_snapshot F n live original_count snap ->
    0 <= i < live ->
    Znth i (snap_states snap) 0 = 2 ->
    exists row,
      nth_error (snap_rows snap) (Z.to_nat i) = Some row /\
      row_wf n row /\
      clause_unit (snapshot_assignment n snap) (dense_decode row) /\
      Znth i (snap_unassigned snap) 0 = 1.
Proof.
  intros F n live original_count snap i Hcoh Hi Hstate.
  destruct (coherent_snapshot_row_summary__bcp_unit_to_assignment
    F n live original_count snap i Hcoh Hi) as
    [row [Hrow [Hrowwf Hsummary]]].
  assert (Hunit : clause_unit (snapshot_assignment n snap) (dense_decode row)).
  { apply (proj1
      (summary_state_two_iff_unit__bcp_unit_to_assignment
        _ _ _ _ _ Hsummary)); exact Hstate. }
  exists row; split; [exact Hrow|].
  split; [exact Hrowwf|].
  split; [exact Hunit|].
  destruct Hsummary as [_ [Hun _]].
  destruct Hunit as [_ Hcount].
  lia.
Qed.
Lemma clause_unassigned_one_has_none__bcp_unit_to_assignment :
  forall sigma c,
    clause_unassigned_count sigma c = 1 ->
    exists l, In l c /\ eval_partial_literal sigma l = None.
Proof.
  intros sigma c; induction c as [|l c IH];
    cbn -[eval_partial_literal Z.add]; intro Hcount; [lia|].
  destruct (eval_partial_literal sigma l) as [b|] eqn:Heval.
  - destruct b.
    + cbn -[Z.add] in Hcount.
      destruct (IH Hcount) as [l' [Hin Hnone]].
      exists l'; split; [right; exact Hin|exact Hnone].
    + cbn -[Z.add] in Hcount.
      destruct (IH Hcount) as [l' [Hin Hnone]].
      exists l'; split; [right; exact Hin|exact Hnone].
  - exists l; split; [left; reflexivity|exact Heval].
Qed.
Lemma dense_decode_literal_range__bcp_unit_to_assignment :
  forall n row l,
    Zlength row = n ->
    In l (dense_decode row) ->
    var_in_range n (literal_var l).
Proof.
  intros n row l Hlen Hin.
  unfold dense_decode in Hin.
  split.
  - pose proof (dense_decode_from_var_lower_bound row 0 l Hin); lia.
  - pose proof
      (dense_decode_from_var_upper_bound__learning_row_and_scan
        row 0 l Hin); lia.
Qed.
Lemma snapshot_assignment_none_value__bcp_unit_to_assignment :
  forall n live snap x,
    snapshot_cells_wf n live snap ->
    var_in_range n x ->
    snapshot_assignment n snap x = None ->
    Znth x (snap_values snap) (-1) = -1.
Proof.
  intros n live snap x [Hvars Hrows] [Hx0 Hxn] Hnone.
  specialize (Hvars x (conj Hx0 Hxn)).
  cbn in Hvars.
  unfold snapshot_assignment in Hnone.
  assert (Hguard : andb ((0 <=? x)%Z) ((x <? n)%Z) = true).
  { apply andb_true_iff; split.
    - apply Z.leb_le; exact Hx0.
    - apply Z.ltb_lt; exact Hxn. }
  rewrite Hguard in Hnone.
  destruct Hvars as [[Hv|[Hv|Hv]] _]; rewrite Hv in *; cbn in Hnone;
    try discriminate; reflexivity.
Qed.
Lemma unit_dense_row_candidate__bcp_unit_to_assignment :
  forall n live snap row,
    snapshot_cells_wf n live snap ->
    row_wf n row ->
    clause_unit (snapshot_assignment n snap) (dense_decode row) ->
    exists x,
      0 <= x < n /\
      Znth x (snap_values snap) (-1) = -1 /\
      Znth x row 0 <> 0.
Proof.
  intros n live snap row Hcells [Hrowlen Hrowdomain] [Htrue Hunassigned].
  destruct (clause_unassigned_one_has_none__bcp_unit_to_assignment
    (snapshot_assignment n snap) (dense_decode row) Hunassigned) as
    [l [Hin Hnone]].
  pose proof (dense_decode_literal_range__bcp_unit_to_assignment
    n row l Hrowlen Hin) as Hrange.
  destruct l as [x|x].
  - change (var_in_range n x) in Hrange.
    assert (Hassign : snapshot_assignment n snap x = None).
    { destruct (snapshot_assignment n snap x) as [b|] eqn:Hassign;
        [unfold eval_partial_literal, literal_var in Hnone;
         rewrite Hassign in Hnone; discriminate|reflexivity]. }
    exists x; split; [exact Hrange|].
    split.
    + apply (snapshot_assignment_none_value__bcp_unit_to_assignment
        n live snap x Hcells Hrange).
      exact Hassign.
    + apply (proj2 (dense_decode_pos n row x
        (conj Hrowlen Hrowdomain) Hrange)) in Hin; lia.
  - change (var_in_range n x) in Hrange.
    assert (Hassign : snapshot_assignment n snap x = None).
    { destruct (snapshot_assignment n snap x) as [b|] eqn:Hassign;
        [unfold eval_partial_literal, literal_var in Hnone;
         rewrite Hassign in Hnone; discriminate|reflexivity]. }
    exists x; split; [exact Hrange|].
    split.
    + apply (snapshot_assignment_none_value__bcp_unit_to_assignment
        n live snap x Hcells Hrange).
      exact Hassign.
    + apply (proj2 (dense_decode_neg n row x
        (conj Hrowlen Hrowdomain) Hrange)) in Hin; lia.
Qed.
Lemma snapshot_value_defaults_eq__bcp_unit_to_assignment :
  forall F n live original_count snap x d d',
    coherent_snapshot F n live original_count snap ->
    var_in_range n x ->
    Znth x (snap_values snap) d = Znth x (snap_values snap) d'.
Proof.
  intros F n live original_count snap x d d' Hcoh Hx.
  assert (Hvalues : Zlength (snap_values snap) = n).
  { unfold coherent_snapshot, snapshot_lengths in Hcoh; tauto. }
  apply Znth_indep. rewrite Hvalues; exact Hx.
Qed.
Lemma unit_prefix_advance_assigned__bcp_unit_to_assignment :
  forall F n live original_count snap c i,
    coherent_snapshot F n live original_count snap ->
    0 <= i < n ->
    Znth i (snap_values snap) 0 <> -1 ->
    (forall x,
      0 <= x < i ->
      snapshot_assignment n snap x = None ->
      ~ (In (Pos x) c \/ In (Neg x) c)) ->
    forall x,
      0 <= x < i + 1 ->
      snapshot_assignment n snap x = None ->
      ~ (In (Pos x) c \/ In (Neg x) c).
Proof.
  intros F n live original_count snap c i Hcoh Hi Hcell Hprefix x Hx Hnone.
  destruct (Z_lt_ge_dec x i) as [Hxi|Hxi].
  - apply Hprefix; [lia|exact Hnone].
  - assert (x = i) by lia; subst x.
    assert (Hcells : snapshot_cells_wf n live snap).
    { unfold coherent_snapshot in Hcoh; tauto. }
    pose proof (snapshot_assignment_none_value__bcp_unit_to_assignment
      n live snap i Hcells Hi Hnone) as Hvalue.
    pose proof (snapshot_value_defaults_eq__bcp_unit_to_assignment
      F n live original_count snap i 0 (-1) Hcoh Hi) as Hdefaults.
    exfalso; apply Hcell; rewrite Hdefaults; exact Hvalue.
Qed.
Lemma unit_prefix_advance_zero__bcp_unit_to_assignment :
  forall n row c i (sigma : partial_valuation),
    row_wf n row ->
    c = dense_decode row ->
    0 <= i < n ->
    Znth i row 0 = 0 ->
    (forall x,
      0 <= x < i ->
      sigma x = None ->
      ~ (In (Pos x) c \/ In (Neg x) c)) ->
    forall x,
      0 <= x < i + 1 ->
      sigma x = None ->
      ~ (In (Pos x) c \/ In (Neg x) c).
Proof.
  intros n row c i sigma Hrowwf -> Hi Hzero Hprefix x Hx Hnone.
  destruct (Z_lt_ge_dec x i) as [Hxi|Hxi].
  - apply Hprefix; [lia|exact Hnone].
  - assert (x = i) by lia; subst x.
    apply (proj1 (dense_decode_zero n row i Hrowwf Hi)) in Hzero.
    tauto.
Qed.
(** ===== group: bcp_assignment_summary_a ===== *)
Lemma coherent_snapshot_row_wf__bcp_assignment_summary_a :
  forall F n live original_count snap i,
    coherent_snapshot F n live original_count snap ->
    0 <= i < live ->
    row_wf n (Znth i (snap_rows snap) (@nil Z)).
Proof.
  intros F n live original_count snap i Hcoherent Hi.
  unfold coherent_snapshot in Hcoherent.
  destruct Hcoherent as (_ & _ & Hlengths & Hcells & _ & _).
  destruct Hlengths as (_ & _ & _ & Hrows_length & _ & _ & _).
  destruct Hcells as (_ & Hrows_wf).
  rewrite Forall_forall in Hrows_wf.
  apply Hrows_wf.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hrows_length.
  lia.
Qed.
Lemma assigns_one_assignment_update__bcp_assignment_summary_a :
  forall old new x b d reason,
    assigns_one old new x b d reason ->
    assignment new = partial_mapping_update (assignment old) x b.
Proof.
  intros old new x b d reason Hassign.
  unfold assigns_one in Hassign.
  destruct Hassign as
    (Hold & Hnew & _ & _ & _ & Hother & _).
  apply functional_extensionality; intro y.
  destruct (Z.eq_dec x y) as [->|Hxy].
  - rewrite partial_mapping_update_eq; exact Hnew.
  - rewrite partial_mapping_update_neq by exact Hxy.
    specialize (Hother y ltac:(lia)).
    tauto.
Qed.
Lemma dense_decode_from_counts_before__bcp_assignment_summary_a :
  forall row base x b,
    x < base ->
    literal_var_count x (dense_decode_from base row) = 0 /\
    literal_true_at_count x b (dense_decode_from base row) = 0.
Proof.
  induction row as [|z row IH]; intros base x b Hlt; simpl.
  - split; reflexivity.
  - assert (Hneq : (base =? x) = false).
    { apply Z.eqb_neq; lia. }
    destruct (z =? 1) eqn:Hz1.
    + simpl. rewrite Hneq. apply IH; lia.
    + destruct (z =? -1) eqn:Hzm.
      * simpl. rewrite Hneq. apply IH; lia.
      * apply IH; lia.
Qed.
Lemma dense_decode_from_counts_pos__bcp_assignment_summary_a :
  forall row base i b,
    0 <= i < Zlength row ->
    Znth i row 0 = 1 ->
    literal_var_count (base + i) (dense_decode_from base row) = 1 /\
    literal_true_at_count (base + i) b (dense_decode_from base row) =
      if b then 1 else 0.
Proof.
  induction row as [|z row IH]; intros base i b Hi Hcell.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons in Hcell; subst z.
      simpl.
      pose proof
        (dense_decode_from_counts_before__bcp_assignment_summary_a
          row (base + 1) base b ltac:(lia)) as [Hvars Htrue].
      replace (base + 0) with base by lia.
      rewrite Z.eqb_refl, Hvars, Htrue.
      destruct b; split; reflexivity.
    + rewrite Znth_cons in Hcell by lia.
      simpl.
      assert (Hneq : (base =? base + i) = false).
      { apply Z.eqb_neq; lia. }
      destruct (z =? 1) eqn:Hz1.
      * simpl; rewrite Hneq.
        replace (base + i) with ((base + 1) + (i - 1)) by lia.
        apply IH; [lia|exact Hcell].
      * destruct (z =? -1) eqn:Hzm.
        -- simpl; rewrite Hneq.
           replace (base + i) with ((base + 1) + (i - 1)) by lia.
           apply IH; [lia|exact Hcell].
        -- replace (base + i) with ((base + 1) + (i - 1)) by lia.
           apply IH; [lia|exact Hcell].
Qed.
Lemma dense_decode_from_counts_neg__bcp_assignment_summary_a :
  forall row base i b,
    0 <= i < Zlength row ->
    Znth i row 0 = -1 ->
    literal_var_count (base + i) (dense_decode_from base row) = 1 /\
    literal_true_at_count (base + i) b (dense_decode_from base row) =
      if b then 0 else 1.
Proof.
  induction row as [|z row IH]; intros base i b Hi Hcell.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons in Hcell; subst z.
      simpl.
      pose proof
        (dense_decode_from_counts_before__bcp_assignment_summary_a
          row (base + 1) base b ltac:(lia)) as [Hvars Htrue].
      replace (base + 0) with base by lia.
      rewrite Z.eqb_refl, Hvars, Htrue.
      destruct b; split; reflexivity.
    + rewrite Znth_cons in Hcell by lia.
      simpl.
      assert (Hneq : (base =? base + i) = false).
      { apply Z.eqb_neq; lia. }
      destruct (z =? 1) eqn:Hz1.
      * simpl; rewrite Hneq.
        replace (base + i) with ((base + 1) + (i - 1)) by lia.
        apply IH; [lia|exact Hcell].
      * destruct (z =? -1) eqn:Hzm.
        -- simpl; rewrite Hneq.
           replace (base + i) with ((base + 1) + (i - 1)) by lia.
           apply IH; [lia|exact Hcell].
        -- replace (base + i) with ((base + 1) + (i - 1)) by lia.
           apply IH; [lia|exact Hcell].
Qed.
Lemma dense_decode_counts_pos__bcp_assignment_summary_a :
  forall n row x b,
    row_wf n row -> var_in_range n x -> Znth x row 0 = 1 ->
    literal_var_count x (dense_decode row) = 1 /\
    literal_true_at_count x b (dense_decode row) = if b then 1 else 0.
Proof.
  intros n row x b [Hlength _] Hx Hcell.
  unfold dense_decode.
  replace x with (0 + x) by lia.
  apply dense_decode_from_counts_pos__bcp_assignment_summary_a.
  - rewrite Hlength; exact Hx.
  - exact Hcell.
Qed.
Lemma dense_decode_counts_neg__bcp_assignment_summary_a :
  forall n row x b,
    row_wf n row -> var_in_range n x -> Znth x row 0 = -1 ->
    literal_var_count x (dense_decode row) = 1 /\
    literal_true_at_count x b (dense_decode row) = if b then 0 else 1.
Proof.
  intros n row x b [Hlength _] Hx Hcell.
  unfold dense_decode.
  replace x with (0 + x) by lia.
  apply dense_decode_from_counts_neg__bcp_assignment_summary_a.
  - rewrite Hlength; exact Hx.
  - exact Hcell.
Qed.
Lemma expected_clause_state_zero__bcp_assignment_summary_a :
  forall sigma c,
    expected_clause_state sigma c = 0 ->
    0 < clause_true_count sigma c.
Proof.
  intros sigma c Hstate.
  unfold expected_clause_state in Hstate.
  destruct (0 <? clause_true_count sigma c) eqn:Htrue.
  - apply Z.ltb_lt; exact Htrue.
  - apply Z.ltb_ge in Htrue.
    pose proof (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment sigma c).
    destruct (clause_unassigned_count sigma c =? 0) eqn:Hunassigned.
    + discriminate Hstate.
    + apply Z.eqb_neq in Hunassigned.
      destruct (clause_unassigned_count sigma c =? 1) eqn:Hunit.
      * discriminate Hstate.
      * lia.
Qed.
Lemma clause_summary_assign__bcp_assignment_summary_a :
  forall old new x b d reason c state true_count unassigned_count delta,
    assigns_one old new x b d reason ->
    clause_summary_ok (assignment old) c state true_count unassigned_count ->
    literal_var_count x c = 1 ->
    literal_true_at_count x b c = delta ->
    (delta = 1 \/ delta = 0 /\ state = 0) ->
    clause_summary_ok (assignment new) c 0
      (true_count + delta) (unassigned_count - 1).
Proof.
  intros old new x b d reason c state true_count unassigned_count delta
    Hassign Hsummary Hvar Htrue Hdelta.
  pose proof Hassign as Hassign_old.
  unfold assigns_one in Hassign_old.
  destruct Hassign_old as (Hold & _).
  pose proof (assigns_one_assignment_update__bcp_assignment_summary_a
    old new x b d reason Hassign) as Hupdate.
  pose proof (clause_counts_assign (assignment old) x b c Hold)
    as [Hunassigned_update Htrue_update].
  unfold clause_summary_ok in Hsummary |- *.
  destruct Hsummary as [Htrue_old [Hunassigned_old Hstate_old]].
  split.
  - rewrite Hupdate, Htrue_update, Htrue, <- Htrue_old; reflexivity.
  - split.
    + rewrite Hupdate, Hunassigned_update, Hvar, <- Hunassigned_old.
      reflexivity.
    + unfold expected_clause_state.
      rewrite Hupdate, Htrue_update, Htrue, <- Htrue_old.
      assert (Hpositive : 0 < true_count + delta).
      {
        destruct Hdelta as [->|[-> Hstate]].
        - pose proof
            (clause_true_count_nonnegative_base__bcp_unit_to_assignment
              (assignment old) c).
          lia.
        - rewrite Hstate in Hstate_old.
          symmetry in Hstate_old.
          apply expected_clause_state_zero__bcp_assignment_summary_a
            in Hstate_old.
          lia.
      }
      assert (Hpositiveb : (0 <? true_count + delta) = true).
      { apply Z.ltb_lt; exact Hpositive. }
      rewrite Hpositiveb.
      reflexivity.
Qed.
Lemma mixed_clause_summaries_old_at_processed__bcp_assignment_summary_a :
  forall old_sigma new_sigma rows states true_counts unassigned
      live cap processed exempt,
    mixed_clause_summaries old_sigma new_sigma rows states true_counts
      unassigned live cap processed (Some exempt) ->
    0 <= processed < live ->
    processed <> exempt ->
    summary_at old_sigma rows states true_counts unassigned processed.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned
    live cap processed exempt Hmixed Hprocessed Hneq.
  unfold mixed_clause_summaries in Hmixed.
  destruct Hmixed as (_ & _ & _ & _ & _ & _ & Hsummaries).
  specialize (Hsummaries processed Hprocessed).
  destruct Hsummaries as [_ Hold].
  apply Hold.
  split; [lia|].
  congruence.
Qed.
(** ===== group: bcp_assignment_summary_b ===== *)
Lemma literal_true_at_count_in__bcp_assignment_summary_b :
  forall x b c l,
    In l c ->
    literal_var l = x ->
    eval_literal (fun _ => b) l = true ->
    1 <= literal_true_at_count x b c.
Proof.
  intros x b c; induction c as [|h c IH]; intros l Hin Hvar Htrue;
    simpl in Hin.
  - contradiction.
  - change
      (1 <= if Z.eqb (literal_var h) x
             then if eval_literal (fun _ => b) h
                  then 1 + literal_true_at_count x b c
                  else literal_true_at_count x b c
             else literal_true_at_count x b c).
    destruct Hin as [<- | Hin].
    + rewrite Hvar, Z.eqb_refl, Htrue.
      pose proof (literal_true_at_count_nonneg x b c); lia.
    + specialize (IH l Hin Hvar Htrue).
      destruct (Z.eqb (literal_var h) x) eqn:Hhead.
      * destruct (eval_literal (fun _ => b) h) eqn:Hvalue.
        -- pose proof (literal_true_at_count_nonneg x b c); lia.
        -- exact IH.
      * exact IH.
Qed.
Lemma literal_true_at_count_complement__bcp_assignment_summary_b :
  forall x b c,
    literal_true_at_count x b c +
    literal_true_at_count x (negb b) c = literal_var_count x c.
Proof.
  intros x b c; induction c as [|l c IH].
  - reflexivity.
  - change
      ((if Z.eqb (literal_var l) x
        then if eval_literal (fun _ => b) l
             then 1 + literal_true_at_count x b c
             else literal_true_at_count x b c
        else literal_true_at_count x b c) +
       (if Z.eqb (literal_var l) x
        then if eval_literal (fun _ => negb b) l
             then 1 + literal_true_at_count x (negb b) c
             else literal_true_at_count x (negb b) c
        else literal_true_at_count x (negb b) c) =
       (if Z.eqb (literal_var l) x
        then 1 + literal_var_count x c
        else literal_var_count x c)).
    destruct (Z.eqb (literal_var l) x) eqn:Hvar.
    + destruct l; destruct b; unfold eval_literal, negb in *; lia.
    + exact IH.
Qed.
Lemma expected_clause_state_two_counts__bcp_assignment_summary_b :
  forall sigma c,
    expected_clause_state sigma c = 2 ->
    clause_true_count sigma c = 0 /\
    clause_unassigned_count sigma c = 1.
Proof.
  intros sigma c Hstate.
  unfold expected_clause_state in Hstate.
  destruct (Z.ltb 0 (clause_true_count sigma c)) eqn:Htrue.
  - discriminate.
  - apply Z.ltb_ge in Htrue.
    destruct (Z.eqb (clause_unassigned_count sigma c) 0)
      eqn:Hunassigned0.
    + discriminate.
    + destruct (Z.eqb (clause_unassigned_count sigma c) 1)
        eqn:Hunassigned1.
      * apply Z.eqb_eq in Hunassigned1.
        pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment sigma c).
        lia.
      * apply Z.eqb_neq in Hunassigned0, Hunassigned1.
        pose proof
          (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment sigma c).
        lia.
Qed.
Lemma bcp_unit_summary_satisfied__bcp_assignment_summary_b :
  forall old_sigma new_sigma c old_true old_unassigned x b,
    old_sigma x = None ->
    new_sigma = partial_mapping_update old_sigma x b ->
    clause_summary_ok old_sigma c 2 old_true old_unassigned ->
    In (satisfying_literal x b) c ->
    clause_summary_ok new_sigma c 0 (old_true + 1) (old_unassigned - 1).
Proof.
  intros old_sigma new_sigma c old_true old_unassigned x b
    Hnone Hupdate Hsummary Hin.
  destruct Hsummary as [Htrue [Hunassigned Hstate]].
  pose proof
    (expected_clause_state_two_counts__bcp_assignment_summary_b
      old_sigma c (eq_sym Hstate)) as [Htrue0 Hunassigned1].
  pose proof (clause_counts_assign old_sigma x b c Hnone) as [Hu Ht].
  assert (Hvar : literal_var_count x c = 1).
  {
    assert (Hlower : 1 <= literal_var_count x c).
    {
      eapply literal_var_count_member__bcp_unit_to_assignment; [exact Hin |].
      unfold satisfying_literal; destruct b; reflexivity.
    }
    pose proof
      (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment
        (partial_mapping_update old_sigma x b) c).
    lia.
  }
  assert (Hlittrue : literal_true_at_count x b c = 1).
  {
    pose proof
      (literal_true_count_le_var_count__bcp_unit_to_assignment x b c).
    assert (Hlower : 1 <= literal_true_at_count x b c).
    {
      eapply literal_true_at_count_in__bcp_assignment_summary_b;
        [exact Hin | |].
      - unfold satisfying_literal; destruct b; reflexivity.
      - unfold satisfying_literal, eval_literal; destruct b; reflexivity.
    }
    lia.
  }
  subst new_sigma.
  unfold clause_summary_ok.
  repeat split.
  - lia.
  - lia.
  - unfold expected_clause_state.
    rewrite Ht, Hu.
    rewrite Htrue0, Hunassigned1, Hvar, Hlittrue.
    reflexivity.
Qed.
Lemma bcp_unit_summary_falsified__bcp_assignment_summary_b :
  forall old_sigma new_sigma c old_true old_unassigned x b,
    old_sigma x = None ->
    new_sigma = partial_mapping_update old_sigma x b ->
    clause_summary_ok old_sigma c 2 old_true old_unassigned ->
    In (falsified_literal x b) c ->
    clause_summary_ok new_sigma c 1 old_true (old_unassigned - 1).
Proof.
  intros old_sigma new_sigma c old_true old_unassigned x b
    Hnone Hupdate Hsummary Hin.
  destruct Hsummary as [Htrue [Hunassigned Hstate]].
  pose proof
    (expected_clause_state_two_counts__bcp_assignment_summary_b
      old_sigma c (eq_sym Hstate)) as [Htrue0 Hunassigned1].
  pose proof (clause_counts_assign old_sigma x b c Hnone) as [Hu Ht].
  assert (Hvar : literal_var_count x c = 1).
  {
    assert (Hlower : 1 <= literal_var_count x c).
    {
      eapply literal_var_count_member__bcp_unit_to_assignment; [exact Hin |].
      unfold falsified_literal; destruct b; reflexivity.
    }
    pose proof
      (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment
        (partial_mapping_update old_sigma x b) c).
    lia.
  }
  assert (Hlitfalse : literal_true_at_count x b c = 0).
  {
    assert (Hcomplement : 1 <= literal_true_at_count x (negb b) c).
    {
      eapply literal_true_at_count_in__bcp_assignment_summary_b;
        [exact Hin | |].
      - unfold falsified_literal; destruct b; reflexivity.
      - unfold falsified_literal, eval_literal; destruct b; reflexivity.
    }
    pose proof
      (literal_true_at_count_complement__bcp_assignment_summary_b x b c).
    pose proof (literal_true_at_count_nonneg x b c).
    lia.
  }
  subst new_sigma.
  unfold clause_summary_ok.
  repeat split.
  - lia.
  - lia.
  - unfold expected_clause_state.
    rewrite Ht, Hu.
    rewrite Htrue0, Hunassigned1, Hvar, Hlitfalse.
    reflexivity.
Qed.
Lemma bcp_summary_assign_step__bcp_assignment_summary_b :
  forall old_sigma new_sigma rows states true_counts unassigned
    live cap i exempt new_state new_true new_unassigned,
    mixed_clause_summaries old_sigma new_sigma rows
      states true_counts unassigned live cap i (Some exempt) ->
    0 <= i < live ->
    i <> exempt ->
    summary_at new_sigma rows
      (replace_Znth i new_state states)
      (replace_Znth i new_true true_counts)
      (replace_Znth i new_unassigned unassigned) i ->
    mixed_clause_summaries old_sigma new_sigma rows
      (replace_Znth i new_state states)
      (replace_Znth i new_true true_counts)
      (replace_Znth i new_unassigned unassigned)
      live cap (i + 1) (Some exempt).
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned
    live cap i exempt new_state new_true new_unassigned
    Hmix Hi Hneq Hnew.
  unfold mixed_clause_summaries in Hmix |- *.
  destruct Hmix as
    [Hrows [Hstates [Htrue [Hunassigned [Hcap [Hprocessed Hall]]]]]].
  split; [exact Hrows |].
  split; [rewrite Zlength_replace_Znth; exact Hstates |].
  split; [rewrite Zlength_replace_Znth; exact Htrue |].
  split; [rewrite Zlength_replace_Znth; exact Hunassigned |].
  split; [exact Hcap |].
  split; [lia |].
  intros j Hj.
    specialize (Hall j Hj).
    split.
    + intros Hnew_source.
      destruct (Z.eq_dec j i) as [-> | Hji].
      * exact Hnew.
      * destruct Hall as [Hallnew Hallold].
        assert (Hsource : j < i \/ Some exempt = Some j) by
          (destruct Hnew_source as [Hjprocessed | Hjexempt];
           [left; lia | right; exact Hjexempt]).
        specialize (Hallnew Hsource).
        unfold summary_at in Hallnew |- *.
        repeat rewrite Znth_replace_Znth_Diff by lia.
        exact Hallnew.
    + intros [Hjprocessed Hjexempt].
      destruct Hall as [Hallnew Hallold].
      specialize (Hallold ltac:(split; [lia | exact Hjexempt])).
      assert (Hji : i <> j) by lia.
      unfold summary_at in Hallold |- *.
      repeat rewrite Znth_replace_Znth_Diff by lia.
      exact Hallold.
Qed.
Lemma bcp_summary_assign_satisfied_step__bcp_assignment_summary_b :
  forall old new x b d reason rows states true_counts unassigned
    live cap i exempt,
    assigns_one old new x b d reason ->
    mixed_clause_summaries (assignment old) (assignment new) rows
      states true_counts unassigned live cap i (Some exempt) ->
    0 <= i < live ->
    i <> exempt ->
    Znth i states 0 = 2 ->
    List.In (satisfying_literal x b) (Znth i rows (@nil literal)) ->
    mixed_clause_summaries (assignment old) (assignment new) rows
      (replace_Znth i 0 states)
      (replace_Znth i (Znth i true_counts 0 + 1) true_counts)
      (replace_Znth i (Znth i unassigned 0 - 1) unassigned)
      live cap (i + 1) (Some exempt).
Proof.
  intros old new x b d reason rows states true_counts unassigned
    live cap i exempt Hassign Hmix Hi Hneq Hstate Hin.
  pose proof Hmix as Hlengths.
  unfold mixed_clause_summaries in Hlengths.
  destruct Hlengths as
    [Hrows [Hstates [Htrue [Hunassigned [Hcap [Hprocessed Hall]]]]]].
  assert (Holdsummary :
    summary_at (assignment old) rows states true_counts unassigned i).
  {
    specialize (Hall i Hi).
    destruct Hall as [Hallnew Hallold].
    apply Hallold; split; [lia | congruence].
  }
  eapply bcp_summary_assign_step__bcp_assignment_summary_b;
    [exact Hmix | exact Hi | exact Hneq |].
  unfold summary_at in Holdsummary |- *.
  rewrite Znth_replace_Znth_Same by lia.
  rewrite Znth_replace_Znth_Same by lia.
  rewrite Znth_replace_Znth_Same by lia.
  rewrite Hstate in Holdsummary.
  eapply bcp_unit_summary_satisfied__bcp_assignment_summary_b.
  - pose proof Hassign as Hassign_copy.
    unfold assigns_one in Hassign_copy.
    destruct Hassign_copy as [Hnone Hrest].
    exact Hnone.
  - eapply assigns_one_assignment_update__bcp_assignment_summary_a.
    exact Hassign.
  - exact Holdsummary.
  - exact Hin.
Qed.
Lemma bcp_summary_assign_falsified_step__bcp_assignment_summary_b :
  forall old new x b d reason rows states true_counts unassigned
    live cap i exempt,
    assigns_one old new x b d reason ->
    mixed_clause_summaries (assignment old) (assignment new) rows
      states true_counts unassigned live cap i (Some exempt) ->
    0 <= i < live ->
    i <> exempt ->
    Znth i states 0 = 2 ->
    List.In (falsified_literal x b) (Znth i rows (@nil literal)) ->
    mixed_clause_summaries (assignment old) (assignment new) rows
      (replace_Znth i 1 states)
      true_counts
      (replace_Znth i (Znth i unassigned 0 - 1) unassigned)
      live cap (i + 1) (Some exempt).
Proof.
  intros old new x b d reason rows states true_counts unassigned
    live cap i exempt Hassign Hmix Hi Hneq Hstate Hin.
  pose proof Hmix as Hlengths.
  unfold mixed_clause_summaries in Hlengths.
  destruct Hlengths as
    [Hrows [Hstates [Htrue [Hunassigned [Hcap [Hprocessed Hall]]]]]].
  assert (Holdsummary :
    summary_at (assignment old) rows states true_counts unassigned i).
  {
    specialize (Hall i Hi).
    destruct Hall as [Hallnew Hallold].
    apply Hallold; split; [lia | congruence].
  }
  assert (Hnewsummary :
    summary_at (assignment new) rows
      (replace_Znth i 1 states)
      (replace_Znth i (Znth i true_counts 0) true_counts)
      (replace_Znth i (Znth i unassigned 0 - 1) unassigned) i).
  {
    unfold summary_at in Holdsummary |- *.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Hstate in Holdsummary.
    eapply bcp_unit_summary_falsified__bcp_assignment_summary_b.
    - pose proof Hassign as Hassign_copy.
      unfold assigns_one in Hassign_copy.
      destruct Hassign_copy as [Hnone Hrest].
      exact Hnone.
    - eapply assigns_one_assignment_update__bcp_assignment_summary_a.
      exact Hassign.
    - exact Holdsummary.
    - exact Hin.
  }
  pose proof
    (bcp_summary_assign_step__bcp_assignment_summary_b
      (assignment old) (assignment new) rows states true_counts unassigned
      live cap i exempt 1 (Znth i true_counts 0)
      (Znth i unassigned 0 - 1) Hmix Hi Hneq Hnewsummary) as Hstep.
  rewrite replace_Znth_Znth in Hstep by lia.
  exact Hstep.
Qed.
Lemma snapshot_replace_cell__bcp_assignment_summary_b :
  forall F n live original_count snap new_snap x z default,
    coherent_snapshot F n live original_count snap ->
    0 <= x < n ->
    snap_values new_snap = replace_Znth x z (snap_values snap) ->
    Znth x (snap_values new_snap) default = z.
Proof.
  intros F n live original_count snap new_snap x z default
    Hcoherent Hx Hreplace.
  unfold coherent_snapshot, snapshot_lengths in Hcoherent.
  destruct Hcoherent as
    [Hn [Horiginal [Hlengths [Hcells [Hsummaries Hsound]]]]].
  destruct Hlengths as
    [Hvalues [Hreasons [Hlevels [Hrows [Hstates [Htrue Hunassigned]]]]]].
  rewrite Hreplace.
  apply Znth_replace_Znth_Same; lia.
Qed.
Lemma coherent_snapshot_row_cell_domain__bcp_assignment_summary_b :
  forall F n live original_count snap i x,
    coherent_snapshot F n live original_count snap ->
    0 <= i < live ->
    0 <= x < n ->
    Znth x (Znth i (snap_rows snap) (@nil Z)) 0 = -1 \/
    Znth x (Znth i (snap_rows snap) (@nil Z)) 0 = 0 \/
    Znth x (Znth i (snap_rows snap) (@nil Z)) 0 = 1.
Proof.
  intros F n live original_count snap i x Hcoherent Hi Hx.
  unfold coherent_snapshot, snapshot_lengths, snapshot_cells_wf
    in Hcoherent.
  destruct Hcoherent as
    [Hn [Horiginal [Hlengths [Hcells [Hsummaries Hsound]]]]].
  destruct Hlengths as
    [Hvalues [Hreasons [Hlevels [Hrows [Hstates [Htrue Hunassigned]]]]]].
  destruct Hcells as [Hvalue_cells Hrow_wf].
  assert (Hrow_in :
    List.In (Znth i (snap_rows snap) (@nil Z)) (snap_rows snap)).
  {
    unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hrows.
    lia.
  }
  apply Forall_forall with
    (x := Znth i (snap_rows snap) (@nil Z)) in Hrow_wf;
    [| exact Hrow_in].
  eapply row_wf_cell_domain; eauto.
Qed.
Lemma assigns_one_replaced_value_decodes__bcp_assignment_summary_b :
  forall F n live original_count snap new_snap ranks new_ranks
    logical_dl x z b reason,
    coherent_snapshot F n live original_count snap ->
    0 <= x < n ->
    snap_values new_snap = replace_Znth x z (snap_values snap) ->
    assigns_one (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n new_snap new_ranks logical_dl)
      x b logical_dl reason ->
    decode_value_cell z = Some b.
Proof.
  intros F n live original_count snap new_snap ranks new_ranks
    logical_dl x z b reason Hcoherent Hx Hreplace Hassign.
  pose proof
    (snapshot_replace_cell__bcp_assignment_summary_b
      F n live original_count snap new_snap x z (-1)
      Hcoherent Hx Hreplace) as Hcell.
  unfold assigns_one in Hassign.
  destruct Hassign as
    [Hold [Hnew [Hlevel [Hreason [Hrank [Hframe Hclauses]]]]]].
  change (snapshot_assignment n new_snap x = Some b) in Hnew.
  unfold snapshot_assignment in Hnew.
  replace (Z.leb 0 x) with true in Hnew by
    (symmetry; apply Z.leb_le; lia).
  replace (Z.ltb x n) with true in Hnew by
    (symmetry; apply Z.ltb_lt; lia).
  cbn in Hnew.
  rewrite Hcell in Hnew.
  exact Hnew.
Qed.
Lemma coherent_snapshot_dense_satisfying_at__bcp_assignment_summary_b :
  forall F n live original_count snap i x (b : bool),
    coherent_snapshot F n live original_count snap ->
    0 <= i < live ->
    0 <= x < n ->
    Znth x (Znth i (snap_rows snap) (@nil Z)) 0 =
      (if b then 1 else -1) ->
    List.In (satisfying_literal x b)
      (Znth i (map dense_decode (snap_rows snap)) (@nil literal)).
Proof.
  intros F n live original_count snap i x b Hcoherent Hi Hx Hcell.
  pose proof Hcoherent as Hcoherent_copy.
  unfold coherent_snapshot, snapshot_lengths in Hcoherent_copy.
  destruct Hcoherent_copy as
    [Hn [Horiginal [Hlengths [Hcells [Hsummaries Hsound]]]]].
  destruct Hlengths as
    [Hvalues [Hreasons [Hlevels [Hrows [Hstates [Htrue Hunassigned]]]]]].
  unfold Znth at 1.
  rewrite (map_nth_len (list Z) clause dense_decode (snap_rows snap)
    (Z.to_nat i) (@nil literal) (@nil Z)) by
    (rewrite Zlength_correct in Hrows; lia).
  fold (Znth i (snap_rows snap) (@nil Z)).
  destruct Hcells as [Hvalue_cells Hrows_wf].
  assert (Hrow_wf : row_wf n (Znth i (snap_rows snap) (@nil Z))).
  {
    apply Forall_forall with
      (x := Znth i (snap_rows snap) (@nil Z)) in Hrows_wf.
    - exact Hrows_wf.
    - unfold Znth.
      apply nth_In.
      replace (List.length (snap_rows snap)) with
        (Z.to_nat (Zlength (snap_rows snap))).
      + apply Z2Nat.inj_lt; lia.
      + rewrite Zlength_correct. rewrite Nat2Z.id. reflexivity.
  }
  destruct b.
  - change
      (List.In (Pos x) (dense_decode (Znth i (snap_rows snap) (@nil Z)))).
    apply (proj1 (dense_decode_pos n
      (Znth i (snap_rows snap) (@nil Z)) x Hrow_wf Hx)).
    exact Hcell.
  - change
      (List.In (Neg x) (dense_decode (Znth i (snap_rows snap) (@nil Z)))).
    apply (proj1 (dense_decode_neg n
      (Znth i (snap_rows snap) (@nil Z)) x Hrow_wf Hx)).
    exact Hcell.
Qed.
Lemma coherent_snapshot_dense_falsified_at__bcp_assignment_summary_b :
  forall F n live original_count snap i x (b : bool),
    coherent_snapshot F n live original_count snap ->
    0 <= i < live ->
    0 <= x < n ->
    Znth x (Znth i (snap_rows snap) (@nil Z)) 0 =
      (if b then -1 else 1) ->
    List.In (falsified_literal x b)
      (Znth i (map dense_decode (snap_rows snap)) (@nil literal)).
Proof.
  intros F n live original_count snap i x b Hcoherent Hi Hx Hcell.
  pose proof Hcoherent as Hcoherent_copy.
  unfold coherent_snapshot, snapshot_lengths in Hcoherent_copy.
  destruct Hcoherent_copy as
    [Hn [Horiginal [Hlengths [Hcells [Hsummaries Hsound]]]]].
  destruct Hlengths as
    [Hvalues [Hreasons [Hlevels [Hrows [Hstates [Htrue Hunassigned]]]]]].
  unfold Znth at 1.
  rewrite (map_nth_len (list Z) clause dense_decode (snap_rows snap)
    (Z.to_nat i) (@nil literal) (@nil Z)) by
    (rewrite Zlength_correct in Hrows; lia).
  fold (Znth i (snap_rows snap) (@nil Z)).
  destruct Hcells as [Hvalue_cells Hrows_wf].
  assert (Hrow_wf : row_wf n (Znth i (snap_rows snap) (@nil Z))).
  {
    apply Forall_forall with
      (x := Znth i (snap_rows snap) (@nil Z)) in Hrows_wf.
    - exact Hrows_wf.
    - unfold Znth.
      apply nth_In.
      replace (List.length (snap_rows snap)) with
        (Z.to_nat (Zlength (snap_rows snap))).
      + apply Z2Nat.inj_lt; lia.
      + rewrite Zlength_correct. rewrite Nat2Z.id. reflexivity.
  }
  destruct b.
  - change
      (List.In (Neg x) (dense_decode (Znth i (snap_rows snap) (@nil Z)))).
    apply (proj1 (dense_decode_neg n
      (Znth i (snap_rows snap) (@nil Z)) x Hrow_wf Hx)).
    exact Hcell.
  - change
      (List.In (Pos x) (dense_decode (Znth i (snap_rows snap) (@nil Z)))).
    apply (proj1 (dense_decode_pos n
      (Znth i (snap_rows snap) (@nil Z)) x Hrow_wf Hx)).
    exact Hcell.
Qed.
Lemma expected_clause_state_one_counts__bcp_assignment_summary_b :
  forall sigma c,
    expected_clause_state sigma c = 1 ->
    clause_true_count sigma c = 0 /\
    clause_unassigned_count sigma c = 0.
Proof.
  intros sigma c Hstate.
  unfold expected_clause_state in Hstate.
  destruct (Z.ltb 0 (clause_true_count sigma c)) eqn:Htrue.
  - discriminate.
  - apply Z.ltb_ge in Htrue.
    destruct (Z.eqb (clause_unassigned_count sigma c) 0)
      eqn:Hunassigned.
    + apply Z.eqb_eq in Hunassigned.
      pose proof
        (clause_true_count_nonnegative_base__bcp_unit_to_assignment sigma c).
      lia.
    + destruct (Z.eqb (clause_unassigned_count sigma c) 1)
        eqn:Hunassigned1.
      * discriminate.
      * pose proof
          (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment sigma c).
        lia.
Qed.
Lemma clause_summary_state_one_false__bcp_assignment_summary_b :
  forall sigma c state true_count unassigned,
    clause_summary_ok sigma c state true_count unassigned ->
    state = 1 ->
    clause_false sigma c.
Proof.
  intros sigma c state true_count unassigned Hsummary Hstate.
  destruct Hsummary as [Htrue [Hunassigned Hexpected]].
  rewrite Hstate in Hexpected.
  pose proof
    (expected_clause_state_one_counts__bcp_assignment_summary_b
      sigma c (eq_sym Hexpected)) as [Htrue0 Hunassigned0].
  eapply clause_counts_zero_false__bcp_unit_to_assignment; eauto.
Qed.
Lemma assigns_one_satisfying_eval__bcp_assignment_summary_b :
  forall old new x b d reason,
    assigns_one old new x b d reason ->
    eval_partial_literal (assignment new) (satisfying_literal x b) = Some true.
Proof.
  intros old new x b d reason Hassign.
  unfold assigns_one in Hassign.
  destruct Hassign as [Hold [Hnew Hrest]].
  unfold satisfying_literal, eval_partial_literal.
  destruct b; cbn; rewrite Hnew; reflexivity.
Qed.
Lemma bcp_next_state_not_conflict__bcp_assignment_summary_b :
  forall old new x b d reason states true_counts unassigned
    live cap i exempt,
    assigns_one old new x b d reason ->
    mixed_clause_summaries (assignment old) (assignment new)
      (installed_clauses old) states true_counts unassigned
      live cap (i + 1) (Some exempt) ->
    no_conflict old ->
    0 <= i < live ->
    0 <= exempt < live ->
    List.In (satisfying_literal x b)
      (Znth exempt (installed_clauses old) (@nil literal)) ->
    Znth (i + 1) states 0 <> 1.
Proof.
  intros old new x b d reason states true_counts unassigned
    live cap i exempt Hassign Hmix Hno Hi Hexempt Hin.
  pose proof Hmix as Hmix_copy.
  unfold mixed_clause_summaries in Hmix_copy.
  destruct Hmix_copy as
    [Hrows [Hstates [Htrue [Hunassigned [Hcap [Hprocessed Hall]]]]]].
  destruct (Z_lt_dec (i + 1) live) as [Hnext | Hnext].
  - specialize (Hall (i + 1) ltac:(lia)).
    destruct Hall as [Hnew_summary Hold_summary].
    destruct (Z.eq_dec (i + 1) exempt) as [Heq | Hneq].
    + subst exempt.
      specialize (Hnew_summary ltac:(right; reflexivity)).
      intro Hstate.
      unfold summary_at in Hnew_summary.
      pose proof
        (clause_summary_state_one_false__bcp_assignment_summary_b
          (assignment new)
          (Znth (i + 1) (installed_clauses old) (@nil literal))
          (Znth (i + 1) states 0)
          (Znth (i + 1) true_counts 0)
          (Znth (i + 1) unassigned 0)
          Hnew_summary Hstate) as Hfalse.
      pose proof (Hfalse (satisfying_literal x b) Hin) as Heval_false.
      pose proof
        (assigns_one_satisfying_eval__bcp_assignment_summary_b
          old new x b d reason Hassign) as Heval_true.
      rewrite Heval_true in Heval_false; discriminate.
    + specialize (Hold_summary ltac:(split; [lia | congruence])).
      intro Hstate.
      unfold summary_at in Hold_summary.
      pose proof
        (clause_summary_state_one_false__bcp_assignment_summary_b
          (assignment old)
          (Znth (i + 1) (installed_clauses old) (@nil literal))
          (Znth (i + 1) states 0)
          (Znth (i + 1) true_counts 0)
          (Znth (i + 1) unassigned 0)
          Hold_summary Hstate) as Hfalse.
      unfold no_conflict in Hno.
      apply (Hno
        (Znth (i + 1) (installed_clauses old) (@nil literal))).
      * unfold Znth.
        apply nth_In.
        rewrite Zlength_correct in Hrows.
        lia.
      * exact Hfalse.
  - assert (Heq : i + 1 = live) by lia.
    rewrite Heq.
    unfold Znth.
    rewrite nth_overflow.
    + discriminate.
    + rewrite Zlength_correct in Hstates.
      lia.
Qed.
(** ===== group: bcp_assignment_summary_c ===== *)
Lemma row_wf_at__bcp_assignment_summary_c : forall n rows i,
  Forall (row_wf n) rows ->
  0 <= i < Zlength rows ->
  row_wf n (Znth i rows (@nil Z)).
Proof.
  intros n rows; induction rows as [|row rows IH]; intros i Hforall Hi.
  - rewrite Zlength_nil in Hi; lia.
  - inversion Hforall as [|? ? Hrow Hrows]; subst.
    rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + rewrite Znth0_cons; exact Hrow.
    + rewrite Znth_cons by lia.
      apply IH; [exact Hrows|].
      lia.
Qed.
Lemma coherent_snapshot_row_cell_domain__bcp_assignment_summary_c :
  forall F n live original_count snap i x,
    coherent_snapshot F n live original_count snap ->
    0 <= i < live -> var_in_range n x ->
    Znth x (Znth i (snap_rows snap) (@nil Z)) 0 = -1 \/
    Znth x (Znth i (snap_rows snap) (@nil Z)) 0 = 0 \/
    Znth x (Znth i (snap_rows snap) (@nil Z)) 0 = 1.
Proof.
  intros F n live original_count snap i x Hcoh Hi Hx.
  unfold coherent_snapshot in Hcoh.
  destruct Hcoh as [_ [_ [Hlens [Hcells _]]]].
  unfold snapshot_lengths in Hlens.
  destruct Hlens as [_ [_ [_ [Hrows_len _]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [_ Hrows].
  apply (row_wf_cell_domain n
    (Znth i (snap_rows snap) (@nil Z)) x); [|exact Hx].
  apply row_wf_at__bcp_assignment_summary_c; [exact Hrows|].
  rewrite Hrows_len; exact Hi.
Qed.
Lemma Znth_map_dense_decode__bcp_assignment_summary_c : forall rows i,
  0 <= i < Zlength rows ->
  Znth i (map dense_decode rows) (@nil literal) =
    dense_decode (Znth i rows (@nil Z)).
Proof.
  intros rows i Hi. apply Znth_map. exact Hi.
Qed.
(** ===== group: bcp_assignment_summary_d ===== *)
Lemma clause_counts_nonnegative__bcp_assignment_summary_d :
  forall sigma c,
    0 <= clause_true_count sigma c /\
    0 <= clause_unassigned_count sigma c.
Proof.
  intros sigma c; split.
  - induction c as [|l c IH]; [reflexivity|].
    cbn [clause_true_count].
    destruct (eval_partial_literal sigma l) as [[|]|].
    + change (0 <= 1 + clause_true_count sigma c); lia.
    + exact IH.
    + exact IH.
  - induction c as [|l c IH]; [reflexivity|].
    cbn [clause_unassigned_count].
    destruct (eval_partial_literal sigma l) as [[|]|].
    + exact IH.
    + exact IH.
    + change (0 <= 1 + clause_unassigned_count sigma c); lia.
Qed.
Lemma coherent_replaced_value_same__bcp_assignment_summary_d :
  forall F n live original_count snap new_values x z dflt,
    coherent_snapshot F n live original_count snap ->
    var_in_range n x ->
    new_values = replace_Znth x z (snap_values snap) ->
    Znth x new_values dflt = z.
Proof.
  intros F n live original_count snap new_values x z dflt
    Hcoh [Hx0 Hxn] Hnew.
  unfold coherent_snapshot in Hcoh.
  destruct Hcoh as [_ [_ [Hlengths _]]].
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as [Hvalues _].
  rewrite Hnew, Znth_replace_Znth_Same by (rewrite Hvalues; lia).
  reflexivity.
Qed.
Lemma assigns_one_replaced_zero_false__bcp_assignment_summary_d :
  forall F n live original_count snap new_snap ranks ranks1 logical_dl
      x d reason b,
    coherent_snapshot F n live original_count snap ->
    var_in_range n x ->
    snap_values new_snap = replace_Znth x 0 (snap_values snap) ->
    assigns_one (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n new_snap ranks1 logical_dl) x b d reason ->
    b = false.
Proof.
  intros F n live original_count snap new_snap ranks ranks1 logical_dl
    x d reason b Hcoh Hx Hvalues Hassign.
  pose proof (coherent_replaced_value_same__bcp_assignment_summary_d
    F n live original_count snap (snap_values new_snap) x 0 (-1)
    Hcoh Hx Hvalues) as Hcell.
  unfold assigns_one in Hassign.
  destruct Hassign as [_ [Hnew _]].
  simpl [cdcl_view_of_snapshot] in Hnew.
  unfold snapshot_assignment in Hnew.
  destruct Hx as [Hx0 Hxn].
  assert (Hguard : andb (0 <=? x)%Z (x <? n)%Z = true).
  { apply andb_true_iff; split;
      [apply Z.leb_le|apply Z.ltb_lt]; assumption. }
  rewrite Hguard in Hnew.
  rewrite Hcell in Hnew; simpl in Hnew.
  destruct b; [discriminate|reflexivity].
Qed.
Lemma assigns_one_replaced_one_true__bcp_assignment_summary_d :
  forall F n live original_count snap new_snap ranks ranks1 logical_dl
      x d reason b,
    coherent_snapshot F n live original_count snap ->
    var_in_range n x ->
    snap_values new_snap = replace_Znth x 1 (snap_values snap) ->
    assigns_one (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n new_snap ranks1 logical_dl) x b d reason ->
    b = true.
Proof.
  intros F n live original_count snap new_snap ranks ranks1 logical_dl
    x d reason b Hcoh Hx Hvalues Hassign.
  pose proof (coherent_replaced_value_same__bcp_assignment_summary_d
    F n live original_count snap (snap_values new_snap) x 1 (-1)
    Hcoh Hx Hvalues) as Hcell.
  unfold assigns_one in Hassign.
  destruct Hassign as [_ [Hnew _]].
  simpl [cdcl_view_of_snapshot] in Hnew.
  unfold snapshot_assignment in Hnew.
  destruct Hx as [Hx0 Hxn].
  assert (Hguard : andb (0 <=? x)%Z (x <? n)%Z = true).
  { apply andb_true_iff; split;
      [apply Z.leb_le|apply Z.ltb_lt]; assumption. }
  rewrite Hguard in Hnew.
  rewrite Hcell in Hnew; simpl in Hnew.
  destruct b; [reflexivity|discriminate].
Qed.
Lemma dense_decode_from_counts_at__bcp_assignment_summary_d :
  forall row base i b,
    0 <= i < Zlength row ->
    literal_var_count (base + i) (dense_decode_from base row) =
      (if Z.eqb (Znth i row 0) 1 then 1
       else if Z.eqb (Znth i row 0) (-1) then 1 else 0) /\
    literal_true_at_count (base + i) b (dense_decode_from base row) =
      (if Z.eqb (Znth i row 0) 1 then if b then 1 else 0
       else if Z.eqb (Znth i row 0) (-1) then if b then 0 else 1 else 0).
Proof.
  induction row as [|z row IH]; intros base i b Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons.
      replace (base + 0) with base by lia.
      pose proof
        (dense_decode_from_counts_before__bcp_assignment_summary_a
          row (base + 1) base b ltac:(lia)) as [Hbelow1 Hbelow2].
      simpl dense_decode_from.
      destruct (Z.eqb z 1) eqn:Hz1;
        destruct (Z.eqb z (-1)) eqn:Hzm;
        destruct b; simpl.
      all: try (apply Z.eqb_eq in Hz1);
        try (apply Z.eqb_eq in Hzm); try lia.
      all: rewrite ?Z.eqb_refl, ?Hbelow1, ?Hbelow2; split; reflexivity.
    + rewrite Znth_cons by lia.
      replace (base + i) with ((base + 1) + (i - 1)) by lia.
      specialize (IH (base + 1) (i - 1) b ltac:(lia)).
      assert (Hneq : Z.eqb base (base + 1 + (i - 1)) = false).
      { apply Z.eqb_neq; lia. }
      simpl dense_decode_from.
      destruct (Z.eqb z 1), (Z.eqb z (-1)); simpl; try rewrite Hneq; exact IH.
Qed.
Lemma dense_decode_counts_neg_true__bcp_assignment_summary_d :
  forall row x,
    0 <= x < Zlength row -> Znth x row 0 = -1 ->
    literal_var_count x (dense_decode row) = 1 /\
    literal_true_at_count x true (dense_decode row) = 0.
Proof.
  intros row x Hx Hcell.
  pose proof (dense_decode_from_counts_at__bcp_assignment_summary_d
    row 0 x true Hx) as H.
  unfold dense_decode; replace (0 + x) with x in H by lia.
  rewrite Hcell in H; simpl in H; exact H.
Qed.
Lemma dense_decode_counts_pos_false__bcp_assignment_summary_d :
  forall row x,
    0 <= x < Zlength row -> Znth x row 0 = 1 ->
    literal_var_count x (dense_decode row) = 1 /\
    literal_true_at_count x false (dense_decode row) = 0.
Proof.
  intros row x Hx Hcell.
  pose proof (dense_decode_from_counts_at__bcp_assignment_summary_d
    row 0 x false Hx) as H.
  unfold dense_decode; replace (0 + x) with x in H by lia.
  rewrite Hcell in H; simpl in H; exact H.
Qed.
Lemma dense_decode_counts_zero__bcp_assignment_summary_d :
  forall row x b,
    0 <= x < Zlength row -> Znth x row 0 = 0 ->
    literal_var_count x (dense_decode row) = 0 /\
    literal_true_at_count x b (dense_decode row) = 0.
Proof.
  intros row x b Hx Hcell.
  pose proof (dense_decode_from_counts_at__bcp_assignment_summary_d
    row 0 x b Hx) as H.
  unfold dense_decode; replace (0 + x) with x in H by lia.
  rewrite Hcell in H; simpl in H; exact H.
Qed.
Lemma clause_summary_assign_false__bcp_assignment_summary_d :
  forall old new x b d reason c state true_count unassigned_count new_state,
    assigns_one old new x b d reason ->
    clause_summary_ok (assignment old) c state true_count unassigned_count ->
    literal_var_count x c = 1 ->
    literal_true_at_count x b c = 0 ->
    state <> 0 -> state <> 1 -> state <> 2 ->
    ((state = -2 /\ new_state = 2) \/
     (state <> -2 /\ new_state = state + 1)) ->
    clause_summary_ok (assignment new) c new_state true_count
      (unassigned_count - 1).
Proof.
  intros old new x b d reason c state true_count unassigned_count
    new_state Hassign Hsummary Hvar Hlit Hstate0 Hstate1 Hstate2 Hnext.
  pose proof Hassign as Hassign_eq.
  pose proof (assigns_one_assignment_update__bcp_assignment_summary_a
    old new x b d reason Hassign_eq) as Heq.
  unfold assigns_one in Hassign.
  destruct Hassign as [Hold _].
  pose proof (clause_counts_assign (assignment old) x b c Hold)
    as [Hunassigned Htrue].
  rewrite Hvar in Hunassigned.
  rewrite Hlit in Htrue.
  unfold clause_summary_ok in Hsummary.
  destruct Hsummary as [Htrue_count [Hunassigned_count Hstate]].
  pose proof (clause_counts_nonnegative__bcp_assignment_summary_d
    (assignment old) c) as [Htrue_nonneg Hunassigned_nonneg].
  assert (Hshape :
    clause_true_count (assignment old) c = 0 /\
    2 <= clause_unassigned_count (assignment old) c /\
    state = - clause_unassigned_count (assignment old) c).
  {
    unfold expected_clause_state in Hstate.
    destruct (Z.ltb 0 (clause_true_count (assignment old) c))
      eqn:Hpositive.
    - apply Z.ltb_lt in Hpositive.
      exfalso; apply Hstate0; exact Hstate.
    - apply Z.ltb_ge in Hpositive.
      destruct (Z.eqb (clause_unassigned_count (assignment old) c) 0)
        eqn:Hunassigned0.
      + apply Z.eqb_eq in Hunassigned0.
        exfalso; apply Hstate1; exact Hstate.
      + apply Z.eqb_neq in Hunassigned0.
        destruct (Z.eqb (clause_unassigned_count (assignment old) c) 1)
          eqn:Hunassigned1.
        * apply Z.eqb_eq in Hunassigned1.
          exfalso; apply Hstate2; exact Hstate.
        * apply Z.eqb_neq in Hunassigned1.
          split; [lia|split; [lia|exact Hstate]].
  }
  destruct Hshape as [Htrue_zero [Hunassigned_ge Hstate_shape]].
  rewrite Heq.
  unfold clause_summary_ok.
  split; [lia|split; [lia|]].
  unfold expected_clause_state.
  rewrite Htrue, Hunassigned, Htrue_zero.
  cbn.
  destruct Hnext as [[Hstate_neg2 Hnew_state]|[Hstate_not_neg2 Hnew_state]].
  - subst new_state.
    assert (Htwo : clause_unassigned_count (assignment old) c = 2) by lia.
    rewrite Htwo; reflexivity.
  - subst new_state.
    assert (3 <= clause_unassigned_count (assignment old) c) by lia.
    assert (Hzero :
      Z.eqb (clause_unassigned_count (assignment old) c - 1) 0 = false).
    { apply Z.eqb_neq; lia. }
    assert (Hone :
      Z.eqb (clause_unassigned_count (assignment old) c - 1) 1 = false).
    { apply Z.eqb_neq; lia. }
    rewrite Hzero, Hone; lia.
Qed.
Lemma clause_summary_assign_absent__bcp_assignment_summary_d :
  forall old new x b d reason c state true_count unassigned_count,
    assigns_one old new x b d reason ->
    clause_summary_ok (assignment old) c state true_count unassigned_count ->
    literal_var_count x c = 0 ->
    literal_true_at_count x b c = 0 ->
    clause_summary_ok (assignment new) c state true_count unassigned_count.
Proof.
  intros old new x b d reason c state true_count unassigned_count
    Hassign Hsummary Hvar Hlit.
  pose proof Hassign as Hassign_eq.
  pose proof (assigns_one_assignment_update__bcp_assignment_summary_a
    old new x b d reason Hassign_eq) as Heq.
  unfold assigns_one in Hassign.
  destruct Hassign as [Hold _].
  pose proof (clause_counts_assign (assignment old) x b c Hold)
    as [Hunassigned Htrue].
  rewrite Hvar in Hunassigned.
  rewrite Hlit in Htrue.
  unfold clause_summary_ok in Hsummary.
  destruct Hsummary as [Htrue_count [Hunassigned_count Hstate]].
  rewrite Heq.
  unfold clause_summary_ok.
  split; [lia|split; [lia|]].
  unfold expected_clause_state.
  rewrite Htrue, Hunassigned.
  replace (clause_true_count (assignment old) c + 0)
    with (clause_true_count (assignment old) c) by lia.
  replace (clause_unassigned_count (assignment old) c - 0)
    with (clause_unassigned_count (assignment old) c) by lia.
  exact Hstate.
Qed.
Lemma summary_at_replace_current__bcp_assignment_summary_d :
  forall sigma rows states true_counts unassigned i state true_count unassigned_count,
    0 <= i < Zlength states ->
    0 <= i < Zlength true_counts ->
    0 <= i < Zlength unassigned ->
    clause_summary_ok sigma (Znth i rows (@nil literal)) state true_count
      unassigned_count ->
    summary_at sigma rows
      (replace_Znth i state states)
      (replace_Znth i true_count true_counts)
      (replace_Znth i unassigned_count unassigned) i.
Proof.
  intros sigma rows states true_counts unassigned i state true_count
    unassigned_count Hstates Htrue Hunassigned Hsummary.
  unfold summary_at.
  rewrite !Znth_replace_Znth_Same by lia.
  exact Hsummary.
Qed.
Lemma summary_at_replace_other__bcp_assignment_summary_d :
  forall sigma rows states true_counts unassigned i state true_count
      unassigned_count k live,
    Zlength states = live ->
    Zlength true_counts = live ->
    Zlength unassigned = live ->
    0 <= i < live -> 0 <= k < live -> k <> i ->
    (summary_at sigma rows
       (replace_Znth i state states)
       (replace_Znth i true_count true_counts)
       (replace_Znth i unassigned_count unassigned) k <->
     summary_at sigma rows states true_counts unassigned k).
Proof.
  intros sigma rows states true_counts unassigned i state true_count
    unassigned_count k live Hstates Htrue Hunassigned Hi Hk Hki.
  unfold summary_at.
  rewrite !Znth_replace_Znth_Diff by lia.
  reflexivity.
Qed.
Lemma mixed_clause_summaries_step__bcp_assignment_summary_d :
  forall old_sigma new_sigma rows states true_counts unassigned
      live capacity i exempt state true_count unassigned_count,
    mixed_clause_summaries old_sigma new_sigma rows states true_counts
      unassigned live capacity i exempt ->
    0 <= i < live ->
    summary_at new_sigma rows
      (replace_Znth i state states)
      (replace_Znth i true_count true_counts)
      (replace_Znth i unassigned_count unassigned) i ->
    mixed_clause_summaries old_sigma new_sigma rows
      (replace_Znth i state states)
      (replace_Znth i true_count true_counts)
      (replace_Znth i unassigned_count unassigned)
      live capacity (i + 1) exempt.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned
    live capacity i exempt state true_count unassigned_count
    Hmixed Hi Hcurrent.
  unfold mixed_clause_summaries in Hmixed |- *.
  destruct Hmixed as
    [Hrows [Hstates [Htrue [Hunassigned [Hcapacity [Hprocessed Hall]]]]]].
  destruct Hcapacity as [Hlive Hcapacity].
  split; [exact Hrows|].
  split; [rewrite Zlength_replace_Znth; exact Hstates|].
  split; [rewrite Zlength_replace_Znth; exact Htrue|].
  split; [rewrite Zlength_replace_Znth; exact Hunassigned|].
  split; [split; [exact Hlive|exact Hcapacity]|].
  split; [split; lia|].
  intros k Hk; split.
    + intros [Hbefore|Hexempt].
      * destruct (Z.eq_dec k i) as [->|Hki].
        -- exact Hcurrent.
        -- apply (proj2 (summary_at_replace_other__bcp_assignment_summary_d
             new_sigma rows states true_counts unassigned i state true_count
             unassigned_count k live Hstates Htrue Hunassigned Hi Hk Hki)).
           apply (proj1 (Hall k Hk)); left; lia.
      * destruct (Z.eq_dec k i) as [->|Hki].
        -- exact Hcurrent.
        -- apply (proj2 (summary_at_replace_other__bcp_assignment_summary_d
             new_sigma rows states true_counts unassigned i state true_count
             unassigned_count k live Hstates Htrue Hunassigned Hi Hk Hki)).
           apply (proj1 (Hall k Hk)); right; exact Hexempt.
    + intros [Hafter Hnotexempt].
      assert (Hki : k <> i) by lia.
      apply (proj2 (summary_at_replace_other__bcp_assignment_summary_d
        old_sigma rows states true_counts unassigned i state true_count
        unassigned_count k live Hstates Htrue Hunassigned Hi Hk Hki)).
      apply (proj2 (Hall k Hk)); split; [lia|exact Hnotexempt].
Qed.
Lemma clause_summary_one_false__bcp_assignment_summary_d :
  forall sigma c true_count unassigned_count,
    clause_summary_ok sigma c 1 true_count unassigned_count ->
    clause_false sigma c.
Proof.
  intros sigma c true_count unassigned_count Hsummary.
  unfold clause_summary_ok in Hsummary.
  destruct Hsummary as [Htrue [Hunassigned Hstate]].
  pose proof (clause_counts_nonnegative__bcp_assignment_summary_d sigma c)
    as [Htrue_nonneg Hunassigned_nonneg].
  unfold expected_clause_state in Hstate.
  destruct (Z.ltb 0 (clause_true_count sigma c)) eqn:Hpositive.
  - discriminate.
  - apply Z.ltb_ge in Hpositive.
    destruct (Z.eqb (clause_unassigned_count sigma c) 0)
      eqn:Hunassigned0.
    + apply Z.eqb_eq in Hunassigned0.
      apply clause_counts_zero_false__bcp_unit_to_assignment; lia.
    + apply Z.eqb_neq in Hunassigned0.
      destruct (Z.eqb (clause_unassigned_count sigma c) 1)
        eqn:Hunassigned1.
      * discriminate.
      * apply Z.eqb_neq in Hunassigned1; exfalso; lia.
Qed.
Lemma clause_summary_true_literal_not_one__bcp_assignment_summary_d :
  forall sigma c state true_count unassigned_count l,
    clause_summary_ok sigma c state true_count unassigned_count ->
    In l c -> eval_partial_literal sigma l = Some true ->
    state <> 1.
Proof.
  intros sigma c state true_count unassigned_count l Hsummary Hin Heval ->.
  pose proof (clause_summary_one_false__bcp_assignment_summary_d
    sigma c true_count unassigned_count Hsummary) as Hfalse.
  specialize (Hfalse l Hin); congruence.
Qed.
Lemma znth_out_of_bounds__bcp_assignment_summary_d :
  forall (A : Type) (l : list A) (d : A) i,
    0 <= i -> Zlength l <= i -> Znth i l d = d.
Proof.
  intros A l; induction l as [|a l IH]; intros d i Hi Hout.
  - unfold Znth; simpl; destruct (Z.to_nat i); reflexivity.
  - rewrite Zlength_cons in Hout.
    pose proof (Zlength_nonneg l).
    assert (i <> 0) by lia.
    rewrite Znth_cons by lia.
    apply IH; lia.
Qed.
Lemma assigned_satisfying_dense_literal__bcp_assignment_summary_d :
  forall old new x b d reason n row,
    assigns_one old new x b d reason ->
    row_wf n row -> var_in_range n x ->
    Znth x row 0 = (if b then 1 else -1) ->
    exists l,
      In l (dense_decode row) /\
      eval_partial_literal (assignment new) l = Some true.
Proof.
  intros old new x b d reason n row Hassign Hrow Hx Hcell.
  unfold assigns_one in Hassign.
  destruct Hassign as [_ [Hnew _]].
  destruct b.
  - exists (Pos x); split.
    + apply (proj1 (dense_decode_pos n row x Hrow Hx)); exact Hcell.
    + unfold eval_partial_literal, literal_var; rewrite Hnew; reflexivity.
  - exists (Neg x); split.
    + apply (proj1 (dense_decode_neg n row x Hrow Hx)); exact Hcell.
    + unfold eval_partial_literal, literal_var; rewrite Hnew; reflexivity.
Qed.
Lemma mixed_next_state_not_one__bcp_assignment_summary_d :
  forall old_sigma new_sigma rows states true_counts unassigned
      live capacity i exempt,
    mixed_clause_summaries old_sigma new_sigma rows states true_counts
      unassigned live capacity i exempt ->
    (forall c, In c rows -> ~ clause_false old_sigma c) ->
    (forall k, 0 <= k < live -> exempt = Some k ->
      exists l,
        In l (Znth k rows (@nil literal)) /\
        eval_partial_literal new_sigma l = Some true) ->
    0 <= i < live ->
    Znth (i + 1) states 0 <> 1.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned
    live capacity i exempt Hmixed Hno_conflict Hexempt_true Hi.
  unfold mixed_clause_summaries in Hmixed.
  destruct Hmixed as
    [Hrows [Hstates [Htrue [Hunassigned [Hcapacity [Hprocessed Hall]]]]]].
  destruct (Z_lt_dec (i + 1) live) as [Hnext_in|Hnext_out].
  - pose proof (Hall (i + 1) ltac:(lia)) as [Hnew_summary Hold_summary].
    destruct exempt as [k|].
    + destruct (Z.eq_dec k (i + 1)) as [->|Hneq].
      * pose proof (Hnew_summary (or_intror eq_refl)) as Hsummary.
        pose proof (Hexempt_true (i + 1) ltac:(lia) eq_refl)
          as [l [Hin Heval]].
        unfold summary_at in Hsummary.
        eapply clause_summary_true_literal_not_one__bcp_assignment_summary_d;
          eauto.
      * assert (Some k <> Some (i + 1)) as Hnotexempt.
        { intro Heq; inversion Heq; contradiction. }
        assert (i <= i + 1) as Hle by lia.
        pose proof (Hold_summary (conj Hle Hnotexempt)) as Hsummary.
        unfold summary_at in Hsummary.
        intro Hstate.
        apply (Hno_conflict (Znth (i + 1) rows (@nil literal))
          (Znth_In
            clause rows (@nil literal) (i + 1) ltac:(rewrite <- Hrows; lia))).
        apply (clause_summary_one_false__bcp_assignment_summary_d
          old_sigma (Znth (i + 1) rows (@nil literal))
          (Znth (i + 1) true_counts 0)
          (Znth (i + 1) unassigned 0)).
        rewrite Hstate in Hsummary; exact Hsummary.
    + assert (None <> Some (i + 1)) as Hnotexempt by discriminate.
      assert (i <= i + 1) as Hle by lia.
      pose proof (Hold_summary (conj Hle Hnotexempt)) as Hsummary.
      unfold summary_at in Hsummary.
      intro Hstate.
      apply (Hno_conflict (Znth (i + 1) rows (@nil literal))
        (Znth_In
          clause rows (@nil literal) (i + 1) ltac:(rewrite <- Hrows; lia))).
      apply (clause_summary_one_false__bcp_assignment_summary_d
        old_sigma (Znth (i + 1) rows (@nil literal))
        (Znth (i + 1) true_counts 0)
        (Znth (i + 1) unassigned 0)).
      rewrite Hstate in Hsummary; exact Hsummary.
  - rewrite (znth_out_of_bounds__bcp_assignment_summary_d
      Z states 0 (i + 1)); [lia|lia|rewrite Hstates; lia].
Qed.
Lemma mixed_clause_summaries_step_same__bcp_assignment_summary_d :
  forall old_sigma new_sigma rows states true_counts unassigned
      live capacity i exempt,
    mixed_clause_summaries old_sigma new_sigma rows states true_counts
      unassigned live capacity i exempt ->
    0 <= i < live ->
    summary_at new_sigma rows states true_counts unassigned i ->
    mixed_clause_summaries old_sigma new_sigma rows states true_counts
      unassigned live capacity (i + 1) exempt.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned
    live capacity i exempt Hmixed Hi Hcurrent.
  pose proof Hmixed as Hlens.
  unfold mixed_clause_summaries in Hlens.
  destruct Hlens as
    [_ [Hstates [Htrue [Hunassigned _]]]].
  pose proof (mixed_clause_summaries_step__bcp_assignment_summary_d
    old_sigma new_sigma rows states true_counts unassigned live capacity
    i exempt (Znth i states 0) (Znth i true_counts 0)
    (Znth i unassigned 0) Hmixed Hi) as Hstep.
  assert (Hcurrent_replaced :
    summary_at new_sigma rows
      (replace_Znth i (Znth i states 0) states)
      (replace_Znth i (Znth i true_counts 0) true_counts)
      (replace_Znth i (Znth i unassigned 0) unassigned) i).
  {
    apply summary_at_replace_current__bcp_assignment_summary_d.
    - rewrite Hstates; exact Hi.
    - rewrite Htrue; exact Hi.
    - rewrite Hunassigned; exact Hi.
    - exact Hcurrent.
  }
  specialize (Hstep Hcurrent_replaced).
  rewrite !replace_Znth_Znth in Hstep
    by (rewrite ?Hstates, ?Htrue, ?Hunassigned; lia).
  exact Hstep.
Qed.
Lemma bcp_advance_same_dense__bcp_assignment_summary_d :
  forall F n live original_count snap ranks logical_dl new
      x b d reason states true_counts unassigned capacity i unitcl,
    coherent_snapshot F n live original_count snap ->
    assigns_one (cdcl_view_of_snapshot n snap ranks logical_dl)
      new x b d reason ->
    no_conflict (cdcl_view_of_snapshot n snap ranks logical_dl) ->
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment new)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      states true_counts unassigned live capacity i (Some unitcl) ->
    0 <= i < live -> 0 <= unitcl < live -> var_in_range n x ->
    Znth x (Znth unitcl (snap_rows snap) (@nil Z)) 0 =
      (if b then 1 else -1) ->
    (i = unitcl \/
     (i <> unitcl /\
      Znth x (Znth i (snap_rows snap) (@nil Z)) 0 = 0)) ->
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment new)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      states true_counts unassigned live capacity (i + 1) (Some unitcl) /\
    Znth (i + 1) states 0 <> 1.
Proof.
  intros F n live original_count snap ranks logical_dl new
    x b d reason states true_counts unassigned capacity i unitcl
    Hcoh Hassign Hno_conflict Hmixed Hi Hunit Hx Hunitcell Hcase.
  pose proof Hcoh as Hcoh_lengths.
  unfold coherent_snapshot in Hcoh_lengths.
  destruct Hcoh_lengths as [_ [_ [Hlengths _]]].
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as [_ [_ [_ [Hrows_length _]]]].
  assert (Hcurrent :
    summary_at (assignment new)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      states true_counts unassigned i).
  {
    pose proof Hmixed as Hscan.
    unfold mixed_clause_summaries in Hscan.
    destruct Hscan as [_ [_ [_ [_ [_ [_ Hall]]]]]].
    destruct Hcase as [->|[Hneq Hcell]].
    - apply (proj1 (Hall unitcl Hunit)); right; reflexivity.
    - assert (Hsome : Some unitcl <> Some i).
      { intro Hsome_eq; apply Hneq; congruence. }
      pose proof (proj2 (Hall i Hi) (conj (Z.le_refl i) Hsome)) as Hold.
      unfold summary_at in Hold |- *.
      change (Znth i
        (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
        (@nil literal)) with
        (Znth i (map dense_decode (snap_rows snap)) (@nil literal)) in Hold |- *.
      rewrite Znth_map_dense_decode__bcp_assignment_summary_c in Hold
        by (rewrite Hrows_length; exact Hi).
      rewrite Znth_map_dense_decode__bcp_assignment_summary_c
        by (rewrite Hrows_length; exact Hi).
      pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
        F n live original_count snap i Hcoh Hi) as Hrow_wf.
      destruct Hrow_wf as [Hrow_length Hrow_cells].
      pose proof (dense_decode_counts_zero__bcp_assignment_summary_d
        (Znth i (snap_rows snap) (@nil Z)) x b
        ltac:(rewrite Hrow_length; exact Hx) Hcell) as [Hvar Hlit].
      exact (clause_summary_assign_absent__bcp_assignment_summary_d
        (cdcl_view_of_snapshot n snap ranks logical_dl) new x b d reason
        (dense_decode (Znth i (snap_rows snap) (@nil Z)))
        (Znth i states 0) (Znth i true_counts 0)
        (Znth i unassigned 0) Hassign Hold Hvar Hlit).
  }
  split.
  - eapply mixed_clause_summaries_step_same__bcp_assignment_summary_d;
      eauto.
  - eapply mixed_next_state_not_one__bcp_assignment_summary_d;
      try eassumption.
    intros k Hk Heq; inversion Heq; subst k.
    pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
      F n live original_count snap unitcl Hcoh Hunit) as Hrow_wf.
    pose proof (assigned_satisfying_dense_literal__bcp_assignment_summary_d
      (cdcl_view_of_snapshot n snap ranks logical_dl) new x b d reason n
      (Znth unitcl (snap_rows snap) (@nil Z)) Hassign Hrow_wf Hx Hunitcell)
      as [l [Hin Heval]].
    exists l; split; [|exact Heval].
    change (Znth unitcl
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (@nil literal)) with
      (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal)).
    rewrite Znth_map_dense_decode__bcp_assignment_summary_c
      by (rewrite Hrows_length; exact Hunit).
    exact Hin.
Qed.
Lemma conflict_prefix_extend_same__bcp_assignment_summary_d :
  forall conflict states i,
    (conflict = -1 ->
      forall k, 0 <= k < i -> Znth k states 0 <> 1) ->
    Znth i states 0 <> 1 ->
    conflict = -1 ->
    forall k, 0 <= k < i + 1 -> Znth k states 0 <> 1.
Proof.
  intros conflict states i Hprefix Hi Hconflict k Hk.
  destruct (Z.eq_dec k i) as [->|Hki]; [exact Hi|].
  apply (Hprefix Hconflict k); lia.
Qed.
Lemma bcp_advance_false_dense__bcp_assignment_summary_d :
  forall F n live original_count snap ranks logical_dl new
      x b d reason states true_counts unassigned capacity i unitcl
      old_state new_state,
    coherent_snapshot F n live original_count snap ->
    assigns_one (cdcl_view_of_snapshot n snap ranks logical_dl)
      new x b d reason ->
    no_conflict (cdcl_view_of_snapshot n snap ranks logical_dl) ->
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment new)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      states true_counts unassigned live capacity i (Some unitcl) ->
    0 <= i < live -> 0 <= unitcl < live -> var_in_range n x ->
    i <> unitcl ->
    Znth x (Znth unitcl (snap_rows snap) (@nil Z)) 0 =
      (if b then 1 else -1) ->
    Znth x (Znth i (snap_rows snap) (@nil Z)) 0 =
      (if b then -1 else 1) ->
    old_state = Znth i states 0 ->
    old_state <> 0 -> old_state <> 1 -> old_state <> 2 ->
    ((old_state = -2 /\ new_state = 2) \/
     (old_state <> -2 /\ new_state = old_state + 1)) ->
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment new)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (replace_Znth i new_state states) true_counts
      (replace_Znth i (Znth i unassigned 0 - 1) unassigned)
      live capacity (i + 1) (Some unitcl) /\
    Znth (i + 1) (replace_Znth i new_state states) 0 <> 1.
Proof.
  intros F n live original_count snap ranks logical_dl new
    x b d reason states true_counts unassigned capacity i unitcl
    old_state new_state Hcoh Hassign Hno_conflict Hmixed
    Hi Hunit Hx Hneq Hunitcell Hrowcell Hstate
    Hstate0 Hstate1 Hstate2 Hnext_state.
  pose proof Hcoh as Hcoh_lengths.
  unfold coherent_snapshot in Hcoh_lengths.
  destruct Hcoh_lengths as [_ [_ [Hlengths _]]].
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as [_ [_ [_ [Hrows_length _]]]].
  pose proof Hmixed as Hlens.
  unfold mixed_clause_summaries in Hlens.
  destruct Hlens as [_ [Hstates [Htrue [Hunassigned _]]]].
  assert (Hold_summary :
    clause_summary_ok
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (dense_decode (Znth i (snap_rows snap) (@nil Z)))
      old_state (Znth i true_counts 0) (Znth i unassigned 0)).
  {
    pose proof Hmixed as Hscan.
    unfold mixed_clause_summaries in Hscan.
    destruct Hscan as [_ [_ [_ [_ [_ [_ Hall]]]]]].
    assert (Hsome : Some unitcl <> Some i).
    { intro Heq; apply Hneq; congruence. }
    pose proof (proj2 (Hall i Hi) (conj (Z.le_refl i) Hsome)) as Hold.
    unfold summary_at in Hold.
    change (Znth i
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (@nil literal)) with
      (Znth i (map dense_decode (snap_rows snap)) (@nil literal)) in Hold.
    rewrite Znth_map_dense_decode__bcp_assignment_summary_c in Hold
      by (rewrite Hrows_length; exact Hi).
    rewrite <- Hstate in Hold.
    exact Hold.
  }
  assert (Hcounts :
    literal_var_count x (dense_decode (Znth i (snap_rows snap) (@nil Z))) = 1 /\
    literal_true_at_count x b
      (dense_decode (Znth i (snap_rows snap) (@nil Z))) = 0).
  {
    pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
      F n live original_count snap i Hcoh Hi) as [Hrow_length Hrow_cells].
    destruct b; simpl in Hrowcell.
    - apply dense_decode_counts_neg_true__bcp_assignment_summary_d;
        [rewrite Hrow_length; exact Hx|exact Hrowcell].
    - apply dense_decode_counts_pos_false__bcp_assignment_summary_d;
        [rewrite Hrow_length; exact Hx|exact Hrowcell].
  }
  destruct Hcounts as [Hvar Hlit].
  assert (Hnew_summary :
    clause_summary_ok (assignment new)
      (dense_decode (Znth i (snap_rows snap) (@nil Z)))
      new_state (Znth i true_counts 0) (Znth i unassigned 0 - 1)).
  {
    eapply clause_summary_assign_false__bcp_assignment_summary_d;
      eauto.
  }
  assert (Hnew_summary_installed :
    clause_summary_ok (assignment new)
      (Znth i
        (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
        (@nil literal))
      new_state (Znth i true_counts 0) (Znth i unassigned 0 - 1)).
  {
    change (Znth i
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (@nil literal)) with
      (Znth i (map dense_decode (snap_rows snap)) (@nil literal)).
    rewrite Znth_map_dense_decode__bcp_assignment_summary_c
      by (rewrite Hrows_length; exact Hi).
    exact Hnew_summary.
  }
  assert (Hcurrent_replaced :
    summary_at (assignment new)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (replace_Znth i new_state states)
      (replace_Znth i (Znth i true_counts 0) true_counts)
      (replace_Znth i (Znth i unassigned 0 - 1) unassigned) i).
  {
    apply summary_at_replace_current__bcp_assignment_summary_d.
    - rewrite Hstates; exact Hi.
    - rewrite Htrue; exact Hi.
    - rewrite Hunassigned; exact Hi.
    - exact Hnew_summary_installed.
  }
  pose proof (mixed_clause_summaries_step__bcp_assignment_summary_d
    (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
    (assignment new)
    (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
    states true_counts unassigned live capacity i (Some unitcl)
    new_state (Znth i true_counts 0) (Znth i unassigned 0 - 1)
    Hmixed Hi Hcurrent_replaced) as Hadvance.
  rewrite replace_Znth_Znth in Hadvance by (rewrite Htrue; exact Hi).
  split; [exact Hadvance|].
  assert (Hnext_original : Znth (i + 1) states 0 <> 1).
  {
    eapply (mixed_next_state_not_one__bcp_assignment_summary_d
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment new)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      states true_counts unassigned live capacity i (Some unitcl)).
    - exact Hmixed.
    - exact Hno_conflict.
    - intros k Hk Heq; inversion Heq; subst k.
      pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
        F n live original_count snap unitcl Hcoh Hunit) as Hrow_wf.
      pose proof (assigned_satisfying_dense_literal__bcp_assignment_summary_d
        (cdcl_view_of_snapshot n snap ranks logical_dl) new x b d reason n
        (Znth unitcl (snap_rows snap) (@nil Z)) Hassign Hrow_wf Hx Hunitcell)
        as [l [Hin Heval]].
      exists l; split; [|exact Heval].
      change (Znth unitcl
        (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
        (@nil literal)) with
        (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal)).
      rewrite Znth_map_dense_decode__bcp_assignment_summary_c
        by (rewrite Hrows_length; exact Hunit).
      exact Hin.
    - exact Hi.
  }
  destruct (Z_lt_dec (i + 1) live) as [Hnext_in|Hnext_out].
  - rewrite Znth_replace_Znth_Diff by (try rewrite Hstates; lia).
    exact Hnext_original.
  - pose proof (znth_out_of_bounds__bcp_assignment_summary_d
      Z (replace_Znth i new_state states) 0 (i + 1)
      ltac:(lia)
      ltac:(rewrite Zlength_replace_Znth, Hstates; lia)) as Hout.
    rewrite Hout; lia.
Qed.
(** ===== group: bcp_scan_invariant ===== *)
Lemma bcp_advance_satisfied_dense__bcp_scan_invariant :
  forall F n live original_count snap ranks logical_dl new
      x b d reason states true_counts unassigned capacity i unitcl delta,
    coherent_snapshot F n live original_count snap ->
    assigns_one (cdcl_view_of_snapshot n snap ranks logical_dl) new x b d reason ->
    no_conflict (cdcl_view_of_snapshot n snap ranks logical_dl) ->
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment new)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      states true_counts unassigned live capacity i (Some unitcl) ->
    0 <= i < live -> 0 <= unitcl < live -> var_in_range n x -> i <> unitcl ->
    Znth x (Znth unitcl (snap_rows snap) (@nil Z)) 0 = (if b then 1 else -1) ->
    literal_var_count x
      (dense_decode (Znth i (snap_rows snap) (@nil Z))) = 1 ->
    literal_true_at_count x b
      (dense_decode (Znth i (snap_rows snap) (@nil Z))) = delta ->
    (delta = 1 \/ (delta = 0 /\ Znth i states 0 = 0)) ->
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment new)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (replace_Znth i 0 states)
      (replace_Znth i (Znth i true_counts 0 + delta) true_counts)
      (replace_Znth i (Znth i unassigned 0 - 1) unassigned)
      live capacity (i + 1) (Some unitcl)
    /\ Znth (i + 1) (replace_Znth i 0 states) 0 <> 1.
Proof.
  intros F n live original_count snap ranks logical_dl new
    x b d reason states true_counts unassigned capacity i unitcl delta
    Hcoh Hassign Hno_conflict Hmix Hi Hunit Hx Hneq Hunitcell
    Hvar Htrue Hdelta.
  pose proof Hcoh as Hcoh_lengths.
  unfold coherent_snapshot in Hcoh_lengths.
  destruct Hcoh_lengths as [_ [_ [Hlengths _]]].
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as [_ [_ [_ [Hrows_length _]]]].
  pose proof Hmix as Hlens.
  unfold mixed_clause_summaries in Hlens.
  destruct Hlens as [_ [Hstates_len [Htrue_len [Hunass_len _]]]].
  assert (Hclause :
    Znth i (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (@nil literal) = dense_decode (Znth i (snap_rows snap) (@nil Z))).
  { change (Znth i (map dense_decode (snap_rows snap)) (@nil literal)
      = dense_decode (Znth i (snap_rows snap) (@nil Z))).
    rewrite Znth_map_dense_decode__bcp_assignment_summary_c
      by (rewrite Hrows_length; lia).
    reflexivity. }
  pose proof (mixed_clause_summaries_old_at_processed__bcp_assignment_summary_a
    _ _ _ _ _ _ _ _ _ _ Hmix Hi Hneq) as Hold_summary.
  unfold summary_at in Hold_summary.
  rewrite Hclause in Hold_summary.
  assert (Hcurrent_summary :
    summary_at (assignment new)
      (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
      (replace_Znth i 0 states)
      (replace_Znth i (Znth i true_counts 0 + delta) true_counts)
      (replace_Znth i (Znth i unassigned 0 - 1) unassigned) i).
  { unfold summary_at.
    rewrite Hclause.
    rewrite Znth_replace_Znth_Same by (rewrite Hstates_len; lia).
    rewrite Znth_replace_Znth_Same by (rewrite Htrue_len; lia).
    rewrite Znth_replace_Znth_Same by (rewrite Hunass_len; lia).
    eapply clause_summary_assign__bcp_assignment_summary_a.
    - exact Hassign.
    - exact Hold_summary.
    - exact Hvar.
    - exact Htrue.
    - exact Hdelta. }
  split.
  - eapply mixed_clause_summaries_step__bcp_assignment_summary_d.
    + exact Hmix.
    + exact Hi.
    + exact Hcurrent_summary.
  - assert (Hnext_orig : Znth (i + 1) states 0 <> 1).
    { eapply (mixed_next_state_not_one__bcp_assignment_summary_d
        (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
        (assignment new)
        (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
        states true_counts unassigned live capacity i (Some unitcl)).
      - exact Hmix.
      - exact Hno_conflict.
      - intros k Hk Heq; inversion Heq; subst k.
        pose proof (coherent_snapshot_row_wf__bcp_assignment_summary_a
          F n live original_count snap unitcl Hcoh Hunit) as Hrow_wf.
        pose proof (assigned_satisfying_dense_literal__bcp_assignment_summary_d
          (cdcl_view_of_snapshot n snap ranks logical_dl) new x b d reason n
          (Znth unitcl (snap_rows snap) (@nil Z)) Hassign Hrow_wf Hx Hunitcell)
          as [l [Hin Heval]].
        exists l; split; [|exact Heval].
        change (Znth unitcl
          (installed_clauses (cdcl_view_of_snapshot n snap ranks logical_dl))
          (@nil literal)) with
          (Znth unitcl (map dense_decode (snap_rows snap)) (@nil literal)).
        rewrite Znth_map_dense_decode__bcp_assignment_summary_c
          by (rewrite Hrows_length; exact Hunit).
        exact Hin.
      - exact Hi. }
    destruct (Z_lt_dec (i + 1) live) as [Hin|Hout].
    + rewrite Znth_replace_Znth_Diff by (try rewrite Hstates_len; lia).
      exact Hnext_orig.
    + pose proof (znth_out_of_bounds__bcp_assignment_summary_d
        Z (replace_Znth i 0 states) 0 (i + 1)
        ltac:(lia)
        ltac:(rewrite Zlength_replace_Znth, Hstates_len; lia)) as Hout2.
      rewrite Hout2; lia.
Qed.
(** ===== group: bcp_exit_results ===== *)
Lemma complete_unit_scan_no_unit__bcp_exit_results :
  forall F n live original_count snap ranks logical_dl next,
    coherent_snapshot F n live original_count snap ->
    live <= next ->
    (forall i, 0 <= i < next ->
      exists c,
        nth_error
          (installed_clauses
            (cdcl_view_of_snapshot n snap ranks logical_dl))
          (Z.to_nat i) = Some c /\
        ~ clause_unit
          (assignment
            (cdcl_view_of_snapshot n snap ranks logical_dl)) c) ->
    no_unit (cdcl_view_of_snapshot n snap ranks logical_dl).
Proof.
  intros F n live original_count snap ranks logical_dl next
    Hcoherent Hcomplete Hscan.
  unfold no_unit.
  intros c Hin Hunit.
  destruct Hcoherent as
    [_ [_ [Hlengths [_ [_ _]]]]].
  destruct Hlengths as
    [_ [_ [_ [Hrows [_ [_ _]]]]]].
  apply In_nth_error in Hin.
  destruct Hin as [k Hnth].
  assert (Hklen : (k < List.length
    (installed_clauses
      (cdcl_view_of_snapshot n snap ranks logical_dl)))%nat).
  {
    apply nth_error_Some.
    rewrite Hnth.
    discriminate.
  }
  assert (Hbound : 0 <= Z.of_nat k < next).
  {
    split; [lia|].
    assert (Hinstalled_length :
      Z.of_nat (List.length
        (installed_clauses
          (cdcl_view_of_snapshot n snap ranks logical_dl))) = live).
    {
      change (Z.of_nat (List.length (map dense_decode (snap_rows snap))) = live).
      rewrite length_map.
      rewrite <- Zlength_correct.
      exact Hrows.
    }
    lia.
  }
  specialize (Hscan (Z.of_nat k) Hbound).
  destruct Hscan as [c' [Hnth' Hnotunit]].
  rewrite Nat2Z.id in Hnth'.
  rewrite Hnth in Hnth'.
  inversion Hnth'; subst c'.
  exact (Hnotunit Hunit).
Qed.
Lemma bcp_exit_view_eq__bcp_exit_results :
  forall n snap new_snap ranks logical_dl cur_states cur_true cur_unassigned,
    snap_rows new_snap = snap_rows snap ->
    cdcl_view_of_snapshot n
      {| snap_values := snap_values new_snap;
         snap_reasons := snap_reasons new_snap;
         snap_levels := snap_levels new_snap;
         snap_rows := snap_rows snap;
         snap_states := cur_states;
         snap_true_counts := cur_true;
         snap_unassigned := cur_unassigned |}
      ranks logical_dl =
    cdcl_view_of_snapshot n new_snap ranks logical_dl.
Proof.
  intros n snap new_snap ranks logical_dl cur_states cur_true cur_unassigned
    Hrows.
  destruct snap as [sv sr sl srows ss st su].
  destruct new_snap as [nv nr nl nrows ns nt nu].
  cbn in Hrows |- *.
  subst nrows.
  reflexivity.
Qed.
Lemma bcp_exit_snapshot_ready__bcp_exit_results :
  forall F n live original_count cap snap new_snap ranks logical_dl
      x reason value_cell cur_states cur_true cur_unassigned processed,
    0 <= x < n ->
    0 <= reason < live ->
    (value_cell = 0 \/ value_cell = 1) ->
    coherent_snapshot F n live original_count snap ->
    stable_search_facts n new_snap ranks logical_dl ->
    snap_rows new_snap = snap_rows snap ->
    snap_values new_snap =
      replace_Znth x value_cell (snap_values snap) ->
    snap_reasons new_snap =
      replace_Znth x reason (snap_reasons snap) ->
    snap_levels new_snap =
      replace_Znth x logical_dl (snap_levels snap) ->
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap (fun _ => None) logical_dl))
      (assignment (cdcl_view_of_snapshot n new_snap ranks logical_dl))
      (installed_clauses
        (cdcl_view_of_snapshot n snap (fun _ => None) logical_dl))
      cur_states cur_true cur_unassigned live cap processed (Some reason) ->
    live <= processed ->
    coherent_snapshot F n live original_count
      {| snap_values := snap_values new_snap;
         snap_reasons := snap_reasons new_snap;
         snap_levels := snap_levels new_snap;
         snap_rows := snap_rows snap;
         snap_states := cur_states;
         snap_true_counts := cur_true;
         snap_unassigned := cur_unassigned |} /\
    stable_search_facts n
      {| snap_values := snap_values new_snap;
         snap_reasons := snap_reasons new_snap;
         snap_levels := snap_levels new_snap;
         snap_rows := snap_rows snap;
         snap_states := cur_states;
         snap_true_counts := cur_true;
         snap_unassigned := cur_unassigned |}
      ranks logical_dl.
Proof.
  intros F n live original_count cap snap new_snap ranks logical_dl
    x reason value_cell cur_states cur_true cur_unassigned processed
    Hx Hreason Hvalue Hcoherent Hstable Hrows Hvalues Hreasons Hlevels
    Hmixed Hprocessed.
  pose proof Hstable as Hstable_copy.
  unfold stable_search_facts in Hstable.
  destruct Hstable as [_ [Hclosed _]].
  destruct Hclosed as [Hdl_nonneg _].
  destruct Hcoherent as
    [Hn [Horiginal [Hlengths [Hcells [Hsummaries Hsound]]]]].
  destruct Hlengths as
    [Hvalues_len [Hreasons_len [Hlevels_len [Hrows_len
      [Hstates_len [Htrue_len Hunassigned_len]]]]]].
  destruct Hcells as [Hcells Hrows_wf].
  destruct Hmixed as
    [Hmixed_rows [Hmixed_states [Hmixed_true [Hmixed_unassigned
      [Hmixed_cap [Hmixed_processed Hmixed_summaries]]]]]].
  split.
  - unfold coherent_snapshot.
    split; [exact Hn |].
    split; [exact Horiginal |].
    split.
    + unfold snapshot_lengths.
      cbn.
      repeat split.
      * rewrite Hvalues, Zlength_replace_Znth, Hvalues_len.
        reflexivity.
      * rewrite Hreasons, Zlength_replace_Znth, Hreasons_len.
        reflexivity.
      * rewrite Hlevels, Zlength_replace_Znth, Hlevels_len.
        reflexivity.
      * exact Hrows_len.
      * exact Hmixed_states.
      * exact Hmixed_true.
      * exact Hmixed_unassigned.
    + split.
      * unfold snapshot_cells_wf.
        cbn.
        split.
        -- intros y Hy.
           destruct (Z.eq_dec y x) as [Hyx | Hyx].
           ++ subst y.
              rewrite Hvalues, Hreasons, Hlevels.
              pose proof (Znth_replace_Znth_Same (-1) (snap_values snap)
                x value_cell ltac:(rewrite Hvalues_len; exact Hx))
                as Hsame_value.
              pose proof (Znth_replace_Znth_Same (-1) (snap_reasons snap)
                x reason ltac:(rewrite Hreasons_len; exact Hx))
                as Hsame_reason.
              pose proof (Znth_replace_Znth_Same (-1) (snap_levels snap)
                x logical_dl ltac:(rewrite Hlevels_len; exact Hx))
                as Hsame_level.
              unfold Znth in Hsame_value, Hsame_reason, Hsame_level.
              rewrite Hsame_value, Hsame_reason, Hsame_level.
              split.
              ** destruct Hvalue; subst value_cell; auto.
              ** split.
                 --- intros Hbad.
                     destruct Hvalue; lia.
                 --- intros _.
                     split.
                     +++ change (0 <= logical_dl) in Hdl_nonneg.
                         exact Hdl_nonneg.
                     +++ right; exact Hreason.
           ++ specialize (Hcells y Hy).
              cbn in Hcells.
              rewrite Hvalues, Hreasons, Hlevels.
              pose proof (Znth_replace_Znth_Diff (-1) (snap_values snap)
                x y value_cell ltac:(rewrite Hvalues_len; exact Hx)
                ltac:(rewrite Hvalues_len; exact Hy) ltac:(lia)) as Hdiff_value.
              pose proof (Znth_replace_Znth_Diff (-1) (snap_reasons snap)
                x y reason ltac:(rewrite Hreasons_len; exact Hx)
                ltac:(rewrite Hreasons_len; exact Hy) ltac:(lia)) as Hdiff_reason.
              pose proof (Znth_replace_Znth_Diff (-1) (snap_levels snap)
                x y logical_dl ltac:(rewrite Hlevels_len; exact Hx)
                ltac:(rewrite Hlevels_len; exact Hy) ltac:(lia)) as Hdiff_level.
              unfold Znth in Hdiff_value, Hdiff_reason, Hdiff_level.
              rewrite Hdiff_value, Hdiff_reason, Hdiff_level.
              exact Hcells.
        -- exact Hrows_wf.
      * split.
        -- unfold snapshot_summaries_exact.
           cbn.
           intros j Hj.
           specialize (Hmixed_summaries j Hj).
           destruct Hmixed_summaries as [Hnew_summary _].
           specialize (Hnew_summary ltac:(left; lia)).
           change (summary_at (snapshot_assignment n new_snap)
             (map dense_decode (snap_rows snap)) cur_states cur_true
             cur_unassigned j).
           change (summary_at (snapshot_assignment n new_snap)
             (map dense_decode (snap_rows snap)) cur_states cur_true
             cur_unassigned j) in Hnew_summary.
           exact Hnew_summary.
        -- exact Hsound.
  - unfold stable_search_facts in Hstable_copy |- *.
    rewrite (bcp_exit_view_eq__bcp_exit_results n snap new_snap ranks
      logical_dl cur_states cur_true cur_unassigned Hrows).
    exact Hstable_copy.
Qed.
Lemma clause_summary_state_one_iff_false__bcp_exit_results :
  forall sigma c state true_count unassigned,
    clause_summary_ok sigma c state true_count unassigned ->
    (state = 1 <-> clause_false sigma c).
Proof.
  intros sigma c state true_count unassigned Hsummary.
  destruct Hsummary as [_ [_ Hstate]].
  split.
  - intros Hone.
    assert (Hexpected : 1 = expected_clause_state sigma c) by lia.
    pose proof (clause_counts_nonnegative__bcp_assignment_summary_d sigma c)
      as [Htrue_nonnegative Hunassigned_nonnegative].
    unfold expected_clause_state in Hexpected.
    destruct ((0 <? clause_true_count sigma c)%Z) eqn:Hpositive_true.
    { discriminate. }
    apply Z.ltb_ge in Hpositive_true.
    assert (Htrue_zero : clause_true_count sigma c = 0) by lia.
    destruct ((clause_unassigned_count sigma c =? 0)%Z)
      eqn:Hunassigned_zero.
    + apply Z.eqb_eq in Hunassigned_zero.
      apply clause_counts_zero_false__bcp_unit_to_assignment;
        assumption.
    + apply Z.eqb_neq in Hunassigned_zero.
      destruct ((clause_unassigned_count sigma c =? 1)%Z)
        eqn:Hunassigned_one.
      * discriminate.
      * lia.
  - intros Hfalse.
    pose proof (clause_false_counts__learning_row_and_scan sigma c Hfalse)
      as [Htrue_zero Hunassigned_zero].
    rewrite Hstate.
    unfold expected_clause_state.
    rewrite Htrue_zero, Hunassigned_zero.
    reflexivity.
Qed.
Lemma coherent_state_one_conflict__bcp_exit_results :
  forall F n live original_count snap ranks logical_dl i,
    coherent_snapshot F n live original_count snap ->
    0 <= i < live ->
    Znth i (snap_states snap) 0 = 1 ->
    exists c,
      nth_error
        (installed_clauses
          (cdcl_view_of_snapshot n snap ranks logical_dl))
        (Z.to_nat i) = Some c /\
      clause_false
        (assignment (cdcl_view_of_snapshot n snap ranks logical_dl)) c.
Proof.
  intros F n live original_count snap ranks logical_dl i
    Hcoherent Hi Hstate.
  destruct Hcoherent as [_ [_ [Hlengths [_ [Hsummaries _]]]]].
  destruct Hlengths as [_ [_ [_ [Hrows_len _]]]].
  specialize (Hsummaries i Hi).
  unfold summary_at in Hsummaries.
  exists (Znth i (map dense_decode (snap_rows snap)) (@nil literal)).
  split.
  - unfold installed_clauses, cdcl_view_of_snapshot.
    unfold Znth.
    apply nth_error_nth'.
    rewrite length_map.
    rewrite Zlength_correct in Hrows_len.
    lia.
  - apply (proj1
      (clause_summary_state_one_iff_false__bcp_exit_results
        _ _ _ _ _ Hsummaries)).
    exact Hstate.
Qed.
Lemma coherent_states_no_conflict__bcp_exit_results :
  forall F n live original_count snap ranks logical_dl,
    coherent_snapshot F n live original_count snap ->
    (forall i, 0 <= i < live -> Znth i (snap_states snap) 0 <> 1) ->
    no_conflict (cdcl_view_of_snapshot n snap ranks logical_dl).
Proof.
  intros F n live original_count snap ranks logical_dl
    Hcoherent Hstates.
  unfold no_conflict.
  intros c Hin Hfalse.
  destruct Hcoherent as [_ [_ [Hlengths [_ [Hsummaries _]]]]].
  destruct Hlengths as [_ [_ [_ [Hrows_len _]]]].
  apply In_nth_error in Hin.
  destruct Hin as [k Hnth].
  assert (Hk : 0 <= Z.of_nat k < live).
  {
    split; [lia |].
    assert (Hklen :
      (k < List.length
        (installed_clauses
          (cdcl_view_of_snapshot n snap ranks logical_dl)))%nat).
    {
      apply nth_error_Some.
      rewrite Hnth.
      discriminate.
    }
    change (k < List.length (map dense_decode (snap_rows snap)))%nat in Hklen.
    rewrite length_map in Hklen.
    rewrite Zlength_correct in Hrows_len.
    lia.
  }
  specialize (Hsummaries (Z.of_nat k) Hk).
  unfold summary_at in Hsummaries.
  assert (Hclause :
    Znth (Z.of_nat k) (map dense_decode (snap_rows snap))
      (@nil literal) = c).
  {
    unfold Znth.
    rewrite Nat2Z.id.
    eapply nth_error_nth.
    exact Hnth.
  }
  rewrite Hclause in Hsummaries.
  assert (Hone : Znth (Z.of_nat k) (snap_states snap) 0 = 1).
  {
    apply (proj2
      (clause_summary_state_one_iff_false__bcp_exit_results
        _ _ _ _ _ Hsummaries)).
    exact Hfalse.
  }
  exact (Hstates (Z.of_nat k) Hk Hone).
Qed.
Lemma assigns_one_dense_conflict__bcp_exit_results :
  forall old new x b d reason,
    no_conflict old ->
    assigns_one old new x b d reason ->
    d = current_level new ->
    dense_conflict_batch old new x.
Proof.
  intros old new x b d reason Hno_conflict Hassigns Hcurrent.
  unfold assigns_one in Hassigns.
  destruct Hassigns as
    [Hold_none [Hnew_some [Hnew_level [Hnew_reason
      [Hnew_rank [Hothers Hinstalled]]]]]].
  unfold dense_conflict_batch.
  exists b.
  repeat split.
  - exact Hold_none.
  - exact Hnew_some.
  - rewrite <- Hcurrent.
    exact Hnew_level.
  - exact Hinstalled.
  - intros c Hin Hfalse.
    destruct (clause_mem_dec (falsified_literal x b) c) as [Hcause | Hcause].
    + exact Hcause.
    + exfalso.
      apply (Hno_conflict c).
      * rewrite <- Hinstalled.
        exact Hin.
      * intros l Hl.
        specialize (Hfalse l Hl).
        destruct l as [y | y].
        -- destruct (Z.eq_dec y x) as [Hy | Hy].
           ++ subst y.
              destruct b eqn:Hb.
              ** unfold eval_partial_literal in Hfalse.
                 cbn in Hfalse.
                 rewrite Hnew_some in Hfalse.
                 discriminate.
              ** exfalso.
                 apply Hcause.
                 cbn.
                 exact Hl.
           ++ destruct (Hothers y Hy) as [Hassignment _].
              unfold eval_partial_literal in Hfalse |- *.
              cbn in Hfalse |- *.
              rewrite <- Hassignment.
              exact Hfalse.
        -- destruct (Z.eq_dec y x) as [Hy | Hy].
           ++ subst y.
              destruct b eqn:Hb.
              ** exfalso.
                 apply Hcause.
                 cbn.
                 exact Hl.
              ** unfold eval_partial_literal in Hfalse.
                 cbn in Hfalse.
                 rewrite Hnew_some in Hfalse.
                 discriminate.
           ++ destruct (Hothers y Hy) as [Hassignment _].
              unfold eval_partial_literal in Hfalse |- *.
              cbn in Hfalse |- *.
              rewrite <- Hassignment.
              exact Hfalse.
Qed.
(** ===== group: backtrack_safety_a ===== *)
Lemma clause_true_count_bounds__backtrack_safety_a : forall sigma c,
  0 <= clause_true_count sigma c <= Zlength c.
Proof.
  intros sigma c.
  induction c as [|l c IH].
  - simpl. rewrite Zlength_nil. lia.
  - split.
    + unfold clause_true_count at 1.
      destruct (eval_partial_literal sigma l) as [[|]|] eqn:Heval.
      * change (0 <= 1 + clause_true_count sigma c). lia.
      * change (0 <= clause_true_count sigma c). lia.
      * change (0 <= clause_true_count sigma c). lia.
    + unfold clause_true_count at 1.
      destruct (eval_partial_literal sigma l) as [[|]|] eqn:Heval.
      * change (1 + clause_true_count sigma c <= Zlength (l :: c)).
        rewrite Zlength_cons. unfold Z.succ. lia.
      * change (clause_true_count sigma c <= Zlength (l :: c)).
        rewrite Zlength_cons. unfold Z.succ. lia.
      * change (clause_true_count sigma c <= Zlength (l :: c)).
        rewrite Zlength_cons. unfold Z.succ. lia.
Qed.
Lemma dense_decode_from_length_le__backtrack_safety_a : forall start row,
  Zlength (dense_decode_from start row) <= Zlength row.
Proof.
  intros start row.
  apply dense_decode_from_Zlength_le__bcp_safety_bounds_a.
Qed.
Lemma expected_clause_state_bounds__backtrack_safety_a : forall sigma c,
  - clause_unassigned_count sigma c <= expected_clause_state sigma c <= 2.
Proof.
  intros sigma c.
  pose proof (clause_unassigned_count_bounds__bcp_safety_bounds_a sigma c) as Hu.
  unfold expected_clause_state.
  destruct (Z.ltb 0 (clause_true_count sigma c)) eqn:Ht; simpl.
  - split; lia.
  - destruct (Z.eqb (clause_unassigned_count sigma c) 0) eqn:Hu0.
    + apply Z.eqb_eq in Hu0. split; lia.
    + destruct (Z.eqb (clause_unassigned_count sigma c) 1) eqn:Hu1.
      * apply Z.eqb_eq in Hu1. split; lia.
      * split; lia.
Qed.
Lemma backtrack_current_summary_bounds__backtrack_safety_a :
  forall old_sigma new_sigma dense_rows states true_counts unassigned
         live cap j n,
    mixed_clause_summaries old_sigma new_sigma
      (map dense_decode dense_rows) states true_counts unassigned
      live cap j None ->
    0 <= j < live ->
    Zlength (Znth j dense_rows (@nil Z)) = n ->
    0 <= Znth j true_counts 0 <= n /\
    0 <= Znth j unassigned 0 <= n /\
    - n <= Znth j states 0 <= 2.
Proof.
  intros old_sigma new_sigma dense_rows states true_counts unassigned
    live cap j n Hmixed Hj Hrowlen.
  unfold mixed_clause_summaries in Hmixed.
  destruct Hmixed as
    [Hlive [Hstates [Htrue_len [Hunassigned_len [Hcap [Hprocessed Hall]]]]]].
  assert (Hj_nat : (Z.to_nat j < List.length dense_rows)%nat).
  {
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite Zlength_correct, length_map in Hlive.
    lia.
  }
  assert (Hrow :
    Znth j (map dense_decode dense_rows) (@nil literal) =
    dense_decode (Znth j dense_rows (@nil Z))).
  {
    unfold Znth.
    apply map_nth_len.
    exact Hj_nat.
  }
  specialize (Hall j Hj).
  destruct Hall as [_ Hold].
  specialize (Hold ltac:(split; [lia | discriminate])).
  unfold summary_at, clause_summary_ok in Hold.
  destruct Hold as [Htrue [Hunassigned Hstate]].
  rewrite Hrow in Htrue, Hunassigned, Hstate.
  pose proof (clause_true_count_bounds__backtrack_safety_a
    old_sigma (dense_decode (Znth j dense_rows (@nil Z)))) as Ht.
  pose proof (clause_unassigned_count_bounds__bcp_safety_bounds_a
    old_sigma (dense_decode (Znth j dense_rows (@nil Z)))) as Hu.
  pose proof (dense_decode_from_length_le__backtrack_safety_a
    0 (Znth j dense_rows (@nil Z))) as Hdecode.
  pose proof (expected_clause_state_bounds__backtrack_safety_a
    old_sigma (dense_decode (Znth j dense_rows (@nil Z)))) as Hstate_bounds.
  rewrite <- Htrue in Ht.
  rewrite <- Hunassigned in Hu.
  rewrite <- Hstate in Hstate_bounds.
  rewrite <- Hunassigned in Hstate_bounds.
  unfold dense_decode in Ht, Hu, Hstate_bounds.
  repeat split; lia.
Qed.
(** ===== group: backtrack_safety_b ===== *)
Lemma dense_decode_from_length_le__backtrack_safety_b :
  forall base row,
    Zlength (dense_decode_from base row) <= Zlength row.
Proof.
  intros base row.
  apply dense_decode_from_Zlength_le__bcp_safety_bounds_a.
Qed.
Lemma Znth_mapped_dense_decode_length_le__backtrack_safety_b :
  forall rows j,
    0 <= j < Zlength rows ->
    Zlength (Znth j (map dense_decode rows) (@nil literal)) <=
    Zlength (Znth j rows (@nil Z)).
Proof.
  intros rows j Hj.
  unfold Znth.
  rewrite Zlength_correct in Hj.
  assert (Hjn : (Z.to_nat j < List.length rows)%nat) by lia.
  remember (Z.to_nat j) as k eqn:Hk.
  clear Hj.
  clear Hk j.
  revert k Hjn.
  induction rows as [| row rows IH]; intros k Hk; simpl in Hk; [lia |].
  destruct k as [| k]; simpl.
  - unfold dense_decode.
    apply dense_decode_from_length_le__backtrack_safety_b.
  - apply IH.
    lia.
Qed.
(** ===== group: backtrack_entry_clear_a ===== *)
Lemma clause_unassigned_count_bounds__backtrack_entry_clear_a :
  forall sigma c,
    0 <= clause_unassigned_count sigma c <= Z.of_nat (List.length c).
Proof.
  intros sigma c; induction c as [|lit c IH].
  - cbn; lia.
  - cbn -[eval_partial_literal Z.add].
    replace (Z.of_nat (S (List.length c)))
      with (1 + Z.of_nat (List.length c)) by lia.
    destruct IH as [IHlo IHhi].
    destruct (eval_partial_literal sigma lit) as [[|]|]; cbn -[Z.add].
    + split; [exact IHlo|lia].
    + split; [exact IHlo|lia].
    + split; lia.
Qed.
Lemma prefix_restriction_zero_same_snapshot__backtrack_entry_clear_a :
  forall n target old_level snap ranks,
    0 <= n ->
    prefix_restriction
      (cdcl_view_of_snapshot n snap ranks old_level)
      (cdcl_view_of_snapshot n snap ranks target)
      n target 0.
Proof.
  intros n target old_level snap ranks Hn.
  unfold prefix_restriction, cdcl_view_of_snapshot.
  cbn.
  split; [lia|].
  split; [reflexivity|].
  intros x Hx; split.
  - intros Habsurd. unfold var_in_range in Hx. exfalso. lia.
  - intros _. repeat split; reflexivity.
Qed.
Lemma coherent_snapshot_mixed_same__backtrack_entry_clear_a :
  forall F n live original_count snap cap,
    coherent_snapshot F n live original_count snap ->
    live <= cap ->
    mixed_clause_summaries
      (snapshot_assignment n snap) (snapshot_assignment n snap)
      (List.map dense_decode (snap_rows snap))
      (snap_states snap) (snap_true_counts snap) (snap_unassigned snap)
      live cap live None.
Proof.
  intros F n live original_count snap cap Hcoh Hcap.
  unfold coherent_snapshot in Hcoh.
  destruct Hcoh as [_ [Hbounds [Hlengths [_ [Hsummaries _]]]]].
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as [_ [_ [_ [Hrows [Hstates [Htrue Hunassigned]]]]]].
  unfold mixed_clause_summaries.
  split.
  - assert (Hmap_length : forall rows : list (list Z),
        Zlength (List.map dense_decode rows) = Zlength rows).
    { intro rows; induction rows as [|row rows IH].
      - reflexivity.
      - cbn [List.map]. repeat rewrite Zlength_cons. lia. }
    rewrite Hmap_length. lia.
  - split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    intros k Hk; split; intros _; apply Hsummaries; exact Hk.
Qed.
Lemma cleared_snapshot_lengths_cells__backtrack_entry_clear_a :
  forall n live snap i,
    snapshot_lengths n live snap ->
    snapshot_cells_wf n live snap ->
    var_in_range n i ->
    let after_snap :=
      {| snap_values := replace_Znth i (-1) (snap_values snap);
         snap_reasons := replace_Znth i (-1) (snap_reasons snap);
         snap_levels := replace_Znth i (-1) (snap_levels snap);
         snap_rows := snap_rows snap;
         snap_states := snap_states snap;
         snap_true_counts := snap_true_counts snap;
         snap_unassigned := snap_unassigned snap |} in
    snapshot_lengths n live after_snap /\
    snapshot_cells_wf n live after_snap.
Proof.
  intros n live snap i Hlengths Hcells Hi.
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as
    [Hv [Hr [Hl [Hrows [Hstates [Htrue Hunassigned]]]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [Hcell Hrow_wf].
  cbn.
  split.
  - unfold snapshot_lengths; cbn.
    repeat rewrite Zlength_replace_Znth.
    tauto.
  - unfold snapshot_cells_wf.
    split; [|exact Hrow_wf].
    intros x Hx.
    unfold var_in_range in Hi, Hx.
    change (
      let v := Znth x (replace_Znth i (-1) (snap_values snap)) (-1) in
      let d := Znth x (replace_Znth i (-1) (snap_levels snap)) (-1) in
      let r := Znth x (replace_Znth i (-1) (snap_reasons snap)) (-1) in
      (v = -1 \/ v = 0 \/ v = 1) /\
      (v = -1 -> d = -1 /\ r = -1) /\
      (v <> -1 -> 0 <= d /\ (r = -1 \/ 0 <= r < live))).
    destruct (Z.eq_dec x i) as [->|Hxi].
    + repeat rewrite Znth_replace_Znth_Same by lia.
      cbn.
      split; [left; reflexivity|].
      split.
      * intros _. split; reflexivity.
      * intros Hcontra. contradiction.
    + specialize (Hcell x Hx).
      repeat rewrite Znth_replace_Znth_Diff by lia.
      exact Hcell.
Qed.
Lemma cleared_snapshot_clears_one__backtrack_entry_clear_a :
  forall n live snap ranks target i,
    snapshot_lengths n live snap ->
    snapshot_cells_wf n live snap ->
    var_in_range n i ->
    Znth i (snap_values snap) (-1) <> -1 ->
    let after_snap :=
      {| snap_values := replace_Znth i (-1) (snap_values snap);
         snap_reasons := replace_Znth i (-1) (snap_reasons snap);
         snap_levels := replace_Znth i (-1) (snap_levels snap);
         snap_rows := snap_rows snap;
         snap_states := snap_states snap;
         snap_true_counts := snap_true_counts snap;
         snap_unassigned := snap_unassigned snap |} in
    let after_ranks := fun y =>
      if Z.eq_dec y i then None else ranks y in
    clears_one
      (cdcl_view_of_snapshot n snap ranks target)
      (cdcl_view_of_snapshot n after_snap after_ranks target) i.
Proof.
  intros n live snap ranks target i Hlengths Hcells Hi Hassigned.
  assert (Hcell_i := Hcells).
  unfold snapshot_cells_wf in Hcell_i.
  destruct Hcell_i as [Hcell_i _].
  specialize (Hcell_i i Hi).
  cbn in Hcell_i.
  destruct Hcell_i as [Hdomain _].
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as
    [Hv [Hr [Hl [Hrows [Hstates [Htrue Hunassigned]]]]]].
  destruct Hi as [Hi0 Hin].
  cbn.
  assert (Hguard : andb (0 <=? i) (i <? n) = true).
  { apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  assert (Hold_assigned : exists b,
      snapshot_assignment n snap i = Some b).
  { unfold snapshot_assignment. rewrite Hguard.
    unfold decode_value_cell.
    destruct Hdomain as [Hneg|[Hzero|Hone]].
    - contradiction.
    - exists false. rewrite Hzero. reflexivity.
    - exists true. rewrite Hone. reflexivity. }
  destruct Hold_assigned as [b Hold_assigned].
  unfold clears_one, cdcl_view_of_snapshot; cbn.
  split.
  - exists b, (Znth i (snap_levels snap) (-1)).
    split; [exact Hold_assigned|].
    unfold snapshot_level. rewrite Hold_assigned. reflexivity.
  - assert (Hafter_none :
        snapshot_assignment n
          {| snap_values := replace_Znth i (-1) (snap_values snap);
             snap_reasons := replace_Znth i (-1) (snap_reasons snap);
             snap_levels := replace_Znth i (-1) (snap_levels snap);
             snap_rows := snap_rows snap;
             snap_states := snap_states snap;
             snap_true_counts := snap_true_counts snap;
             snap_unassigned := snap_unassigned snap |} i = None).
    { unfold snapshot_assignment.
      change ((if andb (0 <=? i) (i <? n)
        then decode_value_cell
          (Znth i (replace_Znth i (-1) (snap_values snap)) (-1))
        else None) = None).
      rewrite Hguard.
      rewrite Znth_replace_Znth_Same by lia.
      reflexivity. }
    split; [exact Hafter_none|].
    split.
    + unfold snapshot_level. rewrite Hafter_none. reflexivity.
    + split.
      * unfold snapshot_reason. rewrite Hafter_none. reflexivity.
      * split.
        -- destruct (Z.eq_dec i i); [reflexivity|contradiction].
        -- split.
           ++ intros y Hyi.
              assert (Hassignment_other :
                snapshot_assignment n
                  {| snap_values := replace_Znth i (-1) (snap_values snap);
                     snap_reasons := replace_Znth i (-1) (snap_reasons snap);
                     snap_levels := replace_Znth i (-1) (snap_levels snap);
                     snap_rows := snap_rows snap;
                     snap_states := snap_states snap;
                     snap_true_counts := snap_true_counts snap;
                     snap_unassigned := snap_unassigned snap |} y =
                snapshot_assignment n snap y).
              { unfold snapshot_assignment.
                change ((if andb (0 <=? y) (y <? n)
                  then decode_value_cell
                    (Znth y (replace_Znth i (-1) (snap_values snap)) (-1))
                  else None) =
                  (if andb (0 <=? y) (y <? n)
                   then decode_value_cell (Znth y (snap_values snap) (-1))
                   else None)).
                destruct (andb (0 <=? y) (y <? n)) eqn:Hyguard;
                  [|reflexivity].
                apply andb_true_iff in Hyguard.
                destruct Hyguard as [Hy0 Hyn].
                apply Z.leb_le in Hy0; apply Z.ltb_lt in Hyn.
                rewrite Znth_replace_Znth_Diff by lia. reflexivity. }
              split; [exact Hassignment_other|].
              split.
              ** unfold snapshot_level. rewrite Hassignment_other.
                 destruct (snapshot_assignment n snap y) as [bv|] eqn:Hy;
                   [|reflexivity].
                 change (Some (Znth y
                   (replace_Znth i (-1) (snap_levels snap)) (-1)) =
                   Some (Znth y (snap_levels snap) (-1))).
                 assert (Hy_bounds : 0 <= y < n).
                 { unfold snapshot_assignment in Hy.
                   destruct (andb (0 <=? y) (y <? n)) eqn:Hyguard;
                     try discriminate.
                   apply andb_true_iff in Hyguard.
                   destruct Hyguard as [Hy0 Hyn].
                   apply Z.leb_le in Hy0; apply Z.ltb_lt in Hyn. lia. }
                 rewrite Znth_replace_Znth_Diff by lia. reflexivity.
              ** split.
                 2:{ destruct (Z.eq_dec y i); [contradiction|reflexivity]. }
                 unfold snapshot_reason. rewrite Hassignment_other.
                 destruct (snapshot_assignment n snap y) as [bv|] eqn:Hy;
                   [|reflexivity].
                 change ((if Znth y
                   (replace_Znth i (-1) (snap_reasons snap)) (-1) =? -1
                   then None
                   else Some (Znth y
                     (replace_Znth i (-1) (snap_reasons snap)) (-1))) =
                   (if Znth y (snap_reasons snap) (-1) =? -1
                    then None
                    else Some (Znth y (snap_reasons snap) (-1)))).
                 assert (Hy_bounds : 0 <= y < n).
                 { unfold snapshot_assignment in Hy.
                   destruct (andb (0 <=? y) (y <? n)) eqn:Hyguard;
                     try discriminate.
                   apply andb_true_iff in Hyguard.
                   destruct Hyguard as [Hy0 Hyn].
                   apply Z.leb_le in Hy0; apply Z.ltb_lt in Hyn. lia. }
                 rewrite Znth_replace_Znth_Diff by lia. reflexivity.
           ++ reflexivity.
Qed.
Lemma mixed_clause_summaries_reset_zero__backtrack_entry_clear_a :
  forall old_sigma new_sigma rows states true_counts unassigned live cap,
    mixed_clause_summaries old_sigma old_sigma rows states true_counts
      unassigned live cap live None ->
    mixed_clause_summaries old_sigma new_sigma rows states true_counts
      unassigned live cap 0 None.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned live cap Hmix.
  unfold mixed_clause_summaries in *.
  destruct Hmix as
    [Hrows [Hstates [Htrue [Hunassigned [Hcap [Hprocessed Hsummaries]]]]]].
  split; [exact Hrows|].
  split; [exact Hstates|].
  split; [exact Htrue|].
  split; [exact Hunassigned|].
  split; [exact Hcap|].
  split; [lia|].
  intros k Hk; split.
  - intros [Hlt|Hnone]; [lia|discriminate].
  - intros _. specialize (Hsummaries k Hk).
    destruct Hsummaries as [Hnew _].
    apply Hnew. left. lia.
Qed.
Lemma snapshot_row_length__backtrack_entry_clear_a :
  forall n live snap j,
    snapshot_lengths n live snap ->
    snapshot_cells_wf n live snap ->
    0 <= j < live ->
    Zlength (Znth j (snap_rows snap) (@nil Z)) = n.
Proof.
  intros n live snap j Hlengths Hcells Hj.
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as [_ [_ [_ [Hrows_length _]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [_ Hrows_wf].
  revert live j Hj Hrows_length.
  induction Hrows_wf as [|row rows Hrow Hrows_wf IH];
    intros live j Hj Hrows_length.
  - rewrite Zlength_nil in Hrows_length. lia.
  - rewrite Zlength_cons in Hrows_length.
    destruct (Z.eq_dec j 0) as [->|Hj0].
    + rewrite Znth0_cons. exact (proj1 Hrow).
    + rewrite Znth_cons by lia.
      apply (IH (live - 1) (j - 1)); lia.
Qed.
Lemma clears_one_assignment_eq_clear_partial__backtrack_entry_clear_a :
  forall old new x,
    clears_one old new x ->
    assignment new = clear_partial (assignment old) x.
Proof.
  intros old new x Hclear.
  unfold clears_one in Hclear.
  destruct Hclear as
    [[b [d [Holdx _]]] [Hnewx [_ [_ [_ [Hother _]]]]]].
  apply functional_extensionality; intro y.
  destruct (Z.eq_dec y x) as [->|Hyx].
  - unfold clear_partial. rewrite Mapping.total_mapping_update_eq.
    exact Hnewx.
  - unfold clear_partial.
    rewrite Mapping.total_mapping_update_neq by lia.
    apply Hother. exact Hyx.
Qed.
Lemma dense_decode_from_pos_counts__backtrack_entry_clear_a :
  forall row base i,
    0 <= i < Zlength row ->
    Znth i row 0 = 1 ->
    literal_var_count (base + i) (dense_decode_from base row) = 1 /\
    literal_true_at_count (base + i) true
      (dense_decode_from base row) = 1.
Proof.
  induction row as [|z row IH]; intros base i Hi Hcell.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons in Hcell. subst z.
      cbn [dense_decode_from literal_var_count literal_true_at_count
        literal_var eval_literal].
      replace (base + 0) with base by lia.
      rewrite Z.eqb_refl.
      pose proof
        (dense_decode_from_counts_before__bcp_assignment_summary_a
          row (base + 1) base true ltac:(lia)) as [Hvar Htrue].
      cbn [literal_var_count literal_true_at_count literal_var eval_literal].
      rewrite Z.eqb_refl.
      rewrite Hvar, Htrue. split; lia.
    + rewrite Znth_cons in Hcell by lia.
      specialize (IH (base + 1) (i - 1) ltac:(lia) Hcell).
      replace ((base + 1) + (i - 1)) with (base + i) in IH by lia.
      cbn [dense_decode_from].
      assert (Hneq : (base =? base + i) = false).
      { apply Z.eqb_neq. lia. }
      destruct (z =? 1) eqn:Hz1.
      * cbn [literal_var_count literal_true_at_count literal_var eval_literal].
        rewrite Hneq. exact IH.
      * destruct (z =? -1) eqn:Hzm.
        -- cbn [literal_var_count literal_true_at_count literal_var eval_literal].
           rewrite Hneq. exact IH.
        -- exact IH.
Qed.
Lemma dense_decode_from_neg_counts__backtrack_entry_clear_a :
  forall row base i,
    0 <= i < Zlength row ->
    Znth i row 0 = -1 ->
    literal_var_count (base + i) (dense_decode_from base row) = 1 /\
    literal_true_at_count (base + i) false
      (dense_decode_from base row) = 1.
Proof.
  induction row as [|z row IH]; intros base i Hi Hcell.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons in Hcell. subst z.
      cbn [dense_decode_from literal_var_count literal_true_at_count
        literal_var eval_literal].
      replace (base + 0) with base by lia.
      rewrite Z.eqb_refl.
      replace (-1 =? 1) with false by reflexivity.
      pose proof
        (dense_decode_from_counts_before__bcp_assignment_summary_a
          row (base + 1) base false ltac:(lia)) as [Hvar Htrue].
      cbn [literal_var_count literal_true_at_count literal_var eval_literal].
      rewrite Z.eqb_refl.
      rewrite Hvar, Htrue. cbn. split; lia.
    + rewrite Znth_cons in Hcell by lia.
      specialize (IH (base + 1) (i - 1) ltac:(lia) Hcell).
      replace ((base + 1) + (i - 1)) with (base + i) in IH by lia.
      cbn [dense_decode_from].
      assert (Hneq : (base =? base + i) = false).
      { apply Z.eqb_neq. lia. }
      destruct (z =? 1) eqn:Hz1.
      * cbn [literal_var_count literal_true_at_count literal_var eval_literal].
        rewrite Hneq. exact IH.
      * destruct (z =? -1) eqn:Hzm.
        -- cbn [literal_var_count literal_true_at_count literal_var eval_literal].
           rewrite Hneq. exact IH.
        -- exact IH.
Qed.
Lemma dense_decode_pos_counts__backtrack_entry_clear_a :
  forall row i,
    0 <= i < Zlength row ->
    Znth i row 0 = 1 ->
    literal_var_count i (dense_decode row) = 1 /\
    literal_true_at_count i true (dense_decode row) = 1.
Proof.
  intros row i Hi Hcell.
  unfold dense_decode.
  replace i with (0 + i) by lia.
  apply dense_decode_from_pos_counts__backtrack_entry_clear_a; assumption.
Qed.
Lemma dense_decode_neg_counts__backtrack_entry_clear_a :
  forall row i,
    0 <= i < Zlength row ->
    Znth i row 0 = -1 ->
    literal_var_count i (dense_decode row) = 1 /\
    literal_true_at_count i false (dense_decode row) = 1.
Proof.
  intros row i Hi Hcell.
  unfold dense_decode.
  replace i with (0 + i) by lia.
  apply dense_decode_from_neg_counts__backtrack_entry_clear_a; assumption.
Qed.
Lemma expected_clause_state_clear_gt1__backtrack_entry_clear_a :
  forall sigma x b c,
    sigma x = Some b ->
    literal_var_count x c = 1 ->
    literal_true_at_count x b c = 1 ->
    1 < clause_true_count sigma c ->
    expected_clause_state (clear_partial sigma x) c = 0.
Proof.
  intros sigma x b c Hx Hvar Hsat Hgt.
  pose proof (clause_counts_clear sigma x b c Hx)
    as [Hclearunassigned Hcleartrue].
  unfold expected_clause_state.
  rewrite Hcleartrue, Hsat.
  destruct (0 <? clause_true_count sigma c - 1) eqn:Hpositive.
  - reflexivity.
  - apply Z.ltb_ge in Hpositive. lia.
Qed.
Lemma expected_clause_state_clear_middle__backtrack_entry_clear_a :
  forall sigma x b c t u,
    sigma x = Some b ->
    literal_var_count x c = 1 ->
    literal_true_at_count x b c = 1 ->
    t = clause_true_count sigma c ->
    u = clause_unassigned_count sigma c ->
    expected_clause_state sigma c = 0 ->
    u > 0 ->
    t <= 1 ->
    expected_clause_state (clear_partial sigma x) c = -u - 1.
Proof.
  intros sigma x b c t u Hx Hvar Hsat Ht Hu Holdstate Hu0 Ht1.
  pose proof (clause_counts_clear sigma x b c Hx)
    as [Hclearunassigned Hcleartrue].
  assert (Ht0 : 0 < t).
  { unfold expected_clause_state in Holdstate.
    rewrite <- Ht, <- Hu in Holdstate.
    destruct (0 <? t) eqn:Hpositive; [apply Z.ltb_lt; assumption|].
    apply Z.ltb_ge in Hpositive.
    destruct (u =? 0) eqn:Hu_eq0.
    - apply Z.eqb_eq in Hu_eq0. lia.
    - destruct (u =? 1) eqn:Hu_eq1.
      + discriminate.
      + lia. }
  unfold expected_clause_state.
  rewrite Hcleartrue, Hclearunassigned, Hsat, Hvar.
  rewrite <- Ht, <- Hu.
  assert (Ht_eq : t = 1) by lia.
  replace t with 1 by (symmetry; exact Ht_eq).
  replace (0 <? 1 - 1) with false by reflexivity.
  replace (u + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (u + 1 =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
  lia.
Qed.
Lemma expected_clause_state_clear_last__backtrack_entry_clear_a :
  forall sigma x b c t u,
    sigma x = Some b ->
    literal_var_count x c = 1 ->
    literal_true_at_count x b c = 1 ->
    t = clause_true_count sigma c ->
    u = clause_unassigned_count sigma c ->
    expected_clause_state sigma c = 0 ->
    u <= 0 ->
    t <= 1 ->
    expected_clause_state (clear_partial sigma x) c = 2.
Proof.
  intros sigma x b c t u Hx Hvar Hsat Ht Hu Holdstate Hu0 Ht1.
  pose proof
    (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment sigma c)
    as Hnonnegative.
  assert (Hu_eq : u = 0) by lia.
  assert (Ht0 : 0 < t).
  { unfold expected_clause_state in Holdstate.
    rewrite <- Ht, <- Hu in Holdstate.
    destruct (0 <? t) eqn:Hpositive; [apply Z.ltb_lt; assumption|].
    apply Z.ltb_ge in Hpositive.
    replace u with 0 in Holdstate by (symmetry; exact Hu_eq).
    replace (0 =? 0) with true in Holdstate by reflexivity.
    discriminate. }
  assert (Ht_eq : t = 1) by lia.
  pose proof (clause_counts_clear sigma x b c Hx)
    as [Hclearunassigned Hcleartrue].
  unfold expected_clause_state.
  rewrite Hcleartrue, Hclearunassigned, Hsat, Hvar.
  rewrite <- Ht, <- Hu.
  replace t with 1 by (symmetry; exact Ht_eq).
  replace u with 0 by (symmetry; exact Hu_eq).
  reflexivity.
Qed.
Lemma mixed_clause_summaries_advance__backtrack_entry_clear_a :
  forall old_sigma new_sigma rows states true_counts unassigned
      live cap j new_state new_true new_unassigned,
    mixed_clause_summaries old_sigma new_sigma rows states true_counts
      unassigned live cap j None ->
    0 <= j < live ->
    summary_at new_sigma rows
      (replace_Znth j new_state states)
      (replace_Znth j new_true true_counts)
      (replace_Znth j new_unassigned unassigned) j ->
    mixed_clause_summaries old_sigma new_sigma rows
      (replace_Znth j new_state states)
      (replace_Znth j new_true true_counts)
      (replace_Znth j new_unassigned unassigned)
      live cap (j + 1) None.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned
    live cap j new_state new_true new_unassigned Hmix Hj Hnewj.
  unfold mixed_clause_summaries in *.
  destruct Hmix as
    [Hrows [Hstates [Htrue [Hunassigned [Hcap [Hprocessed Hsummaries]]]]]].
  repeat rewrite Zlength_replace_Znth.
  split; [exact Hrows|].
  split; [exact Hstates|].
  split; [exact Htrue|].
  split; [exact Hunassigned|].
  split; [exact Hcap|].
  split; [lia|].
  intros k Hk.
  specialize (Hsummaries k Hk).
  destruct Hsummaries as [Hs_new Hs_old].
  split.
  - intros [Hklt|Hnone]; [|discriminate].
    destruct (Z.eq_dec k j) as [->|Hkj].
    + exact Hnewj.
    + assert (Hkjlt : k < j) by lia.
      specialize (Hs_new (or_introl Hkjlt)).
      unfold summary_at.
      rewrite (Znth_replace_Znth_Diff 0 states j k new_state) by lia.
      rewrite (Znth_replace_Znth_Diff 0 true_counts j k new_true) by lia.
      rewrite (Znth_replace_Znth_Diff 0 unassigned j k new_unassigned) by lia.
      exact Hs_new.
  - intros [Hjk Hnone].
    assert (Hjlek : j <= k) by lia.
    assert (Hnot : None <> Some k) by discriminate.
    specialize (Hs_old (conj Hjlek Hnot)).
    unfold summary_at.
    rewrite (Znth_replace_Znth_Diff 0 states j k new_state) by lia.
    rewrite (Znth_replace_Znth_Diff 0 true_counts j k new_true) by lia.
    rewrite (Znth_replace_Znth_Diff 0 unassigned j k new_unassigned) by lia.
    exact Hs_old.
Qed.
(** ===== group: backtrack_clear_b ===== *)
Lemma installed_clause_Znth_dense_decode__backtrack_clear_b :
  forall n snap ranks dl i,
    Znth i
      (installed_clauses (cdcl_view_of_snapshot n snap ranks dl))
      (@nil literal) =
    dense_decode (Znth i (snap_rows snap) (@nil Z)).
Proof.
  intros n snap ranks dl i.
  cbv beta delta [cdcl_view_of_snapshot installed_clauses].
  cbv beta iota.
  unfold Znth.
  replace (@nil literal) with (dense_decode (@nil Z)) by reflexivity.
  apply map_nth.
Qed.
Lemma literal_counts_dense_decode_from_true__backtrack_clear_b :
  forall row base k b,
    0 <= k < Zlength row ->
    ((Znth k row 0 = 1 /\ b = true) \/
     (Znth k row 0 = -1 /\ b = false)) ->
    literal_var_count (base + k) (dense_decode_from base row) = 1 /\
    literal_true_at_count (base + k) b
      (dense_decode_from base row) = 1.
Proof.
  induction row as [|z row IH]; intros base k b Hk Htrue.
  - rewrite Zlength_nil in Hk; lia.
  - rewrite Zlength_cons in Hk.
    destruct (Z.eq_dec k 0) as [->|Hk0].
    + rewrite Znth0_cons in Htrue.
      destruct Htrue as [[Hz Hb]|[Hz Hb]]; subst z; subst b.
      * pose proof
          (dense_decode_from_counts_before__bcp_assignment_summary_a
             row (base + 1) base true ltac:(lia)) as [Hv Ht].
        replace (base + 0) with base by lia.
        cbn [dense_decode_from].
        rewrite Z.eqb_refl.
        cbn [literal_var_count literal_true_at_count literal_var eval_literal].
        rewrite Z.eqb_refl, Hv, Ht; simpl; lia.
      * pose proof
          (dense_decode_from_counts_before__bcp_assignment_summary_a
             row (base + 1) base false ltac:(lia)) as [Hv Ht].
        replace (base + 0) with base by lia.
        cbn [dense_decode_from].
        assert (Hminus : Z.eqb (-1) 1 = false) by reflexivity.
        rewrite Hminus, Z.eqb_refl.
        cbn [literal_var_count literal_true_at_count literal_var eval_literal].
        rewrite Z.eqb_refl, Hv, Ht; simpl; lia.
    + rewrite Znth_cons in Htrue by lia.
      replace (base + k) with ((base + 1) + (k - 1)) by lia.
      specialize (IH (base + 1) (k - 1) b ltac:(lia) Htrue).
      simpl [dense_decode_from].
      destruct (Z.eqb z 1) eqn:Hz1.
      * cbn [literal_var_count literal_true_at_count literal_var].
        assert (Hneq : Z.eqb base (base + 1 + (k - 1)) = false) by
          (apply Z.eqb_neq; lia).
        rewrite Hneq; exact IH.
      * destruct (Z.eqb z (-1)) eqn:Hzm.
        -- cbn [literal_var_count literal_true_at_count literal_var].
           assert (Hneq : Z.eqb base (base + 1 + (k - 1)) = false) by
             (apply Z.eqb_neq; lia).
           rewrite Hneq; exact IH.
        -- exact IH.
Qed.
Lemma literal_counts_dense_decode_true__backtrack_clear_b :
  forall row k b,
    0 <= k < Zlength row ->
    ((Znth k row 0 = 1 /\ b = true) \/
     (Znth k row 0 = -1 /\ b = false)) ->
    literal_var_count k (dense_decode row) = 1 /\
    literal_true_at_count k b (dense_decode row) = 1.
Proof.
  intros row k b Hk Htrue.
  unfold dense_decode.
  replace k with (0 + k) by lia.
  apply literal_counts_dense_decode_from_true__backtrack_clear_b;
    assumption.
Qed.
Lemma literal_counts_dense_decode_from_false__backtrack_clear_b :
  forall row base k b,
    0 <= k < Zlength row ->
    ((Znth k row 0 = 1 /\ b = false) \/
     (Znth k row 0 = -1 /\ b = true)) ->
    literal_var_count (base + k) (dense_decode_from base row) = 1 /\
    literal_true_at_count (base + k) b
      (dense_decode_from base row) = 0.
Proof.
  induction row as [|z row IH]; intros base k b Hk Hfalse.
  - rewrite Zlength_nil in Hk; lia.
  - rewrite Zlength_cons in Hk.
    destruct (Z.eq_dec k 0) as [->|Hk0].
    + rewrite Znth0_cons in Hfalse.
      destruct Hfalse as [[Hz Hb]|[Hz Hb]]; subst z; subst b.
      * pose proof
          (dense_decode_from_counts_before__bcp_assignment_summary_a
             row (base + 1) base false ltac:(lia)) as [Hv Ht].
        replace (base + 0) with base by lia.
        cbn [dense_decode_from].
        rewrite Z.eqb_refl.
        cbn [literal_var_count literal_true_at_count literal_var eval_literal].
        rewrite Z.eqb_refl, Hv, Ht; simpl; lia.
      * pose proof
          (dense_decode_from_counts_before__bcp_assignment_summary_a
             row (base + 1) base true ltac:(lia)) as [Hv Ht].
        replace (base + 0) with base by lia.
        cbn [dense_decode_from].
        assert (Hminus : Z.eqb (-1) 1 = false) by reflexivity.
        rewrite Hminus, Z.eqb_refl.
        cbn [literal_var_count literal_true_at_count literal_var eval_literal].
        rewrite Z.eqb_refl, Hv, Ht; simpl; lia.
    + rewrite Znth_cons in Hfalse by lia.
      replace (base + k) with ((base + 1) + (k - 1)) by lia.
      specialize (IH (base + 1) (k - 1) b ltac:(lia) Hfalse).
      simpl [dense_decode_from].
      destruct (Z.eqb z 1) eqn:Hz1.
      * cbn [literal_var_count literal_true_at_count literal_var].
        assert (Hneq : Z.eqb base (base + 1 + (k - 1)) = false) by
          (apply Z.eqb_neq; lia).
        rewrite Hneq; exact IH.
      * destruct (Z.eqb z (-1)) eqn:Hzm.
        -- cbn [literal_var_count literal_true_at_count literal_var].
           assert (Hneq : Z.eqb base (base + 1 + (k - 1)) = false) by
             (apply Z.eqb_neq; lia).
           rewrite Hneq; exact IH.
        -- exact IH.
Qed.
Lemma literal_counts_dense_decode_false__backtrack_clear_b :
  forall row k b,
    0 <= k < Zlength row ->
    ((Znth k row 0 = 1 /\ b = false) \/
     (Znth k row 0 = -1 /\ b = true)) ->
    literal_var_count k (dense_decode row) = 1 /\
    literal_true_at_count k b (dense_decode row) = 0.
Proof.
  intros row k b Hk Hfalse.
  unfold dense_decode.
  replace k with (0 + k) by lia.
  apply literal_counts_dense_decode_from_false__backtrack_clear_b;
    assumption.
Qed.
Lemma mixed_clause_summaries_advance__backtrack_clear_b :
  forall old_sigma new_sigma rows states true_counts unassigned
         live cap j new_state new_true new_unassigned,
    mixed_clause_summaries old_sigma new_sigma
      rows states true_counts unassigned live cap j None ->
    0 <= j < live ->
    clause_summary_ok new_sigma (Znth j rows (nil : clause))
      new_state new_true new_unassigned ->
    mixed_clause_summaries old_sigma new_sigma rows
      (replace_Znth j new_state states)
      (replace_Znth j new_true true_counts)
      (replace_Znth j new_unassigned unassigned)
      live cap (j + 1) None.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned
    live cap j new_state new_true new_unassigned Hmixed Hj Hsummary.
  unfold mixed_clause_summaries in *.
  destruct Hmixed as
    [Hrows [Hstates [Htrue [Hunassigned [Hcap [Hprocessed Hmixed]]]]]].
  split; [exact Hrows|].
  split; [rewrite Zlength_replace_Znth; exact Hstates|].
  split; [rewrite Zlength_replace_Znth; exact Htrue|].
  split; [rewrite Zlength_replace_Znth; exact Hunassigned|].
  split; [exact Hcap|].
  split; [lia|].
  intros k Hk; specialize (Hmixed k Hk).
    destruct Hmixed as [Hnew Hold].
    split.
    + intros [Hlt|Hnone]; [|discriminate].
      destruct (Z.eq_dec k j) as [->|Hkj].
      * unfold summary_at.
        rewrite !Znth_replace_Znth_Same by lia.
        exact Hsummary.
      * assert (Hkjlt : k < j) by lia.
        specialize (Hnew (or_introl Hkjlt)).
        unfold summary_at in *.
        rewrite !Znth_replace_Znth_Diff by lia.
        exact Hnew.
    + intros [Hge Hnone].
      assert (Hjk : j <= k) by lia.
      assert (Hnone_old : None <> Some k) by discriminate.
      specialize (Hold (conj Hjk Hnone_old)).
      unfold summary_at in *.
      rewrite !Znth_replace_Znth_Diff by lia.
      exact Hold.
Qed.
Lemma mixed_clause_summaries_advance_unassigned_only__backtrack_clear_b :
  forall old_sigma new_sigma rows states true_counts unassigned
         live cap j new_unassigned,
    mixed_clause_summaries old_sigma new_sigma
      rows states true_counts unassigned live cap j None ->
    0 <= j < live ->
    clause_summary_ok new_sigma (Znth j rows (nil : clause))
      (Znth j states 0) (Znth j true_counts 0) new_unassigned ->
    mixed_clause_summaries old_sigma new_sigma rows
      states true_counts
      (replace_Znth j new_unassigned unassigned)
      live cap (j + 1) None.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned
    live cap j new_unassigned Hmixed Hj Hsummary.
  pose proof (mixed_clause_summaries_advance__backtrack_clear_b
    old_sigma new_sigma rows states true_counts unassigned live cap j
    (Znth j states 0) (Znth j true_counts 0) new_unassigned
    Hmixed Hj Hsummary) as H.
  rewrite !replace_Znth_Znth in H.
  exact H.
Qed.
Lemma mixed_clause_summaries_advance_state_unassigned__backtrack_clear_b :
  forall old_sigma new_sigma rows states true_counts unassigned
         live cap j new_state new_unassigned,
    mixed_clause_summaries old_sigma new_sigma
      rows states true_counts unassigned live cap j None ->
    0 <= j < live ->
    clause_summary_ok new_sigma (Znth j rows (nil : clause))
      new_state (Znth j true_counts 0) new_unassigned ->
    mixed_clause_summaries old_sigma new_sigma rows
      (replace_Znth j new_state states) true_counts
      (replace_Znth j new_unassigned unassigned)
      live cap (j + 1) None.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned
    live cap j new_state new_unassigned Hmixed Hj Hsummary.
  pose proof (mixed_clause_summaries_advance__backtrack_clear_b
    old_sigma new_sigma rows states true_counts unassigned live cap j
    new_state (Znth j true_counts 0) new_unassigned
    Hmixed Hj Hsummary) as H.
  rewrite !replace_Znth_Znth in H.
  exact H.
Qed.
Lemma backtrack_summary_clear_step__backtrack_clear_b :
  forall old new rows states true_counts unassigned live cap j i b delta
         new_state,
    clears_one old new i ->
    mixed_clause_summaries (assignment old) (assignment new)
      rows states true_counts unassigned live cap j None ->
    0 <= j < live ->
    assignment old i = Some b ->
    literal_var_count i (Znth j rows (nil : clause)) = 1 ->
    literal_true_at_count i b (Znth j rows (nil : clause)) = delta ->
    expected_clause_state (assignment new) (Znth j rows (nil : clause)) = new_state ->
    mixed_clause_summaries (assignment old) (assignment new) rows
      (replace_Znth j new_state states)
      (replace_Znth j (Znth j true_counts 0 - delta) true_counts)
      (replace_Znth j (Znth j unassigned 0 + 1) unassigned)
      live cap (j + 1) None.
Proof.
  intros old new rows states true_counts unassigned live cap j i b delta
    new_state Hclear Hmixed Hj Hassign Hvar Htrue Hstate.
  assert (Hold_summary :
    clause_summary_ok (assignment old) (Znth j rows (nil : clause))
      (Znth j states 0) (Znth j true_counts 0)
      (Znth j unassigned 0)).
  { unfold mixed_clause_summaries in Hmixed.
    destruct Hmixed as [_ [_ [_ [_ [_ [_ Hmixed]]]]]].
    specialize (Hmixed j Hj).
    destruct Hmixed as [_ Hold].
    apply Hold; split; [lia|discriminate]. }
  pose proof Hmixed as Hmixed_keep.
  apply mixed_clause_summaries_advance__backtrack_clear_b;
    [exact Hmixed_keep|exact Hj|].
  unfold clause_summary_ok in *.
  destruct Hold_summary as [Hold_true [Hold_unassigned Hold_state]].
  pose proof (clause_counts_clear
    (assignment old) i b (Znth j rows (nil : clause)) Hassign) as [Hnew_u Hnew_t].
  pose proof (clears_one_assignment_eq_clear_partial__backtrack_entry_clear_a
    old new i Hclear) as Hclear_assignment.
  rewrite Hclear_assignment.
  rewrite Hnew_t, Hnew_u, Hvar, Htrue.
  split; [lia|].
  split; [lia|].
  rewrite <- Hclear_assignment.
  symmetry; exact Hstate.
Qed.
Lemma backtrack_summary_clear_step_false_unchanged__backtrack_clear_b :
  forall old new rows states true_counts unassigned live cap j i b,
    clears_one old new i ->
    mixed_clause_summaries (assignment old) (assignment new)
      rows states true_counts unassigned live cap j None ->
    0 <= j < live ->
    assignment old i = Some b ->
    literal_var_count i (Znth j rows (nil : clause)) = 1 ->
    literal_true_at_count i b (Znth j rows (nil : clause)) = 0 ->
    Znth j states 0 = 0 ->
    mixed_clause_summaries (assignment old) (assignment new) rows
      states true_counts
      (replace_Znth j (Znth j unassigned 0 + 1) unassigned)
      live cap (j + 1) None.
Proof.
  intros old new rows states true_counts unassigned live cap j i b
    Hclear Hmixed Hj Hassign Hvar Htrue Hstate0.
  assert (Hold_summary :
    clause_summary_ok (assignment old) (Znth j rows (nil : clause))
      (Znth j states 0) (Znth j true_counts 0)
      (Znth j unassigned 0)).
  { unfold mixed_clause_summaries in Hmixed.
    destruct Hmixed as [_ [_ [_ [_ [_ [_ Hmixed]]]]]].
    specialize (Hmixed j Hj).
    destruct Hmixed as [_ Hold].
    apply Hold; split; [lia|discriminate]. }
  pose proof Hmixed as Hmixed_keep.
  apply mixed_clause_summaries_advance_unassigned_only__backtrack_clear_b;
    [exact Hmixed_keep|exact Hj|].
  unfold clause_summary_ok in *.
  destruct Hold_summary as [Hold_true [Hold_unassigned Hold_state]].
  pose proof (clause_counts_clear
    (assignment old) i b (Znth j rows (nil : clause)) Hassign) as [Hnew_u Hnew_t].
  pose proof (clears_one_assignment_eq_clear_partial__backtrack_entry_clear_a
    old new i Hclear) as Hclear_assignment.
  assert (Htpos : 0 < clause_true_count (assignment old) (Znth j rows (nil : clause))).
  { assert (Hold_state' := Hold_state).
    rewrite Hstate0 in Hold_state'.
    unfold expected_clause_state in Hold_state'.
    destruct (Z.ltb 0 (clause_true_count (assignment old) (Znth j rows (nil : clause))))
      eqn:E.
    - apply Z.ltb_lt in E; exact E.
    - apply Z.ltb_ge in E.
      destruct (Z.eqb (clause_unassigned_count (assignment old) (Znth j rows (nil : clause))) 0)
        eqn:E0; [discriminate|].
      destruct (Z.eqb (clause_unassigned_count (assignment old) (Znth j rows (nil : clause))) 1)
        eqn:E1; [discriminate|].
      apply Z.eqb_neq in E0.
      lia. }
  rewrite Hclear_assignment.
  rewrite Hnew_u, Hvar.
  split.
  - rewrite Hnew_t, Htrue.
    lia.
  - split; [lia|].
    rewrite Hstate0.
    unfold expected_clause_state.
    rewrite Hnew_t, Htrue.
    replace (clause_true_count (assignment old) (Znth j rows (nil : clause)) - 0)
      with (clause_true_count (assignment old) (Znth j rows (nil : clause))) by lia.
    destruct (Z.ltb 0 (clause_true_count (assignment old) (Znth j rows (nil : clause))))
      eqn:E2.
    + reflexivity.
    + apply Z.ltb_ge in E2; lia.
Qed.
Lemma clause_summary_true_literal_state_zero__backtrack_clear_b :
  forall sigma c x b state true_count unassigned_count,
    sigma x = Some b ->
    literal_true_at_count x b c = 1 ->
    clause_summary_ok sigma c state true_count unassigned_count ->
    state = 0.
Proof.
  intros sigma c x b state true_count unassigned_count
    Hassign Hliteral Hsummary.
  destruct Hsummary as [_ [_ Hstate]].
  pose proof (clause_counts_clear sigma x b c Hassign) as [_ Hclear_true].
  pose proof (clause_counts_nonnegative__bcp_assignment_summary_d
    (clear_partial sigma x) c) as [Hnonneg _].
  rewrite Hliteral in Hclear_true.
  unfold expected_clause_state in Hstate.
  assert (Htpos : Z.ltb 0 (clause_true_count sigma c) = true).
  { apply Z.ltb_lt; lia. }
  rewrite Htpos in Hstate.
  exact Hstate.
Qed.
Lemma clause_summary_state_one_counts__backtrack_clear_b :
  forall sigma c true_count unassigned_count,
    clause_summary_ok sigma c 1 true_count unassigned_count ->
    true_count = 0 /\ unassigned_count = 0.
Proof.
  intros sigma c true_count unassigned_count Hsummary.
  destruct Hsummary as [Ht [Hu Hstate]].
  pose proof (clause_counts_nonnegative__bcp_assignment_summary_d sigma c)
    as [Htnonneg Hunonneg].
  unfold expected_clause_state in Hstate.
  destruct (Z.ltb 0 (clause_true_count sigma c)) eqn:Htpos;
    [discriminate|].
  apply Z.ltb_ge in Htpos.
  destruct (Z.eqb (clause_unassigned_count sigma c) 0) eqn:Hu0.
  - apply Z.eqb_eq in Hu0; lia.
  - destruct (Z.eqb (clause_unassigned_count sigma c) 1) eqn:Hu1.
    + discriminate.
    + apply Z.eqb_neq in Hu0.
      apply Z.eqb_neq in Hu1.
      lia.
Qed.
Lemma clause_summary_state_two_counts__backtrack_clear_b :
  forall sigma c true_count unassigned_count,
    clause_summary_ok sigma c 2 true_count unassigned_count ->
    true_count = 0 /\ unassigned_count = 1.
Proof.
  intros sigma c true_count unassigned_count Hsummary.
  destruct Hsummary as [Ht [Hu Hstate]].
  pose proof (clause_counts_nonnegative__bcp_assignment_summary_d sigma c)
    as [Htnonneg Hunonneg].
  unfold expected_clause_state in Hstate.
  destruct (Z.ltb 0 (clause_true_count sigma c)) eqn:Htpos;
    [discriminate|].
  apply Z.ltb_ge in Htpos.
  destruct (Z.eqb (clause_unassigned_count sigma c) 0) eqn:Hu0;
    [discriminate|].
  destruct (Z.eqb (clause_unassigned_count sigma c) 1) eqn:Hu1.
  - apply Z.eqb_eq in Hu1; lia.
  - apply Z.eqb_neq in Hu0.
    apply Z.eqb_neq in Hu1.
    lia.
Qed.
(** ===== group: backtrack_finish_decide_bounds ===== *)
Lemma Znth_map_dense_decode__backtrack_finish_decide_bounds : forall rows i,
  Znth i (List.map dense_decode rows) [] =
    dense_decode (Znth i rows []).
Proof.
  intros rows i.
  unfold Znth.
  change (nth (Z.to_nat i) (List.map dense_decode rows)
      (dense_decode []) =
    dense_decode (nth (Z.to_nat i) rows [])).
  apply map_nth.
Qed.
Lemma clause_true_count_bounds__backtrack_finish_decide_bounds : forall sigma c,
  0 <= clause_true_count sigma c <= Z.of_nat (List.length c).
Proof.
  intros sigma c; induction c as [|l c IH].
  - cbn [clause_true_count]; lia.
  - change (0 <= clause_true_count sigma (l :: c) <=
      Z.of_nat (S (List.length c))).
    rewrite Nat2Z.inj_succ.
    cbn [clause_true_count].
    destruct (eval_partial_literal sigma l) as [[|]|]; lia.
Qed.
Lemma expected_clause_state_two_true_zero__backtrack_finish_decide_bounds :
  forall sigma c,
  expected_clause_state sigma c = 2 -> clause_true_count sigma c = 0.
Proof.
  intros sigma c Hstate.
  unfold expected_clause_state in Hstate.
  destruct (Z.ltb 0 (clause_true_count sigma c)) eqn:Htrue.
  - discriminate.
  - apply Z.ltb_ge in Htrue.
    pose proof (clause_true_count_bounds__backtrack_finish_decide_bounds
      sigma c) as Hbounds.
    lia.
Qed.
Lemma expected_clause_state_domain__backtrack_finish_decide_bounds :
  forall sigma c,
  expected_clause_state sigma c = 0 \/
  expected_clause_state sigma c = 1 \/
  expected_clause_state sigma c = 2 \/
  expected_clause_state sigma c < 0.
Proof.
  intros sigma c.
  unfold expected_clause_state.
  destruct (Z.ltb 0 (clause_true_count sigma c)) eqn:Htrue.
  - left; reflexivity.
  - destruct (Z.eqb (clause_unassigned_count sigma c) 0) eqn:Hun0.
    + right; left; reflexivity.
    + destruct (Z.eqb (clause_unassigned_count sigma c) 1) eqn:Hun1.
      * right; right; left; reflexivity.
      * right; right; right.
        apply Z.eqb_neq in Hun0.
        pose proof
          (clause_unassigned_count_bounds__backtrack_entry_clear_a
            sigma c) as Hbounds.
        lia.
Qed.
Lemma snapshot_level_unassigned__backtrack_finish_decide_bounds :
  forall n snap i,
  0 <= i < n ->
  Znth i (snap_values snap) (-1) = -1 ->
  snapshot_level n snap i = None.
Proof.
  intros n snap i [Hi0 Hin] Hvalue.
  unfold snapshot_level, snapshot_assignment.
  assert (Hguard : andb (Z.leb 0 i) (Z.ltb i n) = true).
  { apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; assumption. }
  rewrite Hguard.
  rewrite Hvalue; reflexivity.
Qed.
Lemma snapshot_level_assigned__backtrack_finish_decide_bounds :
  forall n live snap i,
  snapshot_cells_wf n live snap ->
  0 <= i < n ->
  Znth i (snap_values snap) (-1) <> -1 ->
  snapshot_level n snap i = Some (Znth i (snap_levels snap) (-1)).
Proof.
  intros n live snap i Hwf [Hi0 Hin] Hassigned.
  unfold snapshot_cells_wf in Hwf.
  destruct Hwf as [Hcells _].
  specialize (Hcells i ltac:(unfold var_in_range; lia)).
  cbn in Hcells.
  destruct Hcells as [Hvalue _].
  unfold snapshot_level, snapshot_assignment.
  assert (Hguard : andb (Z.leb 0 i) (Z.ltb i n) = true).
  { apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; assumption. }
  rewrite Hguard.
  destruct Hvalue as [Hminus | [Hzero | Hone]]; try contradiction;
    rewrite Hzero || rewrite Hone; reflexivity.
Qed.
Lemma prefix_restriction_advance_unchanged__backtrack_finish_decide_bounds :
  forall old current n target i,
  prefix_restriction old current n target i ->
  0 <= i < n ->
  (forall d, level_of old i = Some d -> d <= target) ->
  prefix_restriction old current n target (i + 1).
Proof.
  intros old current n target i Hprefix Hirange Hlevel.
  destruct Hprefix as [Hprocessed [Hclauses Hcells]].
  split; [lia|].
  split; [exact Hclauses|].
  intros x Hxrange.
  specialize (Hcells x Hxrange).
  destruct Hcells as [Hbefore Hafter].
  split.
  - intros Hxnext.
    destruct (Z_lt_ge_dec x i) as [Hxi | Hix].
    + apply Hbefore; lia.
    + assert (x = i) by lia; subst x.
      specialize (Hafter ltac:(lia)).
      destruct Hafter as [Ha [Hl [Hr Hrank]]].
      destruct (level_of old i) as [d|] eqn:Hold.
      * specialize (Hlevel d eq_refl).
        destruct (Z.ltb target d) eqn:Htd.
        -- apply Z.ltb_lt in Htd; lia.
        -- repeat split; assumption.
      * repeat split; assumption.
  - intros Hnext.
    apply Hafter; lia.
Qed.
Lemma prefix_restriction_advance_clear__backtrack_finish_decide_bounds :
  forall old current after n target i d,
  prefix_restriction old current n target i ->
  clears_one current after i ->
  0 <= i < n ->
  level_of old i = Some d ->
  target < d ->
  prefix_restriction old after n target (i + 1).
Proof.
  intros old current after n target i d Hprefix Hclear Hirange Hold Htarget.
  destruct Hprefix as [Hprocessed [Hclauses Hcells]].
  destruct Hclear as [_ [Hai [Hli [Hri [Hranki [Hother Hafterclauses]]]]]].
  split; [lia|].
  split.
  - rewrite Hafterclauses; exact Hclauses.
  - intros x Hxrange.
    specialize (Hcells x Hxrange).
    destruct Hcells as [Hbefore Hafter].
    split.
    + intros Hxnext.
      destruct (Z_lt_ge_dec x i) as [Hxi | Hix].
      * specialize (Hother x ltac:(lia)).
        destruct Hother as [Ha [Hl [Hr Hrank]]].
        rewrite Ha, Hl, Hr, Hrank.
        apply Hbefore; exact Hxi.
      * assert (x = i) by lia; subst x.
        rewrite Hold.
        destruct (Z.ltb target d) eqn:Htd.
        -- repeat split; assumption.
        -- apply Z.ltb_ge in Htd; lia.
    + intros Hnext.
      specialize (Hother x ltac:(lia)).
      destruct Hother as [Ha [Hl [Hr Hrank]]].
      rewrite Ha, Hl, Hr, Hrank.
      apply Hafter; lia.
Qed.
Lemma clause_true_count_positive__backtrack_finish_decide_bounds :
  forall sigma c l,
  In l c -> eval_partial_literal sigma l = Some true ->
  0 < clause_true_count sigma c.
Proof.
  intros sigma c; induction c as [|h c IH]; intros l Hin Heval.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + cbn [clause_true_count]. rewrite Heval.
      change (0 < 1 + clause_true_count sigma c).
      pose proof (clause_true_count_bounds__backtrack_finish_decide_bounds
        sigma c); lia.
    + specialize (IH l Hin Heval).
      cbn [clause_true_count].
      destruct (eval_partial_literal sigma h) as [[|]|].
      * change (0 < 1 + clause_true_count sigma c).
        pose proof (clause_true_count_bounds__backtrack_finish_decide_bounds
          sigma c); lia.
      * exact IH.
      * exact IH.
Qed.
Lemma snapshot_nonzero_assignment_true__backtrack_finish_decide_bounds :
  forall n live snap i,
  snapshot_lengths n live snap ->
  snapshot_cells_wf n live snap ->
  0 <= i < n ->
  Znth i (snap_values snap) 0 <> 0 ->
  Znth i (snap_values snap) (-1) <> -1 ->
  snapshot_assignment n snap i = Some true.
Proof.
  intros n live snap i Hlen Hcells Hi Hnz0 Hassigned.
  unfold snapshot_lengths in Hlen.
  destruct Hlen as (Hvalues & _).
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [Hvars _].
  specialize (Hvars i Hi).
  cbn in Hvars.
  destruct Hvars as [Hdomain _].
  assert (Hindep : Znth i (snap_values snap) 0 =
    Znth i (snap_values snap) (-1)).
  { apply Znth_indep. rewrite Hvalues; exact Hi. }
  rewrite Hindep in Hnz0.
  assert (Hvalue : Znth i (snap_values snap) (-1) = 1).
  { destruct Hdomain as [Hm | [Hz | Ho]]; [contradiction | contradiction | exact Ho]. }
  unfold snapshot_assignment.
  assert (Hguard : andb (Z.leb 0 i) (Z.ltb i n) = true).
  { apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Hguard, Hvalue; reflexivity.
Qed.
Lemma snapshot_nonzero_assignment_false__backtrack_finish_decide_bounds :
  forall n live snap i,
  snapshot_lengths n live snap ->
  snapshot_cells_wf n live snap ->
  0 <= i < n ->
  Znth i (snap_values snap) 0 <> 1 ->
  Znth i (snap_values snap) (-1) <> -1 ->
  snapshot_assignment n snap i = Some false.
Proof.
  intros n live snap i Hlen Hcells Hi Hno1 Hassigned.
  unfold snapshot_lengths in Hlen.
  destruct Hlen as (Hvalues & _).
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [Hvars _].
  specialize (Hvars i Hi).
  cbn in Hvars.
  destruct Hvars as [Hdomain _].
  assert (Hindep : Znth i (snap_values snap) 0 =
    Znth i (snap_values snap) (-1)).
  { apply Znth_indep. rewrite Hvalues; exact Hi. }
  rewrite Hindep in Hno1.
  assert (Hvalue : Znth i (snap_values snap) (-1) = 0).
  { destruct Hdomain as [Hm | [Hz | Ho]];
      [contradiction | exact Hz | contradiction]. }
  unfold snapshot_assignment.
  assert (Hguard : andb (Z.leb 0 i) (Z.ltb i n) = true).
  { apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Hguard, Hvalue; reflexivity.
Qed.
Lemma literal_var_count_zero_below__backtrack_finish_decide_bounds : forall x c,
  (forall l, In l c -> x < literal_var l) ->
  literal_var_count x c = 0.
Proof.
  intros x c; induction c as [|l c IH]; intros Hbelow.
  - reflexivity.
  - cbn [literal_var_count].
    assert (Hlx : literal_var l <> x).
    { specialize (Hbelow l ltac:(left; reflexivity)); lia. }
    rewrite (proj2 (Z.eqb_neq _ _) Hlx).
    apply IH. intros l' Hin. apply Hbelow. right; exact Hin.
Qed.
Lemma literal_var_count_positive_of_in__backtrack_finish_decide_bounds :
  forall x c,
  In (Pos x) c \/ In (Neg x) c -> 0 < literal_var_count x c.
Proof.
  intros x c; induction c as [|l c IH]; intros Hin.
  - destruct Hin as [Hin|Hin]; contradiction.
  - cbn [literal_var_count].
    destruct (Z.eqb (literal_var l) x) eqn:Hlx.
    + pose proof (literal_var_count_nonneg x c); lia.
    + apply IH.
      destruct Hin as [[Heq|Hin]|[Heq|Hin]].
      * subst l; cbn in Hlx; rewrite Z.eqb_refl in Hlx; discriminate.
      * left; exact Hin.
      * subst l; cbn in Hlx; rewrite Z.eqb_refl in Hlx; discriminate.
      * right; exact Hin.
Qed.
Lemma literal_var_count_zero_if_absent__backtrack_finish_decide_bounds :
  forall x c,
  ~ In (Pos x) c -> ~ In (Neg x) c -> literal_var_count x c = 0.
Proof.
  intros x c; induction c as [|l c IH]; intros Hpos Hneg.
  - reflexivity.
  - cbn [literal_var_count].
    destruct l as [y|y]; cbn [literal_var].
    + assert (Hy : y <> x).
      { intro; subst y; apply Hpos; left; reflexivity. }
      rewrite (proj2 (Z.eqb_neq _ _) Hy).
      apply IH; intro Hin; [apply Hpos|apply Hneg]; right; exact Hin.
    + assert (Hy : y <> x).
      { intro; subst y; apply Hneg; left; reflexivity. }
      rewrite (proj2 (Z.eqb_neq _ _) Hy).
      apply IH; intro Hin; [apply Hpos|apply Hneg]; right; exact Hin.
Qed.
Lemma dense_decode_from_literal_var_count_le_one__backtrack_finish_decide_bounds :
  forall row base x,
  base <= x < base + Zlength row ->
  literal_var_count x (dense_decode_from base row) <= 1.
Proof.
  induction row as [|z row IH]; intros base x Hrange.
  - rewrite Zlength_nil in Hrange; lia.
  - rewrite Zlength_cons in Hrange.
    cbn [dense_decode_from].
    destruct (Z.eqb z 1) eqn:Hz1.
    + cbn [literal_var_count literal_var].
      destruct (Z.eq_dec base x) as [->|Hneq].
      * rewrite Z.eqb_refl.
        rewrite literal_var_count_zero_below__backtrack_finish_decide_bounds.
        -- lia.
        -- intros l Hin.
           pose proof (dense_decode_from_var_lower_bound row (x + 1) l Hin).
           lia.
      * rewrite (proj2 (Z.eqb_neq _ _) Hneq).
        apply IH; lia.
    + destruct (Z.eqb z (-1)) eqn:Hzm.
      * cbn [literal_var_count literal_var].
        destruct (Z.eq_dec base x) as [->|Hneq].
        -- rewrite Z.eqb_refl.
           rewrite literal_var_count_zero_below__backtrack_finish_decide_bounds.
           ++ lia.
           ++ intros l Hin.
              pose proof (dense_decode_from_var_lower_bound row (x + 1) l Hin).
              lia.
        -- rewrite (proj2 (Z.eqb_neq _ _) Hneq).
           apply IH; lia.
      * destruct (Z.eq_dec base x) as [->|Hneq].
        -- rewrite literal_var_count_zero_below__backtrack_finish_decide_bounds.
           ++ lia.
           ++ intros l Hin.
              pose proof (dense_decode_from_var_lower_bound row (x + 1) l Hin).
              lia.
        -- apply IH; lia.
Qed.
Lemma literal_var_count_dense_nonzero__backtrack_finish_decide_bounds :
  forall n row x,
  row_wf n row -> var_in_range n x -> Znth x row 0 <> 0 ->
  literal_var_count x (dense_decode row) = 1.
Proof.
  intros n row x Hwf Hrange Hnonzero.
  pose proof (row_wf_cell_domain n row x Hwf Hrange) as Hdomain.
  assert (Hin : In (Pos x) (dense_decode row) \/ In (Neg x) (dense_decode row)).
  { destruct Hdomain as [Hneg|[Hzero|Hpos]].
    - right. apply (proj1 (dense_decode_neg n row x Hwf Hrange)); exact Hneg.
    - contradiction.
    - left. apply (proj1 (dense_decode_pos n row x Hwf Hrange)); exact Hpos. }
  pose proof
    (literal_var_count_positive_of_in__backtrack_finish_decide_bounds
      x (dense_decode row) Hin) as Hpositive.
  pose proof
    (dense_decode_from_literal_var_count_le_one__backtrack_finish_decide_bounds
      row 0 x) as Hupper.
  unfold dense_decode in *.
  specialize (Hupper ltac:(unfold var_in_range in Hrange;
    destruct Hwf as [Hlen _]; rewrite Hlen; lia)).
  lia.
Qed.
Lemma literal_var_count_dense_zero__backtrack_finish_decide_bounds :
  forall n row x,
  row_wf n row -> var_in_range n x -> Znth x row 0 = 0 ->
  literal_var_count x (dense_decode row) = 0.
Proof.
  intros n row x Hwf Hrange Hzero.
  pose proof (proj1 (dense_decode_zero n row x Hwf Hrange) Hzero)
    as [Hpos Hneg].
  apply literal_var_count_zero_if_absent__backtrack_finish_decide_bounds;
    assumption.
Qed.
Lemma literal_true_at_count_le_true_count__backtrack_finish_decide_bounds :
  forall sigma x b c,
  sigma x = Some b ->
  literal_true_at_count x b c <= clause_true_count sigma c.
Proof.
  intros sigma x b c; induction c as [|l c IH]; intros Hsigma.
  - reflexivity.
  - cbn -[eval_partial_literal Z.add Z.sub] in *.
    specialize (IH Hsigma).
    destruct l as [y|y]; destruct (Z.eq_dec x y) as [->|Hxy].
    + replace (eval_partial_literal sigma (Pos y)) with (Some b) by
        (unfold eval_partial_literal, literal_var; rewrite Hsigma; reflexivity).
      rewrite Z.eqb_refl. destruct b; cbn -[Z.add Z.sub]; lia.
    + assert (Hyx : Z.eqb y x = false) by (apply Z.eqb_neq; lia).
      destruct (eval_partial_literal sigma (Pos y)) as [[|]|];
        cbn -[Z.add Z.sub]; rewrite Hyx; lia.
    + replace (eval_partial_literal sigma (Neg y)) with (Some (negb b)) by
        (unfold eval_partial_literal, literal_var; rewrite Hsigma; reflexivity).
      rewrite Z.eqb_refl. destruct b; cbn -[Z.add Z.sub]; lia.
    + assert (Hyx : Z.eqb y x = false) by (apply Z.eqb_neq; lia).
      destruct (eval_partial_literal sigma (Neg y)) as [[|]|];
        cbn -[Z.add Z.sub]; rewrite Hyx; lia.
Qed.
Lemma expected_clause_state_negative__backtrack_finish_decide_bounds :
  forall sigma c state,
  expected_clause_state sigma c = state -> state < 0 ->
  clause_true_count sigma c = 0 /\
  clause_unassigned_count sigma c = - state /\
  2 <= clause_unassigned_count sigma c.
Proof.
  intros sigma c state Hstate Hnegative.
  unfold expected_clause_state in Hstate.
  destruct (Z.ltb 0 (clause_true_count sigma c)) eqn:Htrue.
  - lia.
  - apply Z.ltb_ge in Htrue.
    pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment
      sigma c) as Htrue_nonneg.
    assert (Htzero : clause_true_count sigma c = 0) by lia.
    destruct (Z.eqb (clause_unassigned_count sigma c) 0) eqn:Hun0.
    + lia.
    + apply Z.eqb_neq in Hun0.
      destruct (Z.eqb (clause_unassigned_count sigma c) 1) eqn:Hun1.
      * lia.
      * apply Z.eqb_neq in Hun1.
        pose proof
          (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment
            sigma c) as Hun_nonneg.
        repeat split; lia.
Qed.
Lemma clause_summary_clear_negative_dense_nonzero__backtrack_finish_decide_bounds :
  forall n row x old_sigma new_sigma state true_count unassigned_count b,
  row_wf n row -> var_in_range n x -> Znth x row 0 <> 0 ->
  old_sigma x = Some b ->
  new_sigma = clear_partial old_sigma x ->
  clause_summary_ok old_sigma (dense_decode row)
    state true_count unassigned_count ->
  state < 0 ->
  clause_summary_ok new_sigma (dense_decode row)
    (state - 1) true_count (unassigned_count + 1).
Proof.
  intros n row x old_sigma new_sigma state true_count unassigned_count b
    Hrow Hrange Hcell Hassign Hnew Hsummary Hnegative.
  subst new_sigma.
  destruct Hsummary as [Htrue [Hunassigned Hstate]].
  pose proof (expected_clause_state_negative__backtrack_finish_decide_bounds
    old_sigma (dense_decode row) state (eq_sym Hstate) Hnegative)
    as [Hold_true [Hold_unassigned Hold_unassigned_lower]].
  pose proof (literal_var_count_dense_nonzero__backtrack_finish_decide_bounds
    n row x Hrow Hrange Hcell) as Hvar_count.
  pose proof
    (literal_true_at_count_le_true_count__backtrack_finish_decide_bounds
      old_sigma x b (dense_decode row) Hassign) as Htrue_at_upper.
  pose proof (literal_true_at_count_nonneg x b (dense_decode row))
    as Htrue_at_lower.
  assert (Htrue_at_zero : literal_true_at_count x b (dense_decode row) = 0)
    by lia.
  pose proof (clause_counts_clear old_sigma x b (dense_decode row) Hassign)
    as [Hnew_unassigned Hnew_true].
  unfold clause_summary_ok.
  split.
  - rewrite Hnew_true. lia.
  - split.
    + rewrite Hnew_unassigned. lia.
    + unfold expected_clause_state.
      rewrite Hnew_true, Hnew_unassigned, Hold_true, Htrue_at_zero,
        Hvar_count, Hold_unassigned.
      assert (Hun0 : Z.eqb (- state + 1) 0 = false).
      { apply Z.eqb_neq; lia. }
      assert (Hun1 : Z.eqb (- state + 1) 1 = false).
      { apply Z.eqb_neq; lia. }
      cbn -[Z.add Z.sub Z.opp].
      rewrite Hun0, Hun1.
      replace (0 - 0) with 0 by lia.
      cbn.
      lia.
Qed.
Lemma clause_summary_clear_dense_zero__backtrack_finish_decide_bounds :
  forall n row x old_sigma new_sigma state true_count unassigned_count b,
  row_wf n row -> var_in_range n x -> Znth x row 0 = 0 ->
  old_sigma x = Some b ->
  new_sigma = clear_partial old_sigma x ->
  clause_summary_ok old_sigma (dense_decode row)
    state true_count unassigned_count ->
  clause_summary_ok new_sigma (dense_decode row)
    state true_count unassigned_count.
Proof.
  intros n row x old_sigma new_sigma state true_count unassigned_count b
    Hrow Hrange Hcell Hassign Hnew Hsummary.
  subst new_sigma.
  destruct Hsummary as [Htrue [Hunassigned Hstate]].
  pose proof (literal_var_count_dense_zero__backtrack_finish_decide_bounds
    n row x Hrow Hrange Hcell) as Hvar_count.
  pose proof (literal_true_count_le_var_count__bcp_unit_to_assignment
    x b (dense_decode row)) as Htrue_at_upper.
  pose proof (literal_true_at_count_nonneg x b (dense_decode row))
    as Htrue_at_lower.
  assert (Htrue_at_zero : literal_true_at_count x b (dense_decode row) = 0)
    by lia.
  pose proof (clause_counts_clear old_sigma x b (dense_decode row) Hassign)
    as [Hnew_unassigned Hnew_true].
  unfold clause_summary_ok.
  split.
  - rewrite Hnew_true. lia.
  - split.
    + rewrite Hnew_unassigned. lia.
    + unfold expected_clause_state.
      rewrite Hnew_true, Hnew_unassigned, Hvar_count, Htrue_at_zero.
      replace (clause_true_count old_sigma (dense_decode row) - 0)
        with (clause_true_count old_sigma (dense_decode row)) by lia.
      replace (clause_unassigned_count old_sigma (dense_decode row) + 0)
        with (clause_unassigned_count old_sigma (dense_decode row)) by lia.
      exact Hstate.
Qed.
Lemma mixed_clause_summaries_advance_replace__backtrack_finish_decide_bounds :
  forall old_sigma new_sigma rows states true_counts unassigned live cap j
    state_j true_j unassigned_j,
  mixed_clause_summaries old_sigma new_sigma rows states true_counts unassigned
    live cap j None ->
  0 <= j < live ->
  summary_at new_sigma rows
    (replace_Znth j state_j states)
    (replace_Znth j true_j true_counts)
    (replace_Znth j unassigned_j unassigned) j ->
  mixed_clause_summaries old_sigma new_sigma rows
    (replace_Znth j state_j states)
    (replace_Znth j true_j true_counts)
    (replace_Znth j unassigned_j unassigned) live cap (j + 1) None.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned live cap j
    state_j true_j unassigned_j Hmixed Hj Hnewj.
  unfold mixed_clause_summaries in Hmixed |- *.
  destruct Hmixed as
    [Hlive [Hstates [Htrue [Hunassigned [Hcap [Hprocessed Hsummary]]]]]].
  split; [exact Hlive|].
  split; [rewrite Zlength_replace_Znth; lia|].
  split; [rewrite Zlength_replace_Znth; lia|].
  split; [rewrite Zlength_replace_Znth; lia|].
  split; [exact Hcap|].
  split; [lia|].
  intros k Hkrange.
  specialize (Hsummary k Hkrange).
  destruct Hsummary as [Hnew Hold].
  split.
  - intros [Hkprocessed|Hexempt].
    + destruct (Z.eq_dec k j) as [->|Hneq].
      * exact Hnewj.
      * assert (Hkj : k < j) by lia.
        specialize (Hnew (or_introl Hkj)).
        unfold summary_at, clause_summary_ok in Hnew |- *.
        rewrite !Znth_replace_Znth_Diff by lia.
        exact Hnew.
    + discriminate.
  - intros [Hkafter Hnone].
    assert (Hkj : j < k) by lia.
    specialize (Hold ltac:(split; [lia|discriminate])).
    unfold summary_at, clause_summary_ok in Hold |- *.
    rewrite !Znth_replace_Znth_Diff by lia.
    exact Hold.
Qed.
Lemma mixed_clause_summaries_advance_same__backtrack_finish_decide_bounds :
  forall old_sigma new_sigma rows states true_counts unassigned live cap j,
  mixed_clause_summaries old_sigma new_sigma rows states true_counts unassigned
    live cap j None ->
  0 <= j < live ->
  summary_at new_sigma rows states true_counts unassigned j ->
  mixed_clause_summaries old_sigma new_sigma rows states true_counts unassigned
    live cap (j + 1) None.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned live cap j
    Hmixed Hj Hnewj.
  unfold mixed_clause_summaries in Hmixed |- *.
  destruct Hmixed as
    [Hlive [Hstates [Htrue [Hunassigned [Hcap [Hprocessed Hsummary]]]]]].
  split; [exact Hlive|].
  split; [exact Hstates|].
  split; [exact Htrue|].
  split; [exact Hunassigned|].
  split; [exact Hcap|].
  split; [lia|].
  intros k Hkrange.
  specialize (Hsummary k Hkrange).
  destruct Hsummary as [Hnew Hold].
  split.
  - intros [Hkprocessed|Hexempt].
    + destruct (Z.eq_dec k j) as [->|Hneq].
      * exact Hnewj.
      * apply Hnew; left; lia.
    + discriminate.
  - intros [Hkafter Hnone].
    apply Hold; split; [lia|discriminate].
Qed.
Lemma dense_summaries_from_complete__backtrack_finish_decide_bounds :
  forall n live target cap old_snap new_snap,
  snapshot_lengths n live new_snap ->
  snap_rows new_snap = snap_rows old_snap ->
  mixed_clause_summaries
    (snapshot_assignment n new_snap) (snapshot_assignment n new_snap)
    (List.map dense_decode (snap_rows old_snap))
    (snap_states new_snap) (snap_true_counts new_snap)
    (snap_unassigned new_snap) live cap live None ->
  dense_summaries_restored n live target old_snap new_snap.
Proof.
  intros n live target cap old_snap new_snap Hlengths Hrows Hmixed.
  unfold dense_summaries_restored.
  split; [exact Hlengths|].
  split.
  - unfold snapshot_summaries_exact.
    intros j Hj.
    unfold mixed_clause_summaries in Hmixed.
    destruct Hmixed as (_ & _ & _ & _ & _ & _ & Hall).
    specialize (Hall j Hj).
    destruct Hall as [Hsummary _].
    specialize (Hsummary (or_introl (proj2 Hj))).
    rewrite Hrows.
    exact Hsummary.
  - split; [reflexivity|exact Hrows].
Qed.
Lemma coherent_snapshot_from_complete__backtrack_finish_decide_bounds :
  forall F n live original_count cap old_snap new_snap,
  coherent_snapshot F n live original_count old_snap ->
  snapshot_lengths n live new_snap ->
  snapshot_cells_wf n live new_snap ->
  snap_rows new_snap = snap_rows old_snap ->
  mixed_clause_summaries
    (snapshot_assignment n new_snap) (snapshot_assignment n new_snap)
    (List.map dense_decode (snap_rows old_snap))
    (snap_states new_snap) (snap_true_counts new_snap)
    (snap_unassigned new_snap) live cap live None ->
  coherent_snapshot F n live original_count new_snap.
Proof.
  intros F n live original_count cap old_snap new_snap Hcoherent
    Hlengths Hcells Hrows Hmixed.
  unfold coherent_snapshot in Hcoherent |- *.
  destruct Hcoherent as
    [Hn [Horiginal [Hold_lengths [Hold_cells [Hold_summaries Hsound]]]]].
  split; [exact Hn|].
  split; [exact Horiginal|].
  split; [exact Hlengths|].
  split; [exact Hcells|].
  split.
  - unfold snapshot_summaries_exact.
    intros j Hj.
    unfold mixed_clause_summaries in Hmixed.
    destruct Hmixed as (_ & _ & _ & _ & _ & _ & Hall).
    specialize (Hall j Hj).
    destruct Hall as [Hsummary _].
    specialize (Hsummary (or_introl (proj2 Hj))).
    rewrite Hrows.
    exact Hsummary.
  - rewrite Hrows; exact Hsound.
Qed.
Lemma prefix_snapshot_restrict__backtrack_finish_decide_bounds :
  forall n target old_snap old_ranks old_dl new_snap new_ranks final_ranks,
  (forall x,
    final_ranks x =
      match snapshot_level n old_snap x with
      | Some d => if Z.leb d target then old_ranks x else None
      | None => None
      end) ->
  prefix_restriction
    (cdcl_view_of_snapshot n old_snap old_ranks old_dl)
    (cdcl_view_of_snapshot n new_snap new_ranks target)
    n target n ->
  restrict_above_level
    (cdcl_view_of_snapshot n old_snap old_ranks old_dl)
    (cdcl_view_of_snapshot n new_snap final_ranks target)
    target.
Proof.
  intros n target old_snap old_ranks old_dl new_snap new_ranks final_ranks
    Hfinal_ranks Hprefix.
  unfold prefix_restriction in Hprefix.
  destruct Hprefix as [Hprocessed [Hclauses Hcells]].
  unfold restrict_above_level.
  split; [reflexivity|].
  split; [exact Hclauses|].
  intros x.
  destruct (andb (Z.leb 0 x) (Z.ltb x n)) eqn:Hguard.
  - apply andb_true_iff in Hguard.
    destruct Hguard as [Hx0 Hxn].
    apply Z.leb_le in Hx0; apply Z.ltb_lt in Hxn.
    specialize (Hcells x ltac:(unfold var_in_range; lia)).
    destruct Hcells as [Hbefore _].
    specialize (Hbefore ltac:(lia)).
    change
      (match snapshot_level n old_snap x with
       | Some d =>
           if Z.ltb target d then
             snapshot_assignment n new_snap x = None /\
             snapshot_level n new_snap x = None /\
             snapshot_reason n new_snap x = None /\
             new_ranks x = None
           else
             snapshot_assignment n new_snap x =
               snapshot_assignment n old_snap x /\
             snapshot_level n new_snap x = snapshot_level n old_snap x /\
             snapshot_reason n new_snap x = snapshot_reason n old_snap x /\
             new_ranks x = old_ranks x
       | None =>
           snapshot_assignment n new_snap x =
             snapshot_assignment n old_snap x /\
           snapshot_level n new_snap x = snapshot_level n old_snap x /\
           snapshot_reason n new_snap x = snapshot_reason n old_snap x /\
           new_ranks x = old_ranks x
       end) in Hbefore.
    change
      (match snapshot_level n old_snap x with
       | Some d =>
           if Z.leb d target then
             snapshot_assignment n new_snap x =
               snapshot_assignment n old_snap x /\
             snapshot_level n new_snap x = snapshot_level n old_snap x /\
             snapshot_reason n new_snap x = snapshot_reason n old_snap x /\
             final_ranks x = old_ranks x
           else
             snapshot_assignment n new_snap x = None /\
             snapshot_level n new_snap x = None /\
             snapshot_reason n new_snap x = None /\
             final_ranks x = None
       | None =>
           snapshot_assignment n new_snap x = None /\
           snapshot_level n new_snap x = None /\
           snapshot_reason n new_snap x = None /\
           final_ranks x = None
       end).
    destruct (snapshot_level n old_snap x) as [d|] eqn:Hlevel.
    + destruct (Z.ltb target d) eqn:Htd.
      * apply Z.ltb_lt in Htd.
        assert (Hleb : Z.leb d target = false) by
          (apply Z.leb_gt; lia).
        rewrite Hleb.
        rewrite Hfinal_ranks, Hlevel, Hleb.
        destruct Hbefore as [Ha [Hl [Hr _]]].
        repeat split; try assumption; reflexivity.
      * apply Z.ltb_ge in Htd.
        assert (Hleb : Z.leb d target = true) by
          (apply Z.leb_le; lia).
        rewrite Hleb.
        rewrite Hfinal_ranks, Hlevel, Hleb.
        destruct Hbefore as [Ha [Hl [Hr _]]].
        repeat split; try assumption; reflexivity.
    + rewrite Hfinal_ranks, Hlevel.
      destruct Hbefore as [Ha [Hl [Hr _]]].
      assert (Hold_assignment : snapshot_assignment n old_snap x = None).
      { unfold snapshot_level in Hlevel.
        destruct (snapshot_assignment n old_snap x); [discriminate|reflexivity]. }
      assert (Hold_reason : snapshot_reason n old_snap x = None).
      { unfold snapshot_reason. rewrite Hold_assignment. reflexivity. }
      rewrite Ha, Hold_assignment, Hl, Hr, Hold_reason.
      repeat split; reflexivity.
  - assert (Hold_assignment : snapshot_assignment n old_snap x = None).
    { unfold snapshot_assignment. rewrite Hguard. reflexivity. }
    assert (Hnew_assignment : snapshot_assignment n new_snap x = None).
    { unfold snapshot_assignment. rewrite Hguard. reflexivity. }
    assert (Hold_level : snapshot_level n old_snap x = None).
    { unfold snapshot_level. rewrite Hold_assignment. reflexivity. }
    assert (Hnew_level : snapshot_level n new_snap x = None).
    { unfold snapshot_level. rewrite Hnew_assignment. reflexivity. }
    assert (Hnew_reason : snapshot_reason n new_snap x = None).
    { unfold snapshot_reason. rewrite Hnew_assignment. reflexivity. }
    change
      (match snapshot_level n old_snap x with
       | Some d =>
           if Z.leb d target then
             snapshot_assignment n new_snap x =
               snapshot_assignment n old_snap x /\
             snapshot_level n new_snap x = snapshot_level n old_snap x /\
             snapshot_reason n new_snap x = snapshot_reason n old_snap x /\
             final_ranks x = old_ranks x
           else
             snapshot_assignment n new_snap x = None /\
             snapshot_level n new_snap x = None /\
             snapshot_reason n new_snap x = None /\
             final_ranks x = None
       | None =>
           snapshot_assignment n new_snap x = None /\
           snapshot_level n new_snap x = None /\
           snapshot_reason n new_snap x = None /\
           final_ranks x = None
       end).
    rewrite Hold_level.
    rewrite Hfinal_ranks, Hold_level.
    repeat split; try assumption; reflexivity.
Qed.
Lemma restrict_assignment_eq__backtrack_finish_decide_bounds : forall old new target,
  restrict_above_level old new target ->
  assignment new = restrict_to_level old target.
Proof.
  intros old new target Hrestrict.
  destruct Hrestrict as [_ [_ Hcells]].
  apply functional_extensionality; intro x.
  specialize (Hcells x).
  unfold restrict_to_level.
  destruct (level_of old x) as [d|] eqn:Hlevel.
  - destruct (Z.leb d target) eqn:Hleb.
    + destruct Hcells as [Hassignment _].
      rewrite Hassignment.
      destruct (assignment old x); reflexivity.
    + destruct Hcells as [Hassignment _].
      rewrite Hassignment.
      destruct (assignment old x); reflexivity.
  - destruct Hcells as [Hassignment _].
    rewrite Hassignment.
    destruct (assignment old x); reflexivity.
Qed.
Lemma eval_partial_literal_restrict_false__backtrack_finish_decide_bounds : forall a target l,
  eval_partial_literal (restrict_to_level a target) l = Some false ->
  eval_partial_literal (assignment a) l = Some false.
Proof.
  intros a target l Hfalse.
  destruct l as [x|x];
    unfold eval_partial_literal, restrict_to_level, literal_var in *;
    destruct (assignment a x) as [b|] eqn:Hassignment;
    destruct (level_of a x) as [d|] eqn:Hlevel;
    try discriminate;
    destruct (Z.leb d target) eqn:Hleb;
    try discriminate;
    destruct b; inversion Hfalse; reflexivity.
Qed.
Lemma clause_false_restrict__backtrack_finish_decide_bounds : forall old new target c,
  restrict_above_level old new target ->
  clause_false (assignment new) c ->
  clause_false (assignment old) c.
Proof.
  intros old new target c Hrestrict Hfalse l Hin.
  pose proof (restrict_assignment_eq__backtrack_finish_decide_bounds _ _ _ Hrestrict) as Hassignment.
  specialize (Hfalse l Hin).
  rewrite Hassignment in Hfalse.
  eapply eval_partial_literal_restrict_false__backtrack_finish_decide_bounds; exact Hfalse.
Qed.
Lemma clause_false_unassigned_zero__backtrack_finish_decide_bounds : forall sigma c,
  clause_false sigma c -> clause_unassigned_count sigma c = 0.
Proof.
  intros sigma c; induction c as [|l c IH]; intros Hfalse.
  - reflexivity.
  - cbn [clause_unassigned_count].
    assert (Hlfalse : eval_partial_literal sigma l = Some false).
    { apply Hfalse; left; reflexivity. }
    rewrite Hlfalse.
    apply IH. intros l' Hin. apply Hfalse. right; exact Hin.
Qed.
Lemma backjump_no_conflict__backtrack_finish_decide_bounds :
  forall (F : cnf) (start conflict old new : cdcl_view)
    (target last : Z) (learned : clause),
  assignment old = assignment conflict ->
  level_of old = level_of conflict ->
  installed_clauses old = installed_clauses conflict ++ (learned :: nil) ->
  dense_conflict_batch start conflict last ->
  learned_backjump_cert F conflict target learned ->
  restrict_above_level old new target ->
  (forall c, In c (installed_clauses old) ->
    clause_false (assignment old) c ->
    ~ clause_false (assignment new) c) /\
  no_conflict new.
Proof.
  intros F start conflict old new target last learned
    Hassignment Hlevel Hclauses Hbatch Hcert Hrestrict.
  destruct Hbatch as
    [b [Hstart [Hlast_assignment [Hlast_level [Hbatch_clauses Hcause]]]]].
  destruct Hcert as
    [Hlearned_sound [Hlearned_nonempty [Htarget [Hasserting Hfrontier]]]].
  assert (Hnew_assignment :
    assignment new = restrict_to_level conflict target).
  { pose proof (restrict_assignment_eq__backtrack_finish_decide_bounds _ _ _ Hrestrict) as Hnew.
    rewrite Hnew.
    unfold restrict_to_level.
    rewrite Hassignment, Hlevel.
    reflexivity. }
  assert (Hnot_after : forall c,
    In c (installed_clauses old) ->
    clause_false (assignment old) c ->
    ~ clause_false (assignment new) c).
  { intros c Hin Hfalse_old Hfalse_new.
    rewrite Hclauses in Hin.
    apply in_app_iff in Hin.
    destruct Hin as [Hin_conflict | Hin_learned].
    - assert (Hfalse_conflict : clause_false (assignment conflict) c).
      { rewrite <- Hassignment; exact Hfalse_old. }
      specialize (Hcause c Hin_conflict Hfalse_conflict).
      destruct Hrestrict as [_ [_ Hrestrict_cells]].
      specialize (Hrestrict_cells last).
      rewrite Hlevel, Hlast_level in Hrestrict_cells.
      assert (Hleb : Z.leb (current_level conflict) target = false).
      { apply Z.leb_gt; lia. }
      rewrite Hleb in Hrestrict_cells.
      destruct Hrestrict_cells as [Hnew_last _].
      specialize (Hfalse_new (falsified_literal last b) Hcause).
      assert (Hliteral_none :
        assignment new (literal_var (falsified_literal last b)) = None).
      { replace (literal_var (falsified_literal last b)) with last by
          (destruct b; reflexivity).
        exact Hnew_last. }
      pose proof
        (eval_partial_literal_unassigned__bcp_unit_to_assignment
          (assignment new) (falsified_literal last b) Hliteral_none) as Hnone.
      rewrite Hnone in Hfalse_new; discriminate.
    - cbn in Hin_learned.
      destruct Hin_learned as [Hceq | Hfalse]; [subst c|contradiction].
      destruct Hasserting as [_ Hunassigned].
      pose proof
        (clause_false_unassigned_zero__backtrack_finish_decide_bounds
          (assignment new) learned Hfalse_new) as Hzero.
      rewrite Hnew_assignment in Hzero.
      lia. }
  split; [exact Hnot_after|].
  intros c Hin Hfalse_new.
  pose proof (clause_false_restrict__backtrack_finish_decide_bounds _ _ _ _ Hrestrict Hfalse_new)
    as Hfalse_old.
  pose proof Hrestrict as Hrestrict_copy.
  destruct Hrestrict_copy as [_ [Hnew_clauses _]].
  rewrite Hnew_clauses in Hin.
  exact (Hnot_after c Hin Hfalse_old Hfalse_new).
Qed.
Lemma restrict_keeps_cell__backtrack_finish_decide_bounds : forall old new target x d,
  restrict_above_level old new target ->
  level_of old x = Some d -> d <= target ->
  assignment new x = assignment old x /\
  level_of new x = level_of old x /\
  reason_of new x = reason_of old x /\
  assignment_rank new x = assignment_rank old x.
Proof.
  intros old new target x d Hrestrict Hlevel Hd.
  destruct Hrestrict as [_ [_ Hcells]].
  specialize (Hcells x).
  rewrite Hlevel in Hcells.
  assert (Hleb : Z.leb d target = true) by (apply Z.leb_le; exact Hd).
  rewrite Hleb in Hcells.
  rewrite Hlevel.
  exact Hcells.
Qed.
Lemma restrict_new_assigned_old__backtrack_finish_decide_bounds : forall old new target x b,
  restrict_above_level old new target ->
  assignment new x = Some b ->
  exists d,
    level_of old x = Some d /\ d <= target /\
    assignment old x = Some b /\
    level_of new x = level_of old x /\
    reason_of new x = reason_of old x /\
    assignment_rank new x = assignment_rank old x.
Proof.
  intros old new target x b Hrestrict Hnew.
  pose proof Hrestrict as Hcopy.
  destruct Hcopy as [_ [_ Hcells]].
  specialize (Hcells x).
  destruct (level_of old x) as [d|] eqn:Hlevel.
  - destruct (Z.leb d target) eqn:Hleb.
    + apply Z.leb_le in Hleb.
      destruct Hcells as [Hassignment [Hnew_level [Hreason Hrank]]].
      exists d; repeat split; try assumption.
      rewrite <- Hassignment; exact Hnew.
    + destruct Hcells as [Hassignment _].
      rewrite Hassignment in Hnew; discriminate.
  - destruct Hcells as [Hassignment _].
    rewrite Hassignment in Hnew; discriminate.
Qed.
Lemma eval_partial_literal_assignment_at__backtrack_finish_decide_bounds : forall sigma1 sigma2 l,
  sigma1 (literal_var l) = sigma2 (literal_var l) ->
  eval_partial_literal sigma1 l = eval_partial_literal sigma2 l.
Proof.
  intros sigma1 sigma2 [x|x] Heq;
    unfold eval_partial_literal, literal_var in *;
    rewrite Heq;
    reflexivity.
Qed.
Lemma nth_error_append_singleton__backtrack_finish_decide_bounds :
  forall (xs : list clause) learned k c,
  nth_error xs k = Some c ->
  nth_error (xs ++ (learned :: nil)) k = Some c.
Proof.
  intros xs learned k c Hnth.
  rewrite nth_error_app1; [exact Hnth|].
  apply nth_error_Some.
  rewrite Hnth; discriminate.
Qed.
Lemma restrict_to_level_chain__backtrack_finish_decide_bounds : forall old new target k,
  restrict_above_level old new target ->
  k <= target ->
  restrict_to_level new k = restrict_to_level old k.
Proof.
  intros old new target k Hrestrict Hktarget.
  pose proof Hrestrict as Hcopy.
  destruct Hcopy as [_ [_ Hcells]].
  apply functional_extensionality; intro x.
  specialize (Hcells x).
  unfold restrict_to_level.
  destruct (level_of old x) as [d|] eqn:Hold_level.
  - destruct (Z.leb d target) eqn:Hdtarget.
    + destruct Hcells as [Hassignment [Hlevel _]].
      rewrite Hassignment, Hlevel.
      reflexivity.
    + apply Z.leb_gt in Hdtarget.
      destruct Hcells as [Hassignment [Hlevel _]].
      rewrite Hassignment.
      destruct (assignment old x) as [b|]; [|reflexivity].
      assert (Hdk : Z.leb d k = false) by (apply Z.leb_gt; lia).
      rewrite Hdk; reflexivity.
  - destruct Hcells as [Hassignment [Hlevel _]].
    rewrite Hassignment.
    destruct (assignment old x); reflexivity.
Qed.
Lemma reason_dependency_transfer__backtrack_finish_decide_bounds :
  forall conflict old new target learned x y dx dy,
  assignment old = assignment conflict ->
  level_of old = level_of conflict ->
  reason_of old = reason_of conflict ->
  assignment_rank old = assignment_rank conflict ->
  installed_clauses old = installed_clauses conflict ++ (learned :: nil) ->
  restrict_above_level old new target ->
  level_of conflict x = Some dx -> dx <= target ->
  level_of conflict y = Some dy -> dy <= target ->
  reason_dependency conflict x y ->
  reason_dependency new x y.
Proof.
  intros conflict old new target learned x y dx dy
    Hassignment Hlevel Hreason Hrank Hclauses Hrestrict
    Hxlevel Hxbound Hylevel Hybound Hdependency.
  destruct Hdependency as
    [i [c [ly [Hxreason [Hnth [Hin [Hlyvar [Hneq Hfalse]]]]]]]].
  assert (Hold_x_level : level_of old x = Some dx).
  { rewrite Hlevel; exact Hxlevel. }
  assert (Hold_y_level : level_of old y = Some dy).
  { rewrite Hlevel; exact Hylevel. }
  pose proof
    (restrict_keeps_cell__backtrack_finish_decide_bounds _ _ _ _ _ Hrestrict Hold_x_level Hxbound)
    as Hkeep_x.
  pose proof
    (restrict_keeps_cell__backtrack_finish_decide_bounds _ _ _ _ _ Hrestrict Hold_y_level Hybound)
    as Hkeep_y.
  destruct Hkeep_x as [_ [_ [Hnew_reason _]]].
  destruct Hkeep_y as [Hnew_assignment _].
  exists i, c, ly.
  split.
  - rewrite Hnew_reason, Hreason; exact Hxreason.
  - split.
    + pose proof Hrestrict as Hrestrict_copy.
      destruct Hrestrict_copy as [_ [Hnew_clauses _]].
      rewrite Hnew_clauses, Hclauses.
      eapply nth_error_append_singleton__backtrack_finish_decide_bounds; exact Hnth.
    + split; [exact Hin|].
      split; [exact Hlyvar|].
      split; [exact Hneq|].
      assert (Hassignment_at :
        assignment new (literal_var ly) =
        assignment conflict (literal_var ly)).
      { rewrite Hlyvar, Hnew_assignment, Hassignment; reflexivity. }
      rewrite (eval_partial_literal_assignment_at__backtrack_finish_decide_bounds
        (assignment new) (assignment conflict) ly Hassignment_at).
      exact Hfalse.
Qed.
Lemma reason_valid_transfer__backtrack_finish_decide_bounds :
  forall conflict old new target learned x i d,
  assignment old = assignment conflict ->
  level_of old = level_of conflict ->
  reason_of old = reason_of conflict ->
  assignment_rank old = assignment_rank conflict ->
  installed_clauses old = installed_clauses conflict ++ (learned :: nil) ->
  restrict_above_level old new target ->
  level_of conflict x = Some d -> d <= target ->
  reason_valid conflict x i ->
  reason_valid new x i.
Proof.
  intros conflict old new target learned x i d
    Hassignment Hlevel Hreason Hrank Hclauses Hrestrict
    Hxlevel Hxbound Hvalid.
  destruct Hvalid as
    [b [dx [rx [c [Hxassignment [Hxdlevel [Hxrank
      [Hnth [Hin Hothers]]]]]]]]].
  assert (Hdx : dx = d).
  { rewrite Hxlevel in Hxdlevel; inversion Hxdlevel; reflexivity. }
  subst dx.
  assert (Hold_x_level : level_of old x = Some d).
  { rewrite Hlevel; exact Hxlevel. }
  pose proof
    (restrict_keeps_cell__backtrack_finish_decide_bounds _ _ _ _ _ Hrestrict Hold_x_level Hxbound)
    as Hkeep_x.
  destruct Hkeep_x as
    [Hnew_assignment [Hnew_level [Hnew_reason Hnew_rank]]].
  exists b, d, rx, c.
  split.
  - rewrite Hnew_assignment, Hassignment; exact Hxassignment.
  - split.
    + rewrite Hnew_level, Hlevel; exact Hxlevel.
    + split.
      * rewrite Hnew_rank, Hrank; exact Hxrank.
      * split.
        -- pose proof Hrestrict as Hrestrict_copy.
           destruct Hrestrict_copy as [_ [Hnew_clauses _]].
           rewrite Hnew_clauses, Hclauses.
           eapply nth_error_append_singleton__backtrack_finish_decide_bounds; exact Hnth.
        -- split; [exact Hin|].
           intros l Hlin Hvarneq.
           specialize (Hothers l Hlin Hvarneq).
           destruct Hothers as
             [Hfalse [dy [ry [Hylevel [Hyrank [Hyd Hry]]]]]].
           assert (Hold_y_level : level_of old (literal_var l) = Some dy).
           { rewrite Hlevel; exact Hylevel. }
           pose proof
             (restrict_keeps_cell__backtrack_finish_decide_bounds _ _ _ _ _ Hrestrict
               Hold_y_level ltac:(lia)) as Hkeep_y.
           destruct Hkeep_y as
             [Hnew_y_assignment [Hnew_y_level [_ Hnew_y_rank]]].
           split.
           ++ assert (Hassignment_at :
                assignment new (literal_var l) =
                assignment conflict (literal_var l)).
              { rewrite Hnew_y_assignment, Hassignment; reflexivity. }
              rewrite (eval_partial_literal_assignment_at__backtrack_finish_decide_bounds
                (assignment new) (assignment conflict) l Hassignment_at).
              exact Hfalse.
           ++ exists dy, ry.
              repeat split; try assumption.
              ** rewrite Hnew_y_level, Hlevel; exact Hylevel.
              ** rewrite Hnew_y_rank, Hrank; exact Hyrank.
Qed.
Lemma same_level_predecessor_transfer__backtrack_finish_decide_bounds :
  forall conflict old new target learned x y d,
  assignment old = assignment conflict ->
  level_of old = level_of conflict ->
  reason_of old = reason_of conflict ->
  assignment_rank old = assignment_rank conflict ->
  installed_clauses old = installed_clauses conflict ++ (learned :: nil) ->
  restrict_above_level old new target ->
  d <= target ->
  same_level_predecessor conflict x y d ->
  same_level_predecessor new x y d.
Proof.
  intros conflict old new target learned x y d
    Hassignment Hlevel Hreason Hrank Hclauses Hrestrict Hbound Hsame.
  destruct Hsame as
    [Hdependency [Hxlevel [Hylevel [rx [ry [Hxrank [Hyrank Hlt]]]]]]].
  assert (Hnew_dependency : reason_dependency new x y).
  { eapply reason_dependency_transfer__backtrack_finish_decide_bounds with
      (conflict := conflict) (old := old) (target := target)
      (learned := learned) (dx := d) (dy := d); eauto. }
  assert (Hold_x_level : level_of old x = Some d).
  { rewrite Hlevel; exact Hxlevel. }
  assert (Hold_y_level : level_of old y = Some d).
  { rewrite Hlevel; exact Hylevel. }
  pose proof
    (restrict_keeps_cell__backtrack_finish_decide_bounds _ _ _ _ _ Hrestrict Hold_x_level Hbound)
    as Hkeep_x.
  pose proof
    (restrict_keeps_cell__backtrack_finish_decide_bounds _ _ _ _ _ Hrestrict Hold_y_level Hbound)
    as Hkeep_y.
  destruct Hkeep_x as [_ [Hnew_x_level [_ Hnew_x_rank]]].
  destruct Hkeep_y as [_ [Hnew_y_level [_ Hnew_y_rank]]].
  split; [exact Hnew_dependency|].
  split.
  - rewrite Hnew_x_level, Hlevel; exact Hxlevel.
  - split.
    + rewrite Hnew_y_level, Hlevel; exact Hylevel.
    + exists rx, ry.
      repeat split; try assumption.
      * rewrite Hnew_x_rank, Hrank; exact Hxrank.
      * rewrite Hnew_y_rank, Hrank; exact Hyrank.
Qed.
Lemma stable_after_backjump__backtrack_finish_decide_bounds :
  forall (F : cnf) (conflict old new : cdcl_view)
    (target : Z) (learned : clause),
  assignment old = assignment conflict ->
  level_of old = level_of conflict ->
  reason_of old = reason_of conflict ->
  assignment_rank old = assignment_rank conflict ->
  installed_clauses old = installed_clauses conflict ++ (learned :: nil) ->
  grounded_at conflict /\ closed_levels conflict /\ frontier_closed conflict ->
  learned_backjump_cert F conflict target learned ->
  restrict_above_level old new target ->
  grounded_at new /\ closed_levels new /\ frontier_closed new.
Proof.
  intros F conflict old new target learned
    Hassignment Hlevel Hreason Hrank Hclauses
    [Hgrounded [Hclosed Hfrontier]] Hcert Hrestrict.
  destruct Hcert as
    [Hlearned_sound [Hlearned_nonempty [Htarget [Hasserting Hlearned_frontier]]]].
  destruct Hclosed as
    [Hconflict_level [Hassigned_bounds [Hno_zero_decision Hunique_decision]]].
  destruct Hfrontier as [Hno_active Hsupported].
  destruct Hlearned_frontier as [Hlearned_no_active Hlearned_target].
  split.
  - unfold grounded_at in Hgrounded |- *.
    intros x b Hnew_assignment.
    pose proof
      (restrict_new_assigned_old__backtrack_finish_decide_bounds _ _ _ _ _ Hrestrict Hnew_assignment)
      as Hretained.
    destruct Hretained as
      [d [Hold_level [Hdbound [Hold_assignment
        [Hnew_level [Hnew_reason Hnew_rank]]]]]].
    assert (Hconflict_assignment : assignment conflict x = Some b).
    { rewrite <- Hassignment; exact Hold_assignment. }
    specialize (Hgrounded x b Hconflict_assignment).
    destruct Hgrounded as
      [dc [rx [Hconflict_x_level [Hconflict_x_rank Hgrounded_case]]]].
    assert (Hdc : dc = d).
    { rewrite Hlevel in Hold_level.
      rewrite Hold_level in Hconflict_x_level.
      inversion Hconflict_x_level; reflexivity. }
    subst dc.
    exists d, rx.
    split.
    + rewrite Hnew_level, Hlevel; exact Hconflict_x_level.
    + split.
      * rewrite Hnew_rank, Hrank; exact Hconflict_x_rank.
      * destruct Hgrounded_case as
          [[Hconflict_reason Hdpositive] |
           [i [Hconflict_reason [Hvalid Hlevel_case]]]].
        -- left; split; [|exact Hdpositive].
           rewrite Hnew_reason, Hreason; exact Hconflict_reason.
        -- right; exists i.
           split.
           ++ rewrite Hnew_reason, Hreason; exact Hconflict_reason.
           ++ split.
              ** eapply reason_valid_transfer__backtrack_finish_decide_bounds with
                   (conflict := conflict) (old := old) (target := target)
                   (learned := learned) (d := d); eauto.
              ** destruct Hlevel_case as [-> | [y Hsame]].
                 --- left; reflexivity.
                 --- right; exists y.
                     eapply same_level_predecessor_transfer__backtrack_finish_decide_bounds with
                       (conflict := conflict) (old := old)
                       (target := target) (learned := learned); eauto.
  - split.
    + unfold closed_levels.
      pose proof Hrestrict as Hrestrict_closed.
      destruct Hrestrict_closed as [Hcurrent_level _].
      split; [rewrite Hcurrent_level; lia|].
      split.
      * intros x b d Hnew_assignment Hnew_level.
        pose proof
          (restrict_new_assigned_old__backtrack_finish_decide_bounds _ _ _ _ _ Hrestrict Hnew_assignment)
          as Hretained.
        destruct Hretained as
          [do [Hold_level [Hdobound [Hold_assignment
            [Hlevel_eq [Hreason_eq Hrank_eq]]]]]].
        assert (Hdo : do = d).
        { rewrite Hlevel_eq, Hold_level in Hnew_level.
          inversion Hnew_level; reflexivity. }
        subst do.
        assert (Hconflict_assignment : assignment conflict x = Some b).
        { rewrite <- Hassignment; exact Hold_assignment. }
        assert (Hconflict_level_x : level_of conflict x = Some d).
        { rewrite <- Hlevel; exact Hold_level. }
        specialize (Hassigned_bounds x b d
          Hconflict_assignment Hconflict_level_x).
        lia.
      * split.
        -- intros x Hdecision_new.
           apply (Hno_zero_decision x).
           unfold decision_at in Hdecision_new |- *.
           destruct Hdecision_new as [[b Hnew_assignment]
             [Hnew_level Hnew_reason]].
           pose proof
             (restrict_new_assigned_old__backtrack_finish_decide_bounds _ _ _ _ _
               Hrestrict Hnew_assignment) as Hretained.
           destruct Hretained as
             [d [Hold_level [Hdbound [Hold_assignment
               [Hlevel_eq [Hreason_eq Hrank_eq]]]]]].
           assert (Hd : d = 0).
           { rewrite Hlevel_eq, Hold_level in Hnew_level.
             inversion Hnew_level; reflexivity. }
           subst d.
           split.
           ++ exists b. rewrite <- Hassignment; exact Hold_assignment.
           ++ split.
              ** rewrite <- Hlevel; exact Hold_level.
              ** rewrite <- Hreason, <- Hreason_eq; exact Hnew_reason.
        -- intros d Hd.
           specialize (Hunique_decision d ltac:(lia)).
           destruct Hunique_decision as [x [Hdecision_x Hunique_x]].
           exists x.
           split.
           ++ unfold decision_at in Hdecision_x |- *.
              destruct Hdecision_x as [[b Hconflict_assignment]
                [Hconflict_level_x Hconflict_reason_x]].
              assert (Hold_level : level_of old x = Some d).
              { rewrite Hlevel; exact Hconflict_level_x. }
              pose proof
                (restrict_keeps_cell__backtrack_finish_decide_bounds _ _ _ _ _ Hrestrict
                  Hold_level ltac:(lia)) as Hkeep.
              destruct Hkeep as
                [Hassignment_eq [Hlevel_eq [Hreason_eq Hrank_eq]]].
              split.
              ** exists b. rewrite Hassignment_eq, Hassignment.
                 exact Hconflict_assignment.
              ** split.
                 --- rewrite Hlevel_eq, Hlevel; exact Hconflict_level_x.
                 --- rewrite Hreason_eq, Hreason; exact Hconflict_reason_x.
           ++ intros y Hdecision_y.
              apply Hunique_x.
              unfold decision_at in Hdecision_y |- *.
              destruct Hdecision_y as [[b Hnew_assignment]
                [Hnew_level Hnew_reason]].
              pose proof
                (restrict_new_assigned_old__backtrack_finish_decide_bounds _ _ _ _ _
                  Hrestrict Hnew_assignment) as Hretained.
              destruct Hretained as
                [dy [Hold_level [Hdybound [Hold_assignment
                  [Hlevel_eq [Hreason_eq Hrank_eq]]]]]].
              assert (Hdy : dy = d).
              { rewrite Hlevel_eq, Hold_level in Hnew_level.
                inversion Hnew_level; reflexivity. }
              subst dy.
              split.
              ** exists b. rewrite <- Hassignment; exact Hold_assignment.
              ** split.
                 --- rewrite <- Hlevel; exact Hold_level.
                 --- rewrite <- Hreason, <- Hreason_eq; exact Hnew_reason.
    + unfold frontier_closed.
      split.
      * intros k Hkrange.
        unfold no_active_clause_at.
        intros c Hin Hactive.
        pose proof Hrestrict as Hrestrict_copy.
        destruct Hrestrict_copy as [Hcurrent [Hnew_clauses Hcells]].
        rewrite Hcurrent in Hkrange.
        rewrite Hnew_clauses, Hclauses in Hin.
        apply in_app_iff in Hin.
        assert (Hsigma :
          restrict_to_level new k = restrict_to_level conflict k).
        { assert (Hktarget : k <= target) by lia.
          pose proof
            (restrict_to_level_chain__backtrack_finish_decide_bounds old new target k
              Hrestrict Hktarget) as Hchain.
          rewrite Hchain.
          unfold restrict_to_level.
          rewrite Hassignment, Hlevel.
          reflexivity. }
        rewrite Hsigma in Hactive.
        destruct Hin as [Hin_conflict | Hin_learned].
        -- specialize (Hno_active k ltac:(lia) c Hin_conflict).
           exact (Hno_active Hactive).
        -- cbn in Hin_learned.
           destruct Hin_learned as [Hceq | Hfalse]; [subst c|contradiction].
           exact (Hlearned_no_active k Hkrange Hactive).
      * unfold current_frontier_supported.
        pose proof Hrestrict as Hrestrict_copy.
        destruct Hrestrict_copy as [Hcurrent [Hnew_clauses Hcells]].
        rewrite Hcurrent.
        destruct (Z.eq_dec target 0) as [-> | Htarget_nonzero].
        -- left; reflexivity.
        -- right.
           intros c Hin Hactive.
           rewrite Hnew_clauses, Hclauses in Hin.
           apply in_app_iff in Hin.
           assert (Hsigma :
             restrict_to_level new target = restrict_to_level conflict target).
           { pose proof
               (restrict_to_level_chain__backtrack_finish_decide_bounds old new target target
                 Hrestrict (Z.le_refl target)) as Hchain.
             rewrite Hchain.
             unfold restrict_to_level.
             rewrite Hassignment, Hlevel.
             reflexivity. }
           rewrite Hsigma in Hactive.
           destruct Hin as [Hin_conflict | Hin_learned].
           ++ specialize (Hno_active target ltac:(lia) c Hin_conflict).
              contradiction.
           ++ cbn in Hin_learned.
              destruct Hin_learned as [Hceq | Hfalse]; [subst c|contradiction].
              destruct Hlearned_target as [Hzero | Hliteral];
                [contradiction|].
              destruct Hliteral as [l [Hin_l Hliteral]].
              exists l; split; [exact Hin_l|].
              unfold literal_false_at_level in Hliteral |- *.
              destruct Hliteral as [Heval Hliteral_level].
              split.
              ** rewrite Hsigma; exact Heval.
              ** assert (Hold_literal_level :
                   level_of old (literal_var l) = Some target).
                 { rewrite Hlevel; exact Hliteral_level. }
                 pose proof
                   (restrict_keeps_cell__backtrack_finish_decide_bounds _ _ _ _ _ Hrestrict
                     Hold_literal_level ltac:(lia)) as Hkeep.
                 destruct Hkeep as [_ [Hnew_level _]].
                 rewrite Hnew_level, Hlevel; exact Hliteral_level.
Qed.
(** ===== group: decide_commit ===== *)
Lemma literal_counts_below_dense_decode_from__decide_commit : forall row base x,
  x < base ->
  literal_var_count x (dense_decode_from base row) = 0 /\
  literal_true_at_count x true (dense_decode_from base row) = 0.
Proof.
  induction row as [|z row IH]; intros base x Hx; simpl.
  - split; reflexivity.
  - destruct (Z.eqb z 1) eqn:Hz1.
    + assert (Hneq : Z.eqb base x = false) by
        (apply Z.eqb_neq; lia).
      cbn [literal_var_count literal_true_at_count literal_var].
      rewrite Hneq.
      apply IH; lia.
    + destruct (Z.eqb z (-1)) eqn:Hzm.
      * assert (Hneq : Z.eqb base x = false) by
          (apply Z.eqb_neq; lia).
        cbn [literal_var_count literal_true_at_count literal_var].
        rewrite Hneq.
        apply IH; lia.
      * apply IH; lia.
Qed.
Lemma dense_decode_from_counts_at__decide_commit : forall row base i,
  0 <= i < Zlength row ->
  literal_var_count (base + i) (dense_decode_from base row) =
    (if orb (Z.eqb (Znth i row 0) 1) (Z.eqb (Znth i row 0) (-1))
     then 1 else 0) /\
  literal_true_at_count (base + i) true (dense_decode_from base row) =
    (if Z.eqb (Znth i row 0) 1 then 1 else 0).
Proof.
  induction row as [|z row IH]; intros base i Hi.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Znth0_cons.
      pose proof
        (literal_counts_below_dense_decode_from__decide_commit row
          (base + 1) base ltac:(lia)) as [Hv Ht].
      replace (base + 0) with base by lia.
      change
        (literal_var_count base
           (if Z.eqb z 1 then Pos base :: dense_decode_from (base + 1) row
            else if Z.eqb z (-1)
                 then Neg base :: dense_decode_from (base + 1) row
                 else dense_decode_from (base + 1) row) =
           (if orb (Z.eqb z 1) (Z.eqb z (-1)) then 1 else 0) /\
         literal_true_at_count base true
           (if Z.eqb z 1 then Pos base :: dense_decode_from (base + 1) row
            else if Z.eqb z (-1)
                 then Neg base :: dense_decode_from (base + 1) row
                 else dense_decode_from (base + 1) row) =
           (if Z.eqb z 1 then 1 else 0)).
      destruct (Z.eqb z 1) eqn:Hz1.
      * cbn [literal_var_count literal_true_at_count literal_var eval_literal].
        rewrite Z.eqb_refl.
        change
          (1 + literal_var_count base (dense_decode_from (base + 1) row) = 1 /\
           1 + literal_true_at_count base true
             (dense_decode_from (base + 1) row) = 1).
        split; lia.
      * destruct (Z.eqb z (-1)) eqn:Hzm.
        -- cbn [literal_var_count literal_true_at_count literal_var eval_literal].
           rewrite Z.eqb_refl.
           change
             (1 + literal_var_count base
                (dense_decode_from (base + 1) row) = 1 /\
              literal_true_at_count base true
                (dense_decode_from (base + 1) row) = 0).
           split; lia.
        -- change
             (literal_var_count base
                (dense_decode_from (base + 1) row) = 0 /\
              literal_true_at_count base true
                (dense_decode_from (base + 1) row) = 0).
           split; lia.
    + rewrite Znth_cons by lia.
      specialize (IH (base + 1) (i - 1) ltac:(lia)).
      replace ((base + 1) + (i - 1)) with (base + i) in IH by lia.
      change
        (literal_var_count (base + i)
           (if Z.eqb z 1 then Pos base :: dense_decode_from (base + 1) row
            else if Z.eqb z (-1)
                 then Neg base :: dense_decode_from (base + 1) row
                 else dense_decode_from (base + 1) row) =
           (if orb (Z.eqb (Znth (i - 1) row 0) 1)
                   (Z.eqb (Znth (i - 1) row 0) (-1))
            then 1 else 0) /\
         literal_true_at_count (base + i) true
           (if Z.eqb z 1 then Pos base :: dense_decode_from (base + 1) row
            else if Z.eqb z (-1)
                 then Neg base :: dense_decode_from (base + 1) row
                 else dense_decode_from (base + 1) row) =
           (if Z.eqb (Znth (i - 1) row 0) 1 then 1 else 0)).
      destruct (Z.eqb z 1) eqn:Hz1.
      * assert (Hneq : Z.eqb base (base + i) = false) by
          (apply Z.eqb_neq; lia).
        cbn [literal_var_count literal_true_at_count literal_var eval_literal].
        rewrite Hneq.
        exact IH.
      * destruct (Z.eqb z (-1)) eqn:Hzm.
        -- assert (Hneq : Z.eqb base (base + i) = false) by
             (apply Z.eqb_neq; lia).
           cbn [literal_var_count literal_true_at_count literal_var eval_literal].
           rewrite Hneq.
           exact IH.
        -- exact IH.
Qed.
Lemma dense_decode_counts_at__decide_commit : forall n row i,
  row_wf n row -> var_in_range n i ->
  literal_var_count i (dense_decode row) =
    (if orb (Z.eqb (Znth i row 0) 1) (Z.eqb (Znth i row 0) (-1))
     then 1 else 0) /\
  literal_true_at_count i true (dense_decode row) =
    (if Z.eqb (Znth i row 0) 1 then 1 else 0).
Proof.
  intros n row i [Hlen _] [Hi0 Hin].
  unfold dense_decode.
  pose proof
    (dense_decode_from_counts_at__decide_commit row 0 i
      ltac:(rewrite Hlen; lia)) as H.
  replace (0 + i) with i in H by lia.
  exact H.
Qed.
Lemma assignment_update_only_eq__decide_commit : forall old new x b,
  assignment_update_only old new x b ->
  assignment new = partial_mapping_update (assignment old) x b.
Proof.
  intros old new x b [Hxold [Hxnew [Hother _]]].
  apply functional_extensionality; intro y.
  destruct (Z.eq_dec y x) as [->|Hneq].
  - rewrite partial_mapping_update_eq; exact Hxnew.
  - rewrite partial_mapping_update_neq by congruence.
    apply Hother; exact Hneq.
Qed.
Lemma summary_at_assignment_true_replace__decide_commit :
  forall old_sigma new_sigma rows states true_counts unassigned j x
    new_state new_true new_unassigned,
  old_sigma x = None ->
  new_sigma = partial_mapping_update old_sigma x true ->
  summary_at old_sigma rows states true_counts unassigned j ->
  new_true = Znth j true_counts 0 +
    literal_true_at_count x true (Znth j rows nil) ->
  new_unassigned = Znth j unassigned 0 -
    literal_var_count x (Znth j rows nil) ->
  new_state = expected_clause_state new_sigma (Znth j rows nil) ->
  0 <= j < Zlength states ->
  Zlength true_counts = Zlength states ->
  Zlength unassigned = Zlength states ->
  summary_at new_sigma rows
    (replace_Znth j new_state states)
    (replace_Znth j new_true true_counts)
    (replace_Znth j new_unassigned unassigned) j.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned j x
    new_state new_true new_unassigned Hnone Hnew Hold Htrue Hunassigned
    Hstate Hj Htrue_len Hunassigned_len.
  unfold summary_at, clause_summary_ok in Hold |- *.
  destruct Hold as [Hold_true [Hold_unassigned Hold_state]].
  subst new_sigma.
  pose proof (clause_counts_assign old_sigma x true
    (Znth j rows nil) Hnone) as [Hcount_unassigned Hcount_true].
  rewrite !Znth_replace_Znth_Same by lia.
  repeat split; subst; lia.
Qed.
Lemma Znth_map_dense_decode__decide_commit : forall rows j,
  0 <= j < Zlength rows ->
  Znth j (map dense_decode rows) nil = dense_decode (Znth j rows nil).
Proof.
  intros rows j Hj. apply Znth_map. exact Hj.
Qed.
Lemma coherent_snapshot_row_wf__decide_commit :
  forall F n live original_count snap j,
  coherent_snapshot F n live original_count snap ->
  0 <= j < live ->
  row_wf n (Znth j (snap_rows snap) nil).
Proof.
  intros F n live original_count snap j Hcoh Hj.
  unfold coherent_snapshot in Hcoh.
  destruct Hcoh as [_ [_ [Hlens [Hcells _]]]].
  destruct Hlens as [_ [_ [_ [Hrows_len _]]]].
  destruct Hcells as [_ Hrows].
  apply Forall_forall with (x := Znth j (snap_rows snap) nil) in Hrows.
  - exact Hrows.
  - unfold Znth.
    apply nth_In.
    replace (List.length (snap_rows snap)) with
      (Z.to_nat (Zlength (snap_rows snap))).
    + apply Z2Nat.inj_lt; lia.
    + rewrite Zlength_correct, Nat2Z.id. reflexivity.
Qed.
Lemma expected_state_assign_absent__decide_commit :
  forall old_sigma new_sigma x c,
  old_sigma x = None ->
  new_sigma = partial_mapping_update old_sigma x true ->
  literal_var_count x c = 0 ->
  literal_true_at_count x true c = 0 ->
  expected_clause_state new_sigma c = expected_clause_state old_sigma c.
Proof.
  intros old_sigma new_sigma x c Hnone Hnew Hvar Htrue.
  subst new_sigma.
  pose proof (clause_counts_assign old_sigma x true c Hnone)
    as [Hunassigned_count Htrue_count].
  unfold expected_clause_state.
  rewrite Hunassigned_count, Htrue_count, Hvar, Htrue.
  replace (clause_true_count old_sigma c + 0)
    with (clause_true_count old_sigma c) by lia.
  replace (clause_unassigned_count old_sigma c - 0)
    with (clause_unassigned_count old_sigma c) by lia.
  reflexivity.
Qed.
Lemma expected_state_assign_positive__decide_commit :
  forall old_sigma new_sigma x c,
  old_sigma x = None ->
  new_sigma = partial_mapping_update old_sigma x true ->
  literal_true_at_count x true c = 1 ->
  expected_clause_state new_sigma c = 0.
Proof.
  intros old_sigma new_sigma x c Hnone Hnew Hliteral_true.
  subst new_sigma.
  pose proof (clause_counts_assign old_sigma x true c Hnone)
    as [_ Htrue_count].
  pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment old_sigma c) as Hnonneg.
  unfold expected_clause_state.
  rewrite Htrue_count, Hliteral_true.
  destruct ((0 <? clause_true_count old_sigma c + 1)%Z) eqn:Hpositive.
  - reflexivity.
  - apply Z.ltb_ge in Hpositive. lia.
Qed.
Lemma expected_state_assign_negative__decide_commit :
  forall old_sigma new_sigma x c old_state old_true old_unassigned,
  old_sigma x = None ->
  new_sigma = partial_mapping_update old_sigma x true ->
  literal_var_count x c = 1 ->
  literal_true_at_count x true c = 0 ->
  clause_summary_ok old_sigma c old_state old_true old_unassigned ->
  old_state < 0 ->
  expected_clause_state new_sigma c =
    (if Z.eqb (old_state + 1) (-1) then 2 else old_state + 1).
Proof.
  intros old_sigma new_sigma x c old_state old_true old_unassigned
    Hnone Hnew Hvar Hliteral_true Hsummary Hnegative.
  unfold clause_summary_ok in Hsummary.
  destruct Hsummary as [Htrue [Hunassigned Hstate]].
  subst new_sigma.
  pose proof (clause_counts_assign old_sigma x true c Hnone)
    as [Hunassigned_count Htrue_count].
  pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment old_sigma c) as Htnonneg.
  pose proof (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment old_sigma c) as Hunonneg.
  unfold expected_clause_state in Hstate |- *.
  rewrite Hunassigned_count, Htrue_count, Hvar, Hliteral_true.
  destruct ((0 <? clause_true_count old_sigma c)%Z) eqn:Htpos.
  - apply Z.ltb_lt in Htpos. lia.
  - apply Z.ltb_ge in Htpos.
    assert (Htzero : clause_true_count old_sigma c = 0) by lia.
    try rewrite Htzero in Hstate.
    rewrite Htzero.
    cbn in Hstate |- *.
    destruct ((clause_unassigned_count old_sigma c =? 0)%Z) eqn:Hu0.
    + apply Z.eqb_eq in Hu0. lia.
    + apply Z.eqb_neq in Hu0.
      destruct ((clause_unassigned_count old_sigma c =? 1)%Z) eqn:Hu1.
      * apply Z.eqb_eq in Hu1. lia.
      * apply Z.eqb_neq in Hu1.
        assert (Hu_gt : 1 < clause_unassigned_count old_sigma c) by lia.
        destruct (Z.eqb (old_state + 1) (-1)) eqn:Hbranch.
        -- apply Z.eqb_eq in Hbranch.
           assert (Hu_eq : clause_unassigned_count old_sigma c = 2) by lia.
           rewrite Hu_eq. reflexivity.
        -- apply Z.eqb_neq in Hbranch.
           destruct ((clause_unassigned_count old_sigma c - 1 =? 0)%Z)
             eqn:Hnew0.
           ++ apply Z.eqb_eq in Hnew0. lia.
           ++ apply Z.eqb_neq in Hnew0.
              destruct ((clause_unassigned_count old_sigma c - 1 =? 1)%Z)
                eqn:Hnew1.
              ** apply Z.eqb_eq in Hnew1. lia.
              ** apply Z.eqb_neq in Hnew1. lia.
Qed.
Lemma expected_state_assign_negative_stays_zero__decide_commit :
  forall old_sigma new_sigma x c old_true old_unassigned,
  old_sigma x = None ->
  new_sigma = partial_mapping_update old_sigma x true ->
  literal_var_count x c = 1 ->
  literal_true_at_count x true c = 0 ->
  clause_summary_ok old_sigma c 0 old_true old_unassigned ->
  expected_clause_state new_sigma c = 0.
Proof.
  intros old_sigma new_sigma x c old_true old_unassigned
    Hnone Hnew Hvar Hliteral_true Hsummary.
  unfold clause_summary_ok in Hsummary.
  destruct Hsummary as [Htrue [Hunassigned Hstate]].
  subst new_sigma.
  pose proof (clause_counts_assign old_sigma x true c Hnone)
    as [Hunassigned_count Htrue_count].
  pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment old_sigma c) as Htnonneg.
  pose proof (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment old_sigma c) as Hunonneg.
  unfold expected_clause_state in Hstate |- *.
  rewrite Hunassigned_count, Htrue_count, Hvar, Hliteral_true.
  destruct ((0 <? clause_true_count old_sigma c)%Z) eqn:Htpos.
  - replace (clause_true_count old_sigma c + 0)
      with (clause_true_count old_sigma c) by lia.
    rewrite Htpos. reflexivity.
  - apply Z.ltb_ge in Htpos.
    assert (Htzero : clause_true_count old_sigma c = 0) by lia.
    try rewrite Htzero in Hstate.
    rewrite Htzero.
    cbn in Hstate |- *.
    destruct ((clause_unassigned_count old_sigma c =? 0)%Z) eqn:Hu0.
    + discriminate.
    + destruct ((clause_unassigned_count old_sigma c =? 1)%Z) eqn:Hu1.
      * discriminate.
      * apply Z.eqb_neq in Hu0. apply Z.eqb_neq in Hu1. lia.
Qed.
Lemma decision_mixed_dense_replace_step__decide_commit :
  forall old new raw_rows states true_counts unassigned live cap j x n
    new_state new_true new_unassigned,
  assignment_update_only old new x true ->
  mixed_clause_summaries (assignment old) (assignment new)
    (map dense_decode raw_rows) states true_counts unassigned live cap j None ->
  0 <= j < live ->
  row_wf n (Znth j raw_rows nil) ->
  var_in_range n x ->
  new_true = Znth j true_counts 0 +
    (if Z.eqb (Znth x (Znth j raw_rows nil) 0) 1 then 1 else 0) ->
  new_unassigned = Znth j unassigned 0 -
    (if orb (Z.eqb (Znth x (Znth j raw_rows nil) 0) 1)
            (Z.eqb (Znth x (Znth j raw_rows nil) 0) (-1))
     then 1 else 0) ->
  new_state = expected_clause_state (assignment new)
    (Znth j (map dense_decode raw_rows) nil) ->
  mixed_clause_summaries (assignment old) (assignment new)
    (map dense_decode raw_rows)
    (replace_Znth j new_state states)
    (replace_Znth j new_true true_counts)
    (replace_Znth j new_unassigned unassigned)
    live cap (j + 1) None.
Proof.
  intros old new raw_rows states true_counts unassigned live cap j x n
    new_state new_true new_unassigned Hassign Hmix Hj Hrow Hx
    Htrue Hunassigned Hstate.
  pose proof Hmix as Hmix_copy.
  unfold mixed_clause_summaries in Hmix_copy.
  destruct Hmix_copy as
    [Hrows [Hstates [Htrue_len [Hunassigned_len
      [Hcap [Hprocessed Hall]]]]]].
  specialize (Hall j Hj).
  destruct Hall as [_ Hold].
  specialize (Hold ltac:(split; [lia|discriminate])).
  pose proof (assignment_update_only_eq__decide_commit old new x true Hassign)
    as Hmap.
  pose proof (dense_decode_counts_at__decide_commit n
    (Znth j raw_rows nil) x Hrow Hx) as [Hvar_count Htrue_count].
  pose proof (Zlength_map_dense_decode__bcp_safety_to_scan_init raw_rows) as Hmaplen.
  assert (Hjraw : 0 <= j < Zlength raw_rows) by lia.
  pose proof (Znth_map_dense_decode__decide_commit raw_rows j Hjraw)
    as Hrow_decode.
  apply mixed_clause_summaries_advance__backtrack_entry_clear_a
    with (old_sigma := assignment old) (new_sigma := assignment new)
      (rows := map dense_decode raw_rows) (states := states)
      (true_counts := true_counts) (unassigned := unassigned)
      (live := live) (cap := cap) (j := j); try assumption.
  destruct Hassign as [Hnone _].
  eapply summary_at_assignment_true_replace__decide_commit
    with (old_sigma := assignment old) (x := x).
  - exact Hnone.
  - exact Hmap.
  - exact Hold.
  - rewrite Hrow_decode, Htrue_count. exact Htrue.
  - rewrite Hrow_decode, Hvar_count. exact Hunassigned.
  - exact Hstate.
  - lia.
  - lia.
  - lia.
Qed.
Lemma mixed_clause_summaries_old_at__decide_commit :
  forall old_sigma new_sigma rows states true_counts unassigned live cap j,
  mixed_clause_summaries old_sigma new_sigma rows states true_counts unassigned
    live cap j None ->
  0 <= j < live ->
  summary_at old_sigma rows states true_counts unassigned j.
Proof.
  intros old_sigma new_sigma rows states true_counts unassigned live cap j
    Hmix Hj.
  unfold mixed_clause_summaries in Hmix.
  destruct Hmix as [_ [_ [_ [_ [_ [_ Hall]]]]]].
  specialize (Hall j Hj).
  destruct Hall as [_ Hold].
  apply Hold. split; [lia|discriminate].
Qed.
Lemma decision_mixed_dense_absent_step__decide_commit :
  forall old new raw_rows states true_counts unassigned live cap j x n,
  assignment_update_only old new x true ->
  mixed_clause_summaries (assignment old) (assignment new)
    (map dense_decode raw_rows) states true_counts unassigned live cap j None ->
  0 <= j < live ->
  row_wf n (Znth j raw_rows nil) ->
  var_in_range n x ->
  Znth x (Znth j raw_rows nil) 0 = 0 ->
  mixed_clause_summaries (assignment old) (assignment new)
    (map dense_decode raw_rows) states true_counts unassigned
    live cap (j + 1) None.
Proof.
  intros old new raw_rows states true_counts unassigned live cap j x n
    Hassign Hmix Hj Hrow Hx Hcell.
  pose proof (mixed_clause_summaries_old_at__decide_commit
    _ _ _ _ _ _ _ _ _ Hmix Hj) as Hold.
  unfold summary_at, clause_summary_ok in Hold.
  destruct Hold as [Hold_true [Hold_unassigned Hold_state]].
  pose proof (assignment_update_only_eq__decide_commit
    old new x true Hassign) as Hmap.
  pose proof Hmix as Hlengths.
  unfold mixed_clause_summaries in Hlengths.
  destruct Hlengths as
    [Hrows [Hstates [Htrue_len [Hunassigned_len _]]]].
  pose proof (Zlength_map_dense_decode__bcp_safety_to_scan_init raw_rows) as Hmap_len.
  assert (Hjraw : 0 <= j < Zlength raw_rows) by lia.
  pose proof (Znth_map_dense_decode__decide_commit raw_rows j Hjraw)
    as Hrow_decode.
  pose proof (dense_decode_counts_at__decide_commit n
    (Znth j raw_rows nil) x Hrow Hx) as [Hvar_count Hliteral_true].
  rewrite Hcell in Hvar_count, Hliteral_true.
  cbn in Hvar_count, Hliteral_true.
  pose proof (expected_state_assign_absent__decide_commit
    (assignment old) (assignment new) x
    (dense_decode (Znth j raw_rows nil)) (proj1 Hassign) Hmap
    Hvar_count Hliteral_true) as Hexpected.
  assert (Hnew_state : Znth j states 0 =
    expected_clause_state (assignment new)
      (Znth j (map dense_decode raw_rows) nil)).
  { rewrite Hrow_decode, Hexpected.
    rewrite Hrow_decode in Hold_state. exact Hold_state. }
  pose proof (decision_mixed_dense_replace_step__decide_commit
    old new raw_rows states true_counts unassigned live cap j x n
    (Znth j states 0) (Znth j true_counts 0) (Znth j unassigned 0)
    Hassign Hmix Hj Hrow Hx) as Hadvance.
  rewrite Hcell in Hadvance. cbn in Hadvance.
  specialize (Hadvance ltac:(lia) ltac:(lia) Hnew_state).
  rewrite !replace_Znth_Znth in Hadvance by lia.
  exact Hadvance.
Qed.
Lemma decision_mixed_dense_positive_step__decide_commit :
  forall old new raw_rows states true_counts unassigned live cap j x n,
  assignment_update_only old new x true ->
  mixed_clause_summaries (assignment old) (assignment new)
    (map dense_decode raw_rows) states true_counts unassigned live cap j None ->
  0 <= j < live ->
  row_wf n (Znth j raw_rows nil) ->
  var_in_range n x ->
  Znth x (Znth j raw_rows nil) 0 = 1 ->
  mixed_clause_summaries (assignment old) (assignment new)
    (map dense_decode raw_rows)
    (replace_Znth j 0 states)
    (replace_Znth j (Znth j true_counts 0 + 1) true_counts)
    (replace_Znth j (Znth j unassigned 0 - 1) unassigned)
    live cap (j + 1) None.
Proof.
  intros old new raw_rows states true_counts unassigned live cap j x n
    Hassign Hmix Hj Hrow Hx Hcell.
  pose proof (assignment_update_only_eq__decide_commit
    old new x true Hassign) as Hmap.
  pose proof Hmix as Hlengths.
  unfold mixed_clause_summaries in Hlengths.
  destruct Hlengths as [Hrows _].
  pose proof (Zlength_map_dense_decode__bcp_safety_to_scan_init raw_rows) as Hmap_len.
  assert (Hjraw : 0 <= j < Zlength raw_rows) by lia.
  pose proof (Znth_map_dense_decode__decide_commit raw_rows j Hjraw)
    as Hrow_decode.
  pose proof (dense_decode_counts_at__decide_commit n
    (Znth j raw_rows nil) x Hrow Hx) as [_ Hliteral_true].
  rewrite Hcell in Hliteral_true. cbn in Hliteral_true.
  pose proof (expected_state_assign_positive__decide_commit
    (assignment old) (assignment new) x
    (dense_decode (Znth j raw_rows nil)) (proj1 Hassign) Hmap
    Hliteral_true) as Hexpected.
  apply decision_mixed_dense_replace_step__decide_commit
    with (old := old) (new := new) (raw_rows := raw_rows)
      (states := states) (true_counts := true_counts)
      (unassigned := unassigned) (live := live) (cap := cap)
      (j := j) (x := x) (n := n); try assumption.
  - rewrite Hcell. reflexivity.
  - rewrite Hcell. reflexivity.
  - rewrite Hrow_decode. symmetry. exact Hexpected.
Qed.
Lemma decision_mixed_dense_negative_step__decide_commit :
  forall old new raw_rows states true_counts unassigned live cap j x n,
  assignment_update_only old new x true ->
  mixed_clause_summaries (assignment old) (assignment new)
    (map dense_decode raw_rows) states true_counts unassigned live cap j None ->
  0 <= j < live ->
  row_wf n (Znth j raw_rows nil) ->
  var_in_range n x ->
  Znth x (Znth j raw_rows nil) 0 = -1 ->
  Znth j states 0 < 0 ->
  mixed_clause_summaries (assignment old) (assignment new)
    (map dense_decode raw_rows)
    (replace_Znth j
      (if Z.eqb (Znth j states 0 + 1) (-1)
       then 2 else Znth j states 0 + 1) states)
    true_counts
    (replace_Znth j (Znth j unassigned 0 - 1) unassigned)
    live cap (j + 1) None.
Proof.
  intros old new raw_rows states true_counts unassigned live cap j x n
    Hassign Hmix Hj Hrow Hx Hcell Hnegative.
  pose proof (mixed_clause_summaries_old_at__decide_commit
    _ _ _ _ _ _ _ _ _ Hmix Hj) as Hold.
  unfold summary_at in Hold.
  pose proof (assignment_update_only_eq__decide_commit
    old new x true Hassign) as Hmap.
  pose proof Hmix as Hlengths.
  unfold mixed_clause_summaries in Hlengths.
  destruct Hlengths as
    [Hrows [Hstates [Htrue_len [Hunassigned_len _]]]].
  pose proof (Zlength_map_dense_decode__bcp_safety_to_scan_init raw_rows) as Hmap_len.
  assert (Hjraw : 0 <= j < Zlength raw_rows) by lia.
  pose proof (Znth_map_dense_decode__decide_commit raw_rows j Hjraw)
    as Hrow_decode.
  pose proof (dense_decode_counts_at__decide_commit n
    (Znth j raw_rows nil) x Hrow Hx) as [Hvar_count Hliteral_true].
  rewrite Hcell in Hvar_count, Hliteral_true.
  cbn in Hvar_count, Hliteral_true.
  pose proof (expected_state_assign_negative__decide_commit
    (assignment old) (assignment new) x
    (dense_decode (Znth j raw_rows nil))
    (Znth j states 0) (Znth j true_counts 0) (Znth j unassigned 0)
    (proj1 Hassign) Hmap Hvar_count Hliteral_true) as Hexpected.
  rewrite Hrow_decode in Hold.
  specialize (Hexpected Hold Hnegative).
  pose proof (decision_mixed_dense_replace_step__decide_commit
    old new raw_rows states true_counts unassigned live cap j x n
    (if Z.eqb (Znth j states 0 + 1) (-1)
     then 2 else Znth j states 0 + 1)
    (Znth j true_counts 0) (Znth j unassigned 0 - 1)
    Hassign Hmix Hj Hrow Hx) as Hadvance.
  rewrite Hcell in Hadvance. cbn in Hadvance.
  specialize (Hadvance ltac:(lia) ltac:(lia)
    ltac:(rewrite Hrow_decode; symmetry; exact Hexpected)).
  rewrite replace_Znth_Znth in Hadvance by lia.
  exact Hadvance.
Qed.
Lemma decision_mixed_dense_negative_zero_step__decide_commit :
  forall old new raw_rows states true_counts unassigned live cap j x n,
  assignment_update_only old new x true ->
  mixed_clause_summaries (assignment old) (assignment new)
    (map dense_decode raw_rows) states true_counts unassigned live cap j None ->
  0 <= j < live ->
  row_wf n (Znth j raw_rows nil) ->
  var_in_range n x ->
  Znth x (Znth j raw_rows nil) 0 = -1 ->
  Znth j states 0 = 0 ->
  mixed_clause_summaries (assignment old) (assignment new)
    (map dense_decode raw_rows) states true_counts
    (replace_Znth j (Znth j unassigned 0 - 1) unassigned)
    live cap (j + 1) None.
Proof.
  intros old new raw_rows states true_counts unassigned live cap j x n
    Hassign Hmix Hj Hrow Hx Hcell Hstate_zero.
  pose proof (mixed_clause_summaries_old_at__decide_commit
    _ _ _ _ _ _ _ _ _ Hmix Hj) as Hold.
  unfold summary_at in Hold.
  pose proof (assignment_update_only_eq__decide_commit
    old new x true Hassign) as Hmap.
  pose proof Hmix as Hlengths.
  unfold mixed_clause_summaries in Hlengths.
  destruct Hlengths as
    [Hrows [Hstates [Htrue_len [Hunassigned_len _]]]].
  pose proof (Zlength_map_dense_decode__bcp_safety_to_scan_init raw_rows) as Hmap_len.
  assert (Hjraw : 0 <= j < Zlength raw_rows) by lia.
  pose proof (Znth_map_dense_decode__decide_commit raw_rows j Hjraw)
    as Hrow_decode.
  pose proof (dense_decode_counts_at__decide_commit n
    (Znth j raw_rows nil) x Hrow Hx) as [Hvar_count Hliteral_true].
  rewrite Hcell in Hvar_count, Hliteral_true.
  cbn in Hvar_count, Hliteral_true.
  pose proof (expected_state_assign_negative_stays_zero__decide_commit
    (assignment old) (assignment new) x
    (dense_decode (Znth j raw_rows nil))
    (Znth j true_counts 0) (Znth j unassigned 0)
    (proj1 Hassign) Hmap Hvar_count Hliteral_true) as Hexpected.
  rewrite Hrow_decode in Hold.
  rewrite Hstate_zero in Hold.
  specialize (Hexpected Hold).
  pose proof (decision_mixed_dense_replace_step__decide_commit
    old new raw_rows states true_counts unassigned live cap j x n
    (Znth j states 0) (Znth j true_counts 0)
    (Znth j unassigned 0 - 1)
    Hassign Hmix Hj Hrow Hx) as Hadvance.
  rewrite Hcell in Hadvance. cbn in Hadvance.
  specialize (Hadvance ltac:(lia) ltac:(lia)
    ltac:(rewrite Hrow_decode; rewrite Hstate_zero; symmetry; exact Hexpected)).
  rewrite !replace_Znth_Znth in Hadvance by lia.
  exact Hadvance.
Qed.
Lemma clause_summary_negative_true_zero__decide_commit :
  forall sigma c state true_count unassigned_count,
  clause_summary_ok sigma c state true_count unassigned_count ->
  state < 0 ->
  true_count = 0.
Proof.
  intros sigma c state true_count unassigned_count Hsummary Hnegative.
  unfold clause_summary_ok in Hsummary.
  destruct Hsummary as [Htrue [_ Hstate]].
  pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment sigma c) as Hnonneg.
  unfold expected_clause_state in Hstate.
  destruct ((0 <? clause_true_count sigma c)%Z) eqn:Hpositive.
  - lia.
  - apply Z.ltb_ge in Hpositive. lia.
Qed.
Lemma Znth_In__decide_commit : forall (A : Type) (l : list A) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros A l i d Hi.
  unfold Znth. apply nth_In.
  replace (List.length l) with (Z.to_nat (Zlength l)).
  - apply Z2Nat.inj_lt; lia.
  - rewrite Zlength_correct, Nat2Z.id. reflexivity.
Qed.
Lemma clause_summary_state_two_unit__decide_commit :
  forall sigma c true_count unassigned_count,
  clause_summary_ok sigma c 2 true_count unassigned_count ->
  clause_unit sigma c.
Proof.
  intros sigma c true_count unassigned_count Hsummary.
  unfold clause_summary_ok in Hsummary.
  destruct Hsummary as [Htrue [Hunassigned Hstate]].
  pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment sigma c) as Htnonneg.
  pose proof (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment sigma c) as Hunonneg.
  unfold expected_clause_state in Hstate.
  destruct ((0 <? clause_true_count sigma c)%Z) eqn:Htpos.
  - discriminate.
  - apply Z.ltb_ge in Htpos.
    assert (Htzero : clause_true_count sigma c = 0) by lia.
    destruct ((clause_unassigned_count sigma c =? 0)%Z) eqn:Hu0.
    + discriminate.
    + apply Z.eqb_neq in Hu0.
      destruct ((clause_unassigned_count sigma c =? 1)%Z) eqn:Hu1.
      * apply Z.eqb_eq in Hu1. split; assumption.
      * apply Z.eqb_neq in Hu1. lia.
Qed.
Lemma closed_levels_decision_prefix__decide_commit : forall a m,
  closed_levels a ->
  Z.of_nat m <= current_level a ->
  exists xs : list Z,
    List.length xs = m /\
    NoDup xs /\
    (forall x, In x xs ->
      exists d, 0 < d <= Z.of_nat m /\ decision_at a x d).
Proof.
  intros a m Hclosed.
  induction m as [|m IH]; intro Hbound.
  - exists nil. repeat split; try constructor.
    intros x Hin. inversion Hin.
  - pose proof Hclosed as Hclosed_parts.
    unfold closed_levels in Hclosed_parts.
    destruct Hclosed_parts as [Hlevel_nonneg
      [Hassigned_levels [Hno_root Hdecision_levels]]].
    destruct (IH ltac:(rewrite Nat2Z.inj_succ in Hbound; lia))
      as [xs [Hlen [Hnodup Hall]]].
    destruct (Hdecision_levels (Z.of_nat (S m)))
      as [x [Hxdecision Hxunique]].
    { rewrite Nat2Z.inj_succ. lia. }
    exists (x :: xs).
    split.
    { simpl. f_equal. exact Hlen. }
    split.
    + constructor.
      * intro Hin.
        destruct (Hall x Hin) as [d [[Hdpos Hdle] Hddecision]].
        unfold decision_at in Hxdecision, Hddecision.
        destruct Hxdecision as [_ [Hxlevel _]].
        destruct Hddecision as [_ [Hdlevel _]].
        rewrite Hxlevel in Hdlevel.
        inversion Hdlevel.
        rewrite Nat2Z.inj_succ in Hbound.
        lia.
      * exact Hnodup.
    + intros y [Hy | Hy].
      * subst y. exists (Z.of_nat (S m)).
        split; [rewrite Nat2Z.inj_succ; lia|exact Hxdecision].
      * destruct (Hall y Hy) as [d [[Hdpos Hdle] Hddecision]].
        exists d. split; [rewrite Nat2Z.inj_succ; lia|exact Hddecision].
Qed.
Lemma stable_unassigned_level_lt__decide_commit :
  forall n snap ranks logical_dl i,
  stable_search_facts n snap ranks logical_dl ->
  var_in_range n i ->
  snapshot_assignment n snap i = None ->
  logical_dl < n.
Proof.
  intros n snap ranks logical_dl i Hstable Hirange Hi_none.
  unfold stable_search_facts in Hstable.
  destruct Hstable as [_ [Hclosed _]].
  pose proof Hclosed as Hclosed_parts.
  unfold closed_levels in Hclosed_parts.
  destruct Hclosed_parts as [Hdl_nonneg _].
  destruct (closed_levels_decision_prefix__decide_commit
    (cdcl_view_of_snapshot n snap ranks logical_dl)
    (Z.to_nat logical_dl) Hclosed)
    as [xs [Hlen [Hnodup Hall]]].
  { change (Z.of_nat (Z.to_nat logical_dl) <= logical_dl).
    rewrite Z2Nat.id by exact Hdl_nonneg. lia. }
  assert (Hi_notin : ~ In i xs).
  {
    intro Hin.
    destruct (Hall i Hin) as [d [_ Hdecision]].
    unfold decision_at in Hdecision.
    destruct Hdecision as [[b Hb] _].
    simpl in Hb.
    rewrite Hi_none in Hb. discriminate.
  }
  pose proof (NoDup_Z_bounded_length
    (i :: xs) n ltac:(destruct Hirange; lia)) as Hcard.
  assert (Hnodup_all : NoDup (i :: xs)) by (constructor; assumption).
  specialize (Hcard Hnodup_all).
  assert (Hbounded : forall x, In x (i :: xs) -> 0 <= x < n).
  {
    intros x [Hx | Hxin].
    - subst x. exact Hirange.
    - destruct (Hall x Hxin) as [d [_ Hdecision]].
      unfold decision_at in Hdecision.
      destruct Hdecision as [[b Hb] _].
      simpl in Hb.
      eapply snapshot_assignment_some_range__bcp_unit_to_assignment; eauto.
  }
  specialize (Hcard Hbounded).
  change (Z.of_nat (S (List.length xs)) <= n) in Hcard.
  rewrite Nat2Z.inj_succ, Hlen in Hcard.
  rewrite Z2Nat.id in Hcard by exact Hdl_nonneg.
  lia.
Qed.
Lemma snapshot_assignment_set_true_update__decide_commit :
  forall n live snap ranks old_dl new_dl x,
  snapshot_lengths n live snap ->
  var_in_range n x ->
  snapshot_assignment n snap x = None ->
  assignment_update_only
    (cdcl_view_of_snapshot n snap ranks old_dl)
    (cdcl_view_of_snapshot n (snapshot_set_value snap x 1) ranks new_dl)
    x true.
Proof.
  intros n live snap ranks old_dl new_dl x Hlengths Hxrange Hxnone.
  unfold assignment_update_only; simpl.
  repeat split.
  - exact Hxnone.
  - unfold snapshot_assignment, snapshot_set_value; simpl.
    destruct Hxrange as [Hx0 Hxn].
    assert (Hguard : andb ((0 <=? x)%Z) ((x <? n)%Z) = true).
    { apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
    rewrite Hguard.
    destruct Hlengths as [Hv _].
    rewrite Znth_replace_Znth_Same by (rewrite Hv; lia).
    reflexivity.
  - intros y Hyx.
    unfold snapshot_assignment, snapshot_set_value; simpl.
    destruct (andb ((0 <=? y)%Z) ((y <? n)%Z)) eqn:Hyguard; auto.
    apply andb_true_iff in Hyguard.
    destruct Hyguard as [Hy0 Hyn].
    apply Z.leb_le in Hy0. apply Z.ltb_lt in Hyn.
    destruct Hlengths as [Hv _].
    rewrite Znth_replace_Znth_Diff.
    + reflexivity.
    + rewrite Hv. exact Hxrange.
    + rewrite Hv. lia.
    + congruence.
Qed.
Lemma mixed_clause_summaries_initial__decide_commit :
  forall n live cap snap new_sigma,
  snapshot_lengths n live snap ->
  snapshot_summaries_exact n live snap ->
  0 <= live <= cap ->
  mixed_clause_summaries
    (snapshot_assignment n snap) new_sigma
    (map dense_decode (snap_rows snap))
    (snap_states snap) (snap_true_counts snap) (snap_unassigned snap)
    live cap 0 None.
Proof.
  intros n live cap snap new_sigma Hlengths Hsummaries Hcap.
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as [_ [_ [_ [Hrows [Hstates [Htrue Hunassigned]]]]]].
  unfold mixed_clause_summaries.
  apply conj.
  { rewrite Zlength_correct, length_map, <- Zlength_correct, Hrows.
    reflexivity. }
  split; [exact Hstates|].
  split; [exact Htrue|].
  split; [exact Hunassigned|].
  split; [exact Hcap|].
  split; [lia|].
  intros j Hj.
  split.
  - intros [Hlt | Hnone]; [lia|discriminate].
  - intros _. apply Hsummaries. exact Hj.
Qed.
Lemma clause_unassigned_count_le_Zlength__decide_commit : forall sigma c,
  clause_unassigned_count sigma c <= Zlength c.
Proof.
  intros sigma c.
  induction c as [|l c IH].
  - simpl. rewrite Zlength_nil. lia.
  - cbn [clause_unassigned_count].
    rewrite Zlength_cons.
    destruct (eval_partial_literal sigma l) as [[|]|]; lia.
Qed.
(** ===== group: decide_exit_solver_setup ===== *)
Lemma clause_false_summary__decide_exit_solver_setup :
  forall sigma c,
    clause_false sigma c ->
    clause_summary_ok sigma c 1 0 0.
Proof.
  intros sigma c Hfalse.
  pose proof
    (clause_false_counts__learning_row_and_scan sigma c Hfalse)
    as [Ht Hu].
  unfold clause_summary_ok, expected_clause_state.
  rewrite Ht, Hu.
  repeat split; reflexivity.
Qed.
Lemma installed_clauses_sound_snoc__decide_exit_solver_setup :
  forall F original installed learned,
    0 <= original <= Zlength installed ->
    installed_clauses_sound F original installed ->
    entails_clause F learned ->
    installed_clauses_sound F original (installed ++ learned :: nil).
Proof.
  intros F original installed learned Hbounds Hsound Hlearned.
  unfold installed_clauses_sound, original_prefix_exact in *.
  destruct Hsound as [[Hprefix [Hcount Hnonempty]] Hlearned_old].
  assert (Hnat :
    (Z.to_nat original <= List.length installed)%nat).
  {
    apply Nat2Z.inj_le.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
  }
  split.
  - repeat split; [|exact Hcount|exact Hnonempty].
    rewrite firstn_app.
    replace (Z.to_nat original - List.length installed)%nat with 0%nat
      by lia.
    simpl.
    rewrite app_nil_r.
    exact Hprefix.
  - rewrite skipn_app.
    replace (Z.to_nat original - List.length installed)%nat with 0%nat
      by lia.
    simpl.
    apply Forall_app.
    split; [exact Hlearned_old|].
    constructor; [exact Hlearned|constructor].
Qed.
Lemma publish_false_learned_clause__decide_exit_solver_setup :
  forall F n live original snap ranks logical_dl row,
    coherent_snapshot F n live original snap ->
    row_wf n row ->
    current_learning_exit_cert F
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (dense_decode row) ->
    exists installed_snap,
      snap_values installed_snap = snap_values snap /\
      snap_reasons installed_snap = snap_reasons snap /\
      snap_levels installed_snap = snap_levels snap /\
      snap_rows installed_snap = snap_rows snap ++ row :: nil /\
      snap_states installed_snap = snap_states snap ++ 1 :: nil /\
      snap_true_counts installed_snap = snap_true_counts snap ++ 0 :: nil /\
      snap_unassigned installed_snap = snap_unassigned snap ++ 0 :: nil /\
      coherent_snapshot F n (live + 1) original installed_snap.
Proof.
  intros F n live original snap ranks logical_dl row
    Hcoherent Hrow Hexit.
  unfold current_learning_exit_cert, learned_clause_sound in Hexit.
  destruct Hexit as [[Hentails Hfalse] _].
  change (clause_false (snapshot_assignment n snap) (dense_decode row))
    in Hfalse.
  pose proof
    (clause_false_summary__decide_exit_solver_setup
      (snapshot_assignment n snap) (dense_decode row) Hfalse)
    as Hnew_summary.
  unfold coherent_snapshot in Hcoherent.
  destruct Hcoherent as
    [Hn [Horiginal [Hlengths [Hcells [Hsummaries Hsound]]]]].
  destruct Horiginal as [Horiginal_nonneg Horiginal_live].
  destruct Hlengths as
    [Hvalues [Hreasons [Hlevels [Hrows [Hstates [Htrue Hunassigned]]]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [Hvar_cells Hrow_cells].
  assert (Hmaprows :
    Zlength (map dense_decode (snap_rows snap)) = live).
  {
    rewrite Zlength_correct, length_map, <- Zlength_correct.
    exact Hrows.
  }
  exists
    {| snap_values := snap_values snap;
       snap_reasons := snap_reasons snap;
       snap_levels := snap_levels snap;
       snap_rows := snap_rows snap ++ row :: nil;
       snap_states := snap_states snap ++ 1 :: nil;
       snap_true_counts := snap_true_counts snap ++ 0 :: nil;
       snap_unassigned := snap_unassigned snap ++ 0 :: nil |}.
  cbn.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  unfold coherent_snapshot.
  split; [exact Hn|].
  split.
  { split; [exact Horiginal_nonneg|lia]. }
  split.
  - unfold snapshot_lengths; cbn.
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split.
    { rewrite Zlength_app, Hrows, Zlength_cons, Zlength_nil; lia. }
    split.
    { rewrite Zlength_app, Hstates, Zlength_cons, Zlength_nil; lia. }
    split.
    { rewrite Zlength_app, Htrue, Zlength_cons, Zlength_nil; lia. }
    rewrite Zlength_app, Hunassigned, Zlength_cons, Zlength_nil; lia.
  - split.
    + unfold snapshot_cells_wf.
      cbn [snap_values snap_reasons snap_levels snap_rows].
      split.
      * intros x Hx.
        specialize (Hvar_cells x Hx).
        destruct Hvar_cells as [Hvalue [Hnone Hassigned]].
        split; [exact Hvalue|].
        split; [exact Hnone|].
        intros Hnotnone.
        specialize (Hassigned Hnotnone).
        destruct Hassigned as [Hlevel Hreason].
        split; [exact Hlevel|].
        destruct Hreason as [Hnone_reason|Hreason].
        -- left; exact Hnone_reason.
        -- right; lia.
      * apply Forall_app.
        split; [exact Hrow_cells|].
        constructor; [exact Hrow|constructor].
    + split.
      * unfold snapshot_summaries_exact in *; cbn.
        intros i Hi.
        unfold summary_at in *; cbn.
        rewrite map_app; cbn.
        destruct (Z_lt_ge_dec i live) as [Hilt|Hige].
        -- specialize (Hsummaries i ltac:(lia)).
           rewrite app_Znth1 by lia.
           rewrite app_Znth1 by lia.
           rewrite app_Znth1 by lia.
           rewrite app_Znth1 by lia.
           exact Hsummaries.
        -- assert (Hi_eq : i = live) by lia.
           subst i.
           rewrite app_Znth2 by lia.
           rewrite app_Znth2 by lia.
           rewrite app_Znth2 by lia.
           rewrite app_Znth2 by lia.
           rewrite Hmaprows, Hstates, Htrue, Hunassigned.
           replace (live - live) with 0 by lia.
           repeat rewrite Znth0_cons.
           exact Hnew_summary.
      * cbn; rewrite map_app; cbn.
        apply installed_clauses_sound_snoc__decide_exit_solver_setup.
        -- rewrite Hmaprows. lia.
        -- exact Hsound.
        -- exact Hentails.
Qed.
Lemma dense_decode_literal_wf__decide_exit_solver_setup :
  forall n row l,
    row_wf n row ->
    In l (dense_decode row) ->
    literal_wf n l.
Proof.
  intros n row l [Hlength _] Hin.
  unfold literal_wf, var_in_range, dense_decode in *.
  split.
  - pose proof
      (dense_decode_from_var_lower_bound
        row 0 l Hin).
    lia.
  - pose proof
      (dense_decode_from_var_upper_bound__learning_row_and_scan
        row 0 l Hin).
    rewrite Hlength in H.
    lia.
Qed.

(* The backjump from old to new by going back to dl target clears all conflicts*)
Lemma stable_false_clause_vars_assigned__decide_exit_solver_setup :
  forall n snap ranks logical_dl L,
    stable_search_facts n snap ranks logical_dl ->
    clause_false
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl)) L ->
    clause_vars_assigned
      (cdcl_view_of_snapshot n snap ranks logical_dl) L.
Proof.
  intros n snap ranks logical_dl L Hstable Hfalse.
  unfold stable_search_facts in Hstable.
  destruct Hstable as [Hgrounded [Hclosed _]].
  unfold clause_vars_assigned.
  intros l Hin.
  specialize (Hfalse l Hin).
  destruct (assignment
    (cdcl_view_of_snapshot n snap ranks logical_dl) (literal_var l))
    as [b |] eqn:Hassigned.
  - specialize (Hgrounded (literal_var l) b Hassigned).
    destruct Hgrounded as [d [rx [Hlevel _]]].
    exists b, d.
    repeat split; auto.
    destruct Hclosed as [_ [Hbounds _]].
    specialize (Hbounds (literal_var l) b d Hassigned Hlevel).
    lia.
  - unfold eval_partial_literal in Hfalse.
    rewrite Hassigned in Hfalse.
    discriminate.
Qed.
Lemma ptr_seg_to_missing_tail__decide_exit_solver_setup :
  forall x lo hi a (l : list Z),
    PtrArray.seg x lo (hi - 1) l |--
    PtrArray.missing_i x (hi - 1) lo hi (l ++ a :: nil).
Proof.
  intros x lo hi a l.
  revert lo hi.
  induction l as [| b l IHl]; intros lo hi.
  - simpl app.
    rewrite PtrArray.seg_empty.
    rewrite PtrArray.missing_i_unfold.
    Left.
    rewrite PtrArray.seg_empty.
    entailer!.
  - simpl app.
    prop_apply
      (PtrArray.seg_length x lo (hi - 1) (b :: l)).
    Intros.
    rewrite PtrArray.seg_unfold.
    rewrite PtrArray.missing_i_unfold.
    Right.
    sep_apply (IHl (lo + 1) hi).
    entailer!.
    simpl in H.
    lia.
Qed.
Lemma remove_Znth_app_last__decide_exit_solver_setup :
  forall {A : Type} (l : list A) a,
    IntPtrArray2.remove_Znth (Z.of_nat (List.length l))
      (l ++ a :: nil) = l.
Proof.
  intros A l.
  induction l as [| b l IHl]; intros a.
  - reflexivity.
  - unfold IntPtrArray2.remove_Znth in *.
    rewrite !Nat2Z.id in *.
    simpl in *.
    f_equal.
    exact (IHl a).
Qed.
Lemma int_ptr_array_full_to_tail_missing__decide_exit_solver_setup :
  forall p live (rows : list (list Z)) newp (row : list Z),
    0 <= live ->
    IntPtrArray2.full p live rows |--
    IntPtrArray2.missing_i p (live + 1) live newp
      (rows ++ row :: nil).
Proof.
  intros p live rows newp row Hlive.
  unfold IntPtrArray2.full, IntPtrArray2.missing_i.
  Intros row_ptrs.
  destruct H as [Hptrs Hrows].
  Exists (row_ptrs ++ newp :: nil).
  assert (Hptrdirect :
    PtrArray.full p live row_ptrs |--
    PtrArray.missing_i p live 0 (live + 1)
      (row_ptrs ++ newp :: nil)).
  {
    pose proof
      (ptr_seg_to_missing_tail__decide_exit_solver_setup
        p 0 (live + 1) newp row_ptrs) as Htail.
    replace (live + 1 - 1) with live in Htail by lia.
    sep_apply PtrArray.full_to_seg.
    sep_apply Htail.
    entailer!.
  }
  assert (Hrowdirect :
    IntPtrArray2.row_blocks row_ptrs rows |--
    IntPtrArray2.row_blocks_missing_i live
      (row_ptrs ++ newp :: nil) (rows ++ row :: nil)).
  {
    assert (Hlen : List.length row_ptrs = List.length rows).
    {
      apply Nat2Z.inj.
      rewrite <- !Zlength_correct.
      lia.
    }
    assert (Hremove :
      IntPtrArray2.remove_Znth live
        (combine (row_ptrs ++ newp :: nil) (rows ++ row :: nil)) =
      combine row_ptrs rows).
    {
      unfold IntPtrArray2.remove_Znth.
      rewrite
        (combine_app row_ptrs (newp :: nil) rows (row :: nil) Hlen).
      simpl combine.
      replace live with
        (Z.of_nat (List.length (combine row_ptrs rows))).
      2: {
        rewrite length_combine, Hlen, Nat.min_id.
        rewrite Zlength_correct in Hptrs.
        lia.
      }
      apply remove_Znth_app_last__decide_exit_solver_setup.
    }
    unfold IntPtrArray2.row_blocks,
      IntPtrArray2.row_blocks_missing_i.
    rewrite Hremove.
    reflexivity.
  }
  entailer!.
  - sep_apply Hptrdirect.
    sep_apply Hrowdirect.
    entailer!.
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    lia.
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    lia.
  - rewrite app_Znth2 by lia.
    rewrite Hptrs.
    replace (live - live) with 0 by lia.
    rewrite Znth0_cons.
    reflexivity.
Qed.
Lemma dense_decode_forall_wf__decide_exit_solver_setup :
  forall n row,
    row_wf n row ->
    Forall (literal_wf n) (dense_decode row).
Proof.
  intros n row Hrow.
  apply Forall_forall.
  intros l Hin.
  eapply dense_decode_literal_wf__decide_exit_solver_setup; eauto.
Qed.
Lemma coherent_snapshot_cnf_wf__decide_exit_solver_setup :
  forall F n live original snap,
    coherent_snapshot F n live original snap ->
    cnf_wf n F.
Proof.
  intros F n live original snap Hcoherent.
  unfold coherent_snapshot in Hcoherent.
  destruct Hcoherent as
    [Hn [_ [_ [Hcells [_ Hsound]]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [_ Hrow_wf].
  unfold installed_clauses_sound, original_prefix_exact in Hsound.
  destruct Hsound as [[Hprefix _] _].
  assert (Hinstalled_wf :
    Forall (fun c => Forall (literal_wf n) c)
      (map dense_decode (snap_rows snap))).
  {
    apply Forall_forall.
    intros c Hc.
    apply in_map_iff in Hc.
    destruct Hc as [row [<- Hinrow]].
    apply Forall_forall with (x := row) in Hrow_wf; [|exact Hinrow].
    apply dense_decode_forall_wf__decide_exit_solver_setup.
    exact Hrow_wf.
  }
  unfold cnf_wf.
  split; [exact Hn|].
  rewrite <- (firstn_skipn (Z.to_nat original)
    (map dense_decode (snap_rows snap))) in Hinstalled_wf.
  apply Forall_app in Hinstalled_wf as [Hfirst _].
  rewrite Hprefix in Hfirst.
  exact Hfirst.
Qed.
Lemma processed_level_of_literal_length__decide_exit_solver_setup :
  forall n row a l d,
    Zlength row = n ->
    In l (dense_decode row) ->
    level_of a (literal_var l) = Some d ->
    processed_level a row n d.
Proof.
  intros n row a l d Hlength Hin Hlevel.
  assert (Hrange : 0 <= literal_var l < Zlength row).
  {
    split.
    - unfold dense_decode in Hin.
      pose proof
        (dense_decode_from_var_lower_bound
          row 0 l Hin).
      lia.
    - unfold dense_decode in Hin.
      pose proof
        (dense_decode_from_var_upper_bound__learning_row_and_scan
          row 0 l Hin).
      lia.
  }
  exists (literal_var l).
  split; [lia|].
  split.
  - destruct l as [x|x]; simpl in *.
    + unfold dense_decode in Hin.
      replace x with (0 + x) in Hin by lia.
      pose proof (proj2
        (dense_decode_from_pos_cell row 0 x Hrange) Hin).
      lia.
    + unfold dense_decode in Hin.
      replace x with (0 + x) in Hin by lia.
      pose proof (proj2
        (dense_decode_from_neg_cell row 0 x Hrange) Hin).
      lia.
  - exact Hlevel.
Qed.
Lemma snapshot_processed_level_nonneg__decide_exit_solver_setup :
  forall n snap ranks logical_dl row d,
    stable_search_facts n snap ranks logical_dl ->
    processed_level
      (cdcl_view_of_snapshot n snap ranks logical_dl) row n d ->
    0 <= d.
Proof.
  intros n snap ranks logical_dl row d Hstable Hprocessed.
  destruct Hprocessed as [x [Hx [_ Hlevel]]].
  unfold stable_search_facts in Hstable.
  destruct Hstable as [_ [Hclosed _]].
  unfold closed_levels in Hclosed.
  destruct Hclosed as [_ [Hbounds _]].
  pose proof Hlevel as Hlevel_view.
  change (snapshot_level n snap x = Some d) in Hlevel.
  unfold snapshot_level in Hlevel.
  destruct (snapshot_assignment n snap x) as [b|] eqn:Hassignment;
    [|discriminate].
  specialize (Hbounds x b d Hassignment Hlevel_view).
  lia.
Qed.
Lemma top_two_max1_minus1_empty_stable__decide_exit_solver_setup :
  forall n row snap ranks logical_dl max2,
    Zlength row = n ->
    stable_search_facts n snap ranks logical_dl ->
    clause_vars_assigned
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (dense_decode row) ->
    top_two_levels_exact
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      row n (-1) max2 ->
    dense_decode row = nil.
Proof.
  intros n row snap ranks logical_dl max2
    Hlength Hstable Hassigned Htop.
  destruct Htop as [[Hnone _]|[Hprocessed _]].
  - destruct (dense_decode row) as [|l tail] eqn:Hdecoded;
      [reflexivity|].
    exfalso.
    assert (Hin : In l (dense_decode row)).
    { rewrite Hdecoded. left. reflexivity. }
    destruct (Hassigned l (or_introl eq_refl))
      as [b [d [_ [Hlevel _]]]].
    apply (Hnone d).
    eapply processed_level_of_literal_length__decide_exit_solver_setup;
      eauto.
  - pose proof
      (snapshot_processed_level_nonneg__decide_exit_solver_setup
        n snap ranks logical_dl row (-1) Hstable Hprocessed).
    lia.
Qed.
Lemma publish_false_learned_clause_record__decide_exit_solver_setup :
  forall F n live original snap ranks logical_dl row,
    coherent_snapshot F n live original snap ->
    row_wf n row ->
    current_learning_exit_cert F
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (dense_decode row) ->
    coherent_snapshot F n (live + 1) original
      {| snap_values := snap_values snap;
         snap_reasons := snap_reasons snap;
         snap_levels := snap_levels snap;
         snap_rows := snap_rows snap ++ row :: nil;
         snap_states := snap_states snap ++ 1 :: nil;
         snap_true_counts := snap_true_counts snap ++ 0 :: nil;
         snap_unassigned := snap_unassigned snap ++ 0 :: nil |}.
Proof.
  intros F n live original snap ranks logical_dl row
    Hcoherent Hrow Hexit.
  destruct
    (publish_false_learned_clause__decide_exit_solver_setup
      F n live original snap ranks logical_dl row
      Hcoherent Hrow Hexit)
    as [installed [Hvalues [Hreasons [Hlevels [Hrows
      [Hstates [Htrue [Hunassigned Hinstalled]]]]]]]].
  destruct installed as [iv ir il irows istates itrue iunassigned].
  cbn in *.
  subst iv ir il irows istates itrue iunassigned.
  exact Hinstalled.
Qed.
Lemma int_ptr_array_publish_existing__decide_exit_solver_setup :
  forall x i count row_ptr rows row row_length,
    0 <= i < count ->
    Zlength rows = count ->
    Zlength row = row_length ->
    Znth i rows nil = row ->
    (x + i * sizeof(PTR)) # Ptr |-> row_ptr **
    IntArray.full row_ptr row_length row **
    IntPtrArray2.missing_i x count i row_ptr rows |--
    IntPtrArray2.full x count rows.
Proof.
  intros x i count row_ptr rows row row_length
    Hi Hrows Hrow Hlookup.
  subst row_length.
  replace (IntPtrArray2.full x count rows)
    with (IntPtrArray2.full x count (replace_Znth i row rows))
    by (rewrite <- Hlookup; rewrite replace_Znth_Znth by lia; reflexivity).
  apply (IntPtrArray2.missing_i_merge_to_full
    x i count row_ptr rows row Hi).
Qed.
Lemma dense_decode_from_nodup__decide_exit_solver_setup :
  forall row base, NoDup (dense_decode_from base row).
Proof.
  induction row as [|z row IH]; intro base.
  - simpl. constructor.
  - simpl.
    destruct ((z =? 1)%Z) eqn:Hz1.
    + constructor.
      * intro Hin.
        pose proof (dense_decode_from_var_lower_bound row (base + 1)
          (Pos base) Hin).
        simpl in H. lia.
      * apply IH.
    + destruct ((z =? -1)%Z) eqn:Hzm.
      * constructor.
        -- intro Hin.
           pose proof (dense_decode_from_var_lower_bound row (base + 1)
             (Neg base) Hin).
           simpl in H. lia.
        -- apply IH.
      * apply IH.
Qed.
Lemma dense_decode_nodup__decide_exit_solver_setup :
  forall row, NoDup (dense_decode row).
Proof.
  intro row.
  apply dense_decode_from_nodup__decide_exit_solver_setup.
Qed.
Lemma processed_level_nonneg__decide_exit_solver_setup :
  forall n row a d,
    row_wf n row ->
    clause_vars_assigned a (dense_decode row) ->
    processed_level a row n d ->
    0 <= d.
Proof.
  intros n row a d Hrow Hassigned Hprocessed.
  destruct Hprocessed as [x [Hx [Hcell Hlevel]]].
  pose proof (row_wf_cell_domain n row x Hrow Hx) as Hdomain.
  destruct Hdomain as [Hneg|[Hzero|Hpos]]; [|contradiction|].
  - pose proof (proj1 (dense_decode_neg n row x Hrow Hx) Hneg) as Hin.
    destruct (Hassigned (Neg x) Hin) as [b [d' [_ [Hd' Hnonneg]]]].
    simpl in Hd'. rewrite Hlevel in Hd'. inversion Hd'. lia.
  - pose proof (proj1 (dense_decode_pos n row x Hrow Hx) Hpos) as Hin.
    destruct (Hassigned (Pos x) Hin) as [b [d' [_ [Hd' Hnonneg]]]].
    simpl in Hd'. rewrite Hlevel in Hd'. inversion Hd'. lia.
Qed.
Lemma installing_clause_rep_row_wf__decide_exit_solver_setup :
  forall F a n cap row learned old_live new_live,
    installing_clause F a n cap row learned old_live new_live ->
    row_wf n row.
Proof.
  intros F a n cap row learned old_live new_live Hp.
  unfold installing_clause in Hp.
  tauto.
Qed.
Lemma processed_level_clause_level_iff__decide_exit_solver_setup :
  forall n row a d,
    row_wf n row ->
    Zlength row = n ->
    (processed_level a row n d <->
     clause_level_occurs a (dense_decode row) d).
Proof.
  intros n row a d Hrow Hlength.
  split.
  - intros [x [Hx [Hcell Hlevel]]].
    pose proof (row_wf_cell_domain n row x Hrow Hx) as Hdomain.
    destruct Hdomain as [Hneg|[Hzero|Hpos]].
    + exists (Neg x).
      split.
      * apply (proj1 (dense_decode_neg n row x Hrow Hx)).
        exact Hneg.
      * exact Hlevel.
    + contradiction.
    + exists (Pos x).
      split.
      * apply (proj1 (dense_decode_pos n row x Hrow Hx)).
        exact Hpos.
      * exact Hlevel.
  - intros [l [Hin Hlevel]].
    eapply processed_level_of_literal_length__decide_exit_solver_setup;
      eauto.
Qed.
Lemma clause_level_closed_bound__decide_exit_solver_setup :
  forall a L d,
    closed_levels a ->
    clause_vars_assigned a L ->
    clause_level_occurs a L d ->
    0 <= d <= current_level a.
Proof.
  intros a L d Hclosed Hassigned [l [Hin Hlevel]].
  destruct (Hassigned l Hin) as [b [d' [Hassignment [Hlevel' Hd']]]].
  rewrite Hlevel in Hlevel'.
  inversion Hlevel'; subst d'.
  destruct Hclosed as [_ [Hbounds _]].
  apply (Hbounds (literal_var l) b d Hassignment Hlevel).
Qed.
Lemma literal_eq_dec__decide_exit_solver_setup :
  forall l1 l2 : literal, {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality; apply Z.eq_dec.
Qed.
Lemma restrict_false_or_none__decide_exit_solver_setup :
  forall a L l d k,
    clause_false (assignment a) L ->
    clause_vars_assigned a L ->
    In l L ->
    level_of a (literal_var l) = Some d ->
    (d <= k ->
      eval_partial_literal (restrict_to_level a k) l = Some false) /\
    (k < d ->
      eval_partial_literal (restrict_to_level a k) l = None).
Proof.
  intros a L l d k Hfalse Hassigned Hin Hlevel.
  destruct (Hassigned l Hin) as [b [d' [Hassignment [Hlevel' _]]]].
  rewrite Hlevel in Hlevel'.
  inversion Hlevel'; subst d'.
  specialize (Hfalse l Hin).
  destruct l as [x|x]; cbn in *.
  all: unfold eval_partial_literal in Hfalse; cbn in Hfalse;
    rewrite Hassignment in Hfalse.
  all: split; intro Hdk;
    unfold eval_partial_literal, restrict_to_level; cbn;
    rewrite Hassignment, Hlevel.
  - assert (Hleb : (d <=? k)%Z = true) by (apply Z.leb_le; lia).
    rewrite Hleb. exact Hfalse.
  - assert (Hleb : (d <=? k)%Z = false) by (apply Z.leb_gt; lia).
    rewrite Hleb. reflexivity.
  - assert (Hleb : (d <=? k)%Z = true) by (apply Z.leb_le; lia).
    rewrite Hleb. exact Hfalse.
  - assert (Hleb : (d <=? k)%Z = false) by (apply Z.leb_gt; lia).
    rewrite Hleb. reflexivity.
Qed.
Lemma clause_unassigned_count_nonneg__decide_exit_solver_setup :
  forall sigma L, 0 <= clause_unassigned_count sigma L.
Proof.
  intros sigma L.
  induction L as [|l L IH]; [reflexivity|].
  simpl.
  destruct (eval_partial_literal sigma l) as [b|] eqn:Heval.
  - exact IH.
  - change (0 <= 1 + clause_unassigned_count sigma L).
    lia.
Qed.
Lemma clause_unassigned_count_ge_one__decide_exit_solver_setup :
  forall sigma L u,
    In u L ->
    eval_partial_literal sigma u = None ->
    1 <= clause_unassigned_count sigma L.
Proof.
  intros sigma L.
  induction L as [|l L IH]; intros u Hin Hnone.
  - contradiction.
  - simpl in Hin.
    destruct Hin as [<-|Hin].
    + simpl. rewrite Hnone.
      pose proof
        (clause_unassigned_count_nonneg__decide_exit_solver_setup
          sigma L) as Hcount_nonneg.
      change (1 + 0 <= 1 + clause_unassigned_count sigma L).
      apply Z.add_le_mono_l.
      exact Hcount_nonneg.
    + simpl.
      specialize (IH u Hin Hnone).
      destruct (eval_partial_literal sigma l) as [b|] eqn:Heval.
      * exact IH.
      * change (1 <= 1 + clause_unassigned_count sigma L).
        lia.
Qed.
Lemma clause_counts_unique_none__decide_exit_solver_setup :
  forall sigma L u,
    NoDup L ->
    In u L ->
    eval_partial_literal sigma u = None ->
    (forall l, In l L -> l <> u ->
      eval_partial_literal sigma l = Some false) ->
    clause_true_count sigma L = 0 /\
    clause_unassigned_count sigma L = 1.
Proof.
  intros sigma L.
  induction L as [|l L IH]; intros u Hnodup Hin Hnone Hother.
  - contradiction.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
    destruct
      (literal_eq_dec__decide_exit_solver_setup l u) as [Heq|Hneq].
    + subst l.
      assert (Htailfalse : clause_false sigma L).
      {
        intros l' Hin'.
        apply Hother.
        - right. exact Hin'.
        - intro Heq'.
          subst l'.
          contradiction.
      }
      pose proof
        (clause_false_counts__learning_row_and_scan
          sigma L Htailfalse) as [Ht Hu].
      simpl. rewrite Hnone, Ht, Hu.
      split; lia.
    + assert (Hin_tail : In u L).
      { destruct Hin as [Heq|Hin]; [contradiction|exact Hin]. }
      assert (Hother_tail :
        forall l', In l' L -> l' <> u ->
          eval_partial_literal sigma l' = Some false).
      {
        intros l' Hin' Hneq'.
        apply Hother; [right; exact Hin'|exact Hneq'].
      }
      specialize (IH u Hnodup_tail Hin_tail Hnone Hother_tail)
        as [Ht Hu].
      assert (Hlfalse : eval_partial_literal sigma l = Some false).
      { apply Hother; [left; reflexivity|exact Hneq]. }
      simpl. rewrite Hlfalse, Ht, Hu.
      split; reflexivity.
Qed.
Lemma clause_unassigned_count_ge_two__decide_exit_solver_setup :
  forall sigma L u v,
    NoDup L ->
    In u L ->
    In v L ->
    u <> v ->
    eval_partial_literal sigma u = None ->
    eval_partial_literal sigma v = None ->
    2 <= clause_unassigned_count sigma L.
Proof.
  intros sigma L.
  induction L as [|l L IH];
    intros u v Hnodup Hinu Hinv Huv Hnoneu Hnonev.
  - contradiction.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
    destruct
      (literal_eq_dec__decide_exit_solver_setup l u) as [Hlu|Hlu].
    + subst l.
      assert (Hinv_tail : In v L).
      {
        destruct Hinv as [Hvu|Hinv].
        - exfalso. apply Huv. exact Hvu.
        - exact Hinv.
      }
      simpl. rewrite Hnoneu.
      pose proof
        (clause_unassigned_count_ge_one__decide_exit_solver_setup
          sigma L v Hinv_tail Hnonev) as Hcount.
      change (1 + 1 <= 1 + clause_unassigned_count sigma L).
      apply Z.add_le_mono_l.
      exact Hcount.
    + destruct
        (literal_eq_dec__decide_exit_solver_setup l v) as [Hlv|Hlv].
      * subst l.
        assert (Hinu_tail : In u L).
        {
          destruct Hinu as [Hvu|Hinu].
          - exfalso. apply Huv. symmetry. exact Hvu.
          - exact Hinu.
        }
        simpl. rewrite Hnonev.
        pose proof
          (clause_unassigned_count_ge_one__decide_exit_solver_setup
            sigma L u Hinu_tail Hnoneu) as Hcount.
        change (1 + 1 <= 1 + clause_unassigned_count sigma L).
        apply Z.add_le_mono_l.
        exact Hcount.
      * assert (Hinu_tail : In u L).
        { destruct Hinu as [H|H]; [contradiction|exact H]. }
        assert (Hinv_tail : In v L).
        { destruct Hinv as [H|H]; [contradiction|exact H]. }
        specialize
          (IH u v Hnodup_tail Hinu_tail Hinv_tail
            Huv Hnoneu Hnonev).
        simpl.
        destruct (eval_partial_literal sigma l) as [b|] eqn:Heval.
        -- exact IH.
        -- change (2 <= 1 + clause_unassigned_count sigma L).
           lia.
Qed.
Lemma unique_current_literal__decide_exit_solver_setup :
  forall n row a,
    row_wf n row ->
    closed_levels a ->
    0 < current_level a ->
    clause_vars_assigned a (dense_decode row) ->
    current_level_support a (dense_decode row) ->
    no_current_level_propagated_literal a (dense_decode row) ->
    exists! l,
      In l (dense_decode row) /\ current_level_literal a l.
Proof.
  intros n row a Hrow Hclosed Hcurrent Hassigned
    [l0 [Hin0 Hlevel0]] Hnode.
  exists l0.
  split; [split; assumption|].
  intros l [Hin Hlevel].
  unfold current_level_literal in Hlevel0, Hlevel.
  assert (Hdecision0 :
    decision_at a (literal_var l0) (current_level a)).
  {
    unfold decision_at.
    destruct (Hassigned l0 Hin0)
      as [b [d [Hassignment [Hassigned_level _]]]].
    rewrite Hlevel0 in Hassigned_level.
    inversion Hassigned_level; subst d.
    split; [exists b; exact Hassignment|].
    split; [exact Hlevel0|].
    apply Hnode; [exact Hin0|exact Hlevel0].
  }
  assert (Hdecision :
    decision_at a (literal_var l) (current_level a)).
  {
    unfold decision_at.
    destruct (Hassigned l Hin)
      as [b [d [Hassignment [Hassigned_level _]]]].
    rewrite Hlevel in Hassigned_level.
    inversion Hassigned_level; subst d.
    split; [exists b; exact Hassignment|].
    split; [exact Hlevel|].
    apply Hnode; [exact Hin|exact Hlevel].
  }
  destruct Hclosed as [_ [_ [_ Hunique]]].
  destruct (Hunique (current_level a) ltac:(lia))
    as [x [Hdecision_x Hunique_x]].
  pose proof (Hunique_x (literal_var l0) Hdecision0) as Hvar0.
  pose proof (Hunique_x (literal_var l) Hdecision) as Hvar.
  eapply dense_decode_unique_var__learning_row_and_scan;
    eauto.
  congruence.
Qed.
Lemma top_two_profile_zero__decide_exit_solver_setup :
  forall F n row a max1,
    row_wf n row ->
    Zlength row = n ->
    closed_levels a ->
    0 < current_level a ->
    clause_vars_assigned a (dense_decode row) ->
    current_learning_exit_cert F a (dense_decode row) ->
    top_two_levels_exact a row n max1 (-1) ->
    max1 <> -1 ->
    learned_clause_sound F a (dense_decode row) /\
    no_current_level_propagated_literal a (dense_decode row) /\
    backjump_target_profile a 0 (dense_decode row).
Proof.
  intros F n row a max1 Hrow Hlength Hclosed Hcurrent
    Hassigned Hexit Htop Hmax1.
  unfold current_learning_exit_cert in Hexit.
  destruct Hexit as [Hsound [Hempty|[Hsupport Hnode]]].
  - assert (Hno_occurs :
      forall d, ~ clause_level_occurs a (dense_decode row) d).
    {
      intros d [l [Hin _]].
      rewrite Hempty in Hin.
      contradiction.
    }
    destruct Htop as [[_ [Hminus _]]|[Hprocessed _]].
    + contradiction.
    + exfalso. apply
        (Hno_occurs max1
          (proj1
            (processed_level_clause_level_iff__decide_exit_solver_setup
              n row a max1 Hrow Hlength) Hprocessed)).
  - assert (Hprocessed_current :
      processed_level a row n (current_level a)).
    {
      destruct Hsupport as [l [Hin Hlevel]].
      apply
        (proj2
          (processed_level_clause_level_iff__decide_exit_solver_setup
            n row a (current_level a) Hrow Hlength)).
      exists l.
      split; [exact Hin|exact Hlevel].
    }
    destruct Htop as [[Hnone _]|[Hprocessed_max [Hgreat Hsecond]]].
    + exfalso. exact (Hnone (current_level a) Hprocessed_current).
    + destruct Hsecond as [[_ Hall]|[Hprocessed_minus [Hlt _]]].
      * assert (Hmax1_current : max1 = current_level a).
        {
          assert (Hmax1_bound : max1 <= current_level a).
          {
            pose proof
              (proj1
                (processed_level_clause_level_iff__decide_exit_solver_setup
                  n row a max1 Hrow Hlength) Hprocessed_max) as Hoccurs.
            pose proof
              (clause_level_closed_bound__decide_exit_solver_setup
                a (dense_decode row) max1 Hclosed Hassigned Hoccurs).
            lia.
          }
          pose proof (Hgreat (current_level a) Hprocessed_current).
          lia.
        }
        split; [exact Hsound|].
        split; [exact Hnode|].
        unfold backjump_target_profile.
        split; [exact Hassigned|].
        split; [exact Hsupport|].
        split.
        -- intros d Hoccurs.
           pose proof
             (clause_level_closed_bound__decide_exit_solver_setup
               a (dense_decode row) d Hclosed Hassigned Hoccurs).
           lia.
        -- left.
           split; [reflexivity|].
           intros d Hoccurs.
           apply
             (proj2
               (processed_level_clause_level_iff__decide_exit_solver_setup
                 n row a d Hrow Hlength)) in Hoccurs.
           specialize (Hall d Hoccurs).
           lia.
      * pose proof
          (processed_level_nonneg__decide_exit_solver_setup
            n row a (-1) Hrow Hassigned Hprocessed_minus).
        lia.
Qed.
Lemma top_two_profile_nonzero__decide_exit_solver_setup :
  forall F n row a max1 max2,
    row_wf n row ->
    Zlength row = n ->
    closed_levels a ->
    0 < current_level a ->
    clause_vars_assigned a (dense_decode row) ->
    current_learning_exit_cert F a (dense_decode row) ->
    top_two_levels_exact a row n max1 max2 ->
    max1 <> -1 ->
    max2 <> -1 ->
    learned_clause_sound F a (dense_decode row) /\
    no_current_level_propagated_literal a (dense_decode row) /\
    backjump_target_profile a max2 (dense_decode row).
Proof.
  intros F n row a max1 max2 Hrow Hlength Hclosed Hcurrent
    Hassigned Hexit Htop Hmax1 Hmax2.
  unfold current_learning_exit_cert in Hexit.
  destruct Hexit as [Hsound [Hempty|[Hsupport Hnode]]].
  - assert (Hno_occurs :
      forall d, ~ clause_level_occurs a (dense_decode row) d).
    {
      intros d [l [Hin _]].
      rewrite Hempty in Hin.
      contradiction.
    }
    destruct Htop as [[_ [Hminus _]]|[Hprocessed _]].
    + contradiction.
    + exfalso. apply
        (Hno_occurs max1
          (proj1
            (processed_level_clause_level_iff__decide_exit_solver_setup
              n row a max1 Hrow Hlength) Hprocessed)).
  - assert (Hprocessed_current :
      processed_level a row n (current_level a)).
    {
      destruct Hsupport as [l [Hin Hlevel]].
      apply
        (proj2
          (processed_level_clause_level_iff__decide_exit_solver_setup
            n row a (current_level a) Hrow Hlength)).
      exists l.
      split; [exact Hin|exact Hlevel].
    }
    destruct Htop as [[Hnone _]|[Hprocessed_max [Hgreat Hsecond]]].
    + exfalso. exact (Hnone (current_level a) Hprocessed_current).
    + destruct Hsecond as [[Hminus _]|
        [Hprocessed_second [Hsecond_lt Hgreat_second]]].
      * contradiction.
      * assert (Hmax1_current : max1 = current_level a).
        {
          assert (Hmax1_bound : max1 <= current_level a).
          {
            pose proof
              (proj1
                (processed_level_clause_level_iff__decide_exit_solver_setup
                  n row a max1 Hrow Hlength) Hprocessed_max) as Hoccurs.
            pose proof
              (clause_level_closed_bound__decide_exit_solver_setup
                a (dense_decode row) max1 Hclosed Hassigned Hoccurs).
            lia.
          }
          pose proof (Hgreat (current_level a) Hprocessed_current).
          lia.
        }
        assert (Hoccurs_second :
          clause_level_occurs a (dense_decode row) max2).
        {
          apply
            (proj1
              (processed_level_clause_level_iff__decide_exit_solver_setup
                n row a max2 Hrow Hlength)).
          exact Hprocessed_second.
        }
        pose proof
          (clause_level_closed_bound__decide_exit_solver_setup
            a (dense_decode row) max2 Hclosed Hassigned Hoccurs_second)
          as Hsecond_bounds.
        split; [exact Hsound|].
        split; [exact Hnode|].
        unfold backjump_target_profile.
        split; [exact Hassigned|].
        split; [exact Hsupport|].
        split.
        -- intros d Hoccurs.
           pose proof
             (clause_level_closed_bound__decide_exit_solver_setup
               a (dense_decode row) d Hclosed Hassigned Hoccurs).
           lia.
        -- right.
           split; [lia|].
           split; [exact Hoccurs_second|].
           intros d Hoccurs Hd.
           apply
             (proj2
               (processed_level_clause_level_iff__decide_exit_solver_setup
                 n row a d Hrow Hlength)) in Hoccurs.
           apply Hgreat_second; [exact Hoccurs|lia].
Qed.
Lemma backjump_profile_cert__decide_exit_solver_setup :
  forall F n row a target,
    row_wf n row ->
    closed_levels a ->
    0 < current_level a ->
    learned_clause_sound F a (dense_decode row) ->
    no_current_level_propagated_literal a (dense_decode row) ->
    backjump_target_profile a target (dense_decode row) ->
    learned_backjump_cert F a target (dense_decode row).
Proof.
  intros F n row a target Hrow Hclosed Hcurrent
    Hsound Hnode Hprofile.
  pose proof Hsound as Hsound_keep.
  destruct Hsound as [Hentails Hfalse].
  unfold backjump_target_profile in Hprofile.
  destruct Hprofile as
    [Hassigned [Hsupport [Hall_levels [Hzero|Hpositive]]]].
  all: pose proof
    (unique_current_literal__decide_exit_solver_setup
      n row a Hrow Hclosed Hcurrent Hassigned Hsupport Hnode)
    as Hunique_current.
  all: destruct Hunique_current as
    [u [[Hinu Hcurrent_u] Hunique_u]].
  all: unfold current_level_literal in Hcurrent_u.
  all: pose proof
    (dense_decode_nodup__decide_exit_solver_setup row) as Hnodup.
  - destruct Hzero as [Htarget Hall_current].
    subst target.
    assert (Hunone :
      eval_partial_literal (restrict_to_level a 0) u = None).
    {
      apply
        (proj2
          (restrict_false_or_none__decide_exit_solver_setup
            a (dense_decode row) u (current_level a) 0
            Hfalse Hassigned Hinu Hcurrent_u)).
      lia.
    }
    assert (Hothers_false :
      forall l, In l (dense_decode row) -> l <> u ->
        eval_partial_literal (restrict_to_level a 0) l = Some false).
    {
      intros l Hin Hneq.
      destruct (Hassigned l Hin)
        as [b [d [Hassignment [Hlevel Hd]]]].
      assert (Hoccurs :
        clause_level_occurs a (dense_decode row) d).
      { exists l. split; assumption. }
      specialize (Hall_current d Hoccurs).
      exfalso.
      apply Hneq.
      symmetry.
      apply Hunique_u.
      split; [exact Hin|].
      unfold current_level_literal.
      rewrite Hlevel, Hall_current.
      reflexivity.
    }
    pose proof
      (clause_counts_unique_none__decide_exit_solver_setup
        (restrict_to_level a 0) (dense_decode row) u
        Hnodup Hinu Hunone Hothers_false)
      as Hasserting.
    assert (Hfrontier :
      learned_frontier_safe_after a 0 (dense_decode row)).
    {
      unfold learned_frontier_safe_after.
      split.
      - intros k Hk. exfalso. lia.
      - left. reflexivity.
    }
    unfold learned_backjump_cert.
    split; [exact Hsound_keep|].
    split.
    { intro Hnil. rewrite Hnil in Hinu. contradiction. }
    split; [lia|].
    split; [exact Hasserting|exact Hfrontier].
  - destruct Hpositive as
      [Htarget_bounds [Htarget_occurs Hgreatest]].
    destruct Htarget_occurs as [t [Hint Hlevelt]].
    assert (Hunone :
      eval_partial_literal (restrict_to_level a target) u = None).
    {
      apply
        (proj2
          (restrict_false_or_none__decide_exit_solver_setup
            a (dense_decode row) u (current_level a) target
            Hfalse Hassigned Hinu Hcurrent_u)).
      lia.
    }
    assert (Hothers_false :
      forall l, In l (dense_decode row) -> l <> u ->
        eval_partial_literal (restrict_to_level a target) l =
          Some false).
    {
      intros l Hin Hneq.
      destruct (Hassigned l Hin)
        as [b [d [Hassignment [Hlevel Hd]]]].
      assert (Hoccurs :
        clause_level_occurs a (dense_decode row) d).
      { exists l. split; assumption. }
      assert (Hd_not_current : d <> current_level a).
      {
        intro Heq.
        apply Hneq.
        symmetry.
        apply Hunique_u.
        split; [exact Hin|].
        unfold current_level_literal.
        rewrite Hlevel, Heq.
        reflexivity.
      }
      assert (Hd_lt_current : d < current_level a).
      { specialize (Hall_levels d Hoccurs). lia. }
      assert (Hd_target : d <= target).
      { apply Hgreatest; assumption. }
      apply
        (proj1
          (restrict_false_or_none__decide_exit_solver_setup
            a (dense_decode row) l d target
            Hfalse Hassigned Hin Hlevel)).
      exact Hd_target.
    }
    pose proof
      (clause_counts_unique_none__decide_exit_solver_setup
        (restrict_to_level a target) (dense_decode row) u
        Hnodup Hinu Hunone Hothers_false)
      as Hasserting.
    assert (Ht_ne_u : t <> u).
    {
      intro Heq.
      subst t.
      rewrite Hcurrent_u in Hlevelt.
      inversion Hlevelt.
      lia.
    }
    assert (Hfrontier :
      learned_frontier_safe_after a target (dense_decode row)).
    {
      unfold learned_frontier_safe_after.
      destruct (Z.eq_dec target 0) as [Htarget0|Htarget0].
      - subst target.
        split.
        + intros k Hk. exfalso. lia.
        + left. reflexivity.
      - split.
        + intros k Hk Hactive.
          destruct Hactive as [_ Hunassigned_le].
          assert (Hunone_k :
            eval_partial_literal (restrict_to_level a k) u = None).
          {
            apply
              (proj2
                (restrict_false_or_none__decide_exit_solver_setup
                  a (dense_decode row) u (current_level a) k
                  Hfalse Hassigned Hinu Hcurrent_u)).
            lia.
          }
          assert (Htnone_k :
            eval_partial_literal (restrict_to_level a k) t = None).
          {
            apply
              (proj2
                (restrict_false_or_none__decide_exit_solver_setup
                  a (dense_decode row) t target k
                  Hfalse Hassigned Hint Hlevelt)).
            lia.
          }
          pose proof
            (clause_unassigned_count_ge_two__decide_exit_solver_setup
              (restrict_to_level a k) (dense_decode row) u t
              Hnodup Hinu Hint
              (fun Heq => Ht_ne_u (eq_sym Heq)) Hunone_k Htnone_k).
          lia.
        + right.
          exists t.
          split; [exact Hint|].
          unfold literal_false_at_level.
          split; [|exact Hlevelt].
          apply
            (proj1
              (restrict_false_or_none__decide_exit_solver_setup
                a (dense_decode row) t target target
                Hfalse Hassigned Hint Hlevelt)).
          lia.
    }
    unfold learned_backjump_cert.
    split; [exact Hsound_keep|].
    split.
    { intro Hnil. rewrite Hnil in Hinu. contradiction. }
    split; [exact Htarget_bounds|].
    split; [exact Hasserting|exact Hfrontier].
Qed.
Lemma literal_var_count_unique_one__decide_exit_solver_setup :
  forall c x,
    NoDup c ->
    (forall l1 l2,
      In l1 c -> In l2 c ->
      literal_var l1 = literal_var l2 -> l1 = l2) ->
    (exists l, In l c /\ literal_var l = x) ->
    literal_var_count x c = 1.
Proof.
  intros c.
  induction c as [|h c IH]; intros x Hnodup Hinjective Hexists.
  - destruct Hexists as [l [Hin _]]. contradiction.
  - inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
    destruct (Z.eq_dec (literal_var h) x) as [Hhead|Hhead].
    + assert (Habsent : forall l, In l c -> literal_var l <> x).
      {
        intros l Hin Hlx.
        assert (Hl_eq : l = h).
        {
          apply Hinjective; [right; exact Hin|left; reflexivity|].
          lia.
        }
        subst l. contradiction.
      }
      pose proof
        (literal_counts_no_var__bcp_unit_to_assignment x true c Habsent)
        as [Htail _].
      unfold literal_var_count; fold literal_var_count.
      destruct (literal_var h =? x)%Z eqn:Heq.
      * lia.
      * apply Z.eqb_neq in Heq. contradiction.
    + assert (Hexists_tail : exists l, In l c /\ literal_var l = x).
      {
        destruct Hexists as [l [[Hl|Hl] Hvar]].
        - subst l. contradiction.
        - exists l. split; assumption.
      }
      assert (Hinjective_tail : forall l1 l2,
        In l1 c -> In l2 c ->
        literal_var l1 = literal_var l2 -> l1 = l2).
      {
        intros l1 l2 Hin1 Hin2 Hvar.
        apply Hinjective; [right|right|]; assumption.
      }
      specialize (IH x Hnodup_tail Hinjective_tail Hexists_tail).
      unfold literal_var_count; fold literal_var_count.
      destruct (literal_var h =? x)%Z eqn:Heq.
      * apply Z.eqb_eq in Heq. contradiction.
      * exact IH.
Qed.
Lemma eval_partial_literal_other__decide_exit_solver_setup :
  forall sigma1 sigma2 x l,
    (forall y, y <> x -> sigma2 y = sigma1 y) ->
    literal_var l <> x ->
    eval_partial_literal sigma2 l = eval_partial_literal sigma1 l.
Proof.
  intros sigma1 sigma2 x [y|y] Hsame Hneq;
    unfold eval_partial_literal; simpl in *;
    rewrite Hsame by exact Hneq; reflexivity.
Qed.
Lemma eval_false_var_not_none__decide_exit_solver_setup :
  forall sigma x l,
    sigma x = None ->
    eval_partial_literal sigma l = Some false ->
    literal_var l <> x.
Proof.
  intros sigma x l Hnone Hfalse Heq.
  assert (Hnone_l : sigma (literal_var l) = None).
  { rewrite Heq. exact Hnone. }
  unfold eval_partial_literal in Hfalse.
  rewrite Hnone_l in Hfalse.
  discriminate.
Qed.
Lemma decision_extension_no_conflict__decide_exit_solver_setup :
  forall old new x d reason,
    assigns_one old new x true d reason ->
    no_conflict old ->
    no_unit old ->
    (forall c, In c (installed_clauses old) ->
      NoDup c /\
      (forall l1 l2,
        In l1 c -> In l2 c ->
        literal_var l1 = literal_var l2 -> l1 = l2)) ->
    no_conflict new.
Proof.
  intros old new x d reason Hassigns Hno_conflict Hno_unit Hunique.
  pose proof Hassigns as Hassigns_fields.
  unfold assigns_one in Hassigns_fields.
  destruct Hassigns_fields as
    [Hold_none [Hnew_x [_ [_ [_ [Hother Hinstalled]]]]]].
  pose proof
    (assigns_one_assignment_update__bcp_assignment_summary_a
      old new x true d reason Hassigns) as Hassignment_update.
  unfold no_conflict.
  intros c Hc_new Hfalse_new.
  rewrite Hinstalled in Hc_new.
  destruct (clause_var_occurs_dec c x)
    as [Hoccurs|Habsent].
  - destruct (Hunique c Hc_new) as [Hnodup Hinjective].
    pose proof
      (literal_var_count_unique_one__decide_exit_solver_setup
        c x Hnodup Hinjective Hoccurs) as Hvar_count.
    pose proof
      (clause_counts_assign (assignment old) x true c Hold_none)
      as [Hunassigned_update Htrue_update].
    rewrite <- Hassignment_update in Hunassigned_update, Htrue_update.
    pose proof
      (clause_false_counts__learning_row_and_scan
        (assignment new) c Hfalse_new) as [Htrue_new Hunassigned_new].
    pose proof (clause_true_count_nonnegative_base__bcp_unit_to_assignment
      (assignment old) c) as Htrue_old_nonneg.
    pose proof (literal_true_at_count_nonneg x true c) as Hliteral_nonneg.
    exfalso.
    apply (Hno_unit c Hc_new).
    unfold clause_unit.
    split; lia.
  - apply (Hno_conflict c Hc_new).
    unfold clause_false.
    intros l Hin.
    specialize (Hfalse_new l Hin).
    assert (Hl_other : literal_var l <> x).
    {
      intro Heq.
      apply Habsent.
      exists l. split; assumption.
    }
    rewrite
      (eval_partial_literal_other__decide_exit_solver_setup
        (assignment old) (assignment new) x l
        (fun y Hy => proj1 (Hother y Hy)) Hl_other)
      in Hfalse_new.
    exact Hfalse_new.
Qed.
Lemma assigns_one_reason_valid_other__decide_exit_solver_setup :
  forall old new x b d reason y i,
    assigns_one old new x b d reason ->
    y <> x ->
    reason_valid old y i ->
    reason_valid new y i.
Proof.
  intros old new x b d reason y i Hassigns Hyx Hvalid.
  unfold assigns_one in Hassigns.
  destruct Hassigns as
    [Hold_none [_ [_ [_ [_ [Hother Hinstalled]]]]]].
  unfold reason_valid in *.
  destruct Hvalid as
    [vy [dy [ry [c [Hassignment_y [Hlevel_y [Hrank_y
      [Hclause [Hsatisfying Hothers]]]]]]]]].
  destruct (Hother y Hyx) as
    [Hassignment_y' [Hlevel_y' [Hreason_y' Hrank_y']]].
  exists vy, dy, ry, c.
  split.
  - rewrite Hassignment_y'. exact Hassignment_y.
  - split.
    + rewrite Hlevel_y'. exact Hlevel_y.
    + split.
      * rewrite Hrank_y'. exact Hrank_y.
      * split.
        -- rewrite Hinstalled. exact Hclause.
        -- split.
          ++ exact Hsatisfying.
          ++ intros lit Hin Hly.
             specialize (Hothers lit Hin Hly).
             destruct Hothers as
               [Heval [dl [rl [Hlevel_l [Hrank_l [Hdl Hrl]]]]]].
             assert (Hlx : literal_var lit <> x).
             {
               eapply eval_false_var_not_none__decide_exit_solver_setup;
                 eauto.
             }
             destruct (Hother (literal_var lit) Hlx) as
               [_ [Hlevel_l' [_ Hrank_l']]].
             split.
             { rewrite
                 (eval_partial_literal_other__decide_exit_solver_setup
                   (assignment old) (assignment new) x lit
                   (fun z Hz => proj1 (Hother z Hz)) Hlx).
               exact Heval. }
             { exists dl, rl.
               repeat split.
               - rewrite Hlevel_l'. exact Hlevel_l.
               - rewrite Hrank_l'. exact Hrank_l.
               - exact Hdl.
               - exact Hrl. }
Qed.
Lemma assigns_one_reason_dependency_other__decide_exit_solver_setup :
  forall old new x b d reason y z,
    assigns_one old new x b d reason ->
    y <> x ->
    reason_dependency old y z ->
    reason_dependency new y z.
Proof.
  intros old new x b d reason y z Hassigns Hyx Hdependency.
  unfold assigns_one in Hassigns.
  destruct Hassigns as
    [Hold_none [_ [_ [_ [_ [Hother Hinstalled]]]]]].
  unfold reason_dependency in *.
  destruct Hdependency as
    [i [c [l [Hreason [Hclause [Hin [Hvar [Hzy Heval]]]]]]]].
  assert (Hlx : literal_var l <> x).
  {
    eapply eval_false_var_not_none__decide_exit_solver_setup;
      eauto.
  }
  exists i, c, l.
  repeat split.
  - rewrite (proj1 (proj2 (proj2 (Hother y Hyx)))).
    exact Hreason.
  - rewrite Hinstalled. exact Hclause.
  - exact Hin.
  - exact Hvar.
  - exact Hzy.
  - rewrite
      (eval_partial_literal_other__decide_exit_solver_setup
        (assignment old) (assignment new) x l
        (fun q Hq => proj1 (Hother q Hq)) Hlx).
    exact Heval.
Qed.
Lemma assigns_one_same_level_predecessor_other__decide_exit_solver_setup :
  forall old new x b d reason y z dl,
    assigns_one old new x b d reason ->
    y <> x ->
    same_level_predecessor old y z dl ->
    same_level_predecessor new y z dl.
Proof.
  intros old new x b d reason y z dl Hassigns Hyx Hpredecessor.
  pose proof Hassigns as Hfields.
  unfold assigns_one in Hfields.
  destruct Hfields as
    [Hold_none [_ [_ [_ [_ [Hother _]]]]]].
  unfold same_level_predecessor in *.
  destruct Hpredecessor as
    [Hdependency [Hlevel_y [Hlevel_z
      [ry [rz [Hrank_y [Hrank_z Hrank_lt]]]]]]].
  unfold reason_dependency in Hdependency.
  destruct Hdependency as
    [i [c [l [Hreason [Hclause [Hin [Hvar [Hzy Heval]]]]]]]].
  assert (Hlx : literal_var l <> x).
  {
    eapply eval_false_var_not_none__decide_exit_solver_setup;
      eauto.
  }
  assert (Hzx : z <> x) by (rewrite <- Hvar; exact Hlx).
  assert (Hdependency_old : reason_dependency old y z).
  {
    exists i, c, l.
    repeat split; assumption.
  }
  split.
  - eapply assigns_one_reason_dependency_other__decide_exit_solver_setup;
      eauto.
  - split.
    + rewrite (proj1 (proj2 (Hother y Hyx))). exact Hlevel_y.
    + split.
      * rewrite (proj1 (proj2 (Hother z Hzx))). exact Hlevel_z.
      * exists ry, rz.
        repeat split.
        -- rewrite (proj2 (proj2 (proj2 (Hother y Hyx)))).
           exact Hrank_y.
        -- rewrite (proj2 (proj2 (proj2 (Hother z Hzx)))).
           exact Hrank_z.
        -- exact Hrank_lt.
Qed.
Lemma assigns_one_grounded_decision__decide_exit_solver_setup :
  forall old new x b d,
    assigns_one old new x b d (-1) ->
    grounded_at old ->
    0 < d ->
    grounded_at new.
Proof.
  intros old new x b d Hassigns Hgrounded Hd.
  pose proof Hassigns as Hfields.
  unfold assigns_one in Hfields.
  destruct Hfields as
    [Hold_none [Hnew_x [Hnew_level [Hnew_reason
      [[rx [Hnew_rank _]] [Hother Hinstalled]]]]]].
  simpl in Hnew_reason.
  unfold grounded_at in *.
  intros y vy Hassigned_new.
  destruct (Z.eq_dec y x) as [->|Hyx].
  - rewrite Hnew_x in Hassigned_new.
    inversion Hassigned_new; subst vy.
    exists d, rx.
    split; [exact Hnew_level|].
    split; [exact Hnew_rank|].
    left. split; assumption.
  - destruct (Hother y Hyx) as
      [Hassignment_y [Hlevel_y [Hreason_y Hrank_y]]].
    rewrite Hassignment_y in Hassigned_new.
    specialize (Hgrounded y vy Hassigned_new).
    destruct Hgrounded as
      [dy [ry [Hold_level [Hold_rank Hsupport_old]]]].
    exists dy, ry.
    split.
    { rewrite Hlevel_y. exact Hold_level. }
    split.
    { rewrite Hrank_y. exact Hold_rank. }
    destruct Hsupport_old as [Hdecision|Hpropagated].
    { left.
      destruct Hdecision as [Hold_reason Hdy].
      split; [rewrite Hreason_y; exact Hold_reason|exact Hdy]. }
    { right.
      destruct Hpropagated as
        [i [Hold_reason [Hold_valid Hsupport]]].
      exists i.
      split.
      { rewrite Hreason_y. exact Hold_reason. }
      split.
      { eapply assigns_one_reason_valid_other__decide_exit_solver_setup;
          eauto. }
      destruct Hsupport as [Hdy0|Hpredecessor].
      { left. exact Hdy0. }
      { right.
        destruct Hpredecessor as [z Hpredecessor].
        exists z.
        eapply
          assigns_one_same_level_predecessor_other__decide_exit_solver_setup;
          eauto. } }
Qed.
Lemma assigns_one_closed_new_level__decide_exit_solver_setup :
  forall old new x b,
    assigns_one old new x b (current_level old + 1) (-1) ->
    current_level new = current_level old + 1 ->
    closed_levels old ->
    closed_levels new.
Proof.
  intros old new x b Hassigns Hcurrent Hclosed.
  pose proof Hassigns as Hfields.
  unfold assigns_one in Hfields.
  destruct Hfields as
    [Hold_none [Hnew_x [Hnew_level [Hnew_reason
      [_ [Hother Hinstalled]]]]]].
  simpl in Hnew_reason.
  unfold closed_levels in *.
  destruct Hclosed as
    [Hold_current [Hold_bounds [Hold_no_zero Hold_unique]]].
  split.
  - rewrite Hcurrent. lia.
  - split.
    + intros y vy dy Hassigned Hlevel.
      destruct (Z.eq_dec y x) as [->|Hyx].
      * rewrite Hnew_x in Hassigned.
        inversion Hassigned; subst vy.
        rewrite Hnew_level in Hlevel.
        inversion Hlevel; subst dy.
        rewrite Hcurrent. lia.
      * destruct (Hother y Hyx) as
          [Hassignment_y [Hlevel_y _]].
        rewrite Hassignment_y in Hassigned.
        rewrite Hlevel_y in Hlevel.
        specialize (Hold_bounds y vy dy Hassigned Hlevel).
        rewrite Hcurrent. lia.
    + split.
      * intros y Hdecision_new.
        unfold decision_at in Hdecision_new.
        destruct Hdecision_new as
          [[vy Hassigned] [Hlevel Hreason]].
        destruct (Z.eq_dec y x) as [->|Hyx].
        -- rewrite Hnew_level in Hlevel. inversion Hlevel. lia.
        -- apply (Hold_no_zero y).
           unfold decision_at.
           destruct (Hother y Hyx) as
             [Hassignment_y [Hlevel_y [Hreason_y _]]].
           split.
           ++ exists vy. rewrite <- Hassignment_y. exact Hassigned.
           ++ split.
              ** rewrite <- Hlevel_y. exact Hlevel.
              ** rewrite <- Hreason_y. exact Hreason.
      * intros dl Hdl.
        destruct (Z.eq_dec dl (current_level old + 1))
          as [Htop|Hbelow].
        -- subst dl.
           exists x.
           split.
           ++ unfold decision_at.
              split.
              ** exists b. exact Hnew_x.
              ** split; [exact Hnew_level|exact Hnew_reason].
           ++ intros y Hdecision_y.
              destruct (Z.eq_dec y x) as [->|Hyx]; [reflexivity|].
              unfold decision_at in Hdecision_y.
              destruct Hdecision_y as
                [[vy Hassigned] [Hlevel _]].
              destruct (Hother y Hyx) as
                [Hassignment_y [Hlevel_y _]].
              rewrite Hassignment_y in Hassigned.
              rewrite Hlevel_y in Hlevel.
              pose proof
                (Hold_bounds y vy (current_level old + 1)
                  Hassigned Hlevel).
              lia.
        -- assert (Hdl_old : 0 < dl <= current_level old) by
             (rewrite Hcurrent in Hdl; lia).
           destruct (Hold_unique dl Hdl_old) as
             [y [Hdecision_old Honly_old]].
           assert (Hyx : y <> x).
           {
             intro Heq. subst y.
             unfold decision_at in Hdecision_old.
             destruct Hdecision_old as [[vy Hassigned] _].
             rewrite Hold_none in Hassigned. discriminate.
           }
           exists y.
           split.
           ++ unfold decision_at in *.
              destruct Hdecision_old as
                [[vy Hassigned] [Hlevel Hreason]].
              destruct (Hother y Hyx) as
                [Hassignment_y [Hlevel_y [Hreason_y _]]].
              split.
              ** exists vy. rewrite Hassignment_y. exact Hassigned.
              ** split.
                 --- rewrite Hlevel_y. exact Hlevel.
                 --- rewrite Hreason_y. exact Hreason.
           ++ intros z Hdecision_z.
              destruct (Z.eq_dec z x) as [->|Hzx].
              ** unfold decision_at in Hdecision_z.
                 destruct Hdecision_z as [_ [Hlevel _]].
                 rewrite Hnew_level in Hlevel.
                 inversion Hlevel; subst dl; lia.
              ** apply Honly_old.
                 unfold decision_at in *.
                 destruct Hdecision_z as
                   [[vz Hassigned] [Hlevel Hreason]].
                 destruct (Hother z Hzx) as
                   [Hassignment_z [Hlevel_z [Hreason_z _]]].
                 split.
                 --- exists vz. rewrite <- Hassignment_z. exact Hassigned.
                 --- split.
                     +++ rewrite <- Hlevel_z. exact Hlevel.
                     +++ rewrite <- Hreason_z. exact Hreason.
Qed.
Lemma assigns_one_restrict_below__decide_exit_solver_setup :
  forall old new x b,
    assigns_one old new x b (current_level old + 1) (-1) ->
    forall k,
      k <= current_level old ->
      restrict_to_level new k = restrict_to_level old k.
Proof.
  intros old new x b Hassigns k Hk.
  unfold assigns_one in Hassigns.
  destruct Hassigns as
    [Hold_none [Hnew_x [Hnew_level [_ [_ [Hother _]]]]]].
  apply functional_extensionality.
  intro y.
  unfold restrict_to_level.
  destruct (Z.eq_dec y x) as [->|Hyx].
  - rewrite Hold_none, Hnew_x, Hnew_level.
    assert (Hleb : (current_level old + 1 <=? k)%Z = false).
    { apply Z.leb_gt. lia. }
    rewrite Hleb.
    reflexivity.
  - destruct (Hother y Hyx) as [Hassignment_y [Hlevel_y _]].
    rewrite Hassignment_y, Hlevel_y.
    reflexivity.
Qed.
Lemma quiescent_no_active__decide_exit_solver_setup :
  forall a c,
    no_conflict a ->
    no_unit a ->
    In c (installed_clauses a) ->
    ~ active_frontier_clause (assignment a) c.
Proof.
  intros a c Hno_conflict Hno_unit Hin Hactive.
  unfold active_frontier_clause in Hactive.
  destruct Hactive as [Htrue Hunassigned].
  pose proof
    (clause_unassigned_count_nonnegative_base__bcp_unit_to_assignment
      (assignment a) c) as Hnonneg.
  assert (Hzero_or_one :
    clause_unassigned_count (assignment a) c = 0 \/
    clause_unassigned_count (assignment a) c = 1) by lia.
  destruct Hzero_or_one as [Hzero|Hone].
  - apply (Hno_conflict c Hin).
    eapply clause_counts_zero_false__bcp_unit_to_assignment; eauto.
  - apply (Hno_unit c Hin).
    unfold clause_unit.
    split; assumption.
Qed.
Lemma assigns_one_frontier_new_level__decide_exit_solver_setup :
  forall old new x,
    assigns_one old new x true (current_level old + 1) (-1) ->
    current_level new = current_level old + 1 ->
    grounded_at old ->
    closed_levels old ->
    frontier_closed old ->
    grounded_at new ->
    closed_levels new ->
    no_conflict old ->
    no_unit old ->
    no_conflict new ->
    frontier_closed new.
Proof.
  intros old new x Hassigns Hcurrent
    Hgrounded_old Hclosed_old Hfrontier_old
    Hgrounded_new Hclosed_new
    Hno_conflict_old Hno_unit_old Hno_conflict_new.
  pose proof Hassigns as Hfields.
  unfold assigns_one in Hfields.
  destruct Hfields as
    [Hold_none [Hnew_x [Hnew_level [_ [_ [Hother Hinstalled]]]]]].
  destruct Hfrontier_old as [Hbelow_old Hcurrent_old].
  pose proof
    (restrict_current_eq_assignment__bcp_unit_to_assignment
      old Hgrounded_old Hclosed_old) as Hrestrict_old.
  pose proof
    (restrict_current_eq_assignment__bcp_unit_to_assignment
      new Hgrounded_new Hclosed_new) as Hrestrict_new.
  assert (Hno_active_old : forall c,
    In c (installed_clauses old) ->
    ~ active_frontier_clause (assignment old) c).
  {
    intros c Hin.
    eapply quiescent_no_active__decide_exit_solver_setup; eauto.
  }
  split.
  - intros k Hk.
    unfold no_active_clause_at.
    intros c Hin_new Hactive_new.
    rewrite Hinstalled in Hin_new.
    assert (Hk_old : k <= current_level old) by
      (rewrite Hcurrent in Hk; lia).
    pose proof
      (assigns_one_restrict_below__decide_exit_solver_setup
        old new x true Hassigns k Hk_old) as Hrestrict_k.
    rewrite Hrestrict_k in Hactive_new.
    destruct (Z.eq_dec k (current_level old)) as [->|Hneq].
    + rewrite Hrestrict_old in Hactive_new.
      exact (Hno_active_old c Hin_new Hactive_new).
    + exact (Hbelow_old k (ltac:(lia)) c Hin_new Hactive_new).
  - right.
    intros c Hin_new Hactive_new.
    rewrite Hrestrict_new in Hactive_new.
    rewrite Hinstalled in Hin_new.
    destruct (clause_var_occurs_dec c x)
      as [Hoccurs|Habsent].
    + destruct Hoccurs as [l [Hin_l Hvar_l]].
      exists l.
      split; [exact Hin_l|].
      unfold literal_false_at_level.
      split.
      * rewrite Hrestrict_new.
        destruct l as [y|y]; simpl in Hvar_l.
        -- rewrite Hvar_l.
           exfalso.
           assert (Heval_pos :
             eval_partial_literal (assignment new) (Pos x) = Some true).
           { unfold eval_partial_literal; simpl.
             rewrite Hnew_x. reflexivity. }
           assert (Hin_pos : In (Pos x) c).
           { rewrite <- Hvar_l. exact Hin_l. }
           pose proof
             (clause_true_count_member_true__bcp_unit_to_assignment
               (assignment new) c (Pos x) Hin_pos Heval_pos).
           unfold active_frontier_clause in Hactive_new.
           lia.
        -- rewrite Hvar_l.
           unfold eval_partial_literal; simpl.
           rewrite Hnew_x. reflexivity.
      * rewrite Hvar_l, Hnew_level, Hcurrent.
        reflexivity.
    + pose proof
        (literal_counts_no_var__bcp_unit_to_assignment x true c
          (fun l Hin Hvar => Habsent (ex_intro _ l (conj Hin Hvar))))
        as [Hvar_count Htrue_at_count].
      pose proof
        (clause_counts_assign (assignment old) x true c Hold_none)
        as [Hunassigned_update Htrue_update].
      pose proof
        (assigns_one_assignment_update__bcp_assignment_summary_a
          old new x true (current_level old + 1) (-1) Hassigns)
        as Hassignment_update.
      rewrite <- Hassignment_update in
        Hunassigned_update, Htrue_update.
      exfalso.
      apply (Hno_active_old c Hin_new).
      unfold active_frontier_clause in *.
      destruct Hactive_new as [Htrue_new Hunassigned_new].
      split; lia.
Qed.
Lemma decision_extension_stable__decide_exit_solver_setup :
  forall old new x,
    assigns_one old new x true (current_level old + 1) (-1) ->
    current_level new = current_level old + 1 ->
    grounded_at old /\ closed_levels old /\ frontier_closed old ->
    no_conflict old ->
    no_unit old ->
    (forall c, In c (installed_clauses old) ->
      NoDup c /\
      (forall l1 l2,
        In l1 c -> In l2 c ->
        literal_var l1 = literal_var l2 -> l1 = l2)) ->
    grounded_at new /\ closed_levels new /\ frontier_closed new /\
    no_conflict new.
Proof.
  intros old new x Hassigns Hcurrent Hstable
    Hno_conflict Hno_unit Hunique.
  destruct Hstable as [Hgrounded [Hclosed Hfrontier]].
  pose proof
    (decision_extension_no_conflict__decide_exit_solver_setup
      old new x (current_level old + 1) (-1)
      Hassigns Hno_conflict Hno_unit Hunique) as Hno_conflict_new.
  assert (Hpositive_new : 0 < current_level old + 1).
  { unfold closed_levels in Hclosed. lia. }
  pose proof
    (assigns_one_grounded_decision__decide_exit_solver_setup
      old new x true (current_level old + 1)
      Hassigns Hgrounded Hpositive_new) as Hgrounded_new.
  pose proof
    (assigns_one_closed_new_level__decide_exit_solver_setup
      old new x true Hassigns Hcurrent Hclosed) as Hclosed_new.
  pose proof
    (assigns_one_frontier_new_level__decide_exit_solver_setup
      old new x Hassigns Hcurrent Hgrounded Hclosed Hfrontier
      Hgrounded_new Hclosed_new Hno_conflict Hno_unit Hno_conflict_new)
    as Hfrontier_new.
  split; [exact Hgrounded_new|].
  split; [exact Hclosed_new|].
  split; [exact Hfrontier_new|exact Hno_conflict_new].
Qed.
(** The decision commit -- write 1 at index [i] of the value array, level
    [logical_dl + 1], reason -1, rank 0, everything else untouched -- is exactly
    one [assigns_one] step of the semantic view.  Extracted from
    [decision_commit_bcp_ready__decide_exit_solver_setup], whose sections 3 and
    4 this replaces. *)
Lemma commit_view_assigns_one__decide_exit_solver_setup :
  forall n snap next_snap ranks next_ranks logical_dl i
      cur_states cur_true cur_unassigned,
    0 <= i < n ->
    Zlength (snap_levels snap) = n ->
    Zlength (snap_reasons snap) = n ->
    assignment_update_only
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n next_snap next_ranks (logical_dl + 1))
      i true ->
    assigns_one
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n
    {| snap_values := snap_values next_snap;
       snap_reasons := replace_Znth i (-1) (snap_reasons snap);
       snap_levels := replace_Znth i (logical_dl + 1) (snap_levels snap);
       snap_rows := snap_rows snap;
       snap_states := cur_states;
       snap_true_counts := cur_true;
       snap_unassigned := cur_unassigned |}
    (fun y => if Z.eq_dec y i then Some O else ranks y)
        (logical_dl + 1))
      i true (logical_dl + 1) (-1).
Proof.
  intros n snap next_snap ranks next_ranks logical_dl i
    cur_states cur_true cur_unassigned
    Hi Hlevels_length Hreasons_length Hupdate.
  unfold assignment_update_only in Hupdate.
  destruct Hupdate as [Hold_none [Hnext_i [Hnext_other Hnext_installed]]].
  set (final_snap :=
    {| snap_values := snap_values next_snap;
       snap_reasons := replace_Znth i (-1) (snap_reasons snap);
       snap_levels := replace_Znth i (logical_dl + 1) (snap_levels snap);
       snap_rows := snap_rows snap;
       snap_states := cur_states;
       snap_true_counts := cur_true;
       snap_unassigned := cur_unassigned |}).
  set (final_ranks :=
(fun y => if Z.eq_dec y i then Some O else ranks y)).
  assert (Htarget_i :
    snapshot_assignment n final_snap i = Some true).
  {
    subst final_snap.
    cbn.
    exact Hnext_i.
  }
  assert (Htarget_other : forall y, y <> i ->
    assignment
      (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1)) y =
      assignment (cdcl_view_of_snapshot n snap ranks logical_dl) y).
  {
    intros y Hyi.
    subst final_snap.
    cbn.
    exact (Hnext_other y Hyi).
  }
  assert (Htarget_level :
    level_of
      (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1)) i =
    Some (logical_dl + 1)).
  {
    change
      (match snapshot_assignment n final_snap i with
       | None => None
       | Some _ => Some (Znth i (snap_levels final_snap) (-1))
       end = Some (logical_dl + 1)).
    rewrite Htarget_i.
    subst final_snap.
    change
      (Some (Znth i
        (replace_Znth i (logical_dl + 1) (snap_levels snap)) (-1)) =
       Some (logical_dl + 1)).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
  }
  assert (Htarget_reason :
    reason_of
      (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1)) i =
    None).
  {
    change
      (match snapshot_assignment n final_snap i with
       | None => None
       | Some _ =>
           let r := Znth i (snap_reasons final_snap) (-1) in
           if Z.eqb r (-1) then None else Some r
       end = None).
    rewrite Htarget_i.
    subst final_snap.
    change
      ((if Z.eqb
          (Znth i (replace_Znth i (-1) (snap_reasons snap)) (-1))
          (-1)
        then None
        else Some (Znth i
          (replace_Znth i (-1) (snap_reasons snap)) (-1))) = None).
    rewrite Znth_replace_Znth_Same by lia.
    rewrite Z.eqb_refl.
    reflexivity.
  }
    unfold assigns_one.
    split; [exact Hold_none|].
    split; [exact Htarget_i|].
    split; [exact Htarget_level|].
    split; [exact Htarget_reason|].
    split.
        * exists O.
          split.
          -- subst final_ranks. cbn.
             destruct (Z.eq_dec i i); [reflexivity|contradiction].
          -- intros y Hdependency.
             unfold reason_dependency in Hdependency.
             destruct Hdependency as
               [reason_index [c [l [Hreason_i _]]]].
             rewrite Htarget_reason in Hreason_i.
             discriminate.
        * split.
          -- intros y Hyi.
             split; [exact (Htarget_other y Hyi)|].
             assert (Hassignment_y :
               snapshot_assignment n final_snap y =
               snapshot_assignment n snap y).
             { exact (Htarget_other y Hyi). }
             split.
             ++ change
                  (match snapshot_assignment n final_snap y with
                   | None => None
                   | Some _ => Some (Znth y (snap_levels final_snap) (-1))
                   end =
                   match snapshot_assignment n snap y with
                   | None => None
                   | Some _ => Some (Znth y (snap_levels snap) (-1))
                   end).
                rewrite Hassignment_y.
                destruct (snapshot_assignment n snap y) eqn:Hassignment_old;
                  [|reflexivity].
                assert (Hy : 0 <= y < n).
                {
                  unfold snapshot_assignment in Hassignment_old.
                  destruct (andb (Z.leb 0 y) (Z.ltb y n)) eqn:Hrange;
                    [|discriminate].
                  apply andb_true_iff in Hrange.
                  destruct Hrange as [Hy0 Hyn].
                  apply Z.leb_le in Hy0.
                  apply Z.ltb_lt in Hyn.
                  lia.
                }
                subst final_snap.
                change
                  (Some (Znth y
                    (replace_Znth i (logical_dl + 1) (snap_levels snap))
                    (-1)) = Some (Znth y (snap_levels snap) (-1))).
                rewrite Znth_replace_Znth_Diff by
                  (rewrite ?Hlevels_length; lia).
                reflexivity.
             ++ split.
                ** change
                     (match snapshot_assignment n final_snap y with
                      | None => None
                      | Some _ =>
                          let r := Znth y (snap_reasons final_snap) (-1) in
                          if Z.eqb r (-1) then None else Some r
                      end =
                      match snapshot_assignment n snap y with
                      | None => None
                      | Some _ =>
                          let r := Znth y (snap_reasons snap) (-1) in
                          if Z.eqb r (-1) then None else Some r
                      end).
                   rewrite Hassignment_y.
                   destruct (snapshot_assignment n snap y)
                     eqn:Hassignment_old;
                     [|reflexivity].
                   assert (Hy : 0 <= y < n).
                   {
                     unfold snapshot_assignment in Hassignment_old.
                     destruct (andb (Z.leb 0 y) (Z.ltb y n)) eqn:Hrange;
                       [|discriminate].
                     apply andb_true_iff in Hrange.
                     destruct Hrange as [Hy0 Hyn].
                     apply Z.leb_le in Hy0.
                     apply Z.ltb_lt in Hyn.
                     lia.
                   }
                   subst final_snap.
                   change
                     ((if Z.eqb
                         (Znth y
                           (replace_Znth i (-1) (snap_reasons snap)) (-1))
                         (-1)
                       then None
                       else Some (Znth y
                         (replace_Znth i (-1) (snap_reasons snap)) (-1))) =
                      (if Z.eqb (Znth y (snap_reasons snap) (-1)) (-1)
                       then None
                       else Some (Znth y (snap_reasons snap) (-1)))).
                   rewrite Znth_replace_Znth_Diff by
                     (rewrite ?Hreasons_length; lia).
                   reflexivity.
                ** subst final_ranks. cbn.
                   destruct (Z.eq_dec y i); [contradiction|reflexivity].
          -- reflexivity.
Qed.

(** The decision commit preserves snapshot coherence.  The overwritten cell is
    well-formed at the new level, and the fresh per-clause summaries are exact
    over the whole live range because the mixed hypothesis is already fully
    processed ([processed_until = live], [exempt = None]).  Extracted from
    [decision_commit_bcp_ready__decide_exit_solver_setup] section 5a.

    Note [0 <= logical_dl]: it is not one of the destructured components, and a
    lemma stated without it is unprovable -- the [lia] for the new level needs
    it. *)
Lemma commit_preserves_coherent__decide_exit_solver_setup :
  forall F n live original cap snap next_snap ranks next_ranks logical_dl i
      cur_states cur_true cur_unassigned,
    0 <= i < n ->
    0 <= logical_dl ->
    coherent_snapshot F n live original snap ->
    snap_values next_snap = replace_Znth i 1 (snap_values snap) ->
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment
        (cdcl_view_of_snapshot n next_snap next_ranks (logical_dl + 1)))
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl))
      cur_states cur_true cur_unassigned live cap live None ->
    coherent_snapshot F n live original
    {| snap_values := snap_values next_snap;
       snap_reasons := replace_Znth i (-1) (snap_reasons snap);
       snap_levels := replace_Znth i (logical_dl + 1) (snap_levels snap);
       snap_rows := snap_rows snap;
       snap_states := cur_states;
       snap_true_counts := cur_true;
       snap_unassigned := cur_unassigned |}.
Proof.
  intros F n live original cap snap next_snap ranks next_ranks logical_dl i
    cur_states cur_true cur_unassigned
    Hi Hlogical Hcoherent Hnext_values Hmixed.
  pose proof Hcoherent as Hcoherent_fields.
  unfold coherent_snapshot in Hcoherent_fields.
  destruct Hcoherent_fields as
    [Hn [Horiginal [Hlengths [Hcells [Hsummaries Hsound]]]]].
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as
    [Hvalues_length [Hreasons_length [Hlevels_length
      [Hrows_length [Hstates_length
        [Htrue_length Hunassigned_length]]]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [Hcell_wf Hrows_wf].
  unfold mixed_clause_summaries in Hmixed.
  destruct Hmixed as
    [Hmixed_rows [Hcur_states_length [Hcur_true_length
      [Hcur_unassigned_length [Hlive_cap [Hprocessed Hmixed_exact]]]]]].
  set (final_snap :=
    {| snap_values := snap_values next_snap;
       snap_reasons := replace_Znth i (-1) (snap_reasons snap);
       snap_levels := replace_Znth i (logical_dl + 1) (snap_levels snap);
       snap_rows := snap_rows snap;
       snap_states := cur_states;
       snap_true_counts := cur_true;
       snap_unassigned := cur_unassigned |}).
  set (final_ranks :=
(fun y => if Z.eq_dec y i then Some O else ranks y)).
    unfold coherent_snapshot.
    refine (conj Hn (conj Horiginal (conj _ (conj _ (conj _ _))))).
    - unfold snapshot_lengths.
      subst final_snap.
      cbn.
      repeat split.
      + rewrite Hnext_values, Zlength_replace_Znth.
        exact Hvalues_length.
      + rewrite Zlength_replace_Znth. exact Hreasons_length.
      + rewrite Zlength_replace_Znth. exact Hlevels_length.
      + exact Hrows_length.
      + exact Hcur_states_length.
      + exact Hcur_true_length.
      + exact Hcur_unassigned_length.
    - unfold snapshot_cells_wf.
      split.
      + intros x Hx.
        destruct (Z.eq_dec x i) as [->|Hxi].
        * subst final_snap.
          change
            ((Znth i (snap_values next_snap) (-1) = -1 \/
              Znth i (snap_values next_snap) (-1) = 0 \/
              Znth i (snap_values next_snap) (-1) = 1) /\
             (Znth i (snap_values next_snap) (-1) = -1 ->
              Znth i
                (replace_Znth i (logical_dl + 1) (snap_levels snap)) (-1) =
                -1 /\
              Znth i (replace_Znth i (-1) (snap_reasons snap)) (-1) =
                -1) /\
             (Znth i (snap_values next_snap) (-1) <> -1 ->
              0 <= Znth i
                (replace_Znth i (logical_dl + 1) (snap_levels snap)) (-1) /\
              (Znth i (replace_Znth i (-1) (snap_reasons snap)) (-1) =
                 -1 \/
               0 <= Znth i
                 (replace_Znth i (-1) (snap_reasons snap)) (-1) < live))).
          rewrite Hnext_values.
          rewrite Znth_replace_Znth_Same by lia.
          rewrite Znth_replace_Znth_Same by lia.
          rewrite Znth_replace_Znth_Same by lia.
          split.
          -- right. right. reflexivity.
          -- split.
             ++ intro Hcontra. discriminate.
             ++ intro Hnotminus. split; [lia|].
                left. reflexivity.
        * specialize (Hcell_wf x Hx).
          unfold var_in_range in Hx.
          subst final_snap.
          change
            (let v := Znth x (snap_values next_snap) (-1) in
             let d := Znth x
               (replace_Znth i (logical_dl + 1) (snap_levels snap)) (-1) in
             let r := Znth x
               (replace_Znth i (-1) (snap_reasons snap)) (-1) in
             (v = -1 \/ v = 0 \/ v = 1) /\
             (v = -1 -> d = -1 /\ r = -1) /\
             (v <> -1 -> 0 <= d /\ (r = -1 \/ 0 <= r < live))).
          rewrite Hnext_values.
          rewrite Znth_replace_Znth_Diff by
            (rewrite ?Hvalues_length; lia).
          rewrite Znth_replace_Znth_Diff by
            (rewrite ?Hlevels_length; lia).
          rewrite Znth_replace_Znth_Diff by
            (rewrite ?Hreasons_length; lia).
          exact Hcell_wf.
      + subst final_snap.
        change (Forall (row_wf n) (snap_rows snap)).
        exact Hrows_wf.
    - unfold snapshot_summaries_exact.
      intros k Hk.
      specialize (Hmixed_exact k Hk).
      destruct Hmixed_exact as [Hnew_summary _].
      assert (Hprocessed_k : k < live \/ None = Some k).
      { left. lia. }
      specialize (Hnew_summary Hprocessed_k).
      subst final_snap. cbn.
      exact Hnew_summary.
    - subst final_snap. cbn. exact Hsound.
Qed.

Lemma decision_commit_bcp_ready__decide_exit_solver_setup :
  forall F n live original cap snap ranks logical_dl i
      next_snap next_ranks cur_states cur_true cur_unassigned,
    0 <= i < n ->
    0 <= logical_dl < n ->
    coherent_snapshot F n live original snap ->
    stable_search_facts n snap ranks logical_dl ->
    no_conflict
      (cdcl_view_of_snapshot n snap ranks logical_dl) ->
    no_unit
      (cdcl_view_of_snapshot n snap ranks logical_dl) ->
    snap_values next_snap =
      replace_Znth i 1 (snap_values snap) ->
    snap_rows next_snap = snap_rows snap ->
    assignment_update_only
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n next_snap next_ranks (logical_dl + 1))
      i true ->
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment
        (cdcl_view_of_snapshot n next_snap next_ranks (logical_dl + 1)))
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl))
      cur_states cur_true cur_unassigned live cap live None ->
    exists final_snap final_ranks,
      snap_values final_snap = snap_values next_snap /\
      snap_levels final_snap =
        replace_Znth i (logical_dl + 1) (snap_levels snap) /\
      snap_reasons final_snap =
        replace_Znth i (-1) (snap_reasons snap) /\
      snap_rows final_snap = snap_rows snap /\
      snap_states final_snap = cur_states /\
      snap_true_counts final_snap = cur_true /\
      snap_unassigned final_snap = cur_unassigned /\
      coherent_snapshot F n live original final_snap /\
      stable_search_facts n final_snap final_ranks (logical_dl + 1) /\
      no_conflict
        (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1)) /\
      assignment_update_only
        (cdcl_view_of_snapshot n snap ranks logical_dl)
        (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1))
        i true /\
      mixed_clause_summaries
        (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
        (assignment
          (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1)))
        (installed_clauses
          (cdcl_view_of_snapshot n snap ranks logical_dl))
        (snap_states final_snap) (snap_true_counts final_snap)
        (snap_unassigned final_snap) live cap live None.
Proof.
  (* Discharges an 11-way conjunction about one constructed snapshot.  Its
     skeleton is a chain of named [assert]s, each self-contained; read them as
     sections:

       1. destructure  -- coherent_snapshot / snapshot_lengths /
                          assignment_update_only / mixed_clause_summaries
       2. [final_snap], [final_ranks]      the witnesses (set, just below)
       3. [Hassigns]   -- assigns_one for the commit, by
                          [commit_view_assigns_one__decide_exit_solver_setup]
       4. [Hunique], [Hstable_view], [Hstable_final], [Hupdate_final],
          [Hmixed_final]  -- one per remaining conjunct
       5. [Hcoherent_final], by
          [commit_preserves_coherent__decide_exit_solver_setup]
       6. assemble     -- exists + a split per conjunct

     An earlier note here recorded that extraction had been rejected because
     the two large blocks would need 11 and 14 hypothesis parameters.  That
     counted the context *after* the destructuring above; passing the
     predicates folded needs 4 and 5, and both blocks moved out.  The witnesses
     stay [set] inside the extracted lemmas, so every [subst final_snap] in the
     moved text still means what it meant here -- which is what avoids the
     reduction-control trap that made hoisting them to global Definitions a bad
     idea. *)
  intros F n live original cap snap ranks logical_dl i
    next_snap next_ranks cur_states cur_true cur_unassigned
    Hi Hlogical Hcoherent Hstable Hno_conflict Hno_unit
    Hnext_values Hnext_rows Hupdate Hmixed.
  pose proof Hcoherent as Hcoherent_fields.
  unfold coherent_snapshot in Hcoherent_fields.
  destruct Hcoherent_fields as
    [Hn [Horiginal [Hlengths [Hcells [Hsummaries Hsound]]]]].
  unfold snapshot_lengths in Hlengths.
  destruct Hlengths as
    [Hvalues_length [Hreasons_length [Hlevels_length
      [Hrows_length [Hstates_length
        [Htrue_length Hunassigned_length]]]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [Hcell_wf Hrows_wf].
  pose proof Hupdate as Hupdate_fields.
  unfold assignment_update_only in Hupdate_fields.
  destruct Hupdate_fields as
    [Hold_none [Hnext_i [Hnext_other Hnext_installed]]].
  pose proof Hmixed as Hmixed_fields.
  unfold mixed_clause_summaries in Hmixed_fields.
  destruct Hmixed_fields as
    [Hmixed_rows [Hcur_states_length [Hcur_true_length
      [Hcur_unassigned_length [Hlive_cap [Hprocessed Hmixed_exact]]]]]].
  set (final_snap :=
    {| snap_values := snap_values next_snap;
       snap_reasons := replace_Znth i (-1) (snap_reasons snap);
       snap_levels := replace_Znth i (logical_dl + 1) (snap_levels snap);
       snap_rows := snap_rows snap;
       snap_states := cur_states;
       snap_true_counts := cur_true;
       snap_unassigned := cur_unassigned |}).
  set (final_ranks := fun y =>
    if Z.eq_dec y i then Some O else ranks y).
  (* section 4: the commit assigns exactly variable i, at the new level *)
  assert (Hassigns :
    assigns_one
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1))
      i true (logical_dl + 1) (-1)).
  {
    subst final_snap final_ranks.
    exact (commit_view_assigns_one__decide_exit_solver_setup
             n snap next_snap ranks next_ranks logical_dl i
             cur_states cur_true cur_unassigned
             Hi Hlevels_length Hreasons_length Hupdate).
  }
  assert (Hunique : forall c,
    In c
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl)) ->
    NoDup c /\
    (forall l1 l2,
      In l1 c -> In l2 c ->
      literal_var l1 = literal_var l2 -> l1 = l2)).
  {
    intros c Hin.
    cbn in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [row [<- Hinrow]].
    apply Forall_forall with (x := row) in Hrows_wf; [|exact Hinrow].
    split.
    - apply dense_decode_nodup__decide_exit_solver_setup.
    - intros l1 l2 Hin1 Hin2 Hvar.
      eapply
        dense_decode_unique_var__learning_row_and_scan;
        eauto.
  }
  assert (Hstable_view :
    grounded_at
      (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1)) /\
    closed_levels
      (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1)) /\
    frontier_closed
      (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1)) /\
    no_conflict
      (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1))).
  {
    unfold stable_search_facts in Hstable.
    eapply decision_extension_stable__decide_exit_solver_setup
      with (x := i).
    - exact Hassigns.
    - reflexivity.
    - exact Hstable.
    - exact Hno_conflict.
    - exact Hno_unit.
    - exact Hunique.
  }
  destruct Hstable_view as
    [Hgrounded_final [Hclosed_final [Hfrontier_final Hno_conflict_final]]].
  (* section 5a: the constructed snapshot is still coherent *)
  assert (Hcoherent_final :
    coherent_snapshot F n live original final_snap).
  {
    subst final_snap.
    exact (commit_preserves_coherent__decide_exit_solver_setup
             F n live original cap snap next_snap ranks next_ranks
             logical_dl i cur_states cur_true cur_unassigned
             Hi ltac:(lia) Hcoherent Hnext_values Hmixed).
  }
  assert (Hstable_final :
    stable_search_facts n final_snap final_ranks (logical_dl + 1)).
  {
    unfold stable_search_facts.
    split; [exact Hgrounded_final|].
    split; [exact Hclosed_final|exact Hfrontier_final].
  }
  assert (Hupdate_final :
    assignment_update_only
      (cdcl_view_of_snapshot n snap ranks logical_dl)
      (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1))
      i true).
  {
    unfold assignment_update_only.
    repeat split; try assumption.
  }
  assert (Hmixed_final :
    mixed_clause_summaries
      (assignment (cdcl_view_of_snapshot n snap ranks logical_dl))
      (assignment
        (cdcl_view_of_snapshot n final_snap final_ranks (logical_dl + 1)))
      (installed_clauses
        (cdcl_view_of_snapshot n snap ranks logical_dl))
      (snap_states final_snap) (snap_true_counts final_snap)
      (snap_unassigned final_snap) live cap live None).
  {
    subst final_snap. cbn. exact Hmixed.
  }
  (* section 6: assemble the 11-way conjunction *)
  exists final_snap, final_ranks.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact Hcoherent_final|].
  split; [exact Hstable_final|].
  split; [exact Hno_conflict_final|].
  split; [exact Hupdate_final|exact Hmixed_final].
Qed.
Lemma decision_update_ready_facts__decide_exit_solver_setup :
  forall old new x next_clause live cap rows
      states true_counts unassigned,
    decision_ready old ->
    decision_update old new
      x next_clause live cap rows states true_counts unassigned ->
    no_conflict old /\
      no_unit old /\
      assignment_update_only old new x true /\
      mixed_clause_summaries
        (assignment old) (assignment new)
        rows states true_counts unassigned
        live cap next_clause None.
Proof.
  intros old new x next_clause live cap rows
    states true_counts unassigned Hready Hupd.
  unfold decision_ready, propagation_quiescent in Hready.
  unfold decision_update in Hupd.
  tauto.
Qed.
(* Retrofit helpers for collapsing the backtrack_entail_wit_4_* family:
   pure clear-step delta reasoning shared by all siblings.  Placed here
   because they depend on the backtrack_entry_clear_a and backtrack_clear_b
   groups above. *)
(* provenance: backtrack_entry_clear_a; kept here for dependency order *)
Lemma snapshot_value_cell_assignment__backtrack_entry_clear_a :
  forall n snap i (b : bool),
    Zlength (snap_values snap) = n ->
    0 <= i < n ->
    Znth i (snap_values snap) 0 = (if b then 1 else 0) ->
    snapshot_assignment n snap i = Some b.
Proof.
  intros n snap i b Hlen Hi Hcell.
  assert (Hindep : Znth i (snap_values snap) (-1) =
      Znth i (snap_values snap) 0).
  { apply Znth_indep. rewrite Hlen; exact Hi. }
  unfold snapshot_assignment.
  assert (Hguard : andb (Z.leb 0 i) (Z.ltb i n) = true).
  { apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite Hguard, Hindep, Hcell.
  destruct b; reflexivity.
Qed.
(* provenance: backtrack_entry_clear_a; kept here for dependency order *)
Lemma backtrack_clear_step_delta__backtrack_entry_clear_a :
  forall old new rows states true_counts unassigned live cap j i (b : bool)
         delta new_state,
    clears_one old new i ->
    mixed_clause_summaries (assignment old) (assignment new)
      rows states true_counts unassigned live cap j None ->
    0 <= j < live ->
    assignment old i = Some b ->
    literal_var_count i (Znth j rows (nil : clause)) = 1 ->
    literal_true_at_count i b (Znth j rows (nil : clause)) = delta ->
    ((delta = 1 /\ 1 < Znth j true_counts 0 /\ new_state = 0) \/
     (delta = 1 /\ Znth j states 0 = 0 /\ Znth j true_counts 0 <= 1 /\
        0 < Znth j unassigned 0 /\
        new_state = - Znth j unassigned 0 - 1) \/
     (delta = 1 /\ Znth j states 0 = 0 /\ Znth j true_counts 0 <= 1 /\
        Znth j unassigned 0 <= 0 /\ new_state = 2) \/
     (delta = 0 /\ Znth j states 0 = 0 /\ new_state = 0) \/
     (delta = 0 /\ Znth j states 0 = 1 /\ new_state = 2) \/
     (delta = 0 /\ Znth j states 0 = 2 /\ new_state = -2)) ->
    mixed_clause_summaries (assignment old) (assignment new) rows
      (replace_Znth j new_state states)
      (replace_Znth j (Znth j true_counts 0 - delta) true_counts)
      (replace_Znth j (Znth j unassigned 0 + 1) unassigned)
      live cap (j + 1) None.
Proof.
  intros old new rows states true_counts unassigned live cap j i b delta
    new_state Hclear Hmixed Hj Hassign Hvar Htrue Hcase.
  assert (Hold_summary :
    clause_summary_ok (assignment old) (Znth j rows (nil : clause))
      (Znth j states 0) (Znth j true_counts 0) (Znth j unassigned 0)).
  { pose proof Hmixed as Hm.
    unfold mixed_clause_summaries in Hm.
    destruct Hm as [_ [_ [_ [_ [_ [_ Hpoints]]]]]].
    specialize (Hpoints j Hj).
    destruct Hpoints as [_ Hold].
    apply Hold; split; [lia|discriminate]. }
  pose proof Hold_summary as Hold_eqs.
  unfold clause_summary_ok in Hold_eqs.
  destruct Hold_eqs as [Ht_eq [Hu_eq Hstate_eq]].
  pose proof (clears_one_assignment_eq_clear_partial__backtrack_entry_clear_a
    old new i Hclear) as Hsigma.
  pose proof (clause_counts_clear
    (assignment old) i b (Znth j rows (nil : clause)) Hassign)
    as [Hnew_u Hnew_t].
  eapply backtrack_summary_clear_step__backtrack_clear_b;
    [exact Hclear|exact Hmixed|exact Hj|exact Hassign|exact Hvar|exact Htrue|].
  rewrite Hsigma.
  destruct Hcase as
    [[Hd [Hgt Hns]]
    |[[Hd [Hs0 [Ht1 [Hu0 Hns]]]]
    |[[Hd [Hs0 [Ht1 [Hu0 Hns]]]]
    |[[Hd [Hs0 Hns]]
    |[[Hd [Hs1 Hns]]
    |[Hd [Hs2 Hns]]]]]]].
  - rewrite Hd in Htrue; subst new_state.
    apply (expected_clause_state_clear_gt1__backtrack_entry_clear_a
      (assignment old) i b);
      [exact Hassign|exact Hvar|exact Htrue|lia].
  - rewrite Hd in Htrue; subst new_state.
    apply (expected_clause_state_clear_middle__backtrack_entry_clear_a
      (assignment old) i b (Znth j rows (nil : clause))
      (Znth j true_counts 0) (Znth j unassigned 0));
      [exact Hassign|exact Hvar|exact Htrue|exact Ht_eq|exact Hu_eq|
       congruence|lia|lia].
  - rewrite Hd in Htrue; subst new_state.
    apply (expected_clause_state_clear_last__backtrack_entry_clear_a
      (assignment old) i b (Znth j rows (nil : clause))
      (Znth j true_counts 0) (Znth j unassigned 0));
      [exact Hassign|exact Hvar|exact Htrue|exact Ht_eq|exact Hu_eq|
       congruence|lia|lia].
  - rewrite Hd in Htrue; subst new_state.
    assert (Hexp0 : expected_clause_state (assignment old)
        (Znth j rows (nil : clause)) = 0) by congruence.
    assert (Htpos : 0 < clause_true_count (assignment old)
        (Znth j rows (nil : clause))).
    { unfold expected_clause_state in Hexp0.
      destruct (0 <? clause_true_count (assignment old)
          (Znth j rows (nil : clause))) eqn:E;
        [apply Z.ltb_lt in E; exact E|].
      apply Z.ltb_ge in E.
      destruct (clause_unassigned_count (assignment old)
          (Znth j rows (nil : clause)) =? 0) eqn:E0; [discriminate|].
      destruct (clause_unassigned_count (assignment old)
          (Znth j rows (nil : clause)) =? 1) eqn:E1; [discriminate|].
      apply Z.eqb_neq in E0; lia. }
    unfold expected_clause_state.
    rewrite Hnew_t, Htrue.
    replace (0 <? clause_true_count (assignment old)
        (Znth j rows (nil : clause)) - 0) with true
      by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  - rewrite Hd in Htrue; subst new_state.
    rewrite Hs1 in Hold_summary.
    pose proof (clause_summary_state_one_counts__backtrack_clear_b
      _ _ _ _ Hold_summary) as [Ht0 Hu0].
    assert (Htc : clause_true_count (assignment old)
        (Znth j rows (nil : clause)) = 0) by lia.
    assert (Huc : clause_unassigned_count (assignment old)
        (Znth j rows (nil : clause)) = 0) by lia.
    unfold expected_clause_state.
    rewrite Hnew_t, Htrue, Htc, Hnew_u, Hvar, Huc.
    reflexivity.
  - rewrite Hd in Htrue; subst new_state.
    rewrite Hs2 in Hold_summary.
    pose proof (clause_summary_state_two_counts__backtrack_clear_b
      _ _ _ _ Hold_summary) as [Ht0 Hu1].
    assert (Htc : clause_true_count (assignment old)
        (Znth j rows (nil : clause)) = 0) by lia.
    assert (Huc : clause_unassigned_count (assignment old)
        (Znth j rows (nil : clause)) = 1) by lia.
    unfold expected_clause_state.
    rewrite Hnew_t, Htrue, Htc, Hnew_u, Hvar, Huc.
    reflexivity.
Qed.
(** ===== ENDGAME: solver-level payoff lemmas =====

    These are the results the whole development exists to produce: they are
    what the five cdcl_solver return obligations consume.  Because every lemma
    in this file carries a work-group suffix, the semantically important names
    are hard to grep for -- so here they are, by role:

      SAT verdict (return 1)
        model_ready_models_original__solver_analysis_and_returns
          -- a totally-assigned, conflict-free snapshot models the ORIGINAL F.
          Built on: partial_clause_false_or_true__ (the constructive
          dichotomy), snapshot_partial_true_rho_true__, installed_clause_entails__.

      UNSAT verdict, route 1 (return 0 at cur_dl == 0, a root conflict)
        root_conflict_implies_cnf_unsat__solver_analysis_and_returns
          -- a clause falsified at level 0 makes the original F unsatisfiable.
          Built on: root_assignment_agrees__ and, beneath it,
          root_assignment_agrees_at_rank__ (well-founded induction on the
          ghost assignment rank -- the only lt_wf_ind in the file).

      UNSAT verdict, route 2 (return 0 after deriving the empty clause)
        entails_empty_cnf_unsat__decide_exit_solver_setup
          -- F |= [] makes F unsatisfiable.

    ALL of these are axiom-free: Print Assumptions reports "Closed under the
    global context" for every one.  Neither UNSAT route nor the SAT verdict
    depends on classical logic.  Please keep it that way -- see the
    "Decidability, in place of classical logic" banner near the top. *)

(* provenance suffix retained; relocated under ENDGAME, which indexes it *)
Lemma entails_empty_cnf_unsat__decide_exit_solver_setup :
  forall n F,
    cnf_wf n F ->
    entails_clause F nil ->
    cnf_unsat n F.
Proof.
  intros n F Hwf Hentails.
  unfold cnf_unsat.
  split; [exact Hwf|].
  intros rho Hbounded Hmodels.
  specialize (Hentails rho Hmodels).
  unfold clause_satisfied in Hentails.
  destruct Hentails as [l [Hin _]].
  contradiction.
Qed.

(** ===== group: solver_analysis_and_returns ===== *)
Lemma snapshot_assignment_rho_agree__solver_analysis_and_returns :
  forall n snap x b,
    snapshot_assignment n snap x = Some b ->
    rho_of_values n (snap_values snap) x = b.
Proof.
  intros n snap x b Hassigned.
  unfold snapshot_assignment in Hassigned.
  unfold rho_of_values.
  destruct (andb ((0 <=? x)%Z) ((x <? n)%Z)) eqn:Hguard;
    try discriminate.
  remember (Znth x (snap_values snap) (-1)) as z.
  unfold decode_value_cell in Hassigned.
  destruct ((z =? -1)%Z) eqn:Hzm; try discriminate.
  destruct ((z =? 0)%Z) eqn:Hz0.
  - apply Z.eqb_eq in Hz0.
    rewrite Hz0.
    inversion Hassigned. reflexivity.
  - destruct ((z =? 1)%Z) eqn:Hz1; try discriminate.
    inversion Hassigned. reflexivity.
Qed.
(** The constructive core of the SAT verdict.  Under "every literal of [c] is
    assigned", the clause is either false outright or contains a true literal.
    This dichotomy is what [classic] used to supply; it needs no axiom, because
    [c] is a finite list and each literal's value under [sigma] is a
    computation.  Establishing it constructively is what makes
    [model_ready_models_original] — and hence the whole mathematical core of
    this development — axiom-free. *)
Lemma partial_clause_false_or_true__solver_analysis_and_returns :
  forall sigma c,
    (forall l, In l c ->
      exists b, sigma (literal_var l) = Some b) ->
    clause_false sigma c \/
    (exists l, In l c /\ eval_partial_literal sigma l = Some true).
Proof.
  intros sigma c.
  induction c as [|l c IH]; intros Hassigned.
  - left. intros l Hin. contradiction.
  - destruct (Hassigned l (or_introl eq_refl)) as [b Hb].
    assert (Heval : exists v, eval_partial_literal sigma l = Some v).
    {
      unfold eval_partial_literal.
      rewrite Hb.
      eexists. reflexivity.
    }
    destruct Heval as [v Heval].
    destruct v.
    + right. exists l. split; [left; reflexivity|exact Heval].
    + assert (Htail_assigned : forall l', In l' c ->
        exists b', sigma (literal_var l') = Some b').
      { intros l' Hin. apply Hassigned. right. exact Hin. }
      destruct (IH Htail_assigned) as [Htailfalse|[l' [Hin Htrue]]].
      * left. intros l' [<- | Hin]; [exact Heval|exact (Htailfalse l' Hin)].
      * right. exists l'. split; [right; exact Hin|exact Htrue].
Qed.

Lemma partial_clause_has_true__solver_analysis_and_returns :
  forall sigma c,
    (forall l, In l c ->
      exists b, sigma (literal_var l) = Some b) ->
    ~ clause_false sigma c ->
    exists l, In l c /\ eval_partial_literal sigma l = Some true.
Proof.
  intros sigma c Hassigned Hnotfalse.
  destruct (partial_clause_false_or_true__solver_analysis_and_returns
              sigma c Hassigned) as [Hfalse|Htrue].
  - contradiction.
  - exact Htrue.
Qed.
Lemma snapshot_partial_true_rho_true__solver_analysis_and_returns :
  forall n snap l,
    eval_partial_literal (snapshot_assignment n snap) l = Some true ->
    eval_literal (rho_of_values n (snap_values snap)) l = true.
Proof.
  intros n snap [x|x] Htrue.
  - change
      (match snapshot_assignment n snap x with
       | None => None
       | Some b => Some b
       end = Some true) in Htrue.
    destruct (snapshot_assignment n snap x) as [b|] eqn:Hassigned;
      try discriminate.
    pose proof
      (snapshot_assignment_rho_agree__solver_analysis_and_returns
        n snap x b Hassigned) as Hagree.
    simpl. destruct b; [exact Hagree|discriminate Htrue].
  - change
      (match snapshot_assignment n snap x with
       | None => None
       | Some b => Some (negb b)
       end = Some true) in Htrue.
    destruct (snapshot_assignment n snap x) as [b|] eqn:Hassigned;
      try discriminate.
    pose proof
      (snapshot_assignment_rho_agree__solver_analysis_and_returns
        n snap x b Hassigned) as Hagree.
    simpl. destruct b; [discriminate Htrue|].
    rewrite Hagree. reflexivity.
Qed.
Theorem model_ready_models_original__solver_analysis_and_returns :
  forall F n live original_count snap ranks logical_dl,
    coherent_snapshot F n live original_count snap ->
    no_conflict
      (cdcl_view_of_snapshot n snap ranks logical_dl) ->
    total_assignment_on n
      (cdcl_view_of_snapshot n snap ranks logical_dl) ->
    models (rho_of_values n (snap_values snap)) F.
Proof.
  intros F n live original_count snap ranks logical_dl
    Hcoherent Hno_conflict Htotal.
  pose proof Hcoherent as Hcoherent'.
  unfold coherent_snapshot in Hcoherent'.
  destruct Hcoherent' as
    [_ [_ [_ [Hcells [_ Hsound]]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [_ Hrows_wf].
  unfold installed_clauses_sound in Hsound.
  destruct Hsound as [Hprefix _].
  unfold original_prefix_exact in Hprefix.
  destruct Hprefix as [Hprefix _].
  unfold no_conflict in Hno_conflict.
  unfold total_assignment_on in Htotal.
  apply Forall_forall.
  intros c HcF.
  assert (Hcinstalled :
    In c (map dense_decode (snap_rows snap))).
  {
    rewrite <- Hprefix in HcF.
    rewrite <-
      (firstn_skipn (Z.to_nat original_count)
        (map dense_decode (snap_rows snap))).
    apply in_or_app. left. exact HcF.
  }
  assert (Hclause_wf : Forall (literal_wf n) c).
  {
    pose proof Hcinstalled as Hcinstalled'.
    apply in_map_iff in Hcinstalled' as [row [Hdecode Hrow]].
    subst c.
    apply dense_decode_forall_wf__decide_exit_solver_setup.
    apply Forall_forall with (x := row) in Hrows_wf;
      assumption.
  }
  assert (Hall_assigned : forall l, In l c ->
    exists b, snapshot_assignment n snap (literal_var l) = Some b).
  {
    intros l Hin.
    apply Htotal.
    apply Forall_forall with (x := l) in Hclause_wf;
      assumption.
  }
  assert (Hnotfalse :
    ~ clause_false (snapshot_assignment n snap) c).
  {
    apply Hno_conflict.
    exact Hcinstalled.
  }
  destruct
    (partial_clause_has_true__solver_analysis_and_returns
      (snapshot_assignment n snap) c Hall_assigned Hnotfalse)
    as [l [Hin Htrue]].
  exists l. split; [exact Hin|].
  now apply snapshot_partial_true_rho_true__solver_analysis_and_returns.
Qed.
Lemma coherent_original_cnf_wf__solver_analysis_and_returns :
  forall F n live original_count snap,
    coherent_snapshot F n live original_count snap ->
    cnf_wf n F.
Proof.
  intros F n live original_count snap Hcoherent.
  unfold coherent_snapshot in Hcoherent.
  destruct Hcoherent as [Hn [_ [_ [Hcells [_ Hsound]]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [_ Hrows_wf].
  unfold installed_clauses_sound in Hsound.
  destruct Hsound as [Hprefix _].
  unfold original_prefix_exact in Hprefix.
  destruct Hprefix as [Hprefix _].
  split; [exact Hn|].
  apply Forall_forall.
  intros c HcF.
  assert (Hcinstalled : In c (map dense_decode (snap_rows snap))).
  {
    rewrite <- Hprefix in HcF.
    rewrite <-
      (firstn_skipn (Z.to_nat original_count)
        (map dense_decode (snap_rows snap))).
    apply in_or_app. left. exact HcF.
  }
  apply in_map_iff in Hcinstalled as [row [Hdecode Hrow]].
  subst c.
  apply dense_decode_forall_wf__decide_exit_solver_setup.
  apply Forall_forall with (x := row) in Hrows_wf;
    assumption.
Qed.
Lemma installed_clause_entails__solver_analysis_and_returns :
  forall F original_count installed c,
    installed_clauses_sound F original_count installed ->
    In c installed ->
    entails_clause F c.
Proof.
  intros F original_count installed c Hsound Hcin.
  unfold installed_clauses_sound in Hsound.
  destruct Hsound as [Hprefix Hlearned].
  unfold original_prefix_exact in Hprefix.
  destruct Hprefix as [Hprefix _].
  assert (Hparts :
    In c
      (firstn (Z.to_nat original_count) installed ++
       skipn (Z.to_nat original_count) installed)).
  {
    rewrite firstn_skipn. exact Hcin.
  }
  apply in_app_or in Hparts as [Horiginal | Hlearned_c].
  - rewrite Hprefix in Horiginal.
    intros rho Hmodels.
    apply Forall_forall with (x := c) in Hmodels;
      assumption.
  - apply Forall_forall with (x := c) in Hlearned;
      assumption.
Qed.
Lemma coherent_installed_clause_var_unique__solver_analysis_and_returns :
  forall F n live original_count snap c l1 l2,
    coherent_snapshot F n live original_count snap ->
    In c (map dense_decode (snap_rows snap)) ->
    In l1 c ->
    In l2 c ->
    literal_var l1 = literal_var l2 ->
    l1 = l2.
Proof.
  intros F n live original_count snap c l1 l2
    Hcoherent Hc Hin1 Hin2 Hvar.
  pose proof Hcoherent as Hcoherent'.
  unfold coherent_snapshot in Hcoherent'.
  destruct Hcoherent' as [_ [_ [_ [Hcells _]]]].
  unfold snapshot_cells_wf in Hcells.
  destruct Hcells as [_ Hrows_wf].
  apply in_map_iff in Hc as [row [Hdecode Hrow]].
  subst c.
  eapply dense_decode_unique_var__learning_row_and_scan.
  - rewrite Forall_forall in Hrows_wf.
    exact (Hrows_wf row Hrow).
  - exact Hin1.
  - exact Hin2.
  - exact Hvar.
Qed.
Lemma eval_partial_literal_total_agree__solver_analysis_and_returns :
  forall sigma rho l v b,
    sigma (literal_var l) = Some b ->
    rho (literal_var l) = b ->
    eval_partial_literal sigma l = Some v ->
    eval_literal rho l = v.
Proof.
  intros sigma rho [x|x] v b Hassigned Hagree Heval;
    unfold eval_partial_literal in Heval; simpl in *;
    rewrite Hassigned in Heval;
    inversion Heval; subst v;
    rewrite Hagree; reflexivity.
Qed.
Lemma root_assignment_agrees_at_rank__solver_analysis_and_returns :
  forall rx F n live original_count snap ranks rho x b,
    coherent_snapshot F n live original_count snap ->
    grounded_at (cdcl_view_of_snapshot n snap ranks 0) ->
    closed_levels (cdcl_view_of_snapshot n snap ranks 0) ->
    models rho F ->
    snapshot_assignment n snap x = Some b ->
    ranks x = Some rx ->
    rho x = b.
Proof.
  intro rx.
  induction rx using lt_wf_ind.
  intros F n live original_count snap ranks rho x b
    Hcoherent Hgrounded Hclosed Hmodels Hassigned Hrank.
  pose proof Hgrounded as Hgrounded_x.
  specialize (Hgrounded_x x b Hassigned).
  destruct Hgrounded_x as
    [d [rx' [Hlevel [Hrank' Horigin]]]].
  assert (Hd0 : d = 0).
  {
    unfold closed_levels in Hclosed.
    destruct Hclosed as [_ [Hlevel_bounds _]].
    specialize (Hlevel_bounds x b d Hassigned Hlevel).
    simpl in Hlevel_bounds. lia.
  }
  change (ranks x = Some rx') in Hrank'.
  assert (Hrx : rx' = rx) by congruence.
  subst d. subst rx'.
  destruct Horigin as [[_ Hpositive] |
    [i [_ [Hreason_valid _]]]].
  - lia.
  - unfold reason_valid in Hreason_valid.
    destruct Hreason_valid as
      [b' [d' [rx' [c
        [Hassigned' [Hlevel' [Hrank'' [Hnth [Hsatisfying Hothers]]]]]]]]].
    change (snapshot_assignment n snap x = Some b') in Hassigned'.
    change (ranks x = Some rx') in Hrank''.
    assert (Hb' : b' = b) by congruence.
    assert (Hrx' : rx' = rx) by congruence.
    subst b'. subst rx'.
    simpl in Hnth.
    apply nth_error_In in Hnth.
    assert (Hsound : installed_clauses_sound F original_count
      (map dense_decode (snap_rows snap))).
    {
      pose proof Hcoherent as Hcoherent_sound.
      unfold coherent_snapshot in Hcoherent_sound.
      tauto.
    }
    pose proof
      (installed_clause_entails__solver_analysis_and_returns
        F original_count (map dense_decode (snap_rows snap)) c
        Hsound Hnth rho Hmodels) as Hclause_models.
    destruct Hclause_models as [l [Hin Heval_true]].
    destruct (Z.eq_dec (literal_var l) x) as [Hsame_var|Hother_var].
    + assert (Hl : l = satisfying_literal x b).
      {
        eapply coherent_installed_clause_var_unique__solver_analysis_and_returns;
          try eassumption.
        unfold satisfying_literal.
        destruct b; simpl; exact Hsame_var.
      }
      subst l.
      unfold satisfying_literal in Heval_true.
      destruct b; simpl in Heval_true |- *;
        destruct (rho x); simpl in *; congruence.
    + specialize (Hothers l Hin Hother_var).
      destruct Hothers as
        [Heval_false [dy [ry [Hlevel_y [Hrank_y [_ Hrank_lt]]]]]].
      destruct
        (eval_partial_literal_assigned__bcp_unit_to_assignment
          (snapshot_assignment n snap) l false Heval_false)
        as [b_y Hassigned_y].
      assert (Hagree_y : rho (literal_var l) = b_y).
      {
        eapply H; try eassumption.
      }
      pose proof
        (eval_partial_literal_total_agree__solver_analysis_and_returns
          (snapshot_assignment n snap) rho l false b_y
          Hassigned_y Hagree_y Heval_false) as Heval_false_rho.
      congruence.
Qed.
Lemma root_assignment_agrees__solver_analysis_and_returns :
  forall F n live original_count snap ranks rho x b,
    coherent_snapshot F n live original_count snap ->
    grounded_at (cdcl_view_of_snapshot n snap ranks 0) ->
    closed_levels (cdcl_view_of_snapshot n snap ranks 0) ->
    models rho F ->
    snapshot_assignment n snap x = Some b ->
    rho x = b.
Proof.
  intros F n live original_count snap ranks rho x b
    Hcoherent Hgrounded Hclosed Hmodels Hassigned.
  pose proof Hgrounded as Hgrounded_x.
  specialize (Hgrounded_x x b Hassigned).
  destruct Hgrounded_x as
    [d [rx [Hlevel [Hrank Horigin]]]].
  eapply root_assignment_agrees_at_rank__solver_analysis_and_returns;
    eassumption.
Qed.
Theorem root_conflict_implies_cnf_unsat__solver_analysis_and_returns :
  forall F n live original_count snap ranks,
    coherent_snapshot F n live original_count snap ->
    stable_search_facts n snap ranks 0 ->
    (exists c,
      In c (map dense_decode (snap_rows snap)) /\
      clause_false (snapshot_assignment n snap) c) ->
    cnf_unsat n F.
Proof.
  intros F n live original_count snap ranks
    Hcoherent Hstable Hconflict.
  pose proof Hstable as Hstable'.
  unfold stable_search_facts in Hstable'.
  destruct Hstable' as [Hgrounded [Hclosed _]].
  split.
  - now apply coherent_original_cnf_wf__solver_analysis_and_returns
      with (live := live) (original_count := original_count) (snap := snap).
  - intros rho Hbounded Hmodels.
    destruct Hconflict as [c [Hcin Hfalse]].
    assert (Hsound : installed_clauses_sound F original_count
      (map dense_decode (snap_rows snap))).
    {
      pose proof Hcoherent as Hcoherent_sound.
      unfold coherent_snapshot in Hcoherent_sound.
      tauto.
    }
    pose proof
      (installed_clause_entails__solver_analysis_and_returns
        F original_count (map dense_decode (snap_rows snap)) c
        Hsound Hcin rho Hmodels) as Hclause_models.
    destruct Hclause_models as [l [Hin Heval_true]].
    specialize (Hfalse l Hin).
    destruct
      (eval_partial_literal_assigned__bcp_unit_to_assignment
        (snapshot_assignment n snap) l false Hfalse)
      as [b Hassigned].
    assert (Hagree : rho (literal_var l) = b).
    {
      eapply root_assignment_agrees__solver_analysis_and_returns;
        eassumption.
    }
    pose proof
      (eval_partial_literal_total_agree__solver_analysis_and_returns
        (snapshot_assignment n snap) rho l false b
        Hassigned Hagree Hfalse) as Heval_false.
    congruence.
Qed.
Lemma stable_search_level_bound__solver_analysis_and_returns :
  forall F n live original_count snap ranks logical_dl,
    coherent_snapshot F n live original_count snap ->
    stable_search_facts n snap ranks logical_dl ->
    logical_dl <= n.
Proof.
  intros F n live original_count snap ranks logical_dl Hcoh Hstable.
  pose proof Hcoh as Hcoh'.
  unfold coherent_snapshot in Hcoh'.
  destruct Hcoh' as [Hn0 _].
  unfold stable_search_facts in Hstable.
  destruct Hstable as [_ [Hclosed _]].
  unfold closed_levels in Hclosed.
  destruct Hclosed as [Hdl0 [_ [_ Hdecisions]]].
  change (forall d, 0 < d <= logical_dl ->
    exists! x,
      decision_at
        (cdcl_view_of_snapshot n snap ranks logical_dl) x d)
    in Hdecisions.
  apply Z.nlt_ge.
  intro Hnlt.
  set (levels := map Z.of_nat (seq 1 (Z.to_nat logical_dl))).
  set (variables := map Z.of_nat (seq 0 (Z.to_nat n))).
  assert (Hlevels_nodup : NoDup levels).
  {
    unfold levels.
    apply Injective_map_NoDup.
    - intros a b Hab. now apply Nat2Z.inj.
    - apply seq_NoDup.
  }
  assert (Hlevels_decide :
    Forall
      (fun d => Exists
        (fun x => decision_at
          (cdcl_view_of_snapshot n snap ranks logical_dl) x d)
        variables)
      levels).
  {
    unfold levels.
    apply Forall_forall.
    intros d Hd.
    apply in_map_iff in Hd as [k [<- Hk]].
    apply in_seq in Hk.
    assert (Hd_range : 0 < Z.of_nat k <= logical_dl).
    {
      destruct Hk as [Hk1 Hk2].
      rewrite <- (Z2Nat.id logical_dl) by lia.
      split; lia.
    }
    destruct (Hdecisions (Z.of_nat k) Hd_range) as [x [Hdecision _]].
    pose proof Hdecision as Hdecision'.
    unfold decision_at in Hdecision'.
    destruct Hdecision' as [[b Hb] _].
    change (snapshot_assignment n snap x = Some b) in Hb.
    pose proof
      (snapshot_assignment_some_range__bcp_unit_to_assignment
        n snap x b Hb) as Hxrange.
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
    - exact Hdecision.
  }
  assert (Hlength :
    (List.length variables < List.length levels)%nat).
  {
    unfold variables, levels.
    rewrite !length_map, !length_seq.
    apply Z2Nat.inj_lt; lia.
  }
  destruct (Permutation_pigeonhole_rel
    (fun d x => decision_at
      (cdcl_view_of_snapshot n snap ranks logical_dl) x d)
    Hlevels_decide Hlength)
    as [d [d' [rest [Hperm [x [_ [Hdecision Hdecision']]]]]]].
  pose proof (Permutation_NoDup Hperm Hlevels_nodup) as Hnodup.
  assert (Hdd' : d <> d').
  {
    inversion Hnodup as [|d0 tail Hnotin Htail]; subst.
    intro Heq. subst d'.
    apply Hnotin. left. reflexivity.
  }
  unfold decision_at in Hdecision, Hdecision'.
  destruct Hdecision as [_ [Hlevel _]].
  destruct Hdecision' as [_ [Hlevel' _]].
  congruence.
Qed.
Lemma top_two_negative_second_is_minus_one__solver_analysis_and_returns :
  forall F n a row max1 max2,
    closed_levels a ->
    current_learning_exit_cert F a (dense_decode row) ->
    row_wf n row ->
    top_two_levels_exact a row n max1 max2 ->
    max2 < 0 ->
    max2 = -1.
Proof.
  intros F n a row max1 max2 Hclosed Hlearning Hrow Htop Hnegative.
  unfold top_two_levels_exact in Htop.
  destruct Htop as [[_ [_ Hminus]] |
    [_ [_ [[Hminus _] | [Hprocessed [_ _]]]]]].
  - exact Hminus.
  - exact Hminus.
  - exfalso.
    destruct Hprocessed as [x [Hx [Hcell Hlevel]]].
    pose proof (row_wf_cell_domain n row x Hrow Hx) as Hdomain.
    unfold current_learning_exit_cert, learned_clause_sound in Hlearning.
    destruct Hlearning as [[_ Hfalse] _].
    assert (Hassigned : exists b, assignment a x = Some b).
    {
      destruct Hdomain as [Hneg | [Hzero | Hpos]].
      - assert (Hin : In (Neg x) (dense_decode row)).
        { apply (proj1 (dense_decode_neg n row x Hrow Hx)); exact Hneg. }
        specialize (Hfalse (Neg x) Hin).
        change
          (match assignment a x with
           | None => None
           | Some b => Some (negb b)
           end = Some false) in Hfalse.
        destruct (assignment a x) as [b|] eqn:Hassignment.
        + now exists b.
        + discriminate Hfalse.
      - congruence.
      - assert (Hin : In (Pos x) (dense_decode row)).
        { apply (proj1 (dense_decode_pos n row x Hrow Hx)); exact Hpos. }
        specialize (Hfalse (Pos x) Hin).
        change
          (match assignment a x with
           | None => None
           | Some b => Some b
           end = Some false) in Hfalse.
        destruct (assignment a x) as [b|] eqn:Hassignment.
        + now exists b.
        + discriminate Hfalse.
    }
    destruct Hassigned as [b Hassigned].
    unfold closed_levels in Hclosed.
    destruct Hclosed as [_ [Hlevels _]].
    specialize (Hlevels x b max2 Hassigned Hlevel).
    lia.
Qed.

(** ===== NON-VACUITY WITNESS =====

    Everything above is conditional: IF the precondition holds, THEN the
    verdicts follow.  That is worthless if the precondition is unsatisfiable,
    because then every obligation holds vacuously.  This exhibits a concrete
    instance and discharges the two pure preconditions of cdcl_solver's
    Require, so the contract is known to be non-empty.

    The instance: one variable, one clause [x0], nothing assigned, decision
    level 0 -- exactly the state the solver is meant to start in.  Only the
    mathematical side conditions are modelled; those are the ones that could
    silently contradict one another.  The spatial conjuncts are ordinary array
    ownership and are satisfiable by construction. *)

Definition witness_snap : dense_snapshot :=
  {| snap_values      := [-1];
     snap_reasons     := [-1];
     snap_levels      := [-1];
     snap_rows        := [[1]];
     snap_states      := [2];
     snap_true_counts := [0];
     snap_unassigned  := [1] |}.

Definition witness_F : cnf := [[Pos 0]].

Lemma witness_unassigned :
  forall x, snapshot_assignment 1 witness_snap x = None.
Proof.
  intros x. unfold snapshot_assignment, witness_snap; simpl.
  destruct (0 <=? x) eqn:E1; simpl; [|reflexivity].
  destruct (x <? 1) eqn:E2; simpl; [|reflexivity].
  assert (Hx : x = 0) by lia. subst x. reflexivity.
Qed.

Lemma witness_rows_decode :
  map dense_decode (snap_rows witness_snap) = [[Pos 0]].
Proof. reflexivity. Qed.

(* Stated in exactly the syntactic shape they occur in, so the rewrites below
   match without depending on how far cbn/simpl happens to reduce. *)
Lemma witness_eval_pos0 :
  eval_partial_literal (snapshot_assignment 1 witness_snap) (Pos 0) = None.
Proof.
  unfold eval_partial_literal.
  rewrite (witness_unassigned (literal_var (Pos 0))). reflexivity.
Qed.

Lemma witness_true_count :
  clause_true_count (snapshot_assignment 1 witness_snap) [Pos 0] = 0.
Proof. cbn [clause_true_count]. rewrite witness_eval_pos0. reflexivity. Qed.

Lemma witness_unassigned_count :
  clause_unassigned_count (snapshot_assignment 1 witness_snap) [Pos 0] = 1.
Proof. cbn [clause_unassigned_count]. rewrite witness_eval_pos0. reflexivity. Qed.

Lemma witness_state :
  expected_clause_state (snapshot_assignment 1 witness_snap) [Pos 0] = 2.
Proof.
  unfold expected_clause_state.
  rewrite witness_true_count, witness_unassigned_count. reflexivity.
Qed.

Lemma witness_coherent :
  coherent_snapshot witness_F 1 1 1 witness_snap.
Proof.
  unfold coherent_snapshot.
  split; [lia|].
  split; [lia|].
  split.
  { unfold snapshot_lengths, witness_snap; simpl. repeat split. }
  split.
  { unfold snapshot_cells_wf. split.
    - intros x Hx. unfold var_in_range in Hx.
      assert (Hx0 : x = 0) by lia. subst x.
      unfold witness_snap; simpl.
      split; [left; reflexivity|].
      split.
      + intros _. split; reflexivity.
      + intros Hne. exfalso. apply Hne. reflexivity.
    - unfold witness_snap; simpl.
      (* Forall (row_wf 1) [[1]].  Spelled out rather than [repeat
         constructor], which would pick the leftmost disjunct of
         [1 = -1 \/ 1 = 0 \/ 1 = 1] and get stuck on a false goal. *)
      apply Forall_cons; [|apply Forall_nil].
      unfold row_wf. split; [reflexivity|].
      apply Forall_cons; [|apply Forall_nil].
      right; right; reflexivity. }
  split.
  { intros i Hi. assert (Hi0 : i = 0) by lia. subst i.
    unfold summary_at, clause_summary_ok.
    replace (Znth 0 (map dense_decode (snap_rows witness_snap)) [])
      with [Pos 0] by reflexivity.
    replace (Znth 0 (snap_states witness_snap) 0) with 2 by reflexivity.
    replace (Znth 0 (snap_true_counts witness_snap) 0) with 0 by reflexivity.
    replace (Znth 0 (snap_unassigned witness_snap) 0) with 1 by reflexivity.
    rewrite witness_true_count, witness_unassigned_count, witness_state.
    repeat split. }
  { unfold installed_clauses_sound, original_prefix_exact, witness_F.
    rewrite witness_rows_decode.
    split.
    - split; [reflexivity|].
      split; [reflexivity|].
      repeat constructor. discriminate.
    - simpl. constructor. }
Qed.

Lemma witness_stable :
  stable_search_facts 1 witness_snap (fun _ => None) 0.
Proof.
  unfold stable_search_facts.
  (* stable_search_facts binds the view with a [let], so zeta-reduce before the
     projections can fire. *)
  cbv zeta.
  unfold cdcl_view_of_snapshot.
  (* Unfold the three predicates FIRST: the record projections only appear
     once they are expanded, so reducing before this is a no-op. *)
  unfold grounded_at, closed_levels, frontier_closed,
         current_frontier_supported, decision_at.
  (* Now reduce ONLY the projections.  A bare [simpl] here also unfolds
     witness_snap into its literal, after which witness_unassigned no longer
     matches syntactically. *)
  cbn [assignment level_of reason_of assignment_rank
       installed_clauses current_level].
  split.
  { (* grounded_at: vacuous, nothing is assigned *)
    intros x b Hassigned.
    rewrite witness_unassigned in Hassigned. discriminate. }
  split.
  { split; [lia|].
    split.
    { intros x b d Hassigned _.
      rewrite witness_unassigned in Hassigned. discriminate. }
    split.
    { intros x [[b Hassigned] _].
      rewrite witness_unassigned in Hassigned. discriminate. }
    intros d Hd. lia. }
  { split.
    - intros k Hk. lia.
    - left. reflexivity. }
Qed.

Example cdcl_solver_precondition_satisfiable :
  coherent_snapshot witness_F 1 1 1 witness_snap /\
  stable_search_facts 1 witness_snap (fun _ => None) 0.
Proof. exact (conj witness_coherent witness_stable). Qed.


(* ==========================================================================
   Wave 2 shared vocabulary (design 2026-07-31, section 2).

   Two purely-spatial shared HEADS reused across functions, plus the thin
   per-function wrappers carrying the pure blocks.  Heads stay spatial on
   purpose (ruling A1): the pure facts a given site needs stay visible C
   conjuncts, so core(0) strategy rules can still see them.
   ========================================================================== *)

(** Wave-2 shared head H2: the whole solver state with the variable side and
    the row table EXPLICIT.  Where [solver_state] keys every array on one
    snapshot, this head takes the three variable lists and the rows list as
    parameters, so it also serves mid-update points where the arrays are keyed
    on different snapshots -- decide's flip loop carries
    [snap_values final_snap] beside [snap_reasons snap], which no
    snapshot-keyed bundle can express.  The variable side is the three
    [IntArray.full]s that [variable_arrays_rep] would add (rules 11/12 shred
    the latter to exactly these atoms, so a longhand block spelled either way
    meets this head at the same multiset); the clause side is
    [clause_arrays_explicit_rep].

    Purely spatial by convention (Wave-2 ruling A1): pure facts stay visible
    C conjuncts, or are absorbed by a per-function wrapper such as
    [backtrack_inner_state] below.  Positional convention follows
    [solver_state]: [s], the ten array/size ghosts verbatim, [dl], then the
    four explicit lists in variable-side order values/reasons/levels/rows,
    then the three clause-summary lists.  [v_data] and [cl_data] are local
    [EX] binders exactly as in [solver_state], and the header's [cur_dl] cell
    carries [dl]. *)
Definition solver_explicit_state
    (s values reasons levels states true_counts unassigned row_table
       n live cap dl : Z)
    (vvals : list Z) (vreas : list Z) (vlevs : list Z)
    (rows : list (list Z))
    (cur_states : list Z) (cur_true : list Z) (cur_unassigned : list Z)
    : Assertion :=
  EX (v_data cl_data : Z),
  (sat_header_rep s n live cap dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   IntArray.full values n vvals **
   IntArray.full reasons n vreas **
   IntArray.full levels n vlevs **
   clause_arrays_explicit_rep states true_counts unassigned row_table
     live cap rows cur_states cur_true cur_unassigned).

(** [backtrack]'s inner-loop resting state: the absorbed pure block of the two
    whole-table backtrack annotations [&&] one [solver_explicit_state]
    instance keyed on [current_snap], with the header's [cur_dl] cell carrying
    [back_dl].

    The two variable-being-cleared facts --
    [Znth i (snap_values current_snap) (-1) <> -1] and
    [Znth i (snap_levels current_snap) (-1) > back_dl] -- are deliberately NOT
    here (Wave-2 ruling A4): they stay visible C lines in both blocks, because
    the invariant-to-first-statement entailment consumes them with nothing in
    between, and readability at the program point is their purpose.
    [0 <= j <= live] is not here either: the wrapper serves both the [j]-loop
    invariant and the post-loop Assert, which differ in [j] visibility.

    The tail conjunct ([backtrack_inner]/[clearing_variable] [&&]
    [pending_backjump_rep]) stays longhand in the C blocks: it is the part
    that differs between the two occurrences, so [ranks], [start_snap],
    [start_ranks], [current_ranks], [after_ranks], [last] and [learned] stay
    out of this signature. *)
Definition backtrack_inner_state
    (s : Z) (F : cnf) (original_count : Z)
    (snap conflict_snap current_snap after_snap : dense_snapshot)
    (conflict_ranks : Z -> option nat)
    (conflict_dl back_dl i : Z)
    (values reasons levels states true_counts unassigned row_table
       n live cap : Z)
    (cur_states : list Z) (cur_true : list Z) (cur_unassigned : list Z)
    : Assertion :=
  “ 0 <= i /\ i < n /\
    0 <= back_dl /\ back_dl < conflict_dl /\
    0 <= n /\ n < INT_MAX /\
    0 <= original_count /\ original_count <= live /\
    0 <= live /\ live <= cap /\
    coherent_snapshot F n live original_count snap /\
    stable_search_facts n conflict_snap conflict_ranks conflict_dl /\
    snapshot_lengths n live current_snap /\
    snapshot_cells_wf n live current_snap /\
    snapshot_lengths n live after_snap /\
    snapshot_cells_wf n live after_snap /\
    snap_values after_snap = replace_Znth i (-1) (snap_values current_snap) /\
    snap_reasons after_snap =
      replace_Znth i (-1) (snap_reasons current_snap) /\
    snap_levels after_snap = replace_Znth i (-1) (snap_levels current_snap) /\
    snap_rows after_snap = snap_rows current_snap /\
    snap_rows current_snap = snap_rows snap ” &&
  solver_explicit_state s values reasons levels states true_counts unassigned
    row_table n live cap back_dl
    (snap_values current_snap) (snap_reasons current_snap)
    (snap_levels current_snap) (snap_rows current_snap)
    cur_states cur_true cur_unassigned.

(** [clause_learning]'s footprint with ONE row of the clause table focused.

    This is [learning_state] with [installed_rows_capacity_rep] replaced by
    [installed_row_focus_rep] at [focus] plus the capacity tail: the same
    thirteen header cells, the same [reasons] and [levels] arrays, and the same
    row table, but decomposed so the row at [focus] can be read element by
    element.  Both occurrences sit inside [clause_learning] at a point where the
    code is indexing one row -- the conflict row [wi] in the copy loop, the
    reason row [wj] just before the resolution call -- and both are reached from
    an unfocused [learning_state] with no intervening call, via the strategy
    chain 69 -> 31 -> 3.

    Unlike the other shared heads this one is NOT purely spatial: it carries its
    own pure gate, and in particular [0 <= focus < live].  That is deliberate.
    Rules 3 and 4 -- the focus and refocus rules for the row table -- discharge
    exactly those two side conditions with [infer], so a folded occurrence that
    did not re-emit them would make the chain unfireable at the very program
    points this predicate exists for.  Every other conjunct of the gate is
    [clause_learning]'s own precondition, unchanged, and the rule pair re-emits
    each of them individually at core(1).

    What stays a VISIBLE conjunct of the C annotation, at both occurrences:
    [0 <= wi < live] and [learning_ready_conflict ... wi] -- both keyed on the
    conflict clause, which is the focus only in the copy loop -- the
    working-row facts, and the [Zlength (Znth focus (snap_rows snap) []) = n]
    bridge.  The last one on purpose, so a reader sees at the [wj] site that the
    reason row has the same width as the conflict row.

    [values] and the three clause-summary pointers are parameters whose arrays
    are NOT owned, exactly as in [learning_state]; the row buffer under
    construction is a separate top-level conjunct of the annotation, not part of
    this predicate. *)
Definition learning_focus_state
    (s : Z) (F : cnf)
    (original_count values reasons levels states true_counts unassigned
       row_table n live cap focus row_ptr : Z)
    (snap : dense_snapshot) (ranks : Z -> option nat)
    (logical_dl : Z) : Assertion :=
  EX (v_data cl_data : Z),
  “ 0 < n /\ n < INT_MAX /\
    0 <= original_count /\ original_count <= live /\
    0 <= live /\ live <= cap /\
    0 < logical_dl /\
    0 <= focus /\ focus < live /\
    coherent_snapshot F n live original_count snap /\
    stable_search_facts n snap ranks logical_dl ” &&
  (sat_header_rep s n live cap logical_dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   IntArray.full reasons n (snap_reasons snap) **
   IntArray.full levels n (snap_levels snap) **
   installed_row_focus_rep row_table live focus row_ptr (snap_rows snap) **
   PtrArray.undef_seg row_table live cap).

(** The focused-row head (H1, Wave 2 design section 2).  [solver_state]'s
    footprint at one decision level, with the row table split around ONE
    focused row and every array's contents passed explicitly rather than read
    out of a snapshot: three variable-side lists, the row table, and the three
    clause-summary lists.  Purely spatial by convention A1 -- every pure fact
    of every H1 site, including [0 <= focus < live] and any
    [Zlength (Znth focus rows nil) = n] bridge, stays a visible C conjunct or
    lives in a per-function wrapper.

    Positional convention: [solver_state]'s twelve-scalar prefix
    [s values .. cap dl] verbatim, then [focus] and [row_ptr], then the
    variable-side lists, the row table and the summary lists in footprint
    order.  Shared with [solver_explicit_state] (H2): the two heads differ
    only in [focus]/[row_ptr] and in the clause side being focused instead of
    whole, so a block can switch heads without renaming ghosts.

    Serves bcp's unit-scan quartet and decide's focused arm directly, and
    [backtrack]'s focused row via [backtrack_row_focus_state] below. *)
Definition solver_row_focus_state
    (s values reasons levels states true_counts unassigned row_table
       n live cap dl focus row_ptr : Z)
    (vvals : list Z) (vreas : list Z) (vlevs : list Z)
    (rows : list (list Z))
    (cur_states : list Z) (cur_true : list Z)
    (cur_unassigned : list Z) : Assertion :=
  EX (v_data cl_data : Z),
  (sat_header_rep s n live cap dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   IntArray.full values n vvals **
   IntArray.full reasons n vreas **
   IntArray.full levels n vlevs **
   clause_summaries_explicit_rep states true_counts unassigned live cap
     cur_states cur_true cur_unassigned **
   installed_row_focus_rep row_table live focus row_ptr rows **
   PtrArray.undef_seg row_table live cap).

(** [backtrack]'s focused-row wrapper: the inner clause loop's stable pure
    facts, [&&] one H1 instance keyed on [current_snap] at level [back_dl]
    with row [j] focused.

    The pure block is the SAME fifteen-line block as [backtrack_inner_state]
    (the whole-table wrapper): everything of backtrack's inner spine that does
    not mention [j] or the cleared cell.  Deliberately NOT here, per rulings
    A4 and section-2's H1 invariant, and staying visible C conjuncts instead:
    the two variable-being-cleared facts
    [Znth i (snap_values current_snap) (-1) <> -1] and
    [Znth i (snap_levels current_snap) (-1) > back_dl], the focus bounds
    [0 <= j < live], and the row-length bridge
    [Zlength (Znth j (snap_rows current_snap) nil) = n].

    [current_ranks]/[after_ranks] are not parameters: no spatial atom or
    absorbed fact mentions them, so they stay existentials of the C block,
    pinned by the visible [backtrack_inner] conjunct exactly as before. *)
Definition backtrack_row_focus_state
    (s : Z) (F : cnf) (original_count : Z)
    (snap : dense_snapshot) (conflict_snap : dense_snapshot)
    (current_snap : dense_snapshot) (after_snap : dense_snapshot)
    (conflict_ranks : Z -> option nat)
    (conflict_dl back_dl i j values reasons levels states true_counts
       unassigned row_table n live cap row_ptr : Z)
    (cur_states : list Z) (cur_true : list Z)
    (cur_unassigned : list Z) : Assertion :=
  “ 0 <= i /\ i < n /\
    0 <= back_dl /\ back_dl < conflict_dl /\
    0 <= n /\ n < INT_MAX /\
    0 <= original_count /\ original_count <= live /\
    0 <= live /\ live <= cap /\
    coherent_snapshot F n live original_count snap /\
    stable_search_facts n conflict_snap conflict_ranks conflict_dl /\
    snapshot_lengths n live current_snap /\
    snapshot_cells_wf n live current_snap /\
    snapshot_lengths n live after_snap /\
    snapshot_cells_wf n live after_snap /\
    snap_values after_snap = replace_Znth i (-1) (snap_values current_snap) /\
    snap_reasons after_snap = replace_Znth i (-1) (snap_reasons current_snap) /\
    snap_levels after_snap = replace_Znth i (-1) (snap_levels current_snap) /\
    snap_rows after_snap = snap_rows current_snap /\
    snap_rows current_snap = snap_rows snap ” &&
  solver_row_focus_state s values reasons levels states true_counts unassigned
    row_table n live cap back_dl j row_ptr
    (snap_values current_snap) (snap_reasons current_snap)
    (snap_levels current_snap) (snap_rows current_snap)
    cur_states cur_true cur_unassigned.

(** The conflict-scan prefix fact of bcp's propagation loop: everything the
    loop knows about [conflict] after scanning clauses [0, i) -- if a
    conflict was recorded it is a real falsified clause below [i], and if
    none was, no scanned clause is falsified.  Pure bookkeeping over
    [cur_states]; no strategy rules (Wave-2 design section 2): the two
    implications are the original C conjuncts verbatim, and the folded
    blocks' neighbours re-derive them by unfolding this definition in the
    manual proofs. *)
Definition bcp_conflict_prefix
    (conflict i : Z) (cur_states : list Z) : Prop :=
  (conflict <> -1 ->
     0 <= conflict /\ conflict < i /\ Znth conflict cur_states 0 = 1) /\
  (conflict = -1 ->
     forall k, 0 <= k /\ k < i -> Znth k cur_states 0 <> 1).

(** The single-assignment delta bcp's propagation loop carries: [new_snap]
    is [snap] with exactly variable [bcpvar] assigned by unit clause
    [unitcl] at level [logical_dl] -- the polarity disjunction (which arm of
    the unit literal fired, fixing [value_cell]), the three [replace_Znth]
    cell equations, the unchanged row table, and the view-level
    [assigns_one] bridge.  This Prop deliberately hides the polarity [\/]
    from symexec -- the wave's SINGLE exception to the rule that a
    disjunction must never be hidden (design risk 4), blessed only because
    the disjunction discriminates no spatial atom: both arms share one
    footprint and [value_cell] is a ghost.  If bcp's clause-update Assert
    misbehaves, look here first.  No strategy rules. *)
Definition bcp_assignment_delta
    (n : Z) (snap new_snap : dense_snapshot)
    (ranks ranks1 : Z -> option nat)
    (bcpvar value_cell unitcl logical_dl : Z) (b : bool) : Prop :=
  snap_rows new_snap = snap_rows snap /\
  ((Znth bcpvar (Znth unitcl (snap_rows snap) nil) 0 = 1 /\
      value_cell = 1) \/
   (Znth bcpvar (Znth unitcl (snap_rows snap) nil) 0 = -1 /\
      value_cell = 0)) /\
  snap_values new_snap = replace_Znth bcpvar value_cell (snap_values snap) /\
  snap_reasons new_snap = replace_Znth bcpvar unitcl (snap_reasons snap) /\
  snap_levels new_snap = replace_Znth bcpvar logical_dl (snap_levels snap) /\
  assigns_one
    (cdcl_view_of_snapshot n snap ranks logical_dl)
    (cdcl_view_of_snapshot n new_snap ranks1 logical_dl)
    bcpvar b logical_dl unitcl.

(** bcp's clause-update resting state (Wave-2 design ruling A9): the whole
    solver footprint at the one point inside the propagation loop where row
    [focus] of the clause table is open for the four-way state dispatch.
    Snapshot-keyed on purpose, unlike the H1/H2 heads: the variable side is
    already at [new_snap] (the unit assignment is written back) while the
    row table is still keyed on [snap] -- pinning both snapshots is what
    lets the single use site name the mid-update footprint without the
    three replace_Znth spellings.  The clause-side summaries are explicit
    lists mid-update; the [states] array is split around the focused cell
    ([storeA] + [IntArray.missing_i]), and the row table is split around
    the focused row ([installed_row_focus_rep] + capacity tail).

    Purely spatial (ruling A1): every pure fact of the use site -- including
    [0 <= focus < live] via the visible [0 <= i && i < live], the row-length
    bridge [Zlength (Znth focus (snap_rows snap) nil) = n], and the
    [bcp_clause_scan] / [coherent_snapshot] pair that strategy rule 9 matches
    on -- stays a visible C conjunct.  Rule 9's THIRD pattern atom,
    [IntArray::full (?un_ptr) live un], is NOT visible: it lives inside this
    head and only reappears once rules 79/80 fire at core(1).  That is the
    design's open risk 1, shared with every folded bcp block; it is a
    regeneration question, not something the annotation can fix.  Single use
    (bcp's inner Assert, rules 79/80); that block has exactly ONE line of
    headroom forever (design M6 flag). *)
Definition bcp_clause_update_state
    (s values reasons levels states true_counts unassigned row_table
       n live cap dl focus row_ptr current_state : Z)
    (snap new_snap : dense_snapshot)
    (cur_states : list Z) (cur_true : list Z) (cur_unassigned : list Z)
    : Assertion :=
  EX (v_data cl_data : Z),
  (sat_header_rep s n live cap dl v_data cl_data **
   var_header_rep v_data values reasons levels **
   clause_header_rep cl_data states true_counts unassigned row_table **
   variable_arrays_rep values reasons levels n new_snap **
   StoreIntAsElement.storeA states focus current_state **
   IntArray.missing_i states focus 0 live cur_states **
   IntArray.seg_shape states live cap **
   IntArray.full true_counts live cur_true **
   IntArray.seg_shape true_counts live cap **
   IntArray.full unassigned live cur_unassigned **
   IntArray.seg_shape unassigned live cap **
   installed_row_focus_rep row_table live focus row_ptr (snap_rows snap) **
   PtrArray.undef_seg row_table live cap).
