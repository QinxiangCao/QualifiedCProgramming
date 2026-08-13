/* See CDCL_qcp.h: includes stay above the guard for QCP V2.0.5 symexec. */

#include "int_ptr_array2_def.h"

#ifndef QCPSAT_QCP_DEF_H
#define QCPSAT_QCP_DEF_H

/*@ Import Coq Require Import SimpleC.EE.Applications_human.CDCL.CDCL_qcp_lib */

/*@ Extern Coq
      (PtrArray::undef_seg : Z -> Z -> Z -> Assertion)
*/

/*@ Extern Coq (repeat_Z : {A} -> A -> Z -> list A) */
/*@ Extern Coq (dense_snapshot :: *) */
/*@ Extern Coq (cnf :: *) */
/*@ Extern Coq (Assignment :: *) */
/*@ Extern Coq
      (snap_values : dense_snapshot -> list Z)
      (snap_reasons : dense_snapshot -> list Z)
      (snap_levels : dense_snapshot -> list Z)
      (snap_rows : dense_snapshot -> list (list Z))
      (snap_states : dense_snapshot -> list Z)
      (snap_true_counts : dense_snapshot -> list Z)
      (snap_unassigned : dense_snapshot -> list Z)
      (installed_rows_capacity_rep :
        Z -> Z -> Z -> list (list Z) -> Assertion)
      (installed_row_focus_rep :
        Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
      (solver_arrays_rep :
        Z -> Z -> Z -> Z -> Z -> Z -> dense_snapshot -> Assertion)
      (variable_arrays_rep :
        Z -> Z -> Z -> Z -> dense_snapshot -> Assertion)
      (var_header_rep :
        Z -> Z -> Z -> Z -> Assertion)
      (clause_header_rep :
        Z -> Z -> Z -> Z -> Z -> Assertion)
      (sat_header_rep :
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
      (sat_entry_header_rep :
        Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
      (clause_summaries_explicit_rep :
        Z -> Z -> Z -> Z -> Z ->
        list Z -> list Z -> list Z -> Assertion)
      (clause_arrays_explicit_rep :
        Z -> Z -> Z -> Z -> Z -> Z ->
        list (list Z) -> list Z -> list Z -> list Z -> Assertion)
      (resolution_rows_rep :
        Z -> Z -> Z -> Z -> list Z -> list Z -> Assertion)
      (conflict_levels_rep :
        Z -> Z -> Z -> Z -> Z ->
        list Z -> dense_snapshot -> Assertion)
*/

/*@ Extern Coq (literal :: *) */
/*@ Extern Coq (cdcl_view :: *) */
/*@ Extern Coq
      (assignment : cdcl_view -> Z -> option bool)
      (level_of : cdcl_view -> Z -> option Z)
      (reason_of : cdcl_view -> Z -> option Z)
      (installed_clauses : cdcl_view -> cnf)
      (current_level : cdcl_view -> Z)
      (cdcl_view_of_snapshot :
        Z -> dense_snapshot -> (Z -> option nat) -> Z -> cdcl_view)
*/
/*@ Extern Coq
      (rho_of_values : Z -> list Z -> Assignment)
      (models : Assignment -> cnf -> Prop)
      (cnf_wf : Z -> cnf -> Prop)
      (cnf_sat : Z -> cnf -> Prop)
      (cnf_unsat : Z -> cnf -> Prop)
      (row_wf : Z -> list Z -> Prop)
      (dense_decode : list Z -> list literal)
      (dense_cancel_union : list Z -> list Z -> list Z)
*/
/*@ Extern Coq
      (snapshot_lengths : Z -> Z -> dense_snapshot -> Prop)
      (snapshot_cells_wf : Z -> Z -> dense_snapshot -> Prop)
      (coherent_snapshot :
        cnf -> Z -> Z -> Z -> dense_snapshot -> Prop)
      (stable_search_facts :
        Z -> dense_snapshot -> (Z -> option nat) -> Z -> Prop)
*/
/*@ Extern Coq
      (bcp_ready : cdcl_view -> Prop)
      (propagation_quiescent : cdcl_view -> Prop)
      (decision_ready : cdcl_view -> Prop)
      (model_ready : Z -> cdcl_view -> Prop)
      (learning_ready_conflict :
        cdcl_view -> Z -> Prop)
      (fresh_formula :
        cnf -> Z -> Z -> cdcl_view -> Prop)
      (pending_backjump_rep :
        cnf ->
        cdcl_view -> cdcl_view -> cdcl_view ->
        Z -> Z -> Z -> list literal -> Assertion)
      (unsat_terminal :
        cnf -> cdcl_view -> Prop)
*/

/* Public solver-contract vocabulary: the input state, the three result arms,
   and the four components they are composed from.  Same order as in
   CDCL_qcp_lib.v. */
/*@ Extern Coq
      (all_unassigned_cells : Z -> dense_snapshot -> Prop)
      (store_cnf :
        cnf -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        dense_snapshot -> Assertion)
      (uninitialized_Assignment :
        Z -> Z -> Z -> Z -> dense_snapshot -> Assertion)
      (store_Assignment :
        Z -> Z -> Z -> Z -> dense_snapshot -> Assignment -> Assertion)
      (unconstrained_Assignment :
        Z -> Z -> Z -> Z -> dense_snapshot -> Assertion)
      (solver_input_core :
        Z -> cnf -> Z -> dense_snapshot -> (Z -> option nat) ->
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
      (solver_sat_arm_core :
        Z -> cnf -> Z -> dense_snapshot -> (Z -> option nat) ->
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        Assignment -> Assertion)
      (solver_unsat_arm_core :
        Z -> cnf -> Z -> dense_snapshot -> (Z -> option nat) ->
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
      (solver_capacity_exhausted_arm_core :
        Z -> cnf -> Z -> dense_snapshot -> (Z -> option nat) ->
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
*/

/* Helper-contract vocabulary (Tasks 8A-8D).  `solver_state` is the merged
   name that Ruling 1 collapses `decision_state`, `propagation_state` and
   `backjump_restored` into: one Assertion, one export, one rule pair.
   Family convention for the positional signature is
     (s values reasons levels states true_counts unassigned row_table
      n live cap dl : Z) (snap : dense_snapshot). */
/*@ Extern Coq
      (solver_state :
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        dense_snapshot -> Assertion)
      (learning_state :
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        dense_snapshot -> Assertion)
      (backjump_state :
        Z -> cnf -> Z ->
        dense_snapshot -> dense_snapshot -> dense_snapshot ->
        (Z -> option nat) -> (Z -> option nat) -> (Z -> option nat) ->
        Z -> Z -> Z -> list literal ->
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
      (propagation_result :
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        dense_snapshot -> (Z -> option nat) -> Assertion)
*/

/*@ Extern Coq
      (current_learning_exit_cert :
        cnf -> cdcl_view -> list literal -> Prop)
      (clause_vars_assigned : cdcl_view -> list literal -> Prop)
      (backjump_target_profile : cdcl_view -> Z -> list literal -> Prop)
      (top_two_levels_exact :
        cdcl_view -> list Z -> Z -> Z -> Z -> Prop)
      (assigns_one :
        cdcl_view -> cdcl_view -> Z -> bool -> Z -> Z -> Prop)
      (dense_conflict_batch : cdcl_view -> cdcl_view -> Z -> Prop)
      (backjump_clears : cdcl_view -> cdcl_view -> Z -> Prop)
      (dense_summaries_restored :
        Z -> Z -> Z -> dense_snapshot -> dense_snapshot -> Prop)
*/
/*@ Extern Coq
      (unit_scan : cdcl_view -> Z -> Z -> Prop)
      (unit_variable_scan :
        cdcl_view -> Z -> Z -> Z -> Z -> Prop)
      (bcp_clause_scan :
        cdcl_view -> cdcl_view -> Z -> bool ->
        Z -> Z -> Z -> Z -> Z -> Z ->
        cnf -> list Z -> list Z -> list Z -> Prop)
      (decision_update :
        cdcl_view -> cdcl_view -> Z -> Z -> Z -> Z ->
        cnf -> list Z -> list Z -> list Z -> Prop)
      (resolution_prefix :
        list Z -> list Z -> list Z -> Z -> Prop)
      (learning_loop :
        cnf -> cdcl_view -> Z -> list Z -> Z ->
        Prop)
      (top_two_levels_prefix :
        cdcl_view -> Z -> list Z -> Z -> Z -> Z -> Prop)
      (installing_clause :
        cnf -> cdcl_view -> Z -> Z ->
        list Z -> list literal -> Z -> Z -> Prop)
      (backtrack_outer :
        cdcl_view -> cdcl_view -> Z -> Z -> Z -> Z -> Z ->
        cnf -> list Z -> list Z -> list Z -> Prop)
      (backtrack_inner :
        cdcl_view -> cdcl_view -> cdcl_view ->
        Z -> Z -> Z -> Z -> Z -> Z ->
        cnf -> list Z -> list Z -> list Z -> Prop)
      (clearing_variable :
        cdcl_view -> cdcl_view -> cdcl_view ->
        Z -> Z -> Z -> Z -> Z ->
        cnf -> list Z -> list Z -> list Z -> Prop)
*/
/*@ Extern Coq
      (bcp_outcome : cdcl_view -> cdcl_view -> Z -> Z -> Z -> Prop)
      (snapshot_installs :
        list Z -> dense_snapshot -> dense_snapshot -> Prop)
      (pending_backjump_facts :
        cnf -> cdcl_view -> cdcl_view -> cdcl_view -> Z -> Z -> Z ->
        list literal -> Prop)
*/
/*@ Extern Coq
      (solver_loop_state :
        Z -> cnf -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        dense_snapshot -> (Z -> option nat) -> Z -> Assertion)
      (solver_after_bcp_state :
        Z -> cnf -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        Z -> dense_snapshot -> (Z -> option nat) -> Z -> Assertion)
      (solver_learning_state :
        Z -> cnf -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        Z -> Z -> list Z ->
        dense_snapshot -> (Z -> option nat) -> Z -> Assertion)
      (slot_at : Z -> Z -> Prop)
      (solver_install_slot_state :
        Z -> cnf -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        Z -> Z -> Z -> list Z ->
        dense_snapshot -> (Z -> option nat) -> Z -> Assertion)
      (solver_installed_row_state :
        Z -> cnf -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        Z -> Z -> list Z ->
        dense_snapshot -> (Z -> option nat) -> Z -> Assertion)
      (learning_focus_state :
        Z -> cnf -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        Z -> Z ->
        dense_snapshot -> (Z -> option nat) -> Z -> Assertion)
*/
/* Wave-2 shared heads (design 2026-07-31, rulings A1/A2/A4): the whole-table
   explicit head H2 and backtrack's thin wrapper over it.  H2's positional
   convention follows solver_state -- s, the ten array/size ghosts, dl --
   then the four explicit lists (values/reasons/levels/rows), then the three
   clause-summary lists. */
/*@ Extern Coq
      (solver_explicit_state :
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        list Z -> list Z -> list Z -> list (list Z) ->
        list Z -> list Z -> list Z -> Assertion)
      (backtrack_inner_state :
        Z -> cnf -> Z ->
        dense_snapshot -> dense_snapshot -> dense_snapshot ->
        dense_snapshot ->
        (Z -> option nat) -> Z -> Z -> Z ->
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        list Z -> list Z -> list Z -> Assertion)
*/
/* Wave-2 shared vocabulary (design section 2): the focused-row head H1 and
   backtrack's focused-row wrapper.  H1 is purely spatial -- every pure fact
   of every H1 site stays a visible C conjunct or lives in a per-function
   wrapper.  Signature prefix follows solver_state:
     (s values reasons levels states true_counts unassigned row_table
      n live cap dl : Z), then (focus row_ptr : Z), then the explicit
   variable-side lists, the row table and the three summary lists. */
/*@ Extern Coq
      (solver_row_focus_state :
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        list Z -> list Z -> list Z -> list (list Z) ->
        list Z -> list Z -> list Z -> Assertion)
      (backtrack_row_focus_state :
        Z -> cnf -> Z ->
        dense_snapshot -> dense_snapshot -> dense_snapshot -> dense_snapshot ->
        (Z -> option nat) ->
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        Z ->
        list Z -> list Z -> list Z -> Assertion)
*/
/* Wave-2 bcp propagation-loop vocabulary (design section 2, commit 9): two
   Props with no strategy rules -- bcp_conflict_prefix (the conflict-scan
   prefix pair) and bcp_assignment_delta (the single-assignment delta;
   holds the polarity disjunction, the wave's single deliberate
   hidden-disjunction exception, design risk 4) -- plus the single-use
   clause-update head bcp_clause_update_state (rules 79/80), snapshot-keyed
   per ruling A9: variable side at new_snap, row table at snap. */
/*@ Extern Coq
      (bcp_conflict_prefix : Z -> Z -> list Z -> Prop)
      (bcp_assignment_delta :
        Z -> dense_snapshot -> dense_snapshot ->
        (Z -> option nat) -> (Z -> option nat) ->
        Z -> Z -> Z -> Z -> bool -> Prop)
      (bcp_clause_update_state :
        Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z ->
        Z -> dense_snapshot -> dense_snapshot ->
        list Z -> list Z -> list Z -> Assertion)
*/
#endif
