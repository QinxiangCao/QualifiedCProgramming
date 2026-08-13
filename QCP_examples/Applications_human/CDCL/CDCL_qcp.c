#include "CDCL_qcp.h"

/* ===========================================================================
   A verified CDCL SAT solver.

   WHAT IS PROVED.  `cdcl_solver` returns 1 only with an assignment that models
   the original formula F, 0 only when F is unsatisfiable (with an
   `unsat_terminal` certificate), and -2 when it gives up on its conflict budget
   -- a resource limit asserting nothing about F.  The checked statement is the
   `Require`/`Ensure` on `cdcl_solver` below; termination is not proved.

   GHOST STATE.  A `dense_snapshot` is a pure copy of the seven mutated arrays:
   snap_values/reasons/levels (per variable, length n) and
   snap_states/true_counts/unassigned/rows (per clause, length live).
   `cdcl_view_of_snapshot(n, snap, ranks, dl)` decodes it into the abstract CDCL
   state the specifications use: assignment, per-variable level and antecedent,
   installed clauses, current decision level; the arrays merely realise it.
   Ghost `ranks : Z -> option nat` is the assignment order, present only to
   express "every implied variable was implied by an earlier one" -- acyclicity
   of the implication graph.

   PREDICATES on a view: bcp_ready (no installed clause false),
   propagation_quiescent = decision_ready (none false, none unit),
   model_ready(n, .) (quiescent, all variables assigned),
   learning_ready_conflict(., i) (clause i exists and is false).  On the
   representation: coherent_snapshot(F, n, live, original_count, snap) --
   lengths and cells in range, per-clause summaries agree with the rows,
   installed clauses still contain F; stable_search_facts(n, snap, ranks, dl) --
   grounded_at (assigned => level and reason), closed_levels (levels in [0,dl]),
   frontier_closed (an implied variable's antecedent was assigned earlier).

   CONVENTIONS.  Blocks name state predicates from CDCL_qcp_lib.v, unfolded
   by the strategy rules: `solver_state` (whole footprint, one snapshot),
   `learning_state`, the purely spatial shared heads `solver_explicit_state`
   and `solver_row_focus_state`, and per-function wrappers over them.  A fact
   the next statement consumes stays visible.  A trailing `&& emp` owns nothing.
   `s->v_data->ancient` is the *antecedent* array (clause index that implied a
   variable, -1 for a decision or unassigned one; `reasons` in the annotations);
   `s->cl_data->state[i]` is 0 = satisfied, 1 = falsified, 2 = unit, -k = k
   unassigned literals remain.
   =========================================================================== */
/*@ include strategies "CDCL_qcp.strategies" */
// #define CDCL_DEBUG 1
#ifdef QCPSAT_QCP_ENABLE_OUTPUT
#include <stdio.h>
#ifdef CDCL_DEBUG
#define QCPSAT_QCP_DEBUG_OUTPUT 1
#endif
#endif
#ifdef QCPSAT_QCP_DEBUG_OUTPUT
// FILE* fp;
#endif

/* Set the first n cells of `a` to `value`.  Initialises the per-variable
   arrays. */
void qcpsat_fill_ints(int *a, int n, int value)
/*@ Require 0 <= n && n < INT_MAX && IntArray::undef_full(a, n)
    Ensure IntArray::full(a, n, repeat_Z(value@pre, n))
*/
{
    int i;
    /*@ Inv Assert
        0 <= i && i <= n@pre &&
        0 <= n@pre && n@pre < INT_MAX &&
        a == a@pre && value == value@pre && n == n@pre &&
        IntArray::full(a@pre, i, repeat_Z(value@pre, i)) *
        IntArray::undef_seg(a@pre, i, n@pre)
    */
    for (i = 0; i < n; ++i) {
        a[i] = value;
    }
}

/* Resolve two clauses.  `wi` and `wj` are dense rows (one cell per variable:
   0 absent, 1 the positive literal, -1 the negative).  Returns a fresh row for
   their resolvent, with every complementary pair cancelled.  Caller owns it. */
int* clause_resolution(int* wi, int* wj, sat_data* s)/*@ With (left right : list Z) n
    Require
      0 < n && n < INT_MAX &&
      row_wf(n, left) && row_wf(n, right) &&
      n == s->v_size &&
      IntArray::full(wi, n, left) *
      IntArray::full(wj, n, right)
    Ensure
      row_wf(n, dense_cancel_union(left, right)) &&
      n == s->v_size &&
      resolution_rows_rep(wi, wj, __return, n, left, right)
*/{
    int *res = qcpsat_alloc_row(s->v_size);
    qcpsat_fill_ints(res, s->v_size, 0);
    /*@ Inv Assert
        exists out,
          wi == wi@pre && wj == wj@pre && s == s@pre &&
          0 < n && n < INT_MAX &&
          row_wf(n, left) && row_wf(n, right) &&
          0 <= i && i <= n &&
          n == s->v_size &&
          IntArray::full(wi, n, left) *
          IntArray::full(wj, n, right) *
          IntArray::full(res, n, out) *
          (resolution_prefix(left, right, out, i) && emp)
    */
    for(int i = 0; i < s->v_size; i++){
        if((wi[i] == 1 && wj[i] == -1) || (wi[i] == -1 && wj[i] == 1) ){
            res[i] = 0;
            continue;
        }
        else{
            if(wi[i] != 0) res[i] = wi[i];
            else res[i] = wj[i];
        }
    }
    return res;
}

/* Last-UIP conflict analysis.  `wi` is the index of a clause that is false
   under the current assignment.  Resolves it against the antecedents of its
   literals, most-recently-assigned first, until no current-level propagated
   literal remains -- the surviving current-level literal is the decision
   itself (the last UIP, not the first).  Returns the learned clause as a
   fresh dense row.  The exit certificate `current_learning_exit_cert` records
   that the learned clause is implied by F and false under the assignment. */
int* clause_learning(int wi, sat_data* s)/*@ With (F : cnf) original_count (snap : dense_snapshot)
          (ranks : Z -> option nat) logical_dl values reasons levels states true_counts
          unassigned row_table n live cap
    Require 0 < n && n < INT_MAX && 0 <= original_count && original_count <= live &&
      0 <= wi && wi < live && 0 <= live && live <= cap && 0 < logical_dl &&
      coherent_snapshot(F, n, live, original_count, snap) &&
      stable_search_facts(n, snap, ranks, logical_dl) &&
      learning_ready_conflict(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), wi) &&
      learning_state(s, values, reasons, levels, states, true_counts, unassigned,
        row_table, n, live, cap, logical_dl, snap)
    Ensure exists learned_row, row_wf(n, learned_row) && current_learning_exit_cert(F,
      cdcl_view_of_snapshot(n, snap, ranks, logical_dl), dense_decode(learned_row)) &&
      learning_state(s, values, reasons, levels, states, true_counts, unassigned,
        row_table, n, live, cap, logical_dl, snap) * IntArray::full(__return, n, learned_row)
*/{   //返回学习到的子句
    bool flag = true;
    int* res = qcpsat_alloc_row(s->v_size);
    qcpsat_fill_ints(res, s->v_size, 0);
    /*@ Inv Assert
        exists copied conflict_row_ptr,
        wi == wi@pre && s == s@pre &&
        flag == 1 &&
        0 <= i && i <= n &&
        Zlength(copied) == n &&
        Zlength(Znth(wi, snap_rows(snap), nil)) == n &&
        (forall (k : Z), (0 <= k && k < i) => Znth(k, copied, 0) ==
          Znth(k, Znth(wi, snap_rows(snap), nil), 0)) &&
        (forall (k : Z), (i <= k && k < n) => Znth(k, copied, 0) == 0) &&
        learning_focus_state(s, F, original_count, values, reasons, levels,
          states, true_counts, unassigned, row_table, n, live, cap, wi,
          conflict_row_ptr, snap, ranks, logical_dl) *
        (learning_ready_conflict(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), wi) && emp) *
        IntArray::full(res, n, copied)
    */
    for(int i = 0; i < s->v_size; i++){
        res[i] = s->cl_data->value[wi][i];
    }
    /*@ Inv Assert
        exists working scan,
        wi == wi@pre && s == s@pre &&
        ((flag == 1 && scan == 0) ||
         (flag == 0 && scan == n)) &&
        0 < n && n < INT_MAX &&
        0 <= original_count && original_count <= live &&
        0 <= wi && wi < live &&
        0 <= live && live <= cap &&
        0 < logical_dl &&
        coherent_snapshot(F, n, live, original_count, snap) &&
        stable_search_facts(n, snap, ranks, logical_dl) &&
        IntArray::full(res, n, working) *
        learning_state(s, values, reasons, levels, states, true_counts, unassigned,
          row_table, n, live, cap, logical_dl, snap) *
        (learning_ready_conflict(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), wi) && emp) *
        (learning_loop(F, cdcl_view_of_snapshot(n, snap, ranks, logical_dl), n, working, scan) && emp)
    */
    while(flag){
        #ifdef QCPSAT_QCP_DEBUG_OUTPUT
        // for(int i = 0; i < s->v_size; i++){
        //     if(res[i] > 0){
        //         fprintf(fp, "%d ", i+1);
        //     }
        //     else if(res[i] < 0){
        //         fprintf(fp, "-%d ", i+1);
        //     }
        // }
        // fprintf(fp, "\n");
        #endif
        flag = false;
        /*@ Inv Assert
            exists working scan,
            wi == wi@pre && s == s@pre &&
            0 <= i && i <= n &&
            flag == 0 && scan == i &&
            0 < n && n < INT_MAX &&
            0 <= original_count && original_count <= live &&
            0 <= wi && wi < live &&
            0 <= live && live <= cap &&
            0 < logical_dl &&
            coherent_snapshot(F, n, live, original_count, snap) &&
            stable_search_facts(n, snap, ranks, logical_dl) &&
            IntArray::full(res, n, working) *
            learning_state(s, values, reasons, levels, states, true_counts, unassigned,
              row_table, n, live, cap, logical_dl, snap) *
            (learning_ready_conflict(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), wi) && emp) *
            (learning_loop(F, cdcl_view_of_snapshot(n, snap, ranks, logical_dl), n, working, scan) && emp)
        */
        for(int i = 0; i < s->v_size; i++){
            if(res[i] == 0) continue;
            if(s->v_data->dl[i] == s->cur_dl && s->v_data->ancient[i] != -1){
                //fprintf(fp,"resol var : %d, its ancient : %d\n", i+1,  s->v_data->ancient[i] +1);
                int wj = s->v_data->ancient[i];
                /*@ Assert
                    exists working,
                    wi == wi@pre && s == s@pre &&
                    0 <= i && i < n &&
                    0 <= wj && wj < live && wj == Znth(i, snap_reasons(snap), 0) &&
                    flag == 0 && Znth(i, working, 0) != 0 &&
                    0 < n && n < INT_MAX &&
                    0 <= original_count && original_count <= live &&
                    0 <= wi && wi < live &&
                    0 <= live && live <= cap &&
                    0 < logical_dl &&
                    coherent_snapshot(F, n, live, original_count, snap) &&
                    stable_search_facts(n, snap, ranks, logical_dl) &&
                    IntArray::full(res, n, working) *
                    learning_state(s, values, reasons, levels, states, true_counts,
                      unassigned, row_table, n, live, cap, logical_dl, snap) *
                    (learning_ready_conflict(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), wi) && emp) *
                    (learning_loop(F, cdcl_view_of_snapshot(n, snap, ranks, logical_dl), n, working, i) && emp)
                */
                /*@ Assert
                    exists working reason_row_ptr,
                    wi == wi@pre && s == s@pre &&
                    0 <= i && i < n &&
                    0 <= wi && wi < live &&
                    wj == Znth(i, snap_reasons(snap), 0) &&
                    Zlength(Znth(wj, snap_rows(snap), nil)) == n &&
                    flag == 0 &&
                    Znth(i, working, 0) != 0 &&
                    IntArray::full(res, n, working) *
                    learning_focus_state(s, F, original_count, values, reasons,
                      levels, states, true_counts, unassigned, row_table, n,
                      live, cap, wj, reason_row_ptr, snap, ranks, logical_dl) *
                    (learning_ready_conflict(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), wi) && emp) *
                    (learning_loop(F, cdcl_view_of_snapshot(n, snap, ranks, logical_dl), n, working, i) && emp)
                */
                int* tmp = res;
                res = clause_resolution(res, s->cl_data->value[wj],s);
                qcpsat_free_row(tmp, s->v_size);
                flag = true;
                break;
            }
        }
    }
    return res;
}


/* Backjump level of a learned clause.  Scans `clause` for the two highest
   decision levels among its assigned variables and returns the second highest
   -- the level to which the search must return for the clause to become unit.
   Returns -1 if no literal is assigned, 0 if they all sit at one level. */
int conflict_analysis(int* clause, sat_data* s)/*@ With (row : list Z) (snap : dense_snapshot)
          (ranks : Z -> option nat) logical_dl n v_data levels
    Require
      0 <= n && n < INT_MAX &&
      row_wf(n, row) &&
      clause_vars_assigned(cdcl_view_of_snapshot(n, snap, ranks, logical_dl),
        dense_decode(row)) &&
      conflict_levels_rep(s, clause, n, v_data, levels, row, snap)
    Ensure
      exists max1 max2,
        top_two_levels_exact(cdcl_view_of_snapshot(n, snap, ranks, logical_dl),
          row, n, max1, max2) &&
        ((max1 == -1 && __return == -1) ||
         (max1 != -1 && max2 == -1 && __return == 0) ||
         (max1 != -1 && max2 != -1 && __return == max2)) &&
        conflict_levels_rep(s, clause, n, v_data, levels, row, snap)
*/{   //返回回溯等级
    int max1, max2;     //最大值和第二大值
    max1 = -1;
    max2 = -1;
    /*@ Inv Assert
        clause == clause@pre && s == s@pre &&
        0 <= n && n < INT_MAX &&
        0 <= i && i <= n &&
        row_wf(n, row) &&
        clause_vars_assigned(
          cdcl_view_of_snapshot(n, snap, ranks, logical_dl),
          dense_decode(row)) &&
        n == s->v_size &&
        v_data == s->v_data &&
        levels == v_data->dl &&
        IntArray::full(clause, n, row) *
        IntArray::full(levels, n, snap_levels(snap)) *
        (top_two_levels_prefix(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), n, row, i, max1, max2) && emp)
    */
    for(int i = 0; i < s->v_size; i++){
        if(clause[i] == 0) continue;
        int dl = s->v_data->dl[i];
        if(dl > max1){
            max2 = max1;
            max1 = dl;
        }
        else if(dl > max2 && dl < max1){
            max2 = dl;
        }
    }
    if(max1 == -1){
        #ifdef QCPSAT_QCP_ENABLE_OUTPUT
        printf("error, empty learnt clause");
        #endif
        return -1;
    }
    else if(max2 == -1) return 0;  //只有一个命题变元
    return max2;

}

/* Boolean constraint propagation to a fixed point.  Repeatedly finds a unit
   clause, assigns its one free literal at the current decision level with that
   clause as antecedent, and updates all three per-clause summaries.

   Returns -1 when no clause is false and none is unit (`propagation_quiescent`)
   or the index of a clause that propagation just falsified.  In the second case
   the postcondition also names `last`, the variable whose assignment caused
   every conflict in this batch -- `dense_conflict_batch` relates the state
   before the batch to the state after it. */
int bcp(sat_data* s)/*@ With (F : cnf) original_count (snap : dense_snapshot)
      (ranks : Z -> option nat) logical_dl values reasons levels states true_counts
      unassigned row_table n live cap
    Require 0 <= n && n < INT_MAX && 0 <= original_count && original_count <= live &&
      0 <= live && live <= cap && coherent_snapshot(F, n, live, original_count, snap) &&
      stable_search_facts(n, snap, ranks, logical_dl) &&
      bcp_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) &&
      solver_state(s, values, reasons, levels, states, true_counts, unassigned,
        row_table, n, live, cap, logical_dl, snap)
    Ensure exists snap1 ranks1, coherent_snapshot(F, n, live, original_count, snap1) &&
      stable_search_facts(n, snap1, ranks1, logical_dl) && ((__return == -1 &&
        propagation_quiescent(cdcl_view_of_snapshot(n, snap1, ranks1, logical_dl)) &&
        solver_state(s, values, reasons, levels, states, true_counts, unassigned,
          row_table, n, live, cap, logical_dl, snap1)) ||
       (0 <= __return && __return < live &&
        learning_ready_conflict(cdcl_view_of_snapshot(n, snap1, ranks1, logical_dl), __return) &&
        propagation_result(s, values, reasons, levels, states, true_counts, unassigned,
          row_table, n, live, cap, logical_dl, snap1, ranks1)))
*/{
    int unitcl = -1;
    /*@ Inv Assert
        unitcl == -1 && s == s@pre && 0 <= i && i <= live &&
        0 <= n && n < INT_MAX && 0 <= original_count && original_count <= live &&
        0 <= live && live <= cap &&
        coherent_snapshot(F, n, live, original_count, snap) &&
        stable_search_facts(n, snap, ranks, logical_dl) &&
        unit_scan(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), live, i) &&
        bcp_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) &&
        solver_state(s, values, reasons, levels, states, true_counts,
          unassigned, row_table, n, live, cap, logical_dl, snap)
    */
    for(int i = 0; i < s->cl_size; i++){
        if(s->cl_data->state[i] == 2){
            unitcl = i;
            break;
        }
    }
    if(unitcl == -1) return -1;
    #ifdef QCPSAT_QCP_DEBUG_OUTPUT
    printf("unitcl : %d\n", unitcl+1);
    #endif
    int bcpvar = -1;
    /*@ Assert
        exists unit_row_ptr,
        bcpvar == -1 && s == s@pre && 0 <= unitcl && unitcl < live &&
        Zlength(Znth(unitcl, snap_rows(snap), nil)) == n && 0 <= n && n < INT_MAX &&
        Znth(unitcl, snap_unassigned(snap), 0) == 1 && 0 <= live && live <= cap &&
        0 <= original_count && original_count <= live && coherent_snapshot(F, n, live, original_count, snap) &&
        stable_search_facts(n, snap, ranks, logical_dl) &&
        solver_row_focus_state(s, values, reasons, levels, states, true_counts,
          unassigned, row_table, n, live, cap, logical_dl, unitcl, unit_row_ptr,
          snap_values(snap), snap_reasons(snap), snap_levels(snap), snap_rows(snap),
          snap_states(snap), snap_true_counts(snap), snap_unassigned(snap)) *
        (unit_variable_scan(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), n, live, unitcl, 0) && bcp_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) && emp)
    */
    /*@ Inv Assert
        exists unit_row_ptr candidate,
        ((0 <= bcpvar && bcpvar < n && candidate == bcpvar &&
          Znth(bcpvar, snap_values(snap), -1) == -1 &&
          Znth(bcpvar, Znth(unitcl, snap_rows(snap), nil), 0) != 0) ||
         (bcpvar == -1 && i <= candidate && candidate < n &&
          Znth(candidate, snap_values(snap), -1) == -1 &&
          Znth(candidate, Znth(unitcl, snap_rows(snap), nil), 0) != 0)) &&
        s == s@pre && 0 <= unitcl && unitcl < live && 0 <= i && i <= n &&
        Zlength(Znth(unitcl, snap_rows(snap), nil)) == n && 0 <= n && n < INT_MAX &&
        Znth(unitcl, snap_unassigned(snap), 0) == 1 && 0 <= live && live <= cap &&
        0 <= original_count && original_count <= live && coherent_snapshot(F, n, live, original_count, snap) &&
        stable_search_facts(n, snap, ranks, logical_dl) &&
        solver_row_focus_state(s, values, reasons, levels, states, true_counts,
          unassigned, row_table, n, live, cap, logical_dl, unitcl, unit_row_ptr,
          snap_values(snap), snap_reasons(snap), snap_levels(snap), snap_rows(snap),
          snap_states(snap), snap_true_counts(snap), snap_unassigned(snap)) *
        (unit_variable_scan(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), n, live, unitcl, i) && bcp_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) && emp)
    */
    for(int i = 0; i < s->v_size; i++){
        if(s->v_data->value[i] == -1 && s->cl_data->value[unitcl][i] != 0){
            bcpvar = i;
            break;
        }
    }
    if(bcpvar == -1) {
        qcpsat_fatal(QCPSAT_FATAL_BCP_NO_VARIABLE);
    }
    #ifdef QCPSAT_QCP_DEBUG_OUTPUT
    printf("bcpvar : %d\n", bcpvar+1);
    #endif
    s->cl_data->state[unitcl] = 0;
    s->cl_data->lit_state[unitcl] = 1;
    s->cl_data->unassign_num[unitcl]--;
    /*@ Assert
        exists unit_row_ptr scanned updated_unassigned,
        s == s@pre && 0 <= unitcl && unitcl < live && 0 <= bcpvar && bcpvar < n &&
        Znth(bcpvar, snap_values(snap), -1) == -1 && Znth(unitcl, snap_unassigned(snap), 0) == 1 &&
        Znth(bcpvar, Znth(unitcl, snap_rows(snap), nil), 0) != 0 && 0 <= scanned && scanned < n &&
        Zlength(Znth(unitcl, snap_rows(snap), nil)) == n && 0 <= n && n < INT_MAX &&
        updated_unassigned == replace_Znth(
          unitcl, Znth(unitcl, snap_unassigned(snap), 0) - 1, snap_unassigned(snap)) &&
        updated_unassigned[unitcl] == 0 && 0 <= live && live <= cap &&
        0 <= original_count && original_count <= live && coherent_snapshot(F, n, live, original_count, snap) &&
        stable_search_facts(n, snap, ranks, logical_dl) &&
        solver_row_focus_state(s, values, reasons, levels, states, true_counts,
          unassigned, row_table, n, live, cap, logical_dl, unitcl, unit_row_ptr,
          snap_values(snap), snap_reasons(snap), snap_levels(snap), snap_rows(snap),
          replace_Znth(unitcl, 0, snap_states(snap)),
          replace_Znth(unitcl, 1, snap_true_counts(snap)), updated_unassigned) *
        (unit_variable_scan(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), n, live, unitcl, scanned) && bcp_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) && emp)
    */
    if(s->cl_data->unassign_num[unitcl]!=0) {
        qcpsat_fatal(QCPSAT_FATAL_BCP_UNIT_COUNT);
    }
    /*@ Assert
        exists unit_row_ptr scanned updated_unassigned,
        s == s@pre && 0 <= unitcl && unitcl < live && 0 <= bcpvar && bcpvar < n &&
        Znth(bcpvar, snap_values(snap), -1) == -1 && Znth(unitcl, snap_unassigned(snap), 0) == 1 &&
        Znth(bcpvar, Znth(unitcl, snap_rows(snap), nil), 0) != 0 && 0 <= scanned && scanned < n &&
        Zlength(Znth(unitcl, snap_rows(snap), nil)) == n && 0 <= n && n < INT_MAX &&
        updated_unassigned == replace_Znth(
          unitcl, Znth(unitcl, snap_unassigned(snap), 0) - 1, snap_unassigned(snap)) &&
        updated_unassigned[unitcl] == 0 && 0 <= live && live <= cap &&
        0 <= original_count && original_count <= live && coherent_snapshot(F, n, live, original_count, snap) &&
        stable_search_facts(n, snap, ranks, logical_dl) &&
        solver_row_focus_state(s, values, reasons, levels, states, true_counts,
          unassigned, row_table, n, live, cap, logical_dl, unitcl, unit_row_ptr,
          snap_values(snap), snap_reasons(snap), snap_levels(snap), snap_rows(snap),
          replace_Znth(unitcl, 0, snap_states(snap)),
          replace_Znth(unitcl, 1, snap_true_counts(snap)), updated_unassigned) *
        (unit_variable_scan(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), n, live, unitcl, scanned) && bcp_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) && emp)
    */
    if(s->cl_data->value[unitcl][bcpvar] == 1) {
        s->v_data->value[bcpvar] = 1 ;
        #ifdef QCPSAT_QCP_DEBUG_OUTPUT
        printf("bcpvar = true\n");
        #endif
        }
    else {
        s->v_data->value[bcpvar] = 0;
        #ifdef QCPSAT_QCP_DEBUG_OUTPUT
        printf("bcpvar = false\n");
        #endif
        }
    s->v_data->ancient[bcpvar] = unitcl;
    s->v_data->dl[bcpvar] = s->cur_dl;
    int conflict = -1;
    /*@ Inv Assert
        exists (b : bool) (value_cell : Z) new_snap ranks1 (cur_states : list Z)
               (cur_true : list Z) (cur_unassigned : list Z),
        s == s@pre && 0 <= unitcl && unitcl < live && 0 <= bcpvar && bcpvar < n &&
        Znth(bcpvar, snap_values(snap), -1) == -1 &&
        Znth(bcpvar, Znth(unitcl, snap_rows(snap), nil), 0) != 0 && 0 <= i && i <= live &&
        bcp_conflict_prefix(conflict, i, cur_states) && (i == live || Znth(i, cur_states, 0) != 1) &&
        0 <= n && n < INT_MAX && 0 <= original_count && original_count <= live &&
        0 <= live && live <= cap && coherent_snapshot(F, n, live, original_count, snap) &&
        stable_search_facts(n, snap, ranks, logical_dl) &&
        stable_search_facts(n, new_snap, ranks1, logical_dl) &&
        bcp_assignment_delta(n, snap, new_snap, ranks, ranks1, bcpvar,
          value_cell, unitcl, logical_dl, b) &&
        solver_explicit_state(s, values, reasons, levels, states, true_counts,
          unassigned, row_table, n, live, cap, logical_dl, snap_values(new_snap),
          snap_reasons(new_snap), snap_levels(new_snap), snap_rows(snap),
          cur_states, cur_true, cur_unassigned) *
        (bcp_clause_scan(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), cdcl_view_of_snapshot(n, new_snap, ranks1, logical_dl), bcpvar, b, logical_dl, unitcl, i, unitcl, live, cap, installed_clauses( cdcl_view_of_snapshot(n, snap, ranks, logical_dl)), cur_states, cur_true, cur_unassigned) && bcp_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) && emp)
    */
    for(int i = 0; i < s->cl_size; i++){
        /*@ Assert
            exists (b : bool) (value_cell : Z) new_snap ranks1 (cur_states : list Z)
                   (cur_true : list Z) (cur_unassigned : list Z) row_ptr current_state,
            s == s@pre && 0 <= unitcl && unitcl < live && 0 <= bcpvar && bcpvar < n &&
            Znth(bcpvar, snap_values(snap), -1) == -1 &&
            Znth(bcpvar, Znth(unitcl, snap_rows(snap), nil), 0) != 0 && 0 <= i && i < live &&
            bcp_conflict_prefix(conflict, i, cur_states) && current_state == Znth(i, cur_states, 0) &&
            current_state != 1 && Zlength(Znth(i, snap_rows(snap), nil)) == n &&
            0 <= n && n < INT_MAX && 0 <= original_count && original_count <= live &&
            0 <= live && live <= cap && coherent_snapshot(F, n, live, original_count, snap) &&
            stable_search_facts(n, snap, ranks, logical_dl) &&
            stable_search_facts(n, new_snap, ranks1, logical_dl) &&
            bcp_assignment_delta(n, snap, new_snap, ranks, ranks1, bcpvar,
              value_cell, unitcl, logical_dl, b) &&
            bcp_clause_update_state(s, values, reasons, levels, states, true_counts,
              unassigned, row_table, n, live, cap, logical_dl, i, row_ptr,
              current_state, snap, new_snap, cur_states, cur_true, cur_unassigned) *
            (bcp_clause_scan(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), cdcl_view_of_snapshot(n, new_snap, ranks1, logical_dl), bcpvar, b, logical_dl, unitcl, i, unitcl, live, cap, installed_clauses( cdcl_view_of_snapshot(n, snap, ranks, logical_dl)), cur_states, cur_true, cur_unassigned) && bcp_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) && emp)
        */
        if(s->cl_data->value[i][bcpvar] == 0 || i == unitcl) continue;
        if(s->cl_data->state[i] == 0){
            if((s->cl_data->value[i][bcpvar] == 1 && s->v_data->value[bcpvar] == 1)||
               (s->cl_data->value[i][bcpvar] == -1 && s->v_data->value[bcpvar] == 0)){
                    s->cl_data->lit_state[i]++;
              }
        }
        else if(s->cl_data->state[i] == 1){
            qcpsat_fatal(QCPSAT_FATAL_BCP_UNSAT_CLAUSE);
        }
        else if(s->cl_data->state[i] == 2){
            if((s->cl_data->value[i][bcpvar] == 1 && s->v_data->value[bcpvar] == 1)||
               (s->cl_data->value[i][bcpvar] == -1 && s->v_data->value[bcpvar] == 0)){
                    s->cl_data->state[i] = 0;
                    s->cl_data->lit_state[i]++;
              }
              else {
                s->cl_data->state[i] = 1;
                if(conflict == -1)conflict = i;
              }
        }
        else {
            if((s->cl_data->value[i][bcpvar] == 1 && s->v_data->value[bcpvar] == 1)||
               (s->cl_data->value[i][bcpvar] == -1 && s->v_data->value[bcpvar] == 0)){
                    s->cl_data->state[i] = 0;
                    s->cl_data->lit_state[i] = 1;
              }
              else {
                s->cl_data->state[i] ++;
                if(s->cl_data->state[i] == -1) s->cl_data->state[i] = 2;
              }
        }
        s->cl_data->unassign_num[i]--;
    }
    if(conflict != -1)/*@ Assert
            exists final_snap final_ranks,
            unitcl == unitcl && bcpvar == bcpvar && conflict == conflict && s == s@pre &&
            0 <= conflict && conflict < live && 0 <= n && n < INT_MAX && 0 <= original_count && original_count <= live &&
            0 <= live && live <= cap && coherent_snapshot(F, n, live, original_count, final_snap) &&
            stable_search_facts(n, final_snap, final_ranks, logical_dl) &&
            dense_conflict_batch(cdcl_view_of_snapshot(n, snap, ranks, logical_dl),
              cdcl_view_of_snapshot(n, final_snap, final_ranks, logical_dl), bcpvar) &&
            learning_ready_conflict(cdcl_view_of_snapshot(n, final_snap, final_ranks, logical_dl), conflict) &&
            bcp_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) &&
            solver_state(s, values, reasons, levels, states, true_counts,
              unassigned, row_table, n, live, cap, logical_dl, final_snap)
        */ return conflict;
    else/*@ Assert
            exists final_snap final_ranks,
            unitcl == unitcl && bcpvar == bcpvar && conflict == conflict && s == s@pre &&
            0 <= n && n < INT_MAX && 0 <= original_count && original_count <= live &&
            0 <= live && live <= cap &&
            coherent_snapshot(F, n, live, original_count, final_snap) &&
            stable_search_facts(n, final_snap, final_ranks, logical_dl) &&
            bcp_ready(cdcl_view_of_snapshot(n, final_snap, final_ranks, logical_dl)) &&
            solver_state(s, values, reasons, levels, states, true_counts,
              unassigned, row_table, n, live, cap, logical_dl, final_snap)
        */
        /*@ Given final_ranks */
        return bcp(s) /*@ where F = F, original_count = original_count,
                                ranks = final_ranks */;

}




/* Undo every assignment made above decision level `back_dl`: clear the value,
   level, antecedent and rank of each such variable and restore the per-clause
   summaries.  `pending_backjump_rep` carries, across the whole function, the
   promise that the learned clause is still an implicate of F and that the state
   being unwound is the one conflict analysis looked at. */
void backtrack(int back_dl, sat_data *s)/*@ With (F : cnf) original_count
          (start_snap conflict_snap snap : dense_snapshot)
          (start_ranks conflict_ranks ranks : Z -> option nat)
          conflict_dl last (learned : list literal)
          values reasons levels states true_counts unassigned row_table n live cap
    Require 0 <= back_dl && back_dl < conflict_dl && 0 <= n && n < INT_MAX &&
      0 <= original_count && original_count <= live && 0 <= live && live <= cap &&
      coherent_snapshot(F, n, live, original_count, snap) &&
      stable_search_facts(n, conflict_snap, conflict_ranks, conflict_dl) &&
      backjump_state(s, F, original_count, start_snap, conflict_snap, snap, start_ranks,
        conflict_ranks, ranks, conflict_dl, back_dl, last, learned, values, reasons,
        levels, states, true_counts, unassigned, row_table, n, live, cap)
    Ensure exists final_snap final_ranks,
      coherent_snapshot(F, n, live, original_count, final_snap) &&
      stable_search_facts(n, final_snap, final_ranks, back_dl) &&
      bcp_ready(cdcl_view_of_snapshot(n, final_snap, final_ranks, back_dl)) &&
      solver_state(s, values, reasons, levels, states, true_counts, unassigned,
        row_table, n, live, cap, back_dl, final_snap)
*/{
    /*@ Inv Assert
        exists current_snap current_ranks,
        back_dl == back_dl@pre && s == s@pre && 0 <= i && i <= n &&
        0 <= back_dl && back_dl < conflict_dl && 0 <= n && n < INT_MAX &&
        0 <= original_count && original_count <= live && 0 <= live && live <= cap &&
        coherent_snapshot(F, n, live, original_count, snap) &&
        stable_search_facts(n, conflict_snap, conflict_ranks, conflict_dl) &&
        snapshot_lengths(n, live, current_snap) &&
        snapshot_cells_wf(n, live, current_snap) &&
        snap_rows(current_snap) == snap_rows(snap) &&
        solver_state(s, values, reasons, levels, states, true_counts, unassigned,
          row_table, n, live, cap, back_dl, current_snap) *
        (backtrack_outer(cdcl_view_of_snapshot(n, snap, ranks, conflict_dl), cdcl_view_of_snapshot( n, current_snap, current_ranks, back_dl), n, back_dl, i, live, cap, installed_clauses( cdcl_view_of_snapshot(n, snap, ranks, conflict_dl)), snap_states(current_snap), snap_true_counts(current_snap), snap_unassigned(current_snap)) && pending_backjump_rep( F, cdcl_view_of_snapshot( n, start_snap, start_ranks, conflict_dl), cdcl_view_of_snapshot( n, conflict_snap, conflict_ranks, conflict_dl), cdcl_view_of_snapshot(n, snap, ranks, conflict_dl), back_dl, back_dl, last, learned))
    */
    for(int i = 0; i < s->v_size; i++){
        if(s->v_data->value[i] != -1 && s->v_data->dl[i] > back_dl){
            #ifdef QCPSAT_QCP_DEBUG_OUTPUT
            printf("unpick %d in dl: %d\n", i+1, s->v_data->dl[i]);
            #endif
            /*@ Inv Assert
                exists current_snap current_ranks after_snap after_ranks
                       (cur_states : list Z) (cur_true : list Z) (cur_unassigned : list Z),
                back_dl == back_dl@pre && s == s@pre && 0 <= j && j <= live &&
                Znth(i, snap_values(current_snap), -1) != -1 &&
                Znth(i, snap_levels(current_snap), -1) > back_dl &&
                backtrack_inner_state(s, F, original_count, snap, conflict_snap,
                  current_snap, after_snap, conflict_ranks, conflict_dl, back_dl, i,
                  values, reasons, levels, states, true_counts, unassigned, row_table,
                  n, live, cap, cur_states, cur_true, cur_unassigned) *
                (backtrack_inner(cdcl_view_of_snapshot(n, snap, ranks, conflict_dl), cdcl_view_of_snapshot( n, current_snap, current_ranks, back_dl), cdcl_view_of_snapshot( n, after_snap, after_ranks, back_dl), n, back_dl, i, j, live, cap, installed_clauses( cdcl_view_of_snapshot(n, snap, ranks, conflict_dl)), cur_states, cur_true, cur_unassigned) && pending_backjump_rep( F, cdcl_view_of_snapshot( n, start_snap, start_ranks, conflict_dl), cdcl_view_of_snapshot( n, conflict_snap, conflict_ranks, conflict_dl), cdcl_view_of_snapshot(n, snap, ranks, conflict_dl), back_dl, back_dl, last, learned))
            */
            for(int j = 0; j < s->cl_size; j++){
                /*@ Assert
                    exists current_snap current_ranks after_snap after_ranks
                           (cur_states : list Z) (cur_true : list Z)
                           (cur_unassigned : list Z) row_ptr,
                    back_dl == back_dl@pre && s == s@pre && 0 <= j && j < live &&
                    Znth(i, snap_values(current_snap), -1) != -1 &&
                    Znth(i, snap_levels(current_snap), -1) > back_dl &&
                    Zlength(Znth(j, snap_rows(current_snap), nil)) == n &&
                    backtrack_row_focus_state(s, F, original_count, snap, conflict_snap,
                      current_snap, after_snap, conflict_ranks, conflict_dl, back_dl, i, j,
                      values, reasons, levels, states, true_counts, unassigned, row_table,
                      n, live, cap, row_ptr, cur_states, cur_true, cur_unassigned) *
                    (backtrack_inner(cdcl_view_of_snapshot(n, snap, ranks, conflict_dl), cdcl_view_of_snapshot( n, current_snap, current_ranks, back_dl), cdcl_view_of_snapshot( n, after_snap, after_ranks, back_dl), n, back_dl, i, j, live, cap, installed_clauses( cdcl_view_of_snapshot(n, snap, ranks, conflict_dl)), cur_states, cur_true, cur_unassigned) && pending_backjump_rep( F, cdcl_view_of_snapshot( n, start_snap, start_ranks, conflict_dl), cdcl_view_of_snapshot( n, conflict_snap, conflict_ranks, conflict_dl), cdcl_view_of_snapshot( n, snap, ranks, conflict_dl), back_dl, back_dl, last, learned))
                */
                if(s->cl_data->value[j][i] == 0) continue;
                if(s->cl_data->state[j] == 0){
                    if((s->cl_data->value[j][i] == 1 && s->v_data->value[i] == 1)||
                       (s->cl_data->value[j][i] == -1 && s->v_data->value[i] == 0)){
                            if(s->cl_data->lit_state[j] > 1) s->cl_data->lit_state[j]--;
                            else {
                                s->cl_data->lit_state[j]--;
                                if(s->cl_data->unassign_num[j] > 0)
                                    s->cl_data->state[j] = -s->cl_data->unassign_num[j] - 1;
                                else{
                                    #ifdef QCPSAT_QCP_DEBUG_OUTPUT
                                    printf("backtrack var : %d, get unit clause : %d\n", i+1, j+1);
                                    #endif
                                    s->cl_data->state[j] = 2;
                                }
                            }
                    }

                }
                else if(s->cl_data->state[j] == 1){
                    if((s->cl_data->value[j][i] == 1 && s->v_data->value[i] == 0)||
                       (s->cl_data->value[j][i] == -1 && s->v_data->value[i] == 1)){
                            #ifdef QCPSAT_QCP_DEBUG_OUTPUT
                            printf("backtrack var : %d, get unit clause : %d\n", i+1, j+1);
                            #endif
                            s->cl_data->state[j] = 2;
                       }
                    else {
                        #ifdef QCPSAT_QCP_ENABLE_OUTPUT
                        printf("unexpected error in backtrack");
                        #endif
                    }
                }
                else if(s->cl_data->state[j] == 2){
                    if((s->cl_data->value[j][i] == 1 && s->v_data->value[i] == 0)||
                       (s->cl_data->value[j][i] == -1 && s->v_data->value[i] == 1)){
                            s->cl_data->state[j] = -2;
                       }
                    else {
                        #ifdef QCPSAT_QCP_ENABLE_OUTPUT
                        printf("unexpected error in backtrack");
                        #endif
                    }
                }
                else if(s->cl_data->state[j] < 0){
                    s->cl_data->state[j] --;
                }
                s->cl_data->unassign_num[j]++;
            }
            /*@ Assert
                exists current_snap current_ranks after_snap after_ranks
                       (cur_states : list Z) (cur_true : list Z) (cur_unassigned : list Z),
                back_dl == back_dl@pre && s == s@pre &&
                Znth(i, snap_values(current_snap), -1) != -1 &&
                Znth(i, snap_levels(current_snap), -1) > back_dl &&
                backtrack_inner_state(s, F, original_count, snap, conflict_snap,
                  current_snap, after_snap, conflict_ranks, conflict_dl, back_dl, i,
                  values, reasons, levels, states, true_counts, unassigned, row_table,
                  n, live, cap, cur_states, cur_true, cur_unassigned) *
                (clearing_variable(cdcl_view_of_snapshot(n, snap, ranks, conflict_dl), cdcl_view_of_snapshot( n, current_snap, current_ranks, back_dl), cdcl_view_of_snapshot( n, after_snap, after_ranks, back_dl), n, back_dl, i, live, cap, installed_clauses( cdcl_view_of_snapshot(n, snap, ranks, conflict_dl)), cur_states, cur_true, cur_unassigned) && pending_backjump_rep( F, cdcl_view_of_snapshot( n, start_snap, start_ranks, conflict_dl), cdcl_view_of_snapshot( n, conflict_snap, conflict_ranks, conflict_dl), cdcl_view_of_snapshot(n, snap, ranks, conflict_dl), back_dl, back_dl, last, learned))
            */
            s->v_data->dl[i] = -1;
            s->v_data->value[i] = -1;
            s->v_data->ancient[i] = -1;
        }
    }
}

/* Choose a branching variable.  Picks the lowest-numbered unassigned variable,
   opens a new decision level, and assigns it true with no antecedent (-1).
   Returns its index, or -1 when every variable is assigned -- in which case the
   postcondition upgrades the state to `model_ready`, i.e. a total satisfying
   assignment. */
int decide(sat_data* s)/*@ With (F : cnf) original_count (snap : dense_snapshot)
          (ranks : Z -> option nat) logical_dl values reasons levels states
          true_counts unassigned row_table n live cap
    Require 0 <= n && n < INT_MAX && 0 <= logical_dl && logical_dl <= n &&
      0 <= original_count && original_count <= live && 0 <= live && live <= cap &&
      coherent_snapshot(F, n, live, original_count, snap) &&
      stable_search_facts(n, snap, ranks, logical_dl) &&
      decision_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) &&
      solver_state(s, values, reasons, levels, states, true_counts, unassigned,
        row_table, n, live, cap, logical_dl, snap)
    Ensure (__return == -1 && model_ready(n, cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) &&
        solver_state(s, values, reasons, levels, states, true_counts, unassigned,
          row_table, n, live, cap, logical_dl, snap)) ||
      (exists final_snap final_ranks, 0 <= __return && __return < n &&
        coherent_snapshot(F, n, live, original_count, final_snap) &&
        stable_search_facts(n, final_snap, final_ranks, logical_dl + 1) &&
        bcp_ready(cdcl_view_of_snapshot(n, final_snap, final_ranks, logical_dl + 1)) &&
        solver_state(s, values, reasons, levels, states, true_counts, unassigned,
          row_table, n, live, cap, logical_dl + 1, final_snap))
*/{
    /*@ Inv Assert
        s == s@pre && 0 <= i && i <= n &&
        (forall (x : Z), (0 <= x && x < i) =>
          Znth(x, snap_values(snap), 0) != -1) &&
        0 <= n && n < INT_MAX && 0 <= logical_dl && logical_dl <= n &&
        0 <= original_count && original_count <= live && 0 <= live && live <= cap &&
        coherent_snapshot(F, n, live, original_count, snap) &&
        stable_search_facts(n, snap, ranks, logical_dl) &&
        solver_state(s, values, reasons, levels, states, true_counts,
          unassigned, row_table, n, live, cap, logical_dl, snap) *
        (decision_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) && emp)
    */
    for(int i = 0; i < s->v_size; i++){
        if(s->v_data->value[i] == -1){
            s->v_data->value[i] = 1;
            #ifdef QCPSAT_QCP_DEBUG_OUTPUT
            printf("decide %d = true\n", i+1);
            #endif
            /*@ Inv Assert
                exists final_snap final_ranks (cur_states : list Z)
                       (cur_true : list Z) (cur_unassigned : list Z),
                s == s@pre && 0 <= i && i < n && 0 <= j && j <= live &&
                (forall (x : Z), (0 <= x && x < i) => Znth(x, snap_values(snap), 0) != -1) &&
                0 <= n && n < INT_MAX && 0 <= logical_dl && logical_dl < n &&
                0 <= original_count && original_count <= live && 0 <= live && live <= cap &&
                coherent_snapshot(F, n, live, original_count, snap) &&
                stable_search_facts(n, snap, ranks, logical_dl) &&
                snap_values(final_snap) == replace_Znth(i, 1, snap_values(snap)) &&
                snap_rows(final_snap) == snap_rows(snap) &&
                solver_explicit_state(s, values, reasons, levels, states, true_counts,
                  unassigned, row_table, n, live, cap, logical_dl, snap_values(final_snap),
                  snap_reasons(snap), snap_levels(snap), snap_rows(snap), cur_states,
                  cur_true, cur_unassigned) *
                (decision_update(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), cdcl_view_of_snapshot( n, final_snap, final_ranks, logical_dl + 1), i, j, live, cap, installed_clauses( cdcl_view_of_snapshot(n, snap, ranks, logical_dl)), cur_states, cur_true, cur_unassigned) && decision_ready(cdcl_view_of_snapshot(n, snap, ranks, logical_dl)) && emp)
            */
            for(int j = 0; j < s->cl_size; j++){
                /*@ Assert
                    exists final_snap final_ranks (cur_states : list Z)
                           (cur_true : list Z) (cur_unassigned : list Z) row_ptr,
                    s == s@pre && 0 <= i && i < n && 0 <= j && j < live &&
                    (forall (x : Z), (0 <= x && x < i) => Znth(x, snap_values(snap), 0) != -1) &&
                    0 <= n && n < INT_MAX && 0 <= logical_dl && logical_dl < n &&
                    0 <= original_count && original_count <= live && 0 <= live && live <= cap &&
                    coherent_snapshot(F, n, live, original_count, snap) &&
                    stable_search_facts(n, snap, ranks, logical_dl) &&
                    snap_values(final_snap) == replace_Znth(i, 1, snap_values(snap)) &&
                    snap_rows(final_snap) == snap_rows(snap) &&
                    Zlength(Znth(j, snap_rows(snap), nil)) == n &&
                    solver_row_focus_state(s, values, reasons, levels, states, true_counts,
                      unassigned, row_table, n, live, cap, logical_dl, j, row_ptr,
                      snap_values(final_snap), snap_reasons(snap), snap_levels(snap),
                      snap_rows(snap), cur_states, cur_true, cur_unassigned) *
                    (decision_update(cdcl_view_of_snapshot(n, snap, ranks, logical_dl), cdcl_view_of_snapshot( n, final_snap, final_ranks, logical_dl + 1), i, j, live, cap, installed_clauses( cdcl_view_of_snapshot(n, snap, ranks, logical_dl)), cur_states, cur_true, cur_unassigned) && decision_ready(cdcl_view_of_snapshot( n, snap, ranks, logical_dl)) && emp)
                */
                if(s->cl_data->value[j][i] == 0) continue;
                s->cl_data->unassign_num[j]--;
                if(s->cl_data->state[j] == 0 && s->cl_data->value[j][i] == 1){
                    s->cl_data->lit_state[j]++;
                }
                else if(s->cl_data->state[j] < 0){
                    if(s->cl_data->value[j][i] == 1){
                        s->cl_data->state[j] = 0;
                        s->cl_data->lit_state[j] = 1;
                    }
                    else {
                        s->cl_data->state[j]++;
                        if(s->cl_data->state[j] == -1) s->cl_data->state[j] = 2;
                    }
                }
                else if(s->cl_data->state[j] == 1 || s->cl_data->state[j] == 2){  //decide的时候不应该存在unsat或unit的子句
                    #ifdef QCPSAT_QCP_ENABLE_OUTPUT
                    printf("unexpected error in decide procedure");
                    #endif
                }
            }
            s->cur_dl++;
            s->v_data->dl[i] = s->cur_dl;
            s->v_data->ancient[i] = -1;
            return i;
        }
    }
    return -1;
}

/* The CDCL main loop: propagate, and on a conflict learn a clause, backjump and
   install it; otherwise decide, until either every variable is assigned or a
   conflict is derived at level zero.

   Returns 1 with `models(J, F)`, 0 with `cnf_unsat(n, F)`, or -2 when the clause
   table is full -- a resource limit asserting nothing about F.  `unsat_terminal`
   is the internal certificate for the 0 case, deliberately not published. */
int cdcl_solver(sat_data* s )/*@ With (F : cnf) original_count (snap : dense_snapshot)
      (ranks : Z -> option nat) values reasons levels states true_counts unassigned
      row_table n live cap
    Require cnf_wf(n, F) && 
    solver_input_core(s, F, original_count, snap, ranks,
      values, reasons, levels, states, true_counts, unassigned, row_table, n, live, cap)
    Ensure
      (exists J, __return == 1 && 
      models(J, F) &&
        solver_sat_arm_core(s, F, original_count, snap, ranks, values, reasons,
          levels, states, true_counts, unassigned, row_table, n, live, cap, J)) ||
      (__return == 0 && 
      cnf_unsat(n, F) &&
        solver_unsat_arm_core(s, F, original_count, snap, ranks, values, reasons,
          levels, states, true_counts, unassigned, row_table, n, live, cap)) ||
      (__return == -2 && 
      solver_capacity_exhausted_arm_core(s, F, original_count,
        snap, ranks, values, reasons, levels, states, true_counts, unassigned,
        row_table, n, live, cap))
*/{
    #ifdef QCPSAT_QCP_DEBUG_OUTPUT
    for(int i = 0; i < s->cl_size; i++){
        for(int j = 0; j < s->v_size; j++){
            if(s->cl_data->value[i][j] > 0){
                printf("%d ", j+1);
            }
            if(s->cl_data->value[i][j] < 0){
                printf("-%d ", j+1);
            }
        }
        printf("\n");
    }
    #endif
    s->cur_dl = 0;
    /*@ Inv Assert
        exists current_live current_snap current_ranks logical_dl,
        s == s@pre && 0 <= n && n < INT_MAX &&
        solver_loop_state(s, F, original_count, values, reasons, levels,
          states, true_counts, unassigned, row_table, n, current_live, cap,
          current_snap, current_ranks, logical_dl)
    */
    while(true){
        /*@ Given current_ranks */
        int conflict_cl = bcp(s) /*@ where F = F,
                                           original_count = original_count,
                                           ranks = current_ranks */;
        /*@ Inv Assert
            exists current_live current_snap bcp_ranks logical_dl,
            s == s@pre && 0 <= n && n < INT_MAX &&
            (conflict_cl == -1 || 0 <= conflict_cl) &&
            solver_after_bcp_state(s, F, original_count, values, reasons,
              levels, states, true_counts, unassigned, row_table, n,
              current_live, cap, conflict_cl,
              current_snap, bcp_ranks, logical_dl)
        */
        while(conflict_cl != -1){         //即bcp产生了冲突
            #ifdef QCPSAT_QCP_DEBUG_OUTPUT
            printf("conflict_cl: %d \n",conflict_cl+1);
            #endif
            if(s->cur_dl == 0) return 0;
            #ifdef QCPSAT_QCP_DEBUG_OUTPUT
            // fprintf(fp, "\nvalue state:\n");
            // for(int i = 0; i < s->v_size; i++){
            //     fprintf(fp, "x%d : dl = %d, ancient = %d \n",i+1, s->v_data->dl[i], s->v_data->ancient[i]+1);
            // }
            #endif
            /*@ Given bcp_ranks */
            int* new_cl = clause_learning(conflict_cl, s)
                /*@ where F = F, original_count = original_count,
                          ranks = bcp_ranks */;
            #ifdef QCPSAT_QCP_DEBUG_OUTPUT
            for(int i = 0; i < s->v_size; i++){
                if(new_cl[i] > 0){
                    printf("%d ", i+1);
                }
                else if(new_cl[i] < 0){
                    printf("-%d ", i+1);
                }
            }
            printf("\n");
            #endif
            /*@ Assert
                exists current_live (learned_row : list Z)
                       current_snap bcp_ranks logical_dl,
                s == s@pre && 0 <= n && n < INT_MAX &&
                solver_learning_state(s, F, original_count, values, reasons,
                  levels, states, true_counts, unassigned, row_table, n,
                  current_live, cap, conflict_cl, new_cl, learned_row,
                  current_snap, bcp_ranks, logical_dl)
            */
            if(s->cl_size == s->cl_maxsize){
                #ifdef QCPSAT_QCP_ENABLE_OUTPUT
                printf("too many clause");
                #endif
                return -2;
            }
            else s->cl_size++;
            /*@ Assert
                exists current_snap bcp_ranks logical_dl current_live
                       slot (learned_row : list Z),
                s == s@pre && 0 <= n && n < INT_MAX &&
                solver_install_slot_state(s, F, original_count, values,
                  reasons, levels, states, true_counts, unassigned,
                  row_table, n, current_live, cap, slot, conflict_cl,
                  new_cl, learned_row, current_snap, bcp_ranks,
                  logical_dl)
            */
            s->cl_data->value[s->cl_size-1] = new_cl;
            s->cl_data->state[s->cl_size-1] = 1;
            s->cl_data->lit_state[s->cl_size-1] = 0;
            s->cl_data->unassign_num[s->cl_size-1] = 0;
            /*@ Assert
                exists current_live (learned_row : list Z)
                       current_snap bcp_ranks logical_dl,
                s == s@pre && 0 <= n && n < INT_MAX &&
                solver_installed_row_state(s, F, original_count, values,
                  reasons, levels, states, true_counts, unassigned,
                  row_table, n, current_live, cap, conflict_cl, new_cl,
                  learned_row, current_snap, bcp_ranks, logical_dl)
            */
            /*@ Given learned_row current_snap logical_dl */
            s->cur_dl = conflict_analysis(new_cl, s)
                /*@ where row = learned_row, snap = current_snap,
                          ranks = bcp_ranks, logical_dl = logical_dl */;
            /*@ Assert
                exists current_snap bcp_ranks logical_dl current_live back_dl last
                       (learned_row : list Z) (pre_snap installed_snap : dense_snapshot)
                       (pre_ranks : Z -> option nat),
                s == s@pre && new_cl == new_cl && conflict_cl == conflict_cl &&
                0 <= n && n < INT_MAX && 0 < logical_dl && logical_dl <= n && 0 <= current_live &&
                current_live < cap && 0 <= original_count && original_count <= current_live &&
                coherent_snapshot(F, n, current_live + 1, original_count, installed_snap) &&
                stable_search_facts(n, current_snap, bcp_ranks, logical_dl) &&
                ((back_dl < 0 &&
                  (unsat_terminal(F, cdcl_view_of_snapshot(n, installed_snap, bcp_ranks, logical_dl)) && emp) *
                  solver_state(s, values, reasons, levels, states, true_counts,
                    unassigned, row_table, n, current_live + 1, cap, back_dl, installed_snap)) ||
                 (0 <= back_dl && back_dl < logical_dl &&
                  backjump_state(s, F, original_count, pre_snap, current_snap,
                    installed_snap, pre_ranks, bcp_ranks, bcp_ranks,
                    logical_dl, back_dl, last, dense_decode(learned_row), values,
                    reasons, levels, states, true_counts, unassigned, row_table,
                    n, current_live + 1, cap)))
            */
            if(s->cur_dl < 0) return 0;   //表示unsat
            backtrack(s->cur_dl, s)
                /*@ where F = F, original_count = original_count */;
            /*@ Given final_ranks */
            #ifdef QCPSAT_QCP_DEBUG_OUTPUT
            printf("backtrack res: ");
            // for(int i = 0; i < s->v_size; i++){
            //     if(s->v_data->value[i] == 1){
            //         printf("%d ", i+1);
            //     }
            //     else if(s->v_data->value[i] == 0){
            //         printf("-%d ", i+1);
            //     }
            // }
            printf("\n");
            #endif
            conflict_cl = bcp(s) /*@ where F = F,
                                           original_count = original_count,
                                           ranks = final_ranks */;
        }
        /*@ Assert
            exists current_snap decision_ranks logical_dl current_live,
            conflict_cl == -1 && s == s@pre && 0 <= n && n < INT_MAX &&
            0 <= logical_dl && logical_dl <= n &&
            0 <= original_count && original_count <= current_live &&
            0 <= current_live && current_live <= cap &&
            coherent_snapshot(
              F, n, current_live, original_count, current_snap) &&
            stable_search_facts(
              n, current_snap, decision_ranks, logical_dl) &&
            decision_ready(cdcl_view_of_snapshot(
              n, current_snap, decision_ranks, logical_dl)) &&
            solver_state(s, values, reasons, levels, states, true_counts,
              unassigned, row_table, n, current_live, cap, logical_dl,
              current_snap)
        */
        /*@ Given decision_ranks */
        if(decide(s) /*@ where F = F, original_count = original_count,
                              ranks = decision_ranks */ == -1){
            #ifdef QCPSAT_QCP_DEBUG_OUTPUT
            for(int i = 0; i < s->v_size; i++){
            if(s->v_data->value[i] == 1){
                printf("%d ",i+1);
            }
            else if(s->v_data->value[i] == 0){
                 printf("-%d ",i+1);
            }
            }
        printf("\n");
           #endif
        return 1;
        }

    }

}
