/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko


#ifndef MINISAT_QCP_INTERNAL_H
#define MINISAT_QCP_INTERNAL_H

/* Verified partial correctness starts at the public contracts in
   solver_qcp.h. The proof does not establish termination, allocation-failure
   handling, parser/I/O behavior, solver_delete, or optional configurations.
   Resource failures terminate through the trusted allocation boundary; they
   do not return an inconclusive solver result.

   M is the logical msolver state; suffixes such as Mscan and Manalyzed
   identify execution phases. Spatial frames describe memory, while pure
   invariants constrain the represented formula, trail and watches. ms_stats
   is the 11-counter vector, read through stats_* accessors.

   minisat_qcp_compat.h declares the trusted allocation/reallocation, RNG and
   budget-cast contracts. In particular, clause pointers must have an even
   low bit, growth preserves initialized prefixes, RNG results are
   range-bounded, and budget casts have unconstrained verification results.
   Heuristic updates do not justify a verdict. Native statistics casts are
   proved against their low-32-bit specification. */

#include "minisat_qcp_compat.h"
#include "solver_qcp_def.h"
/*@ include strategies "solver_qcp.strategies" */
#include "solver_qcp.h"

struct clause_t
{
    int size_learnt;
    lit lits[0];
};

/* Derivation output (verbosity level 2). */
#define L_IND "%-*d"
#define L_ind solver_dlevel(s)*3+3,solver_dlevel(s)
#define L_LIT "%sx%d"
#define L_lit(p) lit_sign(p)?"~":"", (lit_var(p) /*@ where(original) */)

/* Interfaces shared by the implementation translation units. */
int minisat_simpdb_props_after_propagation(int value)
/*@ Require emp
    Ensure ((value == INT_MIN && __return == value) ||
            (value != INT_MIN && __return == value - 1)) && emp
 */;

int   clause_size       (clause* c)
/*@ With header
    Require 0 <= header && store(clause_hdr_addr(c), int, header)
    Ensure __return == header / 2 &&
           store(clause_hdr_addr(c), int, header)
 */;

lit*  clause_begin      (clause* c)
/*@ Require emp
    Ensure __return == clause_lits_addr(c) && emp
 */;

int   clause_learnt     (clause* c)
/*@ With header
    Require 0 <= header && store(clause_hdr_addr(c), int, header)
    Ensure __return == header % 2 &&
           store(clause_hdr_addr(c), int, header)
 */;

clause* clause_from_lit (lit l)
/*@ Require 0 <= l && l <= INT_MAX && emp
    Ensure __return == tag_of_lit(l) && emp
 */;

bool    clause_is_lit   (clause* c)
/*@ Require 0 <= c && emp
    Ensure clause_is_lit_result(c, __return) &&
           ((__return == 1 && is_tag(c) == msat_true) ||
            (__return == 0 && is_tag(c) == msat_false)) && emp
 */;

lit     clause_read_lit (clause* c)
/*@ Require 0 <= c && tagged_word(c) &&
            0 <= tag_lit(c) && tag_lit(c) <= INT_MAX && emp
    Ensure __return == tag_lit(c) && emp
 */;

int     solver_dlevel(solver* s)
/*@ With (lim : list Z)
    Require Veci::rep(&(s->trail_lim), lim)
    Ensure __return == Zlength(lim) &&
           (lim == z_nil => __return == 0) &&
           Veci::rep(&(s->trail_lim), lim)
 */;

vecp*   solver_read_wlist     (solver* s, lit l)
/*@ With rdw_wl
    Require 0 <= l && solver_wlists_handle(s, rdw_wl)
    Ensure __return == Vecp::slot(rdw_wl, l) && solver_wlists_handle(s, rdw_wl)
 */;

void order_update(solver* s, int v) // updateorder
/*@ With n (heap0 orderpos0 : list Z) (activity0 : list fp64)
          orderpos_ptr activity_ptr
    Require order_update_pre(n, v, heap0, orderpos0) &&
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos0) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            Veci::rep(&(s->order), heap0)
    Ensure exists heap1 orderpos1,
            order_update_post(n, v, heap0, orderpos0, heap1, orderpos1) &&
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos1) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            Veci::rep(&(s->order), heap1)
 */;

void order_assigned(solver* s, int v)
/*@ Require emp
    Ensure emp
 */;

void order_unassigned(solver* s, int v) // undoorder
/*@ With n (heap0 orderpos0 : list Z) (activity0 : list fp64)
          orderpos_ptr activity_ptr
    Require order_unassigned_pre(n, v, heap0, orderpos0) &&
            Zlength(activity0) == n &&
            store(&(s->size), int, n) *
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos0) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            Veci::rep(&(s->order), heap0)
    Ensure exists heap1 orderpos1,
            order_unassigned_post(n, v, heap0, orderpos0, heap1, orderpos1) &&
            store(&(s->size), int, n) *
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos1) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            Veci::rep(&(s->order), heap1)
 */;

int order_select(solver* s, float random_var_freq) // selectvar
/*@ With n (heap0 orderpos0 assigns0 trail0 : list Z)
          (activity0 : list fp64) qhead
          orderpos_ptr assigns_ptr activity_ptr seed_value seed_shadow
    Require (order_select_pre(n, heap0, orderpos0, assigns0, trail0, qhead) &&
            Zlength(activity0) == n &&
            seed_value == Z_to_fp64(seed_shadow) &&
            1 <= seed_shadow && seed_shadow <= 2147483646 &&
            store(&(s->size), int, n) *
            store(&(s->random_seed), double, seed_value) *
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->assigns), char *, assigns_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos0) *
            CharArray::seg(assigns_ptr, 0, n, assigns0) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            Veci::rep(&(s->order), heap0)) *
            store(&l_Undef, char, 0) * store(&var_Undef, int, -1)
    Ensure (exists heap1 orderpos1 seed_value1 seed_shadow1,
            order_select_post(n, __return, heap0, heap1, orderpos1,
                              assigns0, trail0, qhead) &&
            seed_value1 == Z_to_fp64(seed_shadow1) &&
            1 <= seed_shadow1 && seed_shadow1 <= 2147483646 &&
            store(&(s->size), int, n) *
            store(&(s->random_seed), double, seed_value1) *
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->assigns), char *, assigns_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos1) *
            CharArray::seg(assigns_ptr, 0, n, assigns0) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            Veci::rep(&(s->order), heap1)) *
            store(&l_Undef, char, 0) * store(&var_Undef, int, -1)
 */;

void act_var_bump(solver* s, int v)
/*@ With n (heap0 orderpos0 : list Z) (activity0 : list fp64) orderpos_ptr activity_ptr var_inc0
    Require order_heap_wf(n, heap0, orderpos0) && 0 <= v && v < n &&
            Zlength(activity0) == n &&
            store(&(s->size), int, n) *
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos0) *
            DoubleArray::seg(activity_ptr, 0, n, activity0) *
            Veci::rep(&(s->order), heap0) *
            store(&(s->var_inc), double, var_inc0)
    Ensure exists heap1 orderpos1 (activity1 : list fp64) var_inc1,
            order_heap_wf(n, heap1, orderpos1) &&
            Permutation(heap0, heap1) &&
            (forall (u : Z), (0 <= u && u < n) =>
               (Znth(u, orderpos0, -1) == -1 =>
                Znth(u, orderpos1, -1) == -1)) &&
            (forall (u : Z), (0 <= u && u < n) =>
               (Znth(u, orderpos1, -1) == -1 =>
                Znth(u, orderpos0, -1) == -1)) &&
            Zlength(activity1) == n &&
            store(&(s->size), int, n) *
            store(&(s->orderpos), int *, orderpos_ptr) *
            store(&(s->activity), double *, activity_ptr) *
            IntArray::seg(orderpos_ptr, 0, n, orderpos1) *
            DoubleArray::seg(activity_ptr, 0, n, activity1) *
            Veci::rep(&(s->order), heap1) *
            store(&(s->var_inc), double, var_inc1)
 */;

void act_var_decay(solver* s)
/*@ With var_inc0 var_decay0
    Require store(&(s->var_inc), var_inc0) *
            store(&(s->var_decay), var_decay0)
    Ensure exists var_inc1,
           store(&(s->var_inc), var_inc1) *
           store(&(s->var_decay), var_decay0)
 */;

void act_clause_bump(solver* s, clause *c)
/*@ With (db : dbmap) cla_inc0
    Require learnt_db(db) && In(c, db_words(db)) &&
            msat_fp32_nonnegative(cla_inc0) &&
            Vecp::rep(&(s->learnts), db_words(db)) *
            clause_db_rep(db) *
            store(&(s->cla_inc), cla_inc0)
    Ensure exists cla_inc1,
           msat_fp32_nonnegative(cla_inc1) &&
           Vecp::rep(&(s->learnts), db_words(db)) *
           clause_db_rep(db) *
           store(&(s->cla_inc), cla_inc1)
 */;

void act_clause_decay(solver* s)
/*@ With cla_inc0 cla_decay0
    Require msat_fp32_nonnegative(cla_inc0) &&
            msat_fp32_positive_finite(cla_decay0) &&
            store(&(s->cla_inc), cla_inc0) *
            store(&(s->cla_decay), cla_decay0)
    Ensure exists cla_inc1,
           msat_fp32_nonnegative(cla_inc1) &&
           msat_fp32_positive_finite(cla_decay0) &&
           store(&(s->cla_inc), cla_inc1) *
           store(&(s->cla_decay), cla_decay0)
 */;

clause *clause_new(solver *s, lit *begin, lit *endvar, int learnt)
/*@ clause_new_spec
    With lvl cn_n (cn_F : cnf) (cn_A_arr cn_A_inst : list literal) (cn_M : msolver)
         (cn_words : list Z)
         (cn_sel : Z) (cn_wl : Z) (cn_root : Z)
    Require learnt == cn_sel && 0 <= cn_sel && cn_sel <= 1 &&
            endvar == begin + Zlength(cn_words) * sizeof(int) &&
            2 <= Zlength(cn_words) &&
            2 * Zlength(cn_words) + 1 <= INT_MAX &&
            Forall(lit_wf_c(cn_n), cn_words) &&
            NoDup(map(lit_var_c, cn_words)) &&
            clause_install_pending_cert(cn_n, cn_F, msolver_set_root(cn_M, cn_root), cn_words, solver_selected_is_learnt(cn_sel)) &&
            solver_shape(cn_M) &&
          solver_support_inv(cn_n, cn_F, cn_A_arr, cn_A_inst, cn_root, cn_M) &&
            ms_capacity_root_propagation_pending(cn_M) == 0 &&
            msolver_seed_shadow(cn_M) &&
            solver_rep_levels_wl_at(s, cn_M, cn_wl, lvl) *
            IntArray::seg(begin, 0, Zlength(cn_words), cn_words)
    Ensure clause_new_pending_at_root(s, begin, lvl, cn_n, cn_F, cn_A_arr, cn_A_inst, cn_M, cn_words, __return, cn_sel, cn_wl, cn_root)
 */;

void clause_remove(solver* s, clause* c)
/*@ With n cap wl reasons_ptr (wm : list (list Z))
          (is_learnt : bool) (clause_words stats0 reasons0 : list Z)
    Require clause_remove_pre(s, c, n, cap, wl, reasons_ptr, wm,
                              is_learnt, clause_words, stats0, reasons0)
    Ensure clause_remove_post(s, c, n, cap, wl, reasons_ptr, wm,
                              clause_words, stats0, reasons0)
 */;

lbool clause_simplify(solver* s, clause* c)
/*@ With n (clause_words assigns0 : list Z) (is_learnt : bool)
          assigns_ptr
    Require (0 <= n && n <= INT_MAX && 2 * n <= INT_MAX &&
            Zlength(assigns0) == n && Forall(lbool_cell, assigns0) &&
            Forall(lit_wf_c(n), clause_words) &&
            0 < c && c % 2 == 0 &&
            store(&(s->assigns), assigns_ptr) *
            CharArray::seg(assigns_ptr, 0, n, assigns0) *
            store(clause_hdr_addr(c), int,
                  clause_hdr_word(is_learnt, Zlength(clause_words))) *
            activity_state(c, is_learnt, Zlength(clause_words)) *
            IntArray::seg(clause_lits_addr(c), 0,
                          Zlength(clause_words), clause_words) *
            Veci::rep(&(s->trail_lim), z_nil)) *
            store(&l_True, char, 1) * store(&l_False, char, -1)
    Ensure (clause_simplify_result(clause_words, assigns0, __return) &&
           0 < c && c % 2 == 0 &&
           store(&(s->assigns), assigns_ptr) *
           CharArray::seg(assigns_ptr, 0, n, assigns0) *
           store(clause_hdr_addr(c), int,
                 clause_hdr_word(is_learnt, Zlength(clause_words))) *
           activity_state(c, is_learnt, Zlength(clause_words)) *
           IntArray::seg(clause_lits_addr(c), 0,
                         Zlength(clause_words), clause_words) *
           Veci::rep(&(s->trail_lim), z_nil)) *
            store(&l_True, char, 1) * store(&l_False, char, -1)
 */;

bool enqueue(solver* s, lit l, clause* reason)
/*@ With asg lvl n cap qtail l0
          (assigns levels0 reasons0 trail lim : list Z)
    Require (l == l0 &&
            enqueue_state_at(s, asg, lvl, n, cap, qtail,
                             assigns, levels0, reasons0, trail, lim) &&
            enqueue_input(n, l0, qtail, assigns, levels0,
                          reasons0, trail)) *
            store(&l_Undef, char, 0) * store(&true, int, 1)
    Ensure (enqueue_post_at(s, asg, lvl, l0, reason,
                           n, cap, qtail, __return,
                           assigns, levels0, reasons0, trail, lim)) *
            store(&l_Undef, char, 0) * store(&true, int, 1)
 */;

void solver_analyze(solver* s, clause* c, veci* learnt)
/*@ With (anz_n : Z) (anz_F : cnf) (anz_A_arr : list literal)
          (K : solver_propagation_context) (M : msolver) anz_focus
          (C : clause) levels_ptr anz_wl
    Require (solver_analyze_pre(
              s, c, learnt, levels_ptr, anz_n, anz_F, anz_A_arr, K, M, anz_focus,
              C, anz_wl)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
    Ensure (solver_analyze_post(
             s, learnt, levels_ptr, anz_n, anz_F, anz_A_arr, K, M, anz_focus, anz_wl)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
 */;

clause *solver_propagate(solver* s)

/*@ With (n : Z) (F : cnf) (A_arr : list literal)
         (K : solver_propagation_context) (M0 : msolver)
         assigns_entry levels_entry wlists_entry
    Require (solver_propagation_inv(n, F, A_arr, K, M0) &&
              msolver_seed_shadow(M0) &&
              solver_rep_assigns_levels_at(s, M0, assigns_entry, levels_entry, wlists_entry)) *
            store(&l_Undef, char, 0) * store(&true, int, 1)
    Ensure (((__return == 0 && exists (propagation_result : msolver),
              solver_propagation_inv(n, F, A_arr, K, propagation_result) &&
              propagation_caller_frame(M0, propagation_result) &&
              minisat_propagation_reuse_live(M0, propagation_result) &&
              msolver_seed_shadow(propagation_result) && mt_qhead(ms_core(propagation_result)) == ms_qtail(propagation_result) &&
              solver_rep_assigns_levels_at(s, propagation_result, assigns_entry, levels_entry, wlists_entry)) ||
             (__return != 0 && mt_qhead(ms_core(M0)) < ms_qtail(M0) &&
              exists (propagation_result : msolver) result_focus (result_clause : clause),
              propagation_cancel_ready(n, F, A_arr, K, propagation_result, result_focus) &&
              propagation_caller_frame(M0, propagation_result) &&
              (minisat_base_watch_completed(M0) => minisat_watch_conflict_ready(n, propagation_result)) &&
              minisat_resident_false_clause(propagation_result) && msolver_seed_shadow(propagation_result) &&
              propagation_conflict_cert(n, F, propagation_result, result_clause) && conflict_ptr_denotes(propagation_result, __return, result_clause) &&
              solver_rep_assigns_levels_at(s, propagation_result, assigns_entry, levels_entry, wlists_entry)))) *
            store(&l_Undef, char, 0) * store(&true, int, 1)
 */;

void solver_reducedb(solver* s)
/*@ With levels_ptr wl n (F : cnf) (A_arr A_inst : list literal)
         (M : msolver)
    Require solver_reducedb_pre_at(
              s, levels_ptr, n, F, A_arr, A_inst, M, wl)
    Ensure solver_reducedb_post_at(
             s, levels_ptr, n, F, A_arr, A_inst, M, wl)
 */;


#endif
