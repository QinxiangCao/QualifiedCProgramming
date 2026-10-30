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

#ifndef solver_h
#define solver_h

#include "minisat_qcp_compat.h"
#include "vec_qcp.h"

// Simple types:

// does not work for c++
typedef int  bool;
extern const bool  true;
extern const bool  false;

typedef int                lit;
typedef char               lbool;

#ifdef _WIN32
typedef signed __int64     uint64;   // compatible with MS VS 6.0
#else
typedef unsigned long long uint64;
#endif

extern const int   var_Undef;
extern const lit   lit_Undef;

extern const lbool l_Undef;
extern const lbool l_True;
extern const lbool l_False;

/*@ Extern Coq
      (literal :: *)
      (cnf :: *)
      (msolver :: *)
      (valuation :: *)
 */
/*@ Extern Coq
      (lit_neg_c : Z -> Z)
      (lit_var_c : Z -> Z)
      (lit_sign_c : Z -> Z)
      (solver_simplify_post_at : Z -> Z -> cnf -> list literal -> msolver -> Z -> Z -> Z -> Assertion)
      (solver_clauses_rep : Z -> list Z -> Assertion)
      (solver_size_cell : Z -> Z -> Assertion)
      (solver_conflict_count_cell : Z -> Z -> Assertion)
 */

/*@ Extern Coq
      (ms_size : msolver -> Z)
      (ms_cap : msolver -> Z)
      (ms_model : msolver -> list Z)
      (model_is_total : list Z -> Prop)
      (models : valuation -> cnf -> Prop)
      (rho_of_model : list Z -> valuation)
      (assumptions_true_under : valuation -> list literal -> Prop)
      (cnf_unsat : Z -> cnf -> Prop)
      (cnf_with_units : cnf -> list literal -> cnf)
      (solver_rep_wl : Z -> msolver -> Z -> Assertion)
      (assumptions_array : Z -> Z -> Z -> list literal -> Assertion)
      (solver_public_query_entry : Z -> cnf -> msolver -> Prop)
      (solver_query_reentry : Z -> cnf -> msolver -> Prop)
      (solver_query_reuse_guard : msolver -> Prop)
      (solver_simplify_pre_at : Z -> Z -> cnf -> list literal -> msolver -> Z -> Z -> Assertion)
      (msolver_seed_shadow : msolver -> Prop)
      (solver_query_ready : Z -> cnf -> msolver -> Prop)
      (solver_assumptions_entry_ready : list literal -> msolver -> Prop)
      (cnf_nil : cnf)
      (solver_normal_root : Z -> cnf -> msolver -> Prop)
      (solver_rep_growable : Z -> msolver -> Assertion)
      (solver_query_watch_ready : msolver -> Prop)
      (minisat_watch_completed : msolver -> Prop)
      (solver_base_recovery : Z -> cnf -> msolver -> Prop)
 */

lit  toLit   (int v)
/*@ Require 0 <= v && v + v <= INT_MAX && emp
    Ensure __return == v + v && emp
 */;
lit  lit_neg (lit l)
/*@ bounded
    With lit_bound_n
    Require 0 <= l && l < 2 * lit_bound_n && 0 <= lit_bound_n &&
            2 * lit_bound_n <= INT_MAX && emp
    Ensure __return == lit_neg_c(l) &&
           0 <= __return && __return < 2 * lit_bound_n && emp
 */
/*@ original
    Require 0 <= l && l <= INT_MAX && emp
    Ensure __return == lit_neg_c(l) && emp
 */
/*@ sentinel
    Require (0 - 2) <= l && l <= INT_MAX && emp
    Ensure __return == lit_neg_c(l) && emp
 */;
int  lit_var (lit l)
/*@ bounded_index
    With lv_bound_n
    Require 0 <= l && l < 2 * lv_bound_n && 0 <= lv_bound_n &&
            2 * lv_bound_n <= INT_MAX && emp
    Ensure __return == lit_var_c(l) &&
           0 <= __return && __return < lv_bound_n && emp
 */
/*@ zero_index
    With lv_asg (lv_assigns : list Z)
    Require 0 <= l && l < 2 * Zlength(lv_assigns) &&
            2 * Zlength(lv_assigns) <= INT_MAX &&
            Znth(lit_var_c(l), lv_assigns, 0) == 0 &&
            store(pointer_offset(lv_asg, lit_var_c(l), char),
                  char, Znth(lit_var_c(l), lv_assigns, 0)) *
            CharArray::missing_i(lv_asg, lit_var_c(l), 0,
                                 Zlength(lv_assigns), lv_assigns)
    Ensure __return == lit_var_c(l) &&
           0 <= __return && __return < Zlength(lv_assigns) &&
           lv_assigns[__return - 0] == 0 &&
           store(pointer_offset(lv_asg, __return, char),
                 char, lv_assigns[__return - 0]) *
           CharArray::missing_i(lv_asg, __return, 0,
                                Zlength(lv_assigns), lv_assigns)
 */
/*@ original
    Require 0 <= l && l <= INT_MAX && emp
    Ensure __return == lit_var_c(l) && emp
 */;
int  lit_sign(lit l)
/*@ Require 0 <= l && l <= INT_MAX && emp
    Ensure __return == lit_sign_c(l) && emp
 */;

// Public interface:

/* Client protocol: solver_new -> solver_setnvars* -> solver_addclause* ->
   [solver_simplify] -> solver_solve*. Before a nonempty assumptions query, drain root propagation
   with a successful solver_simplify call (or supply an already drained state).
   Empty-assumption queries let search propagate.

   A false simplify result proves the formula UNSAT. Its post does not export
   solver_query_watch_ready, which both solve contracts and the incremental
   addclause, simplify and setnvars contracts require, so these contracts
   cover no later call to them. main_qcp.c, like upstream main.c, returns
   that result as an lbool, so false reaches main as l_Undef rather than
   l_False and main still calls solver_solve. Natively that solve finds the
   root conflict again and reports UNSAT, but the call is outside these specs.

   addclause, simplify and solve return Boolean results. Allocation failure or
   unrepresentable capacity terminates with an error diagnostic; it cannot
   report a SAT/UNSAT verdict. This native failure behavior is outside Rocq's
   partial-correctness guarantee for normal returns.

   SAT exports a total model and query readiness. A solve UNSAT result exports
   watch readiness OR base-formula UNSAT; only the former supports a later
   query. The live decision level is zero after a query, but the stored
   assumption root may be stale. Do not require that stored field to be zero.

   setnvars returns void and establishes max(old size, requested size).
   Existing literal, clause and doubled-capacity bounds remain in the specs.
   Growth tries the upstream geometric request, then a strictly smaller
   minimum once; a batch retains earlier successful larger allocations.
 */

/* Ghost vocabulary (definitions are in solver_qcp_model.v and
   solver_qcp_lib.v; SAT notions are in Rocq/cdcllib):
     M : msolver ties struct fields to logical contents; ms_core(M) is the
       assignment and decision-level trail, ms_prob(M) and ms_learnt(M) are
       address/clause databases, and ms_model(M) is the output vector.
     solver_incremental_ownership_at owns the solver, growth slack, seed
       shadow and capacity bounds. Pure invariants separately constrain its
       contents.
     With the public contracts' zero pending flag, solver_update_ready
       describes the strong assuming invariant at decision level 0;
       solver_query_watch_ready requires watcher completeness.
     solver_query_ready also requires a drained root queue and implies
       solver_public_query_entry.
     cnf_with_units(F, A) adds the temporary assumptions to F. cnf_unsat
       includes formula well-formedness. assumptions_array connects a
       caller-owned packed-literal range to its logical literals.
 */

/*@ Extern Coq
      (dbmap :: *)
 */
/*@ Extern Coq
      (solver_update_ready : Z -> cnf -> list literal -> msolver -> Prop)
      (solver_incremental_ownership_at : Z -> msolver -> Assertion)
      (ms_capacity_root_propagation_pending : msolver -> Z)
      (ms_prob : msolver -> dbmap)
      (db_words : dbmap -> list Z)
      (ms_stats : msolver -> list Z)
      (stats_conflicts : list Z -> Z)
      (cnf_add_clause : cnf -> list Z -> cnf)
      (lit_wf_c : Z -> Z -> Prop)
      (Forall : {A} -> (A -> Prop) -> list A -> Prop)
      (Z::max : Z -> Z -> Z)
 */

/*@ Extern Coq
      (mtrail :: *)
 */
/*@ Extern Coq
      (ms_core : msolver -> mtrail)
      (mt_lim : mtrail -> list Z)
      (ms_root_level : msolver -> Z)
      (solver_shape : msolver -> Prop)
      (solver_support_inv : Z -> cnf -> list literal -> list literal -> Z -> msolver -> Prop)
      (addclause_support_post_at : Z -> Z -> Z -> cnf -> list literal -> list literal -> msolver -> list Z -> Z -> Assertion)
 */

struct solver_t;
typedef struct solver_t solver;

/* Allocation succeeds by the trusted allocator contract. */
extern solver* solver_new(void)
/*@ solver_new_spec
    Require emp
    Ensure __return != 0 &&
           (exists (M : msolver),
              ms_size(M) == 0 && ms_cap(M) == 0 &&
              solver_update_ready(0, cnf_nil, nil, M) &&
              solver_query_watch_ready(M) &&
              ms_capacity_root_propagation_pending(M) == 0 &&
              solver_incremental_ownership_at(__return, M) &&
              solver_normal_root(0, cnf_nil, M))
 */;
/* Uncontracted destructor; outside the verified configuration. */
extern void    solver_delete(solver* s);

extern bool    solver_addclause(solver* s, lit* begin, lit* endvar)
/*@ addclause_spec
    With (ac_F : cnf) (ac_A_arr ac_A_inst : list literal) (ac_M : msolver)
         (ac_n : Z) (ac_input : list Z)
    Require (0 <= ac_n && ac_n <= Z::max(ms_cap(ac_M), INT_MAX / 4) &&
            2 * ms_cap(ac_M) <= INT_MAX &&
            endvar == begin + Zlength(ac_input) * sizeof(int) &&
            2 * Zlength(ac_input) + 1 <= INT_MAX &&
            Forall(lit_wf_c(ac_n), ac_input) &&
            solver_shape(ac_M) &&
          solver_support_inv(ms_size(ac_M), ac_F, ac_A_arr, ac_A_inst, 0, ac_M) &&
            ms_capacity_root_propagation_pending(ac_M) == 0 &&
            Zlength(mt_lim(ms_core(ac_M))) == 0 &&
            msolver_seed_shadow(ac_M) &&
            solver_rep_growable(s, ac_M) *
            IntArray::seg(begin, 0, Zlength(ac_input), ac_input)) *
            store(&l_Undef, char, 0) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
    Ensure ((__return == 0 || __return == 1) &&
            addclause_support_post_at(s, begin, ac_n, ac_F, ac_A_arr,
                             ac_A_inst, ac_M, ac_input, __return)) *
            store(&l_Undef, char, 0) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
 */

;
/* The general simplify postcondition stays folded to avoid splitting
   solver_search during symbolic execution. */
extern bool    solver_simplify(solver* s)
/*@ solver_simplify_spec
    With (smp_n : Z) (smp_F : cnf) (smp_A_arr : list literal)
         (M : msolver) (levels_ptr smp_wl : Z)
    Require (solver_simplify_pre_at(
              s, smp_n, smp_F, smp_A_arr, M, levels_ptr, smp_wl)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&true, int, 1) * store(&false, int, 0)
    Ensure (((__return == 0 || __return == 1) && solver_simplify_post_at(
             s, smp_n, smp_F, smp_A_arr, M, levels_ptr, __return, smp_wl))) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&true, int, 1) * store(&false, int, 0)
 */

;
/* solver_query_watch_ready at entry discharges the general spec's reuse
   guard.

   On SAT, ms_model contains n cells, each 1 (true) or -1 (false), and
   rho_of_model reads them as a total valuation.

   assumptions_array owns [begin, endvar) and bounds its literals by n. Even
   an empty range requires a valid, int-aligned begin address; NULL satisfies
   this condition. */
extern bool    solver_solve(solver* s, lit* begin, lit* endvar)
/*@ solver_solve_spec
    With (solve_wl : Z) (n : Z) (F : cnf) (A_arr : list literal) (M : msolver)
    Require (solver_update_ready(n, F, nil, M) &&
            ms_capacity_root_propagation_pending(M) == 0 &&
            solver_query_watch_ready(M) &&
            solver_assumptions_entry_ready(A_arr, M) &&
            msolver_seed_shadow(M) &&
            solver_rep_wl(s, M, solve_wl) *
            assumptions_array(n, begin, endvar, A_arr)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
    Ensure (assumptions_array(n, begin, endvar, A_arr) *
           ((__return == 1 &&
             (exists (Msat : msolver),
                ms_size(Msat) == n &&
                Zlength(ms_model(Msat)) == n &&
                model_is_total(ms_model(Msat)) &&
                models(rho_of_model(ms_model(Msat)), F) &&
                assumptions_true_under(rho_of_model(ms_model(Msat)), A_arr) &&
                solver_query_ready(n, F, Msat) &&
                msolver_seed_shadow(Msat) &&
                ms_cap(Msat) == ms_cap(M) &&
                (solver_query_reuse_guard(M) => minisat_watch_completed(Msat)) &&
                solver_rep_wl(s, Msat, solve_wl))) ||
            (__return == 0 &&
             (exists (Munsat : msolver),
                ms_size(Munsat) == n &&
                cnf_unsat(n, cnf_with_units(F, A_arr)) &&
                ms_cap(Munsat) == ms_cap(M) &&
                (solver_query_reuse_guard(M) =>
                  solver_base_recovery(n, F, Munsat) &&
                  solver_query_reentry(n, F, Munsat) &&
                  msolver_seed_shadow(Munsat)) &&
                solver_rep_wl(s, Munsat, solve_wl))) )) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
 */

;

extern int     solver_nvars(solver* s)
/*@ solver_nvars_spec
    With n
    Require solver_size_cell(s, n)
    Ensure __return == n && solver_size_cell(s, n)
 */

;
/* solver_nclauses counts resident problem clauses, not clauses in the input
   F: normalization and root simplification can change the count. */
extern int     solver_nclauses(solver* s)
/*@ solver_nclauses_spec
    With (l : list Z)
    Require solver_clauses_rep(s, l)
    Ensure __return == Zlength(l) && solver_clauses_rep(s, l)
 */

;

extern int     solver_nconflicts(solver* s)
/*@ solver_nconflicts_spec
    With conflicts
    Require solver_conflict_count_cell(s, conflicts)
    Ensure __return == MiniSatTarget::signed_low32(conflicts) &&
           solver_conflict_count_cell(s, conflicts)
 */

;

/* Variable extension preserves the retained formula and watch readiness. */
extern void    solver_setnvars(solver* s, int n)
/*@ setnvars_spec
    With (sn_F : cnf) (sn_A_arr sn_A_inst : list literal) (sn_M : msolver) sn_root
    Require (0 <= n && n <= Z::max(ms_cap(sn_M), INT_MAX / 4) &&
            2 * ms_cap(sn_M) <= INT_MAX &&
          solver_support_inv(ms_size(sn_M), sn_F, sn_A_arr, sn_A_inst, sn_root, sn_M) &&
            solver_rep_growable(s, sn_M)) *
            store(&l_Undef, char, 0)
    Ensure (exists (Mnew : msolver),
      ms_size(sn_M) <= ms_size(Mnew) &&
      ms_cap(sn_M) <= ms_cap(Mnew) &&
      2 * ms_cap(Mnew) <= INT_MAX &&
      ms_root_level(Mnew) == ms_root_level(sn_M) &&
      solver_support_inv(ms_size(Mnew), sn_F, sn_A_arr, sn_A_inst, sn_root, Mnew) &&
      ((Zlength(mt_lim(ms_core(sn_M))) == 0 &&
        (ms_capacity_root_propagation_pending(sn_M) == 0 &&
         msolver_seed_shadow(sn_M))) =>
       (Zlength(mt_lim(ms_core(Mnew))) == 0 &&
        (ms_capacity_root_propagation_pending(Mnew) == 0 &&
         msolver_seed_shadow(Mnew)))) &&
      (minisat_watch_completed(sn_M) => minisat_watch_completed(Mnew)) &&
      ms_size(Mnew) == Z::max(ms_size(sn_M), n) &&
      solver_rep_growable(s, Mnew)) *
            store(&l_Undef, char, 0)
 */

;

struct stats_t
{
    uint64   starts, decisions, propagations, inspects, conflicts;
    uint64   clauses, clauses_literals, learnts, learnts_literals, max_literals, tot_literals;
};
typedef struct stats_t stats;

// Solver representation:

struct clause_t;
typedef struct clause_t clause;

struct solver_t
{
    int      size;          // nof variables
    int      cap;           // size of varmaps
    int      qhead;         // Head index of queue.
    int      qtail;         // Tail index of queue.

    // clauses
    vecp     clauses;       // List of problem constraints. (contains: clause*)
    vecp     learnts;       // List of learnt clauses. (contains: clause*)

    // activities
    double   var_inc;       // Amount to bump next variable with.
    double   var_decay;     // INVERSE decay factor for variable activity: stores 1/decay.
    float    cla_inc;       // Amount to bump next clause with.
    float    cla_decay;     // INVERSE decay factor for clause activity: stores 1/decay.

    vecp*    wlists;        //
    double*  activity;      // A heuristic measurement of the activity of a variable.
    lbool*   assigns;       // Current values of variables.
    int*     orderpos;      // Index in variable order.
    clause** reasons;       //
    int*     levels;        //
    lit*     trail;

    clause*  binary;        // A temporary binary clause
    lbool*   tags;          //
    veci     tagged;        // (contains: var)
    veci     stack;         // (contains: var)

    veci     order;         // Variable order. (heap) (contains: var)
    veci     trail_lim;     // Separator indices for different decision levels in 'trail'. (contains: int)
    veci     model;         // If problem is solved, this vector contains the model (contains: lbool).

    int      root_level;    // Level of first proper decision.
    int      simpdb_assigns;// Number of top-level assignments at last 'simplifyDB()'.
    int      simpdb_props;  // Number of propagations before next 'simplifyDB()'.
    double   random_seed;
    double   progress_estimate;
    int      verbosity;     // Verbosity level. 0=silent, 1=some progress report, 2=everything

    stats    stats;
};

#endif /* solver_h */
