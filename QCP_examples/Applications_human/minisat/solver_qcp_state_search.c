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


/* Solver state, search and public API. */
#include "solver_qcp_internal.h"

extern bool    solver_addclause(solver* s, lit* begin, lit* endvar)
/*@ solver_addclause_incremental_spec <= addclause_spec
    With (n input_bound : Z) (F : cnf) (M : msolver) (input : list Z)
    Require (solver_update_ready(n, F, nil, M) &&
            ms_capacity_root_propagation_pending(M) == 0 &&
            solver_query_watch_ready(M) &&
            0 <= input_bound && input_bound <= Z::max(ms_cap(M), INT_MAX / 4) &&
            endvar == begin + Zlength(input) * sizeof(int) &&
            2 * Zlength(input) + 1 <= INT_MAX &&
            Forall(lit_wf_c(input_bound), input) &&
            solver_incremental_ownership_at(s, M) *
            IntArray::seg(begin, 0, Zlength(input), input)) *
            store(&l_Undef, char, 0) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
    Ensure (exists (Mout : msolver) (current : list Z),
      Zlength(current) == Zlength(input) && n <= ms_size(Mout) &&
      solver_query_watch_ready(Mout) &&
      ms_capacity_root_propagation_pending(Mout) == 0 &&
      ((__return == 1 &&
        (exists (Fnew : cnf),
          solver_update_ready(ms_size(Mout), Fnew, nil, Mout) &&
          (forall (rho : valuation),
            (models(rho, Fnew) => models(rho, cnf_add_clause(F, input))) &&
            (models(rho, cnf_add_clause(F, input)) => models(rho, Fnew))))) ||
       (__return == 0 &&
        cnf_unsat(Z::max(n, input_bound), cnf_add_clause(F, input)) &&
        solver_update_ready(ms_size(Mout), F, nil, Mout)) ) &&
      solver_incremental_ownership_at(s, Mout) *
      IntArray::seg(begin, 0, Zlength(input), current)) *
            store(&l_Undef, char, 0) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
 */;

extern bool    solver_simplify(solver* s)
/*@ solver_simplify_incremental_spec <= solver_simplify_spec
    With (n : Z) (F : cnf) (M : msolver)
    Require (solver_update_ready(n, F, nil, M) &&
            ms_capacity_root_propagation_pending(M) == 0 &&
            solver_query_watch_ready(M) &&
            solver_incremental_ownership_at(s, M)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&true, int, 1) * store(&false, int, 0)
    Ensure (exists (Mout : msolver),
      solver_update_ready(n, F, nil, Mout) &&
      ((__return == 1 &&
        solver_query_ready(n, F, Mout) &&
        solver_query_reuse_guard(Mout) &&
        ms_capacity_root_propagation_pending(Mout) == 0 &&
        solver_query_watch_ready(Mout)) ||
       (__return == 0 &&
        cnf_unsat(n, F) &&
        solver_public_query_entry(n, F, Mout) &&
        ms_capacity_root_propagation_pending(Mout) == 0 &&
        solver_query_reuse_guard(Mout)) ) &&
      solver_incremental_ownership_at(s, Mout)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&true, int, 1) * store(&false, int, 0)
 */;

extern bool    solver_solve(solver* s, lit* begin, lit* endvar)
/*@ solver_solve_incremental_spec <= solver_solve_spec
    With (n : Z) (F : cnf) (A_arr : list literal) (M : msolver)
    Require (solver_update_ready(n, F, nil, M) &&
            ms_capacity_root_propagation_pending(M) == 0 &&
            solver_query_watch_ready(M) &&
            solver_assumptions_entry_ready(A_arr, M) &&
            solver_incremental_ownership_at(s, M) *
            assumptions_array(n, begin, endvar, A_arr)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
    Ensure (assumptions_array(n, begin, endvar, A_arr) *
      (exists (Mout : msolver),
        solver_public_query_entry(n, F, Mout) &&
        solver_query_reuse_guard(Mout) &&
        solver_update_ready(n, F, nil, Mout) &&
        ((__return == 1 &&
          solver_query_ready(n, F, Mout) &&
          Zlength(ms_model(Mout)) == n &&
          model_is_total(ms_model(Mout)) &&
          models(rho_of_model(ms_model(Mout)), F) &&
          assumptions_true_under(rho_of_model(ms_model(Mout)), A_arr) &&
          ms_capacity_root_propagation_pending(Mout) == 0 &&
          solver_query_watch_ready(Mout)) ||
         (__return == 0 &&
          cnf_unsat(n, cnf_with_units(F, A_arr)) &&
          ms_capacity_root_propagation_pending(Mout) == 0 &&
          (solver_query_watch_ready(Mout) || cnf_unsat(n, F))) ) &&
        solver_incremental_ownership_at(s, Mout))) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
 */;

extern int     solver_nvars(solver* s)
/*@ solver_nvars_incremental_spec <= solver_nvars_spec
    With (M : msolver)
    Require solver_incremental_ownership_at(s, M)
    Ensure __return == ms_size(M) && solver_incremental_ownership_at(s, M)
 */;

extern int     solver_nclauses(solver* s)
/*@ solver_nclauses_incremental_spec <= solver_nclauses_spec
    With (M : msolver)
    Require solver_incremental_ownership_at(s, M)
    Ensure __return == Zlength(db_words(ms_prob(M))) &&
           solver_incremental_ownership_at(s, M)
 */;

extern int     solver_nconflicts(solver* s)
/*@ solver_nconflicts_incremental_spec <= solver_nconflicts_spec
    With (M : msolver)
    Require solver_incremental_ownership_at(s, M)
    Ensure __return == MiniSatTarget::signed_low32(stats_conflicts(ms_stats(M))) &&
           solver_incremental_ownership_at(s, M)
 */;

extern void    solver_setnvars(solver* s, int n)
/*@ solver_setnvars_incremental_spec <= setnvars_spec
    With (nv : Z) (F : cnf) (M : msolver)
    Require (solver_update_ready(nv, F, nil, M) &&
            solver_query_watch_ready(M) &&
            ms_capacity_root_propagation_pending(M) == 0 &&
            0 <= n && n <= Z::max(ms_cap(M), INT_MAX / 4) &&
            solver_incremental_ownership_at(s, M)) *
            store(&l_Undef, char, 0)
    Ensure (exists (Mnew : msolver),
      nv <= ms_size(Mnew) &&
      solver_update_ready(ms_size(Mnew), F, nil, Mnew) &&
      solver_query_watch_ready(Mnew) &&
      ms_capacity_root_propagation_pending(Mnew) == 0 &&
      ms_size(Mnew) == Z::max(nv, n) &&
      solver_incremental_ownership_at(s, Mnew)) *
            store(&l_Undef, char, 0)
 */;

void solver_setnvars(solver* s, int n)
/*@ setnvars_spec */
{
    /*@ solver_support_inv(ms_size(sn_M), sn_F, sn_A_arr, sn_A_inst, sn_root, sn_M) &&
          solver_rep_growable(s, sn_M)
        which implies
        exists wl act asg opos rsn lvl trl tgs,
          solver_support_inv(ms_size(sn_M), sn_F, sn_A_arr, sn_A_inst, sn_root, sn_M) &&
          solver_shape(sn_M) &&
          store(&(s->size), int, ms_size(sn_M)) *
          store(&(s->cap), int, ms_cap(sn_M)) *
          setnvars_arrays_at(s, sn_M, ms_size(sn_M),
                             wl, act, asg, opos, rsn, lvl, trl, tgs) *
          Veci::rep(&(s->order), ms_order(sn_M)) *
          setnvars_frame_at(s, sn_M)
     */
    /*@ Given wl act asg opos rsn lvl trl tgs */
    int new_cap = s->cap;
    int var;

    if (new_cap < n) {
        /*@ Inv Assert (s == s@pre && n == n@pre &&
              0 <= new_cap && ms_cap(sn_M) <= new_cap &&
              ms_cap(sn_M) < n &&
              2 * new_cap <= INT_MAX &&
              0 <= n && 4 * n <= INT_MAX && 2 * ms_cap(sn_M) <= INT_MAX &&
          solver_support_inv(ms_size(sn_M), sn_F, sn_A_arr, sn_A_inst, sn_root, sn_M) &&
              solver_shape(sn_M) &&
              has_permission(&var) *
              store(&(s->size), int, ms_size(sn_M)) *
          store(&(s->cap), int, ms_cap(sn_M)) *
          setnvars_arrays_at(s, sn_M, ms_size(sn_M),
                             wl, act, asg, opos, rsn, lvl, trl, tgs) *
          Veci::rep(&(s->order), ms_order(sn_M)) *
          setnvars_frame_at(s, sn_M)) *
          store(&l_Undef, char, 0)
         */
        while (new_cap < n) {
            new_cap = vec_next_capacity(new_cap);
        }

        /*@ setnvars_arrays_at(s, sn_M, ms_size(sn_M),
                 wl, act, asg, opos, rsn, lvl, trl, tgs)
            which implies exists sn_act_physical sn_asg_physical sn_opos_physical sn_rsn_physical sn_lvl_physical sn_tgs_physical sn_trl_physical sn_wl_physical,
              ms_cap(sn_M) <= sn_act_physical && sn_act_physical <= INT_MAX && vec_buf_ok(sn_act_physical, act) &&
              ms_cap(sn_M) <= sn_asg_physical && sn_asg_physical <= INT_MAX && vec_buf_ok(sn_asg_physical, asg) &&
              ms_cap(sn_M) <= sn_opos_physical && sn_opos_physical <= INT_MAX && vec_buf_ok(sn_opos_physical, opos) &&
              ms_cap(sn_M) <= sn_rsn_physical && sn_rsn_physical <= INT_MAX && vec_buf_ok(sn_rsn_physical, rsn) &&
              ms_cap(sn_M) <= sn_lvl_physical && sn_lvl_physical <= INT_MAX && vec_buf_ok(sn_lvl_physical, lvl) &&
              ms_cap(sn_M) <= sn_tgs_physical && sn_tgs_physical <= INT_MAX && vec_buf_ok(sn_tgs_physical, tgs) &&
              ms_cap(sn_M) <= sn_trl_physical && sn_trl_physical <= INT_MAX && vec_buf_ok(sn_trl_physical, trl) &&
              2 * ms_cap(sn_M) <= sn_wl_physical && sn_wl_physical <= INT_MAX && vec_buf_ok(sn_wl_physical, wl) &&
              store(&(s->qtail), int, ms_qtail(sn_M)) *
              store(&(s->wlists), vecp *, wl) *
              store(&(s->activity), double *, act) *
              DoubleArray::seg(act, 0, ms_size(sn_M), ms_activity(sn_M)) *
              DoubleArray::undef_seg(act, ms_size(sn_M), sn_act_physical) *
              store(&(s->assigns), char *, asg) *
              CharArray::seg(asg, 0, ms_size(sn_M), mt_assigns(ms_core(sn_M))) *
              CharArray::undef_seg(asg, ms_size(sn_M), sn_asg_physical) *
              store(&(s->orderpos), int *, opos) *
              IntArray::seg(opos, 0, ms_size(sn_M), ms_orderpos(sn_M)) *
              IntArray::undef_seg(opos, ms_size(sn_M), sn_opos_physical) *
              store(&(s->reasons), void **, rsn) *
              PtrArray::seg(rsn, 0, ms_size(sn_M), ms_reason_words(sn_M)) *
              PtrArray::undef_seg(rsn, ms_size(sn_M), sn_rsn_physical) *
              store(&(s->levels), int *, lvl) *
              IntArray::seg(lvl, 0, ms_size(sn_M), mt_levels(ms_core(sn_M))) *
              IntArray::undef_seg(lvl, ms_size(sn_M), sn_lvl_physical) *
              store(&(s->tags), char *, tgs) *
              CharArray::seg(tgs, 0, ms_size(sn_M), ms_tags(sn_M)) *
              CharArray::undef_seg(tgs, ms_size(sn_M), sn_tgs_physical) *
              store(&(s->trail), int *, trl) *
              IntArray::seg(trl, 0, ms_qtail(sn_M), mt_trail(ms_core(sn_M))) *
              IntArray::undef_seg(trl, ms_qtail(sn_M), sn_trl_physical) *
              wlists_rep(wl, ms_size(sn_M), ms_wm(sn_M)) *
              VecpArray::undef_seg(wl, 2 * ms_size(sn_M), sn_wl_physical)
         */
        /*@ Given sn_act_physical sn_asg_physical sn_opos_physical sn_rsn_physical sn_lvl_physical sn_tgs_physical sn_trl_physical sn_wl_physical */
        s->wlists   = (vecp *)   minisat_vecp_array_grow(s->wlists, s->size, s->cap, n, &new_cap);
        s->activity = (double *) minisat_double_array_grow(s->activity, s->size, s->cap, n, &new_cap);
        s->assigns  = (lbool *)  minisat_char_array_grow(s->assigns, s->size, s->cap, n, &new_cap);
        s->orderpos = (int *)    minisat_int_array_grow(s->orderpos, s->size, s->cap, n, &new_cap);
        s->reasons  = (clause **)minisat_ptr_array_grow((void **)s->reasons, s->size, s->cap, n, &new_cap);
        s->levels   = (int *)    minisat_int_array_grow(s->levels, s->size, s->cap, n, &new_cap);
        s->tags     = (lbool *)  minisat_char_array_grow(s->tags, s->size, s->cap, n, &new_cap);
        s->trail    = (lit *)    minisat_int_array_grow(s->trail, s->qtail, s->cap, n, &new_cap);
        s->cap = new_cap;
    }

    /*@ Inv Assert (exists Mcur wlc actc asgc oposc rsnc lvlc trlc tgsc,
          s == s@pre && n == n@pre &&
          ms_size(Mcur) == var &&
          ms_size(sn_M) <= var && setnvars_bound(ms_size(sn_M), var, n) &&
          ms_cap(sn_M) <= ms_cap(Mcur) && n <= ms_cap(Mcur) &&
          2 * ms_cap(Mcur) <= INT_MAX &&
          0 <= n &&
          setnvars_core_equiv(sn_M, Mcur) &&
          solver_support_inv(var, sn_F, sn_A_arr, sn_A_inst, sn_root, Mcur) &&
              (minisat_watch_completed(sn_M) => minisat_watch_completed(Mcur)) &&
          solver_shape(Mcur) &&
          has_permission(&new_cap) *
          store(&(s->size), int, ms_size(sn_M)) *
          store(&(s->cap), int, ms_cap(Mcur)) *
          setnvars_arrays_at(s, Mcur, var,
                             wlc, actc, asgc, oposc, rsnc, lvlc, trlc, tgsc) *
          Veci::rep(&(s->order), ms_order(Mcur)) *
          setnvars_frame_at(s, Mcur)) *
          store(&l_Undef, char, 0)
     */
    for (var = s->size; var < n; var++) {
        /*@ Given Mcur wlc actc */

        /*@ 2 * var + 1 < 2 * ms_cap(Mcur) && 0 <= var &&
              store(&(s->wlists), vecp *, wlc) *
              solver_wlists_tail(wlc, 2*var, 2 * ms_cap(Mcur))
            which implies
              store(&(s->wlists), vecp *, wlc) *
              Vecp::shell(&(s->wlists[2*var])) *
              solver_wlists_tail(wlc, 2*var + 1, 2 * ms_cap(Mcur))
         */
        vecp_new(&s->wlists[2*var]);
        /*@ 2 * var + 1 < 2 * ms_cap(Mcur) && 0 <= var &&
              store(&(s->wlists), vecp *, wlc) *
              solver_wlists_tail(wlc, 2*var+1, 2 * ms_cap(Mcur))
            which implies
              store(&(s->wlists), vecp *, wlc) *
              Vecp::shell(&(s->wlists[2*var+1])) *
              solver_wlists_tail(wlc, 2*var + 2, 2 * ms_cap(Mcur))
         */
        vecp_new(&s->wlists[2*var+1]);
        /*@ 0 <= var && var < ms_cap(Mcur) &&
              store(&(s->activity), double *, actc) *
              solver_double_tail(actc, var, ms_cap(Mcur))
            which implies
              store(&(s->activity), double *, actc) *
              undef_data_at(&(s->activity[var]), double) *
              solver_double_tail(actc, var + 1, ms_cap(Mcur))
         */
        s->activity [var] = 0;
        /*@ ms_size(Mcur) == var && solver_shape(Mcur) &&
              store(&(s->activity), double *, actc) *
              DoubleArray::seg(actc, 0, var, ms_activity(Mcur)) *
              store(&(s->activity[var]), double, Z_to_fp64(0))
            which implies
              ms_size(Mcur) == var && solver_shape(Mcur) &&
              store(&(s->activity), double *, actc) *
              DoubleArray::seg(actc, 0, var + 1,
                app(ms_activity(Mcur), cons(Z_to_fp64(0), nil)))
         */
        s->assigns  [var] = l_Undef;
        s->orderpos [var] = veci_size(&s->order);
        s->reasons  [var] = (clause*)0;
        s->levels   [var] = 0;
        s->tags     [var] = l_Undef;

        veci_push(&s->order,var);
        /*@ ms_size(Mcur) == var && var < ms_cap(Mcur) &&
              2 * (ms_size(Mcur) + 1) <= INT_MAX &&
              solver_support_inv(ms_size(Mcur), sn_F, sn_A_arr, sn_A_inst, sn_root, Mcur) &&
              (minisat_watch_completed(sn_M) => minisat_watch_completed(Mcur))
            which implies
              ms_size(Mcur) == var && var < ms_cap(Mcur) &&
              2 * (ms_size(Mcur) + 1) <= INT_MAX &&
              solver_support_inv(ms_size(Mcur), sn_F, sn_A_arr, sn_A_inst, sn_root, Mcur) &&
              (minisat_watch_completed(sn_M) => minisat_watch_completed(Mcur)) &&
              order_update_pre(ms_size(Mcur) + 1, ms_size(Mcur),
                app(ms_order(Mcur), cons(ms_size(Mcur), nil)),
                app(ms_orderpos(Mcur), cons(Zlength(ms_order(Mcur)), nil)))
         */
        order_update(s, var);

    }
    s->size = n > s->size ? n : s->size;
}

bool enqueue(solver* s, lit l, clause* reason)
/*@ default */
{
    /*@ enqueue_state_at(s, asg, lvl, n, cap, qtail,
                         assigns, levels0, reasons0, trail, lim)
        which implies exists rsn trl,
          0 <= n && n <= cap && cap <= INT_MAX &&
          Zlength(assigns) == n && Zlength(levels0) == n &&
          Zlength(reasons0) == n && Zlength(trail) == qtail &&
          0 <= qtail && qtail <= cap &&
          store(&(s->qtail), qtail) *
          store(&(s->assigns), asg) *
          store(&(s->levels), lvl) *
          store(&(s->reasons), rsn) *
          store(&(s->trail), trl) *
          CharArray::seg(asg, 0, n, assigns) *
          solver_char_tail(asg, n, cap) *
          IntArray::seg(lvl, 0, n, levels0) *
          solver_int_tail(lvl, n, cap) *
          PtrArray::seg(rsn, 0, n, reasons0) *
          solver_ptr_tail(rsn, n, cap) *
          IntArray::seg(trl, 0, qtail, trail) *
          solver_int_tail(trl, qtail, cap) *
          Veci::rep(&(s->trail_lim), lim)
     */
    /*@ Given rsn trl */
    lbool* values = s->assigns;
    int    v      = lit_var(l) /*@ where(original) */;
    /*@ v == lit_var_c(l0) by local */
    /*@ enqueue_input(n, l0, qtail, assigns, levels0, reasons0,
                      trail) &&
          CharArray::seg(asg, 0, n, assigns)
        which implies
          enqueue_input(n, l0, qtail, assigns, levels0, reasons0,
                        trail) &&
          0 <= lit_var_c(l0) && lit_var_c(l0) < n &&
          store(pointer_offset(asg, lit_var_c(l0), char),
                char, Znth(lit_var_c(l0), assigns, 0)) *
          CharArray::missing_i(
            asg, lit_var_c(l0), 0, n, assigns)
     */
    lbool  val    = values[v];
#ifdef VERBOSEDEBUG
    printf(L_IND"enqueue("L_LIT")\n", L_ind, L_lit(l));
#endif

    lbool sig = !lit_sign(l);
    /*@ 0 <= sig && sig <= 1 by local */
    sig += sig - 1;
    if (val != l_Undef){
        return val == sig;
    }else{
        // New fact -- store it.
#ifdef VERBOSEDEBUG
        printf(L_IND"bind("L_LIT")\n", L_ind, L_lit(l));
#endif
        int*     levels  = s->levels;
        clause** reasons = s->reasons;

        /*@ Znth(lit_var_c(l0), assigns, 0) == 0 &&
              enqueue_input(n, l0, qtail, assigns, levels0, reasons0,
                            trail) &&
              qtail < cap &&
              IntArray::seg(lvl, 0, n, levels0) *
              PtrArray::seg(rsn, 0, n, reasons0) *
              solver_int_tail(trl, qtail, cap)
            which implies
            exists old_level old_reason,
              0 <= lit_var_c(l0) && lit_var_c(l0) < n && qtail < n &&
              old_level == Znth(lit_var_c(l0), levels0, 0) &&
              old_reason == Znth(lit_var_c(l0), reasons0, 0) &&
              store(pointer_offset(
                      lvl, lit_var_c(l0), int),
                    int, old_level) *
              IntArray::missing_i(
                lvl, lit_var_c(l0), 0, n, levels0) *
              store(pointer_offset(
                      rsn, lit_var_c(l0), clause *),
                    clause *, old_reason) *
              PtrArray::missing_i(
                rsn, lit_var_c(l0), 0, n, reasons0) *
              undef_data_at(pointer_offset(trl, qtail, int),
                            int) *
              solver_int_tail(trl, qtail + 1, cap)
         */
        /*@ 0 <= lit_var_c(l0) && lit_var_c(l0) < n &&
              CharArray::full(asg, n, assigns)
            which implies
              store(pointer_offset(
                      asg, lit_var_c(l0), char),
                    char, Znth(lit_var_c(l0), assigns, 0)) *
              CharArray::missing_i(
                asg, lit_var_c(l0), 0, n, assigns)
         */
        values [v] = sig;
        levels [v] = solver_dlevel(s);
        reasons[v] = reason;
        s->trail[s->qtail] = l;
        s->qtail++;

        order_assigned(s, v);

        return true;
    }
}

static inline void assume(solver* s, lit l)
/*@ With asg lvl n cap qtail s0 l0
          (assigns levels reasons trail lim : list Z)
    Require (s == s0 && l == l0 &&
            Znth(lit_var_c(l0), assigns, 0) == 0 &&
            Zlength(lim) < n &&
            enqueue_input(n, l0, qtail, assigns, levels,
                          reasons, trail) &&
            store(&(s->qhead), qtail) *
            enqueue_state_at(s, asg, lvl, n, cap, qtail,
                             assigns, levels, reasons, trail, lim)) *
            store(&l_Undef, char, 0) * store(&true, int, 1)
    Ensure (assume_post_at(s, asg, lvl, l0, n, cap, qtail,
                          assigns, levels, reasons, trail, lim)) *
            store(&l_Undef, char, 0) * store(&true, int, 1)
 */
{
    /*@ store(&(s->qhead), qtail) *
          enqueue_state_at(s, asg, lvl, n, cap, qtail,
                           assigns, levels, reasons, trail, lim)
        which implies exists rsn trl,
          0 <= n && n <= cap && cap <= INT_MAX &&
          Zlength(assigns) == n && Zlength(levels) == n &&
          Zlength(reasons) == n && Zlength(trail) == qtail &&
          store(&(s->qhead), qtail) *
          store(&(s->qtail), qtail) *
          store(&(s->assigns), asg) *
          store(&(s->levels), lvl) *
          store(&(s->reasons), rsn) *
          store(&(s->trail), trl) *
          CharArray::seg(asg, 0, n, assigns) *
          solver_char_tail(asg, n, cap) *
          IntArray::seg(lvl, 0, n, levels) *
          solver_int_tail(lvl, n, cap) *
          PtrArray::seg(rsn, 0, n, reasons) *
          solver_ptr_tail(rsn, n, cap) *
          IntArray::seg(trl, 0, qtail, trail) *
          solver_int_tail(trl, qtail, cap) *
          Veci::rep(&(s->trail_lim), lim)
     */
    /*@ Given rsn trl */
    assert(s->qtail == s->qhead);
    /*@ 0 <= lit_var_c(l0) && lit_var_c(l0) < n &&
          CharArray::seg(asg, 0, n, assigns)
        which implies
          store(pointer_offset(asg, lit_var_c(l0), char),
                char, Znth(lit_var_c(l0), assigns, 0)) *
          CharArray::missing_i(
            asg, lit_var_c(l0), 0, Zlength(assigns), assigns)
     */
    assert(s->assigns[lit_var(l) /*@ where (zero_index) lv_asg = asg */] ==
           l_Undef);
    /*@ Assert (s0 == s@pre &&
          0 <= n && n <= cap && cap <= INT_MAX &&
          Zlength(assigns) == n && Zlength(levels) == n &&
          Zlength(reasons) == n && Zlength(trail) == qtail &&
          Znth(lit_var_c(l0), assigns, 0) == 0 &&
          Zlength(lim) < n && 2 * n <= INT_MAX &&
          enqueue_input(n, l0, qtail, assigns, levels, reasons,
                        trail) &&
          store(&(s), solver *, s0) *
          store(&(l), int, l0) *
          store(&(s->qhead), qtail) *
          store(&(s->qtail), qtail) *
          store(&(s->assigns), asg) *
          store(&(s->levels), lvl) *
          store(&(s->reasons), rsn) *
          store(&(s->trail), trl) *
          CharArray::seg(asg, 0, n, assigns) *
          solver_char_tail(asg, n, cap) *
          IntArray::seg(lvl, 0, n, levels) *
          solver_int_tail(lvl, n, cap) *
          PtrArray::seg(rsn, 0, n, reasons) *
          solver_ptr_tail(rsn, n, cap) *
          IntArray::seg(trl, 0, qtail, trail) *
          solver_int_tail(trl, qtail, cap) *
          Veci::rep(&(s->trail_lim), lim)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
     */
#ifdef VERBOSEDEBUG
    printf(L_IND"assume("L_LIT")\n", L_ind, L_lit(l));
#endif
    veci_push(&s->trail_lim,s->qtail) /*@ where l = lim */;
    /*@ store(&(s->qhead), qtail) *
          enqueue_state_at(
            s, asg, lvl, n, cap, qtail, assigns, levels, reasons, trail,
            app(lim, cons(qtail, nil)))
     */
    enqueue(s,l,(clause*)0);

}

static inline void solver_canceluntil(solver* s, int level)
/*@ With (M : msolver) (wl : Z)
    Require (solver_cancel_pre(s, level, M, wl)) *
            store(&l_Undef, char, 0)
    Ensure (solver_cancel_post(s, level@pre, M, wl)) *
            store(&l_Undef, char, 0)
 */
{
    /*@ solver_cancel_pre(s, level, M, wl)
        which implies exists (activity_ptr assigns_ptr orderpos_ptr
                              reasons_ptr trail_ptr : Z),
          solver_shape(M) && mtrail_wf(ms_size(M), ms_core(M)) &&
          heap_wf(ms_size(M), msolver_heap(M)) &&
          cancel_bound_ready(M, level) &&
          0 <= level && level <= Zlength(mt_lim(ms_core(M))) &&
          solver_cancel_open_at(s, M, activity_ptr, assigns_ptr, orderpos_ptr,
                   reasons_ptr, trail_ptr, mt_assigns(ms_core(M)), ms_orderpos(M), ms_reason_words(M),
                   ms_order(M), wl)
     */
    /*@ Given activity_ptr assigns_ptr orderpos_ptr reasons_ptr trail_ptr */
    lit*     trail;
    lbool*   values;
    clause** reasons;
    int      bound;
    int      c;

    if (solver_dlevel(s) <= level)
        return;

    trail   = s->trail;
    values  = s->assigns;
    reasons = s->reasons;
    bound   = (veci_begin(&s->trail_lim))[level];

    /*@ Inv Assert (exists (assigns_now reasons_now : list Z),
          s == s@pre && level == level@pre &&
          solver_shape(M) && mtrail_wf(ms_size(M), ms_core(M)) &&
          heap_wf(ms_size(M), msolver_heap(M)) &&
          cancel_bound_ready(M, level) &&
          trail == trail_ptr && values == assigns_ptr &&
          reasons == reasons_ptr &&
          bound == Znth(level, mt_lim(ms_core(M)), 0) &&
          cancel_clear_loop_inv(M, level, c, assigns_now, reasons_now) &&
          solver_cancel_open_at(s, M, activity_ptr, assigns_ptr, orderpos_ptr,
                   reasons_ptr, trail, assigns_now, ms_orderpos(M), reasons_now,
                   ms_order(M), wl)) *
          store(&l_Undef, char, 0)
     */
    for (c = s->qtail-1; c >= bound; c--) {
        /*@ Given assigns_now reasons_now */
        /*@ solver_shape(M) && mtrail_wf(ms_size(M), ms_core(M)) &&
              cancel_clear_loop_inv(
                M, level, c, assigns_now, reasons_now) &&
              c >= Znth(level, mt_lim(ms_core(M)), 0)
            which implies
              mtrail_wf(ms_size(M), ms_core(M)) &&
              cancel_clear_loop_inv(
                M, level, c, assigns_now, reasons_now) &&
              c >= Znth(level, mt_lim(ms_core(M)), 0) &&
              0 <= c && c < ms_qtail(M) &&
              0 <= Znth(c, mt_trail(ms_core(M)), 0) &&
              Znth(c, mt_trail(ms_core(M)), 0) <= INT_MAX &&
              0 <= lit_var_c(
                     Znth(c, mt_trail(ms_core(M)), 0)) &&
              lit_var_c(Znth(c, mt_trail(ms_core(M)), 0)) <
                ms_size(M)
         */
        int     x  = lit_var(trail[c]) /*@ where(original) */;
        /*@ 0 <= x && x < ms_size(M) &&
              CharArray::seg(
                assigns_ptr, 0, ms_size(M), assigns_now)
            which implies
              store(pointer_offset(
                      assigns_ptr, x, char),
                    char, Znth(x, assigns_now, 0)) *
              CharArray::missing_i(
                assigns_ptr, x, 0, ms_size(M), assigns_now)
         */
        values [x] = l_Undef;
        /*@ 0 <= x && x < ms_size(M) &&
              PtrArray::seg(
                reasons_ptr, 0, ms_size(M), reasons_now)
            which implies
              store(pointer_offset(
                      reasons_ptr, x, struct clause_t *),
                    struct clause_t *, Znth(x, reasons_now, 0)) *
              PtrArray::missing_i(
                reasons_ptr, x, 0, ms_size(M), reasons_now)
         */
        reasons[x] = (clause*)0;
    }

    /*@ Inv Assert (exists (assigns_now reasons_now order_now orderpos_now
                            : list Z),
          s == s@pre && level == level@pre &&
          solver_shape(M) && mtrail_wf(ms_size(M), ms_core(M)) &&
          cancel_bound_ready(M, level) &&
          trail == trail_ptr && values == assigns_ptr &&
          reasons == reasons_ptr &&
          bound == Znth(level, mt_lim(ms_core(M)), 0) &&
          cancel_reinsert_loop_inv(M, level, c,
                                   assigns_now, reasons_now,
                                   order_now, orderpos_now) &&
          solver_cancel_open_at(s, M, activity_ptr, assigns_ptr, orderpos_ptr,
                   reasons_ptr, trail, assigns_now, orderpos_now, reasons_now,
                   order_now, wl)) *
          store(&l_Undef, char, 0)
     */
    for (c = s->qhead-1; c >= bound; c--)
        /*@ Given assigns_now reasons_now
                  order_now orderpos_now */
        /*@ solver_shape(M) && mtrail_wf(ms_size(M), ms_core(M)) &&
              cancel_reinsert_loop_inv(
                M, level, c, assigns_now, reasons_now,
                order_now, orderpos_now) &&
              c >= Znth(level, mt_lim(ms_core(M)), 0)
            which implies
              solver_shape(M) && mtrail_wf(ms_size(M), ms_core(M)) &&
              cancel_reinsert_loop_inv(
                M, level, c, assigns_now, reasons_now,
                order_now, orderpos_now) &&
              c >= Znth(level, mt_lim(ms_core(M)), 0) &&
              0 <= c && c < ms_qtail(M) &&
              0 <= Znth(c, mt_trail(ms_core(M)), 0) &&
              Znth(c, mt_trail(ms_core(M)), 0) <= INT_MAX &&
              0 <= lit_var_c(
                     Znth(c, mt_trail(ms_core(M)), 0)) &&
              lit_var_c(Znth(c, mt_trail(ms_core(M)), 0)) <
                ms_size(M) &&
              Zlength(ms_activity(M)) == ms_size(M) &&
              order_unassigned_pre(
                ms_size(M),
                lit_var_c(Znth(c, mt_trail(ms_core(M)), 0)),
                order_now, orderpos_now)
         */
        order_unassigned(s,lit_var(trail[c]) /*@ where(original) */);

    s->qtail = bound;
    s->qhead = bound;
    veci_resize(&s->trail_lim,level);

}

static void solver_record(solver *s, veci *cls)
/*@ With levels_ptr rec_wl rec_n (rec_F : cnf) (rec_A_arr rec_A_inst : list literal) (M : msolver)
          (rec_words : list Z)
    Require (solver_record_pre_at(s, cls, levels_ptr, rec_n, rec_F, rec_A_arr, rec_A_inst,
                                 M, rec_words, rec_wl)) *
            store(&l_Undef, char, 0) * store(&true, int, 1)
    Ensure (solver_record_post_at(s, cls, levels_ptr, rec_n, rec_F, rec_A_arr, rec_A_inst,
                                 M, rec_words, 1, rec_wl)) *
            store(&l_Undef, char, 0) * store(&true, int, 1)
 */
{
    /*@ solver_record_pre_at(s, cls, levels_ptr, rec_n, rec_F, rec_A_arr, rec_A_inst,
                             M, rec_words, rec_wl)
        which implies exists learnt_ptr,
          1 <= Zlength(rec_words) &&
          record_clause_cert(rec_n, rec_F, M, rec_words) &&
          msolver_inv(rec_n, rec_F, rec_A_arr, rec_A_inst, M) &&
          mt_qhead(ms_core(M)) == ms_qtail(M) &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          solver_rep_levels_wl_at(s, M, rec_wl, levels_ptr) *
          Veci::rep_ptr(cls, learnt_ptr, rec_words)
     */
    /*@ Given learnt_ptr */
    lit *begin = veci_begin(cls);
    lit *endvar = begin + veci_size(cls);
    clause *c = (veci_size(cls) > 1) ? clause_new(s, begin, endvar, 1)
            /*@ where (clause_new_spec) lvl = levels_ptr, cn_n = rec_n, cn_F = rec_F,
                  cn_A_arr = rec_A_arr, cn_A_inst = rec_A_inst, cn_M = M,
                  cn_words = rec_words, cn_sel = 1, cn_wl = rec_wl,
                  cn_root = ms_root_level(M) */ : (clause *)0;
    /*@ Assert (exists Mstage,
          s == s@pre && cls == cls@pre &&
          1 <= Zlength(rec_words) &&
          record_allocated(rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
          store(&(begin), lit *, learnt_ptr) * has_permission(&endvar) *
          solver_record_rep_at(s, Mstage, rec_wl, levels_ptr,
              db_words(ms_learnt(M))) *
          Veci::rep_ptr(cls, learnt_ptr, rec_words)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
     */
    /*@ Given Mstage */
    /*@ record_allocated(rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
          solver_record_rep_at(s, Mstage, rec_wl, levels_ptr,
              db_words(ms_learnt(M)))
        which implies exists assigns_ptr,
          record_allocated(rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
          enqueue_input(
            ms_size(Mstage), Znth(0, rec_words, 0), ms_qtail(Mstage),
            mt_assigns(ms_core(Mstage)), mt_levels(ms_core(Mstage)),
            ms_reason_words(Mstage), mt_trail(ms_core(Mstage))) &&
          enqueue_state_at(
            s, assigns_ptr, levels_ptr, ms_size(Mstage), ms_cap(Mstage),
            ms_qtail(Mstage), mt_assigns(ms_core(Mstage)),
            mt_levels(ms_core(Mstage)), ms_reason_words(Mstage),
            mt_trail(ms_core(Mstage)), mt_lim(ms_core(Mstage))) *
          solver_record_enqueue_frame_at(s, Mstage, rec_wl,
              db_words(ms_learnt(M)))
     */
    /*@ Given assigns_ptr */
    enqueue(s, *begin, c);
    /*@ IntArray::missing_i(
            learnt_ptr, 0, 0, Zlength(rec_words), rec_words) *
          store(learnt_ptr, int, Znth(0, rec_words, 0))
        which implies
          IntArray::seg(learnt_ptr, 0, Zlength(rec_words), rec_words)
     */
    assert(veci_size(cls) > 0);
    /*@ Assert (s == s@pre && cls == cls@pre &&
          record_allocated(
            rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
          store(&(begin), lit *, learnt_ptr) * has_permission(&endvar) *
          enqueue_post_at(
          s, assigns_ptr, levels_ptr, Znth(0, rec_words, 0), c,
          ms_size(Mstage), ms_cap(Mstage), ms_qtail(Mstage), 1,
          mt_assigns(ms_core(Mstage)), mt_levels(ms_core(Mstage)),
          ms_reason_words(Mstage), mt_trail(ms_core(Mstage)),
          mt_lim(ms_core(Mstage))) *
          solver_record_enqueue_frame_at(s, Mstage, rec_wl,
              db_words(ms_learnt(M))) *
          Veci::rep_ptr(cls, learnt_ptr, rec_words)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
     */
    /*@ record_allocated(
          rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
          enqueue_post_at(
          s, assigns_ptr, levels_ptr, Znth(0, rec_words, 0), c,
          ms_size(Mstage), ms_cap(Mstage), ms_qtail(Mstage), 1,
          mt_assigns(ms_core(Mstage)), mt_levels(ms_core(Mstage)),
          ms_reason_words(Mstage), mt_trail(ms_core(Mstage)),
          mt_lim(ms_core(Mstage))) *
          solver_record_enqueue_frame_at(s, Mstage, rec_wl,
              db_words(ms_learnt(M)))
        which implies exists Menq,
          record_enqueue_success(
            rec_n, rec_F, rec_A_arr, rec_A_inst, M, Mstage, rec_words, c, Menq) &&
          solver_record_rep_at(s, Menq, rec_wl, levels_ptr,
              db_words(ms_learnt(M)))
     */
    /*@ Given Menq */
    if (c != 0) {
        /*@ c != 0 &&
            record_allocated(rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
            record_enqueue_success(rec_n, rec_F, rec_A_arr, rec_A_inst, M, Mstage, rec_words, c, Menq) &&
            msat_fp32_nonnegative(ms_cla_inc(Menq)) &&
            solver_record_rep_at(s, Menq, rec_wl, levels_ptr,
              db_words(ms_learnt(M)))
            which implies
              c != 0 &&
            record_allocated(rec_n, rec_F, rec_A_arr, rec_A_inst, M, rec_words, c, Mstage) &&
            record_enqueue_success(rec_n, rec_F, rec_A_arr, rec_A_inst, M, Mstage, rec_words, c, Menq) &&
            msat_fp32_nonnegative(ms_cla_inc(Menq)) &&
              db_words(ms_learnt(Menq)) == app(db_words(ms_learnt(M)), cons(c, nil)) &&
              Vecp::rep(&(s->learnts), db_words(ms_learnt(M))) *
              clause_db_rep(ms_learnt(Menq)) *
              store(&(s->cla_inc), float, ms_cla_inc(Menq)) *
              store(&(s->stats.learnts), unsigned long long,
                    stats_learnts(ms_stats(Menq))) *
              store(&(s->stats.learnts_literals), unsigned long long,
                    stats_learnts_literals(ms_stats(Menq))) *
              solver_record_finish_frame_at(s, Menq, levels_ptr, rec_wl)
         */
        vecp_push(&s->learnts, c);
        /*@ Assert s == s@pre && cls == cls@pre && c != 0 &&
              msat_fp32_nonnegative(ms_cla_inc(Menq)) &&
              record_allocated(rec_n, rec_F, rec_A_arr, rec_A_inst,
                               M, rec_words, c, Mstage) &&
              record_enqueue_success(rec_n, rec_F, rec_A_arr, rec_A_inst,
                                     M, Mstage, rec_words, c, Menq) &&
              Vecp::rep(&(s->learnts), db_words(ms_learnt(Menq))) *
              clause_db_rep(ms_learnt(Menq)) *
              store(&(s->cla_inc), float, ms_cla_inc(Menq)) *
              store(&(s->stats.learnts), unsigned long long, stats_learnts(ms_stats(Menq))) *
              store(&(s->stats.learnts_literals), unsigned long long, stats_learnts_literals(ms_stats(Menq))) *
              solver_record_finish_frame_at(s, Menq, levels_ptr, rec_wl) *
              store(&(begin), lit *, learnt_ptr) * has_permission(&endvar) *
              Veci::rep_ptr(cls, learnt_ptr, rec_words) *
              store(&l_Undef, char, 0) * store(&true, int, 1)
         */
        act_clause_bump(s, c);
        /*@ Assert (exists cla_inc1,
              s == s@pre && cls == cls@pre &&
              c != 0 &&
              msat_fp32_nonnegative(cla_inc1) &&
              record_enqueue_success(
                rec_n, rec_F, rec_A_arr, rec_A_inst, M, Mstage, rec_words, c, Menq) &&
              store(&(begin), lit *, learnt_ptr) * has_permission(&endvar) *
              Vecp::rep(&(s->learnts), db_words(ms_learnt(Menq))) *
              clause_db_rep(ms_learnt(Menq)) *
              store(&(s->cla_inc), float, cla_inc1) *
              store(&(s->stats.learnts), unsigned long long,
                    stats_learnts(ms_stats(Menq))) *
              store(&(s->stats.learnts_literals), unsigned long long,
                    stats_learnts_literals(ms_stats(Menq))) *
              solver_record_finish_frame_at(s, Menq, levels_ptr, rec_wl) *
              Veci::rep_ptr(cls, learnt_ptr, rec_words)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
         */
        /*@ Given cla_inc1 */
        s->stats.learnts++;
        s->stats.learnts_literals += veci_size(cls);
        /*@ Assert (exists Mstats,
              s == s@pre && cls == cls@pre &&
              record_finish_with_capacity(
                rec_n, rec_F, rec_A_arr, rec_A_inst, M, Menq, rec_words, c,
                cla_inc1, Mstats) &&
              store(&(begin), lit *, learnt_ptr) * has_permission(&endvar) *
              solver_rep_levels_wl_at(s, Mstats, rec_wl, levels_ptr) *
              Veci::rep_ptr(cls, learnt_ptr, rec_words)) *
          store(&l_Undef, char, 0) * store(&true, int, 1)
         */
    }

}

static double solver_progress(solver* s)
/*@ With n (assigns0 levels0 : list Z) assigns_ptr levels_ptr
    Require (0 <= n && n <= INT_MAX && Zlength(assigns0) == n &&
            Zlength(levels0) == n &&
            store(&(s->size), n) *
            store(&(s->assigns), assigns_ptr) *
            store(&(s->levels), levels_ptr) *
            CharArray::seg(assigns_ptr, 0, n, assigns0) *
            IntArray::seg(levels_ptr, 0, n, levels0)) *
            store(&l_Undef, char, 0)
    Ensure (msat_fp64_value(__return) &&
           store(&(s->size), n) *
           store(&(s->assigns), assigns_ptr) *
           store(&(s->levels), levels_ptr) *
           CharArray::seg(assigns_ptr, 0, n, assigns0) *
           IntArray::seg(levels_ptr, 0, n, levels0)) *
            store(&l_Undef, char, 0)
 */
{
    lbool*  values = s->assigns;
    int*    levels = s->levels;
    int     i;

    double  progress = 0;
    double  F        = 1.0 / s->size;
    /*@ Inv Assert (exists (progress_now F_now : fp64),
                   s == s@pre &&
                   values == assigns_ptr && levels == levels_ptr &&
                   0 <= i && i <= n &&
                   store(&(s->size), n) *
                   store(&(s->assigns), assigns_ptr) *
                   store(&(s->levels), levels_ptr) *
                   CharArray::seg(assigns_ptr, 0, n, assigns0) *
                   IntArray::seg(levels_ptr, 0, n, levels0) *
                   store(&progress, double, progress_now) *
                   store(&F, double, F_now)) *
          store(&l_Undef, char, 0)
     */
    for (i = 0; i < s->size; i++)
        if (values[i] != l_Undef)
            progress += pow(F, levels[i]);
    return progress / s->size;
}

/* One search restart: propagate, learn/backjump/record on conflict, or
   prepare a model or decision. Results: 1 model, 0 budget exhaustion, -1
   root refutation. */
static lbool solver_search(solver* s, int nof_conflicts, int nof_learnts)
/*@ With (search_wl : Z) (n : Z) (F : cnf) (A_arr A_inst : list literal) (M : msolver)
    Require (solver_search_pre(s, n, F, A_arr, A_inst, M, search_wl)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
    Ensure (-1 <= __return && __return <= 1 &&
            solver_search_result(s, n, F, A_arr, A_inst, __return, search_wl, M)) *
            store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
 */
{
    /*@ solver_search_pre(s, n, F, A_arr, A_inst, M, search_wl)
        which implies exists levels_entry,
          msolver_inv(n, F, A_arr, A_inst, M) &&
          solver_at_root(M) &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          store(&(s->levels), int *, levels_entry) *
          IntArray::seg(levels_entry, 0, ms_size(M),
                        mt_levels(ms_core(M))) *
          solver_int_tail(levels_entry, ms_size(M), ms_cap(M)) *
          solver_cancel_owned(s, M, search_wl)
     */
    /*@ Given levels_entry */
    int*    levels          = s->levels;
    double  var_decay       = 0.95;
    double  clause_decay    = 0.999;
    double  random_var_freq = 0.02;

    uint64  conflictC       = 0;
    veci    learnt_clause;

    /*@ levels == levels_entry &&
          solver_shape(M) &&
          store(&(s->levels), int *, levels_entry) *
          IntArray::seg(levels_entry, 0, ms_size(M),
                        mt_levels(ms_core(M))) *
          solver_int_tail(levels_entry, ms_size(M), ms_cap(M)) *
          solver_cancel_owned(s, M, search_wl)
        which implies solver_rep_levels_wl_at(s, M, search_wl, levels)
     */
    /*@ solver_rep_levels_wl_at(s, M, search_wl, levels)
        which implies
          store(&(s->root_level), int, ms_root_level(M)) *
          Veci::rep(&(s->trail_lim),
                   mt_lim(ms_core(M))) *
          solver_search_root_frame_at(s, M, levels, search_wl)
     */
    /*@ solver_at_root(M)
        which implies
          ms_root_level(M) == Zlength(mt_lim(ms_core(M)))
     */
    assert(s->root_level == solver_dlevel(s));

    /*@ store(&(s->root_level), int, ms_root_level(M)) *
          Veci::rep(&(s->trail_lim),
                   mt_lim(ms_core(M))) *
          solver_search_root_frame_at(s, M, levels, search_wl)
        which implies
          store(&(s->stats.starts), uint64, stats_starts(ms_stats(M))) *
          store(&(s->var_decay), double, ms_var_decay(M)) *
          store(&(s->cla_decay), float, ms_cla_decay(M)) *
          Veci::rep(&(s->model), ms_model(M)) *
          solver_search_init_frame_at(s, M, levels, search_wl)
     */
    s->stats.starts++;
    s->var_decay = (float)(1 / var_decay   );
    s->cla_decay = (float)(1 / clause_decay);
    veci_resize(&s->model,0);
    veci_new(&learnt_clause);

    /*@ exists starts_now (vd : fp64) (cd : fp32),
          msolver_inv(n, F, A_arr, A_inst, M) &&
          solver_at_root(M) &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          msat_fp32_positive_finite(cd) &&
          store(&(s->stats.starts), uint64, starts_now) *
          store(&(s->var_decay), double, vd) *
          store(&(s->cla_decay), float, cd) *
          Veci::rep(&(s->model), sublist(0, 0, ms_model(M))) *
          solver_search_init_frame_at(s, M, levels, search_wl) *
          Veci::rep(&(learnt_clause), nil)
        which implies
          solver_search_loop(
            s, &(learnt_clause), levels, n, F, A_arr, A_inst, search_wl, M)
     */
    /*@ Inv Assert (exists conflict_budget_value learnt_budget_value
                     conflict_count_value (random_value : fp64),
          s == s@pre &&
          0 <= conflict_count_value &&
          solver_search_loop(
          s, &(learnt_clause), levels, n, F, A_arr, A_inst, search_wl, M) *
          store(&nof_conflicts, int, conflict_budget_value) *
          store(&nof_learnts, int, learnt_budget_value) *
          store(&random_var_freq, double, random_value) *
          has_permission(&var_decay) * has_permission(&clause_decay) *
          store(&conflictC, uint64, conflict_count_value)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */

    for (;;) {
        /*@ solver_search_loop(s, &(learnt_clause), levels, n, F,
                A_arr, A_inst, search_wl, M)
            which implies exists (Mcur : msolver) assigns_ptr
                                 (learnt_words : list Z),
              ms_cap(Mcur) == ms_cap(M) && solver_search_reuse(M, Mcur) &&
              solver_propagation_inv(n, F, A_arr, PropagationStable(A_inst), Mcur) &&
              msolver_seed_shadow(Mcur) && ms_model(Mcur) == nil &&
              msat_fp32_positive_finite(ms_cla_decay(Mcur)) &&
              solver_rep_assigns_levels_at(s, Mcur, assigns_ptr, levels, search_wl) *
              Veci::rep(&(learnt_clause), learnt_words)
         */
        /*@ Given Mcur assigns_ptr learnt_words */
        clause *confl = solver_propagate(s);


        if (confl != 0){
            // CONFLICT
            int blevel;

            /*@ Given propagation_result result_focus result_clause */
            /*@ exists conflict_word,
                  conflict_word != 0 && ms_cap(Mcur) == ms_cap(M) &&
                  solver_search_reuse(M, Mcur) && ms_model(Mcur) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mcur)) &&
                  propagation_cancel_ready(n, F, A_arr, PropagationStable(A_inst),
                                           propagation_result, result_focus) &&
                  propagation_caller_frame(Mcur, propagation_result) &&
                  (minisat_base_watch_completed(Mcur) =>
                   minisat_watch_conflict_ready(n, propagation_result)) &&
                  minisat_resident_false_clause(propagation_result) && msolver_seed_shadow(propagation_result) &&
                  propagation_conflict_cert(n, F, propagation_result, result_clause) &&
                  conflict_ptr_denotes(propagation_result, conflict_word, result_clause) &&
                  solver_rep_assigns_levels_at(s, propagation_result, assigns_ptr, levels, search_wl) *
                  data_at(&confl, conflict_word)
                which implies exists (Mconf : msolver) p focus
                                            (Cconf : clause),
                  ms_cap(Mconf) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_watch_conflict_ready(n, Mconf)) &&
                  minisat_resident_false_clause(Mconf) &&
                  propagation_cancel_ready(
                    n, F, A_arr, PropagationStable(A_inst),
                    Mconf, focus) &&
                  propagation_conflict_cert(n, F, Mconf, Cconf) &&
                  conflict_ptr_denotes(Mconf, p, Cconf) &&
                  ms_model(Mconf) == nil &&
                  msolver_seed_shadow(Mconf) &&
                  msat_fp32_positive_finite(ms_cla_decay(Mconf)) &&
                  msat_fp32_same(
                    ms_cla_decay(Mconf), ms_cla_decay(Mcur)) &&
                  solver_rep_assigns_levels_at(
                    s, Mconf, assigns_ptr, levels, search_wl) * data_at(&confl, p)
             */
            /*@ Given Mconf p focus Cconf */
            /*@ solver_rep_assigns_levels_at(
                  s, Mconf, assigns_ptr, levels, search_wl)
                which implies
                  store(&(s->stats.conflicts), uint64, stats_conflicts(ms_stats(Mconf))) *
                  store(&(s->root_level), int, ms_root_level(Mconf)) *
                  Veci::rep(&(s->trail_lim),
                           mt_lim(ms_core(Mconf))) *
                  solver_search_conflict_frame_at(s, Mconf, levels, search_wl)
             */

#ifdef VERBOSEDEBUG
            printf(L_IND"**CONFLICT**\n", L_ind);
#endif
            s->stats.conflicts++; conflictC++;
            if (solver_dlevel(s) == s->root_level){
                /*@ exists conflicts_now,
                      ms_cap(Mconf) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_watch_conflict_ready(n, Mconf)) &&
                      minisat_resident_false_clause(Mconf) &&
          propagation_cancel_ready(
                        n, F, A_arr, PropagationStable(A_inst),
                        Mconf, focus) &&
                      propagation_conflict_cert(n, F, Mconf, Cconf) &&
                      conflict_ptr_denotes(Mconf, p, Cconf) &&
                      msolver_seed_shadow(Mconf) &&
                      ms_model(Mconf) == nil &&
                      msat_fp32_positive_finite(ms_cla_decay(Mconf)) &&
                      Zlength(mt_lim(ms_core(Mconf))) <=
                        ms_root_level(Mconf) &&
                      ms_root_level(Mconf) <=
                        Zlength(mt_lim(ms_core(Mconf))) &&
                      store(&(s->stats.conflicts), uint64, conflicts_now) *
                      store(&(s->root_level), int, ms_root_level(Mconf)) *
                      Veci::rep(&(s->trail_lim),
                               mt_lim(ms_core(Mconf))) *
                      solver_search_conflict_frame_at(s, Mconf, levels, search_wl)
                    which implies exists (Mrootconf : msolver),
                      ms_cap(Mrootconf) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           solver_search_conflict_reuse(n, F, A_arr, A_inst, Mrootconf)) &&
                      msolver_inv_weak(
                        n, F, A_arr, A_inst, Mrootconf) &&
                      solver_at_root(Mrootconf) &&
                      cancel_bound_ready(Mrootconf, 0) &&
                      ms_capacity_root_propagation_pending(Mrootconf) == 0 &&
                      cnf_unsat(n, cnf_with_units(F, A_arr)) &&
                      ms_model(Mrootconf) == nil &&
                      solver_rep_levels_wl_at(s, Mrootconf, search_wl, levels)
                 */
                veci_delete(&learnt_clause);
                return l_False;
            }

            veci_resize(&learnt_clause,0);
            /*@ exists conflicts_now,
                  ms_cap(Mconf) == ms_cap(M) &&
          (minisat_base_watch_completed(M) =>
           minisat_watch_conflict_ready(n, Mconf)) &&
                  minisat_resident_false_clause(Mconf) &&
                  ms_cap(Mcur) == ms_cap(M) &&
                  solver_search_reuse(M, Mcur) &&
          propagation_cancel_ready(
                    n, F, A_arr, PropagationStable(A_inst),
                    Mconf, focus) &&
                  propagation_conflict_cert(n, F, Mconf, Cconf) &&
                  conflict_ptr_denotes(Mconf, p, Cconf) &&
                  msolver_seed_shadow(Mconf) &&
                  ms_model(Mconf) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mconf)) &&
                  msat_fp32_same(
                    ms_cla_decay(Mconf), ms_cla_decay(Mcur)) &&
                  Zlength(mt_lim(ms_core(Mconf))) != ms_root_level(Mconf) &&
                  store(&(s->stats.conflicts), uint64, conflicts_now) *
                  store(&(s->root_level), int, ms_root_level(Mconf)) *
                  Veci::rep(&(s->trail_lim),
                           mt_lim(ms_core(Mconf))) *
                  solver_search_conflict_frame_at(s, Mconf, levels, search_wl) *
                  Veci::rep(&(learnt_clause),
                           sublist(0, 0, learnt_words))
                which implies exists (Manalyze : msolver),
                  ms_cap(Manalyze) == ms_cap(M) &&
                  solver_search_reuse(M, Manalyze) &&
                  Manalyze == msolver_with_cla_inc_stats(
                    Mconf, ms_cla_inc(Mconf),
                    stats_set_conflicts(conflicts_now, ms_stats(Mconf))) &&
                  propagation_cancel_ready(
                    n, F, A_arr, PropagationStable(A_inst),
                    Manalyze, focus) &&
                  propagation_conflict_cert(n, F, Manalyze, Cconf) &&
                  conflict_ptr_denotes(Manalyze, p, Cconf) &&
                  msolver_seed_shadow(Manalyze) &&
                  ms_model(Manalyze) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Manalyze)) &&
                  msat_fp32_same(
                    ms_cla_decay(Manalyze), ms_cla_decay(Mcur)) &&
                  solver_analyze_pre(
                    s, p, &(learnt_clause), levels,
                    n, F, A_arr, PropagationStable(A_inst),
                    Manalyze, focus, Cconf, search_wl)
             */
            /*@ Given Manalyze */
            solver_analyze(s, confl, &learnt_clause)
              /*@ where anz_n = n, anz_F = F, anz_A_arr = A_arr,
                        K = PropagationStable(A_inst), M = Manalyze,
                        anz_focus = focus, C = Cconf,
                        levels_ptr = levels, anz_wl = search_wl */;
            /*@ ms_cap(Manalyze) == ms_cap(M) &&
                  solver_search_reuse(M, Manalyze) &&
                  ms_cap(Mcur) == ms_cap(M) &&
                  solver_search_reuse(M, Mcur) &&
                  ms_model(Manalyze) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Manalyze)) &&
                  msat_fp32_same(
                    ms_cla_decay(Manalyze), ms_cla_decay(Mcur)) &&
                  solver_analyze_post(
                  s, &(learnt_clause), levels, n, F, A_arr,
                  PropagationStable(A_inst), Manalyze, focus, search_wl)
                which implies exists (Manalyzed : msolver)
                                     (words : list Z)
                                     backjump,
                  ms_cap(Manalyzed) == ms_cap(M) &&
                  solver_search_reuse(M, Manalyzed) &&
                  analysis_cancel_ready(
                    n, F, A_arr, PropagationStable(A_inst),
                    Manalyzed, focus) &&
                  ms_tags(Manalyzed) == repeat_Z(0, n) &&
                  ms_tagged(Manalyzed) == nil &&
                  msat_fp32_nonnegative(ms_cla_inc(Manalyzed)) &&
                  analyze_clause_cert(n, F, Manalyzed, words) &&
                  analyze_backjump_cert(
                    n, Manalyzed, words, backjump) &&
                  msolver_seed_shadow(Manalyzed) &&
                  ms_model(Manalyzed) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Manalyzed)) &&
                  msat_fp32_same(
                    ms_cla_decay(Manalyzed), ms_cla_decay(Mcur)) &&
                  1 <= Zlength(words) && Zlength(words) <= n &&
                  Forall(lit_wf_c(n), words) &&
                  0 <= lit_var_c(words[1 - 0]) &&
                  lit_var_c(words[1 - 0]) < ms_size(Manalyzed) &&
                  solver_rep_levels_wl_at(s, Manalyzed, search_wl, levels) *
                  Veci::rep(&(learnt_clause), words)
             */
            /*@ Given Manalyzed words backjump */
            /*@ solver_rep_levels_wl_at(s, Manalyzed, search_wl, levels)
                which implies
                  store(&(s->root_level), int,
                        ms_root_level(Manalyzed)) *
                  Veci::rep(&(s->trail_lim),
                           mt_lim(ms_core(Manalyzed))) *
                  store(&(s->levels), int *, levels) *
                  IntArray::seg(levels, 0, ms_size(Manalyzed),
                                mt_levels(ms_core(Manalyzed))) *
                  solver_int_tail(
                    levels, ms_size(Manalyzed), ms_cap(Manalyzed)) *
                  solver_search_root_payload(s, Manalyzed, search_wl)
             */
            blevel = veci_size(&learnt_clause) > 1 ? levels[lit_var(veci_begin(&learnt_clause)[1]) /*@ where(original) */] : s->root_level;
            blevel = s->root_level > blevel ? s->root_level : blevel;

            /*@ store(&(s->root_level), int,
                      ms_root_level(Manalyzed)) *
                  Veci::rep(&(s->trail_lim),
                           mt_lim(ms_core(Manalyzed))) *
                  store(&(s->levels), int *, levels) *
                  IntArray::seg(levels, 0, ms_size(Manalyzed),
                                mt_levels(ms_core(Manalyzed))) *
                  solver_int_tail(
                    levels, ms_size(Manalyzed), ms_cap(Manalyzed)) *
                  solver_search_root_payload(s, Manalyzed, search_wl)
                which implies solver_rep_levels_wl_at(s, Manalyzed, search_wl, levels)
             */
            /*@ blevel == backjump &&
                  analysis_cancel_ready(
                    n, F, A_arr, PropagationStable(A_inst),
                    Manalyzed, focus) &&
                  ms_tags(Manalyzed) == repeat_Z(0, n) &&
                  ms_tagged(Manalyzed) == nil &&
                  msat_fp32_nonnegative(ms_cla_inc(Manalyzed)) &&
                  analyze_clause_cert(n, F, Manalyzed, words) &&
                  analyze_backjump_cert(
                    n, Manalyzed, words, blevel) &&
                  msolver_seed_shadow(Manalyzed) &&
                  ms_model(Manalyzed) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Manalyzed)) &&
                  msat_fp32_same(
                    ms_cla_decay(Manalyzed), ms_cla_decay(Mcur)) &&
                  solver_rep_levels_wl_at(s, Manalyzed, search_wl, levels) *
                  Veci::rep(&(learnt_clause), words)
             */
            /*@ analysis_cancel_ready(
                  n, F, A_arr, PropagationStable(A_inst),
                  Manalyzed, focus) &&
                  ms_tags(Manalyzed) == repeat_Z(0, n) &&
                  ms_tagged(Manalyzed) == nil &&
                  msat_fp32_nonnegative(ms_cla_inc(Manalyzed)) &&
                  analyze_clause_cert(n, F, Manalyzed, words) &&
                  analyze_backjump_cert(
                    n, Manalyzed, words, blevel) &&
                  msolver_seed_shadow(Manalyzed) &&
                  ms_model(Manalyzed) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Manalyzed)) &&
                  msat_fp32_same(
                    ms_cla_decay(Manalyzed), ms_cla_decay(Mcur)) &&
                  solver_rep_levels_wl_at(s, Manalyzed, search_wl, levels)
                which implies
                  solver_cancel_pre(s, blevel, Manalyzed, search_wl) *
                  solver_levels_slice_at(s, Manalyzed, levels)
             */
            solver_canceluntil(s,blevel);
            /*@ ms_cap(Manalyzed) == ms_cap(M) &&
                  solver_search_reuse(M, Manalyzed) &&
                  ms_cap(Mcur) == ms_cap(M) &&
                  solver_search_reuse(M, Mcur) &&
          analysis_cancel_ready(
                  n, F, A_arr, PropagationStable(A_inst),
                  Manalyzed, focus) &&
                  ms_tags(Manalyzed) == repeat_Z(0, n) &&
                  ms_tagged(Manalyzed) == nil &&
                  msat_fp32_nonnegative(ms_cla_inc(Manalyzed)) &&
                  analyze_clause_cert(n, F, Manalyzed, words) &&
                  analyze_backjump_cert(
                    n, Manalyzed, words, blevel) &&
                  msolver_seed_shadow(Manalyzed) &&
                  ms_model(Manalyzed) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Manalyzed)) &&
                  ms_model(Mcur) == nil &&
                  msat_fp32_same(
                    ms_cla_decay(Manalyzed), ms_cla_decay(Mcur)) &&
                  solver_cancel_post(s, blevel, Manalyzed, search_wl) *
                  solver_levels_slice_at(s, Manalyzed, levels) *
                  Veci::rep(&(learnt_clause), words)
                which implies exists (Mback : msolver),
                  ms_cap(Mback) == ms_cap(M) &&
                  solver_search_reuse(M, Mback) &&
                  record_watch1_positive(Mback, words) &&
                  solver_search_backjump_ready(
                    n, F, A_arr, A_inst, Mcur, Mback, words) &&
                  msat_fp32_positive_finite(ms_cla_decay(Mback)) &&
                  1 <= Zlength(words) &&
                  solver_rep_levels_wl_at(s, Mback, search_wl, levels) *
                  Veci::rep(&(learnt_clause), words) *
                  has_permission(&blevel)
             */
            /*@ Given Mback */
            /*@ solver_search_backjump_ready(
                  n, F, A_arr, A_inst, Mcur, Mback, words) &&
                  1 <= Zlength(words) &&
                  solver_rep_levels_wl_at(s, Mback, search_wl, levels) *
                  Veci::rep(&(learnt_clause), words)
                which implies
                  solver_record_pre_at(
                    s, &(learnt_clause), levels, n, F, A_arr, A_inst,
                    Mback, words, search_wl)
             */
            solver_record(s, &learnt_clause);
            /*@
                  ms_cap(Mback) == ms_cap(M) &&
                  solver_search_reuse(M, Mback) &&
                  record_watch1_positive(Mback, words) &&
                  ms_model(Mback) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mback)) &&
                  solver_record_post_at(
                  s, &(learnt_clause), levels, n, F, A_arr, A_inst,
                  Mback, words, 1, search_wl)
                which implies exists (Mrecord : msolver),
                  ms_cap(Mrecord) == ms_cap(M) &&
                  solver_search_reuse(M, Mrecord) &&
                  msolver_inv(n, F, A_arr, A_inst, Mrecord) &&
                  ms_capacity_root_propagation_pending(Mrecord) == 0 &&
                  msolver_seed_shadow(Mrecord) &&
                  ms_model(Mrecord) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mrecord)) &&
                  solver_rep_levels_wl_at(s, Mrecord, search_wl, levels) *
                  Veci::rep(&(learnt_clause), words)
             */
            /*@ Given Mrecord */
            /*@ msat_fp32_nonnegative(ms_cla_inc(Mrecord)) &&
                msat_fp32_positive_finite(ms_cla_decay(Mrecord)) &&
                solver_rep_levels_wl_at(s, Mrecord, search_wl, levels)
                which implies
                  msat_fp32_nonnegative(ms_cla_inc(Mrecord)) &&
                  msat_fp32_positive_finite(ms_cla_decay(Mrecord)) &&
                  store(&(s->var_inc), double, ms_var_inc(Mrecord)) *
                  store(&(s->var_decay), double, ms_var_decay(Mrecord)) *
                  store(&(s->cla_inc), float, ms_cla_inc(Mrecord)) *
                  store(&(s->cla_decay), float, ms_cla_decay(Mrecord)) *
                  solver_search_decay_frame_at(s, Mrecord, levels, search_wl)
             */
            act_var_decay(s);
            act_clause_decay(s);

            /*@ exists (var_inc_now var_decay_now : fp64)
                       (cla_inc_now cla_decay_now : fp32),
                  ms_cap(Mrecord) == ms_cap(M) &&
                  solver_search_reuse(M, Mrecord) &&
                  msolver_inv(n, F, A_arr, A_inst, Mrecord) &&
                  ms_capacity_root_propagation_pending(Mrecord) == 0 &&
                  msolver_seed_shadow(Mrecord) &&
                  ms_model(Mrecord) == nil &&
                  msat_fp32_nonnegative(cla_inc_now) &&
                  msat_fp32_positive_finite(cla_decay_now) &&
                  store(&(s->var_inc), double, var_inc_now) *
                  store(&(s->var_decay), double, var_decay_now) *
                  store(&(s->cla_inc), float, cla_inc_now) *
                  store(&(s->cla_decay), float, cla_decay_now) *
                  solver_search_decay_frame_at(s, Mrecord, levels, search_wl) *
                  Veci::rep(&(learnt_clause), words)
                which implies
                  solver_search_loop(
                    s, &(learnt_clause), levels, n, F, A_arr, A_inst, search_wl, M)
             */
            /*@ Assert (exists conflict_budget_value learnt_budget_value
                         conflict_count_value (random_value : fp64),
                  s == s@pre &&
                  0 <= conflict_count_value &&
                  solver_search_loop(
                  s, &(learnt_clause), levels, n, F, A_arr, A_inst, search_wl, M) *
                  store(&nof_conflicts, int, conflict_budget_value) *
                  store(&nof_learnts, int, learnt_budget_value) *
                  store(&random_var_freq, double, random_value) *
                  has_permission(&var_decay) * has_permission(&clause_decay) *
                  store(&conflictC, uint64, conflict_count_value) *
                  has_permission(&confl) *
                  has_permission(&blevel)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
             */

        }else{
            // NO CONFLICT
            int next;

            /*@ Given propagation_result */
            /*@
                  confl == 0 && ms_cap(Mcur) == ms_cap(M) &&
                  solver_search_reuse(M, Mcur) && ms_model(Mcur) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mcur)) &&
                  solver_propagation_inv(n, F, A_arr, PropagationStable(A_inst), propagation_result) &&
                  propagation_caller_frame(Mcur, propagation_result) &&
                  minisat_propagation_reuse_live(Mcur, propagation_result) &&
                  msolver_seed_shadow(propagation_result) && mt_qhead(ms_core(propagation_result)) == ms_qtail(propagation_result) &&
                  solver_rep_assigns_levels_at(s, propagation_result, assigns_ptr, levels, search_wl)
                which implies exists (Mstable : msolver),
                  ms_cap(Mstable) == ms_cap(M) &&
                  solver_search_reuse(M, Mstable) &&
                  msolver_inv(n, F, A_arr, A_inst, Mstable) &&
                  mt_qhead(ms_core(Mstable)) == ms_qtail(Mstable) &&
                  ms_capacity_root_propagation_pending(Mstable) == 0 &&
                  msolver_seed_shadow(Mstable) &&
                  ms_model(Mstable) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mstable)) &&
                  solver_rep_assigns_levels_at(
                    s, Mstable, assigns_ptr, levels, search_wl) * data_at(&confl, 0)
             */
            /*@ Given Mstable */

            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                /*@ solver_rep_assigns_levels_at(
                      s, Mstable, assigns_ptr, levels, search_wl)
                    which implies
                      store(&(s->size), int, ms_size(Mstable)) *
                      store(&(s->assigns), char *, assigns_ptr) *
                      CharArray::seg(
                        assigns_ptr, 0, ms_size(Mstable),
                        mt_assigns(ms_core(Mstable))) *
                      store(&(s->levels), int *, levels) *
                      IntArray::seg(
                        levels, 0, ms_size(Mstable),
                        mt_levels(ms_core(Mstable))) *
                      store(&(s->progress_estimate), double,
                            ms_progress(Mstable)) *
                      solver_search_progress_frame_at(
                        s, Mstable, assigns_ptr, levels, search_wl)
                 */
                s->progress_estimate = solver_progress(s);
                /*@ exists (progress_now : fp64),
                      ms_cap(Mstable) == ms_cap(M) &&
                      solver_search_reuse(M, Mstable) &&
                      msolver_inv(n, F, A_arr, A_inst, Mstable) &&
                      mt_qhead(ms_core(Mstable)) == ms_qtail(Mstable) &&
                      ms_capacity_root_propagation_pending(Mstable) == 0 &&
                      msolver_seed_shadow(Mstable) &&
                      ms_model(Mstable) == nil &&
                      msat_fp32_positive_finite(ms_cla_decay(Mstable)) &&
                      store(&(s->size), int, ms_size(Mstable)) *
                      store(&(s->assigns), char *, assigns_ptr) *
                      CharArray::seg(
                        assigns_ptr, 0, ms_size(Mstable),
                        mt_assigns(ms_core(Mstable))) *
                      store(&(s->levels), int *, levels) *
                      IntArray::seg(
                        levels, 0, ms_size(Mstable),
                        mt_levels(ms_core(Mstable))) *
                      store(&(s->progress_estimate), double, progress_now) *
                      solver_search_progress_frame_at(
                        s, Mstable, assigns_ptr, levels, search_wl)
                    which implies exists (Mprogress : msolver),
                      ms_cap(Mprogress) == ms_cap(M) &&
                      solver_search_reuse(M, Mprogress) &&
                      msolver_inv(n, F, A_arr, A_inst, Mprogress) &&
                      mt_qhead(ms_core(Mprogress)) == ms_qtail(Mprogress) &&
                      ms_capacity_root_propagation_pending(Mprogress) == 0 &&
                      msolver_seed_shadow(Mprogress) &&
                      ms_model(Mprogress) == nil &&
                      msat_fp32_positive_finite(ms_cla_decay(Mprogress)) &&
                      solver_rep_assigns_levels_at(
                        s, Mprogress, assigns_ptr, levels, search_wl)
                 */
                /*@ Given Mprogress */
                /*@ solver_rep_assigns_levels_at(
                      s, Mprogress, assigns_ptr, levels, search_wl)
                    which implies
                      store(&(s->root_level), int,
                            ms_root_level(Mprogress)) *
                      Veci::rep(&(s->trail_lim),
                        mt_lim(ms_core(Mprogress))) *
                      solver_search_root_frame_at(
                        s, Mprogress, levels, search_wl)
                 */
                /*@ msolver_inv(n, F, A_arr, A_inst, Mprogress) &&
                      mt_qhead(ms_core(Mprogress)) == ms_qtail(Mprogress) &&
                      msat_fp32_positive_finite(ms_cla_decay(Mprogress)) &&
                      store(&(s->root_level), int,
                            ms_root_level(Mprogress)) *
                      Veci::rep(&(s->trail_lim),
                        mt_lim(ms_core(Mprogress))) *
                      solver_search_root_frame_at(
                        s, Mprogress, levels, search_wl)
                    which implies
                      solver_cancel_pre(
                        s, ms_root_level(Mprogress), Mprogress, search_wl) *
                      solver_levels_slice_at(s, Mprogress, levels)
                 */
                solver_canceluntil(s,s->root_level) /*@ where M = Mprogress, wl = search_wl */;
                /*@ ms_cap(Mprogress) == ms_cap(M) &&
                      solver_search_reuse(M, Mprogress) &&
                      msolver_inv(n, F, A_arr, A_inst, Mprogress) &&
                      mt_qhead(ms_core(Mprogress)) == ms_qtail(Mprogress) &&
                      ms_capacity_root_propagation_pending(Mprogress) == 0 &&
                      msolver_seed_shadow(Mprogress) &&
                      ms_model(Mprogress) == nil &&
                      msat_fp32_positive_finite(ms_cla_decay(Mprogress)) &&
                      solver_cancel_post(
                        s, ms_root_level(Mprogress), Mprogress, search_wl) *
                      solver_levels_slice_at(s, Mprogress, levels)
                    which implies exists (Mrestart : msolver),
                      ms_cap(Mrestart) == ms_cap(M) &&
                      solver_search_reuse(M, Mrestart) &&
                      msolver_inv(n, F, A_arr, A_inst, Mrestart) &&
                      solver_at_root(Mrestart) &&
                      mt_qhead(ms_core(Mrestart)) == ms_qtail(Mrestart) &&
                      ms_capacity_root_propagation_pending(Mrestart) == 0 &&
                      msolver_seed_shadow(Mrestart) &&
                      ms_model(Mrestart) == nil &&
                      msat_fp32_positive_finite(ms_cla_decay(Mrestart)) &&
                      solver_rep_levels_wl_at(s, Mrestart, search_wl, levels)
                 */
                veci_delete(&learnt_clause);
                return l_Undef; }

            /*@ solver_rep_assigns_levels_at(
                  s, Mstable, assigns_ptr, levels, search_wl)
                which implies
                  store(&(s->root_level), int,
                        ms_root_level(Mstable)) *
                  Veci::rep(&(s->trail_lim),
                    mt_lim(ms_core(Mstable))) *
                  solver_search_root_frame_at(s, Mstable, levels, search_wl)
             */
            if (solver_dlevel(s) == 0)
                // Simplify the set of problem clauses:
                /*@ msolver_inv(n, F, A_arr, A_inst, Mstable) &&
                      Zlength(mt_lim(ms_core(Mstable))) == 0 &&
                      ms_capacity_root_propagation_pending(Mstable) == 0 &&
                      msolver_seed_shadow(Mstable) &&
                      store(&(s->root_level), int,
                          ms_root_level(Mstable)) *
                      Veci::rep(&(s->trail_lim),
                        mt_lim(ms_core(Mstable))) *
                      solver_search_root_frame_at(s, Mstable, levels, search_wl)
                    which implies A_inst == nil && ms_root_level(Mstable) == 0 &&
                      solver_simplify_pre_at(
                      s, n, F, A_arr, Mstable, levels, search_wl)
                 */
                solver_simplify(s)
                  /*@ where (solver_simplify_spec)
                            smp_n = n, smp_F = F, smp_A_arr = A_arr,
                            M = Mstable,
                            levels_ptr = levels, smp_wl = search_wl */;

            /*@ Assert (exists (Mclean : msolver) (search_levels : Z),
                  s == s@pre && levels == search_levels && 0 <= conflictC &&
                  ms_cap(Mclean) == ms_cap(M) &&
                  solver_search_reuse(M, Mclean) &&
                  msolver_inv(n, F, A_arr, A_inst, Mclean) &&
                  mt_qhead(ms_core(Mclean)) == ms_qtail(Mclean) &&
                  ms_capacity_root_propagation_pending(Mclean) == 0 &&
                  msolver_seed_shadow(Mclean) && ms_model(Mclean) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mclean)) &&
                  solver_rep_levels_wl_at(s, Mclean, search_wl, search_levels) *
                  Veci::rep(&(learnt_clause),
                           learnt_words) *
                  store(&nof_conflicts, int, nof_conflicts) *
                  store(&nof_learnts, int, nof_learnts) *
                  store(&random_var_freq, double, random_var_freq) *
                  has_permission(&var_decay) * has_permission(&clause_decay) *
                  has_permission(&confl) *
                  has_permission(&next)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
             */
            /*@ Given Mclean search_levels */

            /*@ solver_rep_levels_wl_at(s, Mclean, search_wl, levels)
                which implies
                  store(&(s->qtail), int, ms_qtail(Mclean)) *
                  Vecp::rep(&(s->learnts),
                    db_words(ms_learnt(Mclean))) *
                  solver_search_reducedb_frame_at(
                    s, Mclean, levels, search_wl)
             */
            if (nof_learnts >= 0 && vecp_size(&s->learnts) - s->qtail >= nof_learnts)
                // Reduce the set of learnt clauses:
                /*@ msolver_inv(n, F, A_arr, A_inst, Mclean) &&
                      mt_qhead(ms_core(Mclean)) == ms_qtail(Mclean) &&
                      ms_capacity_root_propagation_pending(Mclean) == 0 &&
                      msolver_seed_shadow(Mclean) &&
                      msat_fp32_positive_finite(ms_cla_decay(Mclean)) &&
                      store(&(s->qtail), int, ms_qtail(Mclean)) *
                      Vecp::rep(&(s->learnts),
                        db_words(ms_learnt(Mclean))) *
                      solver_search_reducedb_frame_at(
                        s, Mclean, levels, search_wl)
                    which implies solver_reducedb_pre_at(
                      s, levels, n, F, A_arr, A_inst, Mclean, search_wl)
                 */
                solver_reducedb(s);

            /*@ Assert (exists (Mdb : msolver),
                  s == s@pre && levels == search_levels && 0 <= conflictC &&
                  ms_cap(Mdb) == ms_cap(M) &&
                  solver_search_reuse(M, Mdb) &&
                  msolver_inv(n, F, A_arr, A_inst, Mdb) &&
                  mt_qhead(ms_core(Mdb)) == ms_qtail(Mdb) &&
                  ms_capacity_root_propagation_pending(Mdb) == 0 &&
                  msolver_seed_shadow(Mdb) && ms_model(Mdb) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mdb)) &&
                  solver_rep_levels_wl_at(s, Mdb, search_wl, search_levels) *
                  Veci::rep(&(learnt_clause),
                           learnt_words) *
                  store(&nof_conflicts, int, nof_conflicts) *
                  store(&nof_learnts, int, nof_learnts) *
                  store(&random_var_freq, double, random_var_freq) *
                  has_permission(&var_decay) * has_permission(&clause_decay) *
                  has_permission(&confl) *
                  has_permission(&next)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
             */
            /*@ Given Mdb */

            // New variable decision:
            /*@ msolver_inv(n, F, A_arr, A_inst, Mdb) &&
                  mt_qhead(ms_core(Mdb)) == ms_qtail(Mdb)
                which implies
                  msolver_inv(n, F, A_arr, A_inst, Mdb) &&
                  mt_qhead(ms_core(Mdb)) == ms_qtail(Mdb) &&
                  order_select_pre(
                    ms_size(Mdb), ms_order(Mdb), ms_orderpos(Mdb),
                    mt_assigns(ms_core(Mdb)), mt_trail(ms_core(Mdb)),
                    mt_qhead(ms_core(Mdb)))
             */
            /*@ msolver_seed_shadow(Mdb) &&
                  msat_fp32_positive_finite(ms_cla_decay(Mdb)) &&
                  solver_rep_levels_wl_at(s, Mdb, search_wl, levels)
                which implies exists activity_ptr assigns_select
                                     orderpos_ptr seed_shadow,
                  1 <= seed_shadow && seed_shadow <= 2147483646 &&
                  ms_random_seed(Mdb) == Z_to_fp64(seed_shadow) &&
                  store(&(s->size), int, ms_size(Mdb)) *
                  store(&(s->random_seed), double,
                        ms_random_seed(Mdb)) *
                  store(&(s->stats.decisions), uint64,
                        stats_decisions(ms_stats(Mdb))) *
                  store(&(s->activity), double *, activity_ptr) *
                  DoubleArray::seg(
                    activity_ptr, 0, ms_size(Mdb), ms_activity(Mdb)) *
                  store(&(s->assigns), char *, assigns_select) *
                  CharArray::seg(
                    assigns_select, 0, ms_size(Mdb),
                    mt_assigns(ms_core(Mdb))) *
                  store(&(s->orderpos), int *, orderpos_ptr) *
                  IntArray::seg(
                    orderpos_ptr, 0, ms_size(Mdb), ms_orderpos(Mdb)) *
                  Veci::rep(&(s->order),
                    ms_order(Mdb)) *
                  solver_search_order_frame_at(
                    s, Mdb, levels, activity_ptr,
                    assigns_select, orderpos_ptr, search_wl)
             */
            /*@ Given activity_ptr assigns_select orderpos_ptr */
            s->stats.decisions++;
            /*@ Given select_seed_shadow from seed_shadow */
            next = order_select(s,(float)random_var_freq) /*@ where seed_shadow = select_seed_shadow */;
            /*@ Given order_now from heap1
                      orderpos_now from orderpos1
                      seed_now from seed_value1
                      seed_shadow_now from seed_shadow1 */

            /*@ ms_cap(Mdb) == ms_cap(M) &&
                  solver_search_reuse(M, Mdb) &&
                  msolver_inv(n, F, A_arr, A_inst, Mdb) &&
                  mt_qhead(ms_core(Mdb)) == ms_qtail(Mdb) &&
                  ms_capacity_root_propagation_pending(Mdb) == 0 &&
                  msolver_seed_shadow(Mdb) &&
                  ms_model(Mdb) == nil &&
                  msat_fp32_positive_finite(ms_cla_decay(Mdb)) &&
                  order_select_post(
                    ms_size(Mdb), next, ms_order(Mdb), order_now,
                    orderpos_now, mt_assigns(ms_core(Mdb)),
                    mt_trail(ms_core(Mdb)), mt_qhead(ms_core(Mdb))) &&
                  seed_now == Z_to_fp64(seed_shadow_now) &&
                  1 <= seed_shadow_now &&
                  seed_shadow_now <= 2147483646 &&
                  store(&(s->size), int, ms_size(Mdb)) *
                  store(&(s->random_seed), double, seed_now) *
                  store(&(s->stats.decisions), uint64,
                        unsigned_last_nbits(
                          stats_decisions(ms_stats(Mdb)) + 1, 64)) *
                  store(&(s->activity), double *, activity_ptr) *
                  DoubleArray::seg(
                    activity_ptr, 0, ms_size(Mdb), ms_activity(Mdb)) *
                  store(&(s->assigns), char *, assigns_select) *
                  CharArray::seg(
                    assigns_select, 0, ms_size(Mdb),
                    mt_assigns(ms_core(Mdb))) *
                  store(&(s->orderpos), int *, orderpos_ptr) *
                  IntArray::seg(
                    orderpos_ptr, 0, ms_size(Mdb), orderpos_now) *
                  Veci::rep(&(s->order), order_now) *
                  solver_search_order_frame_at(
                    s, Mdb, levels, activity_ptr,
                    assigns_select, orderpos_ptr, search_wl)
                which implies exists (Mselected : msolver)
                                     (orderpos_after order_after
                                      stats_after : list Z)
                                     (seed_after : fp64),
                  ms_cap(Mselected) == ms_cap(M) &&
                  solver_search_reuse(M, Mselected) &&
                  solver_search_select_transition(
                    n, F, A_arr, A_inst, Mdb, next,
                    orderpos_after, order_after,
                    seed_after, stats_after, Mselected) &&
                  msat_fp32_positive_finite(ms_cla_decay(Mselected)) &&
                  solver_rep_levels_wl_at(s, Mselected, search_wl, levels)
             */
            /*@ Given Mselected orderpos_after order_after stats_after seed_after */

            if (next == var_Undef){
                // Model found:
                /*@ solver_search_select_transition(
                      n, F, A_arr, A_inst, Mdb, next,
                      orderpos_after, order_after,
                      seed_after, stats_after, Mselected) &&
                      next == -1
                    which implies solver_search_model_ready(
                      n, F, A_arr, A_inst, Mselected) &&
                      has_permission(&next)
                 */
                /*@ ms_size(Mselected) == n &&
                      ms_model(Mselected) == nil &&
                      solver_rep_levels_wl_at(s, Mselected, search_wl, levels)
                    which implies exists values_ptr,
                      store(&(s->size), int, n) *
                      store(&(s->assigns), lbool *, values_ptr) *
                      CharArray::seg(
                        values_ptr, 0, n,
                        mt_assigns(ms_core(Mselected))) *
                      solver_char_tail(
                        values_ptr, n, ms_cap(Mselected)) *
                      Veci::rep(&(s->model), nil) *
                      solver_model_copy_frame_at(
                        s, Mselected, levels, search_wl)
                 */
                /*@ Given values_ptr */
                lbool* values = s->assigns;
                int i;
                /*@ Inv Assert (exists (model_words : list Z),
                      s == s@pre &&
                      ms_cap(Mselected) == ms_cap(M) &&
                      solver_search_reuse(M, Mselected) &&
                      solver_search_model_ready(
                        n, F, A_arr, A_inst, Mselected) &&
                      values == values_ptr &&
                      ms_size(Mselected) == n && 0 <= n &&
                      2 * n <= INT_MAX &&
                      model_copy_progress(
                        n, Mselected, model_words, i) &&
                      Zlength(model_words) == i &&
                      0 <= i && i <= n &&
                      store(&(s->size), n) *
                      store(&(s->assigns), lbool *, values) *
                      CharArray::seg(
                        values, 0, n,
                        mt_assigns(ms_core(Mselected))) *
                      solver_char_tail(
                        values, n, ms_cap(Mselected)) *
                      Veci::rep(
                        &(s->model), model_words) *
                      Veci::rep(&(learnt_clause),
                               learnt_words) *
                      solver_model_copy_frame_at(
                        s, Mselected, levels, search_wl) *
                      store(&nof_conflicts, int, nof_conflicts) *
                      store(&nof_learnts, int, nof_learnts) *
                      has_permission(&random_var_freq) *
                      has_permission(&var_decay) * has_permission(&clause_decay) *
                      has_permission(&conflictC) *
                      has_permission(&confl) *
                      has_permission(&next)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
                 */
                for (i = 0; i < s->size; i++)
                    /*@ Given model_words */
                    /*@ model_copy_progress(
                          n, Mselected, model_words, i) && i < n &&
                          CharArray::seg(
                            values, 0, n,
                            mt_assigns(ms_core(Mselected)))
                        which implies
                          store(pointer_offset(
                                  values, i, char),
                                char,
                                Znth(i,
                                  mt_assigns(ms_core(Mselected)), 0)) *
                          CharArray::missing_i(
                            values, i, 0, n,
                            mt_assigns(ms_core(Mselected)))
                     */
                    veci_push(&s->model,(int)values[i]);

                /*@ exists (model_words_now : list Z),
                      ms_cap(Mselected) == ms_cap(M) &&
                      solver_search_reuse(M, Mselected) &&
          solver_search_model_ready(
                        n, F, A_arr, A_inst, Mselected) &&
                      ms_size(Mselected) == n && 0 <= n &&
                      2 * n <= INT_MAX &&
                      model_copy_progress(
                        n, Mselected, model_words_now, i) &&
                      i >= n &&
                      store(&(s->size), int, n) *
                      store(&(s->assigns), char *, values) *
                      CharArray::seg(
                        values, 0, n,
                        mt_assigns(ms_core(Mselected))) *
                      solver_char_tail(
                        values, n, ms_cap(Mselected)) *
                      Veci::rep(&(s->model),
                               model_words_now) *
                      solver_model_copy_frame_at(
                        s, Mselected, levels, search_wl)
                    which implies exists (Mdone : msolver)
                                         (model_words : list Z),
                      ms_cap(Mdone) == ms_cap(M) &&
                      solver_search_reuse(M, Mdone) &&
                      model_copy_finish(
                        n, F, A_arr, A_inst, Mselected,
                        model_words, Mdone) &&
                      solver_rep_assigns_levels_at(
                        s, Mdone, values, levels, search_wl) *
                      has_permission(&i)
                 */
                /*@ Given Mdone model_words */
                /*@ model_copy_finish(
                      n, F, A_arr, A_inst, Mselected,
                      model_words, Mdone) &&
                      solver_rep_assigns_levels_at(
                        s, Mdone, values, levels, search_wl)
                    which implies
                      model_copy_finish(
                        n, F, A_arr, A_inst, Mselected,
                        model_words, Mdone) &&
                      store(&(s->root_level), int,
                        ms_root_level(Mdone)) *
                      Veci::rep(&(s->trail_lim),
                        mt_lim(ms_core(Mdone))) *
                      solver_search_root_frame_at(s, Mdone, levels, search_wl) *
                      has_permission(&values)
                 */
                /*@ model_copy_finish(
                      n, F, A_arr, A_inst, Mselected,
                      model_words, Mdone) &&
                      store(&(s->root_level), int,
                        ms_root_level(Mdone)) *
                      Veci::rep(&(s->trail_lim),
                        mt_lim(ms_core(Mdone))) *
                      solver_search_root_frame_at(s, Mdone, levels, search_wl)
                    which implies
                      model_copy_finish(
                        n, F, A_arr, A_inst, Mselected,
                        model_words, Mdone) &&
                      solver_cancel_pre(
                        s, ms_root_level(Mdone), Mdone, search_wl) *
                      solver_levels_slice_at(s, Mdone, levels)
                 */
                solver_canceluntil(s,s->root_level) /*@ where M = Mdone, wl = search_wl */;
                /*@ ms_cap(Mdone) == ms_cap(M) &&
                      solver_search_reuse(M, Mdone) &&
                      ms_cap(Mselected) == ms_cap(M) &&
                      solver_search_reuse(M, Mselected) &&
          model_copy_finish(
                      n, F, A_arr, A_inst, Mselected,
                      model_words, Mdone) &&
                      solver_cancel_post(
                      s, ms_root_level(Mdone), Mdone, search_wl) *
                      solver_levels_slice_at(s, Mdone, levels) *
                      Veci::rep(&(learnt_clause),
                               learnt_words)
                    which implies exists (Mmodel_root : msolver),
                      ms_cap(Mmodel_root) == ms_cap(M) &&
                      solver_search_reuse(M, Mmodel_root) &&
                      msolver_inv(n, F, A_arr, A_inst, Mmodel_root) &&
                      solver_at_root(Mmodel_root) &&
                      mt_qhead(ms_core(Mmodel_root)) ==
                        ms_qtail(Mmodel_root) &&
                      ms_capacity_root_propagation_pending(
                        Mmodel_root) == 0 &&
                      msolver_seed_shadow(Mmodel_root) &&
                      model_saved(n, F, A_arr, Mmodel_root) &&
                      solver_rep_levels_wl_at(
                        s, Mmodel_root, search_wl, levels) *
                      Veci::rep(&(learnt_clause),
                               learnt_words)
                 */
                veci_delete(&learnt_clause);

                return l_True;
            }

            /*@ solver_search_select_transition(
                  n, F, A_arr, A_inst, Mdb, next,
                  orderpos_after, order_after,
                  seed_after, stats_after, Mselected) &&
                  next != -1
                which implies solver_search_selection_state(
                  n, F, A_arr, A_inst, next, Mselected)
             */

            /*@ solver_search_selection_state(
                  n, F, A_arr, A_inst, next, Mselected) &&
                  solver_rep_levels_wl_at(s, Mselected, search_wl, levels)
                which implies exists decision_asg,
                  Zlength(mt_lim(ms_core(Mselected))) < n &&
                  enqueue_input(
                    n, lit_neg_c(next + next), ms_qtail(Mselected),
                    mt_assigns(ms_core(Mselected)),
                    mt_levels(ms_core(Mselected)),
                    ms_reason_words(Mselected),
                    mt_trail(ms_core(Mselected))) &&
                  store(&(s->qhead), int, ms_qtail(Mselected)) *
                  enqueue_state_at(
                    s, decision_asg, levels, n, ms_cap(Mselected),
                    ms_qtail(Mselected), mt_assigns(ms_core(Mselected)),
                    mt_levels(ms_core(Mselected)),
                    ms_reason_words(Mselected),
                    mt_trail(ms_core(Mselected)),
                    mt_lim(ms_core(Mselected))) *
                  solver_assume_frame_wl(s, Mselected, search_wl)
             */
            /*@ Given decision_asg */
            assume(s,lit_neg(toLit(next)) /*@ where (original) */);
            /*@ exists decision_lit,
                  ms_cap(Mselected) == ms_cap(M) &&
                  solver_search_reuse(M, Mselected) &&
                  lit_neg_c(next + next) <= decision_lit &&
                  decision_lit <= lit_neg_c(next + next) &&
                  solver_search_selection_state(
                    n, F, A_arr, A_inst, next, Mselected) &&
                  Zlength(mt_lim(ms_core(Mselected))) < n &&
                  enqueue_input(
                    n, lit_neg_c(next + next), ms_qtail(Mselected),
                    mt_assigns(ms_core(Mselected)),
                    mt_levels(ms_core(Mselected)),
                    ms_reason_words(Mselected),
                    mt_trail(ms_core(Mselected))) &&
                  assume_post_at(
                    s, decision_asg, levels, decision_lit, n,
                    ms_cap(Mselected), ms_qtail(Mselected),
                    mt_assigns(ms_core(Mselected)),
                    mt_levels(ms_core(Mselected)),
                    ms_reason_words(Mselected),
                    mt_trail(ms_core(Mselected)),
                    mt_lim(ms_core(Mselected))) *
                  solver_assume_frame_wl(s, Mselected, search_wl)
                which implies exists (Mdecision : msolver),
                  ms_cap(Mdecision) == ms_cap(M) &&
                  solver_search_reuse(M, Mdecision) &&
                  solver_search_decision_transition(
                    n, F, A_arr, A_inst,
                    Mselected, next, Mdecision) &&
                  msat_fp32_positive_finite(ms_cla_decay(Mdecision)) &&
                  solver_rep_levels_wl_at(s, Mdecision, search_wl, levels)
             */
            /*@ Assert (exists conflict_budget_value learnt_budget_value
                         conflict_count_value (random_value : fp64),
                  s == s@pre &&
                  0 <= conflict_count_value &&
                  solver_search_loop(
                  s, &(learnt_clause), levels,
                  n, F, A_arr, A_inst, search_wl, M) *
                  store(&nof_conflicts, int, conflict_budget_value) *
                  store(&nof_learnts, int, learnt_budget_value) *
                  store(&random_var_freq, double, random_value) *
                  has_permission(&var_decay) * has_permission(&clause_decay) *
                  store(&conflictC, uint64, conflict_count_value) *
                  has_permission(&confl) *
                  has_permission(&next)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
             */
        }
    }

    return l_Undef; // cannot happen
}

solver* solver_new(void)
/*@ solver_new_spec */
{
    solver* s = minisat_solver_alloc();
    /*@ solver_storage_undef(s)
        which implies
        undef_data_at(&(s->size), int) *
        undef_data_at(&(s->cap), int) *
        undef_data_at(&(s->qhead), int) *
        undef_data_at(&(s->qtail), int) *


        undef_data_at(&(s->root_level), int) *
        undef_data_at(&(s->simpdb_assigns), int) *
        undef_data_at(&(s->simpdb_props), int) *
        undef_data_at(&(s->verbosity), int) *
        undef_data_at(&(s->var_inc), double) *
        undef_data_at(&(s->var_decay), double) *
        undef_data_at(&(s->cla_inc), float) *
        undef_data_at(&(s->cla_decay), float) *
        undef_data_at(&(s->random_seed), double) *
        undef_data_at(&(s->progress_estimate), double) *
        undef_data_at(&(s->wlists), vecp *) *
        undef_data_at(&(s->activity), double *) *
        undef_data_at(&(s->assigns), lbool *) *
        undef_data_at(&(s->orderpos), int *) *
        undef_data_at(&(s->reasons), clause **) *
        undef_data_at(&(s->levels), int *) *
        undef_data_at(&(s->trail), lit *) *
        undef_data_at(&(s->binary), clause *) *
        undef_data_at(&(s->tags), lbool *) *
        Vecp::shell(&(s->clauses)) *
        Vecp::shell(&(s->learnts)) *
        Veci::shell(&(s->order)) *
        Veci::shell(&(s->trail_lim)) *
        Veci::shell(&(s->tagged)) *
        Veci::shell(&(s->stack)) *
        Veci::shell(&(s->model)) *
        undef_data_at(&(s->stats.starts), uint64) *
        undef_data_at(&(s->stats.decisions), uint64) *
        undef_data_at(&(s->stats.propagations), uint64) *
        undef_data_at(&(s->stats.inspects), uint64) *
        undef_data_at(&(s->stats.conflicts), uint64) *
        undef_data_at(&(s->stats.clauses), uint64) *
        undef_data_at(&(s->stats.clauses_literals), uint64) *
        undef_data_at(&(s->stats.learnts), uint64) *
        undef_data_at(&(s->stats.learnts_literals), uint64) *
        undef_data_at(&(s->stats.max_literals), uint64) *
        undef_data_at(&(s->stats.tot_literals), uint64)
     */

    // initialize vectors
    vecp_new(&s->clauses);
    vecp_new(&s->learnts);
    veci_new(&s->order);
    veci_new(&s->trail_lim);
    veci_new(&s->tagged);
    veci_new(&s->stack);
    veci_new(&s->model);

    // initialize arrays
    s->wlists    = 0;
    s->activity  = 0;
    s->assigns   = 0;
    s->orderpos  = 0;
    s->reasons   = 0;
    s->levels    = 0;
    s->tags      = 0;
    s->trail     = 0;

    // initialize other vars
    s->size                   = 0;
    s->cap                    = 0;
    s->qhead                  = 0;
    s->qtail                  = 0;


    s->cla_inc                = 1;
    s->cla_decay              = 1;
    s->var_inc                = 1;
    s->var_decay              = 1;
    s->root_level             = 0;
    s->simpdb_assigns         = 0;
    s->simpdb_props           = 0;
    s->random_seed            = 91648253;
    s->progress_estimate      = 0;
    s->binary                 = minisat_clause_alloc(2, 0);
    /*@ MiniSatClause::undef(s->binary, solver_selected_is_learnt(0), 2)
        which implies
          0 < s->binary && s->binary % 2 == 0 &&
          undef_data_at(&(s->binary->size_learnt), int) *
          IntArray::undef_seg(&(s->binary->lits), 0, 2)
     */
    s->binary->size_learnt    = (2 << 1);
    s->verbosity              = 0;

    s->stats.starts           = 0;
    s->stats.decisions        = 0;
    s->stats.propagations     = 0;
    s->stats.inspects         = 0;
    s->stats.conflicts        = 0;
    s->stats.clauses          = 0;
    s->stats.clauses_literals = 0;
    s->stats.learnts          = 0;
    s->stats.learnts_literals = 0;
    s->stats.max_literals     = 0;
    s->stats.tot_literals     = 0;

    /*@ exists (initial_binary_raw : Z),
          s != 0 && 0 < initial_binary_raw && initial_binary_raw % 2 == 0 &&
          store(&(s->size), int, 0) *
          store(&(s->cap), int, 0) *
          store(&(s->qhead), int, 0) *
          store(&(s->qtail), int, 0) *


          store(&(s->root_level), int, 0) *
          store(&(s->simpdb_assigns), int, 0) *
          store(&(s->simpdb_props), int, 0) *
          store(&(s->verbosity), int, 0) *
          store(&(s->var_inc), double, Z_to_fp64(1)) *
          store(&(s->var_decay), double, Z_to_fp64(1)) *
          store(&(s->cla_inc), float, Z_to_fp32(1)) *
          store(&(s->cla_decay), float, Z_to_fp32(1)) *
          store(&(s->random_seed), double, Z_to_fp64(91648253)) *
          store(&(s->progress_estimate), double, Z_to_fp64(0)) *
          store(&(s->wlists), vecp *, 0) *
          store(&(s->activity), double *, 0) *
          store(&(s->assigns), lbool *, 0) *
          store(&(s->orderpos), int *, 0) *
          store(&(s->reasons), clause **, 0) *
          store(&(s->levels), int *, 0) *
          store(&(s->trail), lit *, 0) *
          store(&(s->tags), lbool *, 0) *
          store(&(s->binary), clause *, initial_binary_raw) *
          Vecp::rep(&(s->clauses), nil) *
          Vecp::rep(&(s->learnts), nil) *
          Veci::rep(&(s->order), nil) *
          Veci::rep(&(s->trail_lim), nil) *
          Veci::rep(&(s->tagged), nil) *
          Veci::rep(&(s->stack), nil) *
          Veci::rep(&(s->model), nil) *
          store(&(s->stats.starts), uint64, 0) *
          store(&(s->stats.decisions), uint64, 0) *
          store(&(s->stats.propagations), uint64, 0) *
          store(&(s->stats.inspects), uint64, 0) *
          store(&(s->stats.conflicts), uint64, 0) *
          store(&(s->stats.clauses), uint64, 0) *
          store(&(s->stats.clauses_literals), uint64, 0) *
          store(&(s->stats.learnts), uint64, 0) *
          store(&(s->stats.learnts_literals), uint64, 0) *
          store(&(s->stats.max_literals), uint64, 0) *
          store(&(s->stats.tot_literals), uint64, 0) *
          store(&(((clause *)initial_binary_raw)->size_learnt), int, 2 << 1) *
          IntArray::undef_seg(&(((clause *)initial_binary_raw)->lits), 0, 2)
        which implies exists (initial_binary : Z),
          solver_initial_layout(s, initial_binary)
     */
    /*@ Given initial_binary */
    /*@ solver_initial_layout(s, initial_binary)
        which implies s != 0 && exists (M : msolver),
          ms_size(M) == 0 && ms_cap(M) == 0 &&
          solver_normal_root(0, cnf_nil, M) &&
          msolver_seed_shadow(M) && solver_query_watch_ready(M) &&
          solver_rep_growable(s, M)
     */
    return s;
}

void solver_delete(solver* s)
{
    int i;
    for (i = 0; i < vecp_size(&s->clauses); i++)
        free(vecp_begin(&s->clauses)[i]);

    for (i = 0; i < vecp_size(&s->learnts); i++)
        free(vecp_begin(&s->learnts)[i]);

    // delete vectors
    vecp_delete(&s->clauses);
    vecp_delete(&s->learnts);
    veci_delete(&s->order);
    veci_delete(&s->trail_lim);
    veci_delete(&s->tagged);
    veci_delete(&s->stack);
    veci_delete(&s->model);
    free(s->binary);

    // delete arrays
    if (s->wlists != 0){
        int i;
        for (i = 0; i < s->size*2; i++)
            vecp_delete(&s->wlists[i]);

        // if one is different from null, all are
        free(s->wlists);
        free(s->activity );
        free(s->assigns  );
        free(s->orderpos );
        free(s->reasons  );
        free(s->levels   );
        free(s->trail    );
        free(s->tags     );
    }

    free(s);
}

bool solver_addclause(solver* s, lit* begin, lit* endvar)
/*@ addclause_spec */
{
    lit *i,*j;
    int maxvar;

    lbool* values;
    lit last;

    if (begin == endvar) return false;

    /*@ begin != endvar &&
          endvar == begin + Zlength(ac_input) * sizeof(int) &&
          0 <= Zlength(ac_input) &&
          Forall(lit_wf_c(ac_n), ac_input) &&
          0 <= ac_n && 2 * ac_n <= INT_MAX
        which implies
          endvar == begin + Zlength(ac_input) * sizeof(int) &&
          1 <= Zlength(ac_input) &&
          Forall(lit_wf_c(ac_n), ac_input) &&
          0 <= ac_n &&
          lit_wf_c(ac_n, Znth(0, ac_input, 0)) &&
          0 <= Znth(0, ac_input, 0) && Znth(0, ac_input, 0) <= INT_MAX
     */

    // insertion sort
    maxvar = lit_var(*begin) /*@ where (original) */;
    /*@ Inv Assert (exists (sorted rest : list Z) k,
          Zlength(mt_lim(ms_core(ac_M))) == 0 &&
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          1 <= k && k <= Zlength(ac_input) &&
          1 <= Zlength(ac_input) &&
          Zlength(sorted) == k &&
          Zlength(app(sorted, rest)) == Zlength(ac_input) &&
          endvar == begin + Zlength(ac_input) * sizeof(int) &&
          i == begin + k * sizeof(int) &&
          addclause_sort_outer_inv(ac_n, maxvar, ac_input, sorted, rest) &&
          0 <= ac_n && ac_n <= Z::max(ms_cap(ac_M), INT_MAX / 4) &&
          2 * Zlength(ac_input) + 1 <= INT_MAX &&
          2 * ms_cap(ac_M) <= INT_MAX &&
          solver_shape(ac_M) &&
          solver_support_inv(ms_size(ac_M), ac_F, ac_A_arr, ac_A_inst, 0, ac_M) &&
          ms_capacity_root_propagation_pending(ac_M) == 0 &&
          msolver_seed_shadow(ac_M) &&
          solver_rep_growable(s, ac_M) *
          IntArray::seg(begin, 0, Zlength(ac_input), app(sorted, rest)) *
          has_permission(&j) * has_permission(&values) * has_permission(&last)) *
          store(&l_Undef, char, 0) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    for (i = begin + 1; i < endvar; i++){
        /*@ Given sorted rest k */
        /*@ 1 <= k && k <= Zlength(ac_input) &&
              Zlength(app(sorted, rest)) == Zlength(ac_input) &&
              i == begin + k * sizeof(int) &&
              endvar == begin + Zlength(ac_input) * sizeof(int) && i < endvar &&
              addclause_sort_outer_inv(ac_n, maxvar, ac_input, sorted, rest) &&
              0 <= ac_n && 2 * ac_n <= INT_MAX
            which implies
              1 <= k && k < Zlength(ac_input) &&
              Zlength(app(sorted, rest)) == Zlength(ac_input) &&
              i == begin + k * sizeof(int) &&
              endvar == begin + Zlength(ac_input) * sizeof(int) &&
              addclause_sort_outer_inv(ac_n, maxvar, ac_input, sorted, rest) &&
              lit_wf_c(ac_n, Znth(k - 0, app(sorted, rest), 0)) &&
              0 <= Znth(k - 0, app(sorted, rest), 0) &&
              Znth(k - 0, app(sorted, rest), 0) <= INT_MAX
         */
        lit l = *i;
        maxvar = lit_var(l) /*@ where (original) */ > maxvar ? lit_var(l) /*@ where (original) */ : maxvar;
        /*@ Inv Assert (exists (pre suf rest2 arr : list Z) p junk,
              Zlength(mt_lim(ms_core(ac_M))) == 0 &&
              s == s@pre && begin == begin@pre && endvar == endvar@pre &&
              0 <= p && p <= k && p < Zlength(ac_input) && Zlength(pre) == p &&
              Zlength(app(pre, suf)) == k &&
              Zlength(app(pre, cons(junk, app(suf, rest2))))
                == Zlength(ac_input) &&
              Zlength(arr) == Zlength(ac_input) &&
              endvar == begin + Zlength(ac_input) * sizeof(int) &&
              i == begin + k * sizeof(int) &&
              j == begin + p * sizeof(int) &&
              addclause_sort_inner_inv(l, app(pre, suf), pre, suf) &&
              addclause_sort_outer_inv(ac_n, maxvar, ac_input,
                                       app(pre, suf), cons(l, rest2)) &&
              lit_var_c(l) <= maxvar && 0 <= maxvar && maxvar < ac_n &&
              0 <= ac_n && ac_n <= Z::max(ms_cap(ac_M), INT_MAX / 4) &&
              2 * Zlength(ac_input) + 1 <= INT_MAX &&
              2 * ms_cap(ac_M) <= INT_MAX &&
              solver_shape(ac_M) &&
          solver_support_inv(ms_size(ac_M), ac_F, ac_A_arr, ac_A_inst, 0, ac_M) &&
              ms_capacity_root_propagation_pending(ac_M) == 0 &&
              msolver_seed_shadow(ac_M) &&
              arr == app(pre, cons(junk, app(suf, rest2))) &&
              solver_rep_growable(s, ac_M) *
              IntArray::seg(begin, 0, Zlength(ac_input), arr) *
              has_permission(&values) *
              has_permission(&last)) *
          store(&l_Undef, char, 0) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
         */
        for (j = i; j > begin && *(j-1) > l; j--)
            /*@ Given pre suf rest2 arr p junk */
            /*@ 0 <= p && p <= k && Zlength(pre) == p &&
                  arr == app(pre, cons(junk, app(suf, rest2))) &&
                  Zlength(arr) == Zlength(ac_input) &&
                  j == begin + p * sizeof(int) && begin < j
                which implies
                  1 <= p && p <= k && Zlength(pre) == p &&
                  Zlength(app(pre, cons(junk, app(suf, rest2))))
                    == Zlength(ac_input) &&
                  j == begin + p * sizeof(int) &&
                  0 <= p - 1 && p - 1 < Zlength(ac_input) &&
                  p < Zlength(ac_input) &&
                  Zlength(arr) == Zlength(ac_input)
             */

            /*@ 0 <= p && p < Zlength(ac_input) &&
                  Zlength(arr) == Zlength(ac_input) &&
                  IntArray::seg(begin, 0, Zlength(ac_input), arr)
                which implies
                  0 <= p && p < Zlength(ac_input) &&
                  Zlength(arr) == Zlength(ac_input) &&
                  store(pointer_offset(begin, p, int),
                        int, Znth(p, arr, 0)) *
                  IntArray::missing_i(begin, p, 0, Zlength(ac_input), arr)
             */
            *j = *(j-1);
        /*@ Given pre suf rest2 arr p */

        /*@ 0 <= p && p < Zlength(ac_input) &&
              Zlength(arr) == Zlength(ac_input) &&
              j == begin + p * sizeof(int) &&
              IntArray::seg(begin, 0, Zlength(ac_input), arr)
            which implies
              0 <= p && p < Zlength(ac_input) &&
              Zlength(arr) == Zlength(ac_input) &&
              j == begin + p * sizeof(int) &&
              store(pointer_offset(begin, p, int),
                    int, Znth(p, arr, 0)) *
              IntArray::missing_i(begin, p, 0, Zlength(ac_input), arr)
         */
        *j = l;
    }
    solver_setnvars(s, maxvar+1)
      /*@ where (setnvars_spec) sn_F = ac_F, sn_A_arr = ac_A_arr,
                sn_A_inst = ac_A_inst, sn_M = ac_M, sn_root = 0 */;

    /*@ Assert (exists (Mnew : msolver) (sortedf : list Z) asg lvlp wlg,
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          1 <= Zlength(ac_input) &&
          0 <= maxvar && maxvar < ac_n &&
          maxvar + 1 <= ms_size(Mnew) &&
          ms_size(ac_M) <= ms_size(Mnew) && ms_cap(ac_M) <= ms_cap(Mnew) &&
          2 * ms_cap(Mnew) <= INT_MAX &&
          solver_shape(Mnew) &&
          solver_support_inv(ms_size(Mnew), ac_F, ac_A_arr, ac_A_inst, 0, Mnew) &&
          (minisat_watch_completed(ac_M) => minisat_watch_completed(Mnew)) &&
          ms_capacity_root_propagation_pending(Mnew) == 0 &&
          Zlength(mt_lim(ms_core(Mnew))) == 0 &&
          msolver_seed_shadow(Mnew) &&
          2 * Zlength(ac_input) + 1 <= INT_MAX &&
          Zlength(mt_assigns(ms_core(Mnew))) == ms_size(Mnew) &&
          cnf_wf(ms_size(ac_M), ac_F) &&
          Forall(lit_wf_c(ac_n), ac_input) &&
          Permutation(sortedf, ac_input) && sorted_le(sortedf) &&
          all_from(ac_input, sortedf) &&
          Zlength(sortedf) == Zlength(ac_input) &&
          Forall(lit_wf_c(ms_size(Mnew)), sortedf) &&
          endvar == begin + Zlength(ac_input) * sizeof(int) &&
          store(&(s->assigns), lbool *, asg) *
          CharArray::seg(asg, 0, ms_size(Mnew), mt_assigns(ms_core(Mnew))) *
          solver_char_tail(asg, ms_size(Mnew), ms_cap(Mnew)) *
          solver_assigns_focus_frame_wl_at(s, Mnew, wlg, lvlp) *
          solver_wlists_tail(wlg, 2 * ms_size(Mnew), 2 * ms_cap(Mnew)) *
          IntArray::seg(begin, 0, Zlength(ac_input), sortedf) *
          has_permission(&i) * has_permission(&j) *
          has_permission(&values) * has_permission(&last)) *
          store(&l_Undef, char, 0) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    /*@ Given Mnew sortedf asg lvlp wlg */

    values = s->assigns;

    // delete duplicates
    last = lit_Undef;
    j = begin;
    /*@ Inv Assert (exists (kept tail : list Z) k q,
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          1 <= Zlength(ac_input) &&
          0 <= k && k <= Zlength(ac_input) &&
          0 <= q && q <= k && Zlength(kept) == q &&
          Zlength(app(kept, tail)) == Zlength(ac_input) &&
          Permutation(sortedf, ac_input) && sorted_le(sortedf) &&
          addclause_prefix_equiv(
            ac_F, sublist(0, k, sortedf), kept) &&
          all_from(ac_input, app(kept, tail)) &&
          tail == sublist(q, Zlength(ac_input), sortedf) &&
          all_ge(last, sublist(k, Zlength(ac_input), sortedf)) &&
          endvar == begin + Zlength(ac_input) * sizeof(int) &&
          i == begin + k * sizeof(int) &&
          j == begin + q * sizeof(int) &&
          values == asg &&
          addclause_dedup_inv(ms_size(Mnew), mt_assigns(ms_core(Mnew)),
                              ac_input, kept, last) &&
          Zlength(mt_assigns(ms_core(Mnew))) == ms_size(Mnew) &&
          2 * ms_cap(Mnew) <= INT_MAX &&
          solver_shape(Mnew) &&
          solver_support_inv(ms_size(Mnew), ac_F, ac_A_arr, ac_A_inst, 0, Mnew) &&
          (minisat_watch_completed(ac_M) => minisat_watch_completed(Mnew)) &&
          ms_size(ac_M) <= ms_size(Mnew) && ms_cap(ac_M) <= ms_cap(Mnew) &&
          cnf_wf(ms_size(ac_M), ac_F) &&
          Forall(lit_wf_c(ac_n), ac_input) &&
          Forall(lit_wf_c(ms_size(Mnew)), app(kept, tail)) &&
          ms_capacity_root_propagation_pending(Mnew) == 0 &&
          Zlength(mt_lim(ms_core(Mnew))) == 0 &&
          msolver_seed_shadow(Mnew) &&
          2 * Zlength(ac_input) + 1 <= INT_MAX &&
          store(&(s->assigns), lbool *, asg) *
          CharArray::seg(asg, 0, ms_size(Mnew), mt_assigns(ms_core(Mnew))) *
          solver_char_tail(asg, ms_size(Mnew), ms_cap(Mnew)) *
          solver_assigns_focus_frame_wl_at(s, Mnew, wlg, lvlp) *
          solver_wlists_tail(wlg, 2 * ms_size(Mnew), 2 * ms_cap(Mnew)) *
          IntArray::seg(begin, 0, Zlength(ac_input), app(kept, tail)) *
          has_permission(&maxvar)) *
          store(&l_Undef, char, 0) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    for (i = begin; i < endvar; i++){
        /*@ Given kept tail k q */
        /*@ 0 <= k && k <= Zlength(ac_input) &&
              Zlength(app(kept, tail)) == Zlength(ac_input) &&
              i == begin + k * sizeof(int) &&
              endvar == begin + Zlength(ac_input) * sizeof(int) && i < endvar &&
              Forall(lit_wf_c(ms_size(Mnew)), app(kept, tail)) &&
              addclause_dedup_inv(ms_size(Mnew), mt_assigns(ms_core(Mnew)),
                                  ac_input, kept, last) &&
              2 * ms_size(Mnew) <= INT_MAX
            which implies
              Forall(lit_wf_c(ms_size(Mnew)), app(kept, tail)) &&
              0 <= k && k < Zlength(ac_input) &&
              Zlength(app(kept, tail)) == Zlength(ac_input) &&
              i == begin + k * sizeof(int) &&
              endvar == begin + Zlength(ac_input) * sizeof(int) &&
              addclause_dedup_inv(ms_size(Mnew), mt_assigns(ms_core(Mnew)),
                                  ac_input, kept, last) &&
              lit_wf_c(ms_size(Mnew), Znth(k - 0, app(kept, tail), 0)) &&
              0 <= Znth(k - 0, app(kept, tail), 0) &&
              Znth(k - 0, app(kept, tail), 0) <= INT_MAX &&
              0 <= lit_var_c(Znth(k - 0, app(kept, tail), 0)) &&
              lit_var_c(Znth(k - 0, app(kept, tail), 0)) < ms_size(Mnew)
         */
        lbool sig = !lit_sign(*i); sig += sig - 1;

        /*@               0 <= lit_var_c(app(kept, tail)[k - 0]) && lit_var_c(app(kept, tail)[k - 0]) < ms_size(Mnew) &&
              Zlength(mt_assigns(ms_core(Mnew))) == ms_size(Mnew) &&
              CharArray::seg(asg, 0, ms_size(Mnew), mt_assigns(ms_core(Mnew)))
            which implies
              0 <= lit_var_c(app(kept, tail)[k - 0]) && lit_var_c(app(kept, tail)[k - 0]) < ms_size(Mnew) &&
              Zlength(mt_assigns(ms_core(Mnew))) == ms_size(Mnew) &&
              store(pointer_offset(asg, lit_var_c(app(kept, tail)[k - 0]), char),
                    char, Znth(lit_var_c(app(kept, tail)[k - 0]), mt_assigns(ms_core(Mnew)), 0)) *
              CharArray::missing_i(asg, lit_var_c(app(kept, tail)[k - 0]), 0, ms_size(Mnew),
                                   mt_assigns(ms_core(Mnew)))
         */
        if (*i == lit_neg(last) /*@ where (sentinel) */ || sig == values[lit_var(*i) /*@ where(original) */])
            return true;   // tautology
        else if (*i != last && values[lit_var(*i) /*@ where(original) */] == l_Undef) {

                /*@ 0 <= q && q < Zlength(ac_input) &&
                      Zlength(app(kept, tail)) == Zlength(ac_input) &&
                      j == begin + q * sizeof(int) &&
                      IntArray::seg(begin, 0, Zlength(ac_input),
                                    app(kept, tail))
                    which implies
                      0 <= q && q < Zlength(ac_input) &&
                      Zlength(app(kept, tail)) == Zlength(ac_input) &&
                      j == begin + q * sizeof(int) &&
                      store(pointer_offset(begin, q, int),
                            int, Znth(q, app(kept, tail), 0)) *
                      IntArray::missing_i(begin, q, 0, Zlength(ac_input),
                                          app(kept, tail))
                 */
                last = *i;
                *j = last;
                j++;
        }
    }

    /*@ Assert (exists (kept tail : list Z) q,
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          1 <= Zlength(ac_input) &&
          0 <= q && q <= Zlength(ac_input) && Zlength(kept) == q &&
          Zlength(app(kept, tail)) == Zlength(ac_input) &&
          all_from(ac_input, app(kept, tail)) &&
          addclause_prefix_equiv(ac_F, ac_input, kept) &&
          j == begin + q * sizeof(int) &&
          endvar == begin + Zlength(ac_input) * sizeof(int) &&
          values == asg &&
          addclause_dedup_inv(ms_size(Mnew), mt_assigns(ms_core(Mnew)),
                              ac_input, kept, last) &&
          Zlength(mt_assigns(ms_core(Mnew))) == ms_size(Mnew) &&
          2 * ms_cap(Mnew) <= INT_MAX &&
          ms_size(ac_M) <= ms_size(Mnew) && ms_cap(ac_M) <= ms_cap(Mnew) &&
          cnf_wf(ms_size(ac_M), ac_F) &&
          Forall(lit_wf_c(ac_n), ac_input) &&
          solver_shape(Mnew) &&
          solver_support_inv(ms_size(Mnew), ac_F, ac_A_arr, ac_A_inst, 0, Mnew) &&
          (minisat_watch_completed(ac_M) => minisat_watch_completed(Mnew)) &&
          ms_capacity_root_propagation_pending(Mnew) == 0 &&
          Zlength(mt_lim(ms_core(Mnew))) == 0 &&
          msolver_seed_shadow(Mnew) &&
          2 * Zlength(ac_input) + 1 <= INT_MAX &&
          store(&(s->assigns), lbool *, asg) *
          CharArray::seg(asg, 0, ms_size(Mnew), mt_assigns(ms_core(Mnew))) *
          solver_char_tail(asg, ms_size(Mnew), ms_cap(Mnew)) *
          solver_assigns_focus_frame_wl_at(s, Mnew, wlg, lvlp) *
          solver_wlists_tail(wlg, 2 * ms_size(Mnew), 2 * ms_cap(Mnew)) *
          IntArray::seg(begin, 0, Zlength(ac_input), app(kept, tail)) *
          has_permission(&i) * has_permission(&maxvar)) *
          store(&l_Undef, char, 0) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    /*@ Given kept tail q */
    if (j == begin)          // empty clause
        return false;
    else if (j - begin == 1) // unit clause
        /*@ store(&(s->assigns), lbool *, asg) *
              CharArray::seg(asg, 0, ms_size(Mnew), mt_assigns(ms_core(Mnew))) *
              solver_char_tail(asg, ms_size(Mnew), ms_cap(Mnew)) *
              solver_assigns_focus_frame_wl_at(s, Mnew, wlg, lvlp) &&
              addclause_dedup_inv(ms_size(Mnew), mt_assigns(ms_core(Mnew)),
                                  ac_input, kept, last) &&
              Zlength(kept) == q && q == 1 &&
              Zlength(app(kept, tail)) == Zlength(ac_input) &&
              Zlength(mt_assigns(ms_core(Mnew))) == ms_size(Mnew) &&
              2 * ms_cap(Mnew) <= INT_MAX &&
              solver_shape(Mnew) &&
          solver_support_inv(ms_size(Mnew), ac_F, ac_A_arr, ac_A_inst, 0, Mnew) &&
          (minisat_watch_completed(ac_M) => minisat_watch_completed(Mnew))
            which implies
              (-2) <= last &&
              enqueue_input(
                ms_size(Mnew), Znth(0 - 0, app(kept, tail), 0), ms_qtail(Mnew),
                mt_assigns(ms_core(Mnew)), mt_levels(ms_core(Mnew)),
                ms_reason_words(Mnew), mt_trail(ms_core(Mnew))) &&
              enqueue_state_at(
                s, asg, lvlp, ms_size(Mnew), ms_cap(Mnew), ms_qtail(Mnew),
                mt_assigns(ms_core(Mnew)), mt_levels(ms_core(Mnew)),
                ms_reason_words(Mnew), mt_trail(ms_core(Mnew)),
                mt_lim(ms_core(Mnew))) *
              solver_enqueue_frame_wl(s, Mnew, wlg)
         */
        return enqueue(s,*begin,(clause*)0)
               /*@ where asg = asg, lvl = lvlp, n = ms_size(Mnew),
                     cap = ms_cap(Mnew), qtail = ms_qtail(Mnew),
                     l0 = Znth(0 - 0, app(kept, tail), 0),
                     assigns = mt_assigns(ms_core(Mnew)),
                     levels0 = mt_levels(ms_core(Mnew)),
                     reasons0 = ms_reason_words(Mnew),
                     trail = mt_trail(ms_core(Mnew)),
                     lim = mt_lim(ms_core(Mnew)) */;

    /*@ store(&(s->assigns), lbool *, asg) *
          CharArray::seg(asg, 0, ms_size(Mnew), mt_assigns(ms_core(Mnew))) *
          solver_char_tail(asg, ms_size(Mnew), ms_cap(Mnew)) *
          solver_assigns_focus_frame_wl_at(s, Mnew, wlg, lvlp) *
          IntArray::seg(begin, 0, Zlength(ac_input), app(kept, tail)) &&
          addclause_dedup_inv(ms_size(Mnew), mt_assigns(ms_core(Mnew)),
                              ac_input, kept, last) &&
          Zlength(kept) == q && 2 <= q &&
          Zlength(app(kept, tail)) == Zlength(ac_input) &&
          2 * Zlength(ac_input) + 1 <= INT_MAX &&
          ms_capacity_root_propagation_pending(Mnew) == 0 &&
          Zlength(mt_lim(ms_core(Mnew))) == 0 &&
          msolver_seed_shadow(Mnew) &&
          solver_shape(Mnew) &&
          solver_support_inv(ms_size(Mnew), ac_F, ac_A_arr, ac_A_inst, 0, Mnew) &&
          (minisat_watch_completed(ac_M) => minisat_watch_completed(Mnew))
        which implies
          (-2) <= last &&
          2 <= Zlength(kept) &&
          2 * Zlength(kept) + 1 <= INT_MAX &&
          Forall(lit_wf_c(ms_size(Mnew)), kept) &&
          NoDup(map(lit_var_c, kept)) &&
          clause_install_pending_cert(ms_size(Mnew), ac_F, msolver_set_root(Mnew, 0), kept, solver_selected_is_learnt(0)) &&
          solver_shape(Mnew) &&
          solver_support_inv(ms_size(Mnew), ac_F, ac_A_arr, ac_A_inst, 0, Mnew) &&
          (minisat_watch_completed(ac_M) => minisat_watch_completed(Mnew)) &&
          ms_capacity_root_propagation_pending(Mnew) == 0 &&
          Zlength(mt_lim(ms_core(Mnew))) == 0 &&
          msolver_seed_shadow(Mnew) &&
          &(s->clauses) == solver_selected_vec(s, 0) &&
          solver_rep_levels_wl_at(s, Mnew, wlg, lvlp) *
          IntArray::seg(begin, 0, Zlength(kept), kept) *
          IntArray::seg(begin, Zlength(kept), Zlength(ac_input), tail)
     */

    // create new clause
    vecp_push(&s->clauses, clause_new(s, begin, j, 0)
        /*@ where (clause_new_spec) lvl = lvlp, cn_n = ms_size(Mnew), cn_F = ac_F,
              cn_A_arr = ac_A_arr, cn_A_inst = ac_A_inst, cn_M = Mnew,
              cn_words = kept, cn_sel = 0, cn_wl = wlg, cn_root = 0 */) /*@ where l = db_words(ms_prob(Mnew)) */;

    /*@ Assert (exists (Mclause : msolver) c_new,
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          1 <= Zlength(ac_input) &&
          j == begin + q * sizeof(int) &&
          clause_new_success_transition_root(ms_size(Mnew), ac_F, ac_A_arr, ac_A_inst, Mnew, kept, c_new, 0, 0, Mclause) &&
          solver_shape(Mclause) &&
          (minisat_watch_completed(ac_M) => minisat_watch_completed(Mclause)) &&
          Zlength(mt_lim(ms_core(Mclause))) == 0 &&
          addclause_prefix_equiv(ac_F, ac_input, kept) &&
          ms_size(ac_M) <= ms_size(Mnew) && ms_cap(ac_M) <= ms_cap(Mnew) &&
          2 * ms_cap(Mnew) <= INT_MAX &&
          Zlength(kept) == q && 2 <= q &&
          Zlength(app(kept, tail)) == Zlength(ac_input) &&
          solver_rep_levels_wl_at(s, Mclause, wlg, lvlp) *
          solver_wlists_tail(wlg, 2 * ms_size(Mnew), 2 * ms_cap(Mnew)) *
          IntArray::seg(begin, 0, Zlength(kept), kept) *
          IntArray::seg(begin, Zlength(kept), Zlength(ac_input), tail) *
          has_permission(&i) * has_permission(&maxvar) *
          has_permission(&values) * has_permission(&last)) *
          store(&l_Undef, char, 0) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    /*@ Given Mclause */
    /*@ solver_rep_levels_wl_at(s, Mclause, wlg, lvlp)
        which implies
          addclause_stats_open_frame_wl_at(s, Mclause, wlg, lvlp) *
          store(&(s->stats.starts), stats_starts(ms_stats(Mclause))) *
          store(&(s->stats.decisions), stats_decisions(ms_stats(Mclause))) *
          store(&(s->stats.propagations), stats_propagations(ms_stats(Mclause))) *
          store(&(s->stats.inspects), stats_inspects(ms_stats(Mclause))) *
          store(&(s->stats.conflicts), stats_conflicts(ms_stats(Mclause))) *
          store(&(s->stats.clauses), stats_clauses(ms_stats(Mclause))) *
          store(&(s->stats.clauses_literals), stats_clauses_literals(ms_stats(Mclause))) *
          store(&(s->stats.learnts), stats_learnts(ms_stats(Mclause))) *
          store(&(s->stats.learnts_literals), stats_learnts_literals(ms_stats(Mclause))) *
          store(&(s->stats.max_literals), stats_max_literals(ms_stats(Mclause))) *
          store(&(s->stats.tot_literals), stats_tot_literals(ms_stats(Mclause)))
     */
    s->stats.clauses++;
    s->stats.clauses_literals += j - begin;

    return true;
}

bool solver_simplify(solver* s)
/*@ solver_simplify_spec */
{

    clause** reasons;
    int type;

    /*@ solver_simplify_pre_at(
          s, smp_n, smp_F, smp_A_arr, M, levels_ptr, smp_wl)
        which implies exists assigns_entry,
          msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, M) &&
          Zlength(mt_lim(ms_core(M))) == 0 &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          Veci::rep(&(s->trail_lim), mt_lim(ms_core(M))) *
          solver_simplify_lim_frame_at(
            s, M, assigns_entry, levels_ptr, smp_wl)
     */
    /*@ Given assigns_entry */

    assert(solver_dlevel(s) == 0);

    /*@ Veci::rep(&(s->trail_lim), mt_lim(ms_core(M))) *
        solver_simplify_lim_frame_at(s, M, assigns_entry, levels_ptr, smp_wl)
        which implies solver_rep_levels_wl_at(s, M, smp_wl, levels_ptr)
     */
    /*@ solver_rep_levels_wl_at(s, M, smp_wl, levels_ptr)
        which implies exists assigns_prop,
          solver_rep_assigns_levels_at(
            s, M, assigns_prop, levels_ptr, smp_wl)
     */
    /*@ Given assigns_prop */
    /*@ msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, M) &&
          ms_capacity_root_propagation_pending(M) == 0 &&
          msolver_seed_shadow(M) &&
          solver_rep_assigns_levels_at(
            s, M, assigns_prop, levels_ptr, smp_wl)
        which implies
          solver_propagation_inv(smp_n, smp_F, smp_A_arr,
            PropagationAssuming(smp_A_arr), M) &&
          msolver_seed_shadow(M) &&
          solver_rep_assigns_levels_at(
            s, M, assigns_prop, levels_ptr, smp_wl)
     */
    if (solver_propagate(s)
          /*@ where n = smp_n, F = smp_F, A_arr = smp_A_arr,
                    K = PropagationAssuming(smp_A_arr), M0 = M,
                    assigns_entry = assigns_prop, levels_entry = levels_ptr,
                    wlists_entry = smp_wl */ != 0)
        return false;

    /*@ Given propagation_result */
    /*@ msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, M) &&
          Zlength(mt_lim(ms_core(M))) == 0 &&
          solver_propagation_inv(smp_n, smp_F, smp_A_arr,
            PropagationAssuming(smp_A_arr), propagation_result) &&
          propagation_caller_frame(M, propagation_result) &&
          minisat_propagation_reuse_live(M, propagation_result) &&
          msolver_seed_shadow(propagation_result) &&
          mt_qhead(ms_core(propagation_result)) == ms_qtail(propagation_result) &&
          solver_rep_assigns_levels_at(
            s, propagation_result, assigns_prop, levels_ptr, smp_wl)
        which implies exists Mprop,
          ms_cap(Mprop) == ms_cap(M) &&
          ms_root_level(Mprop) == ms_root_level(M) &&
          solver_simplify_reuse(M, Mprop) &&
          msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, Mprop) &&
          (ms_model(M) == nil => ms_model(Mprop) == nil) &&
          (msat_fp32_positive_finite(ms_cla_decay(M)) =>
           msat_fp32_positive_finite(ms_cla_decay(Mprop))) &&
          Zlength(mt_lim(ms_core(Mprop))) == 0 &&
          mt_qhead(ms_core(Mprop)) == ms_qtail(Mprop) &&
          ms_capacity_root_propagation_pending(Mprop) == 0 &&
          msolver_seed_shadow(Mprop) &&
          solver_rep_assigns_levels_at(
            s, Mprop, assigns_prop, levels_ptr, smp_wl)
     */
    /*@ Given Mprop */

    /*@ solver_rep_assigns_levels_at(
          s, Mprop, assigns_prop, levels_ptr, smp_wl)
        which implies exists reasons_ptr,
          store(&(s->qhead), mt_qhead(ms_core(Mprop))) *
          store(&(s->simpdb_assigns), ms_simpdb_assigns(Mprop)) *
          store(&(s->simpdb_props), ms_simpdb_props(Mprop)) *
          store(&(s->reasons), reasons_ptr) *
          solver_simplify_control_frame_at(
            s, Mprop, assigns_prop, levels_ptr, reasons_ptr, smp_wl)
     */
    /*@ Given reasons_ptr */

    if (s->qhead == s->simpdb_assigns || s->simpdb_props > 0)
        /*@ store(&(s->qhead), mt_qhead(ms_core(Mprop))) *
            store(&(s->simpdb_assigns), ms_simpdb_assigns(Mprop)) *
            store(&(s->simpdb_props), ms_simpdb_props(Mprop)) *
            store(&(s->reasons), reasons_ptr) *
            solver_simplify_control_frame_at(
              s, Mprop, assigns_prop, levels_ptr, reasons_ptr, smp_wl)
            which implies solver_rep_assigns_levels_at(
              s, Mprop, assigns_prop, levels_ptr, smp_wl)
         */
        return true;

    reasons = s->reasons;
    /*@ store(&(s->qhead), mt_qhead(ms_core(Mprop))) *
        store(&(s->simpdb_assigns), ms_simpdb_assigns(Mprop)) *
        store(&(s->simpdb_props), ms_simpdb_props(Mprop)) *
        store(&(s->reasons), reasons) *
        solver_simplify_control_frame_at(
          s, Mprop, assigns_prop, levels_ptr, reasons, smp_wl)
        which implies solver_rep_reasons_levels_wl_at(
          s, Mprop, reasons, levels_ptr, smp_wl)
     */
    /*@ Inv Assert (s == s@pre &&
          solver_simplify_outer_loop(
          s, smp_n, smp_F, smp_A_arr, reasons, levels_ptr, type, M, smp_wl)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&true, int, 1) * store(&false, int, 0)
     */
    for (type = 0; type < 2; type++){
        /*@ type < 2 &&
              solver_simplify_outer_loop(
              s, smp_n, smp_F, smp_A_arr,
              reasons, levels_ptr, type, M, smp_wl)
            which implies exists Mtype (words_type : list Z) asg_type,
          ms_cap(Mtype) == ms_cap(M) &&
          ms_root_level(Mtype) == ms_root_level(M) &&
          solver_simplify_reuse(M, Mtype) &&
              msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, Mtype) &&
              Zlength(mt_lim(ms_core(Mtype))) == 0 &&
              mt_qhead(ms_core(Mtype)) == ms_qtail(Mtype) &&
              ms_capacity_root_propagation_pending(Mtype) == 0 &&
              msolver_seed_shadow(Mtype) && (ms_model(M) == nil => ms_model(Mtype) == nil) &&
              (msat_fp32_positive_finite(ms_cla_decay(M)) =>
               msat_fp32_positive_finite(ms_cla_decay(Mtype))) &&
              (type == 0 || type == 1) &&
              words_type == db_words(solver_selected_db(type, Mtype)) &&
              Vecp::rep(solver_selected_vec(s, type), words_type) *
              clause_db_rep(solver_selected_db(type, Mtype)) *
              store(&(s->assigns), lbool *, asg_type) *
              CharArray::seg(asg_type, 0, ms_size(Mtype),
                             mt_assigns(ms_core(Mtype))) *
              Veci::rep(&(s->trail_lim), z_nil) *
              solver_simplify_db_rest_at(
                s, type, Mtype, reasons, levels_ptr, smp_wl, asg_type)
         */
        vecp*    cs  = type ? &s->learnts : &s->clauses;
        /*@ cs == solver_selected_vec(s, type) */
        clause** cls = (clause**)vecp_begin(cs);

        int i, j;
        i = 0;
        /*@ Inv Assert (exists Mcur (words : list Z) asg,
          ms_cap(Mcur) == ms_cap(M) &&
          ms_root_level(Mcur) == ms_root_level(M) &&
          solver_simplify_reuse(M, Mcur) &&
              s == s@pre &&
              msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, Mcur) &&
              Zlength(mt_lim(ms_core(Mcur))) == 0 &&
              mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
              ms_capacity_root_propagation_pending(Mcur) == 0 &&
              msolver_seed_shadow(Mcur) && (ms_model(M) == nil => ms_model(Mcur) == nil) &&
              (msat_fp32_positive_finite(ms_cla_decay(M)) =>
               msat_fp32_positive_finite(ms_cla_decay(Mcur))) &&
              cs == solver_selected_vec(s, type) &&
              solver_simplify_db_compaction_inv(type, Mcur, words, i, j) &&
              Vecp::rep_ptr(cs, cls, words) *
              clause_db_rep(solver_selected_db(type, Mcur)) *
              store(&(s->assigns), lbool *, asg) *
              CharArray::seg(asg, 0, ms_size(Mcur),
                             mt_assigns(ms_core(Mcur))) *
              Veci::rep(&(s->trail_lim), z_nil) *
              solver_simplify_db_rest_at(
                s, type, Mcur, reasons, levels_ptr, smp_wl, asg)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&true, int, 1) * store(&false, int, 0)
         */
        for (j = 0; i < vecp_size(cs); i++){
            /*@ Given Mcur words asg */
            /*@ 0 <= j && j <= i && i < Zlength(words) &&
                  msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, Mcur) &&
                  solver_simplify_db_compaction_inv(
                    type, Mcur, words, i, j) &&
                  solver_simplify_db_rest_at(
                    s, type, Mcur, reasons, levels_ptr, smp_wl, asg) *
                  clause_db_rep(solver_selected_db(type, Mcur))
                which implies exists (co : clause_obj) jcur,
                  jcur == j && 0 <= j && j <= i && i < Zlength(words) &&
                  2 <= Zlength(co_lits(co)) &&
                  0 <= ms_size(Mcur) && ms_size(Mcur) <= INT_MAX &&
                  2 * ms_size(Mcur) <= INT_MAX &&
                  Zlength(mt_assigns(ms_core(Mcur))) == ms_size(Mcur) &&
                  Forall(lbool_cell, mt_assigns(ms_core(Mcur))) &&
                  Forall(lit_wf_c(ms_size(Mcur)), co_lits(co)) &&
                  0 <= lit_var_c(co_lits(co)[0 - 0]) &&
                  lit_var_c(co_lits(co)[0 - 0]) < ms_size(Mcur) &&
                  db_lookup(solver_selected_db(type, Mcur),
                            words[i - 0], co) &&
                  store(&(s->size), int, ms_size(Mcur)) *
                  solver_wlists_handle(s, smp_wl) *
                  wlists_rep(smp_wl, ms_size(Mcur),
                             ms_wm(Mcur)) *
                  store(&(s->reasons), clause **, reasons) *
                  PtrArray::seg(reasons, 0, ms_size(Mcur),
                                ms_reason_words(Mcur)) *
                  solver_ptr_tail(reasons, ms_size(Mcur), ms_cap(Mcur)) *
                  store(clause_hdr_addr(words[i - 0]), int,
                        clause_hdr_word(co_learnt(co), Zlength(co_lits(co)))) *
                  activity_state(words[i - 0], co_learnt(co), Zlength(co_lits(co))) *
                  IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                                Zlength(co_lits(co)), co_lits(co)) *
                  clause_db_pair_remainder(
                    solver_selected_prob_db(type, Mcur),
                    solver_selected_learnt_db(type, Mcur),
                    words[i - 0], co_learnt(co), co_lits(co)) *
                  stats_rep(&(s->stats), ms_stats(Mcur)) *
                  solver_simplify_clause_frame_at(
                    s, type, Mcur, asg, levels_ptr)
             */
            /*@ Given co jcur */
            if (reasons[lit_var(*clause_begin(cls[i])) /*@ where(original) */] != cls[i] &&
                clause_simplify(s,cls[i])
                  /*@ where n = ms_size(Mcur), clause_words = co_lits(co),
                            assigns0 = mt_assigns(ms_core(Mcur)),
                            is_learnt = co_learnt(co),
                            assigns_ptr = asg */
                  == l_True)
                /*@ msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, Mcur) &&
                      Zlength(mt_lim(ms_core(Mcur))) == 0 &&
                      db_lookup(solver_selected_db(type, Mcur),
                                words[i - 0], co) &&
                      ms_reason_words(Mcur)[lit_var_c(co_lits(co)[0 - 0]) - 0] !=
                        words[i - 0] &&
                      2 <= Zlength(co_lits(co)) &&
                      0 < words[i - 0] && words[i - 0] % 2 == 0 &&
                      store(&(s->size), int, ms_size(Mcur)) *
                      store(&(s->reasons), clause **, reasons) *
                      PtrArray::seg(reasons, 0, ms_size(Mcur),
                                    ms_reason_words(Mcur)) *
                      solver_ptr_tail(reasons, ms_size(Mcur), ms_cap(Mcur)) *
                      solver_wlists_handle(s, smp_wl) *
                      wlists_rep(smp_wl, ms_size(Mcur),
                                 ms_wm(Mcur)) *
                      store(clause_hdr_addr(words[i - 0]), int,
                            clause_hdr_word(co_learnt(co),
                                            Zlength(co_lits(co)))) *
                      activity_state(words[i - 0], co_learnt(co), Zlength(co_lits(co))) *
                      IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                                    Zlength(co_lits(co)), co_lits(co)) *
                      stats_rep(&(s->stats), ms_stats(Mcur))
                    which implies
                      db_lookup(solver_selected_db(type, Mcur),
                                words[i - 0], co) &&
                      clause_remove_pre(
                      s, words[i - 0], ms_size(Mcur), ms_cap(Mcur), smp_wl, reasons,
                      ms_wm(Mcur), co_learnt(co),
                      co_lits(co), ms_stats(Mcur), ms_reason_words(Mcur))
                 */
                clause_remove(s,cls[i]);
            else {
                cls[j] = cls[i];
                /*@ msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, Mcur) &&
                      solver_simplify_db_compaction_inv(
                        type, Mcur, words, i, j) &&
                      0 <= j && j <= i && i < Zlength(words) &&
                      Zlength(mt_lim(ms_core(Mcur))) == 0 &&
                      mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
                      ms_capacity_root_propagation_pending(Mcur) == 0 &&
                      msolver_seed_shadow(Mcur) &&
                      Vecp::rep_ptr(cs, cls,
                                    replace_Znth(j, words[i - 0], words)) *
                      clause_db_pair_remainder(
                        solver_selected_prob_db(type, Mcur),
                        solver_selected_learnt_db(type, Mcur),
                        words[i - 0], co_learnt(co), co_lits(co)) *
                      store(clause_hdr_addr(words[i - 0]), int,
                            clause_hdr_word(co_learnt(co),
                                            Zlength(co_lits(co)))) *
                      activity_state(words[i - 0], co_learnt(co), Zlength(co_lits(co))) *
                      IntArray::seg(clause_lits_addr(words[i - 0]), 0,
                                    Zlength(co_lits(co)), co_lits(co)) *
                      store(&(s->size), int, ms_size(Mcur)) *
                      solver_wlists_handle(s, smp_wl) *
                      wlists_rep(smp_wl, ms_size(Mcur),
                                 ms_wm(Mcur)) *
                      store(&(s->reasons), clause **, reasons) *
                      PtrArray::seg(reasons, 0, ms_size(Mcur),
                                    ms_reason_words(Mcur)) *
                      solver_ptr_tail(reasons, ms_size(Mcur), ms_cap(Mcur)) *
                      stats_rep(&(s->stats), ms_stats(Mcur)) *
                      solver_simplify_clause_frame_at(
                        s, type, Mcur, asg, levels_ptr)
                    which implies
                      solver_simplify_compaction_step(
                        smp_n, smp_F, smp_A_arr, type, Mcur, words,
                        i, j, Mcur,
                        solver_simplify_keep_words(words, i, j), j + 1) &&
                      0 <= j && j <= i && i < Zlength(words) &&
                      Vecp::rep_ptr(cs, cls,
                                  solver_simplify_keep_words(words, i, j)) *
                      clause_db_rep(solver_selected_db(type, Mcur)) *
                      solver_simplify_db_rest_at(
                        s, type, Mcur, reasons, levels_ptr, smp_wl, asg)
                 */
                j++;
            }
            /*@ Assert (exists Mnext (words_next : list Z),
                  ms_cap(Mnext) == ms_cap(M) &&
                  ms_root_level(Mnext) == ms_root_level(M) &&
                  solver_simplify_reuse(M, Mnext) &&
                  s == s@pre &&
                  (ms_model(M) == nil => ms_model(Mnext) == nil) &&
                  (msat_fp32_positive_finite(ms_cla_decay(M)) =>
                   msat_fp32_positive_finite(ms_cla_decay(Mnext))) &&
                  cs == solver_selected_vec(s, type) &&
                  solver_simplify_compaction_step(
                    smp_n, smp_F, smp_A_arr, type, Mcur, words,
                    i, jcur, Mnext, words_next, j) &&
                  Vecp::rep_ptr(cs, cls, words_next) *
                  clause_db_rep(solver_selected_db(type, Mnext)) *
                  store(&(s->assigns), lbool *, asg) *
                  CharArray::seg(asg, 0, ms_size(Mnext),
                                 mt_assigns(ms_core(Mnext))) *
                  Veci::rep(&(s->trail_lim), z_nil) *
                  solver_simplify_db_rest_at(
                    s, type, Mnext, reasons, levels_ptr, smp_wl, asg)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&true, int, 1) * store(&false, int, 0)
             */
        }
        vecp_resize(cs,j);
        /*@ Assert (s == s@pre &&
              solver_simplify_outer_loop(
              s, smp_n, smp_F, smp_A_arr,
              reasons, levels_ptr, type + 1, M, smp_wl) *
              has_permission(&cs) * has_permission(&cls) *
              has_permission(&i) * has_permission(&j)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&true, int, 1) * store(&false, int, 0)
         */
    }

    /*@ type >= 2 &&
          solver_simplify_outer_loop(
          s, smp_n, smp_F, smp_A_arr, reasons, levels_ptr, type, M, smp_wl)
        which implies exists Mdone,
          ms_cap(Mdone) == ms_cap(M) &&
          ms_root_level(Mdone) == ms_root_level(M) &&
          solver_simplify_reuse(M, Mdone) &&
          type == 2 &&
          msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, Mdone) &&
          Zlength(mt_lim(ms_core(Mdone))) == 0 &&
          mt_qhead(ms_core(Mdone)) == ms_qtail(Mdone) &&
          ms_capacity_root_propagation_pending(Mdone) == 0 &&
          msolver_seed_shadow(Mdone) &&
          (ms_model(M) == nil => ms_model(Mdone) == nil) &&
          (msat_fp32_positive_finite(ms_cla_decay(M)) =>
           msat_fp32_positive_finite(ms_cla_decay(Mdone))) &&
          solver_rep_reasons_levels_wl_at(
            s, Mdone, reasons, levels_ptr, smp_wl)
     */
    /*@ Given Mdone */

    /*@ solver_rep_reasons_levels_wl_at(
          s, Mdone, reasons, levels_ptr, smp_wl)
        which implies
          store(&(s->qhead), int, mt_qhead(ms_core(Mdone))) *
          store(&(s->simpdb_assigns), int, ms_simpdb_assigns(Mdone)) *
          store(&(s->simpdb_props), int, ms_simpdb_props(Mdone)) *
          store(&(s->stats.clauses_literals), unsigned long long,
                stats_clauses_literals(ms_stats(Mdone))) *
          store(&(s->stats.learnts_literals), unsigned long long,
                stats_learnts_literals(ms_stats(Mdone))) *
          solver_simplify_finish_frame_at(s, Mdone, levels_ptr, smp_wl) *
          has_permission(&reasons)
     */
    s->simpdb_assigns = s->qhead;

    s->simpdb_props = (int)(s->stats.clauses_literals + s->stats.learnts_literals);

    /*@ ms_cap(Mdone) == ms_cap(M) &&
          ms_root_level(Mdone) == ms_root_level(M) &&
          solver_simplify_reuse(M, Mdone) &&
          msolver_inv_assuming_strong(smp_n, smp_F, smp_A_arr, smp_A_arr, Mdone) &&
          Zlength(mt_lim(ms_core(Mdone))) == 0 &&
          mt_qhead(ms_core(Mdone)) == ms_qtail(Mdone) &&
          ms_capacity_root_propagation_pending(Mdone) == 0 &&
          msolver_seed_shadow(Mdone) &&
          store(&(s->qhead), int, mt_qhead(ms_core(Mdone))) *
          store(&(s->simpdb_assigns), int, mt_qhead(ms_core(Mdone))) *
          store(&(s->simpdb_props), int,
                MiniSatTarget::uint64_sum_to_int(
                  stats_clauses_literals(ms_stats(Mdone)),
                  stats_learnts_literals(ms_stats(Mdone)))) *
          store(&(s->stats.clauses_literals), unsigned long long,
                stats_clauses_literals(ms_stats(Mdone))) *
          store(&(s->stats.learnts_literals), unsigned long long,
                stats_learnts_literals(ms_stats(Mdone))) *
          solver_simplify_finish_frame_at(s, Mdone, levels_ptr, smp_wl)
        which implies exists Mfinish,
          ms_cap(Mfinish) == ms_cap(M) &&
          ms_root_level(Mfinish) == ms_root_level(M) &&
          solver_simplify_reuse(M, Mfinish) &&
          solver_simplify_finish_transition(
            smp_n, smp_F, smp_A_arr, Mdone,
            MiniSatTarget::uint64_sum_to_int(
              stats_clauses_literals(ms_stats(Mdone)),
              stats_learnts_literals(ms_stats(Mdone))), Mfinish) &&
          solver_rep_levels_wl_at(s, Mfinish, smp_wl, levels_ptr)
     */
    /*@ Given Mfinish */
    return true;
}

bool solver_solve(solver* s, lit* begin, lit* endvar)
/*@ solver_solve_spec */
{

    /*@ Assert (s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          exists (Mdrained : msolver),
          ms_cap(Mdrained) == ms_cap(M) &&
          solver_query_reuse(M, Mdrained) &&
          solver_update_ready(n, F, nil, Mdrained) &&
          ms_capacity_root_propagation_pending(Mdrained) == 0 &&
          (A_arr != nil => mt_qhead(ms_core(Mdrained)) == ms_qtail(Mdrained)) &&
          msolver_seed_shadow(Mdrained) &&
          assumptions_array(n, begin, endvar, A_arr) *
          solver_rep_wl(s, Mdrained, solve_wl)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    /*@ Given Mdrained */

    /*@ solver_update_ready(n, F, nil, Mdrained) &&
          ms_capacity_root_propagation_pending(Mdrained) == 0 &&
          (A_arr != nil => mt_qhead(ms_core(Mdrained)) == ms_qtail(Mdrained)) &&
          msolver_seed_shadow(Mdrained) &&
          solver_rep_wl(s, Mdrained, solve_wl)
        which implies exists values_entry levels_done,
          solver_update_ready(n, F, nil, Mdrained) &&
          ms_capacity_root_propagation_pending(Mdrained) == 0 &&
          (A_arr != nil => mt_qhead(ms_core(Mdrained)) == ms_qtail(Mdrained)) &&
          msolver_seed_shadow(Mdrained) &&
          Vecp::rep(
            &(s->clauses), db_words(ms_prob(Mdrained))) *
          store(&(s->assigns), lbool *, values_entry) *
          CharArray::seg(
            values_entry, 0, ms_size(Mdrained), mt_assigns(ms_core(Mdrained))) *
          solver_char_tail(
            values_entry, ms_size(Mdrained), ms_cap(Mdrained)) *
          solver_solve_entry_rest_at(s, Mdrained, levels_done, solve_wl)
     */
    /*@ Given values_entry levels_done */
    double  nof_conflicts = 100;
    double  nof_learnts   = solver_nclauses(s)
                              /*@ where (solver_nclauses_spec) */ / 3;
    lbool   status        = l_Undef;
    lbool*  values        = s->assigns;
    lit*    i;

    /*@ Vecp::rep(
          &(s->clauses), db_words(ms_prob(Mdrained))) *
          store(&(s->assigns), lbool *, values_entry) *
          CharArray::seg(
            values_entry, 0, ms_size(Mdrained), mt_assigns(ms_core(Mdrained))) *
          solver_char_tail(
            values_entry, ms_size(Mdrained), ms_cap(Mdrained)) *
          solver_solve_entry_rest_at(s, Mdrained, levels_done, solve_wl)
        which implies
          solver_rep_assigns_levels_at(
            s, Mdrained, values_entry, levels_done, solve_wl)
     */

    /*@ Assert (exists (Mready : msolver) levels_ptr,
          ms_cap(Mready) == ms_cap(M) &&
          solver_query_reuse(M, Mready) &&
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          solver_update_ready(n, F, nil, Mready) &&
          ms_capacity_root_propagation_pending(Mready) == 0 &&
          (A_arr != nil => mt_qhead(ms_core(Mready)) == ms_qtail(Mready)) &&
          msolver_seed_shadow(Mready) &&
          assumptions_array(n, begin, endvar, A_arr) *
          solver_rep_assigns_levels_at(
            s, Mready, values, levels_ptr, solve_wl) *
          store(&nof_conflicts, double, nof_conflicts) *
          store(&nof_learnts, double, nof_learnts) *
          store(&status, char, 0) *
          has_permission(&i)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    /*@ Given Mready levels_ptr */

    //printf("solve: "); printlits(begin, endvar); printf("\n");
    /*@ solver_update_ready(n, F, nil, Mready) &&
          ms_capacity_root_propagation_pending(Mready) == 0 &&
          (A_arr != nil => mt_qhead(ms_core(Mready)) == ms_qtail(Mready)) &&
          msolver_seed_shadow(Mready) &&
          assumptions_array(n, begin, endvar, A_arr) *
          solver_rep_assigns_levels_at(
            s, Mready, values, levels_ptr, solve_wl)
        which implies exists (raw_entry : list Z),
          endvar == begin + Zlength(raw_entry) * sizeof(int) &&
          A_arr == assumption_prefix(raw_entry, Zlength(raw_entry)) &&
          Forall(lit_wf_c(n), raw_entry) &&
          (raw_entry != nil || valid_int_position(begin)) &&
          ms_size(Mready) == n && 0 <= n && 2 * n <= INT_MAX &&
          Zlength(mt_assigns(ms_core(Mready))) == n &&
          msolver_inv_assuming_strong(n, F, A_arr, nil, Mready) &&
          (raw_entry != nil => mt_qhead(ms_core(Mready)) == ms_qtail(Mready)) &&
          ms_capacity_root_propagation_pending(Mready) == 0 &&
          msolver_seed_shadow(Mready) &&
          store(&(s->assigns), lbool *, values) *
          CharArray::seg(
            values, 0, n, mt_assigns(ms_core(Mready))) *
          solver_char_tail(values, n, ms_cap(Mready)) *
          IntArray::seg(begin, 0, Zlength(raw_entry), raw_entry) *
          solver_assigns_focus_frame_wl_at(
            s, Mready, solve_wl, levels_ptr)
     */
    /*@ Inv Assert (exists (raw : list Z) (Mcur : msolver) k,
          ms_cap(Mcur) == ms_cap(M) &&
          solver_query_reuse(M, Mcur) &&
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          0 <= k && k <= Zlength(raw) &&
          endvar == begin + Zlength(raw) * sizeof(int) &&
          i == begin + k * sizeof(int) &&
          A_arr == assumption_prefix(raw, Zlength(raw)) && Forall(lit_wf_c(n), raw) &&
          (raw != nil || valid_int_position(begin)) &&
          ms_size(Mcur) == n && 0 <= n && 2 * n <= INT_MAX &&
          Zlength(mt_assigns(ms_core(Mcur))) == n &&
          msolver_inv_assuming_strong(
            n, F, A_arr, assumption_prefix(raw, k), Mcur) &&
          (raw != nil => mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur)) &&
          ms_capacity_root_propagation_pending(Mcur) == 0 &&
          msolver_seed_shadow(Mcur) &&
          store(&(s->assigns), lbool *, values) *
          CharArray::seg(
            values, 0, n, mt_assigns(ms_core(Mcur))) *
          solver_char_tail(values, n, ms_cap(Mcur)) *
          IntArray::seg(begin, 0, Zlength(raw), raw) *
          solver_assigns_focus_frame_wl_at(s, Mcur, solve_wl, levels_ptr) *
          store(&nof_conflicts, double, nof_conflicts) *
          store(&nof_learnts, double, nof_learnts) *
          store(&status, char, 0)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    for (i = begin; i < endvar; i++){
        /*@ Given raw Mcur k */
        /*@ 2 * n <= INT_MAX &&
              0 <= k && k <= Zlength(raw) &&
              i == begin + k * sizeof(int) &&
              endvar == begin + Zlength(raw) * sizeof(int) && i < endvar &&
              Forall(lit_wf_c(n), raw)
            which implies
              0 <= k && k < Zlength(raw) &&
              i == begin + k * sizeof(int) &&
              endvar == begin + Zlength(raw) * sizeof(int) &&
              Forall(lit_wf_c(n), raw) &&
              0 <= Znth(k, raw, 0) && Znth(k, raw, 0) <= INT_MAX &&
              0 <= lit_var_c(Znth(k - 0, raw, 0)) &&
              lit_var_c(Znth(k - 0, raw, 0)) < n
         */
        lbool assumption_status =
            lit_sign(*i)
              ? -values[lit_var(*i) /*@ where (bounded_index) lv_bound_n = n */]
              : values[lit_var(*i) /*@ where (bounded_index) lv_bound_n = n */];

        /*@ -1 <= assumption_status &&
                   assumption_status <= 1
         */

        /*@ Assert (ms_cap(Mcur) == ms_cap(M) &&
          solver_query_reuse(M, Mcur) &&
          s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          0 <= k && k < Zlength(raw) &&
          endvar == begin + Zlength(raw) * sizeof(int) &&
          A_arr == assumption_prefix(raw, Zlength(raw)) && Forall(lit_wf_c(n), raw) &&
          raw != nil &&
          ms_size(Mcur) == n && 0 <= n && 2 * n <= INT_MAX &&
          Zlength(mt_assigns(ms_core(Mcur))) == n &&
          msolver_inv_assuming_strong(
            n, F, A_arr, assumption_prefix(raw, k), Mcur) &&
          mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
          ms_capacity_root_propagation_pending(Mcur) == 0 &&
          msolver_seed_shadow(Mcur) &&
          store(&i, int *, begin + k * sizeof(int)) *
          store(&values, lbool *, values) *
          store(&assumption_status, lbool,
            (1 - 2 * lit_sign_c(Znth(k, raw, 0))) *
            Znth(lit_var_c(Znth(k, raw, 0)), mt_assigns(ms_core(Mcur)), 0)) *
          store(&(s->assigns), lbool *, values) *
          CharArray::seg(
            values, 0, n, mt_assigns(ms_core(Mcur))) *
          solver_char_tail(values, n, ms_cap(Mcur)) *
          IntArray::seg(begin, 0, Zlength(raw), raw) *
          solver_assigns_focus_frame_wl_at(s, Mcur, solve_wl, levels_ptr) *
          store(&nof_conflicts, double, nof_conflicts) *
          store(&nof_learnts, double, nof_learnts) *
          store(&status, char, 0)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
         */

        switch (assumption_status) {
        case 1:
            /*@ msolver_inv_assuming_strong(
                  n, F, A_arr, assumption_prefix(raw, k), Mcur) &&
                  A_arr == assumption_prefix(raw, Zlength(raw)) &&
                  0 <= k && k < Zlength(raw) &&
                  Forall(lit_wf_c(n), raw) &&
                  Znth(lit_var_c(Znth(k, raw, 0)),
                       mt_assigns(ms_core(Mcur)), 0) ==
                    1 - 2 * lit_sign_c(Znth(k, raw, 0)) &&
                  assumption_status == 1
                which implies
                  A_arr == assumption_prefix(raw, Zlength(raw)) &&
                  0 <= k && k < Zlength(raw) &&
                  assumption_true_advance(n, F, A_arr, raw, k, Mcur) &&
                  has_permission(&assumption_status)
             */
            break;
        case 0:

            /*@ msolver_inv_assuming_strong(
                  n, F, A_arr, assumption_prefix(raw, k), Mcur) &&
                  mt_qhead(ms_core(Mcur)) == ms_qtail(Mcur) &&
                  Forall(lit_wf_c(n), raw) &&
                  Znth(lit_var_c(Znth(k, raw, 0)),
                       mt_assigns(ms_core(Mcur)), 0) == 0 &&
                  assumption_status == 0 &&
                  0 <= k && k < Zlength(raw)
                which implies
                  0 <= k && k < Zlength(raw) &&
                  assumption_status == 0 &&
                  assumption_fresh_ready(n, raw, k, Mcur)
             */
            /*@ assumption_fresh_ready(n, raw, k, Mcur) &&
                  store(&(s->assigns), lbool *, values) *
                  CharArray::seg(
                    values, 0, n, mt_assigns(ms_core(Mcur))) *
                  solver_char_tail(values, n, ms_cap(Mcur)) *
                  solver_assigns_focus_frame_wl_at(s, Mcur, solve_wl, levels_ptr)
                which implies
                  assumption_fresh_ready(n, raw, k, Mcur) &&
                  store(&(s->qhead), int, ms_qtail(Mcur)) *
                  enqueue_state_at(
                    s, values, levels_ptr, n, ms_cap(Mcur),
                    ms_qtail(Mcur), mt_assigns(ms_core(Mcur)),
                    mt_levels(ms_core(Mcur)), ms_reason_words(Mcur),
                    mt_trail(ms_core(Mcur)), mt_lim(ms_core(Mcur))) *
                  solver_assume_frame_wl(s, Mcur, solve_wl)
             */
            assume(s, *i);
            /*@ ms_cap(Mcur) == ms_cap(M) &&
                  solver_query_reuse(M, Mcur) &&
          msolver_inv_assuming_strong(
                  n, F, A_arr, assumption_prefix(raw, k), Mcur) &&
                  assumption_fresh_ready(n, raw, k, Mcur) &&
                  msolver_seed_shadow(Mcur) &&
                  ms_capacity_root_propagation_pending(Mcur) == 0 &&
                  A_arr == assumption_prefix(raw, Zlength(raw)) &&
                  Forall(lit_wf_c(n), raw) &&
                  0 <= k && k < Zlength(raw) &&
                  assume_post_at(
                  s, values, levels_ptr, raw[k - 0], n,
                  ms_cap(Mcur), ms_qtail(Mcur),
                  mt_assigns(ms_core(Mcur)), mt_levels(ms_core(Mcur)),
                  ms_reason_words(Mcur), mt_trail(ms_core(Mcur)),
                  mt_lim(ms_core(Mcur))) *
                  solver_assume_frame_wl(s, Mcur, solve_wl)
                which implies exists (Mdecide : msolver),
                  ms_cap(Mdecide) == ms_cap(M) &&
                  solver_query_reuse(M, Mdecide) &&
                  assumption_fresh_transition(
                    n, F, A_arr, raw, k,
                    Mcur, Mdecide) &&
                  solver_rep_assigns_levels_at(
                    s, Mdecide, values, levels_ptr, solve_wl)
             */
            /*@ Given Mdecide */
            /*@ assumption_fresh_transition(
                  n, F, A_arr, raw, k, Mcur, Mdecide) &&
                  solver_rep_assigns_levels_at(
                    s, Mdecide, values, levels_ptr, solve_wl)
                which implies
                  solver_propagation_inv(n, F, A_arr,
                    PropagationAssuming(assumption_prefix(raw, k + 1)), Mdecide) &&
                  msolver_seed_shadow(Mdecide) &&
                  solver_rep_assigns_levels_at(
                    s, Mdecide, values, levels_ptr, solve_wl)
             */
            if (solver_propagate(s)
                  /*@ where n = n, F = F, A_arr = A_arr,
                            K = PropagationAssuming(assumption_prefix(raw, k + 1)),
                            M0 = Mdecide, assigns_entry = values,
                            levels_entry = levels_ptr, wlists_entry = solve_wl */ == NULL)
                /*@ Given propagation_result */
                /*@ ms_cap(Mdecide) == ms_cap(M) &&
                      solver_query_reuse(M, Mdecide) &&
                      solver_propagation_inv(n, F, A_arr,
                        PropagationAssuming(assumption_prefix(raw, k + 1)), propagation_result) &&
                      propagation_caller_frame(Mdecide, propagation_result) &&
                      minisat_propagation_reuse_live(Mdecide, propagation_result) &&
                      msolver_seed_shadow(propagation_result) &&
                      mt_qhead(ms_core(propagation_result)) == ms_qtail(propagation_result) &&
                      solver_rep_assigns_levels_at(
                        s, propagation_result, values, levels_ptr, solve_wl)
                    which implies exists (Mprop : msolver),
                      ms_cap(Mprop) == ms_cap(M) &&
                      solver_query_reuse(M, Mprop) &&
                      assumption_propagation_success(
                        n, F, A_arr, raw, k + 1, Mprop) &&
                      solver_rep_assigns_levels_at(
                        s, Mprop, values, levels_ptr, solve_wl)
                 */
                /*@ Given Mprop */
                /*@ assumption_propagation_success(
                      n, F, A_arr, raw, k + 1, Mprop) &&
                      0 <= n && 2 * n <= INT_MAX &&
                      solver_rep_assigns_levels_at(
                      s, Mprop, values, levels_ptr, solve_wl)
                    which implies
                      ms_size(Mprop) == n && 0 <= n &&
                      2 * n <= INT_MAX &&
                      Zlength(mt_assigns(ms_core(Mprop))) == n &&
                      store(&(s->assigns), lbool *, values) *
                      CharArray::seg(
                        values, 0, n, mt_assigns(ms_core(Mprop))) *
                      solver_char_tail(values, n, ms_cap(Mprop)) *
                      solver_assigns_focus_frame_wl_at(
                        s, Mprop, solve_wl, levels_ptr)
                 */
                break;


        case -1:
            /*@ Assert (exists (Mfailure : msolver) failure_kind failure_focus,
                  s == s@pre && begin == begin@pre && endvar == endvar@pre &&
                  ms_cap(Mfailure) == ms_cap(M) && ms_size(Mfailure) == n &&
                  ms_capacity_root_propagation_pending(Mfailure) == 0 &&
                  msolver_seed_shadow(Mfailure) &&
                  cnf_unsat(n, cnf_with_units(F, A_arr)) &&
                  0 <= failure_kind && failure_kind <= 1 &&
                  (failure_kind == 0 =>
                    msolver_inv_assuming_strong(n, F, A_arr,
                      assumption_prefix(raw, k), Mfailure) &&
                    mt_qhead(ms_core(Mfailure)) == ms_qtail(Mfailure) &&
                    solver_query_reuse(M, Mfailure)) &&
                  (failure_kind == 1 =>
                    propagation_cancel_ready(n, F, A_arr,
                      PropagationAssuming(assumption_prefix(raw, k + 1)), Mfailure, failure_focus) &&
                    (solver_query_reuse_guard(M) => minisat_watch_conflict_ready(n, Mfailure)) &&
                    minisat_resident_false_clause(Mfailure)) &&
                  assumptions_array(n, begin, endvar, A_arr) *
                  solver_rep_assigns_levels_at(s, Mfailure, values, levels_ptr, solve_wl) *
                  store(&nof_conflicts, double, nof_conflicts) *
                  store(&nof_learnts, double, nof_learnts) *
                  store(&status, char, 0) * has_permission(&i) *
                  has_permission(&assumption_status)) *
                  store(&l_Undef, char, 0) * store(&l_True, char, 1) *
                  store(&l_False, char, -1) * store(&var_Undef, int, -1) *
                  store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
             */
            /*@ Given Mfailure failure_kind failure_focus */
            /*@ ms_cap(Mfailure) == ms_cap(M) && ms_size(Mfailure) == n &&
                  ms_capacity_root_propagation_pending(Mfailure) == 0 &&
                  msolver_seed_shadow(Mfailure) &&
                  cnf_unsat(n, cnf_with_units(F, A_arr)) &&
                  0 <= failure_kind && failure_kind <= 1 &&
                  (failure_kind == 0 =>
                    msolver_inv_assuming_strong(n, F, A_arr,
                      assumption_prefix(raw, k), Mfailure) &&
                    mt_qhead(ms_core(Mfailure)) == ms_qtail(Mfailure) &&
                    solver_query_reuse(M, Mfailure)) &&
                  (failure_kind == 1 =>
                    propagation_cancel_ready(n, F, A_arr,
                      PropagationAssuming(assumption_prefix(raw, k + 1)), Mfailure, failure_focus) &&
                    (solver_query_reuse_guard(M) => minisat_watch_conflict_ready(n, Mfailure)) &&
                    minisat_resident_false_clause(Mfailure)) &&
                  solver_rep_assigns_levels_at(s, Mfailure, values, levels_ptr, solve_wl)
                which implies
                  solver_cancel_pre(s, 0, Mfailure, solve_wl) *
                  solver_levels_slice_at(s, Mfailure, levels_ptr) * has_permission(&values)
             */
            solver_canceluntil(s, 0);
            /*@ ms_cap(Mfailure) == ms_cap(M) && ms_size(Mfailure) == n &&
                  ms_capacity_root_propagation_pending(Mfailure) == 0 &&
                  msolver_seed_shadow(Mfailure) &&
                  cnf_unsat(n, cnf_with_units(F, A_arr)) &&
                  0 <= failure_kind && failure_kind <= 1 &&
                  (failure_kind == 0 =>
                    msolver_inv_assuming_strong(n, F, A_arr,
                      assumption_prefix(raw, k), Mfailure) &&
                    mt_qhead(ms_core(Mfailure)) == ms_qtail(Mfailure) &&
                    solver_query_reuse(M, Mfailure)) &&
                  (failure_kind == 1 =>
                    propagation_cancel_ready(n, F, A_arr,
                      PropagationAssuming(assumption_prefix(raw, k + 1)), Mfailure, failure_focus) &&
                    (solver_query_reuse_guard(M) => minisat_watch_conflict_ready(n, Mfailure)) &&
                    minisat_resident_false_clause(Mfailure)) &&
                  solver_cancel_post(s, 0, Mfailure, solve_wl) *
                  solver_levels_slice_at(s, Mfailure, levels_ptr)
                which implies exists (Mfalse_unsat : msolver),
                  ms_cap(Mfalse_unsat) == ms_cap(M) &&
                  solver_unsat_arm_at(s, n, F, A_arr, M, Mfalse_unsat, solve_wl)
             */
            return false;
        }
    }

    /*@ Given raw Mcur k */
    /*@ 0 <= k && k <= Zlength(raw) &&
          i == begin + k * sizeof(int) &&
          endvar == begin + Zlength(raw) * sizeof(int) && i >= endvar &&
          A_arr == assumption_prefix(raw, Zlength(raw))
        which implies
          k == Zlength(raw) && assumption_prefix(raw, k) == A_arr &&
          endvar == begin + Zlength(raw) * sizeof(int) &&
          has_permission(&i)
     */
    /*@ store(&(s->assigns), lbool *, values) *
          CharArray::seg(
            values, 0, n, mt_assigns(ms_core(Mcur))) *
          solver_char_tail(values, n, ms_cap(Mcur)) *
          solver_assigns_focus_frame_wl_at(s, Mcur, solve_wl, levels_ptr)
        which implies
          store(&(s->root_level), int, ms_root_level(Mcur)) *
          Veci::rep(&(s->trail_lim),
                   mt_lim(ms_core(Mcur))) *
          solver_root_install_frame_at(
            s, Mcur, values, levels_ptr, solve_wl)
     */
    s->root_level = solver_dlevel(s);
    /*@ ms_cap(Mcur) == ms_cap(M) &&
          solver_query_reuse(M, Mcur) &&
          msolver_inv_assuming_strong(n, F, A_arr, A_arr, Mcur) &&
          ms_capacity_root_propagation_pending(Mcur) == 0 &&
          msolver_seed_shadow(Mcur) &&
          store(&(s->root_level), int,
                Zlength(mt_lim(ms_core(Mcur)))) *
          Veci::rep(&(s->trail_lim),
                   mt_lim(ms_core(Mcur))) *
          solver_root_install_frame_at(
            s, Mcur, values, levels_ptr, solve_wl)
        which implies exists (Mroot : msolver) (A_inst : list literal),
          ms_cap(Mroot) == ms_cap(M) &&
          solver_query_reuse(M, Mroot) &&
          assumption_root_install(
            n, F, A_arr, Mcur, Mroot, A_inst) &&
          solver_rep_wl(s, Mroot, solve_wl) * has_permission(&values)
     */

#ifdef MINISAT_QCP_ENABLE_OUTPUT
    if (s->verbosity >= 1){
        printf("==================================[MINISAT]===================================\n");
        printf("| Conflicts |     ORIGINAL     |              LEARNT              | Progress |\n");
        printf("|           | Clauses Literals |   Limit Clauses Literals  Lit/Cl |          |\n");
        printf("==============================================================================\n");
    }
#endif

    /*@ Inv Assert (s == s@pre && begin == begin@pre && endvar == endvar@pre &&
          -1 <= status && status <= 1 &&
          solver_restart_loop(
          s, begin, endvar, n, F, A_arr, status, solve_wl, M) *
          store(&nof_conflicts, double, nof_conflicts) *
          store(&nof_learnts, double, nof_learnts) *
          has_permission(&values) *
          has_permission(&i)) *
          store(&l_Undef, char, 0) * store(&l_True, char, 1) * store(&l_False, char, -1) * store(&var_Undef, int, -1) * store(&lit_Undef, int, -2) * store(&true, int, 1) * store(&false, int, 0)
     */
    while (status == l_Undef){
#ifdef MINISAT_QCP_ENABLE_OUTPUT
        double Ratio = (s->stats.learnts == 0)? 0.0 :
            s->stats.learnts_literals / (double)s->stats.learnts;

        if (s->verbosity >= 1){
            printf("| %9.0f | %7.0f %8.0f | %7.0f %7.0f %8.0f %7.1f | %6.3f %% |\n",
                (double)s->stats.conflicts,
                (double)s->stats.clauses,
                (double)s->stats.clauses_literals,
                (double)nof_learnts,
                (double)s->stats.learnts,
                (double)s->stats.learnts_literals,
                Ratio,
                s->progress_estimate*100);
            fflush(stdout);
        }
#endif
        /* The trusted budget facade has an unconstrained verification
           result; search soundness is independent of the chosen heuristic
           budgets. */
        /*@ solver_restart_loop(
              s, begin, endvar, n, F, A_arr, status, solve_wl, M) &&
              status <= 0 &&
              0 <= status
            which implies exists (A_search : list literal)
                                 (Msearch : msolver),
          ms_cap(Msearch) == ms_cap(M) &&
              (solver_query_reuse_guard(M) =>
               minisat_base_watch_completed(Msearch)) &&
              assumptions_array(n, begin, endvar, A_arr) *
              solver_search_pre(
                s, n, F, A_arr, A_search, Msearch, solve_wl) *
              has_permission(&status)
         */

        /*@ Given A_search Msearch */
        status = solver_search(s, minisat_budget_to_int(nof_conflicts), minisat_budget_to_int(nof_learnts));
        /*@ ms_cap(Msearch) == ms_cap(M) &&
              (solver_query_reuse_guard(M) =>
               minisat_base_watch_completed(Msearch)) &&
              assumptions_array(n, begin, endvar, A_arr) *
              solver_search_result(s, n, F, A_arr, A_search,
                                   status, solve_wl, Msearch)
            which implies
              solver_restart_loop(s, begin, endvar, n, F, A_arr,
                                  status, solve_wl, M)
         */
        nof_conflicts *= 1.5;
        nof_learnts   *= 1.1;
    }
#ifdef MINISAT_QCP_ENABLE_OUTPUT
    if (s->verbosity >= 1)
        printf("==============================================================================\n");
#endif



    /*@ solver_restart_loop(
          s, begin, endvar, n, F, A_arr, status, solve_wl, M) &&
          -1 <= status && status <= 1 && status != 0
        which implies exists (Mterminal : msolver) terminal_levels,
          ms_cap(Mterminal) == ms_cap(M) &&
          solver_terminal_reuse(n, F, A_arr, M, Mterminal, status) &&
          ms_size(Mterminal) == n &&
          -1 <= status &&
          status <= 1 &&
          status != 0 &&
          (status == 1 =>
             model_saved(n, F, A_arr, Mterminal) &&
             solver_sat_cancel_ready(n, F, A_arr, Mterminal)) &&
          (status == -1 =>
             cnf_unsat(n, cnf_with_units(F, A_arr))) &&
          assumptions_array(n, begin, endvar, A_arr) *
          solver_cancel_pre(s, 0, Mterminal, solve_wl) *
          solver_levels_slice_at(s, Mterminal, terminal_levels)
     */
    /*@ Given Mterminal terminal_levels */
    solver_canceluntil(s, 0);
    /*@ ms_cap(Mterminal) == ms_cap(M) &&
          solver_terminal_reuse(n, F, A_arr, M, Mterminal, status) &&
          ms_size(Mterminal) == n &&
          -1 <= status && status <= 1 && status != 0 &&
          (status == 1 =>
             model_saved(n, F, A_arr, Mterminal) &&
             solver_sat_cancel_ready(n, F, A_arr, Mterminal)) &&
          (status == -1 =>
             cnf_unsat(n, cnf_with_units(F, A_arr))) &&
          solver_cancel_post(s, 0, Mterminal, solve_wl) *
          solver_levels_slice_at(s, Mterminal, terminal_levels)
        which implies
          (exists (Msat : msolver),
             status == 1 && ms_cap(Msat) == ms_cap(M) &&
             solver_sat_arm_at(s, n, F, A_arr, M, Msat, solve_wl)) ||
          (exists (Munsat : msolver),
             status == -1 && ms_cap(Munsat) == ms_cap(M) &&
             solver_unsat_arm_at(s, n, F, A_arr, M, Munsat, solve_wl))
     */
    return status != l_False;
}

int solver_nvars(solver* s)
/*@ solver_nvars_spec */
{
    /*@ solver_size_cell(s, n) which implies store(&(s->size), n) */
    return s->size;
}

int solver_nclauses(solver* s)
/*@ solver_nclauses_spec */
{
    return vecp_size(&s->clauses);
}

int solver_nconflicts(solver* s)
/*@ solver_nconflicts_spec */
{
    /*@ solver_conflict_count_cell(s, conflicts)
        which implies store(&(s->stats.conflicts), conflicts) */
    return (int)s->stats.conflicts;
}
